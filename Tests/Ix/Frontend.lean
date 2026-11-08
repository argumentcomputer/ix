/-
  Tests/Ix/Frontend.lean

  Comprehensive test suite for the pure, deterministic Ix frontend (`Ix/Frontend/*`):
  1. Pure parser (`Text -> Ix.Syntax`): commands, terms, operators, `#<hash>`, `map Name := #<hash>`
  2. Substructural usage (`0`, `1`, `&`), ownership (`!`), and locality (`~`) annotations + `let borrow`
  3. Order-free & `mutual`-free declarations via Tarjan SCC (`SccPass.lean`)
  4. In-elaborator block & constructor canonicalization (with source-order tie-breaking for α-identical ctors)
  5. Surgery-free `AuxGen` (`.rec`, `.recOn`, `.casesOn`, `._ctorIdx`, structure projections)
  6. Tactic mode (`intro`, `exact`, `assumption`, `rfl`, `constructor`, `have`, `cases`),
     structural recursion lowering (`casesOn` -> `recOn`), and `String`/`Char`/`Nat` acceleration
  7. Programmable module mapping (`map Name := #<hash>`) & `ElabClaim` verification
-/
import Lean
import LSpec
import Ix.Frontend
import Ix.Store
import Ix.Meta
import Ix.EnvScope
import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups
import Ix.IxVM.ClaimHarness
import Tests.Aiur.Common

open LSpec
open Ix
open Ix.Frontend
open Ix.Frontend.Parser
open Ix.Frontend.Elab
open Ix.Frontend.Canon
open IxVM.ClaimHarness

/-! ## 1. Pure Parser Tests (`Text -> Ix.Syntax`) -/

def testParserBasic : Bool :=
  let src := "
    import #0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
    map Std.Hash := #fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210

    namespace Demo
    infixl:65 \" +++ \" => myAdd
    def idNat (x : Nat) : Nat := x
    end Demo
  "
  match parseSource src with
  | .error _ => false
  | .ok (stx, pEnv) =>
    Syntax.isOfKind stx SyntaxKind.moduleKind &&
    (Syntax.getArgs stx).size >= 4 &&
    pEnv.operators.any (fun op => op.symbol == "+++")

/-! ## 2. Substructural Usage, Ownership & Locality Contract Tests -/

def testSubstructuralContracts : Bool :=
  let src := "
    def linearUnique (!1 x : Nat) : ! Nat := x
    def erasedArg (0 ghost : Type) (1 y : Nat) : Nat := y
    def affineLocal (&!~ x : Nat) (~ y : Nat) : ~ Nat := y
    def withBorrowLet (x : Nat) : Nat :=
      let borrow b : Nat := x;
      b
  "
  match elabSource src with
  | .error _ => false
  | .ok env =>
    let linName := Name.simple "linearUnique"
    let eraName := Name.simple "erasedArg"
    let affName := Name.simple "affineLocal"
    let borName := Name.simple "withBorrowLet"
    let (linBcs, linRet) := env.binderContracts.get? linName |>.getD (#[], .shared)
    let (eraBcs, _eraRet) := env.binderContracts.get? eraName |>.getD (#[], .shared)
    let (affBcs, affRet) := env.binderContracts.get? affName |>.getD (#[], .shared)
    let borLets := env.letContracts.get? borName |>.getD #[]
    -- Check `linearUnique`: binder 0 has `{ uses := .linear, value := .unique }`, return `.unique`
    let okLin :=
      linBcs.size == 1 &&
      linBcs[0]! == { uses := .linear, value := .unique } &&
      linRet == .unique
    -- Check `erasedArg`: binder 0 has `.erased`, binder 1 has `.linear`
    let okEra :=
      eraBcs.size == 2 &&
      eraBcs[0]!.uses == .erased &&
      eraBcs[1]!.uses == .linear
    -- Check `affineLocal`: binder 0 has `{ uses := .affine, value := .localUnique }`,
    -- binder 1 has `{ uses := .many, value := .localShared }`, return `.localShared`
    let okAff :=
      affBcs.size == 2 &&
      affBcs[0]! == { uses := .affine, value := .localUnique } &&
      affBcs[1]! == { uses := .many, value := .localShared } &&
      affRet == .localShared
    -- Check `withBorrowLet`: let contract has `kind == .borrowShared`
    let okBor :=
      borLets.size == 1 &&
      borLets[0]!.kind == .borrowShared
    -- Also verify `Ix.SemanticContract` metadata frame attached to `linearUnique`'s type
    let okSemantic := match env.find? linName with
      | some (.defnInfo dval) =>
        match dval.cnst.type with
        | .mdata data (.forallE ..) _ =>
          match Ix.SemanticContract.read data with
          | .ok c => c.kind == .all && c.binder == { uses := .linear, value := .unique } && c.result == .unique
          | .error _ => false
        | _ => false
      | _ => false
    okLin && okEra && okAff && okBor && okSemantic

/-! ## 3. Order-Free & `mutual`-Free Declarations via Tarjan SCC -/

def testOrderFreeAndMutualFree : Bool :=
  -- Note: `caller` is declared BEFORE `callee`, `useShow` is declared BEFORE `instShowNat`,
  -- and `EvenN`/`OddN` are mutually recursive inductives without `mutual ... end`!
  let src := "
    def caller (x : Nat) : Nat := callee x

    def callee (x : Nat) : Nat := x

    inductive EvenN : Type
      | zero : EvenN
      | succOdd : OddN → EvenN

    inductive OddN : Type
      | succEven : EvenN → OddN

    class ShowVal (α : Type) : Type where
      tag : α → Nat

    def useShow (x : Nat) : Nat :=
      ShowVal.tag x

    instance instShowNat : ShowVal Nat where
      tag := fun n => n
  "
  match elabSource src with
  | .error _ => false
  | .ok env =>
    env.contains (Name.simple "caller") &&
    env.contains (Name.simple "callee") &&
    env.contains (Name.simple "EvenN") &&
    env.contains (Name.simple "OddN") &&
    env.contains (Name.mkStr2 "EvenN" "rec") &&
    env.contains (Name.mkStr2 "OddN" "rec") &&
    env.contains (Name.simple "useShow") &&
    env.contains (Name.simple "instShowNat")

/-! ## 4. In-Elaborator Canonicalization & Source-Order Tie-Breaking -/

def testConstructorCanonicalization : Bool :=
  -- 1. `RevNat` declares `succ` (1 field) BEFORE `zero` (0 fields).
  --    Canonicalization sorts by nameless structural skeleton (`numFields`),
  --    so `RevNat.zero` MUST receive `cidx = 0` and `RevNat.succ` MUST receive `cidx = 1`!
  -- 2. `MyBool` declares `false` (0 fields) then `true` (0 fields).
  --    Both constructors are structurally α-identical (`0` fields), so ties are broken by
  --    source declaration order: `MyBool.false` gets `cidx = 0` and `MyBool.true` gets `cidx = 1`!
  let src := "
    inductive RevNat : Type
      | succ : RevNat → RevNat
      | zero : RevNat

    inductive MyBool : Type
      | false : MyBool
      | true : MyBool
  "
  match elabSource src with
  | .error _ => false
  | .ok env =>
    let revZeroOk := match env.find? (Name.mkStr2 "RevNat" "zero") with
      | some (.ctorInfo cv) => cv.cidx == 0
      | _ => false
    let revSuccOk := match env.find? (Name.mkStr2 "RevNat" "succ") with
      | some (.ctorInfo cv) => cv.cidx == 1
      | _ => false
    let revIndOk := match env.find? (Name.simple "RevNat") with
      | some (.inductInfo iv) =>
        iv.ctors == #[Name.mkStr2 "RevNat" "zero", Name.mkStr2 "RevNat" "succ"]
      | _ => false
    let boolFalseOk := match env.find? (Name.mkStr2 "MyBool" "false") with
      | some (.ctorInfo cv) => cv.cidx == 0
      | _ => false
    let boolTrueOk := match env.find? (Name.mkStr2 "MyBool" "true") with
      | some (.ctorInfo cv) => cv.cidx == 1
      | _ => false
    revZeroOk && revSuccOk && revIndOk && boolFalseOk && boolTrueOk

/-! ## 5. Surgery-Free `AuxGen` & Structure Projections -/

def testAuxGenAndStructures : Bool :=
  let src := "
    structure PairNat : Type where
      fst : Nat
      snd : Nat

    def mkPair (a b : Nat) : PairNat :=
      { fst := a, snd := b }

    def sumPair (p : PairNat) : Nat :=
      Nat.add p.fst p.snd

    theorem proj_mkPair_fst (a b : Nat) : Eq (mkPair a b).fst a := by
      rfl
  "
  match elabSource src with
  | .error _ => false
  | .ok env =>
    env.contains (Name.simple "PairNat") &&
    env.contains (Name.mkStr2 "PairNat" "mk") &&
    env.contains (Name.mkStr2 "PairNat" "rec") &&
    env.contains (Name.mkStr2 "PairNat" "recOn") &&
    env.contains (Name.mkStr2 "PairNat" "casesOn") &&
    env.contains (Name.mkStr2 "PairNat" "_ctorIdx") &&
    env.contains (Name.mkStr2 "PairNat" "fst") &&
    env.contains (Name.mkStr2 "PairNat" "snd") &&
    env.contains (Name.simple "proj_mkPair_fst")

/-! ## 6. Structural Recursion (`recOn`) Lowering, Tactics, and `String`/`Nat` Acceleration -/

def testStructuralRecursionAndTactics : Bool :=
  let src := "
    def myAdd (n m : Nat) : Nat
      | 0 => m
      | Nat.succ k => Nat.succ (myAdd k m)

    theorem myAdd_zero_left (m : Nat) : Eq (myAdd 0 m) m := by
      rfl

    theorem myAdd_two_three : Eq (myAdd 2 3) 5 := by
      rfl

    theorem id_prop (P : Prop) (h : P) : P := by
      assumption

    theorem impl_refl (P : Prop) : P → P := by
      intro hp
      exact hp

    theorem str_accel_append : Eq (String.append \"ix-\" \"frontend\") \"ix-frontend\" := by
      rfl

    theorem str_accel_len : Eq (String.length \"hello\") 5 := by
      rfl

    theorem str_accel_utf8 : Eq (String.utf8ByteSize \"hello\") 5 := by
      rfl
  "
  match elabSource src with
  | .error _ => false
  | .ok env =>
    -- Verify `myAdd` was lowered to `Nat.recOn` (no self-reference to `myAdd` in its value!)
    let myAddName := Name.simple "myAdd"
    let isSelfRefFree := match env.find? myAddName with
      | some (.defnInfo dval) =>
        let refs := collectRefsInSet (NameSet.empty.insert myAddName) dval.value
        refs.isEmpty
      | _ => false
    isSelfRefFree &&
    env.contains (Name.simple "myAdd_zero_left") &&
    env.contains (Name.simple "myAdd_two_three") &&
    env.contains (Name.simple "id_prop") &&
    env.contains (Name.simple "impl_refl") &&
    env.contains (Name.simple "str_accel_append") &&
    env.contains (Name.simple "str_accel_len") &&
    env.contains (Name.simple "str_accel_utf8")

/-! ## 6b. Pure Tactic Engine (`Ix.Frontend.Elab.Tactic`) -/

def testPureTacticEngineResult : Except String Bool :=
  let src := "
    def myAdd (n m : Nat) : Nat
      | 0 => m
      | Nat.succ k => Nat.succ (myAdd k m)

    -- 1. Structured induction (`Nat.recOn`) + `rw [ih]` (`Eq.casesOn`)
    theorem myAdd_zero_right (n : Nat) : myAdd n 0 = n := by
      induction n with
      | zero => rfl
      | succ k ih => rw [ih]

    -- 2. Unstructured induction + `case` focus blocks
    theorem myAdd_zero_right_case (n : Nat) : myAdd n 0 = n := by
      induction n
      case zero => rfl
      case succ k ih =>
        rw [ih]
        done

    -- 3. `symm`, `trans`, `congr`, `rw [← h]`, and `rw [h] at hyp`
    theorem eq_symm_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : c = a := by
      symm
      trans b
      · exact h1
      · exact h2

    theorem eq_congr_succ (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := by
      congr
      exact h

    theorem rw_backward_and_at (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P a) : P b := by
      rw [h] at hp
      exact hp

    theorem rw_rev (a b : Nat) (h : a = b) : b = a := by
      rw [← h]

    -- 4. Logical connectives & combinators (`·`, `<;>`, `all_goals`, `first`, `try`, `repeat`)
    theorem and_comm_tac (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
      cases h with
      | intro hp hq =>
        constructor
        · exact hq
        · exact hp

    theorem or_comm_tac (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
      cases h with
      | inl hp =>
        right
        exact hp
      | inr hq =>
        left
        exact hq

    theorem comb_and_then (P : Prop) (hp : P) : P ∧ P := by
      constructor <;> assumption

    theorem comb_first_try (P Q : Prop) (hq : Q) : P ∨ Q := by
      first
      | left; assumption
      | right; try rfl; assumption

    -- 5. `contradiction`, `exfalso`, `trivial`, `exists`, `have`, `let`, `show`, `dsimp`, `simp`
    theorem absurd_tac (P Q : Prop) (hp : P) (hnp : ¬ P) : Q := by
      contradiction

    theorem exfalso_tac (P : Prop) (h : False) : P := by
      exfalso
      exact h

    theorem exists_witness : Exists (fun (n : Nat) => myAdd n 2 = 5) := by
      exists 3

    theorem have_let_show_simp (n : Nat) (h : n = 4) : myAdd 1 n = 5 := by
      let m : Nat := 1
      have hm : m = 1 := (by rfl)
      show myAdd 1 n = 5
      simp [h]
  "
  match compileSourceToIxon src "<tactics.ix>" IxElabEnv.empty defaultParserEnv true with
  | .error e => .error e
  | .ok (_stx, env, _ixonEnv, cenv) =>
    .ok (
      cenv.ungrounded.isEmpty &&
      env.contains (Name.simple "myAdd_zero_right") &&
      env.contains (Name.simple "myAdd_zero_right_case") &&
      env.contains (Name.simple "eq_symm_trans") &&
      env.contains (Name.simple "eq_congr_succ") &&
      env.contains (Name.simple "rw_backward_and_at") &&
      env.contains (Name.simple "rw_rev") &&
      env.contains (Name.simple "and_comm_tac") &&
      env.contains (Name.simple "or_comm_tac") &&
      env.contains (Name.simple "comb_and_then") &&
      env.contains (Name.simple "comb_first_try") &&
      env.contains (Name.simple "absurd_tac") &&
      env.contains (Name.simple "exfalso_tac") &&
      env.contains (Name.simple "exists_witness") &&
      env.contains (Name.simple "have_let_show_simp")
    )

def testPureTacticEngine : Bool :=
  match testPureTacticEngineResult with
  | .ok b => b
  | .error _ => false

/-! ## 6c. Advanced Frontend Features (`where`, `let rec`, Auto-Implicits, `deriving`, `extends`, `@[simp]`, `Coe`, Custom Operators) -/

def testAdvancedFrontendResult : Except String Bool :=
  let src := "
    -- 1. Auto-bound implicit parameters (`{α : Type}`, `{β : Type}`)
    def polyId (x : α) : α := x
    def polyConst (x : α) (y : β) : α := x

    theorem polyId_nat : polyId 7 = 7 := by rfl

    -- 2. `where` clauses and `let rec` local structural recursion (lowered to `Nat.recOn` + `.letE`)
    def doubleWithWhere (n : Nat) : Nat :=
      helper n
    where
      helper (k : Nat) : Nat
        | 0 => 0
        | Nat.succ m => Nat.succ (Nat.succ (helper m))

    theorem doubleWithWhere_three : doubleWithWhere 3 = 6 := by rfl

    def sumDownLetRec (n : Nat) : Nat :=
      let rec loop (k : Nat) : Nat
        | 0 => 0
        | Nat.succ m => Nat.add (Nat.succ m) (loop m);
      loop n

    theorem sumDownLetRec_three : sumDownLetRec 3 = 6 := by rfl

    -- 3. `deriving Inhabited, BEq` on `inductive` and `structure`
    inductive Color : Type
      | red : Color
      | green : Color
      | blue : Color
      deriving Inhabited, BEq

    structure Point2D : Type where
      x : Nat
      y : Nat
      deriving Inhabited, BEq

    theorem color_default_eq : (default : Color) = Color.red := by rfl
    theorem color_beq_self : (Color.green == Color.green) = true := by rfl
    theorem color_beq_diff : (Color.red == Color.blue) = false := by rfl
    theorem point_default_x : (default : Point2D).x = 0 := by rfl
    theorem point_beq_check : (Point2D.mk 2 3 == Point2D.mk 2 3) = true := by rfl

    -- 4. Structure & Class Inheritance (`extends`) with diamond deduplication & subobject coercion
    structure BaseX : Type where
      x : Nat

    structure LeftXY extends BaseX : Type where
      y : Nat

    structure RightXZ extends BaseX : Type where
      z : Nat

    structure DiamondXYZ extends LeftXY, RightXZ : Type where
      w : Nat

    def sumFromLeft (p : LeftXY) : Nat := Nat.add p.x p.y

    def mkDiamond : DiamondXYZ :=
      { x := 10, y := 20, z := 30, w := 40 }

    -- Subobject coercion `DiamondXYZ -> LeftXY` via `DiamondXYZ.toLeftXY`
    theorem diamond_coerces_to_left : sumFromLeft mkDiamond = 30 := by rfl

    -- 5. Attributes (`@[simp]`, `@[reducible]`) & Custom `prefix` / `postfix` / `infixl` operators
    @[reducible] def addOne (n : Nat) : Nat := Nat.succ n
    prefix:75 \"+++\" => addOne
    postfix:80 \"!+\" => addOne
    infixl:65 \" <+> \" => Nat.add

    theorem custom_ops_reduce : (+++ 2 !+ <+> 1) = 5 := by rfl

    def tagVal (n : Nat) : Nat := n
    @[simp] theorem tagVal_four : tagVal 4 = 4 := by rfl

    theorem simp_uses_attr : tagVal 4 = 4 := by
      simp

    -- 6. `Coe` typeclass coercion
    structure WrappedNat : Type where
      unbox : Nat

    instance instCoeWrappedNat : Coe WrappedNat Nat where
      coe w := w.unbox

    def takeNat (n : Nat) : Nat := n

    theorem coe_wrapped_nat : takeNat (WrappedNat.mk 42) = 42 := by rfl
  "
  match compileSourceToIxon src "<advanced.ix>" IxElabEnv.empty defaultParserEnv true with
  | .error e => .error e
  | .ok (_stx, env, _ixonEnv, cenv) =>
    .ok (
      cenv.ungrounded.isEmpty &&
      env.contains (Name.simple "polyId") &&
      env.contains (Name.simple "doubleWithWhere") &&
      env.contains (Name.simple "sumDownLetRec") &&
      env.contains (Name.simple "instInhabitedColor") &&
      env.contains (Name.simple "instBEqColor") &&
      env.contains (Name.simple "instInhabitedPoint2D") &&
      env.contains (Name.simple "instBEqPoint2D") &&
      env.contains (Name.mkStr2 "DiamondXYZ" "toLeftXY") &&
      env.contains (Name.mkStr2 "DiamondXYZ" "toRightXZ") &&
      env.contains (Name.simple "diamond_coerces_to_left") &&
      env.contains (Name.simple "custom_ops_reduce") &&
      env.contains (Name.simple "simp_uses_attr") &&
      env.contains (Name.simple "coe_wrapped_nat")
    )

def testAdvancedFrontend : Bool :=
  match testAdvancedFrontendResult with
  | .ok b => b
  | .error _ => false

/-! ## 7. Programmable Module Import Mapping (`map Name := #<hash>`) & `ElabClaim` -/

def testImportMapAndElabClaim : Bool := Id.run do
  -- First elaborate a small base definition `baseVal : Nat := 42`
  let baseSrc := "def baseVal : Nat := 42"
  match compileSourceToIxon baseSrc "<base>" IxElabEnv.empty defaultParserEnv true with
  | .error _ => return false
  | .ok (_stx, baseElabEnv, _ixonEnv, _cenv) =>
    let some baseCi := baseElabEnv.find? (Name.simple "baseVal") | return false
    let baseAddr := Address.blake3 "0123456789abcdef0123456789abcdef".toUTF8
    let initEnv := baseElabEnv.registerImportedConst baseAddr baseCi
    let hexAddr := toString baseAddr
    let clientSrc := s!"
      map Ext.answer := #{hexAddr}
      def doubleAnswer : Nat := Ext.answer
    "
    let importMapOk := match elabSource clientSrc "<client>" initEnv true with
      | .error _ => false
      | .ok clientEnv => clientEnv.contains (Name.simple "doubleAnswer")
    -- Test `ElabClaim` roundtrip & pure verification on `baseSrc`
    let claimOk := match mkElabClaimFromSource baseSrc default none "<base>" IxElabEnv.empty defaultParserEnv true with
      | .error _ => false
      | .ok (claim, _, _, _) =>
        let bytes := ElabClaim.ser claim
        let roundtripOk := match ElabClaim.de bytes with
          | .ok claim' => claim == claim'
          | .error _ => false
        let verifyOk := match verifyElabClaimPure claim baseSrc "<base>" IxElabEnv.empty defaultParserEnv true with
          | .ok b => b
          | .error _ => false
        let tamperOk := match verifyElabClaimPure claim "def baseVal : Nat := 43" "<base>" IxElabEnv.empty defaultParserEnv true with
          | .ok b => !b
          | .error _ => false
        roundtripOk && verifyOk && tamperOk
    return importMapOk && claimOk

/-! ## 8. Kernel-Level `rfl` Reduction Proofs (`parseSource`, `buildModuleIndex`, `elabModuleSyntax`) -/

/-- Lean's kernel reduces `InputContext` + identifier/number scanning by definitional equality (`rfl`). -/
theorem kernel_lexer_reduces :
    let ctx := InputContext.mkInputContext "  def idNat := 42" "<kernel>"
    let pos0 := skipWhitespace ctx 0
    (scanOneIdentComponent ctx pos0, parseNatLiteral "42") =
      (some ("def", 5), some 42) := rfl

/-- Lean's kernel reduces `tarjanCondensation` (Tarjan SCC + topological sort) by `rfl`. -/
theorem kernel_tarjan_scc_reduces :
    (match tarjanCondensation #[#[1], #[2], #[1]] with
     | some c => c.comps
     | none   => #[]) = #[#[1, 2], #[0]] := rfl

/-- Kernel-level reduction theorems for `String` operations accelerated in `IxVM` (`Whnf.lean` & `NatPrim.lean`). -/
theorem str_accel_append_reduces :
    String.append "ix-" "frontend" = "ix-frontend" := rfl

theorem str_accel_length_reduces :
    String.length "ix-frontend" = 11 := rfl

theorem str_accel_utf8_reduces :
    String.utf8ByteSize "ix-frontend" = 11 := rfl

/-- Minimal `IxParserEnv` for kernel-level `rfl` reduction of `parseSource` and `elabModuleSyntax`. -/
def minKernelParserEnv : IxParserEnv :=
  { tokens    := Trie.ofSymbols ["(", ")", ":", ":="]
    keywords  := (Trie.empty.insert "def" true).insert "Type" true
    operators := [] }

/-- End-to-end pure parsing predicate reduced by Lean's kernel. -/
def kernelParseCheck : Bool :=
  match parseSource "def id (x : Type) : Type := x" "<kernel>" minKernelParserEnv with
  | .ok (stx, _) => (Syntax.getArgs stx).size == 1
  | .error _ => false

/-- End-to-end Pass 1 (`buildModuleIndex`) predicate reduced by Lean's kernel. -/
def kernelScopeCheck : Bool :=
  match do
    let (stx, _) ← parseSource "def id (x : Type) : Type := x" "<kernel>" minKernelParserEnv
    buildModuleIndex stx
  with
  | .ok modIdx => modIdx.decls.size == 1
  | .error _ => false

/-- End-to-end 4-pass elaboration (`parseSource` + `elabModuleSyntax`) predicate reduced by Lean's kernel. -/
def kernelElabCheck : Bool :=
  match do
    let (stx, _) ← parseSource "def id (x : Type) : Type := x" "<kernel>" minKernelParserEnv
    elabModuleSyntax stx IxElabEnv.empty false
  with
  | .ok env => env.consts.contains (Name.simple "id")
  | .error _ => false

/-! ## 8b. Fermat's Last Theorem Proposition (`AnthropicFLT` `FinalCheck.lean`) Elaboration & Ixon Hash Proof -/

/-- Reference Lean 4 declaration of `flt_pinned` matching `anthropics/fermats-last-theorem` (`FinalCheck.lean`). -/
axiom flt_pinned (n : Nat) (hn : 3 ≤ n) (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ n + b ^ n ≠ c ^ n

/-- Reference Lean 4 declaration of `FermatLastTheorem` matching `anthropics/fermats-last-theorem` (`FinalCheck.lean`). -/
def FermatLastTheorem : Prop :=
  ∀ (n : Nat), n > 2 → ∀ (a b c : Nat), a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- Exact human-readable source text of the Fermat's Last Theorem proposition from `FinalCheck.lean`. -/
def fltSourceText : String :=
  "axiom flt_pinned (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n\ndef FermatLastTheorem : Prop := ∀ n : ℕ, n > 2 → ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n"

/-- Focused `IxParserEnv` for fast kernel-level `rfl` reduction of `fltSourceText`. -/
def fltKernelParserEnv : IxParserEnv :=
  { tokens := Trie.ofSymbols ["(", ")", ":", ":=", ",", "→", "∀", "≤", "<", ">", "^", "+", "≠"]
    keywords := (((Trie.empty.insert "axiom" true).insert "def" true).insert "Prop" true).insert "∀" true
    operators := [
      { symbol := "^", prec := 80, fixity := .infixr, kind := SyntaxKind.binOpTerm, targetFn := some (Name.mkStr2 "HPow" "hPow") },
      { symbol := "+", prec := 65, fixity := .infixl, kind := SyntaxKind.binOpTerm, targetFn := some (Name.mkStr2 "HAdd" "hAdd") },
      { symbol := "≤", prec := 50, fixity := .infixn, kind := SyntaxKind.binOpTerm, targetFn := some (Name.mkStr2 "LE" "le") },
      { symbol := "<", prec := 50, fixity := .infixn, kind := SyntaxKind.binOpTerm, targetFn := some (Name.mkStr2 "LT" "lt") },
      { symbol := ">", prec := 50, fixity := .infixn, kind := SyntaxKind.binOpTerm, targetFn := some (Name.mkStr2 "GT" "gt") },
      { symbol := "≠", prec := 50, fixity := .infixn, kind := SyntaxKind.binOpTerm, targetFn := some (Name.simple "Ne") }
    ] }

/-- Construct the exact expected `Ix.Expr` for `(flt_pinned.type, FermatLastTheorem.value)`. -/
def mkExpectedFltExprs : Ix.Expr × Ix.Expr :=
  let z := Ix.Frontend.Level.mkZero
  let one := Ix.Frontend.Level.mkSucc z
  let nat := Ix.Frontend.Expr.mkConst (Name.simple "Nat") #[]
  let mkNatOfNat (k : Nat) : Ix.Expr :=
    let raw := Ix.Frontend.Expr.mkNatLit k
    let inst := Ix.Frontend.Expr.mkApp (Ix.Frontend.Expr.mkConst (Name.simple "instOfNatNat") #[]) raw
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "OfNat" "ofNat") #[z]) #[nat, raw, inst]
  let mkNatPow (base exp : Ix.Expr) : Ix.Expr :=
    let instNatPow := Ix.Frontend.Expr.mkConst (Name.simple "instNatPowNat") #[]
    let instPow := Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.simple "instPowNat") #[z]) #[nat, instNatPow]
    let instHPow := Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.simple "instHPow") #[z, z]) #[nat, nat, instPow]
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "HPow" "hPow") #[z, z, z]) #[nat, nat, nat, instHPow, base, exp]
  let mkNatAdd (lhs rhs : Ix.Expr) : Ix.Expr :=
    let instAdd := Ix.Frontend.Expr.mkConst (Name.simple "instAddNat") #[]
    let instHAdd := Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.simple "instHAdd") #[z]) #[nat, instAdd]
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "HAdd" "hAdd") #[z, z, z]) #[nat, nat, nat, instHAdd, lhs, rhs]
  let mkNatNe (lhs rhs : Ix.Expr) : Ix.Expr :=
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.simple "Ne") #[one]) #[nat, lhs, rhs]
  let mkNatLe (lhs rhs : Ix.Expr) : Ix.Expr :=
    let instLE := Ix.Frontend.Expr.mkConst (Name.simple "instLENat") #[]
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "LE" "le") #[z]) #[nat, instLE, lhs, rhs]
  let mkNatLt (lhs rhs : Ix.Expr) : Ix.Expr :=
    let instLT := Ix.Frontend.Expr.mkConst (Name.simple "instLTNat") #[]
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "LT" "lt") #[z]) #[nat, instLT, lhs, rhs]
  let mkNatGt (lhs rhs : Ix.Expr) : Ix.Expr :=
    let instLT := Ix.Frontend.Expr.mkConst (Name.simple "instLTNat") #[]
    Ix.Frontend.Expr.mkAppN (Ix.Frontend.Expr.mkConst (Name.mkStr2 "GT" "gt") #[z]) #[nat, instLT, lhs, rhs]
  -- Under 8 binders (n, hn, a, b, c, ha, hb, hc): n=#7, a=#5, b=#4, c=#3
  let body :=
    mkNatNe
      (mkNatAdd (mkNatPow (Ix.Frontend.Expr.mkBVar 5) (Ix.Frontend.Expr.mkBVar 7)) (mkNatPow (Ix.Frontend.Expr.mkBVar 4) (Ix.Frontend.Expr.mkBVar 7)))
      (mkNatPow (Ix.Frontend.Expr.mkBVar 3) (Ix.Frontend.Expr.mkBVar 7))
  let lit0 := mkNatOfNat 0
  let lit2 := mkNatOfNat 2
  let lit3 := mkNatOfNat 3
  let pinnedTy :=
    Ix.Frontend.Expr.mkForallE (Name.simple "n") nat
      (Ix.Frontend.Expr.mkForallE (Name.simple "hn") (mkNatLe lit3 (Ix.Frontend.Expr.mkBVar 0))
        (Ix.Frontend.Expr.mkForallE (Name.simple "a") nat
          (Ix.Frontend.Expr.mkForallE (Name.simple "b") nat
            (Ix.Frontend.Expr.mkForallE (Name.simple "c") nat
              (Ix.Frontend.Expr.mkForallE (Name.simple "ha") (mkNatLt lit0 (Ix.Frontend.Expr.mkBVar 2))
                (Ix.Frontend.Expr.mkForallE (Name.simple "hb") (mkNatLt lit0 (Ix.Frontend.Expr.mkBVar 2))
                  (Ix.Frontend.Expr.mkForallE (Name.simple "hc") (mkNatLt lit0 (Ix.Frontend.Expr.mkBVar 2))
                    body .default) .default) .default) .default) .default) .default) .default) .default
  let fltDefVal :=
    Ix.Frontend.Expr.mkForallE (Name.simple "n") nat
      (Ix.Frontend.Expr.mkForallE Ix.Frontend.Name.mkAnon (mkNatGt (Ix.Frontend.Expr.mkBVar 0) lit2)
        (Ix.Frontend.Expr.mkForallE (Name.simple "a") nat
          (Ix.Frontend.Expr.mkForallE (Name.simple "b") nat
            (Ix.Frontend.Expr.mkForallE (Name.simple "c") nat
              (Ix.Frontend.Expr.mkForallE Ix.Frontend.Name.mkAnon (mkNatNe (Ix.Frontend.Expr.mkBVar 2) lit0)
                (Ix.Frontend.Expr.mkForallE Ix.Frontend.Name.mkAnon (mkNatNe (Ix.Frontend.Expr.mkBVar 2) lit0)
                  (Ix.Frontend.Expr.mkForallE Ix.Frontend.Name.mkAnon (mkNatNe (Ix.Frontend.Expr.mkBVar 2) lit0)
                    body .default) .default) .default) .default) .default) .default) .default) .default
  (pinnedTy, fltDefVal)

/-- Pure kernel-level check that `fltSourceText` parses and elaborates to `mkExpectedFltExprs`. -/
def kernelFltPropCheck : Bool :=
  match do
    let (stx, _) ← parseSource fltSourceText "<FinalCheck.ix>" fltKernelParserEnv
    elabModuleSyntax stx (seedLeanInitArith IxElabEnv.empty) false
  with
  | .ok env =>
    let (expPinnedTy, expFltVal) := mkExpectedFltExprs
    let okPinned := match env.find? (Name.simple "flt_pinned") with
      | some (.axiomInfo aval) => aval.cnst.type == expPinnedTy
      | _ => false
    let okDef := match env.find? (Name.simple "FermatLastTheorem") with
      | some (.defnInfo dval) =>
        dval.cnst.type == Ix.Frontend.Expr.mkProp &&
        dval.value == expFltVal
      | _ => false
    okPinned && okDef
  | .error _ => false

/-- Pre-built `ElabHints` certificate for `fltSourceText` (`flt_pinned` + `FermatLastTheorem`). -/
def fltPropHints : Ix.Frontend.Elab.ElabHints :=
  let (expPinnedTy, expFltVal) := mkExpectedFltExprs
  let h0 := Ix.Frontend.Elab.ElabHints.empty
  let h1 := h0.insert {
    fullName    := Name.simple "flt_pinned"
    levelParams := #[]
    «type»      := expPinnedTy
    value?      := none
  }
  h1.insert {
    fullName    := Name.simple "FermatLastTheorem"
    levelParams := #[]
    «type»      := Ix.Frontend.Expr.mkProp
    value?      := some expFltVal
    defKind     := .defn
    hints       := .regular 1
  }

/-- Pure kernel-level check that `fltSourceText` parses and verifies via `elabModuleWithHints`
    (Track 2 certificate-guided `O(|stx|)` elaboration, zero metavariables) to `mkExpectedFltExprs`,
    while rejecting tampered hints. -/
def kernelFltHintedCheck : Bool :=
  match do
    let (stx, _) ← parseSource fltSourceText "<FinalCheck.ix>" fltKernelParserEnv
    elabModuleWithHints stx fltPropHints (seedLeanInitArith IxElabEnv.empty) false
  with
  | .ok env =>
    let (expPinnedTy, expFltVal) := mkExpectedFltExprs
    let okPinned := match env.find? (Name.simple "flt_pinned") with
      | some (.axiomInfo aval) => aval.cnst.type == expPinnedTy
      | _ => false
    let okDef := match env.find? (Name.simple "FermatLastTheorem") with
      | some (.defnInfo dval) =>
        dval.cnst.type == Ix.Frontend.Expr.mkProp &&
        dval.value == expFltVal
      | _ => false
    okPinned && okDef
  | .error _ => false

/-- Host-level check that `fltSourceText` elaborates under the full `defaultParserEnv`
    and produces the exact expected Merkle `Address` digests. -/
def testFltPropositionElab : Bool :=
  match elabSource fltSourceText "<FinalCheck.ix>" (seedLeanInitArith IxElabEnv.empty) false with
  | .ok env =>
    let (expPinnedTy, expFltVal) := mkExpectedFltExprs
    let okPinned := match env.find? (Name.simple "flt_pinned") with
      | some (.axiomInfo aval) =>
        aval.cnst.type == expPinnedTy &&
        (Ix.Frontend.Expr.rehash aval.cnst.type).getHash == (Ix.Frontend.Expr.rehash expPinnedTy).getHash
      | _ => false
    let okDef := match env.find? (Name.simple "FermatLastTheorem") with
      | some (.defnInfo dval) =>
        dval.cnst.type == Ix.Frontend.Expr.mkProp &&
        dval.value == expFltVal &&
        (Ix.Frontend.Expr.rehash dval.value).getHash == (Ix.Frontend.Expr.rehash expFltVal).getHash
      | _ => false
    okPinned && okDef
  | .error _ => false

/-- Verify that `fltSourceText` elaborated via `Ix.Frontend` and compiled via pure Lean `Ix.CompileM`
    produces the exact same 32-byte `Ixon.Constant` content `Address` as Lean 4's `flt_pinned` and `FermatLastTheorem`. -/
def verifyFltIxonAddressParity (leanEnv : Lean.Environment) : IO (Bool × String) := do
  let fltTargets : List Lean.Name := [``flt_pinned, ``FermatLastTheorem]
  let depClosure := Ix.EnvScope.collectDeps leanEnv fltTargets
  let leanPhases ← Ix.CompileM.rsCompilePhasesOf depClosure
  let pinnedIxName := Name.rehash (Name.simple "flt_pinned")
  let fltDefIxName := Name.rehash (Name.simple "FermatLastTheorem")
  let some leanPinnedAddr := leanPhases.compileEnv.getAddr? pinnedIxName
    | throw (IO.userError "flt_pinned not found in Lean Ixon.Env")
  let some leanFltDefAddr := leanPhases.compileEnv.getAddr? fltDefIxName
    | throw (IO.userError "FermatLastTheorem not found in Lean Ixon.Env")
  -- Populate `baseElabEnv` with the `Init` dependency constants from `leanPhases.rawEnv`
  -- (excluding `flt_pinned` and `FermatLastTheorem` so `Ix.Frontend` elaborates them from text!)
  let mut baseElabEnv := IxElabEnv.empty
  for (nm, ci) in leanPhases.rawEnv.consts.toList do
    if nm != pinnedIxName && nm != fltDefIxName then
      baseElabEnv := baseElabEnv.addConst ci
  baseElabEnv := registerLeanInitArithInstances baseElabEnv
  -- Elaborate `fltSourceText` from raw string and compile to `Ixon.Env` via pure Lean `Ix.CompileM`!
  let (_, _, ixFrontendIxonEnv, _) ← IO.ofExcept (
    compileSourceToIxon fltSourceText "<FinalCheck.ix>" baseElabEnv defaultParserEnv false)
  let some ixPinnedAddr := ixFrontendIxonEnv.getAddr? pinnedIxName
    | throw (IO.userError "flt_pinned not found in Ix.Frontend Ixon.Env")
  let some ixFltDefAddr := ixFrontendIxonEnv.getAddr? fltDefIxName
    | throw (IO.userError "FermatLastTheorem not found in Ix.Frontend Ixon.Env")
  let ok := (ixPinnedAddr == leanPinnedAddr) && (ixFltDefAddr == leanFltDefAddr)
  let summary :=
    s!"[AnthropicFLT Proposition Text -> Ixon Content Address Proof]\n" ++
    s!"  • Source: {fltSourceText.replace "\n" "\n            "}\n" ++
    s!"  • flt_pinned        (Lean 4):      #{leanPinnedAddr}\n" ++
    s!"  • flt_pinned        (Ix.Frontend): #{ixPinnedAddr} (match={ixPinnedAddr == leanPinnedAddr})\n" ++
    s!"  • FermatLastTheorem (Lean 4):      #{leanFltDefAddr}\n" ++
    s!"  • FermatLastTheorem (Ix.Frontend): #{ixFltDefAddr} (match={ixFltDefAddr == leanFltDefAddr})"
  return (ok, summary)

-- Verify `kernel_parse_reduces`, `kernel_scope_reduces`, `kernel_elab_reduces`, `kernel_flt_prop_reduces`,
-- and `kernel_flt_hinted_reduces` directly in Lean's C++ kernel with `@Eq.refl Bool true`.
run_meta do
  let boolTy := Lean.mkConst ``Bool
  let trueVal := Lean.mkConst ``Bool.true
  let eqReflTrue := Lean.mkApp2 (Lean.mkConst ``Eq.refl [Lean.Level.succ Lean.Level.zero]) boolTy trueVal
  for (thmName, lhsConst) in [
    (`kernel_parse_reduces,      ``kernelParseCheck),
    (`kernel_scope_reduces,      ``kernelScopeCheck),
    (`kernel_elab_reduces,       ``kernelElabCheck),
    (`kernel_flt_prop_reduces,   ``kernelFltPropCheck),
    (`kernel_flt_hinted_reduces, ``kernelFltHintedCheck)
  ] do
    let eqTy := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero]) boolTy (Lean.mkConst lhsConst) trueVal
    Lean.addDecl (.thmDecl {
      name := thmName
      levelParams := []
      «type» := eqTy
      value := eqReflTrue
    })

/-! ## 8c. Test 11: `IxVCS` AST & Type-Aware Module Merge Engine (`Ix.Frontend.Merge`) -/

def testIxVCSMergeEngineResult : Except String Bool := do
  -- 11A. First-class `.#merge` identifiers and `#merge | _1 => ... | _2 => ... end` conflict block syntax
  let surfaceConflictSrc := "
    #merge
      | _1 => def Acme.foobar : Nat := 42
      | _2 => def Acme.foobar : String := \"hello\"
    end
    def Acme.use1 : Nat := Acme.foobar.#merge._1 + 8
    def Acme.use2 : String := Acme.foobar.#merge._2
    theorem Acme.use1_eq : Eq Acme.use1 50 := by rfl
  "
  let (stxSurf, _) ← parseSource surfaceConflictSrc "<surface_conflict>"
  let modIdxSurf ← buildModuleIndex stxSurf
  let variantsSurf := modIdxSurf.findConflictVariants (Name.mkStr2 "Acme" "foobar")
  if variantsSurf.length != 2 then
    throw s!"11A failed: expected 2 conflict variants for Acme.foobar, got {variantsSurf.length}"
  let envSurf ← elabSource surfaceConflictSrc "<surface_conflict>"
  let nFoobar1 := Name.mkMergeVariant (Name.mkStr2 "Acme" "foobar") "_1"
  let nFoobar2 := Name.mkMergeVariant (Name.mkStr2 "Acme" "foobar") "_2"
  if !envSurf.contains nFoobar1 || !envSurf.contains nFoobar2 || !envSurf.contains (Name.mkStr2 "Acme" "use1_eq") then
    throw "11A failed: surface #merge block did not elaborate expected conflict variants"

  -- 11B. 2-way disambiguating merge (`mergeSource2`) on conflicting `def Acme.foobar : Nat := 42` vs `String := "hello"`
  let srcX := "
    def Acme.sharedBase : Nat := 100
    def Acme.foobar : Nat := 42
    def Acme.useInX : Nat := Acme.foobar + Acme.sharedBase
  "
  let srcY := "
    def Acme.sharedBase : Nat := 100
    def Acme.foobar : String := \"hello\"
    def Acme.useInY : String := Acme.foobar
  "
  -- Default `.mergeIndexed` mode (`Acme.foobar.#merge._1` and `Acme.foobar.#merge._2`)
  let outXY ← mergeSource2 srcX srcY .mergeIndexed
  let outYX ← mergeSource2 srcY srcX .mergeIndexed
  if outXY.conflicts.size != 1 then
    throw s!"11B failed: expected 1 conflict in outXY, got {outXY.conflicts.size}"
  -- Verify strict commutativity: `mergeSource2 srcX srcY` and `mergeSource2 srcY srcX` produce identical schedules!
  let namesXY := outXY.sched.modIdx.decls.toList.map (·.fullName)
  let namesYX := outYX.sched.modIdx.decls.toList.map (·.fullName)
  if namesXY != namesYX then
    throw "11B failed: mergeSource2 is not commutative on declaration names"
  let envXY ← outXY.elaborate
  let envYX ← outYX.elaborate
  if !envXY.contains nFoobar1 || !envXY.contains nFoobar2 ||
     !envXY.contains (Name.mkStr2 "Acme" "useInX") || !envXY.contains (Name.mkStr2 "Acme" "useInY") ||
     !envXY.contains (Name.mkStr2 "Acme" "sharedBase") then
    throw "11B failed: merged module missing expected declarations"
  for nm in namesXY do
    match envXY.find? nm, envYX.find? nm with
    | some ci1, some ci2 =>
      let c1 := (Ix.Frontend.Expr.ConstantInfo.rehash ci1).getCnst
      let c2 := (Ix.Frontend.Expr.ConstantInfo.rehash ci2).getCnst
      if c1.name.getHash != c2.name.getHash || c1.type.getHash != c2.type.getHash then
        throw s!"11B failed: constant {Name.toStringTotal nm} has different Merkle hash under XY vs YX"
    | _, _ =>
      throw s!"11B failed: constant {Name.toStringTotal nm} missing in elaborated env"

  -- Verify idempotence: `mergeSource2 srcX srcX` produces 0 conflicts
  let outXX ← mergeSource2 srcX srcX .mergeIndexed
  if !outXX.conflicts.isEmpty then
    throw "11B failed: mergeSource2 srcX srcX was not idempotent (produced conflicts)"

  -- Verify `.namespacePrefix` mode (`X.Acme.foobar` and `Y.Acme.foobar`)
  let outPref ← mergeSource2 srcX srcY (.namespacePrefix (Name.simple "X") (Name.simple "Y"))
  let envPref ← outPref.elaborate
  if !envPref.contains (Name.mkStr3 "X" "Acme" "foobar") ||
     !envPref.contains (Name.mkStr3 "Y" "Acme" "foobar") then
    throw "11B failed: namespacePrefix mode did not produce X.Acme.foobar and Y.Acme.foobar"

  -- 11C. 2-way merge on conflicting `inductive Acme.Expr` + pattern-matching & recursive `Acme.eval`
  let indX := "
    namespace Acme
    inductive Expr : Type
      | lit (n : Nat) : Expr
      | add (a b : Expr) : Expr
    def eval (e : Expr) : Nat
      | Expr.lit n => n
      | Expr.add a b => eval a + eval b
    def testEvalX : Nat := eval (Expr.add (Expr.lit 2) (Expr.lit 3))
    end Acme
  "
  let indY := "
    namespace Acme
    inductive Expr : Type
      | flag (b : Bool) : Expr
    def eval (e : Expr) : Bool
      | Expr.flag b => b
    def testEvalY : Bool := eval (Expr.flag true)
    end Acme
  "
  let outInd ← mergeSource2 indX indY .mergeIndexed
  let envInd ← outInd.elaborate
  let nExpr1 := Name.mkMergeVariant (Name.mkStr2 "Acme" "Expr") "_1"
  let nExpr2 := Name.mkMergeVariant (Name.mkStr2 "Acme" "Expr") "_2"
  let nEval1 := Name.mkMergeVariant (Name.mkStr2 "Acme" "eval") "_1"
  let nEval2 := Name.mkMergeVariant (Name.mkStr2 "Acme" "eval") "_2"
  if !envInd.contains nExpr1 || !envInd.contains nExpr2 ||
     !envInd.contains nEval1 || !envInd.contains nEval2 ||
     !envInd.contains (Name.mkStr2 "Acme" "testEvalX") ||
     !envInd.contains (Name.mkStr2 "Acme" "testEvalY") then
    throw "11C failed: inductive + pattern-matching merge missing expected declarations"

  -- 11D. Intra-Declaration Proof Irrelevance Absorption (`Prop` theorems with different proofs unify with 0 conflicts)
  let thmBranch1 := "
    def Acme.double (n : Nat) : Nat := n + n
    theorem Acme.double_two : Eq (Acme.double 2) 4 := by rfl
  "
  let thmBranch2 := "
    def Acme.double (n : Nat) : Nat := n + n
    theorem Acme.double_two : Eq (Acme.double 2) 4 := Eq.refl 4
  "
  let outThm ← mergeSource2 thmBranch1 thmBranch2 .mergeIndexed
  if !outThm.conflicts.isEmpty then
    throw s!"11D failed: proof-irrelevant theorem merge produced {outThm.conflicts.size} conflicts instead of 0"
  let envThm ← outThm.elaborate
  if !envThm.contains (Name.mkStr2 "Acme" "double_two") then
    throw "11D failed: unified theorem Acme.double_two missing"

  -- 11E. 3-Way Merge (`mergeSource3`) — Case B: 1-sided body update where Right's caller still typechecks (fast-forward!)
  let base3 := "
    def Acme.foobar : Nat := 1
  "
  let left3B := "
    def Acme.foobar : Nat := 2
    def Acme.leftCaller : Nat := Acme.foobar + 100
  "
  let right3B := "
    def Acme.foobar : Nat := 1
    def Acme.rightCaller : Nat := Acme.foobar + 10
  "
  let out3B ← mergeSource3 base3 left3B right3B .mergeIndexed
  if !out3B.conflicts.isEmpty then
    throw s!"11E (Case B) failed: expected 0 conflicts on fast-forward body update, got {out3B.conflicts.size}"
  let env3B ← out3B.elaborate
  if !env3B.contains (Name.mkStr2 "Acme" "foobar") ||
     !env3B.contains (Name.mkStr2 "Acme" "leftCaller") ||
     !env3B.contains (Name.mkStr2 "Acme" "rightCaller") then
    throw "11E (Case B) failed: fast-forwarded module missing expected declarations"

  -- 11F. 3-Way Merge (`mergeSource3`) — Case C: 1-sided body update that would break Right's `rfl` proof
  -- Must be treated as a semantic conflict and split into `Acme.foobar.#merge._1` and `Acme.foobar.#merge._2`!
  let right3C := "
    def Acme.foobar : Nat := 1
    theorem Acme.right_eq : Eq (Acme.foobar + 10) 11 := by rfl
  "
  let out3C ← mergeSource3 base3 left3B right3C .mergeIndexed
  if out3C.conflicts.size != 1 || !(out3C.conflicts.getD 0 default).isSemanticConflict then
    throw s!"11F (Case C) failed: expected 1 semantic conflict when body change breaks caller rfl proof, got {out3C.conflicts.size}"
  let env3C ← out3C.elaborate
  if !env3C.contains nFoobar1 || !env3C.contains nFoobar2 ||
     !env3C.contains (Name.mkStr2 "Acme" "leftCaller") ||
     !env3C.contains (Name.mkStr2 "Acme" "right_eq") then
    throw "11F (Case C) failed: semantic conflict split did not preserve both leftCaller and right_eq"

  -- 11G. 3-Way Merge (`mergeSource3`) — Case D: 1-sided type signature change that would break Right's caller
  let left3D := "
    def Acme.foobar : String := \"changed\"
    def Acme.leftStr : String := Acme.foobar
  "
  let out3D ← mergeSource3 base3 left3D right3B .mergeIndexed
  if out3D.conflicts.size != 1 || !(out3D.conflicts.getD 0 default).isSemanticConflict then
    throw s!"11G (Case D) failed: expected 1 semantic conflict when type change breaks caller, got {out3D.conflicts.size}"
  let env3D ← out3D.elaborate
  if !env3D.contains nFoobar1 || !env3D.contains nFoobar2 ||
     !env3D.contains (Name.mkStr2 "Acme" "leftStr") ||
     !env3D.contains (Name.mkStr2 "Acme" "rightCaller") then
    throw "11G (Case D) failed: type-change conflict split did not preserve both leftStr and rightCaller"

  -- 11H. 3-Way Keyed AST Splice (`tryMergeDeclSyntax3` on disjoint `match` arms)
  let baseMatch := "
    inductive Tag : Type
      | a : Tag
      | b : Tag
    def evalTag (t : Tag) : Nat
      | Tag.a => 1
      | Tag.b => 2
  "
  let leftMatch := "
    inductive Tag : Type
      | a : Tag
      | b : Tag
    def evalTag (t : Tag) : Nat
      | Tag.a => 10
      | Tag.b => 2
  "
  let rightMatch := "
    inductive Tag : Type
      | a : Tag
      | b : Tag
    def evalTag (t : Tag) : Nat
      | Tag.a => 1
      | Tag.b => 20
  "
  let outMatch ← mergeSource3 baseMatch leftMatch rightMatch .mergeIndexed
  if !outMatch.conflicts.isEmpty then
    throw s!"11H failed: expected 0 conflicts on disjoint match-arm 3-way splice, got {outMatch.conflicts.size}"
  let envMatch ← outMatch.elaborate
  if !envMatch.contains (Name.simple "evalTag") then
    throw "11H failed: spliced evalTag missing in elaborated env"

  -- 11I. Conflict Resolution (`resolveConflictVariant`)
  let resolvedSched ← resolveConflictVariant out3C.sched (Name.mkStr2 "Acme" "foobar")
    -- Pick whichever tag corresponds to `1` (`right3C`'s variant) so `Acme.right_eq` and `Acme.leftCaller` both typecheck!
    (match out3C.rightRenaming.get? (Name.mkStr2 "Acme" "foobar") with
     | some rName => match Name.splitMergeVariant? rName with
       | some (_, tag, []) => tag
       | _ => "_2"
     | none => "_2")
  let resolvedEnv ← match elabModuleSchedule resolvedSched IxElabEnv.empty true with
    | .ok e => pure e
    | .error err => throw s!"11I failed: resolved schedule failed to elaborate: {err}"
  if !resolvedEnv.contains (Name.mkStr2 "Acme" "foobar") ||
     resolvedEnv.contains nFoobar1 || resolvedEnv.contains nFoobar2 then
    throw "11I failed: resolveConflictVariant did not collapse conflict variants back to Acme.foobar"

  return true

def testIxVCSMergeEngine : Bool :=
  match testIxVCSMergeEngineResult with
  | .ok b    => b
  | .error _ => false

/-! ## 9. Step 1: Closure Certification Gate (`parseSource`, `elabSource`, `mergeSource2`, `mergeSource3`) -/

/-- Pure transitive closure audit over `leanEnv` for `parseSource`, `elabSource`, `mergeSource2`, and `mergeSource3`. -/
def checkClosureCertification (leanEnv : Lean.Environment) : Bool × String := Id.run do
  let parseClosure : List (Lean.Name × Lean.ConstantInfo) := Ix.EnvScope.collectDeps leanEnv [``parseSource]
  let elabClosure  : List (Lean.Name × Lean.ConstantInfo) :=
    Ix.EnvScope.collectDeps leanEnv [``elabSource, ``elabSourceWithHints, ``mergeSource2, ``mergeSource3, ``formatSyntax, ``elabModuleDAG]
  let isBad (ci : Lean.ConstantInfo) : Option String :=
    match ci with
    | .defnInfo v =>
      match v.safety with
      | .unsafe  => some "unsafe def"
      | .partial => some "partial def"
      | .safe    => none
    | .opaqueInfo v => if v.isUnsafe then some "unsafe opaque" else none
    | .axiomInfo v  => if v.isUnsafe then some "unsafe axiom" else none
    | .inductInfo v => if v.isUnsafe then some "unsafe induct" else none
    | .ctorInfo v   => if v.isUnsafe then some "unsafe ctor" else none
    | .recInfo v    => if v.isUnsafe then some "unsafe rec" else none
    | _ => none
  let badParse := parseClosure.filterMap fun (p : Lean.Name × Lean.ConstantInfo) => (isBad p.2).map (fun r => (p.1, r))
  let badElab  := elabClosure.filterMap fun (p : Lean.Name × Lean.ConstantInfo) => (isBad p.2).map (fun r => (p.1, r))
  let allowedAxioms : List Lean.Name := [``propext, ``Quot.sound, ``Classical.choice]
  let axiomsElab := elabClosure.filterMap fun (p : Lean.Name × Lean.ConstantInfo) =>
    match p.2 with
    | .axiomInfo _ => some p.1
    | _ => none
  let disallowedAxioms := axiomsElab.filter fun a => !allowedAxioms.contains a
  let bannedOpaques : List String := [
    "Lean.opaqueId",
    "WellFounded.opaqueFix",
    "_private.Init.While.0.Lean.Loop.forIn.loop",
    "_private.Init.While.0.repeatM.impl",
    "Blake3.Rust.Hasher.init",
    "String.append",
    "String.Internal.append"
  ]
  let mut bannedCallers : List (String × List Lean.Name) := []
  for targetOpaqueStr in bannedOpaques do
    let callers := elabClosure.filterMap fun (p : Lean.Name × Lean.ConstantInfo) =>
      if p.1 == `mkPanicMessageWithDecl then
        none
      else
        match p.2.value? (allowOpaque := true) with
        | some v => if v.getUsedConstants.any (fun (c : Lean.Name) => c.toString == targetOpaqueStr) then some p.1 else none
        | none => none
    if !callers.isEmpty then
      bannedCallers := (targetOpaqueStr, callers) :: bannedCallers
  let ok := badParse.isEmpty && badElab.isEmpty && disallowedAxioms.isEmpty && bannedCallers.isEmpty
  let summary :=
    s!"[Step 1: Closure Certification Gate]\n" ++
    s!"  • parseSource closure: {parseClosure.length} constants, bad={badParse.length}\n" ++
    s!"  • elabSource closure:  {elabClosure.length} constants, bad={badElab.length}\n" ++
    s!"  • elabSource axioms ({axiomsElab.length}): {axiomsElab} (disallowed={disallowedAxioms})\n" ++
    s!"  • banned opaque callers: {bannedCallers}"
  return (ok, summary)

def runClosureCertificationGate : IO (Bool × String) := do
  let leanEnv ← getCompileEnv #[`Ix.Frontend]
  return checkClosureCertification leanEnv

/-! ## 10. Step 2: Host Throughput & `IxVM` STARK FFT Benchmarks -/

/-- Generate a synthetic `n`-declaration `.ix` module with out-of-order dependency chains,
    mutual pairs, substructural contracts, and `rfl` theorems. -/
def mkSyntheticIxModule (numPairs : Nat) : String := Id.run do
  let mut lines : Array String := #[
    "structure BoxedNat : Type where",
    "  val : Nat",
    "  tag : Nat",
    "",
    "inductive ParityFlag : Type",
    "  | even : ParityFlag",
    "  | odd  : ParityFlag",
    ""
  ]
  -- Emit declarations in REVERSE dependency order so Tarjan SCC must topologically invert them!
  for idx in (List.range numPairs).reverse do
    let prevCall := if idx == 0 then "x" else s!"stepB_{idx - 1} x"
    lines := lines.push s!"def stepB_{idx} (x : Nat) : Nat := stepA_{idx} x"
    lines := lines.push s!"def stepA_{idx} (x : Nat) : Nat := {prevCall}"
    lines := lines.push s!"def linId_{idx} (!1 x : Nat) : ! Nat := x"
    lines := lines.push s!"theorem step_eq_{idx} (x : Nat) : Eq (stepB_{idx} x) (stepA_{idx} x) := by rfl"
  return "\n".intercalate lines.toList

def runFrontendBenchmarks (testEnv : Lean.Environment) : IO String := do
  let stdout ← IO.getStdout
  let emit (line : String) : IO Unit := do
    IO.println line
    stdout.flush
  emit "[Step 2: Ix Frontend Host & IxVM Benchmarks]"
  let mut report : Array String := #["[Step 2: Ix Frontend Host & IxVM Benchmarks]"]

  -- 2A. Host Pass-by-Pass Latency on Feature Suite + 60-Decl Synthetic Module
  let featureSrc := "
    inductive EvenN : Type
      | zero : EvenN
      | succOdd : OddN → EvenN
    inductive OddN : Type
      | succEven : EvenN → OddN
    structure PairNat : Type where
      fst : Nat
      snd : Nat
    class HasTag (α : Type) : Type where
      tagOf : α → Nat
    def useTag (x : Nat) : Nat := HasTag.tagOf x
    instance instTagNat : HasTag Nat where
      tagOf := fun n => n
    def myAdd (n m : Nat) : Nat
      | 0 => m
      | Nat.succ k => Nat.succ (myAdd k m)
    def linearId (!1 x : Nat) : ! Nat := x
    theorem myAdd_two_three : Eq (myAdd 2 3) 5 := by rfl
    theorem str_append_eq : Eq (String.append \"ix-\" \"vm\") \"ix-vm\" := by rfl
  "
  let synthSrc := mkSyntheticIxModule 20 -- 2 + 20*3 = 62 declarations in reverse dependency order

  for (label, src) in [("FeatureMix (10 decls)", featureSrc), ("SyntheticOutOfOrder (62 decls)", synthSrc)] do
    let t0 ← IO.monoNanosNow
    let (stx, _) ← IO.ofExcept (parseSource src)
    let t1 ← IO.monoNanosNow
    let modIdx ← IO.ofExcept (buildModuleIndex stx)
    let t2 ← IO.monoNanosNow
    let sched ← IO.ofExcept (analyzeModuleSyntax stx)
    let t3 ← IO.monoNanosNow
    let elabEnv ← IO.ofExcept (elabModuleSchedule sched IxElabEnv.empty true)
    let t4 ← IO.monoNanosNow
    let (ixonEnv, _) ← IO.ofExcept (compileElabEnvToIxon elabEnv)
    let _ ← IO.ofExcept (Ix.Resource.Addressed.checkResources ixonEnv {})
    let t5 ← IO.monoNanosNow
    let us (a b : Nat) : Nat := (b - a) / 1000
    let declCount := modIdx.decls.size
    let sccCount  := sched.sccs.size
    let constCount := elabEnv.consts.size
    let entry :=
      s!"  • Host Pipeline [{label}]: {declCount} source decls -> {sccCount} SCCs -> {constCount} elaborated consts ({ixonEnv.consts.size} Ixon consts)\n" ++
      s!"      Pass 0 Parse (`Text -> Syntax`):              {us t0 t1} µs\n" ++
      s!"      Pass 1 Scope (`Syntax -> ModuleIndex`):       {us t1 t2} µs\n" ++
      s!"      Pass 1-3 Tarjan SCC (`Syntax -> Schedule`):   {us t1 t3} µs\n" ++
      s!"      Pass 4 Elab+Canon+AuxGen (`Schedule -> Env`): {us t3 t4} µs\n" ++
      s!"      Pass 5 Ixon+Resources (`Env -> Ixon.Env`):    {us t4 t5} µs\n" ++
      s!"      Total End-to-End (`Text -> Checked Ixon`):    {us t0 t5} µs ({(us t0 t5) / (max 1 declCount)} µs/decl)"
    emit entry
    report := report.push entry

  -- 2B. IxVM `verify_claim` Execution & STARK FFT Cost on Frontend/String Theorems
  let aiurEnv ← IO.ofExcept (AiurTestEnv.build IxVM.ixVM IxVM.functionGroups)
  let verifyIdx := aiurEnv.compiled.getFuncIdx `verify_claim |>.get!
  let claimTargets : List (String × Lean.Name) := [
    ("String.append acceleration (`rfl`)",       ``str_accel_append_reduces),
    ("String.length acceleration (`rfl`)",       ``str_accel_length_reduces),
    ("String.utf8ByteSize acceleration (`rfl`)", ``str_accel_utf8_reduces),
    ("Pure Lexer + Literal Scanner (`rfl`)",     ``kernel_lexer_reduces),
    ("Pure Tarjan SCC Condensation (`rfl`)",     ``kernel_tarjan_scc_reduces),
    ("End-to-End Pure Parser (`parseSource`)",   `kernel_parse_reduces),
    ("End-to-End Pass 1 (`buildModuleIndex`)",   `kernel_scope_reduces),
    ("End-to-End 4-Pass Elab (`elabModuleSyntax`)", `kernel_elab_reduces),
    ("AnthropicFLT Proposition (`flt_pinned` & `FermatLastTheorem`)", `kernel_flt_prop_reduces),
    ("AnthropicFLT Proposition Hinted (`elabModuleWithHints`)", `kernel_flt_hinted_reduces)
  ]
  let tShared0 ← IO.monoMsNow
  let targetNames := claimTargets.toArray.map Prod.snd ++ synthesizedPrimNames
  let ixonEnv ← loadSharedIxonEnv targetNames testEnv
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv)
  let tShared1 ← IO.monoMsNow
  let hdr := s!"  • IxVM `verify_claim` (`Claim.check`) Execution & STARK FFT Cost (shared Ixon closure={ixonEnv.consts.size} consts, compiled in {tShared1 - tShared0}ms):"
  emit hdr
  report := report.push hdr
  for (lbl, targetName) in claimTargets do
    let tWitness0 ← IO.monoMsNow
    let targetAddr ← lookupAddr ixonEnv targetName
    -- Compute thin direct assumption frontier (matching `shardCheckEnvClaimTrees`)
    let depLeaves : Array Address := Id.run do
      let mut fs : Std.HashSet Address := {}
      if let some c := ixonEnv.getConst? targetAddr then
        let used := constIdxsOf c
        for (r, i) in c.refs.zipIdx do
          if used.contains i.toUInt64 && r != targetAddr && ixonEnv.consts.contains r then
            fs := fs.insert r
        let blockOpt : Option Address := match c.info with
          | .iPrj p => some p.block
          | .cPrj p => some p.block
          | .rPrj p => some p.block
          | .dPrj p => some p.block
          | _ => none
        if let some b := blockOpt then
          if b != targetAddr && ixonEnv.consts.contains b then
            fs := fs.insert b
      return fs.toArray
    let some depTree := Ix.AssumptionTree.canonical depLeaves
      | throw (IO.userError s!"deps unexpectedly empty for {targetName}")
    let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert depTree.root depTree
    let claim := Ix.Claim.check { ctx with bindingAssumed := true } targetAddr (some depTree.root)
    let witness ← IO.ofExcept (buildClaimWitness ixonEnv claim trees)
    let tExec0 ← IO.monoMsNow
    match aiurEnv.compiled.bytecode.execute verifyIdx witness.input witness.inputIOBuffer with
    | .error e =>
      throw (IO.userError s!"IxVM verify_claim failed for {lbl} ({targetName}): {e}")
    | .ok (_, _, queryCounts) =>
      let tExec1 ← IO.monoMsNow
      let stats := Aiur.computeStats aiurEnv.compiled queryCounts aiurEnv.shapes
      let fftCost := stats.totalFftCost.round.toUInt64.toNat
      let line :=
        s!"      - {lbl} ({targetName}): deps={depLeaves.size} consts, " ++
        s!"witness={tExec0 - tWitness0}ms, ixvm_exec={tExec1 - tExec0}ms, totalFftCost={fftCost}"
      emit line
      report := report.push line

  return "\n".intercalate report.toList

/-! ## 12–14. Wave 1, Wave 2, and Wave 3 Mathlib Tactics, Surface Syntax, Macros & Decision Procedures -/

def testWave1MathlibTacticsResult : Except String Bool := do
  let src := "
@[simp] theorem iff_self_custom (P : Prop) : P ↔ P :=
  Iff.intro (fun h => h) (fun h => h)

-- 1. Term-level and tactic-level `calc` chains (`=`, `↔`, `≤`, `<`, `_`)
theorem calc_eq_chain (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d :=
  calc
    a = b := h1
    _ = c := h2
    _ = d := by exact h3

theorem calc_iff_chain (P Q R : Prop) (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R := by
  calc
    P ↔ Q := h1
    _ ↔ R := h2

theorem calc_order_chain (a b c d : Nat) (h1 : a = b) (h2 : b < c) (h3 : c ≤ d) : a < d := by
  calc
    a = b := h1
    _ < c := h2
    _ ≤ d := h3

-- 2. `rintro`, `rcases`, and `obtain` (tuples, alternation `|`, and `rfl` substitution)
theorem rintro_and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact And.intro hq hp

theorem rintro_nested_and (P Q R : Prop) : P ∧ (Q ∧ R) → R ∧ P := by
  rintro ⟨hp, hq, hr⟩
  exact And.intro hr hp

theorem rcases_or_comm (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

theorem rcases_rfl_subst (a b : Nat) (P : Nat → Prop) (h : a = b ∧ P a) : P b := by
  rcases h with ⟨rfl, hpa⟩
  exact hpa

theorem obtain_exists_witness (P : Nat → Prop) (h : Exists (fun x => P x ∧ x = 7)) : P 7 := by
  obtain ⟨w, hpw, rfl⟩ := h
  exact hpw

-- 3. `rw` and `simp` over `Iff` (`↔`) via `@propext`, plus `simp only` / `dsimp only`
theorem rw_iff_in_goal (P Q R : Prop) (hPQ : P ↔ Q) (hQ : Q ∧ R) : P ∧ R := by
  rw [hPQ]
  exact hQ

theorem rw_iff_symm_in_hyp (P Q : Prop) (hPQ : P ↔ Q) (hP : P) : Q := by
  rw [hPQ] at hP
  exact hP

theorem simp_only_test (P Q : Prop) (hPQ : P ↔ Q) (hQ : Q) : P := by
  simp only [hPQ]
  exact hQ

theorem dsimp_only_beta : (fun (x : Nat) => x) 42 = 42 := by
  dsimp only
  rfl

-- 4. Context & Classical Tactics: `have`/`let` type inference, `suffices`, `specialize`,
--    `clear`, `revert`, `generalize`, `subst`, `by_cases`, `by_contra`, `use`
theorem have_let_infer_test (a : Nat) (h : a = 5) : a = 5 := by
  let x := a
  have hx := h
  exact hx

theorem suffices_by_and_from (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  suffices hq : Q by
    exact h2 hq
  suffices hp2 : P from h1 hp2
  exact hp

theorem specialize_clear_revert_test (P Q : Nat → Prop) (hAll : ∀ x : Nat, P x → Q x) (a : Nat) (ha : P a) : Q a := by
  specialize hAll a ha
  clear ha
  revert a
  intro b hb
  exact hb

theorem generalize_and_subst_test (a b : Nat) (P : Nat → Prop) (h : b = a) (hp : ∀ z : Nat, a + a = z → P z) : P (b + a) := by
  subst h
  generalize hgen : (a + a) = z
  exact hp z hgen

theorem by_cases_em (P : Prop) : P ∨ ¬ P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

theorem by_contra_dne (P : Prop) (h : ¬ ¬ P) : P := by
  by_contra hnp
  exact h hnp

theorem use_witness_test : Exists (fun (n : Nat) => n = 10) := by
  use 10
"
  let env ← elabSource src
  let (ixonEnv, _) ← compileElabEnvToIxon env
  let _ ← Ix.Resource.Addressed.checkResources ixonEnv {}
  let expected := [
    "calc_eq_chain", "calc_iff_chain", "calc_order_chain",
    "rintro_and_swap", "rintro_nested_and", "rcases_or_comm",
    "rcases_rfl_subst", "obtain_exists_witness",
    "rw_iff_in_goal", "rw_iff_symm_in_hyp", "simp_only_test", "dsimp_only_beta",
    "have_let_infer_test", "suffices_by_and_from", "specialize_clear_revert_test",
    "generalize_and_subst_test", "by_cases_em", "by_contra_dne", "use_witness_test"
  ]
  for nm in expected do
    if !env.contains (Name.simple nm) then
      throw s!"missing expected Wave 1 declaration '{nm}'"
  return true

def testWave2SurfaceAndMacrosResult : Except String Bool := do
  let src := "
-- 1. Declarative `notation`, `macro`, and `macro_rules`
notation:65 lhs \" +++ \" rhs => Nat.add lhs rhs
macro \"double! \" x:term : term => `(Nat.add $x $x)
syntax \"my_rfl_tac\" : tactic
macro_rules
  | `(tactic| my_rfl_tac) => `(tactic| rfl)

def test_notation_and_macro (n : Nat) : Nat :=
  (n +++ 3) +++ (double! n)

theorem test_tactic_macro (n : Nat) : double! n = Nat.add n n := by
  my_rfl_tac

-- 2. Existential (`∃`) and bounded quantifiers (`∀ x > 0, ...`, `∃ n ≤ 10, ...`)
def ExSurfaceProp : Prop :=
  ∃ x : Nat, x = 5

def ExMultiBinderProp : Prop :=
  ∃ (x y : Nat), x = y

def BoundedForallProp : Prop :=
  ∀ x > 0, ∀ y ≤ x, y ≤ x

def BoundedExistsProp : Prop :=
  ∃ n > 0, n = 1

theorem ex_surface_prove : ∃ n : Nat, n = 4 :=
  ⟨4, Eq.refl 4⟩

-- 3. Right-associative nested anonymous constructors `⟨a, b, c⟩`
theorem nested_anon_ctor_and (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R :=
  ⟨hp, hq, hr⟩

theorem nested_anon_ctor_exists : ∃ x : Nat, x = 2 ∧ 2 = x :=
  ⟨2, Eq.refl 2, Eq.refl 2⟩

-- 4. Centered-dot lambda placeholders `(· + 1)`
def incFn : Nat → Nat := (Nat.add · 1)
def addBothFn : Nat → Nat → Nat := (Nat.add · ·)

theorem centered_dot_beta : incFn 5 = 6 := by
  rfl

-- 5. Structure spread `{ s with field := val }` and destructuring `let ⟨a, b⟩ := ...`
structure PairNat where
  fst : Nat
  snd : Nat

def updateFst (p : PairNat) (newFst : Nat) : PairNat :=
  { p with fst := newFst }

def sumPairDestruct (p : PairNat) : Nat :=
  let ⟨a, b⟩ := p;
  Nat.add a b

theorem struct_spread_and_destruct_eq :
    sumPairDestruct (updateFst ⟨1, 2⟩ 10) = 12 := by
  rfl

-- 6. Dependent `if h : c then t else e` (`@dite`) and propositional `if c then t else e`
def depIfExample (p : Prop) [Decidable p] : Nat :=
  if h : p then 1 else 0
"
  let env ← elabSource src
  let (ixonEnv, _) ← compileElabEnvToIxon env
  let _ ← Ix.Resource.Addressed.checkResources ixonEnv {}
  let expected := [
    "test_notation_and_macro", "test_tactic_macro",
    "ExSurfaceProp", "ExMultiBinderProp", "BoundedForallProp", "BoundedExistsProp",
    "ex_surface_prove", "nested_anon_ctor_and", "nested_anon_ctor_exists",
    "incFn", "addBothFn", "centered_dot_beta",
    "PairNat", "updateFst", "sumPairDestruct", "struct_spread_and_destruct_eq",
    "depIfExample"
  ]
  for nm in expected do
    if !env.contains (Name.simple nm) then
      throw s!"missing expected Wave 2 declaration '{nm}'"
  return true

def testWave3DecisionAndHintsResult : Except String Bool := do
  let src := "
-- 1. `norm_num` on closed arithmetic & comparisons
theorem norm_num_eq : 12 * 12 + 5 = 149 := by
  norm_num

theorem norm_num_lt : 2 ^ 5 + 3 < 40 := by
  norm_num

theorem norm_num_ne : 7 * 8 ≠ 55 := by
  norm_num

theorem norm_num_logic : (3 ≤ 3 ∧ 4 < 9) ∧ ¬ (5 < 2) := by
  norm_num

-- 2. `ring` on universal commutative semiring polynomial identities
theorem ring_binomial_sq (x y : Nat) :
    (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  ring

theorem ring_cube_identity (a b : Nat) :
    (a + b) * (a * a + b * b) = a ^ 3 + a * b * b + b * a * a + b ^ 3 := by
  ring

theorem ring_comm_assoc (x y z : Nat) :
    (x + y) + z * (x + 1) = z * x + (y + x) + z := by
  ring

-- 3. `omega` on linear arithmetic entailments & inequalities
theorem omega_trans_strict (x y z : Nat) (h1 : x < y) (h2 : y ≤ z) : x < z + 1 := by
  omega

theorem omega_antisymm_eq (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  omega

theorem omega_linear_combo (x y : Nat) (h1 : x + y ≤ 10) (h2 : y ≥ 6) : x ≤ 4 := by
  omega
"
  let env ← elabSource src
  let (ixonEnv, _) ← compileElabEnvToIxon env
  let _ ← Ix.Resource.Addressed.checkResources ixonEnv {}
  -- 4. Verify `generateElabHints` + `elabSourceWithHints` works on tactic-proved theorems (`SyntaxKind.byTactic`)!
  let hints ← generateElabHints src
  let hintedEnv ← elabSourceWithHints src hints
  let (hintedIxon, _) ← compileElabEnvToIxon hintedEnv
  for (addr, _) in ixonEnv.consts do
    if !hintedIxon.consts.contains addr then
      throw s!"Hinted Ixon.Env missing content-addressed constant {addr} on tactic module"
  -- 5. Negative tests: verify `norm_num`, `ring`, and `omega` reject false goals!
  if (elabSource "theorem bad_norm : 2 + 2 = 5 := by norm_num").isOk then
    throw "norm_num accepted a false equality 2 + 2 = 5"
  if (elabSource "theorem bad_ring (x y : Nat) : x + y = x + 2 * y := by ring").isOk then
    throw "ring accepted a non-identity x + y = x + 2 * y"
  if (elabSource "theorem bad_omega (x y : Nat) (h : x ≤ y) : y < x := by omega").isOk then
    throw "omega accepted a satisfiable counterexample x ≤ y ⊢ y < x"
  return true

def testWave1MathlibTactics : Bool :=
  match testWave1MathlibTacticsResult with
  | .ok b => b
  | .error _ => false

def testWave2SurfaceAndMacros : Bool :=
  match testWave2SurfaceAndMacrosResult with
  | .ok b => b
  | .error _ => false

def testWave3DecisionAndHints : Bool :=
  match testWave3DecisionAndHintsResult with
  | .ok b => b
  | .error _ => false

def testTracksABCDResult : Except String Bool := do
  -- 1. Track A (`Ix.Frontend.Format`): round-trip `formatModule` -> `parseSource` -> `elabSource`
  let origSrc := "
structure BoxNat : Type where
  val : Nat

def unbox (b : BoxNat) : Nat :=
  BoxNat.val b

theorem unbox_mk (n : Nat) : Eq (unbox (BoxNat.mk n)) n := by
  rfl
"
  let (origStx, _) ← parseSource origSrc
  let formatted := formatModule origStx
  let (reparsedStx, _) ← parseSource formatted
  let envOrig ← elabModuleSyntax origStx
  let envReparsed ← elabModuleSyntax reparsedStx
  let (ixonOrig, _) ← compileElabEnvToIxon envOrig
  let (ixonReparsed, _) ← compileElabEnvToIxon envReparsed
  for (addr, _) in ixonOrig.consts do
    if !ixonReparsed.consts.contains addr then
      throw s!"Track A formatModule round-trip lost content-addressed constant {addr}\nFormatted:\n{formatted}"

  -- Also verify `formatMergeOutcome` renders `.#merge` stubs cleanly
  let baseSrc := "def f (x : Nat) : Nat := x"
  let leftSrc := "def f (x : Nat) : Nat := Nat.add x 1\ndef caller : Nat := f 5"
  let rightSrc := "def f (x : Nat) : Nat := Nat.add x 2"
  let outcome ← mergeSource3 baseSrc leftSrc rightSrc
  let renderedMerge := formatMergeOutcome outcome
  if (renderedMerge.splitOn "f.#merge._1").length < 2 then
    throw s!"Track A formatMergeOutcome did not contain f.#merge._1:\n{renderedMerge}"
  if (renderedMerge.splitOn "#merge").length < 2 then
    throw s!"Track A formatMergeOutcome did not contain #merge block:\n{renderedMerge}"

  -- 2. Track B (`elabModuleDAG` & `IxElabEnv.ofIxonEnv`): multi-module DAG + `.ixe` hydration
  let modASrc := "
structure PairNat : Type where
  fst : Nat
  snd : Nat

def sumPair (p : PairNat) : Nat :=
  Nat.add (PairNat.fst p) (PairNat.snd p)

infixl:65 \" <+> \" => Nat.add
"
  let modBSrc := "
import ModA

def makeAndSum (a b : Nat) : Nat :=
  sumPair (PairNat.mk (a <+> 1) b)

theorem makeAndSum_eq : Eq (makeAndSum 2 3) 6 := by
  rfl
"
  -- Pass modules in reverse order (`ModB` before `ModA`) to verify topological scheduling!
  let (dagEnv, _) ← elabModuleDAG [
    (Name.simple "ModB", modBSrc),
    (Name.simple "ModA", modASrc)
  ]
  if !dagEnv.contains (Name.simple "makeAndSum_eq") then
    throw "Track B elabModuleDAG missing 'makeAndSum_eq'"

  -- Verify cyclic module imports are rejected
  let cycRes := elabModuleDAG [
    (Name.simple "ModX", "import ModY\ndef x : Nat := 1"),
    (Name.simple "ModY", "import ModX\ndef y : Nat := 2")
  ]
  if cycRes.isOk then
    throw "Track B elabModuleDAG failed to reject cyclic module imports"

  -- Verify `.ixe` hydration via `IxElabEnv.ofIxonEnv` reconstructs constants and `structTable`
  let (_, _, ixonA, _) ← compileSourceToIxon modASrc
  let hydratedEnv := IxElabEnv.ofIxonEnv ixonA
  if !hydratedEnv.structTable.contains (Name.simple "PairNat") then
    throw "Track B IxElabEnv.ofIxonEnv failed to reconstruct PairNat in structTable"
  let (stxDownstream, _) ← parseSource "def useHydrated (p : PairNat) : Nat := sumPair { p with fst := 10 }"
  let envDownstream ← elabModuleSyntax stxDownstream hydratedEnv
  if !envDownstream.contains (Name.simple "useHydrated") then
    throw "Track B downstream module failed to elaborate against hydrated Ixon.Env"

  -- 3. Track C (`compileSourceCertified` & `compileModuleDAGCertified`): bridge to `Ix.Cert.compileReport`
  let (_, _, certIxe, certFailures) ← compileSourceCertified origSrc
  if !certFailures.isEmpty then
    throw s!"Track C compileSourceCertified had {certFailures.toMap.size} failures"
  if certIxe.consts.isEmpty then
    throw "Track C compileSourceCertified produced 0 Ixon constants"

  let (_, _, dagCertIxe, dagCertFailures) ← compileModuleDAGCertified [
    (Name.simple "ModB", modBSrc),
    (Name.simple "ModA", modASrc)
  ]
  if !dagCertFailures.isEmpty then
    throw s!"Track C compileModuleDAGCertified had {dagCertFailures.toMap.size} failures"
  if dagCertIxe.consts.isEmpty then
    throw "Track C compileModuleDAGCertified produced 0 Ixon constants"
  return true

def testTracksABCD : Bool :=
  match testTracksABCDResult with
  | .ok b => b
  | .error _ => false

/-! ## LSpec Test Suite & Compile-Time Verification -/

def frontendSuite : TestSeq :=
  group "Ix.Frontend" (
    test "1. Pure Parser (commands, operators, #hash imports, map)" testParserBasic ++
    test "2. Substructural contracts (0, 1, &, !, ~, let borrow)" testSubstructuralContracts ++
    test "3. Order-free & mutual-free declarations via Tarjan SCC" testOrderFreeAndMutualFree ++
    test "4. In-elaborator constructor canonicalization & tie-breaking" testConstructorCanonicalization ++
    test "5. Surgery-free AuxGen & structure projections" testAuxGenAndStructures ++
    test "6. Structural recursion (recOn), tactics & String/Nat acceleration" testStructuralRecursionAndTactics ++
    test "6b. Pure Tactic Engine (induction, rw, cases, combinators, simp)" testPureTacticEngine ++
    test "7. Programmable module import mapping & ElabClaim verification" testImportMapAndElabClaim ++
    test "8. Kernel-level reduction of parseSource, buildModuleIndex & elabModuleSyntax"
      (kernelParseCheck && kernelScopeCheck && kernelElabCheck) ++
    test "9. Fermat's Last Theorem proposition (`flt_pinned` & `FermatLastTheorem`) elaboration (unhinted & hinted)"
      (kernelFltPropCheck && kernelFltHintedCheck && testFltPropositionElab) ++
    test "10. Advanced Frontend (where, let rec, auto-implicits, deriving, extends, @[simp], Coe, prefix/postfix)"
      testAdvancedFrontend ++
    test "11. IxVCS AST & Type-Aware Module Merge Engine (mergeSource2, mergeSource3, #merge, proof irrelevance)"
      testIxVCSMergeEngine ++
    test "12. Wave 1 Mathlib Tactics (calc, rcases, obtain, rintro, Iff rw/simp, suffices, subst, by_cases, by_contra, use)"
      testWave1MathlibTactics ++
    test "13. Wave 2 Surface Idioms & Declarative Macros (∃, bounded ∀/∃, dite, ·, nested ⟨...⟩, spread, notation, macro_rules)"
      testWave2SurfaceAndMacros ++
    test "14. Wave 3 Decision Procedures (norm_num, ring, omega) & Tactic ElabHints Verification"
      testWave3DecisionAndHints ++
    test "15. Tracks A-C (Format Round-Trip, Multi-Module DAG & .ixe Hydration, Certified Compiler Bridge)"
      testTracksABCD
  )

def Tests.Ix.Frontend.suite : List TestSeq := [frontendSuite]

run_meta do
  unless testParserBasic do
    throwError "testParserBasic failed"
  unless testSubstructuralContracts do
    throwError "testSubstructuralContracts failed"
  unless testOrderFreeAndMutualFree do
    throwError "testOrderFreeAndMutualFree failed"
  unless testConstructorCanonicalization do
    throwError "testConstructorCanonicalization failed"
  unless testAuxGenAndStructures do
    throwError "testAuxGenAndStructures failed"
  unless testStructuralRecursionAndTactics do
    throwError "testStructuralRecursionAndTactics failed"
  match testPureTacticEngineResult with
  | .ok true => pure ()
  | .ok false => throwError "testPureTacticEngine returned false"
  | .error msg => throwError s!"testPureTacticEngine failed: {msg}"
  match testAdvancedFrontendResult with
  | .ok true => pure ()
  | .ok false => throwError "testAdvancedFrontend returned false"
  | .error msg => throwError s!"testAdvancedFrontend failed: {msg}"
  match testIxVCSMergeEngineResult with
  | .ok true => pure ()
  | .ok false => throwError "testIxVCSMergeEngine returned false"
  | .error msg => throwError s!"testIxVCSMergeEngine failed: {msg}"
  match testWave1MathlibTacticsResult with
  | .ok true => pure ()
  | .ok false => throwError "testWave1MathlibTactics returned false"
  | .error msg => throwError s!"testWave1MathlibTactics failed: {msg}"
  match testWave2SurfaceAndMacrosResult with
  | .ok true => pure ()
  | .ok false => throwError "testWave2SurfaceAndMacros returned false"
  | .error msg => throwError s!"testWave2SurfaceAndMacros failed: {msg}"
  match testWave3DecisionAndHintsResult with
  | .ok true => pure ()
  | .ok false => throwError "testWave3DecisionAndHints returned false"
  | .error msg => throwError s!"testWave3DecisionAndHints failed: {msg}"
  match testTracksABCDResult with
  | .ok true => pure ()
  | .ok false => throwError "testTracksABCD returned false"
  | .error msg => throwError s!"testTracksABCD failed: {msg}"
  unless testImportMapAndElabClaim do
    throwError "testImportMapAndElabClaim failed"
  unless testFltPropositionElab do
    throwError "testFltPropositionElab failed"
  let env ← Lean.getEnv
  let (gateOk, gateSummary) := checkClosureCertification env
  IO.println gateSummary
  unless gateOk do
    throwError "Closure Certification Gate failed!"
  IO.println "✓ All 15 Ix.Frontend test suites + Step 1 Closure Certification Gate passed!"

def Tests.Ix.Frontend.runStoreEngineTest : IO Unit := do
  let payloadA := "ix-store-loose-test-payload-alpha".toUTF8
  let addrA ← StoreIO.toIO (Store.write payloadA)
  let hasA ← StoreIO.toIO (Store.contains addrA)
  unless hasA do
    throw (IO.userError "testStoreEngine: Store.contains returned false for freshly written object")
  let readA ← StoreIO.toIO (Store.readVerified addrA)
  unless readA == payloadA do
    throw (IO.userError "testStoreEngine: Store.readVerified payload mismatch")
  let p1 := "ix-store-pack-entry-1".toUTF8
  let p2 := "ix-store-pack-entry-2".toUTF8
  let a1 := Address.blake3 p1
  let a2 := Address.blake3 p2
  let (_packId, _written) ← StoreIO.toIO (Store.writePack #[(a1, p1), (a2, p2)])
  let r1 ← StoreIO.toIO (Store.readVerified a1)
  let r2 ← StoreIO.toIO (Store.readVerified a2)
  unless r1 == p1 && r2 == p2 do
    throw (IO.userError "testStoreEngine: Store.writePack round-trip failed")
  let st ← StoreIO.toIO Store.stats
  unless st.hotEntries >= 3 do
    throw (IO.userError s!"testStoreEngine: expected >= 3 hot entries, got {st.hotEntries}")

def Tests.Ix.Frontend.runBenchmarksWithEnv (env : Lean.Environment) : IO UInt32 := do
  let stdout ← IO.getStdout
  let (fltOk, fltSummary) ← verifyFltIxonAddressParity env
  IO.println fltSummary
  stdout.flush
  unless fltOk do
    throw (IO.userError "verifyFltIxonAddressParity failed!")
  let (gateOk, gateSummary) := checkClosureCertification env
  IO.println gateSummary
  stdout.flush
  unless gateOk do
    throw (IO.userError "Closure Certification Gate failed!")
  let _ ← runFrontendBenchmarks env
  return 0
