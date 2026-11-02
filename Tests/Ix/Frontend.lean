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
  "axiom flt_pinned (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n\n" ++
  "def FermatLastTheorem : Prop := ∀ n : ℕ, n > 2 → ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n"

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

-- Verify `kernel_parse_reduces`, `kernel_scope_reduces`, `kernel_elab_reduces`, and `kernel_flt_prop_reduces`
-- directly in Lean's C++ kernel with `@Eq.refl Bool true` (bypassing redundant `Meta.isDefEq` unfolding).
run_meta do
  let boolTy := Lean.mkConst ``Bool
  let trueVal := Lean.mkConst ``Bool.true
  let eqReflTrue := Lean.mkApp2 (Lean.mkConst ``Eq.refl [Lean.Level.succ Lean.Level.zero]) boolTy trueVal
  for (thmName, lhsConst) in [
    (`kernel_parse_reduces,    ``kernelParseCheck),
    (`kernel_scope_reduces,    ``kernelScopeCheck),
    (`kernel_elab_reduces,     ``kernelElabCheck),
    (`kernel_flt_prop_reduces, ``kernelFltPropCheck)
  ] do
    let eqTy := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero]) boolTy (Lean.mkConst lhsConst) trueVal
    Lean.addDecl (.thmDecl {
      name := thmName
      levelParams := []
      «type» := eqTy
      value := eqReflTrue
    })

/-! ## 9. Step 1: Closure Certification Gate (`parseSource` & `elabSource`) -/

/-- Pure transitive closure audit over `leanEnv` for `parseSource` and `elabSource`. -/
def checkClosureCertification (leanEnv : Lean.Environment) : Bool × String := Id.run do
  let parseClosure : List (Lean.Name × Lean.ConstantInfo) := Ix.EnvScope.collectDeps leanEnv [``parseSource]
  let elabClosure  : List (Lean.Name × Lean.ConstantInfo) := Ix.EnvScope.collectDeps leanEnv [``elabSource]
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
    ("AnthropicFLT Proposition (`flt_pinned` & `FermatLastTheorem`)", `kernel_flt_prop_reduces)
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
    let closure := closureFrom ixonEnv targetAddr
    let depLeaves : Array Address :=
      closure.fold (init := #[]) fun acc a =>
        if a == targetAddr then acc else acc.push a
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

/-! ## LSpec Test Suite & Compile-Time Verification -/

def frontendSuite : TestSeq :=
  group "Ix.Frontend" (
    test "1. Pure Parser (commands, operators, #hash imports, map)" testParserBasic ++
    test "2. Substructural contracts (0, 1, &, !, ~, let borrow)" testSubstructuralContracts ++
    test "3. Order-free & mutual-free declarations via Tarjan SCC" testOrderFreeAndMutualFree ++
    test "4. In-elaborator constructor canonicalization & tie-breaking" testConstructorCanonicalization ++
    test "5. Surgery-free AuxGen & structure projections" testAuxGenAndStructures ++
    test "6. Structural recursion (recOn), tactics & String/Nat acceleration" testStructuralRecursionAndTactics ++
    test "7. Programmable module import mapping & ElabClaim verification" testImportMapAndElabClaim ++
    test "8. Kernel-level reduction of parseSource, buildModuleIndex & elabModuleSyntax"
      (kernelParseCheck && kernelScopeCheck && kernelElabCheck) ++
    test "9. Fermat's Last Theorem proposition (`flt_pinned` & `FermatLastTheorem`) elaboration"
      (kernelFltPropCheck && testFltPropositionElab)
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
  unless testImportMapAndElabClaim do
    throwError "testImportMapAndElabClaim failed"
  unless testFltPropositionElab do
    throwError "testFltPropositionElab failed"
  let env ← Lean.getEnv
  let (gateOk, gateSummary) := checkClosureCertification env
  IO.println gateSummary
  unless gateOk do
    throwError "Closure Certification Gate failed!"
  IO.println "✓ All 9 Ix.Frontend test suites + Step 1 Closure Certification Gate passed!"

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
