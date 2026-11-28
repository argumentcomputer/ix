import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.AssumptionTree
import Tests.Ix.IxVM.Harness

/-!
# Must-reject gate

Hand-built inputs the IxVM program must refuse, with the controls that show each fixture
reaches the code it targets. Several are closed proofs of `False`:

* a recursor family that splits its elimination levels (a `Prop`-only recursor of a
  two-constructor proposition `P` in one family with a large recursor of `T | mk : P → T`),
  and the same idea through a genuine nested occurrence in `Nonempty`;
* a negative occurrence behind a mutual container's peer, with three projections out of it;
* declaration shapes Lean refuses (a type that mentions its peer, a non-uniform nested
  occurrence, peers that differ in universe count or safety, a recursor with an extra
  universe parameter or a rule bound at another minor's type, misnumbered constructors);
* structure eta and unit-like conversion at members of recursive mutual and nested blocks.

Each case has a required verdict and the reason for it:
- Lean's kernel, where the input is a Lean declaration: the case carries the
  declarations and the suite checks Lean's verdict on them
  (`Kernel.Environment.addDecl`) before it trusts the requirement;
- otherwise a construction Lean cannot produce: a recursor record that is not
  the recursor Lean regenerates from its inductive, peers whose universe counts
  or safety differ (one `inductDecl` has one level list and one safety flag),
  or a closure that contains such a record.

Known divergences (`knownDivergences`) are cases the program decides against the
requirement by design: every one is a refusal of something Lean accepts. The gate:
- reports every case on the list, and does not fail for it;
- fails when a listed case stops diverging;
- fails when any case not on the list diverges.
The list is enforced by submitting a listed case with the program's verdict as the
expected one, so the host fails it as soon as the verdict changes.

The suite runs in circuit-verdict mode (`Tests.Ix.IxVM.Harness`): every
assertion is checked, so the verdicts are the circuit's on these witnesses.
-/

namespace Tests.Ix.IxVM.MustReject.Fx

-- A legal mutual container pair, and the same field in a non-mutual one.
mutual
inductive C1 (α : Type) : Type
  | mk : C2 α → C1 α
inductive C2 (α : Type) : Type
  | mk : (α → False) → C2 α
end
inductive C3 (α : Type) : Type
  | mk : (α → False) → C3 α

-- A three-member chain and an honest pair.
mutual
inductive Wa (α : Type) : Type
  | mk : Wb α → Wa α
inductive Wb (α : Type) : Type
  | mk : Wc α → Wb α
inductive Wc (α : Type) : Type
  | mk : (α → False) → Wc α
end
mutual
inductive Ha (α : Type) : Type
  | mk : Hb α → Ha α
inductive Hb (α : Type) : Type
  | mk : α → Hb α
end

-- A plain two-constructor type.
inductive Two where
  | a | b

-- Records inside recursive mutual and nested blocks, and controls.
mutual
  structure Lone where
    a : Nat
    b : Bool
  inductive Other where
    | mk : Nat → Other
end
mutual
  inductive LU where | mk : LU
  inductive LV where | mk : Nat → LV
end
mutual
  structure Pos where
    line : Nat
    col : Nat
  inductive Tag where
    | t : Tag
  inductive Tm where
    | var : Nat → Tm
    | at : Pos → Tm → Tm
    | tag : Tag → Tm → Tm
end
mutual
  structure Attr where
    k : Nat
    v : Bool
  inductive Node where
    | elem : List Attr → List Node → Node
end
structure DS where
  a : Nat
  b : Bool
inductive DU where | mk : DU

theorem loneEta (p : Lone) : p = ⟨p.a, p.b⟩ := rfl

def stLone : Prop := ∀ p : Lone, p = Lone.mk p.a p.b
def stLonei : Prop := ∀ p : Lone, (match p with | ⟨a, _⟩ => a) = p.a
def stLU : Prop := ∀ x y : LU, x = y
def stPos : Prop := ∀ p : Pos, p = Pos.mk p.line p.col
def stPosi : Prop := ∀ p : Pos, (match p with | ⟨a, _⟩ => a) = p.line
def stTag : Prop := ∀ x y : Tag, x = y
def stAttr : Prop := ∀ p : Attr, p = Attr.mk p.k p.v
def stDS : Prop := ∀ p : DS, p = DS.mk p.a p.b
def stDSi : Prop := ∀ p : DS, (match p with | ⟨a, _⟩ => a) = p.a
def stDU : Prop := ∀ x y : DU, x = y

end Tests.Ix.IxVM.MustReject.Fx

namespace Tests.Ix.IxVM.MustReject

open IxVM.ClaimHarness
open Tests.Ix.IxVM.MustReject.Fx

abbrev E := Ixon.Expr

/-- A case of the gate. -/
structure MRCase where
  /-- Short identifier. -/
  name : String
  /-- What acceptance would mean. -/
  intent : String
  env : Ixon.Env
  claim : Ix.Claim
  trees : Std.HashMap Address Ix.AssumptionTree := {}
  /-- The required verdict. -/
  mustAccept : Bool := false
  /-- Why the verdict is required (the oracle). -/
  oracle : String
  /-- Lean declarations, added in order to the test binary's kernel
  environment: Lean's kernel must accept them all iff `mustAccept`. -/
  lean : List Lean.Declaration := []
  /-- For a required rejection: text the error must contain, once pinned. -/
  rejectsWith : Option String := none

/-- Cases the program decides against the requirement, by design. Each is a refusal of
something Lean's kernel accepts:
* `peer-negative/inductive-BadH-honest`: the hand-built block carries no recursor records,
  and the modeled route checks a nested block only with its recursor family
  ("no model advice"; a compiled block always carries them);
* `eta/control-{eLone,iLone,uLU,loneEta}`: `Lone` and `LU` are members of mutual blocks,
  where the program grants no structure eta, eta-iota, unit-like conversion or projection,
  and refuses the recursors their statements name;
* `shapes/control-zero-ctor-safety-flip`: an unsafe inductive as the seed, which a typing
  claim refuses. -/
def knownDivergences : List (String × String) := [
  ("peer-negative/inductive-BadH-honest", "a nested block without recursor records has no model"),
  ("eta/control-eLone", "no structure eta at a mutual block"),
  ("eta/control-iLone", "no structure eta at a mutual block"),
  ("eta/control-uLU", "no unit-like conversion at a mutual block"),
  ("eta/control-loneEta", "no structure eta at a mutual block"),
  ("shapes/control-zero-ctor-safety-flip", "an unsafe seed")]

private def noModel : String := "no model advice for a mutual or nested block"
private def twoMotives : String := "a recursor of a native block with more than one motive"
private def levelLink : String :=
  "universe-parameter count is not its block's plus the elimination parameter"
private def lamZeroDatum : String := "a lambda's datum does not match its body"

/-- The rejection message each case not on the list is pinned to: the first assertion the
program is expected to meet on the case's walk. A required rejection without one accepts
any failure of the program except a missing hint. -/
def rejectionReasons : List (String × String) := [
  -- a block of two recursors over a native family: more than one motive
  ("split-elim/recursor-X", twoMotives),
  ("split-elim/recursor-Y", twoMotives),
  -- refused by the level link before the type comparison: a two-constructor `Prop`
  -- eliminates into `Prop` only, so its recursor carries no elimination parameter
  ("split-elim/control-large-recursor-of-P", levelLink),
  -- a nested block the reader does not model, and its recursors
  ("nonempty-nest/inductive-T", noModel),
  ("nonempty-nest/recursor-T", noModel),
  ("nonempty-nest/recursor-aux", noModel),
  ("peer-negative/inductive-Bad", noModel),
  ("peer-negative/ctor-Bad.mk", noModel),
  ("peer-negative/unwrap", noModel),
  ("peer-negative/false", lamZeroDatum),
  ("peer-negative/control-nonmutual-container", noModel),
  ("peer-negative/inductive-Bad2-three-peers", noModel),
  ("peer-negative/false-three-peers", lamZeroDatum),
  ("peer-negative/control-declared-mutual-negative", noModel),
  ("shapes/inductive-inductive", "an inductive's type mentions a type of its own block"),
  ("shapes/peer-universe-counts", noModel),
  ("shapes/partial-uses-unsafe", "claim seed is unsafe or partial"),
  -- the recursor level link and the syntactic rule comparison
  ("shapes/recursor-extra-universe", levelLink),
  ("shapes/rule-binder-domain", "a stored rule is not the generated one up to consumed wrappers"),
  ("shapes/ctor-index-assumed-block", "ctor's stored index differs from its position")]

/-! ## Construction helpers -/

def st (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.ser c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a (.regular 0) }
    | _ => env
  (env, a)

/-- A projection record: no tables, no binder data. -/
def prj (info : Ixon.ConstantInfo) : Ixon.Constant := ⟨info, #[], #[], #[], #[]⟩

/-- A constructor with inherited field modes. -/
def ctor (cidx fields : UInt64) (typ : E) (params : UInt64 := 0) (lvls : UInt64 := 0)
    (isUnsafe : Bool := false) : Ixon.Constructor :=
  { isUnsafe, lvls, cidx, params, fields, typ }

/-- A definition or theorem record body. -/
def dfn (kind : Ix.DefKind) (typ value : E) (safety : Ix.DefinitionSafety := .safe) :
    Ixon.Definition :=
  { kind, safety, lvls := 0, typ, value }

def apps (f : E) (xs : List E) : E := xs.foldl .app f

def lams : Nat → E → E
  | 0, b => b
  | n + 1, b => .leanLam (.sort 0) (lams n b)

/-- The addresses the fixtures reference, from the compiled base. -/
structure Base where
  env : Ixon.Env
  falseA : Address
  trueA : Address
  trueIntroA : Address
  eqA : Address
  reflA : Address
  eqMpA : Address
  congrArgA : Address
  nonemptyA : Address
  nonemptyIntroA : Address
  listA : Address
  natA : Address

/-- `inductive N : Type | mk : K N → N` for a one-parameter container `K`. -/
def badBlock (kA : Address) : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[ctor 0 1 (.leanAll (.app (.ref 0 #[]) (.recur 0 #[])) (.recur 0 #[]))]⟩],
   #[], #[kA], #[.succ .zero], #[]⟩

/-- A `Lean.InductiveType`, built through a typed helper so the anonymous
constructors are unambiguous (`InductiveType` and `Constructor` share fields). -/
def mkInd (name : Lean.Name) (type : Lean.Expr)
    (ctors : List (Lean.Name × Lean.Expr)) : Lean.InductiveType :=
  { name := name, type := type, ctors := ctors.map fun (n, t) => ({ name := n, type := t } : Lean.Constructor) }

/-- A `Lean.DefinitionVal` declaration through a typed helper. -/
def mkDefn (name : Lean.Name) (type value : Lean.Expr)
    (safety : Lean.DefinitionSafety) : Lean.Declaration :=
  .defnDecl { name := name, levelParams := [], type := type, value := value, hints := .opaque, safety := safety, all := [name] }

/-- `inductive name : Type | mk : container name → name`. -/
def leanBadDecl (name container : Lean.Name) : Lean.Declaration :=
  .inductDecl [] 0 [mkInd name (.sort (.succ .zero))
    [(name ++ `mk, .forallE `x (.app (.const container []) (.const name []))
      (.const name []) .default)]] false

/-- A `check` case of `target` with no assumptions. -/
def chk (env : Ixon.Env) (ctx : Ix.ClaimContext) (name intent oracle : String) (target : Address)
    (mustAccept : Bool := false) (lean : List Lean.Declaration := []) : MRCase :=
  { name, intent, env, claim := .check ctx target none, mustAccept, oracle, lean }

/-! ## A recursor family with split elimination levels -/

def recTyA (s major : UInt64) (concl : E) : E :=
  .leanAll (.leanAll (.ref 0 #[]) (.sort s)) <|
  .leanAll (.leanAll (.ref 1 #[]) (.sort s)) <|
  .leanAll (.app (.var 1) (.ref 2 #[])) <|
  .leanAll (.app (.var 2) (.ref 3 #[])) <|
  .leanAll (.leanAll (.ref 0 #[]) (.leanAll (.app (.var 4) (.var 0))
    (.app (.var 4) (.app (.ref 4 #[]) (.var 1))))) <|
  .leanAll (.ref major #[]) concl

def splitElim (b : Base) (ctx : Ix.ClaimContext) : Array MRCase := Id.run do
  let env := b.env
  let pInd : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[ctor 0 0 (.recur 0 #[]), ctor 1 0 (.recur 0 #[])]⟩
  let (env, bP) := st env ⟨.muts #[.indc pInd], #[], #[], #[.zero], #[]⟩
  let (env, pA) := st env (prj (.iPrj ⟨0, bP⟩))
  let (env, c1A) := st env (prj (.cPrj ⟨0, 0, bP⟩))
  let (env, c2A) := st env (prj (.cPrj ⟨0, 1, bP⟩))
  let tInd : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[ctor 0 1 (.leanAll (.ref 0 #[]) (.recur 0 #[]))]⟩
  let (env, bT) := st env ⟨.muts #[.indc tInd], #[], #[pA], #[.succ .zero], #[]⟩
  let (env, tA) := st env (prj (.iPrj ⟨0, bT⟩))
  let (env, mkA) := st env (prj (.cPrj ⟨0, 0, bT⟩))
  let xRec : Ixon.Recursor := ⟨false, false, 1, 0, 0, 2, 3,
    recTyA 0 0 (.app (.var 5) (.var 0)),
    #[⟨0, lams 5 (.var 2)⟩, ⟨0, lams 5 (.var 1)⟩]⟩
  let yRule : E := lams 6 (.app (.app (.var 1) (.var 0))
    (apps (.recur 0 #[1]) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0]))
  let yRec : Ixon.Recursor := ⟨false, false, 1, 0, 0, 2, 3,
    recTyA 1 1 (.app (.var 4) (.var 0)), #[⟨1, yRule⟩]⟩
  let (env, bR) := st env ⟨.muts #[.recr xRec, .recr yRec], #[], #[pA, tA, c1A, c2A, mkA],
    #[.zero, .var 0], #[]⟩
  let (env, xA) := st env (prj (.rPrj ⟨0, bR⟩))
  let (env, yA) := st env (prj (.rPrj ⟨1, bR⟩))
  let pBig : Ixon.Recursor := ⟨false, false, 1, 0, 0, 1, 2,
    .leanAll (.leanAll (.ref 0 #[]) (.sort 1)) (.leanAll (.app (.var 0) (.ref 1 #[]))
      (.leanAll (.app (.var 1) (.ref 2 #[])) (.leanAll (.ref 0 #[]) (.app (.var 3) (.var 0))))),
    #[⟨0, lams 3 (.var 1)⟩, ⟨0, lams 3 (.var 0)⟩]⟩
  let (env, pBigA) := st env ⟨.recr pBig, #[], #[pA, c1A, c2A], #[.zero, .var 0], #[]⟩
  let gVal : E := .leanLam (.ref 0 #[]) (apps (.ref 1 #[1])
    [.leanLam (.ref 0 #[]) (.sort 0), .leanLam (.ref 2 #[]) (.sort 0), .ref 3 #[], .ref 4 #[],
     .leanLam (.ref 0 #[]) (.leanLam (.sort 0) (.var 0)), .app (.ref 5 #[]) (.var 0)])
  let (env, gA) := st env ⟨.defn (dfn .defn (.leanAll (.ref 0 #[]) (.sort 0)) gVal),
    #[], #[pA, yA, tA, b.trueA, b.falseA, mkA], #[.zero, .succ .zero], #[]⟩
  let hVal : E := apps (.ref 3 #[0, 1]) [.ref 4 #[], .sort 0, .ref 5 #[], .ref 6 #[], .ref 7 #[],
    apps (.ref 8 #[0]) [.ref 4 #[], .ref 5 #[]]]
  let hTy : E := apps (.ref 1 #[1]) [.sort 0, .ref 2 #[], .ref 0 #[]]
  let (env, hTFA) := st env ⟨.defn (dfn .thm hTy hVal),
    #[], #[b.falseA, b.eqA, b.trueA, b.congrArgA, pA, c1A, c2A, gA, b.reflA], #[.zero, .succ .zero], #[]⟩
  let (env, badA) := st env ⟨.defn (dfn .thm (.ref 0 #[])
    (apps (.ref 1 #[0]) [.ref 2 #[], .ref 0 #[], .ref 3 #[], .ref 4 #[]])),
    #[], #[b.falseA, b.eqMpA, b.trueA, hTFA, b.trueIntroA], #[.zero], #[]⟩
  let pN : Lean.Name := `MustRejectFx.SplitElim.P
  let tN : Lean.Name := `MustRejectFx.SplitElim.T
  let leanPT : List Lean.Declaration := [
    .inductDecl [] 0 [mkInd pN (.sort .zero)
      [(pN ++ `c1, .const pN []), (pN ++ `c2, .const pN [])]] false,
    .inductDecl [] 0 [mkInd tN (.sort (.succ .zero))
      [(tN ++ `mk, .forallE `p (.const pN []) (.const tN []) .default)]] false]
  let regen := "not the recursor Lean regenerates: Lean's recursor of P has one Prop motive \
    and none for T (P and T are separate blocks), and T.rec does not call it"
  #[chk env ctx "split-elim/inductive-P" "a two-constructor Prop" "legal Lean" pA (mustAccept := true) (lean := leanPT.take 1),
    chk env ctx "split-elim/inductive-T" "T : Type | mk : P → T" "legal Lean" tA (mustAccept := true) (lean := leanPT),
    chk env ctx "split-elim/recursor-X" "a Prop-only recursor of P in a family with T" regen xA,
    chk env ctx "split-elim/recursor-Y" "a large recursor of T that eliminates P into Sort u" regen yA,
    chk env ctx "split-elim/g" "g : P → Prop separating P's constructors" "its closure holds the forged recursor Y" gA,
    chk env ctx "split-elim/true-eq-false" "True = False" "its closure holds the forged recursor Y" hTFA,
    chk env ctx "split-elim/false" "a closed proof of False" "its closure holds the forged recursor Y" badA,
    chk env ctx "split-elim/control-large-recursor-of-P" "a standalone large recursor of a two-constructor Prop"
      "not Lean's P.rec, which eliminates into Prop only" pBigA]

/-! ## The same through a genuine nested occurrence in `Nonempty` -/

def ntB : E := .app (.ref 1 #[2]) (.ref 0 #[])

def recTyB (s : UInt64) (major concl : E) : E :=
  .leanAll (.leanAll (.ref 0 #[]) (.sort s)) <|
  .leanAll (.leanAll ntB (.sort s)) <|
  .leanAll (.leanAll (.sort 0) (.app (.var 2) (.app (.ref 2 #[]) (.var 0)))) <|
  .leanAll (.leanAll ntB (.leanAll (.app (.var 2) (.var 0)) (.app (.var 4) (.app (.ref 3 #[]) (.var 1))))) <|
  .leanAll (.leanAll (.ref 0 #[]) (.leanAll (.app (.var 4) (.var 0))
    (.app (.var 4) (apps (.ref 4 #[2]) [.ref 0 #[], .var 1])))) <|
  .leanAll major concl

def nonemptyNest (b : Base) (ctx : Ix.ClaimContext) : Array MRCase := Id.run do
  let env := b.env
  let nA := b.nonemptyA
  let introA := b.nonemptyIntroA
  let tInd : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[ctor 0 1 (.leanAll (.sort 1) (.recur 0 #[])),
      ctor 1 1 (.leanAll (.app (.ref 0 #[0]) (.recur 0 #[])) (.recur 0 #[]))]⟩
  let (env, bT) := st env ⟨.muts #[.indc tInd], #[], #[nA], #[.succ .zero, .zero], #[]⟩
  let (env, tA) := st env (prj (.iPrj ⟨0, bT⟩))
  let (env, baseA) := st env (prj (.cPrj ⟨0, 0, bT⟩))
  let (env, mkA) := st env (prj (.cPrj ⟨0, 1, bT⟩))
  let tRec : Ixon.Recursor := ⟨false, false, 1, 0, 0, 2, 3,
    recTyB 1 (.ref 0 #[]) (.app (.var 5) (.var 0)),
    #[⟨1, lams 6 (.app (.var 3) (.var 0))⟩,
      ⟨1, lams 6 (.app (.app (.var 2) (.var 0))
        (apps (.recur 1 #[1]) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0]))⟩]⟩
  let nRec : Ixon.Recursor := ⟨false, false, 1, 0, 0, 2, 3,
    recTyB 0 ntB (.app (.var 4) (.var 0)),
    #[⟨1, lams 6 (.app (.app (.var 1) (.var 0))
        (apps (.recur 0 #[1]) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0]))⟩]⟩
  let (env, bR) := st env ⟨.muts #[.recr tRec, .recr nRec], #[],
    #[tA, nA, baseA, mkA, introA], #[.zero, .var 0, .succ .zero], #[]⟩
  let (env, trA) := st env (prj (.rPrj ⟨0, bR⟩))
  let (env, nrA) := st env (prj (.rPrj ⟨1, bR⟩))
  let ntG : E := .app (.ref 0 #[1]) (.ref 2 #[])
  let gVal : E := .leanLam ntG (apps (.ref 1 #[1])
    [.leanLam (.ref 2 #[]) (.sort 0), .leanLam ntG (.sort 0), .leanLam (.sort 0) (.var 0),
     .leanLam ntG (.leanLam (.sort 0) (.var 0)), .leanLam (.ref 2 #[]) (.leanLam (.sort 0) (.var 0)),
     .app (.ref 3 #[]) (.var 0)])
  let (env, gA) := st env ⟨.defn (dfn .defn (.leanAll ntG (.sort 0)) gVal),
    #[], #[nA, trA, tA, mkA], #[.zero, .succ .zero], #[]⟩
  let ntH : E := .app (.ref 4 #[1]) (.ref 9 #[])
  let i1 : E := apps (.ref 5 #[1]) [.ref 9 #[], .app (.ref 6 #[]) (.ref 2 #[])]
  let i2 : E := apps (.ref 5 #[1]) [.ref 9 #[], .app (.ref 6 #[]) (.ref 0 #[])]
  let hVal : E := apps (.ref 3 #[0, 1]) [ntH, .sort 0, i1, i2, .ref 7 #[], apps (.ref 8 #[0]) [ntH, i1]]
  let hTy : E := apps (.ref 1 #[1]) [.sort 0, .ref 2 #[], .ref 0 #[]]
  let (env, hTFA) := st env ⟨.defn (dfn .thm hTy hVal),
    #[], #[b.falseA, b.eqA, b.trueA, b.congrArgA, nA, introA, baseA, gA, b.reflA, tA],
    #[.zero, .succ .zero], #[]⟩
  let (env, badA) := st env ⟨.defn (dfn .thm (.ref 0 #[])
    (apps (.ref 1 #[0]) [.ref 2 #[], .ref 0 #[], .ref 3 #[], .ref 4 #[]])),
    #[], #[b.falseA, b.eqMpA, b.trueA, hTFA, b.trueIntroA], #[.zero], #[]⟩
  let tN : Lean.Name := `MustRejectFx.NonemptyNest.T
  let leanT : Lean.Declaration := .inductDecl [] 0 [mkInd tN (.sort (.succ .zero))
    [(tN ++ `base, .forallE `p (.sort .zero) (.const tN []) .default),
     (tN ++ `mk, .forallE `n (.app (.const ``Nonempty [.succ .zero]) (.const tN []))
       (.const tN []) .default)]] false
  let rejected := "its closure holds T, which Lean's kernel rejects"
  #[chk env ctx "nonempty-nest/inductive-T" "T : Type | base : Prop → T | mk : Nonempty T → T"
      "Lean's kernel rejects T (the nested auxiliary lives in another universe)" tA (lean := [leanT]),
    chk env ctx "nonempty-nest/recursor-T" "T's recursor, large" rejected trA,
    chk env ctx "nonempty-nest/recursor-aux" "the auxiliary recursor, Prop-only" rejected nrA,
    chk env ctx "nonempty-nest/g" "g : Nonempty T → Prop separating two proofs" rejected gA,
    chk env ctx "nonempty-nest/true-eq-false" "True = False" rejected hTFA,
    chk env ctx "nonempty-nest/false" "a closed proof of False" rejected badA]

/-! ## A negative occurrence behind a mutual container's peer -/

def peerNegative (b : Base) (ctx : Ix.ClaimContext) (c1A c2A c1MkA c2MkA c3A : Address) :
    Array MRCase := Id.run do
  let (env, bBad) := st b.env (badBlock c1A)
  let (env, badIndA) := st env (prj (.iPrj ⟨0, bBad⟩))
  let (env, badMkA) := st env (prj (.cPrj ⟨0, 0, bBad⟩))
  let (env, bBad3) := st env (badBlock c3A)
  let (env, bad3IndA) := st env (prj (.iPrj ⟨0, bBad3⟩))
  let (env, _) := st env (prj (.cPrj ⟨0, 0, bBad3⟩))
  let refs : Array Address := #[b.falseA, badIndA, badMkA, c1MkA, c2MkA, c1A, c2A]
  let unwrapF : E := .leanLam (.ref 1 #[])
    (.app (.prj 6 0 (.prj 5 0 (.prj 1 0 (.var 0)))) (.var 0))
  let (env, selfA) := st env ⟨.defn (dfn .defn
    (.leanAll (.ref 1 #[]) (.leanAll (.ref 1 #[]) (.ref 0 #[])))
    (.leanLam (.ref 1 #[]) (.prj 6 0 (.prj 5 0 (.prj 1 0 (.var 0)))))), #[], refs, #[.zero], #[]⟩
  let mkTerm : E := .app (.ref 2 #[]) (apps (.ref 3 #[]) [.ref 1 #[], apps (.ref 4 #[]) [.ref 1 #[], .var 0]])
  let badVal : E := .app (.leanLam (.leanAll (.ref 1 #[]) (.ref 0 #[])) (.app (.var 0) mkTerm)) unwrapF
  let (env, badA) := st env ⟨.defn (dfn .thm (.ref 0 #[]) badVal), #[], refs, #[.zero], #[]⟩
  let rejected := "its closure holds Bad, which Lean's kernel rejects"
  #[chk env ctx "peer-negative/container-C1" "a legal mutual container" "legal Lean (compiled)" c1A (mustAccept := true),
    chk env ctx "peer-negative/inductive-Bad" "Bad | mk : C1 Bad → Bad, negative behind C1's peer C2"
      "Lean's kernel rejects Bad (non-positive occurrence in the auxiliary for C2 Bad)" badIndA
      (lean := [leanBadDecl `MustRejectFx.PeerNegative.Bad ``C1]),
    chk env ctx "peer-negative/ctor-Bad.mk" "Bad's constructor" rejected badMkA,
    chk env ctx "peer-negative/unwrap" "Bad → Bad → False by three projections" rejected selfA,
    chk env ctx "peer-negative/false" "a closed proof of False" rejected badA,
    chk env ctx "peer-negative/control-nonmutual-container" "the same field in a non-mutual container"
      "Lean's kernel rejects it" bad3IndA (lean := [leanBadDecl `MustRejectFx.PeerNegative.Bad3 ``C3])]

def peerChain (b : Base) (ctx : Ix.ClaimContext) (waA wbA wcA waMkA wbMkA wcMkA haA : Address) :
    Array MRCase := Id.run do
  let (env, bBad2) := st b.env (badBlock waA)
  let (env, bad2IndA) := st env (prj (.iPrj ⟨0, bBad2⟩))
  let (env, bad2MkA) := st env (prj (.cPrj ⟨0, 0, bBad2⟩))
  let refs2 : Array Address := #[b.falseA, bad2IndA, bad2MkA, waMkA, wbMkA, wcMkA, waA, wbA, wcA]
  let mkTerm2 : E := .app (.ref 2 #[])
    (apps (.ref 3 #[]) [.ref 1 #[], apps (.ref 4 #[]) [.ref 1 #[], apps (.ref 5 #[]) [.ref 1 #[], .var 0]]])
  let elim2 : E := .leanLam (.ref 1 #[])
    (.app (.prj 8 0 (.prj 7 0 (.prj 6 0 (.prj 1 0 (.var 0))))) (.var 0))
  let bad2Val : E := .app (.leanLam (.leanAll (.ref 1 #[]) (.ref 0 #[])) (.app (.var 0) mkTerm2)) elim2
  let (env, bad2A) := st env ⟨.defn (dfn .thm (.ref 0 #[]) bad2Val), #[], refs2, #[.zero], #[]⟩
  let (env, bBadH) := st env (badBlock haA)
  let (env, badHIndA) := st env (prj (.iPrj ⟨0, bBadH⟩))
  let (env, _) := st env (prj (.cPrj ⟨0, 0, bBadH⟩))
  -- a declared mutual block {A, B}: A.mk : B → A, B.mk : (A → False) → B
  let dmut : Ixon.Constant := ⟨.muts #[
    .indc ⟨false, 0, 0, 0, .sort 0, #[ctor 0 1 (.leanAll (.recur 1 #[]) (.recur 0 #[]))]⟩,
    .indc ⟨false, 0, 0, 0, .sort 0,
      #[ctor 0 1 (.leanAll (.leanAll (.recur 0 #[]) (.ref 0 #[])) (.recur 1 #[]))]⟩],
    #[], #[b.falseA], #[.succ .zero], #[]⟩
  let (env, bDmut) := st env dmut
  let (env, dmutIndA) := st env (prj (.iPrj ⟨0, bDmut⟩))
  let (env, _) := st env (prj (.iPrj ⟨1, bDmut⟩))
  let (env, _) := st env (prj (.cPrj ⟨0, 0, bDmut⟩))
  let (env, _) := st env (prj (.cPrj ⟨1, 0, bDmut⟩))
  let dA : Lean.Name := `MustRejectFx.PeerChain.DA
  let dB : Lean.Name := `MustRejectFx.PeerChain.DB
  let leanDmut : Lean.Declaration := .inductDecl [] 0 [
    mkInd dA (.sort (.succ .zero))
      [(dA ++ `mk, .forallE `x (.const dB []) (.const dA []) .default)],
    mkInd dB (.sort (.succ .zero))
      [(dB ++ `mk, .forallE `x (.forallE `y (.const dA []) (.const ``False []) .default)
        (.const dB []) .default)]] false
  #[chk env ctx "peer-negative/inductive-Bad2-three-peers" "negative occurrence two peers behind the container"
      "Lean's kernel rejects it" bad2IndA (lean := [leanBadDecl `MustRejectFx.PeerChain.Bad2 ``Wa]),
    chk env ctx "peer-negative/false-three-peers" "a closed proof of False" "its closure holds Bad2" bad2A,
    chk env ctx "peer-negative/inductive-BadH-honest" "an honest positive nest through a mutual container"
      "Lean's kernel accepts it" badHIndA (mustAccept := true) (lean := [leanBadDecl `MustRejectFx.PeerChain.BadH ``Ha]),
    chk env ctx "peer-negative/control-declared-mutual-negative" "a declared mutual block with a negative field"
      "Lean's kernel rejects it" dmutIndA (lean := [leanDmut])]

/-! ## Declaration shapes Lean refuses -/

/-- `e` with the domain of its `k`-th leading lambda (from 0) replaced by `d`, a
top-level shared node read through the record's sharing table. -/
partial def setLamDom (sharing : Array E) (e : E) (k : Nat) (d : E) : Option E :=
  match e, k with
  | .share i, _ => sharing[i.toNat]? >>= fun s => setLamDom sharing s k d
  | .lam _ body, 0 => some (.lam d body)
  | .lam t body, k + 1 => (setLamDom sharing body k d).map (.lam t ·)
  | _, _ => none

def shapes (b : Base) (ctx : Ix.ClaimContext) (twoRecA twoA twoAA : Address) :
    Except String (Array MRCase) := do
  let mut out : Array MRCase := #[]
  -- {A : B → Type, B : Type}: A's type mentions its peer B.
  let iiBlock : Ixon.Constant := ⟨.muts #[
    .indc ⟨false, 0, 0, 1, .leanAll (.recur 1 #[]) (.sort 0),
      #[ctor 0 1 (.leanAll (.recur 1 #[]) (.app (.recur 0 #[]) (.var 0)))]⟩,
    .indc ⟨false, 0, 0, 0, .sort 0, #[ctor 0 0 (.recur 1 #[])]⟩],
    #[], #[], #[.succ .zero], #[]⟩
  let (env, iiB) := st b.env iiBlock
  let (env, iiA) := st env (prj (.iPrj ⟨0, iiB⟩))
  let (env, _) := st env (prj (.iPrj ⟨1, iiB⟩))
  let (env, _) := st env (prj (.cPrj ⟨0, 0, iiB⟩))
  let (env, _) := st env (prj (.cPrj ⟨1, 0, iiB⟩))
  let aN : Lean.Name := `MustRejectFx.Shapes.IIA
  let bN : Lean.Name := `MustRejectFx.Shapes.IIB
  out := out.push (chk env ctx "shapes/inductive-inductive" "A : B → Type with B its peer"
    "Lean's kernel rejects the block" iiA (lean := [.inductDecl [] 0 [
      mkInd aN (.forallE `b (.const bN []) (.sort (.succ .zero)) .default)
        [(aN ++ `mk, .forallE `b (.const bN []) (.app (.const aN []) (.bvar 0)) .default)],
      mkInd bN (.sort (.succ .zero)) [(bN ++ `mk, .const bN [])]] false]))
  -- T (A : Type) | node : List (T Nat) → T A
  let nuBlock : Ixon.Constant := ⟨.muts #[.indc ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
    #[ctor 0 1 (params := 1) (.leanAll (.sort 0)
        (.leanAll (.app (.ref 0 #[1]) (.app (.recur 0 #[]) (.ref 1 #[]))) (.app (.recur 0 #[]) (.var 1))))]⟩],
    #[], #[b.listA, b.natA], #[.succ .zero, .zero], #[]⟩
  let (env, nuB) := st b.env nuBlock
  let (env, nuA) := st env (prj (.iPrj ⟨0, nuB⟩))
  let (env, _) := st env (prj (.cPrj ⟨0, 0, nuB⟩))
  let tN : Lean.Name := `MustRejectFx.Shapes.NU
  out := out.push (chk env ctx "shapes/nonuniform-nested" "T A | node : List (T Nat) → T A"
    "Lean's kernel rejects it" nuA (lean := [.inductDecl [] 1 [mkInd tN
      (.forallE `A (.sort (.succ .zero)) (.sort (.succ .zero)) .default)
      [(tN ++ `node, .forallE `A (.sort (.succ .zero))
        (.forallE `x (.app (.const ``List [.zero]) (.app (.const tN []) (.const ``Nat [])))
          (.app (.const tN []) (.bvar 1)) .default) .default)]] false]))
  -- peers that disagree on universe count, or on safety
  let peers (aLvls : UInt64) (aUnsafe : Bool) : Ixon.Constant := ⟨.muts #[
    .indc ⟨aUnsafe, aLvls, 0, 0, .sort 0, #[ctor 0 0 (.recur 0 #[]) (lvls := aLvls) (isUnsafe := aUnsafe)]⟩,
    .indc ⟨false, 0, 0, 0, .sort 0, #[ctor 0 0 (.recur 1 #[])]⟩],
    #[], #[], #[.succ .zero], #[]⟩
  for (name, blk) in [("shapes/peer-universe-counts", peers 1 false), ("shapes/peer-safety", peers 0 true)] do
    let (env, pb) := st b.env blk
    let (env, _) := st env (prj (.iPrj ⟨0, pb⟩))
    let (env, pbb) := st env (prj (.iPrj ⟨1, pb⟩))
    let (env, _) := st env (prj (.cPrj ⟨0, 0, pb⟩))
    let (env, _) := st env (prj (.cPrj ⟨1, 0, pb⟩))
    out := out.push (chk env ctx name "peers of one mutual block with different universe counts or safety"
      "no Lean declaration produces it: an inductDecl has one level list and one safety flag" pbb)
  -- a partial definition that uses an unsafe one: `u : Type := Prop` (unsafe), `p : Type := u`
  let (env, uA) := st b.env ⟨.defn (dfn .defn (.sort 0) (.sort 1) (safety := .unsaf)), #[], #[],
    #[.succ .zero, .zero], #[]⟩
  let (env, pA) := st env ⟨.defn (dfn .defn (.sort 0) (.ref 0 #[]) (safety := .part)), #[], #[uA],
    #[.succ .zero], #[]⟩
  let uN : Lean.Name := `MustRejectFx.Shapes.u
  let pN : Lean.Name := `MustRejectFx.Shapes.p
  let ty : Lean.Expr := .sort (.succ .zero)
  out := out.push (chk env ctx "shapes/partial-uses-unsafe" "a partial definition whose value is unsafe"
    "Lean's kernel rejects the partial definition" pA (lean := [
      mkDefn uN ty (.sort .zero) .unsafe, mkDefn pN ty (.const uN []) .partial]))
  -- a safe seed `s : Type := A`, `A` the safe member of a definition block whose other member
  -- `U : Type := Prop → Prop` is unsafe: the seed passes the seed check, and the walk reaches
  -- the block through `A`
  let mixed : Ixon.Constant := ⟨.muts #[.defn (dfn .defn (.sort 0) (.sort 1)),
    .defn (dfn .defn (.sort 0) (.leanAll (.sort 1) (.sort 1)) (safety := .unsaf))], #[], #[],
    #[.succ .zero, .zero], #[]⟩
  let (env, mb) := st b.env mixed
  let (env, mA) := st env (prj (.dPrj ⟨0, mb⟩))
  let (env, _) := st env (prj (.dPrj ⟨1, mb⟩))
  let (env, sA) := st env ⟨.defn (dfn .defn (.sort 0) (.ref 0 #[])), #[], #[mA], #[.succ .zero], #[]⟩
  out := out.push (chk env ctx "shapes/mixed-safety-block"
    "a safe seed using the safe member of a block whose other member is unsafe"
    "no Lean declaration produces it: a mutual definition carries one safety" sA)
  -- a recursor with one more universe parameter than its inductive's plus the motive's
  let some rc := b.env.getConst? twoRecA | throw "Two.rec is not in the compiled environment"
  let (env, eA) ← match rc.info with
    | .recr r => pure (st b.env { rc with info := .recr { r with lvls := r.lvls + 1 } })
    | .rPrj p => do
      let some blk := b.env.getConst? p.block | throw "Two.rec's block is missing"
      let .muts ms := blk.info | throw "Two.rec's block is not a mutual block"
      let some (.recr r) := ms[p.idx.toNat]? | throw "Two.rec's member is not a recursor"
      let (env, nb) := st b.env { blk with info := .muts (ms.set! p.idx.toNat (.recr { r with lvls := r.lvls + 1 })) }
      pure (st env (prj (.rPrj ⟨p.idx, nb⟩)))
    | _ => throw "Two.rec is neither a recursor nor a recursor projection"
  out := out.push (chk env ctx "shapes/recursor-extra-universe" "Two.rec declaring an unused extra universe parameter"
    "differs from the recursor Lean regenerates (its level count is one more)" eA)
  -- Two.rec whose rule for `Two.a` binds its third argument (the minor for `Two.b`) at
  -- `motive Two.a`; the rule's body is unchanged. The record's binder data are dropped: the
  -- harness recomputes them for the rewritten rule.
  let retarget (r : Ixon.Recursor) (refs : Array Address) (sharing : Array E) :
      Except String Ixon.Recursor := do
    let some ia := refs.findIdx? (· == twoAA) | throw "Two.rec does not reference Two.a"
    let some r0 := r.rules[0]? | throw "Two.rec has no rule"
    let some rhs := setLamDom sharing r0.rhs 2 (.app (.var 1) (.ref ia.toUInt64 #[]))
      | throw "Two.rec's first rule is not a lambda telescope of three binders"
    pure { r with rules := r.rules.set! 0 { r0 with rhs } }
  let (env, dA) ← match rc.info with
    | .recr r => do
      let r' ← retarget r rc.refs rc.sharing
      pure (st b.env { rc with info := .recr r', binders := #[] })
    | .rPrj p => do
      let some blk := b.env.getConst? p.block | throw "Two.rec's block is missing"
      let .muts ms := blk.info | throw "Two.rec's block is not a mutual block"
      let some (.recr r) := ms[p.idx.toNat]? | throw "Two.rec's member is not a recursor"
      let r' ← retarget r blk.refs blk.sharing
      let (env, nb) := st b.env { blk with info := .muts (ms.set! p.idx.toNat (.recr r')), binders := #[] }
      pure (st env (prj (.rPrj ⟨p.idx, nb⟩)))
    | _ => throw "Two.rec is neither a recursor nor a recursor projection"
  out := out.push (chk env ctx "shapes/rule-binder-domain"
    "Two.rec whose first rule binds its third argument at another minor's type"
    "differs from the recursor Lean regenerates (a rule's binder domain is not its recursor type's)" dA)
  -- a misnumbered constructor whose block is assumed
  let some w := b.env.getConst? twoA | throw "Two is not in the compiled environment"
  let .iPrj p := w.info | throw "Two is not an inductive projection"
  let some blk := b.env.getConst? p.block | throw "Two's block is missing"
  let .muts ms := blk.info | throw "Two's block is not a mutual block"
  let some (.indc ind) := ms[p.idx.toNat]? | throw "Two's member is not an inductive"
  let ctors := ind.ctors.mapIdx fun i k => { k with cidx := (ind.ctors.size - 1 - i).toUInt64 }
  let (env, fb) := st b.env { blk with info := .muts (ms.set! p.idx.toNat (.indc { ind with ctors })) }
  let (env, fi) := st env (prj (.iPrj ⟨p.idx, fb⟩))
  let (env, fc0) := st env (prj (.cPrj ⟨p.idx, 0, fb⟩))
  let (env, _) := st env (prj (.cPrj ⟨p.idx, 1, fb⟩))
  -- d : Two' := Two'.a; its type and value reach the forged block
  let (env, dA) := st env ⟨.defn (dfn .defn (.ref 0 #[]) (.ref 1 #[])), #[], #[fi, fc0], #[], #[]⟩
  let some tree := Ix.AssumptionTree.canonical #[fb] | throw "empty assumption tree"
  let assumed := chk env ctx "shapes/ctor-index-assumed-block"
    "constructor indices swapped in a block the claim assumes"
    "not Lean's constructor numbering; iota would pick the other rule" dA
  out := out.push { assumed with
    claim := .check ctx dA (some tree.root), trees := ({} : Std.HashMap _ _).insert tree.root tree }
  out := out.push (chk env ctx "shapes/ctor-index-walked-block" "the same block, walked"
    "not Lean's constructor numbering" dA)
  -- Control: a zero-constructor inductive (`False`) with its safety flag flipped has no
  -- constructor flag to disagree with, so it is a valid `unsafe inductive : Prop`, which
  -- Lean's kernel accepts.
  let some fw := b.env.getConst? b.falseA | throw "False is not in the compiled environment"
  let .iPrj fp := fw.info | throw "False is not an inductive projection"
  let some fblk := b.env.getConst? fp.block | throw "False's block is missing"
  let .muts fms := fblk.info | throw "False's block is not a mutual block"
  let some (.indc find) := fms[fp.idx.toNat]? | throw "False's member is not an inductive"
  unless find.ctors.isEmpty do throw "False has a constructor"
  let (env, fb2) := st b.env
    { fblk with info := .muts (fms.set! fp.idx.toNat (.indc { find with isUnsafe := !find.isUnsafe })) }
  let (env, fi2) := st env (prj (.iPrj ⟨fp.idx, fb2⟩))
  let eN : Lean.Name := `MustRejectFx.Shapes.E
  out := out.push (chk env ctx "shapes/control-zero-ctor-safety-flip"
    "False with its safety flag flipped (no constructor to disagree with)"
    "Lean's kernel accepts an unsafe inductive with no constructors" fi2 (mustAccept := true)
    (lean := [.inductDecl [] 0 [mkInd eN (.sort .zero) []] true]))
  return out

/-! ## Structure eta and unit-like conversion in recursive mutual and nested blocks -/

/-- `fun x₁ … xₙ => Eq.refl lhs` for a statement `∀ x₁ … xₙ, lhs = rhs`. -/
partial def rflProof : Lean.Expr → Option Lean.Expr
  | .forallE n t b bi => (rflProof b).map (.lam n t · bi)
  | .mdata _ e => rflProof e
  | e => match e.getAppFn, e.getAppArgs with
    | .const ``Eq us, #[T, l, _] => some (Lean.mkApp2 (.const ``Eq.refl us) T l)
    | _, _ => none

/-- The statements, as `(case, theorem name, statement, Lean accepts)`. -/
def etaTheorems : List (String × Lean.Name × Lean.Name × Bool) := [
  ("eta/ePos", `MustRejectFx.Eta.ePos, ``stPos, false),
  ("eta/iPos", `MustRejectFx.Eta.iPos, ``stPosi, false),
  ("eta/uTag", `MustRejectFx.Eta.uTag, ``stTag, false),
  ("eta/eAttr", `MustRejectFx.Eta.eAttr, ``stAttr, false),
  ("eta/control-eLone", `MustRejectFx.Eta.eLone, ``stLone, true),
  ("eta/control-iLone", `MustRejectFx.Eta.iLone, ``stLonei, true),
  ("eta/control-uLU", `MustRejectFx.Eta.uLU, ``stLU, true),
  ("eta/control-eDS", `MustRejectFx.Eta.eDS, ``stDS, true),
  ("eta/control-iDS", `MustRejectFx.Eta.iDS, ``stDSi, true),
  ("eta/control-uDU", `MustRejectFx.Eta.uDU, ``stDU, true)]

/-- The theorem `thm : stmt := rfl` as a Lean declaration. -/
def etaDecl (leanEnv : Lean.Environment) (thm stmt : Lean.Name) : Except String Lean.Declaration := do
  let some (.defnInfo dv) := leanEnv.find? stmt | throw s!"no statement {stmt}"
  let some pf := rflProof dv.value | throw s!"{stmt} is not an Eq telescope"
  return .thmDecl { name := thm, levelParams := [], type := dv.value, value := pf }

/-- The eta cases: each theorem added to a copy of the environment without the
kernel (so that the compiler can compile what Lean refuses), compiled with the
repository's compiler, and checked. -/
def eta (leanEnv : Lean.Environment) : IO (Array MRCase) := do
  let mut kenv := leanEnv.toKernelEnv
  let mut decls : Array (String × Lean.Name × Lean.Declaration × Bool) := #[]
  for (name, thm, stmt, accepts) in etaTheorems do
    let d ← IO.ofExcept (etaDecl leanEnv thm stmt)
    kenv ← match kenv.addDeclWithoutChecking d with
      | .ok k => pure k
      | .error _ => throw (IO.userError s!"{thm} could not be added")
    decls := decls.push (name, thm, d, accepts)
  let env' := Lean.Environment.ofKernelEnv kenv
  let ixon ← loadSharedIxonEnv ((decls.map (·.2.1)) ++ #[``loneEta]) env'
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixon)
  let mut out := #[]
  for (name, thm, d, accepts) in decls do
    let a ← lookupAddr ixon thm
    -- Lean's verdict is taken under a fresh name: the theorem is already in `env'`.
    let fresh := match d with
      | .thmDecl tv => Lean.Declaration.thmDecl { tv with name := thm ++ `oracle, all := [thm ++ `oracle] }
      | other => other
    let oracle := if accepts then "the kernel accepts it" else "the kernel rejects it"
    out := out.push (chk ixon ctx name s!"{thm} by rfl" oracle a (mustAccept := accepts) (lean := [fresh]))
  let a ← lookupAddr ixon ``loneEta
  out := out.push (chk ixon ctx "eta/control-loneEta" "ordinary Lean: p = mk p.a p.b by rfl"
    "elaborated and checked by Lean" a (mustAccept := true))
  return out

/-! ## Runner -/

/-- Lean's verdict on `decls`, added in order: `none` if every one is accepted,
else the first error. -/
def leanVerdict (leanEnv : Lean.Environment) (decls : List Lean.Declaration) :
    IO (Option String) := do
  let mut kenv := leanEnv.toKernelEnv
  for d in decls do
    match kenv.addDecl {} d with
    | .ok k => kenv := k
    | .error e => return some (← (e.toMessageData {}).toString)
  return none

def MRCase.toCase (c : MRCase) : Except String Tests.Ix.IxVM.Case :=
  match knownDivergences.lookup c.name with
  | some finding =>
    -- Submitted with the program's verdict: the host fails it once that changes.
    Tests.Ix.IxVM.Case.ofClaim
      s!"KNOWN DIVERGENCE [{finding}] {c.name} (required: {if c.mustAccept then "accept" else "reject"}; \
        {c.oracle}): {c.intent}" c.env c.claim c.trees (accept := !c.mustAccept)
  | none =>
    let reason := if c.mustAccept then none else c.rejectsWith <|> rejectionReasons.lookup c.name
    Tests.Ix.IxVM.Case.ofClaim
      s!"{if c.mustAccept then "MUST ACCEPT" else "MUST REJECT"} {c.name} ({c.oracle}): {c.intent}"
      c.env c.claim c.trees (accept := c.mustAccept) (rejectsWith := reason)

/-- Every case of the gate. -/
def cases (leanEnv : Lean.Environment) : IO (Array MRCase) := do
  let base ← loadSharedIxonEnv
    #[``False, ``True, ``True.intro, ``Eq, ``Eq.refl, ``Eq.mp, ``congrArg, ``Nonempty,
      ``Nonempty.intro, ``List, ``Nat, ``C1, ``C2, ``C1.mk, ``C2.mk, ``C3, ``C3.mk,
      ``Wa, ``Wb, ``Wc, ``Wa.mk, ``Wb.mk, ``Wc.mk,
      ``Ha, ``Ha.mk, ``Hb, ``Hb.mk, ``Two, ``Two.a, ``Two.rec] leanEnv
  let lk := lookupAddr base
  let b : Base := {
    env := base, falseA := ← lk ``False, trueA := ← lk ``True, trueIntroA := ← lk ``True.intro,
    eqA := ← lk ``Eq, reflA := ← lk ``Eq.refl, eqMpA := ← lk ``Eq.mp, congrArgA := ← lk ``congrArg,
    nonemptyA := ← lk ``Nonempty, nonemptyIntroA := ← lk ``Nonempty.intro,
    listA := ← lk ``List, natA := ← lk ``Nat }
  let ctx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
  let mut out := splitElim b ctx ++ nonemptyNest b ctx
  out := out ++ peerNegative b ctx (← lk ``C1) (← lk ``C2) (← lk ``C1.mk) (← lk ``C2.mk) (← lk ``C3)
  out := out ++ peerChain b ctx (← lk ``Wa) (← lk ``Wb) (← lk ``Wc) (← lk ``Wa.mk) (← lk ``Wb.mk)
    (← lk ``Wc.mk) (← lk ``Ha)
  out := out ++ (← IO.ofExcept (shapes b ctx (← lk ``Two.rec) (← lk ``Two) (← lk ``Two.a)))
  out := out ++ (← eta leanEnv)
  return out

/-- The gate. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let cases ← cases leanEnv
  let mut problems := 0
  -- Every listed name must be a case; every case name must be unique.
  for (n, _) in knownDivergences do
    unless cases.any (·.name == n) do
      IO.eprintln s!"[ixvm-must-reject] known divergence {n} is not a case"
      problems := problems + 1
  -- Lean's kernel must agree with every requirement that rests on it.
  for c in cases do
    unless c.lean.isEmpty do
      let v ← leanVerdict leanEnv c.lean
      let accepted := v.isNone
      let shown := match v with
        | none => "accepted"
        | some e => s!"rejected: {(e.replace "\n" " ").take 160}"
      IO.println s!"[ixvm-must-reject] Lean's kernel on {c.name}: {shown}"
      unless accepted == c.mustAccept do
        IO.eprintln s!"[ixvm-must-reject] FAIL: {c.name} requires \
          {if c.mustAccept then "acceptance" else "rejection"}, but Lean's kernel disagrees"
        problems := problems + 1
  let code ← Tests.Ix.IxVM.runCases "ixvm-must-reject" (circuit := some true)
    (cases.map fun c _ => c.toCase)
  let known := cases.filter fun c => knownDivergences.lookup c.name |>.isSome
  IO.println s!"[ixvm-must-reject] {cases.size} cases; {known.size} known divergences \
    (reported, not failing):"
  for c in known do
    IO.println s!"  - {c.name} [{(knownDivergences.lookup c.name).getD ""}]: required \
      {if c.mustAccept then "accept" else "reject"} ({c.oracle})"
  return if code == 0 && problems == 0 then 0 else 1

end Tests.Ix.IxVM.MustReject
