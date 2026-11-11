import IxCK.Kernel.Core
import IxCC.Src.Semantics
import IxCC.Src.Readback
import IxCC.Src.Relevance.Syntax

/-!
# The grounding development's syntax (`IxCCGrounding.Syntax`)

Everything the grounding statements say about terms, the program, the kernel's reading and the
certificate's annotation, and nothing about models: so the Boolean checks (`IxCCGrounding.Check`)
and the suite that runs them on closure bytes (`tests-grounding`) import neither the kernel's
model (`IxCK.Kernel.Denotes`) nor any proof about it.

* the kernel terms of the fragment's constants (`primKey`, `litE`, `primApp`), telescopes and lifts;
* the node-for-node correspondence of a Src term and a kernel term (`TermCorr`);
* `Ok`, the certificate's datum of which constant instances SrcEval may unfold, and its closure
  (`OkClosed`, decided by `okClosedB`);
* the shapes the checks decide: an `eqn` entry's (`EqnShape`), a `case` entry's (`CaseStored`,
  `CaseProg`), the faithfulness clauses (`Faith`), the `Nat` basis (`NatBasis`), and their
  conjunction (`GroundFacts`);
* what SrcEval runs a constant as (`RunPair`) and the application sites it may evaluate there
  (`evalSites`), over which the typing hypothesis (`SitesOk`, in `IxCCGrounding.Runs`) ranges.

The `case` builders are the specification the check decides; `tests-grounding` checks them
against the committed closures.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

abbrev KExpr := Ix.Kernel.Expr .anon
abbrev KKey := Ix.Kernel.Key .anon
abbrev KEnv := Ix.Kernel.Env .anon

/-! ## Primitives and literals -/

section Prims

variable {md : Mode}

/-- The kernel's role key of one of SrcEval's fifteen primitives. -/
def primKey : IxCC.Src.PrimOp → Key md
  | .add => natAddName | .sub => natSubName | .mul => natMulName | .div => natDivName
  | .mod => natModName | .pow => natPowName | .gcd => natGcdName | .beq => natBeqName
  | .ble => natBleName | .land => natLandName | .lor => natLorName | .xor => natXorName
  | .shiftLeft => natShiftLeftName | .shiftRight => natShiftRightName | .pred => natPredName

/-- A `Nat` literal as a kernel term. -/
def litE (n : Nat) : Expr md := .lit (.natVal n)

/-- A primitive's result as a kernel term. -/
def primResultE : IxCC.Src.PrimResult → Expr md
  | .nat n => litE n
  | .bool true => .const boolTrueName []
  | .bool false => .const boolFalseName []

/-- A primitive applied to literals, as a kernel term (`pred` takes one). -/
def primApp (op : IxCC.Src.PrimOp) (a b : Nat) : Expr md :=
  if op.arity = 1 then .app (.const (primKey op) []) (litE a)
  else .app (.app (.const (primKey op) []) (litE a)) (litE b)


end Prims

/-- Binder data: never a proposition; a proposition exactly where the parameter `0` is zero. -/
def bmN : BinderMeta := { pw := PropWhen.never }
def bmZ : BinderMeta := { pw := PropWhen.ifAllZero [0] }

def natK : KExpr := .const natName []
def zeroK : KExpr := .const natZeroName []
def succK : KExpr := .const natSuccName []

/-- `Nat → Nat`, with its binder datum. -/
def natFnType : KExpr := .forallE natK natK bmN

/-- `Eq.{u} : ∀ {α : Sort u}, α → α → Prop`, as the kernel stores it. -/
def eqType : KExpr :=
  .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) bmN) bmN) bmN

/-- The built-in `Eq` is stored with its type, which the `eqn` lemma reads. -/
def EqBasis (env : KEnv) : Prop :=
  ∃ ci : ConstantInfo .anon, env.find? eqName = some ci ∧ ci.toConstantVal.levelParams = [0] ∧
    ci.toConstantVal.type = eqType

/-! ## Correspondence -/

/-- A Src universe and a kernel level correspond: Src's variable `i` is the parameter `lps[i]`. -/
inductive UnivCorr (lps : List Nat) : IxCC.Ixon.Univ → Level → Prop
  | zero : UnivCorr lps .zero .zero
  | succ {u : IxCC.Ixon.Univ} {l : Level} : UnivCorr lps u l → UnivCorr lps (.succ u) (.succ l)
  | max {a b : IxCC.Ixon.Univ} {c d : Level} :
      UnivCorr lps a c → UnivCorr lps b d → UnivCorr lps (.max a b) (.max c d)
  | imax {a b : IxCC.Ixon.Univ} {c d : Level} :
      UnivCorr lps a c → UnivCorr lps b d → UnivCorr lps (.imax a b) (.imax c d)
  | var {i : UInt64} {p : Nat} : lps[i.toNat]? = some p → UnivCorr lps (.var i) (.param p)

/-- SrcEval's concrete levels `ls` and the assignment `φ` agree on the kernel parameters `lps`. -/
def LvAt (φ : LevelParam → Nat) (lps : List Nat) (ls : Levels) : Prop :=
  ∀ i p, lps[i]? = some p → φ p = ls.getD i 0

/-- A Src term corresponds to a kernel term node for node (no `let`, no string literal: the
first fragment). Decided by a Boolean check on the bytes. -/
inductive TermCorr (κ : CId → KKey) (lps : List Nat) : Term → KExpr → Prop
  | var {i : Nat} : TermCorr κ lps (.var i) (.bvar i)
  | sort {u : IxCC.Ixon.Univ} {l : Level} : UnivCorr lps u l → TermCorr κ lps (.sort u) (.sort l)
  | const {c : CId} {us : List IxCC.Ixon.Univ} {ls : List Level} :
      us.length = ls.length →
      (∀ (i : Nat) (u : IxCC.Ixon.Univ) (l : Level), us[i]? = some u → ls[i]? = some l →
        UnivCorr lps u l) →
      TermCorr κ lps (.const c us) (.const (κ c) ls)
  | app {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel} {f' a' : KExpr} :
      TermCorr κ lps f f' → TermCorr κ lps a a' → TermCorr κ lps (.app f a m r) (.app f' a')
  | lam {b : IxCC.Src.Binder} {d body : Term} {d' body' : KExpr} {mb : BinderMeta} :
      TermCorr κ lps d d' → TermCorr κ lps body body' →
      TermCorr κ lps (.lam b d body) (.lam d' body' mb)
  | pi {b : IxCC.Src.Binder} {r : IxCC.Ixon.V3.ValueContract} {d c : Term} {d' c' : KExpr}
      {mb : BinderMeta} :
      TermCorr κ lps d d' → TermCorr κ lps c c' → TermCorr κ lps (.pi b r d c) (.forallE d' c' mb)
  | proj {s : CId} {i : Nat} {e : Term} {e' : KExpr} :
      TermCorr κ lps e e' → TermCorr κ lps (.proj s i e) (.proj (κ s) i e')
  | natLit {n : Nat} : TermCorr κ lps (.natLit n) (.lit (.natVal n))

/-- Every bound variable of a kernel term is below `n` (under its binders): the term is closed
in a context of `n` binders. -/
def bvarsLt : Nat → KExpr → Bool
  | n, .bvar i => decide (i < n)
  | n, .app f a => bvarsLt n f && bvarsLt n a
  | n, .lam d b _ => bvarsLt n d && bvarsLt (n + 1) b
  | n, .forallE d b _ => bvarsLt n d && bvarsLt (n + 1) b
  | n, .letE t v b _ => bvarsLt n t && bvarsLt n v && bvarsLt (n + 1) b
  | n, .proj _ _ e => bvarsLt n e
  | _, _ => true

/-- The number of leading `∀`s of a kernel term, syntactically. -/
def kPis : KExpr → Nat
  | .forallE _ b _ => kPis b + 1
  | _ => 0

/-- Every constant a Src term names is in `S`. -/
def ConstsIn (S : CId → Prop) (t : Term) : Prop :=
  ∀ c, t.mentions c = true → S c

/-! ## `Ok`, a datum of the certificate, and its closure

`Ok c ls` reads the annotation's class of the constant `c` (`ConstRel.result`, which the kernel
annotator computes from `c`'s stored type: `proof w` with `w` the zero condition of its sort, or
`type`, or `rel`): SrcEval may unfold `c` at `ls` when the class is not irrelevant there. The
datum's correctness is not a hypothesis of anything: `Ok` only indexes where the typing
hypothesis is asked. What soundness needs is that it contains the root and is *closed* (every
constant at a position SrcEval may evaluate, in a run term of an `Ok` instance, is at an `Ok`
instance), and closure is decided per constant and per profile of its level parameters
(`okClosedB`). That it passes is what a complete annotation (relevance in the proof direction,
KF-1) gives; `tests-grounding` runs it on the committed closures. -/

/-- The annotation's class of `c`. -/
def constClass (ann : IxCC.Src.Relevance.Ann) (c : CId) : Option IxCC.Src.Rel :=
  (ann.constRel? c).map (·.result)

/-- The number of level parameters of `c` in the program. -/
def lvlsOf (p : Program) (c : CId) : Nat := ((p.decl? c).map IxCC.Src.Decl.lvls).getD 0

/-- **`Ok`**: `ls` instantiates `c`'s level parameters, and the annotation classifies `c` as
neither a proof nor a type there. -/
def Ok (p : Program) (ann : IxCC.Src.Relevance.Ann) (c : CId) (ls : Levels) : Prop :=
  ls.length = lvlsOf p c ∧ ∃ r, constClass ann c = some r ∧ r.irrAt ls = false

/-- The terms SrcEval unfolds `c` to: its value (a safe definition without a table entry), or
its `eqn` body. -/
def runTerms (p : Program) (c : CId) : List Term :=
  match p.table.resolveOf c with
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => [v]
    | _ => []
  | some (.eqn _ body) => [body]
  | _ => []

/-- The constant nodes at positions SrcEval may evaluate at `ls`: not under an argument
irrelevant at `ls`, not inside a type; under λ bodies and projections. -/
def evalConsts (ls : Levels) : Term → List (CId × List IxCC.Ixon.Univ)
  | .const c us => [(c, us)]
  | .app f a _ r => evalConsts ls f ++ (if r.irrAt ls then [] else evalConsts ls a)
  | .lam _ _ body => evalConsts ls body
  | .proj _ _ e => evalConsts ls e
  | _ => []

/-- The same at a profile (which parameters are zero). -/
def evalConstsP (prof : IxCC.Src.Profile) : Term → List (CId × List IxCC.Ixon.Univ)
  | .const c us => [(c, us)]
  | .app f a _ r => evalConstsP prof f ++ (if r.irrP prof then [] else evalConstsP prof a)
  | .lam _ _ body => evalConstsP prof body
  | .proj _ _ e => evalConstsP prof e
  | _ => []

/-- **`Ok` is closed** on `S`. -/
def OkClosed (p : Program) (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls, S c → Ok p ann c ls → ∀ t ∈ runTerms p c,
    ∀ d us, (d, us) ∈ evalConsts ls t → Ok p ann d (us.map (IxCC.Src.evalUniv ls))

/-- Every profile of `n` parameters. -/
def profiles : Nat → List IxCC.Src.Profile
  | 0 => [[]]
  | n + 1 => (profiles n).flatMap fun prof => [prof ++ [true], prof ++ [false]]

/-- **The closure check**: per constant of `Sl` and per profile of its parameters at which it is
`Ok`, every constant at an evaluated position is `Ok` at the instantiated profile. -/
def okClosedB (p : Program) (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  Sl.all fun c =>
    (runTerms p c).all fun t =>
      (profiles (lvlsOf p c)).all fun prof =>
        match constClass ann c with
        | none => true
        | some r =>
          r.irrP prof || (evalConstsP prof t).all fun (d, us) =>
            us.length == lvlsOf p d &&
            match constClass ann d with
            | some r' => !((r'.irrWhen.inst us).holdsP prof)
            | none => false

/-! ## Telescopes, and the shape of an `eqn` entry

An `eqn` entry is checked against its stored equation theorem: any telescope of arguments, any
result type (the inhabited `Eq` forces both sides into its type, whatever it is). Its lemma
(`IxCCGrounding.Eqn`) needs no law and no typing hypothesis: `mem` of the function, of the
theorem and of `Eq`, and `eq_equality`. -/

/-- A ∀-telescope and a λ-telescope. -/
def piTele : List (KExpr × BinderMeta) → KExpr → KExpr
  | [], b => b
  | (A, m) :: rest, b => .forallE A (piTele rest b) m

def lamTele : List (KExpr × BinderMeta) → KExpr → KExpr
  | [], b => b
  | (A, m) :: rest, b => .lam A (lamTele rest b) m

/-- `n` consecutive variables from `k`, outermost first: `#(k+n-1) … #k`. -/
def bvarsFrom (k n : Nat) : List KExpr := (List.range n).reverse.map fun i => .bvar (k + i)

/-- An `eqn` entry's data, read off the stored theorem and function. -/
structure EqnData where
  /-- the theorem's binders (domains, and the theorem's own binder data) -/
  Ds : List (KExpr × BinderMeta)
  /-- the function's binder data, which the equation body's λs take -/
  ms : List BinderMeta
  u : Level
  T : KExpr
  rhs : KExpr
  /-- the function's result type -/
  R : KExpr

/-- The equation body's kernel term: `λ Ds. rhs`, with the function's binder data. -/
def EqnData.body (d : EqnData) : KExpr :=
  lamTele (d.Ds.zipWith (fun b m => (b.1, m)) d.ms) d.rhs

/-- **The checked shape of an `eqn` entry**: the theorem `thm` is stored with type
`∀ Ds, @Eq.{u} T (f.{ps} #(n-1) … #0) rhs`, `ps` the function's level parameters, and the
function `c` with type `∀ Ds, R` over the same domains with its own binder data. -/
def EqnShape (env : KEnv) (κ : CId → KKey) (c thm : CId) (d : EqnData) : Prop :=
  EqBasis env ∧ ∃ (ciF : ConstantInfo .anon) (cvT : ConstantVal .anon) (pf : KExpr),
    env.find? (κ c) = some ciF ∧ env.find? (κ thm) = some (.thmInfo cvT pf) ∧
    d.Ds.length = d.ms.length ∧ cvT.levelParams = ciF.toConstantVal.levelParams ∧
    cvT.type = piTele d.Ds (Expr.mkAppN (.const eqName [d.u])
      [d.T, Expr.mkAppN (.const (κ c) (cvT.levelParams.map Level.param))
        (bvarsFrom 0 d.Ds.length), d.rhs]) ∧
    ciF.toConstantVal.type = piTele (d.Ds.zipWith (fun b m => (b.1, m)) d.ms) d.R

/-! ## What SrcEval runs, and the application sites it may evaluate -/

/-- What `c` runs as, paired with its kernel term: its stored value, or its `eqn` body
against the equation body read off the stored theorem. -/
inductive RunPair (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) : Term → KExpr → Prop
  | value {lvls : Nat} {ty v : Term} {cv : ConstantVal .anon} {val : KExpr}
      {hint : ReducibilityHint} :
      p.table.resolveOf c = none → p.decl? c = some (.defn .defn .safe lvls ty v) →
      env.find? (κ c) = some (.defnInfo cv val hint) → RunPair p env κ c v val
  | eqn {thm : CId} {body : Term} {d : EqnData} :
      p.table.resolveOf c = some (.eqn thm body) → EqnShape env κ c thm d →
      RunPair p env κ c body d.body

/-- The application sites SrcEval may evaluate at `ls`, each with its context: every
application reached through functions, arguments relevant at `ls`, λ bodies and projections. -/
def evalSites (ls : Levels) : List KExpr → Term → KExpr → List (List KExpr × KExpr × KExpr)
  | Γ, .app f a _ r, .app f' a' =>
    (Γ, f', a') :: (evalSites ls Γ f f' ++ (if r.irrAt ls then [] else evalSites ls Γ a a'))
  | Γ, .lam _ _ body, .lam d' body' _ => evalSites ls (d' :: Γ) body body'
  | Γ, .proj _ _ e, .proj _ _ e' => evalSites ls Γ e e'
  | _, _, _ => []

/-! ## The checked shape of a `case` entry

`casesOn` is stored as `λ ps motive t minors. rec.{lps} ps motive W₀ … W_{n-1} t`, each `Wⱼ`
being `λ fields ihs. minorⱼ fields` over the recursor's minor premise's binders (or the minor
itself when there are none); the recursor's rules are `λ ps motive minors fields. minorⱼ fields
ihs`, each induction hypothesis the recursor at a recursive field. No indices (the first
fragment). The builders below are the specification the check decides. -/

/-- Lift each binder's domain of a telescope by `k` above `c` (the cutoff growing by one per
binder). -/
def liftTele (k : Nat) : Nat → List (KExpr × BinderMeta) → List (KExpr × BinderMeta)
  | _, [] => []
  | c, (A, m) :: bs => (A.liftLooseBVars k c, m) :: liftTele k (c + 1) bs

/-- One constructor of a `case` shape, in rule order. -/
structure CtorShape where
  key : KKey
  nF : Nat
  /-- the minor premise's field binders, as in the recursor's type (under `ps motive minors<j`) -/
  fields : List (KExpr × BinderMeta)
  /-- its induction hypothesis binders, one per recursive field -/
  ihs : List (KExpr × BinderMeta)
  /-- the positions (among the fields) of the recursive fields -/
  recFields : List Nat
  /-- the minor premise's codomain, under the fields only -/
  codom : KExpr
  /-- the recursor's binder datum for this minor premise -/
  minorMeta : BinderMeta

/-- The checked shape of a `case` constant. -/
structure CaseShape where
  lps : List Nat
  /-- the inductive, and the levels at which `casesOn`'s major premise uses it -/
  ind : KKey
  indLevels : List Level
  nP : Nat
  /-- `casesOn`'s binders: parameters, motive, major, minors -/
  binders : List (KExpr × BinderMeta)
  ctors : List CtorShape
  /-- the recursor's binder datum for the major premise -/
  majorMeta : BinderMeta

def CaseShape.nM (sh : CaseShape) : Nat := sh.ctors.length

/-- The wrapper `casesOn` hands the recursor for minor `j`, in `casesOn`'s body. -/
def CaseShape.wrapper (sh : CaseShape) (j : Nat) (cs : CtorShape) : KExpr :=
  let bs := liftTele (sh.nM + 1 - j) j (cs.fields ++ cs.ihs)
  lamTele bs (Expr.mkAppN (.bvar (sh.nM - 1 - j + bs.length)) (bvarsFrom (bs.length - cs.nF) cs.nF))

/-- `casesOn`'s body. -/
def CaseShape.body (sh : CaseShape) (kr : KKey) : KExpr :=
  Expr.mkAppN (.const kr (sh.lps.map Level.param))
    (bvarsFrom (sh.nM + 2) sh.nP ++ [.bvar (sh.nM + 1)] ++
      ((List.range sh.nM).filterMap fun j => (sh.ctors[j]?).map (sh.wrapper j)) ++ [.bvar sh.nM])

/-- `casesOn`'s minor premise `j`, in `casesOn`'s type (under `ps motive t minors<j`). -/
def CaseShape.casesMinor (j : Nat) (cs : CtorShape) : KExpr :=
  (piTele cs.fields cs.codom).liftLooseBVars 1 j

/-- The recursor's minor premise `j`, in its type (under `ps motive minors<j`). -/
def CtorShape.recMinor (cs : CtorShape) : KExpr :=
  piTele (cs.fields ++ cs.ihs) (cs.codom.liftLooseBVars cs.ihs.length 0)

/-- The recursor's stored type. -/
def CaseShape.recType (sh : CaseShape) : KExpr :=
  piTele (sh.binders.take (sh.nP + 1) ++ sh.ctors.map (fun cs => (cs.recMinor, cs.minorMeta)) ++
      ((sh.binders[sh.nP + 1]?).toList.map fun (A, _) => (A.liftLooseBVars sh.nM 0, sh.majorMeta)))
    (.app (.bvar (sh.nM + 1)) (.bvar 0))

/-- The recursor's rule `j` right-hand side: `λ ps motive minors fields. minorⱼ fields ihs`. -/
def CaseShape.ruleRhs (sh : CaseShape) (kr : KKey) (j : Nat) (cs : CtorShape) : KExpr :=
  let pre := sh.binders.take (sh.nP + 1) ++ sh.ctors.map (fun c => (c.recMinor, c.minorMeta))
  let fbs := liftTele (sh.nM - j) j cs.fields
  let n := cs.nF
  let ih (r : Nat) : KExpr :=
    Expr.mkAppN (.const kr (sh.lps.map Level.param))
      (bvarsFrom (n + sh.nM + 1) sh.nP ++ [.bvar (n + sh.nM)] ++ bvarsFrom n sh.nM ++
        [.bvar (n - 1 - r)])
  lamTele (pre ++ fbs)
    (Expr.mkAppN (.bvar (n + sh.nM - 1 - j)) (bvarsFrom 0 n ++ cs.recFields.map ih))

/-- **The checked shape of a `case` constant `kc` over its recursor `kr`**, against the kernel's
reading. Decided by the check. -/
structure CaseStored (env : KEnv) (kc kr : KKey) (sh : CaseShape) : Prop where
  arity : sh.binders.length = sh.nP + 2 + sh.nM ∧ 0 < sh.nM
  casesOnStored : ∃ (cvc : ConstantVal .anon) (hint : ReducibilityHint),
    env.find? kc = some (.defnInfo cvc (lamTele sh.binders (sh.body kr)) hint) ∧
    cvc.levelParams = sh.lps ∧
    cvc.type = piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM))
  minors : ∀ j cs, sh.ctors[j]? = some cs →
    (sh.binders[sh.nP + 2 + j]?).map (·.1) = some (CaseShape.casesMinor j cs) ∧
    cs.ihs.length = cs.recFields.length ∧ cs.fields.length = cs.nF
  major : ∃ m, sh.binders[sh.nP + 1]? = some
    (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP), m)
  recursor : ∃ (cvr : ConstantVal .anon) (rules : List (RecRule .anon)),
    env.find? kr = some (.recInfo cvr (sh.nP + 1 + sh.nM) (sh.nP + 1 + sh.nM) rules) ∧
    cvr.levelParams = sh.lps ∧ cvr.type = sh.recType ∧ rules.length = sh.nM ∧
    ∀ j cs rl, sh.ctors[j]? = some cs → rules[j]? = some rl →
      rl.ctor = cs.key ∧ rl.rhs = sh.ruleRhs kr j cs
  /-- constructor `j`'s type, at the `case`'s levels: `∀ ps fields, ind ps`, its parameter
  domains `casesOn`'s and its field domains the minor premise's (moved past the motive and the
  earlier minors); binder data may differ -/
  ctors : ∀ j cs, sh.ctors[j]? = some cs → ∃ (cvC : ConstantVal .anon)
    (pbs fbs : List (KExpr × BinderMeta)),
    env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF) ∧
    cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels =
      piTele pbs (piTele fbs (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom cs.nF sh.nP))) ∧
    pbs.map (·.1) = (sh.binders.take sh.nP).map (·.1) ∧
    (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1)

/-- **The program side of a `case` entry**: the recursor `r`'s Src declaration has the shape's
counts, every constructor of its inductive in `S` is the shape's constructor at its index, and
at the pinned `Nat` a literal major reads as `Nat.zero` and `Nat.succ`. -/
structure CaseProg (p : Program) (κ : CId → KKey) (S : CId → Prop) (r : CId) (sh : CaseShape) :
    Prop where
  recr : ∃ (sf kk : Bool) (lvls : Nat) (ind : CId) (rules : List IxCC.Src.Rule) (ty : Term),
    p.decl? r = some (.recr sf kk lvls sh.nP 1 sh.nM 0 ind rules ty) ∧
    (∀ c, S c → ∀ (sf' : Bool) (lv' cidx np nf : Nat) (ty' : Term),
      p.decl? c = some (.ctor sf' lv' ind cidx np nf ty') →
      np = sh.nP ∧ ∃ cs, sh.ctors[cidx]? = some cs ∧ cs.key = κ c ∧ cs.nF = nf) ∧
    (some ind = p.known.nat →
      sh.nP = 0 ∧ sh.ctors.map (fun cs => (cs.key, cs.nF)) = [(natZeroName, 0), (natSuccName, 1)])

/-- **The faithfulness clauses** (the spike's `Faith`, with `lvls` added). -/
structure Faith (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) : Prop where
  stored : ∀ c, S c → ∃ ci, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = lpsOf c
  lvls : ∀ c, S c → lvlsOf p c = (lpsOf c).length
  nodup : ∀ c, S c → (lpsOf c).Nodup
  noCsimp : ∀ c g us thm, S c → p.table.resolveOf c ≠ some (.csimp g us thm)
  noRecr : ∀ c, S c → ∀ sf kk lvls np nmot nmin ni ind rules ty,
    p.decl? c ≠ some (.recr sf kk lvls np nmot nmin ni ind rules ty)
  noQuot : ∀ c, S c → ∀ qk lvls ty, p.decl? c ≠ some (.quot qk lvls ty)
  noOpaque : ∀ c, S c → p.table.isOpaqueByValue c = false
  prim : ∀ c op, S c → p.table.resolveOf c = some (.prim op) → κ c = primKey op ∧
    ∃ ci, env.find? (primKey op) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      op.arity ≤ kPis ci.toConstantVal.type
  ctor : ∀ c, S c → ∀ sf lvls ind cidx np nf ty,
    p.decl? c = some (.ctor sf lvls ind cidx np nf ty) →
    ∃ cv, env.find? (κ c) = some (.ctorInfo cv np nf) ∧ np + nf ≤ kPis cv.type
  caseRec : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
    p.table.recKindOf r = some .ordinary ∧
    ∃ ci, env.find? (κ c) = some ci ∧ p.headArity (.cases c) ≤ kPis ci.toConstantVal.type
  defn : ∀ c, S c → p.table.resolveOf c = none → ∀ lvls ty v,
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    (∃ cv val hint, env.find? (κ c) = some (.defnInfo cv val hint)) ∧ ConstsIn S v
  eqnClosed : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) → ConstsIn S body
  proj : ∀ s, S s → ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) →
    ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → ∀ i, i < nf →
      ∃ entry, env.findProj? (κ s) i = some entry ∧ entry.ctor = κ c
  natZero : ∀ c, p.known.natZero = some c → κ c = natZeroName
  natSucc : ∀ c, p.known.natSucc = some c → κ c = natSuccName
  bool : ∀ (b : Bool) c, (if b then p.known.boolTrue else p.known.boolFalse) = some c →
    S c ∧ κ c = (if b then boolTrueName else boolFalseName) ∧
    ∃ cv, env.find? (κ c) = some (.ctorInfo cv 0 0) ∧ cv.levelParams = []

/-- `Nat` and its constructors are stored as the literal reading needs. -/
structure NatBasis (env : KEnv) : Prop where
  nat : ∃ ci : ConstantInfo .anon, env.find? natName = some ci ∧ ci.toConstantVal.levelParams = []
  zero : ∃ cv : ConstantVal .anon, env.find? natZeroName = some (.ctorInfo cv 0 0) ∧
    cv.name = natZeroName ∧ cv.type = .const natName [] ∧ cv.levelParams = []
  succ : ∃ cv : ConstantVal .anon, env.find? natSuccName = some (.ctorInfo cv 0 1) ∧
    cv.name = natSuccName ∧
    cv.type = .forallE (.const natName []) (.const natName []) { pw := PropWhen.never } ∧
    cv.levelParams = []

/-- **The checked shapes of the `case` entries** of `S` (consumed by the generic `case` lemma). -/
def CaseFacts (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop :=
  ∀ c r, S c → p.table.resolveOf c = some (.case r) →
    ∃ sh, CaseStored env (κ c) (κ r) sh ∧ CaseProg p κ S r sh

/-- **Every decidable fact the root theorem consumes** about the program, the kernel's reading
and the certificate's annotation, on a set `S` of constants. The check decides it. -/
structure GroundFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop where
  faith : Faith p env κ lpsOf S
  natBasis : NatBasis env
  eqns : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) →
    (∃ d, EqnShape env κ c thm d) ∧ ∀ d, EqnShape env κ c thm d → TermCorr κ (lpsOf c) body d.body
  values : ∀ c lvls ty v cv val hint, S c → p.table.resolveOf c = none →
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    env.find? (κ c) = some (.defnInfo cv val hint) → TermCorr κ (lpsOf c) v val
  /-- every run term is closed -/
  closed : ∀ c t e, S c → RunPair p env κ c t e → bvarsLt 0 e = true
  okClosed : OkClosed p ann S


end IxCC.Grounding
