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
* the node-for-node correspondence of a Src term and a kernel term (`TermCorr`), and of a run
  term and its stored ζ-reduct through a substitution (`TermCorrS`, the `let` cases);
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

/-- The sort a stored type ends in: `Sort s` after its leading `∀`s (an inductive family's
universe). -/
def finalSort : Expr md → Option Level
  | .forallE _ b _ => finalSort b
  | .sort s => some s
  | _ => none

/-- **`D` is stored as an inductive family that is never a proposition**: its type ends in a sort
whose zero-ness datum never holds, so the family is not a proposition at any assignment of its
level parameters. Decided on the bytes; what the restricted laws `ctor_canon` and `proj_ctor`
are asked at. -/
def NeverProp (env : Env md) (D : Key md) : Prop :=
  ∃ (cvD : ConstantVal md) (caps : IndCaps md) (s : Level),
    env.find? D = some (.indInfo cvD caps) ∧ finalSort cvD.type = some s ∧
      Level.zeronessOf s = PropWhen.never

/-- `NeverProp`, decided. -/
def neverPropB (env : Env md) (D : Key md) : Bool :=
  match env.find? D with
  | some (.indInfo cvD _) =>
    match finalSort cvD.type with
    | some s => decide (Level.zeronessOf s = PropWhen.never)
    | none => false
  | _ => false

theorem neverProp_of_check {env : Env md} {D : Key md} (h : neverPropB env D = true) :
    NeverProp env D := by
  unfold neverPropB at h
  split at h
  · rename_i cvD caps hf
    split at h
    · rename_i s hs
      exact ⟨cvD, caps, s, hf, hs, of_decide_eq_true h⟩
    · cases h
  · cases h

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

/-- A Src term corresponds to a kernel term node for node (no `let`, no string literal). The
recursor rules and `case` checks read it (their terms are kernel-generated); run terms are read
through `TermCorrS`, which admits `let`. Decided by a Boolean check on the bytes. -/
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

/-! ### The correspondence under a substitution (step C: `let` in run terms)

The kernel stores the ζ-reduct of a run term (its annotation pass substitutes every `let` away),
and neither our `Denotes` nor #678's reads a `let` (#678 at `d4c079de2`,
`IxC/Kernel/Denotes.lean:635`). So a Src `let x := v; b` corresponds to the stored term `e` of its
body with `x` replaced by the kernel copy `v'` of `v`: Src variables stand for kernel *terms*, through
a substitution `σ : Sig`. A `let` whose variable meets no kernel term (a dead `let`) gets `none`: its
slot is related to nothing, and nothing about its value is asked. -/

/-- A substitution from Src variables to kernel terms over the current kernel context: `some e`, or
`none` for a dead `let`'s variable. -/
abbrev Sig := List (Option KExpr)

/-- Under a binder: the new variable is `#0`, every other term lifted past it. -/
def liftσ (σ : Sig) : Sig := some (.bvar 0) :: σ.map (·.map (Expr.liftLooseBVars 1 0))

/-- The identity substitution of `n` bound variables: `[some #0, …, some #(n-1)]`. -/
def idσ (n : Nat) : Sig := (List.range n).map fun i => some (.bvar i)

theorem idσ_zero : idσ 0 = [] := rfl

theorem liftσ_idσ (n : Nat) : liftσ (idσ n) = idσ (n + 1) := by
  simp only [liftσ, idσ, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp [Expr.liftLooseBVars]

theorem idσ_get {n i : Nat} (h : i < n) : (idσ n)[i]? = some (some (.bvar i)) := by
  simp [idσ, h]

/-- `e` with its loose variables at or above `c + d` lowered by `d`; `none` when one in `[c, c + d)`
occurs. -/
def lowerK (d : Nat) : Nat → KExpr → Option KExpr
  | c, .bvar i => if i < c then some (.bvar i) else if i < c + d then none else some (.bvar (i - d))
  | c, .app f a => do pure (.app (← lowerK d c f) (← lowerK d c a))
  | c, .lam t b m => do pure (.lam (← lowerK d c t) (← lowerK d (c + 1) b) m)
  | c, .forallE t b m => do pure (.forallE (← lowerK d c t) (← lowerK d (c + 1) b) m)
  | c, .letE t v b m => do pure (.letE (← lowerK d c t) (← lowerK d c v) (← lowerK d (c + 1) b) m)
  | c, .proj s i e => do pure (.proj s i (← lowerK d c e))
  | _, e => some e

/-- **The copy** (a producer: `TermCorrS` checks every occurrence against what it returns): the
kernel term Src variable `k` first meets when `t` is walked against `e`, `d` kernel binders below
the variable's scope, lowered to that scope (inner `let`s: their value against their own copy).
Structural on `t`. -/
def zcopyAt (k d : Nat) : Term → KExpr → Option KExpr
  | .var i, e => if i == k then lowerK d 0 e else none
  | .app f a _ _, .app f' a' => (zcopyAt k d f f').orElse fun _ => zcopyAt k d a a'
  | .lam _ dm b, .lam dm' b' _ => (zcopyAt k d dm dm').orElse fun _ => zcopyAt (k + 1) (d + 1) b b'
  | .pi _ _ dm c, .forallE dm' c' _ =>
    (zcopyAt k d dm dm').orElse fun _ => zcopyAt (k + 1) (d + 1) c c'
  | .proj _ _ x, .proj _ _ x' => zcopyAt k d x x'
  | .letE _ _ _ v b, e =>
    ((zcopyAt 0 0 b e).bind fun v2 => zcopyAt k d v v2).orElse fun _ => zcopyAt (k + 1) d b e
  | _, _ => none

/-- The copy of a `let`'s variable in its body's kernel term. -/
def zcopy (b : Term) (e : KExpr) : Option KExpr := zcopyAt 0 0 b e

/-- `v` occurs in `e` with no binder between (through applications and projections). -/
inductive SubAt0 (v : KExpr) : KExpr → Prop
  | refl : SubAt0 v v
  | appL {f a : KExpr} : SubAt0 v f → SubAt0 v (.app f a)
  | appR {f a : KExpr} : SubAt0 v a → SubAt0 v (.app f a)
  | proj {s : KKey} {i : Nat} {x : KExpr} : SubAt0 v x → SubAt0 v (.proj s i x)

/-- `SubAt0`, decided. -/
def subAt0B (v : KExpr) : KExpr → Bool
  | .app f a => decide (v = .app f a) || subAt0B v f || subAt0B v a
  | .proj s i x => decide (v = .proj s i x) || subAt0B v x
  | e => decide (v = e)

/-- **The closure-capture shape** (step C): a `let`'s body `b` is a λ, its kernel term `e` a λ, and
the copy `v'` (in the `let`'s context), lifted past the λ, occurs in the λ's body with no binder
between. -/
def cloShapeB (b : Term) (e v' : KExpr) : Bool :=
  match b, e with
  | .lam _ _ _, .lam _ b' _ => subAt0B (v'.liftLooseBVars 1 0) b'
  | _, _ => false

/-- **Where a closure-capture `let`'s value runs** (step C): the λ's domain and the copy lifted past
it, when the copy is not at depth 0 and the shape is the closure-capture one. -/
def cloSite? (b : Term) (e : KExpr) : Option (KExpr × KExpr) :=
  match zcopy b e, e with
  | some v', .lam A _ _ =>
    if !subAt0B v' e && cloShapeB b e v' then some (A, v'.liftLooseBVars 1 0) else none
  | _, _ => none

theorem subAt0_of_check {v : KExpr} : ∀ {e : KExpr}, subAt0B v e = true → SubAt0 v e := by
  intro e h
  induction e with
  | app f a ihf iha =>
    simp only [subAt0B, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (rfl | h) | h
    · exact .refl
    · exact .appL (ihf h)
    · exact .appR (iha h)
  | proj s i x ih =>
    simp only [subAt0B, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .proj (ih h)
  | _ =>
    simp only [subAt0B, decide_eq_true_eq] at h
    subst h; exact .refl

theorem cloShapeB_lam {b : Term} {A b' v' : KExpr} {m : BinderMeta}
    (h : cloShapeB b (.lam A b' m) v' = true) : subAt0B (v'.liftLooseBVars 1 0) b' = true := by
  cases b <;> simp_all [cloShapeB]

/-- **What `cloSite?` returns**: the kernel term is a λ over the returned domain, and the returned
copy occurs in its body with no binder between. -/
theorem cloSite?_spec {b : Term} {e A cp : KExpr} (h : cloSite? b e = some (A, cp)) :
    ∃ b' m, e = .lam A b' m ∧ SubAt0 cp b' := by
  unfold cloSite? at h
  cases hz : zcopy b e with
  | none => simp [hz] at h
  | some v' =>
    rw [hz] at h
    cases e with
    | lam A' b' m =>
      simp only at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true] at hc
        exact ⟨b', m, rfl, subAt0_of_check (cloShapeB_lam hc.2)⟩
      · cases h
    | _ => simp at h


/-- **The correspondence under a substitution** (what `valueCorr` and `eqnCorr` check, at `σ = []`):
as `TermCorr`, with `var i` meeting `σ[i]`'s term, binders lifting `σ`, and two `let` cases: a live
`let` (its variable's copy `v'` occurs in the body's kernel term with no binder between, and the value
corresponds to it) and a dead one (its variable meets no kernel term); since step C a third, the
closure-capture shape (`letClo`). The `let`'s type is not compared: SrcEval never evaluates it, and
the kernel stores no `let`. -/
inductive TermCorrS (κ : CId → KKey) (lps : List Nat) : Sig → Term → KExpr → Prop
  | var {σ : Sig} {i : Nat} {e : KExpr} : σ[i]? = some (some e) → TermCorrS κ lps σ (.var i) e
  | sort {σ : Sig} {u : IxCC.Ixon.Univ} {l : Level} : UnivCorr lps u l →
      TermCorrS κ lps σ (.sort u) (.sort l)
  | const {σ : Sig} {c : CId} {us : List IxCC.Ixon.Univ} {ls : List Level} :
      us.length = ls.length →
      (∀ (i : Nat) (u : IxCC.Ixon.Univ) (l : Level), us[i]? = some u → ls[i]? = some l →
        UnivCorr lps u l) →
      TermCorrS κ lps σ (.const c us) (.const (κ c) ls)
  | app {σ : Sig} {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel} {f' a' : KExpr} :
      TermCorrS κ lps σ f f' → TermCorrS κ lps σ a a' → TermCorrS κ lps σ (.app f a m r) (.app f' a')
  | lam {σ : Sig} {b : IxCC.Src.Binder} {d body : Term} {d' body' : KExpr} {mb : BinderMeta} :
      TermCorrS κ lps σ d d' → TermCorrS κ lps (liftσ σ) body body' →
      TermCorrS κ lps σ (.lam b d body) (.lam d' body' mb)
  | pi {σ : Sig} {b : IxCC.Src.Binder} {r : IxCC.Ixon.V3.ValueContract} {d c : Term}
      {d' c' : KExpr} {mb : BinderMeta} :
      TermCorrS κ lps σ d d' → TermCorrS κ lps (liftσ σ) c c' →
      TermCorrS κ lps σ (.pi b r d c) (.forallE d' c' mb)
  | proj {σ : Sig} {s : CId} {i : Nat} {e : Term} {e' : KExpr} :
      TermCorrS κ lps σ e e' → TermCorrS κ lps σ (.proj s i e) (.proj (κ s) i e')
  | natLit {σ : Sig} {n : Nat} : TermCorrS κ lps σ (.natLit n) (.lit (.natVal n))
  | letLive {σ : Sig} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel} {ty v b : Term}
      {e v' : KExpr} :
      zcopy b e = some v' → subAt0B v' e = true → TermCorrS κ lps σ v v' →
      TermCorrS κ lps (some v' :: σ) b e → TermCorrS κ lps σ (.letE c r ty v b) e
  | letDead {σ : Sig} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel} {ty v b : Term}
      {e : KExpr} :
      zcopy b e = none → TermCorrS κ lps (none :: σ) b e → TermCorrS κ lps σ (.letE c r ty v b) e
  /-- the closure-capture shape (step C): the `let`'s body and its kernel term are λs, the copy is
  not at depth 0 but, lifted past the λ, occurs in the λ's body with no binder between; the value
  corresponds in the λ's context to the lifted copy -/
  | letClo {σ : Sig} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel} {ty v : Term}
      {bz : IxCC.Src.Binder} {d body : Term} {A b' v' : KExpr} {mb : BinderMeta} :
      zcopy (.lam bz d body) (.lam A b' mb) = some v' → subAt0B v' (.lam A b' mb) = false →
      subAt0B (v'.liftLooseBVars 1 0) b' = true →
      TermCorrS κ lps (σ.map (·.map (Expr.liftLooseBVars 1 0))) v (v'.liftLooseBVars 1 0) →
      TermCorrS κ lps (some v' :: σ) (.lam bz d body) (.lam A b' mb) →
      TermCorrS κ lps σ (.letE c r ty v (.lam bz d body)) (.lam A b' mb)

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

/-- Does the bound variable `i` occur loose in `e` (counted from `e`'s own scope)? -/
def looseIn : Nat → KExpr → Bool
  | i, .bvar k => k == i
  | i, .app f a => looseIn i f || looseIn i a
  | i, .lam d b _ => looseIn i d || looseIn (i + 1) b
  | i, .forallE d b _ => looseIn i d || looseIn (i + 1) b
  | i, .letE t v b _ => looseIn i t || looseIn i v || looseIn (i + 1) b
  | i, .proj _ _ e => looseIn i e
  | _, _ => false

/-- No bound variable in `[c, c + j)` occurs loose in `e`. -/
def avoids (c j : Nat) (e : KExpr) : Bool := (List.range j).all fun t => !looseIn (c + t) e

/-- The number of leading `∀`s of a kernel term, syntactically. -/
def kPis : KExpr → Nat
  | .forallE _ b _ => kPis b + 1
  | _ => 0

/-- What remains of a kernel term after `n` leading `∀`s. -/
def piBody : Nat → KExpr → KExpr
  | n + 1, .forallE _ b _ => piBody n b
  | _, e => e

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
irrelevant at `ls`, not inside a type; under λ bodies and projections; a `let`'s value where the
`let` is relevant at `ls` (dead or not: SrcEval evaluates it), and its body. -/
def evalConsts (ls : Levels) : Term → List (CId × List IxCC.Ixon.Univ)
  | .const c us => [(c, us)]
  | .app f a _ r => evalConsts ls f ++ (if r.irrAt ls then [] else evalConsts ls a)
  | .lam _ _ body => evalConsts ls body
  | .proj _ _ e => evalConsts ls e
  | .letE _ r _ v b => (if r.irrAt ls then [] else evalConsts ls v) ++ evalConsts ls b
  | _ => []

/-- The same at a profile (which parameters are zero). -/
def evalConstsP (prof : IxCC.Src.Profile) : Term → List (CId × List IxCC.Ixon.Univ)
  | .const c us => [(c, us)]
  | .app f a _ r => evalConstsP prof f ++ (if r.irrP prof then [] else evalConstsP prof a)
  | .lam _ _ body => evalConstsP prof body
  | .proj _ _ e => evalConstsP prof e
  | .letE _ r _ v b => (if r.irrP prof then [] else evalConstsP prof v) ++ evalConstsP prof b
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

/-- A `∀`-telescope's binders, all of them, and what remains. -/
def splitAll : KExpr → List (KExpr × BinderMeta) × KExpr
  | .forallE d b m => ((d, m) :: (splitAll b).1, (splitAll b).2)
  | e => ([], e)

/-- Exactly `n` leading binders of a `∀`-telescope, and what remains. -/
def splitPi : Nat → KExpr → Option (List (KExpr × BinderMeta) × KExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE d b m => (splitPi n b).map fun r => ((d, m) :: r.1, r.2)
  | _ + 1, _ => none

/-- An `eqn` entry's data, read off the stored theorem and function (the check then verifies
the shape against it, so this reading needs no proof). -/
def eqnData? (env : KEnv) (kc kt : KKey) : Option EqnData :=
  match env.find? kt, env.find? kc with
  | some (.thmInfo cvT _), some ciF =>
    match splitAll cvT.type with
    | (Ds, .app (.app (.app (.const _ [u]) T) _) rhs) =>
      (splitPi Ds.length ciF.toConstantVal.type).map fun r =>
        { Ds, ms := r.1.map (·.2), u, T, rhs, R := r.2 }
    | _ => none
  | _, _ => none

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
application reached through functions, arguments relevant at `ls`, λ bodies and projections; at a
`let`, its value's sites at the value's copy where the `let` is relevant and the copy occurs with no
binder between (none where it is dead); at a closure-capture `let` (step C, `cloSite?`) where it
is relevant, its value's sites in the λ's context at the lifted copy; and its body's. Every site
is an application node of the kernel term with its binder domains (a `let` adds no kernel
binder). -/
def evalSites (ls : Levels) : List KExpr → Term → KExpr → List (List KExpr × KExpr × KExpr)
  | Γ, .app f a _ r, .app f' a' =>
    (Γ, f', a') :: (evalSites ls Γ f f' ++ (if r.irrAt ls then [] else evalSites ls Γ a a'))
  | Γ, .lam _ _ body, .lam d' body' _ => evalSites ls (d' :: Γ) body body'
  | Γ, .proj _ _ e, .proj _ _ e' => evalSites ls Γ e e'
  | Γ, .letE _ r _ v b, e =>
    (match zcopy b e with
      | some v' => if r.irrAt ls || !subAt0B v' e then [] else evalSites ls Γ v v'
      | none => []) ++
    ((match cloSite? b e with
      | some (A, cp) => if r.irrAt ls then [] else evalSites ls (A :: Γ) v cp
      | none => []) ++ evalSites ls Γ b e)
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
  /-- the levels, in `casesOn`'s level parameters, at which `casesOn`'s body calls the recursor
  (the recursor may name its own level parameters apart from `casesOn`'s; its stored type and
  rules are compared at these levels) -/
  recLevels : List Level

def CaseShape.nM (sh : CaseShape) : Nat := sh.ctors.length

/-- The wrapper `casesOn` hands the recursor for minor `j`, in `casesOn`'s body. -/
def CaseShape.wrapper (sh : CaseShape) (j : Nat) (cs : CtorShape) : KExpr :=
  let bs := liftTele (sh.nM + 1 - j) j (cs.fields ++ cs.ihs)
  lamTele bs (Expr.mkAppN (.bvar (sh.nM - 1 - j + bs.length)) (bvarsFrom (bs.length - cs.nF) cs.nF))

/-- `casesOn`'s body. -/
def CaseShape.body (sh : CaseShape) (kr : KKey) : KExpr :=
  Expr.mkAppN (.const kr sh.recLevels)
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
    Expr.mkAppN (.const kr sh.recLevels)
      (bvarsFrom (n + sh.nM + 1) sh.nP ++ [.bvar (n + sh.nM)] ++ bvarsFrom n sh.nM ++
        [.bvar (n - 1 - r)])
  lamTele (pre ++ fbs)
    (Expr.mkAppN (.bvar (n + sh.nM - 1 - j)) (bvarsFrom 0 n ++ cs.recFields.map ih))

/-- A recursive field's domain in minor premise `j` (under the parameters, the motive, the minors
before `j` and the fields before `r`): the inductive at the `case`'s parameters. -/
def CaseShape.recFieldDom (sh : CaseShape) (j r : Nat) : KExpr :=
  Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom (r + j + 1) sh.nP)

/-- Induction hypothesis `r`'s domain in minor premise `j` (under the parameters, the motive, the
minors before `j`, the fields and the hypotheses before `r`): the motive at the recursive field
`rf`. -/
def CtorShape.ihDom (cs : CtorShape) (j r rf : Nat) : KExpr :=
  .app (.bvar (r + cs.nF + j)) (.bvar (r + cs.nF - 1 - rf))

/-- **What the generic `case` lemma needs beyond the builders** (all true of the recursors the
kernel generates for inductives without indices, nested or reflexive occurrences; decided by
the check):

* `recFields`, `ihs`: each induction hypothesis is the motive at a recursive field, and each
  recursive field's domain is the inductive at the `case`'s parameters (without them the
  wrapper's β at an induction hypothesis has no justification: the hypotheses' binders are free
  data of the shape);
* `codom`: a minor premise's codomain does not mention the minors before it (the wrapper reads
  `casesOn`'s minors there, the recursor's minor premise the wrappers);
* `regime`: every field binder of every minor premise carries the zero-ness datum of
  `casesOn`'s last binder (so the minor applies to its fields in the graph regime whenever the
  saturating site was in it);
* `ctorRaw`: each constructor's stored type is closed, its level parameters cover it, it has as
  many level parameters as `indLevels`, and its codomain is headed by the inductive at the
  constructor's own parameters (what moves a constructor value from the assignment and
  environment it was built at to the `case`'s, through canonicity);
* `indSort`: the inductive is stored as a family that is never a proposition (`NeverProp`), the
  class at which canonicity (`Laws.ctor_canon`) is assumed. A `case` over a family in `Prop`
  (`And.casesOn` into `Type`) is outside the fragment: there SrcEval's major is an erased proof,
  on which F5 selects no rule, and a constructor value of it would need canonicity where it is
  false (a proposition's constructor image is the proof point). -/
structure CaseWF (env : KEnv) (sh : CaseShape) : Prop where
  recFields : ∀ (j : Nat) (cs : CtorShape), sh.ctors[j]? = some cs → ∀ rf ∈ cs.recFields,
    rf < cs.nF ∧ (cs.fields[rf]?).map (·.1) = some (sh.recFieldDom j rf)
  ihs : ∀ (j : Nat) (cs : CtorShape), sh.ctors[j]? = some cs → ∀ r rf, cs.recFields[r]? = some rf →
    (cs.ihs[r]?).map (·.1) = some (cs.ihDom j r rf)
  codom : ∀ (j : Nat) (cs : CtorShape), sh.ctors[j]? = some cs → avoids cs.nF j cs.codom = true
  regime : ∃ (A : KExpr) (m : BinderMeta), sh.binders.getLast? = some (A, m) ∧
    ∀ (j : Nat) (cs : CtorShape), sh.ctors[j]? = some cs → ∀ b ∈ cs.fields, b.2.pw = m.pw
  ctorRaw : ∀ (j : Nat) (cs : CtorShape), sh.ctors[j]? = some cs → ∃ cvC : ConstantVal .anon,
    env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF) ∧
    cvC.levelParams.length = sh.indLevels.length ∧ bvarsLt 0 cvC.type = true ∧
    cvC.type.allLevelParamsDefined cvC.levelParams = true ∧
    (piBody (sh.nP + cs.nF) cvC.type).getAppFn = .const sh.ind (cvC.levelParams.map .param)
  indSort : NeverProp env sh.ind

/-- **The recursor of a `case` shape, compared at the levels `casesOn`'s body calls it at**
(`sh.recLevels`): its stored type and its rules' right-hand sides, instantiated there, are the
shape's. The recursor may name its level parameters apart from `casesOn`'s (the kernel's reading
of a universe-polymorphic inductive does: `ForInStep`'s recursor's are `casesOn`'s in the other
order); ι (`Laws.iota_rule`) is stated at any instantiation, so nothing else changes. -/
def CaseRec (env : KEnv) (kr : KKey) (sh : CaseShape) : Prop :=
  ∃ (cvr : ConstantVal .anon) (rules : List (RecRule .anon)),
    env.find? kr = some (.recInfo cvr (sh.nP + 1 + sh.nM) (sh.nP + 1 + sh.nM) rules) ∧
    cvr.levelParams.length = sh.recLevels.length ∧
    cvr.type.instantiateLevelParams cvr.levelParams sh.recLevels = sh.recType ∧
    rules.length = sh.nM ∧
    ∀ j cs rl, sh.ctors[j]? = some cs → rules[j]? = some rl →
      rl.ctor = cs.key ∧ rl.rhs.instantiateLevelParams cvr.levelParams sh.recLevels = sh.ruleRhs kr j cs

/-- **The recursor clause as first landed** (G1b): `casesOn`'s body calls the recursor at
`casesOn`'s own level parameters, which the recursor shares, and its stored type and rules are
the shape's as they stand. `CaseRec` holds whenever this does (`caseRec_of_named`), so the
renaming-tolerant `CaseStored` holds wherever the landed one did. -/
def CaseRecNamed (env : KEnv) (kr : KKey) (sh : CaseShape) : Prop :=
  sh.recLevels = sh.lps.map Level.param ∧
  ∃ (cvr : ConstantVal .anon) (rules : List (RecRule .anon)),
    env.find? kr = some (.recInfo cvr (sh.nP + 1 + sh.nM) (sh.nP + 1 + sh.nM) rules) ∧
    cvr.levelParams = sh.lps ∧ cvr.type = sh.recType ∧ rules.length = sh.nM ∧
    ∀ j cs rl, sh.ctors[j]? = some cs → rules[j]? = some rl →
      rl.ctor = cs.key ∧ rl.rhs = sh.ruleRhs kr j cs

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
  /-- the recursor, compared at the levels `casesOn`'s body calls it at (renaming-tolerant;
  as first landed, `CaseRecNamed`) -/
  recursor : CaseRec env kr sh
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
  /-- what the generic `case` lemma needs beyond the builders -/
  wf : CaseWF env sh

/-- **`CaseStored` as first landed** (G1b, before the renaming-tolerant recursor clause): the same
clauses, the recursor's `CaseRecNamed`. It implies `CaseStored` (`caseStored_of_named`), so every
theorem taking `CaseStored` (or `CaseFacts`) is at least as strong as its landed form. -/
structure CaseStoredNamed (env : KEnv) (kc kr : KKey) (sh : CaseShape) : Prop where
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
  recursor : CaseRecNamed env kr sh
  ctors : ∀ j cs, sh.ctors[j]? = some cs → ∃ (cvC : ConstantVal .anon)
    (pbs fbs : List (KExpr × BinderMeta)),
    env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF) ∧
    cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels =
      piTele pbs (piTele fbs (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom cs.nF sh.nP))) ∧
    pbs.map (·.1) = (sh.binders.take sh.nP).map (·.1) ∧
    (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1)
  wf : CaseWF env sh

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

/-! ## Recursors in the checked set (G3)

SrcEval fires a recursor head by its kind at the levels it runs it at (`RecKind.atLevels`): F2
(`ordinary`: force the major premise, select the rule by its constructor), F3 (`subsingleton`:
do not force the major; the rule's fields from index slots or `irr`), F4 (`empty`: trap). The
recursors the fundamental lemma handles are classified on the bytes (`recClassB`), and the check
admits the classes in `admittedClasses`, a constant that grows as each class is proved. -/

/-- The recursor classes. -/
inductive RecClass where
  /-- no rules, kind `empty` at every level (`False.rec`, run by `False.elim`): F4, a trap -/
  | empty
  /-- the built-in `Eq.rec` (two parameters, one motive, one minor premise, one index, one rule,
  kind `subsingleton` at every level with no fields): F3, the minor premise returned -/
  | eqRec
  /-- the flat part of `ordinary` (G3, part D): kind `ordinary`, no parameter, no index, the
  inductive stored as never a proposition, every rule without fields and its body (peeled of the
  motives' and minor premises' λs) a variable (`Bool.rec`, an enumeration's recursor): F2, which
  evaluates a variable there, so a rule body runs no term -/
  | flat
  /-- the rest of `ordinary` without parameters (G3, part E): kind `ordinary`, no parameter, no index,
  the inductive stored as never a proposition, not `flat` (a rule with fields, or a rule body that is
  not a variable): F2, whose rule body SrcEval evaluates (`T16.rec`, whose last rule applies its
  minor premise to its field; `Nat.rec`, whose `succ` rule calls the recursor, which the check then
  refuses at `recShape`, `RecBodies`) -/
  | noParams
  /-- kind `ordinary`, no indices, the inductive stored as never a proposition, with parameters: F2
  (not admitted) -/
  | ordinary
  deriving DecidableEq, Repr

/-- A Src term peeled of `n` λs is a variable below `n` (the body of a flat recursor's rule). -/
def bodyVarB (n : Nat) (t : Term) : Bool :=
  match IxCC.Src.peelLams n t with
  | some (.var i) => decide (i < n)
  | _ => false

/-- **The class of a recursor `r`, decided** on the program, its table and the kernel's reading.
Anything else is not admitted. At `Eq.rec` the kind's condition must be "always" (`allZero []`),
so SrcEval takes F3 there at every level. An `ordinary` recursor without parameters whose rules
have no fields and whose rule bodies are variables is `flat` (part D); any other without parameters
is `noParams` (part E). -/
def recClassB (p : Program) (env : KEnv) (κ : CId → KKey) (r : CId) : Option RecClass :=
  match p.decl? r, p.table.recKindOf r with
  | some (.recr _ _ _ _ _ _ _ _ [] _), some .empty => some .empty
  | some (.recr _ _ _ 2 1 1 1 _ [_] _), some (.subsingleton w []) =>
    if κ r == eqRecName && w == IxCC.Src.PropWhen.allZero [] then some .eqRec else none
  | some (.recr _ _ _ np nmot nmin 0 ind rules _), some .ordinary =>
    if neverPropB env (κ ind) then
      if np == 0 && rules.all (fun rl => rl.fields == 0 && bodyVarB (nmot + nmin) rl.rhs) then
        some .flat
      else if np == 0 then some .noParams
      else some .ordinary
    else none
  | _, _ => none

/-- **The recursor classes the check admits**: those the fundamental lemma handles. G3 adds them
one at a time, each when its case of the fundamental lemma is proved; extending the list only
makes the check accept more (`groundCheckWith_mono`). -/
def admittedClasses : List RecClass := [.empty, .eqRec, .flat, .noParams]

/-- **The checked shape of a recursor entry**: the kernel stores `κ r` as a recursor whose major
index and rule prefix are the Src declaration's counts, at the level parameters `lpsOf r`, whose
stored type has a binder for every argument SrcEval takes (`np + nmot + nmin + ni + 1`, the head's
arity), with the Src rules: the same constructors (by key) and field counts, and right-hand sides
that correspond node for node (`TermCorr`). -/
structure RecStored (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (r : CId) :
    Prop where
  stored : ∃ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
      (ty : Term) (cvr : ConstantVal .anon) (krules : List (RecRule .anon)),
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) ∧
    env.find? (κ r) = some (.recInfo cvr (np + nmot + nmin + ni) (np + nmot + nmin) krules) ∧
    cvr.levelParams = lpsOf r ∧ np + nmot + nmin + ni + 1 ≤ kPis cvr.type ∧
    rules.length = krules.length ∧
    ∀ (j : Nat) (rl : IxCC.Src.Rule) (krl : RecRule .anon), rules[j]? = some rl →
      krules[j]? = some krl → κ rl.ctor = krl.ctor ∧ rl.fields = krl.nfields ∧
        TermCorr κ (lpsOf r) rl.rhs krl.rhs

/-- `Eq.refl : ∀ {α : Sort u} (a : α), @Eq α a a`, as the kernel stores it (both binder data
"always a proposition": `Eq.refl α a` is a proof). -/
def eqReflType : KExpr :=
  .forallE (.sort (.param 0))
    (.forallE (.bvar 0)
      (Expr.mkAppN (.const eqName [.param 0]) [.bvar 1, .bvar 0, .bvar 0])
      { pw := PropWhen.ifAllZero [] })
    { pw := PropWhen.ifAllZero [] }

/-- The built-in `Eq.refl` is stored as a constructor with two parameters, no field, one level
parameter and that type (what F3 at `Eq.rec` reads). -/
def EqReflBasis (env : KEnv) : Prop :=
  ∃ cv : ConstantVal .anon, env.find? eqReflName = some (.ctorInfo cv 2 0) ∧
    cv.levelParams = [0] ∧ cv.type = eqReflType

/-- `@Eq.{u} A a b`, `u` the level parameter `0`. -/
def eqAppK (A a b : KExpr) : KExpr := Expr.mkAppN (.const eqName [.param 0]) [A, a, b]

/-- The binder datum of `Eq.rec`'s six binders and of its rule's four λs: a proposition exactly
where the motive's universe (the level parameter `1`) is zero. -/
def bmR : BinderMeta := { pw := PropWhen.ifAllZero [1] }

/-- `motive : ∀ (b : α), @Eq α a b → Sort u₁`, under `α a`. -/
def eqRecMotiveDom : KExpr :=
  .forallE (.bvar 1) (.forallE (eqAppK (.bvar 2) (.bvar 1) (.bvar 0)) (.sort (.param 1)) bmN) bmN

/-- `refl : motive a (@Eq.refl α a)`, under `α a motive`. -/
def eqRecMinorDom : KExpr :=
  Expr.mkAppN (.bvar 0) [.bvar 1, Expr.mkAppN (.const eqReflName [.param 0]) [.bvar 2, .bvar 1]]

/-- `Eq.rec`'s first four binders, `α a motive refl`: its rule's prefix. -/
def eqRecPrefix : List (KExpr × BinderMeta) :=
  [(.sort (.param 0), bmR), (.bvar 0, bmR), (eqRecMotiveDom, bmR), (eqRecMinorDom, bmR)]

/-- `Eq.rec`'s last two binders, `b : α` and the major premise `t : @Eq α a b`. -/
def eqRecMajors : List (KExpr × BinderMeta) :=
  [(.bvar 3, bmR), (eqAppK (.bvar 4) (.bvar 3) (.bvar 0), bmR)]

/-- `Eq.rec`'s codomain, `motive b t`. -/
def eqRecBody : KExpr := Expr.mkAppN (.bvar 3) [.bvar 1, .bvar 0]

/-- `Eq.rec : ∀ {α : Sort u₀} {a : α} {motive : ∀ b : α, @Eq α a b → Sort u₁}
(refl : motive a (Eq.refl a)) {b : α} (t : @Eq α a b), motive b t`, as the kernel stores it. -/
def eqRecType : KExpr := piTele (eqRecPrefix ++ eqRecMajors) eqRecBody

/-- The right-hand side of `Eq.rec`'s one rule, `λ α a motive refl. refl`, its λ-domains the
type's. -/
def eqRecRhs : KExpr := lamTele eqRecPrefix (.bvar 0)

/-- **The built-in `Eq.rec` is stored as F3 reads it** (G3, part C): a recursor with major index
`5` and rule prefix `4`, of type `eqRecType`, with one rule, at `Eq.refl`, with the right-hand side
`eqRecRhs`. What the proof reads of it: the counts and the type, for ι and for the arguments'
domains (the major's is `@Eq α a b`, whose members make `a` and `b` equal); the rule's constructor,
for ι; its right-hand side, for what ι returns (the minor premise, by β through `eqRecRhs`, whose
λ-domains are the type's). Not its level-parameter list (the proof reads `Eq.rec` at its own
parameters, where instantiating them is the identity whatever their order) nor the rule's field
count (ι takes the constructor's, from `EqReflBasis`). Compared with the stored terms structurally
(no address). -/
def EqRecBasis (env : KEnv) : Prop :=
  ∃ (cvr : ConstantVal .anon) (krl : RecRule .anon),
    env.find? eqRecName = some (.recInfo cvr 5 4 [krl]) ∧ cvr.type = eqRecType ∧
      krl.ctor = eqReflName ∧ krl.rhs = eqRecRhs

/-- **The rules' telescopes** (G3, part D): every stored rule of the recursor `kr` is a λ-telescope
over the `rP` binders of its prefix and its fields, whose first `rP` domains are the stored type's
first `rP` domains. What the proof reads: β through a rule's right-hand side, after ι, needs each
argument in its λ's domain, which `Fits` against the type's binders gives. Not the binder data
(β holds in regime `0` too, `app_den_lam`). Compared with the stored terms structurally. -/
def RecTele (env : KEnv) (kr : KKey) : Prop :=
  ∃ (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon))
    (tbs : List (KExpr × BinderMeta)) (C : KExpr),
    env.find? kr = some (.recInfo cvr mI rP krules) ∧ cvr.type = piTele tbs C ∧ tbs.length = rP ∧
    ∀ krl ∈ krules, ∃ (bs : List (KExpr × BinderMeta)) (b : KExpr), krl.rhs = lamTele bs b ∧
      bs.length = rP + krl.nfields ∧ (bs.take rP).map (·.1) = tbs.map (·.1)

/-- **The program side of a recursor** (G3, part D; as `CaseProg.recr` for a `case` entry): every
constructor of `S` declared of the recursor's inductive has the recursor's parameter count, and
the Src rule at its declared index is its own (by key) with its field count; at the pinned `Nat`
the rules are `Nat.zero`'s and `Nat.succ`'s. Why: F2 selects the rule by the major's declared
index (`selectRule`), ι the stored rule by its constructor's key, and `RecStored` matches the Src
rules with the stored ones by position only. -/
def RecProg (p : Program) (κ : CId → KKey) (S : CId → Prop) (r : CId) : Prop :=
  ∃ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term), p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) ∧
    (∀ c, S c → ∀ (sf' : Bool) (lv' cidx np' nf : Nat) (ty' : Term),
      p.decl? c = some (.ctor sf' lv' ind cidx np' nf ty') →
      np' = np ∧ ∃ rl, rules[cidx]? = some rl ∧ κ rl.ctor = κ c ∧ rl.fields = nf) ∧
    (some ind = p.known.nat → np = 0 ∧
      rules.map (fun rl => (κ rl.ctor, rl.fields)) =
        [((natZeroName : KKey), 0), ((natSuccName : KKey), 1)])

/-- **The rules' constructors, as ι and canonicity read them** (G3, part D): the recursor's major
premise's domain (its stored type's binder after the `mI` of the prefix) is the declared
inductive at some levels `ls` applied to the recursor's parameters; every stored rule's
constructor is stored with the recursor's parameter count and as many level parameters as `ls`,
and its stored type, after its parameters and fields, ends in the inductive at the constructor's
own level parameters with at most its parameters as arguments (no index). What the proof reads:
ι names the constructor at the major domain's levels `ls` and asks its codomain to carry no index;
the relation gives the major's set as the constructor's image at the assignment it was built at,
which is the image at `ls` without a law where the constructor has no level parameters
(`Laws.cval_params`) and by canonicity (`Laws.ctor_canon`, at the inductive, never a proposition
by the class) where it has some, canonicity reading the codomain's head. As the `case` shape's
`CaseWF.ctorRaw`; compared structurally. -/
def RecCtorsRaw (p : Program) (env : KEnv) (κ : CId → KKey) (r : CId) : Prop :=
  ∃ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term) (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon))
    (dom body : KExpr) (m : BinderMeta) (ls : List Level),
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) ∧
    env.find? (κ r) = some (.recInfo cvr mI rP krules) ∧ piBody mI cvr.type = .forallE dom body m ∧
    dom = Expr.mkAppN (.const (κ ind) ls) (bvarsFrom (mI - np) np) ∧
    ∀ krl ∈ krules, ∃ (cvC : ConstantVal .anon) (nF : Nat),
      env.find? krl.ctor = some (.ctorInfo cvC np nF) ∧ cvC.levelParams.length = ls.length ∧
      (piBody (np + nF) cvC.type).getAppFn = .const (κ ind) (cvC.levelParams.map .param) ∧
      (piBody (np + nF) cvC.type).getAppArgs.length ≤ np

/-- Every relevance annotation of a Src term names only level variables below `n`: SrcEval's
decisions there (which argument it evaluates) read only the first `n` levels it carries. -/
def relsBelow (n : Nat) : Term → Bool
  | .app f a _ r => r.irrWhen.params.all (· < n) && relsBelow n f && relsBelow n a
  | .lam _ d b => relsBelow n d && relsBelow n b
  | .pi _ _ d c => relsBelow n d && relsBelow n c
  | .letE _ r t v b =>
    r.irrWhen.params.all (· < n) && relsBelow n t && relsBelow n v && relsBelow n b
  | .proj _ _ e => relsBelow n e
  | _ => true

/-- **The rules' fields** (G3, part E; the approved field-domains fact, its rule half): with `ls`
the levels the recursor's major premise's domain names, every stored rule's constructor is stored
with no parameter and the rule's field count, its stored type closed and covered by its level
parameters; instantiated at `ls`, its type is a telescope of as many field binders as the rule has,
and the rule's λ-domains after the prefix are those field domains lifted past the prefix. What the
proof reads: β through the rule's λs at the fields needs each field in its λ's domain, and the
constructor value's fields fit its type at the assignment and environment it was built at, which
the type being closed and covered moves to the recursor's. Not the minor premise's field binders
(the other half of the approved fact): the direct route checks each site of a rule body against the
minor premise's own binder (`RecSites`). Compared with the stored terms structurally. -/
def RecFields (env : KEnv) (kr : KKey) : Prop :=
  ∃ (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)) (dom body : KExpr)
    (m : BinderMeta) (D : KKey) (ls : List Level),
    env.find? kr = some (.recInfo cvr mI rP krules) ∧ piBody mI cvr.type = .forallE dom body m ∧
    dom.getAppFn = .const D ls ∧
    ∀ krl ∈ krules, ∃ (cvC : ConstantVal .anon) (fbs bs : List (KExpr × BinderMeta)) (Cc b : KExpr),
      env.find? krl.ctor = some (.ctorInfo cvC 0 krl.nfields) ∧ bvarsLt 0 cvC.type = true ∧
      cvC.type.allLevelParamsDefined cvC.levelParams = true ∧
      cvC.type.instantiateLevelParams cvC.levelParams ls = piTele fbs Cc ∧
      fbs.length = krl.nfields ∧ krl.rhs = lamTele bs b ∧ bs.length = rP + krl.nfields ∧
      (bs.drop rP).map (·.1) = (liftTele rP 0 fbs).map (·.1)

/-- **The rule bodies** (G3, part E): every Src rule's body, peeled of the prefix's and the fields'
λs (what SrcEval evaluates), names no constant, and the rule's relevance annotations name only the
recursor's level variables; every stored rule is closed. What the proof reads: SrcEval evaluates the
body through `eval`, whose induction hypothesis asks the body to run (`Runs`): its kernel term
closed, and every constant it may unfold at an instance the fundamental lemma's `Ok` admits, which
nothing decides for rule bodies; so no constant (no recursive call: `Nat.rec`'s `succ` rule is
refused here). Its annotations below the level count let the proof read the body at the levels
SrcEval carries cut or padded to the recursor's level count (`fire` knows no length for them). -/
def RecBodies (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (r : CId) :
    Prop :=
  ∃ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term) (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)),
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) ∧
    env.find? (κ r) = some (.recInfo cvr mI rP krules) ∧
    (∀ rl ∈ rules, (∃ t', IxCC.Src.peelLams (np + nmot + nmin + rl.fields) rl.rhs = some t' ∧
        ∀ c, t'.mentions c = false) ∧ relsBelow (lpsOf r).length rl.rhs = true) ∧
    ∀ krl ∈ krules, bvarsLt 0 krl.rhs = true

/-- **The recursor clause as first landed**: no constant of `S` is a recursor. -/
def NoRecr (p : Program) (S : CId → Prop) : Prop :=
  ∀ c, S c → ∀ sf kk lvls np nmot nmin ni ind rules ty,
    p.decl? c ≠ some (.recr sf kk lvls np nmot nmin ni ind rules ty)

/-- A recursor's class is read off its declaration. -/
theorem recClassB_recr {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId} {k : RecClass}
    (h : recClassB p env κ r = some k) :
    ∃ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) := by
  cases hd : p.decl? r with
  | none => cases hk : p.table.recKindOf r <;> simp [recClassB, hd, hk] at h
  | some d =>
    cases d with
    | recr sf kk lvls np nmot nmin ni ind rules ty =>
      exact ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, rfl⟩
    | _ => cases hk : p.table.recKindOf r <;> simp [recClassB, hd, hk] at h

/-- At class `empty` the table's kind is `empty` (at every level). -/
theorem recClassB_empty {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId}
    (h : recClassB p env κ r = some .empty) : p.table.recKindOf r = some .empty := by
  unfold recClassB at h
  split at h
  · assumption
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · cases h
  · cases h

/-- At class `eqRec`: the key is `Eq.rec`'s, the table's kind is `subsingleton` at every level with
no fields, and the declaration has two parameters, one motive, one minor premise, one index and one
rule. -/
theorem recClassB_eqRec {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId}
    (h : recClassB p env κ r = some .eqRec) :
    κ r = eqRecName ∧
      p.table.recKindOf r = some (.subsingleton (IxCC.Src.PropWhen.allZero []) []) ∧
      ∃ sf kk lvls ind rl ty, p.decl? r = some (.recr sf kk lvls 2 1 1 1 ind [rl] ty) := by
  unfold recClassB at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      have hw : ∀ w : IxCC.Src.PropWhen, (w == .allZero []) = true → w = .allZero [] := by
        intro w hw
        cases w with
        | never => cases hw
        | allZero ps =>
          cases ps with
          | nil => rfl
          | cons _ _ => cases hw
      obtain rfl := hw _ hc2
      exact ⟨hc1, by assumption, _, _, _, _, _, _, by assumption⟩
    · cases h
  · split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · cases h
  · cases h

/-- At class `flat`: the table's kind is `ordinary`, the declaration has no parameter and no
index, its inductive is stored as never a proposition, and every rule has no field and a body,
peeled of the motives' and minor premises' λs, that is a variable below their number. -/
theorem recClassB_flat {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId}
    (h : recClassB p env κ r = some .flat) :
    p.table.recKindOf r = some .ordinary ∧
      ∃ sf kk lvls nmot nmin ind rules ty,
        p.decl? r = some (.recr sf kk lvls 0 nmot nmin 0 ind rules ty) ∧
        neverPropB env (κ ind) = true ∧
        ∀ rl ∈ rules, rl.fields = 0 ∧
          ∃ i, IxCC.Src.peelLams (nmot + nmin) rl.rhs = some (.var i) ∧ i < nmot + nmin := by
  unfold recClassB at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i sf kk lvls np nmot nmin ind rules ty hd hk
    split at h
    · rename_i hn
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
        obtain ⟨rfl, hall⟩ := hc
        refine ⟨hk, sf, kk, lvls, nmot, nmin, ind, rules, ty, hd, hn, fun rl hrl => ?_⟩
        obtain ⟨hf, hb⟩ := hall rl hrl
        refine ⟨hf, ?_⟩
        unfold bodyVarB at hb
        split at hb
        · rename_i i hp
          exact ⟨i, hp, of_decide_eq_true hb⟩
        · cases hb
      · split at h <;> cases h
    · cases h
  · cases h

/-- At class `noParams`: the table's kind is `ordinary`, the declaration has no parameter and no
index, and its inductive is stored as never a proposition. -/
theorem recClassB_noParams {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId}
    (h : recClassB p env κ r = some .noParams) :
    p.table.recKindOf r = some .ordinary ∧
      ∃ sf kk lvls nmot nmin ind rules ty,
        p.decl? r = some (.recr sf kk lvls 0 nmot nmin 0 ind rules ty) ∧
        neverPropB env (κ ind) = true := by
  unfold recClassB at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i sf kk lvls np nmot nmin ind rules ty hd hk
    split at h
    · rename_i hn
      split at h
      · cases h
      · split at h
        · rename_i hnp
          simp only [beq_iff_eq] at hnp
          subst hnp
          exact ⟨hk, sf, kk, lvls, nmot, nmin, ind, rules, ty, hd, hn⟩
        · cases h
    · cases h
  · cases h

/-- **The faithfulness clauses** (the spike's `Faith`, with `lvls` added), over a recursor clause
`Recs`: `Faith` takes `RecFacts`; as first landed it took `NoRecr` (`FaithWith.mono`). -/
structure FaithWith (Recs : Prop) (p : Program) (env : KEnv) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (S : CId → Prop) : Prop where
  stored : ∀ c, S c → ∃ ci, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = lpsOf c
  lvls : ∀ c, S c → lvlsOf p c = (lpsOf c).length
  nodup : ∀ c, S c → (lpsOf c).Nodup
  noCsimp : ∀ c g us thm, S c → p.table.resolveOf c ≠ some (.csimp g us thm)
  /-- No fixed-width word entry (stage W1): their model fact (`wordAccel_of_eqns`) is not yet in
  the library, so a program whose relevant closure reaches one is outside the grounded fragment. -/
  noWord : ∀ c w op thm, S c → p.table.resolveOf c ≠ some (.word w op thm)
  /-- the recursors of `S` (`RecFacts`: each in an admitted class, with the checked shape; as
  first landed, `NoRecr`: none) -/
  recs : Recs
  noQuot : ∀ c, S c → ∀ qk lvls ty, p.decl? c ≠ some (.quot qk lvls ty)
  noOpaque : ∀ c, S c → p.table.isOpaqueByValue c = false
  prim : ∀ c op, S c → p.table.resolveOf c = some (.prim op) → κ c = primKey op ∧
    ∃ ci, env.find? (primKey op) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      op.arity ≤ kPis ci.toConstantVal.type
  ctor : ∀ c, S c → ∀ sf lvls ind cidx np nf ty,
    p.decl? c = some (.ctor sf lvls ind cidx np nf ty) →
    ∃ cv, env.find? (κ c) = some (.ctorInfo cv np nf) ∧ np + nf ≤ kPis cv.type
  /-- a `case` entry's recursor is of kind `ordinary` (SrcEval forces the major and fires F5) or
  `empty` (SrcEval traps: step E0), and the stored constant has a binder for every argument -/
  caseRec : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
    (p.table.recKindOf r = some .ordinary ∨ p.table.recKindOf r = some .empty) ∧
    ∃ ci, env.find? (κ c) = some ci ∧ p.headArity (.cases c) ≤ kPis ci.toConstantVal.type
  defn : ∀ c, S c → p.table.resolveOf c = none → ∀ lvls ty v,
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    (∃ cv val hint, env.find? (κ c) = some (.defnInfo cv val hint)) ∧ ConstsIn S v
  eqnClosed : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) → ConstsIn S body
  proj : ∀ s, S s → ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) →
    ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → ∀ i, i < nf →
      ∃ entry, env.findProj? (κ s) i = some entry ∧ entry.ctor = κ c
  /-- a structure of `S` whose constructor is in `S` and has fields is never a proposition (the
  class at which `Laws.proj_ctor` is assumed: a proposition's constructor image is the proof
  point, from which no data field can be read back) -/
  projSort : ∀ s, S s → ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) →
    S c → ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → 0 < nf →
      NeverProp env (κ s)
  natZero : ∀ c, p.known.natZero = some c → κ c = natZeroName
  natSucc : ∀ c, p.known.natSucc = some c → κ c = natSuccName
  bool : ∀ (b : Bool) c, (if b then p.known.boolTrue else p.known.boolFalse) = some c →
    S c ∧ κ c = (if b then boolTrueName else boolFalseName) ∧
    ∃ cv, env.find? (κ c) = some (.ctorInfo cv 0 0) ∧ cv.levelParams = []

/-- **`Faith` as first landed** (before G3): no constant of `S` is a recursor. -/
abbrev FaithNoRecr (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) : Prop :=
  FaithWith (NoRecr p S) p env κ lpsOf S

theorem FaithWith.mono {A B : Prop} {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} (h : A → B) (hF : FaithWith A p env κ lpsOf S) :
    FaithWith B p env κ lpsOf S :=
  { hF with recs := h hF.recs }

/-- `Nat` and its constructors are stored as the literal reading needs. -/
structure NatBasis (env : KEnv) : Prop where
  nat : ∃ ci : ConstantInfo .anon, env.find? natName = some ci ∧ ci.toConstantVal.levelParams = []
  zero : ∃ cv : ConstantVal .anon, env.find? natZeroName = some (.ctorInfo cv 0 0) ∧
    cv.name = natZeroName ∧ cv.type = .const natName [] ∧ cv.levelParams = []
  succ : ∃ cv : ConstantVal .anon, env.find? natSuccName = some (.ctorInfo cv 0 1) ∧
    cv.name = natSuccName ∧
    cv.type = .forallE (.const natName []) (.const natName []) { pw := PropWhen.never } ∧
    cv.levelParams = []

/-- **The checked shapes of the `case` entries** of `S` whose recursor is of kind `ordinary`
(consumed by the generic `case` lemma). At an entry of kind `empty` SrcEval traps and F5 is never
asked (step E0), so no shape is read there. -/
def CaseFacts (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop :=
  ∀ c r, S c → p.table.resolveOf c = some (.case r) → p.table.recKindOf r = some .ordinary →
    ∃ sh, CaseStored env (κ c) (κ r) sh ∧ CaseProg p κ S r sh

/-- **Every decidable fact the root theorem consumes** about the program, the kernel's reading
and the certificate's annotation, on a set `S` of constants, over a recursor clause `Recs`
(`GroundFacts` takes `RecFacts`, decided by the check; as first landed, `NoRecr`). -/
structure GroundFactsWith (Recs : Prop) (p : Program) (env : KEnv) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop where
  faith : FaithWith Recs p env κ lpsOf S
  natBasis : NatBasis env
  eqns : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) →
    (∃ d, EqnShape env κ c thm d) ∧
      ∀ d, EqnShape env κ c thm d → TermCorrS κ (lpsOf c) [] body d.body
  values : ∀ c lvls ty v cv val hint, S c → p.table.resolveOf c = none →
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    env.find? (κ c) = some (.defnInfo cv val hint) → TermCorrS κ (lpsOf c) [] v val
  /-- every run term is closed -/
  closed : ∀ c t e, S c → RunPair p env κ c t e → bvarsLt 0 e = true
  okClosed : OkClosed p ann S

/-- **`GroundFacts` as first landed** (before G3): no constant of `S` is a recursor. -/
abbrev GroundFactsNoRecr (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  GroundFactsWith (NoRecr p S) p env κ lpsOf ann S

theorem GroundFactsWith.mono {A B : Prop} {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (h : A → B)
    (hG : GroundFactsWith A p env κ lpsOf ann S) : GroundFactsWith B p env κ lpsOf ann S :=
  { hG with faith := hG.faith.mono h }


end IxCC.Grounding
