import IxCCGrounding.Ok
import IxCCGrounding.CaseCheck
import IxCCGrounding.Facts

/-!
# The check (`IxCCGrounding.Check`)

**Every decidable fact the grounding theorems consume, decided by one Boolean function with a
proved soundness lemma** (`groundCheck`, `groundFacts_of_check`): over the program SrcEval runs,
the kernel's reading of the closure, the key map, the level parameters, the certificate's
annotation and a finite list `Sl` of constants. It imports neither the kernel's model nor any
proof about it, so `tests-grounding` runs it on closure bytes, conjunct by conjunct
(`checkParts`): each conjunct has a name, and the suite's negative controls assert that a
mutation targeting one makes exactly that one false.

| Conjunct | What it decides |
| --- | --- |
| `stored` | every constant of `Sl` is stored under its key, with its level parameters |
| `lvls` | the program's level count is the stored one |
| `nodup` | the level parameters are distinct |
| `noCsimp`, `noWord`, `declOk`, `notOpaque` | the fragment: no `csimp` entry, fixed-width word entry (stage W1), quotient constant, or opaque by value; a recursor only in an admitted class (`recClassB`, `admittedClasses`) |
| `recShape` | a recursor is stored with the program's counts, level parameters and rules, its type a binder for every argument SrcEval takes (`RecStored`); at `Eq.rec`, `Eq.refl` and `Eq.rec` stored as F3 reads them (`EqReflBasis`, `EqRecBasis`: `Eq.rec`'s type and its one rule compared with `eqRecType` and `eqRecRhs`) |
| `prim` | a `prim` entry is the operation's role, stored with no level parameters, telescope long enough |
| `ctor` | a constructor is stored with the program's counts, telescope long enough |
| `caseRec` | a `case` entry's recursor is ordinary, the key's telescope long enough |
| `defn` | a δ-unfolded definition is stored as a definition; its value names only `Sl` |
| `eqnNames` | an `eqn` body names only `Sl` |
| `proj` | a projected structure has a projection table naming its constructor; one whose constructor is in `Sl` and has fields is never a proposition (`NeverProp`) |
| `pins` | the `Nat` and `Bool` pins are the kernel's roles; the `Bool` constructors in `Sl` |
| `natBasis` | `Nat`, `Nat.zero` and `Nat.succ` stored as the literal reading needs |
| `eqBasis` | `Eq` stored with its type |
| `eqnShape` | each `eqn` entry's theorem has the checked shape (`EqnShape`) |
| `eqnCorr`, `eqnClosed` | each `eqn` body corresponds to the equation body (its `let`s through the substitution of their copies, `corrSB []`), which is closed |
| `valueCorr`, `valueClosed` | each δ value corresponds to the stored value, the ζ-reduct (`corrSB []`), which is closed |
| `okClosed` | `Ok`'s closure (`okClosedB`) |
| `caseShape` | each `case` entry's stored `casesOn`, recursor and constructors have the checked shape (`CaseStored`, read by `caseShape?`), its inductive never a proposition |
| `caseProg` | each `case` entry's recursor and constructors in the program agree with the shape (`CaseProg`) |
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-! ## Constants a term names -/

/-- The constants a Src term names (with repeats). -/
def constsOf : Term → List CId
  | .const c _ => [c]
  | .app f a _ _ => constsOf f ++ constsOf a
  | .lam _ d t | .pi _ _ d t => constsOf d ++ constsOf t
  | .letE _ _ t v b => constsOf t ++ constsOf v ++ constsOf b
  | .proj s _ e => s :: constsOf e
  | _ => []

theorem mentions_constsOf {c : CId} : ∀ {t : Term}, t.mentions c = true → c ∈ constsOf t
  | .var _, h | .sort _, h | .natLit _, h | .strLit _, h => by simp [Term.mentions] at h
  | .const d _, h => by simp only [Term.mentions, beq_iff_eq] at h; simp [constsOf, h]
  | .app f a _ _, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .lam _ d t, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .pi _ _ d t, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .letE _ _ t v b, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mentions_constsOf h))
    · exact Or.inl (Or.inr (mentions_constsOf h))
    · exact Or.inr (mentions_constsOf h)
  | .proj s _ e, h => by
    simp only [Term.mentions, Bool.or_eq_true, beq_iff_eq] at h
    simp only [constsOf, List.mem_cons]
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (mentions_constsOf h)

/-- Every constant `t` names is in `Sl`. -/
def namesInB (Sl : List CId) (t : Term) : Bool := (constsOf t).all fun c => decide (c ∈ Sl)

theorem constsIn_of_check {Sl : List CId} {t : Term} (h : namesInB Sl t = true) :
    ConstsIn (· ∈ Sl) t := by
  intro c hc
  have := List.all_eq_true.mp h c (mentions_constsOf hc)
  simpa using this

/-! ## The correspondence of terms -/

def univCorrB (lps : List Nat) : IxCC.Ixon.Univ → Level → Bool
  | .zero, .zero => true
  | .succ u, .succ l => univCorrB lps u l
  | .max a b, .max c d => univCorrB lps a c && univCorrB lps b d
  | .imax a b, .imax c d => univCorrB lps a c && univCorrB lps b d
  | .var i, .param p => lps[i.toNat]? == some p
  | _, _ => false

theorem univCorr_of_check {lps : List Nat} :
    ∀ (u : IxCC.Ixon.Univ) (l : Level), univCorrB lps u l = true → UnivCorr lps u l := by
  intro u
  induction u with
  | zero => intro l h; cases l <;> simp [univCorrB] at h; exact .zero
  | succ u ih => intro l h; cases l <;> simp [univCorrB] at h; exact .succ (ih _ h)
  | max a b iha ihb =>
    intro l h; cases l <;> simp [univCorrB] at h; exact .max (iha _ h.1) (ihb _ h.2)
  | imax a b iha ihb =>
    intro l h; cases l <;> simp [univCorrB] at h; exact .imax (iha _ h.1) (ihb _ h.2)
  | var i => intro l h; cases l <;> simp [univCorrB] at h; exact .var h

def termCorrB (κ : CId → KKey) (lps : List Nat) : Term → KExpr → Bool
  | .var i, .bvar j => i == j
  | .sort u, .sort l => univCorrB lps u l
  | .const c us, .const k ls =>
    decide (k = κ c) && us.length == ls.length && (us.zip ls).all fun (u, l) => univCorrB lps u l
  | .app f a _ _, .app f' a' => termCorrB κ lps f f' && termCorrB κ lps a a'
  | .lam _ d b, .lam d' b' _ => termCorrB κ lps d d' && termCorrB κ lps b b'
  | .pi _ _ d c, .forallE d' c' _ => termCorrB κ lps d d' && termCorrB κ lps c c'
  | .proj s i e, .proj k j e' => decide (k = κ s) && i == j && termCorrB κ lps e e'
  | .natLit n, .lit (.natVal m) => n == m
  | _, _ => false

theorem termCorr_of_check {κ : CId → KKey} {lps : List Nat} :
    ∀ (t : Term) (e : KExpr), termCorrB κ lps t e = true → TermCorr κ lps t e := by
  intro t
  induction t with
  | var i => intro e h; cases e <;> simp [termCorrB] at h; subst h; exact .var
  | sort u => intro e h; cases e <;> simp [termCorrB] at h; exact .sort (univCorr_of_check _ _ h)
  | const c us =>
    intro e h
    cases e <;> simp only [termCorrB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hall⟩ := h
    refine .const hlen fun i u l hu hl => univCorr_of_check _ _ ?_
    exact hall (u, l) (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hu, hl⟩))
  | app f a m r ihf iha =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .app (ihf _ h.1) (iha _ h.2)
  | lam b d body ihd ihb =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .lam (ihd _ h.1) (ihb _ h.2)
  | pi b r d c ihd ihc =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .pi (ihd _ h.1) (ihc _ h.2)
  | letE => intro e h; cases e <;> simp [termCorrB] at h
  | proj s i e ih =>
    intro e' h
    cases e' <;> simp only [termCorrB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact .proj (ih _ h)
  | natLit n =>
    intro e h
    cases e with
    | lit l => cases l <;> simp [termCorrB] at h; subst h; exact .natLit
    | _ => simp [termCorrB] at h
  | strLit => intro e h; cases e <;> simp [termCorrB] at h

/-! ## The correspondence under a substitution, decided (`valueCorr`, `eqnCorr`) -/

/-- **`TermCorrS`, decided** (`valueCorr` and `eqnCorr` at `σ = []`): structural on the Src term, the
copy of each `let`'s variable produced by `zcopy` and checked at every occurrence; a copy not at
depth 0 only in the closure-capture shape (`cloShapeB`, step C), tried after the live case fails. -/
def corrSB (κ : CId → KKey) (lps : List Nat) : Sig → Term → KExpr → Bool
  | σ, .var i, e => match σ[i]? with | some (some e') => decide (e' = e) | _ => false
  | _, .sort u, .sort l => univCorrB lps u l
  | _, .const c us, .const k ls =>
    decide (k = κ c) && us.length == ls.length && (us.zip ls).all fun (u, l) => univCorrB lps u l
  | σ, .app f a _ _, .app f' a' => corrSB κ lps σ f f' && corrSB κ lps σ a a'
  | σ, .lam _ d b, .lam d' b' _ => corrSB κ lps σ d d' && corrSB κ lps (liftσ σ) b b'
  | σ, .pi _ _ d c, .forallE d' c' _ => corrSB κ lps σ d d' && corrSB κ lps (liftσ σ) c c'
  | σ, .proj s i x, .proj k j x' => decide (k = κ s) && i == j && corrSB κ lps σ x x'
  | _, .natLit n, .lit (.natVal m) => n == m
  | σ, .letE _ _ _ v b, e =>
    match zcopy b e with
    | some v' =>
      (if subAt0B v' e then corrSB κ lps σ v v'
        else cloShapeB b e v' &&
          corrSB κ lps (σ.map (·.map (Expr.liftLooseBVars 1 0))) v (v'.liftLooseBVars 1 0)) &&
        corrSB κ lps (some v' :: σ) b e
    | none => corrSB κ lps (none :: σ) b e
  | _, _, _ => false

theorem termCorrS_of_check {κ : CId → KKey} {lps : List Nat} :
    ∀ (σ : Sig) (t : Term) (e : KExpr), corrSB κ lps σ t e = true → TermCorrS κ lps σ t e := by
  intro σ t
  induction t generalizing σ with
  | var i =>
    intro e h
    simp only [corrSB] at h
    split at h
    · rename_i e' he
      simp only [decide_eq_true_eq] at h
      subst h
      exact .var he
    · cases h
  | sort u =>
    intro e h; cases e <;> simp [corrSB] at h; exact .sort (univCorr_of_check _ _ h)
  | const c us =>
    intro e h
    cases e <;> simp only [corrSB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hall⟩ := h
    refine .const hlen fun i u l hu hl => univCorr_of_check _ _ ?_
    exact hall (u, l) (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hu, hl⟩))
  | app f a m r ihf iha =>
    intro e h; cases e <;> simp [corrSB] at h; exact .app (ihf _ _ h.1) (iha _ _ h.2)
  | lam b d body ihd ihb =>
    intro e h; cases e <;> simp [corrSB] at h; exact .lam (ihd _ _ h.1) (ihb _ _ h.2)
  | pi b r d c ihd ihc =>
    intro e h; cases e <;> simp [corrSB] at h; exact .pi (ihd _ _ h.1) (ihc _ _ h.2)
  | letE c r ty v b _ ihv ihb =>
    intro e h
    simp only [corrSB] at h
    split at h
    · rename_i v' hz
      simp only [Bool.and_eq_true] at h
      obtain ⟨hv, hb⟩ := h
      cases hsub : subAt0B v' e
      · -- the closure-capture shape (step C)
        simp only [hsub, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hv
        obtain ⟨hcl, hv⟩ := hv
        unfold cloShapeB at hcl
        split at hcl
        · exact .letClo hz hsub hcl (ihv _ _ hv) (ihb _ _ hb)
        · cases hcl
      · simp only [hsub, ↓reduceIte] at hv
        exact .letLive hz hsub (ihv _ _ hv) (ihb _ _ hb)
    · rename_i hz
      exact .letDead hz (ihb _ _ h)
  | proj s i e ih =>
    intro e' h
    cases e' <;> simp only [corrSB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact .proj (ih _ _ h)
  | natLit n =>
    intro e h
    cases e with
    | lit l => cases l <;> simp [corrSB] at h; subst h; exact .natLit
    | _ => simp [corrSB] at h
  | strLit => intro e h; cases e <;> simp [corrSB] at h

/-- **On a let-free run term the substitution check is the landed one**: what `termCorrB` accepts
on a closed kernel term, `corrSB []` accepts (so no verdict of a let-free program moves). -/
theorem corrSB_idσ_of_termCorrB {κ : CId → KKey} {lps : List Nat} :
    ∀ (t : Term) (n : Nat) (e : KExpr), termCorrB κ lps t e = true → bvarsLt n e = true →
      corrSB κ lps (idσ n) t e = true := by
  intro t
  induction t with
  | var i =>
    intro n e h hc
    cases e <;> simp only [termCorrB, beq_iff_eq, Bool.false_eq_true] at h
    subst h
    simp only [bvarsLt, decide_eq_true_eq] at hc
    simp [corrSB, idσ_get hc]
  | sort u => intro n e h _; cases e <;> simp_all [termCorrB, corrSB]
  | const c us => intro n e h _; cases e <;> simp_all [termCorrB, corrSB]
  | app f a m r ihf iha =>
    intro n e h hc
    cases e <;> simp only [termCorrB, Bool.and_eq_true, Bool.false_eq_true] at h
    simp only [bvarsLt, Bool.and_eq_true] at hc
    simp [corrSB, ihf _ _ h.1 hc.1, iha _ _ h.2 hc.2]
  | lam b d body ihd ihb =>
    intro n e h hc
    cases e <;> simp only [termCorrB, Bool.and_eq_true, Bool.false_eq_true] at h
    simp only [bvarsLt, Bool.and_eq_true] at hc
    simp [corrSB, liftσ_idσ, ihd _ _ h.1 hc.1, ihb _ _ h.2 hc.2]
  | pi b r d c ihd ihc =>
    intro n e h hc
    cases e <;> simp only [termCorrB, Bool.and_eq_true, Bool.false_eq_true] at h
    simp only [bvarsLt, Bool.and_eq_true] at hc
    simp [corrSB, liftσ_idσ, ihd _ _ h.1 hc.1, ihc _ _ h.2 hc.2]
  | letE => intro n e h _; cases e <;> simp [termCorrB] at h
  | proj s i x ih =>
    intro n e h hc
    cases e <;> simp only [termCorrB, Bool.and_eq_true, Bool.false_eq_true] at h
    simp only [bvarsLt] at hc
    simp only [corrSB, Bool.and_eq_true]
    exact ⟨h.1, ih _ _ h.2 hc⟩
  | natLit n' =>
    intro n e h _
    cases e with
    | lit l => cases l <;> simp_all [termCorrB, corrSB]
    | _ => simp [termCorrB] at h
  | strLit => intro n e h _; cases e <;> simp [termCorrB] at h

/-- `corrSB_idσ_of_termCorrB` at a closed term (`σ = []`). -/
theorem corrSB_of_termCorrB {κ : CId → KKey} {lps : List Nat} {t : Term} {e : KExpr}
    (h : termCorrB κ lps t e = true) (hc : bvarsLt 0 e = true) : corrSB κ lps [] t e = true :=
  corrSB_idσ_of_termCorrB t 0 e h hc

/-- **A node-for-node correspondence is one under the identity substitution**, on a kernel term
closed in its context (the recursor rules, which the kernel generates, are read with `TermCorr`). -/
theorem termCorrS_of_termCorr {κ : CId → KKey} {lps : List Nat} {t : Term} {e : KExpr}
    (h : TermCorr κ lps t e) : ∀ {n : Nat}, bvarsLt n e = true → TermCorrS κ lps (idσ n) t e := by
  induction h with
  | @var i => intro n hc; simp only [bvarsLt, decide_eq_true_eq] at hc; exact .var (idσ_get hc)
  | sort hu => intro _ _; exact .sort hu
  | const hlen hu => intro _ _; exact .const hlen hu
  | app _ _ ihf iha =>
    intro n hc; simp only [bvarsLt, Bool.and_eq_true] at hc; exact .app (ihf hc.1) (iha hc.2)
  | lam _ _ ihd ihb =>
    intro n hc; simp only [bvarsLt, Bool.and_eq_true] at hc
    exact .lam (ihd hc.1) (by rw [liftσ_idσ]; exact ihb hc.2)
  | pi _ _ ihd ihc =>
    intro n hc; simp only [bvarsLt, Bool.and_eq_true] at hc
    exact .pi (ihd hc.1) (by rw [liftσ_idσ]; exact ihc hc.2)
  | proj _ ih => intro n hc; simp only [bvarsLt] at hc; exact .proj (ih hc)
  | natLit => intro _ _; exact .natLit

/-! ## The shape of an `eqn` entry -/

/-- Exactly `n` leading binders of a `λ`-telescope, and its body. -/
def lamSplit : Nat → KExpr → Option (List (KExpr × BinderMeta) × KExpr)
  | 0, e => some ([], e)
  | n + 1, .lam d b m => (lamSplit n b).map fun r => ((d, m) :: r.1, r.2)
  | _ + 1, _ => none

theorem lamSplit_spec (n : Nat) : ∀ (e : KExpr) (bs : List (KExpr × BinderMeta)) (b : KExpr),
    lamSplit n e = some (bs, b) → e = lamTele bs b ∧ bs.length = n := by
  induction n with
  | zero =>
    intro e bs b h
    simp only [lamSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro e bs b h
    cases e with
    | lam d e' m =>
      simp only [lamSplit] at h
      cases h' : lamSplit n e' with
      | none => rw [h'] at h; cases h
      | some r =>
        rw [h'] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e1, e2⟩ := ih e' r.1 r.2 (by rw [h'])
        exact ⟨by rw [e1]; rfl, by simp [e2]⟩
    | _ => simp [lamSplit] at h

theorem piSplit_length (n : Nat) : ∀ (T : KExpr) (bs : List (KExpr × BinderMeta)) (R : KExpr),
    piSplit n T = some (bs, R) → bs.length = n := by
  induction n with
  | zero =>
    intro T bs R h
    simp only [piSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro T bs R h
    cases T with
    | forallE d b m =>
      simp only [piSplit] at h
      cases h' : piSplit n b with
      | none => rw [h'] at h; cases h
      | some r =>
        rw [h'] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih b r.1 r.2 (by rw [h'])]
    | _ => simp [piSplit] at h

def eqBasisB (env : KEnv) : Bool :=
  match env.find? eqName with
  | some ci => ci.toConstantVal.levelParams == [0] && decide (ci.toConstantVal.type = eqType)
  | none => false

theorem eqBasis_of_check {env : KEnv} (h : eqBasisB env = true) : EqBasis env := by
  unfold eqBasisB at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨ci, hf, h.1, h.2⟩
  · exact absurd h (by simp)

/-- `EqnShape` without the `Eq` basis, decided. -/
def eqnShapeB (env : KEnv) (κ : CId → KKey) (c thm : CId) (d : EqnData) : Bool :=
  match env.find? (κ c), env.find? (κ thm) with
  | some ciF, some (.thmInfo cvT _) =>
    d.Ds.length == d.ms.length && cvT.levelParams == ciF.toConstantVal.levelParams &&
      decide (cvT.type = piTele d.Ds (Expr.mkAppN (.const eqName [d.u])
        [d.T, Expr.mkAppN (.const (κ c) (cvT.levelParams.map Level.param))
          (bvarsFrom 0 d.Ds.length), d.rhs])) &&
      decide (ciF.toConstantVal.type = piTele (d.Ds.zipWith (fun b m => (b.1, m)) d.ms) d.R)
  | _, _ => false

theorem eqnShape_of_check {env : KEnv} {κ : CId → KKey} {c thm : CId} {d : EqnData}
    (hE : EqBasis env) (h : eqnShapeB env κ c thm d = true) : EqnShape env κ c thm d := by
  unfold eqnShapeB at h
  split at h
  · rename_i ciF cvT pf hf ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨hE, ciF, cvT, pf, hf, ht, h1, h2, h3, h4⟩
  · exact absurd h (by simp)

theorem piTele_inj_app : ∀ (bs bs' : List (KExpr × BinderMeta)) (f a f' a' : KExpr),
    piTele bs (.app f a) = piTele bs' (.app f' a') → bs = bs' ∧ f = f' ∧ a = a'
  | [], [], _, _, _, _, h => by simp only [piTele, Expr.app.injEq] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, _, _, h => by simp [piTele] at h
  | _ :: _, [], _, _, _, _, h => by simp [piTele] at h
  | (A, m) :: bs, (A', m') :: bs', f, a, f', a', h => by
    simp only [piTele, Expr.forallE.injEq] at h
    obtain ⟨rfl, h2, rfl⟩ := h
    obtain ⟨rfl, h3⟩ := piTele_inj_app bs bs' f a f' a' h2
    exact ⟨rfl, h3⟩

theorem piTele_inj : ∀ (bs bs' : List (KExpr × BinderMeta)) (X X' : KExpr),
    bs.length = bs'.length → piTele bs X = piTele bs' X' → bs = bs' ∧ X = X'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, (A', m') :: bs', X, X', hl, h => by
    simp only [piTele, Expr.forallE.injEq] at h
    obtain ⟨rfl, h2, rfl⟩ := h
    obtain ⟨rfl, h3⟩ := piTele_inj bs bs' X X' (by simpa using hl) h2
    exact ⟨rfl, h3⟩

/-- **An `eqn` entry's equation body is determined by its shape.** -/
theorem eqnShape_body {env : KEnv} {κ : CId → KKey} {c thm : CId} {d d' : EqnData}
    (h : EqnShape env κ c thm d) (h' : EqnShape env κ c thm d') : d.body = d'.body := by
  obtain ⟨_, ciF, cvT, pf, hf, ht, hl, _, htT, htF⟩ := h
  obtain ⟨_, ciF', cvT', pf', hf', ht', hl', _, htT', htF'⟩ := h'
  rw [hf] at hf'; cases hf'
  rw [ht] at ht'; cases ht'
  simp only [Expr.mkAppN] at htT htT'
  obtain ⟨hD, hf1, hrhs⟩ := piTele_inj_app _ _ _ _ _ _ (htT.symm.trans htT')
  have hzl : (d.Ds.zipWith (fun b m => (b.1, m)) d.ms).length =
      (d'.Ds.zipWith (fun b m => (b.1, m)) d'.ms).length := by
    have e1 : d.Ds.length = d'.Ds.length := by rw [hD]
    simp only [List.length_zipWith]; omega
  obtain ⟨hz, _⟩ := piTele_inj _ _ _ _ hzl (htF.symm.trans htF')
  simp only [EqnData.body, hz, hrhs]

/-! ## The conjuncts -/

section Checks

variable (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (Sl : List CId)

def storedB (c : CId) : Bool :=
  match env.find? (κ c) with
  | some ci => ci.toConstantVal.levelParams == lpsOf c
  | none => false

def lvlsB (c : CId) : Bool := lvlsOf p c == (lpsOf c).length

def nodupB (c : CId) : Bool := decide (lpsOf c).Nodup

def noCsimpB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.csimp ..) => false
  | _ => true

def noWordB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.word ..) => false
  | _ => true

/-- No quotient constant; a recursor only in a class of `adm` (the check takes the library's
`admittedClasses`; as first landed, no class: `declOkB_nil`). -/
def declOkB (adm : List RecClass) (c : CId) : Bool :=
  match p.decl? c with
  | some (.recr ..) =>
    match recClassB p env κ c with
    | some k => adm.contains k
    | none => false
  | some (.quot ..) => false
  | _ => true

/-- `RecStored`, decided. -/
def recStoredB (r : CId) : Bool :=
  match p.decl? r, env.find? (κ r) with
  | some (.recr _ _ _ np nmot nmin ni _ rules _), some (.recInfo cvr mI rP krules) =>
    mI == np + nmot + nmin + ni && rP == np + nmot + nmin && cvr.levelParams == lpsOf r &&
      decide (np + nmot + nmin + ni + 1 ≤ kPis cvr.type) &&
      rules.length == krules.length &&
      (rules.zip krules).all fun (rl, krl) =>
        decide (κ rl.ctor = krl.ctor) && rl.fields == krl.nfields &&
          termCorrB κ (lpsOf r) rl.rhs krl.rhs
  | _, _ => false

/-- `EqReflBasis`, decided. -/
def eqReflBasisB : Bool :=
  match env.find? eqReflName with
  | some (.ctorInfo cv 2 0) => cv.levelParams == [0] && decide (cv.type = eqReflType)
  | _ => false

/-- `EqRecBasis`, decided (the type and the rule compared structurally with `eqRecType` and
`eqRecRhs`). -/
def eqRecBasisB : Bool :=
  match env.find? eqRecName with
  | some (.recInfo cvr mI rP [krl]) =>
    mI == 5 && rP == 4 && decide (cvr.type = eqRecType) && decide (krl.ctor = eqReflName) &&
      decide (krl.rhs = eqRecRhs)
  | _ => false

/-- `RecTele`, decided (domains compared structurally). -/
def recTeleB (kr : KKey) : Bool :=
  match env.find? kr with
  | some (.recInfo cvr _ rP krules) =>
    match piSplit rP cvr.type with
    | some (tbs, _) =>
      krules.all fun krl =>
        match lamSplit (rP + krl.nfields) krl.rhs with
        | some (bs, _) => decide ((bs.take rP).map (·.1) = tbs.map (·.1))
        | none => false
    | none => false
  | _ => false

/-- `RecProg`, decided (as `caseProgB`). -/
def recProgB (r : CId) : Bool :=
  match p.decl? r with
  | some (.recr _ _ _ np _ _ _ ind rules _) =>
    Sl.all (fun c =>
      match p.decl? c with
      | some (.ctor _ _ ind' cidx np' nf' _) =>
        if ind' == ind then
          np' == np &&
            match rules[cidx]? with
            | some rl => decide (κ rl.ctor = κ c) && rl.fields == nf'
            | none => false
        else true
      | _ => true) &&
    (if some ind == p.known.nat then
      np == 0 && decide (rules.map (fun rl => (κ rl.ctor, rl.fields)) =
        [((natZeroName : KKey), 0), ((natSuccName : KKey), 1)])
    else true)
  | _ => false

/-- `RecCtorsRaw`, decided (terms compared structurally). -/
def recCtorsRawB (r : CId) : Bool :=
  match p.decl? r, env.find? (κ r) with
  | some (.recr _ _ _ np _ _ _ ind _ _), some (.recInfo cvr mI _ krules) =>
    match piBody mI cvr.type with
    | .forallE dom _ _ =>
      match dom.getAppFn with
      | .const _ ls =>
        decide (dom = Expr.mkAppN (.const (κ ind) ls) (bvarsFrom (mI - np) np)) &&
        krules.all fun krl =>
          match env.find? krl.ctor with
          | some (.ctorInfo cvC np' nF) =>
            np' == np && cvC.levelParams.length == ls.length &&
              decide ((piBody (np + nF) cvC.type).getAppFn =
                .const (κ ind) (cvC.levelParams.map .param)) &&
              decide ((piBody (np + nF) cvC.type).getAppArgs.length ≤ np)
          | _ => false
      | _ => false
    | _ => false
  | _, _ => false

/-- `RecFields`, decided (terms compared structurally). -/
def recFieldsB (kr : KKey) : Bool :=
  match env.find? kr with
  | some (.recInfo cvr mI rP krules) =>
    match piBody mI cvr.type with
    | .forallE dom _ _ =>
      match dom.getAppFn with
      | .const _ ls =>
        krules.all fun krl =>
          match env.find? krl.ctor with
          | some (.ctorInfo cvC np nF) =>
            np == 0 && nF == krl.nfields && bvarsLt 0 cvC.type &&
              cvC.type.allLevelParamsDefined cvC.levelParams &&
              match piSplit krl.nfields (cvC.type.instantiateLevelParams cvC.levelParams ls),
                lamSplit (rP + krl.nfields) krl.rhs with
              | some (fbs, _), some (bs, _) =>
                decide ((bs.drop rP).map (·.1) = (liftTele rP 0 fbs).map (·.1))
              | _, _ => false
          | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- `RecBodies`, decided. -/
def recBodiesB (r : CId) : Bool :=
  match p.decl? r, env.find? (κ r) with
  | some (.recr _ _ _ np nmot nmin _ _ rules _), some (.recInfo _ _ _ krules) =>
    rules.all (fun rl =>
      (match IxCC.Src.peelLams (np + nmot + nmin + rl.fields) rl.rhs with
        | some t' => (constsOf t').isEmpty
        | none => false) && relsBelow (lpsOf r).length rl.rhs) &&
      krules.all fun krl => bvarsLt 0 krl.rhs
  | _, _ => false

/-- `RecSites`, decided: the direct route over every rule (the reading's table built once per
recursor), at the profiles where the major premise's binder datum does not hold. -/
def recSitesB (r : CId) : Bool :=
  match p.decl? r, env.find? (κ r) with
  | some (.recr _ _ _ _ _ _ _ _ rules _), some (.recInfo cvr mI _ krules) =>
    match piBody mI cvr.type with
    | .forallE _ _ m =>
      let tab := KTab.of env
      m.pw.paramsDefined (lpsOf r) &&
        (rules.zip krules).all fun (rl, krl) =>
          (termRefused tab (lpsOf r) directFuel (recProfiles (lpsOf r) m.pw) [] rl.rhs krl.rhs
            []).isEmpty
    | _ => false
  | _, _ => false

/-- A recursor has the checked shape (`RecStored`); where it is `Eq.rec` the `Eq.refl` and
`Eq.rec` bases hold; where it is `flat`, its rules' telescopes (`RecTele`), the program side
(`RecProg`) and its rules' constructors (`RecCtorsRaw`); where it is of class `noParams` (part E),
those three and its rules' fields (`RecFields`), its rule bodies (`RecBodies`) and its rule bodies'
sites typed by the direct route (`RecSites`). -/
def recShapeB (c : CId) : Bool :=
  match p.decl? c with
  | some (.recr ..) =>
    recStoredB p env κ lpsOf c &&
      (recClassB p env κ c != some .eqRec || (eqReflBasisB env && eqRecBasisB env)) &&
      (recClassB p env κ c != some .flat ||
        (recTeleB env (κ c) && recProgB p κ Sl c && recCtorsRawB p env κ c)) &&
      (recClassB p env κ c != some .noParams ||
        (recTeleB env (κ c) && recProgB p κ Sl c && recCtorsRawB p env κ c &&
          recFieldsB env (κ c) && recBodiesB p env κ lpsOf c && recSitesB p env κ lpsOf c))
  | _ => true

def primB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.prim op) =>
    decide (κ c = (primKey op : KKey)) &&
      match env.find? (primKey op) with
      | some ci => (ci.toConstantVal.levelParams == []) &&
          decide (op.arity ≤ kPis ci.toConstantVal.type)
      | none => false
  | _ => true

def ctorB (c : CId) : Bool :=
  match p.decl? c with
  | some (.ctor _ _ _ _ np nf _) =>
    match env.find? (κ c) with
    | some (.ctorInfo cv np' nf') => (np' == np) && (nf' == nf) && decide (np + nf ≤ kPis cv.type)
    | _ => false
  | _ => true

/-- A `case` entry's recursor is of kind `ordinary` or `empty` (step E0: SrcEval traps there), and
the stored constant has a binder for every argument. -/
def caseRecB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    (match p.table.recKindOf r with
      | some .ordinary => true
      | some .empty => true
      | _ => false) &&
    (match env.find? (κ c) with
      | some ci => decide (p.headArity (.cases c) ≤ kPis ci.toConstantVal.type)
      | none => false)
  | _ => true

def defnB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) =>
      (match env.find? (κ c) with
        | some (.defnInfo ..) => true
        | _ => false) && namesInB Sl v
    | _ => true
  | some _ => true

def eqnNamesB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => namesInB Sl body
  | _ => true

/-- A one-constructor inductive of `Sl`: its projection table names its constructor at every
field; and when the constructor is in `Sl` and has fields, the inductive is never a proposition
(`NeverProp`, where `Laws.proj_ctor` is assumed). -/
def projB (c : CId) : Bool :=
  match p.decl? c with
  | some (.induct _ _ _ _ _ [c₁]) =>
    match env.find? (κ c₁) with
    | some (.ctorInfo _ _ nf) =>
      ((List.range nf).all fun i =>
        match env.findProj? (κ c) i with
        | some e => decide (e.ctor = κ c₁)
        | none => false) &&
      (nf == 0 || !decide (c₁ ∈ Sl) || neverPropB env (κ c))
    | _ => true
  | _ => true

def boolPinB (b : Bool) : Bool :=
  match (if b then p.known.boolTrue else p.known.boolFalse) with
  | some c =>
    decide (c ∈ Sl) && decide (κ c = if b then boolTrueName else boolFalseName) &&
      match env.find? (κ c) with
      | some (.ctorInfo cv 0 0) => cv.levelParams == []
      | _ => false
  | none => true

def pinsB : Bool :=
  (match p.known.natZero with
    | some c => decide (κ c = natZeroName)
    | none => true) &&
  (match p.known.natSucc with
    | some c => decide (κ c = natSuccName)
    | none => true) &&
  boolPinB p env κ Sl true && boolPinB p env κ Sl false

def natBasisB : Bool :=
  (match env.find? natName with
    | some ci => ci.toConstantVal.levelParams == []
    | none => false) &&
  (match env.find? natZeroName with
    | some (.ctorInfo cv 0 0) =>
      decide (cv.name = natZeroName ∧ cv.type = .const natName [] ∧ cv.levelParams = [])
    | _ => false) &&
  (match env.find? natSuccName with
    | some (.ctorInfo cv 0 1) =>
      decide (cv.name = natSuccName ∧
        cv.type = .forallE (.const natName []) (.const natName []) { pw := PropWhen.never } ∧
        cv.levelParams = [])
    | _ => false)

/-- An `eqn` entry's shape, decided against the data read off the stored terms. -/
def eqnShapeOkB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm _) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => eqnShapeB env κ c thm d
    | none => false
  | _ => true

def eqnCorrB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm body) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => corrSB κ (lpsOf c) [] body d.body
    | none => false
  | _ => true

def eqnClosedB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm _) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => bvarsLt 0 d.body
    | none => false
  | _ => true

def valueCorrB (c : CId) : Bool :=
  match p.table.resolveOf c, p.decl? c, env.find? (κ c) with
  | none, some (.defn .defn .safe _ _ v), some (.defnInfo _ val _) => corrSB κ (lpsOf c) [] v val
  | _, _, _ => true

def valueClosedB (c : CId) : Bool :=
  match p.table.resolveOf c, p.decl? c, env.find? (κ c) with
  | none, some (.defn .defn .safe _ _ _), some (.defnInfo _ val _) => bvarsLt 0 val
  | _, _, _ => true

/-- A `case` entry's stored shape (none is read at an entry whose recursor is of kind `empty`, where
SrcEval traps: step E0). -/
def caseShapeB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.table.recKindOf r with
    | some .empty => true
    | _ =>
      match caseShape? env (κ c) (κ r) with
      | some sh => caseStoredB env (κ c) (κ r) sh
      | none => false
  | _ => true

/-- A `case` entry's program side (true when no shape is read: `caseShape` reports that; true at an
entry whose recursor is of kind `empty`, as `caseShape`). -/
def caseProgOkB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.table.recKindOf r with
    | some .empty => true
    | _ =>
      match caseShape? env (κ c) (κ r) with
      | some sh => caseProgB p κ Sl r sh
      | none => true
  | _ => true

end Checks

/-- **The conjuncts of the check, with the recursor classes `adm` admitted**, by name. -/
def checkPartsWith (adm : List RecClass) (p : Program) (env : KEnv) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) :
    List (String × Bool) :=
  [("stored", Sl.all (storedB env κ lpsOf)),
   ("lvls", Sl.all (lvlsB p lpsOf)),
   ("nodup", Sl.all (nodupB lpsOf)),
   ("noCsimp", Sl.all (noCsimpB p)),
   ("noWord", Sl.all (noWordB p)),
   ("declOk", Sl.all (declOkB p env κ adm)),
   ("recShape", Sl.all (recShapeB p env κ lpsOf Sl)),
   ("notOpaque", Sl.all fun c => p.table.isOpaqueByValue c == false),
   ("prim", Sl.all (primB p env κ)),
   ("ctor", Sl.all (ctorB p env κ)),
   ("caseRec", Sl.all (caseRecB p env κ)),
   ("defn", Sl.all (defnB p env κ Sl)),
   ("eqnNames", Sl.all (eqnNamesB p Sl)),
   ("proj", Sl.all (projB p env κ Sl)),
   ("pins", pinsB p env κ Sl),
   ("natBasis", natBasisB env),
   ("eqBasis", eqBasisB env),
   ("eqnShape", Sl.all (eqnShapeOkB p env κ)),
   ("eqnCorr", Sl.all (eqnCorrB p env κ lpsOf)),
   ("eqnClosed", Sl.all (eqnClosedB p env κ)),
   ("valueCorr", Sl.all (valueCorrB p env κ lpsOf)),
   ("valueClosed", Sl.all (valueClosedB p env κ)),
   ("okClosed", okClosedB p ann Sl),
   ("caseShape", Sl.all (caseShapeB p env κ)),
   ("caseProg", Sl.all (caseProgOkB p env κ Sl))]

/-- **The check with the recursor classes `adm` admitted.** -/
def groundCheckWith (adm : List RecClass) (p : Program) (env : KEnv) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkPartsWith adm p env κ lpsOf ann Sl).all (·.2)

/-- **The conjuncts of the check**, by name: the classes the library admits
(`admittedClasses`). -/
def checkParts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : List (String × Bool) :=
  checkPartsWith admittedClasses p env κ lpsOf ann Sl

/-- **The check.** -/
def groundCheck (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkParts p env κ lpsOf ann Sl).all (·.2)

theorem groundCheck_eq (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) :
    groundCheck p env κ lpsOf ann Sl = groundCheckWith admittedClasses p env κ lpsOf ann Sl := rfl

/-- As first landed, `declOk` refused every recursor: that is `declOkB` with no class admitted. -/
theorem declOkB_nil (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) :
    declOkB p env κ [] c =
      match p.decl? c with
      | some (.recr ..) => false
      | some (.quot ..) => false
      | _ => true := by
  unfold declOkB
  cases p.decl? c with
  | none => rfl
  | some d =>
    cases d with
    | recr => cases recClassB p env κ c <;> rfl
    | _ => rfl

/-- **Admitting more recursor classes only makes the check accept more**: `declOk` is the only
conjunct that reads `adm`, and it is monotone in it. -/
theorem groundCheckWith_mono {adm adm' : List RecClass} (hsub : ∀ k ∈ adm, k ∈ adm')
    {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : groundCheckWith adm p env κ lpsOf ann Sl = true) :
    groundCheckWith adm' p env κ lpsOf ann Sl = true := by
  have hd : ∀ c, declOkB p env κ adm c = true → declOkB p env κ adm' c = true := by
    intro c hc
    unfold declOkB at hc ⊢
    cases hdc : p.decl? c with
    | none => rfl
    | some d =>
      rw [hdc] at hc
      cases d with
      | recr =>
        simp only at hc ⊢
        cases hk : recClassB p env κ c with
        | none => rw [hk] at hc; exact hc
        | some k =>
          rw [hk] at hc
          simp only [List.contains_iff_mem] at hc ⊢
          exact hsub k hc
      | quot => exact hc
      | _ => rfl
  unfold groundCheckWith checkPartsWith at h ⊢
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  exact ⟨h1, h2, h3, h4, h5, List.all_eq_true.mpr fun c hc => hd c (List.all_eq_true.mp h6 c hc),
    h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

/-! ## Soundness -/

section Lemmas

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat} {Sl : List CId}

theorem part_of {ann : IxCC.Src.Relevance.Ann} {name : String} {b : Bool}
    (h : groundCheck p env κ lpsOf ann Sl = true) (hm : (name, b) ∈ checkParts p env κ lpsOf ann Sl) :
    b = true :=
  List.all_eq_true.mp h _ hm

theorem stored_of {c : CId} (h : storedB env κ lpsOf c = true) :
    ∃ ci, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = lpsOf c := by
  unfold storedB at h
  split at h
  · rename_i ci hf
    exact ⟨ci, hf, beq_iff_eq.mp h⟩
  · exact absurd h (by simp)

theorem noCsimp_of {c : CId} (h : noCsimpB p c = true) :
    ∀ g us thm, p.table.resolveOf c ≠ some (.csimp g us thm) := by
  intro g us thm hr
  simp [noCsimpB, hr] at h

theorem noWord_of {c : CId} (h : noWordB p c = true) :
    ∀ w op thm, p.table.resolveOf c ≠ some (.word w op thm) := by
  intro w op thm hr
  simp [noWordB, hr] at h

theorem recClass_of {adm : List RecClass} {c : CId} (h : declOkB p env κ adm c = true) :
    ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? c = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      ∃ k, recClassB p env κ c = some k ∧ k ∈ adm := by
  intro sf kk lvls np nmot nmin ni ind rules ty hd
  unfold declOkB at h
  rw [hd] at h
  simp only at h
  cases hk : recClassB p env κ c with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k =>
    rw [hk] at h
    exact ⟨k, rfl, List.contains_iff_mem.mp h⟩

theorem noQuot_of {adm : List RecClass} {c : CId} (h : declOkB p env κ adm c = true) :
    ∀ qk lvls ty, p.decl? c ≠ some (.quot qk lvls ty) := by
  intro qk lvls ty hd
  simp [declOkB, hd] at h

theorem recStored_of_check {r : CId} (h : recStoredB p env κ lpsOf r = true) :
    RecStored p env κ lpsOf r := by
  unfold recStoredB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty cvr mI rP krules hd hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hmI, hrP⟩, hlps⟩, har⟩, hlen⟩, hall⟩ := h
    subst hmI hrP
    refine ⟨⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, cvr, krules, hd, hf, hlps, har, hlen,
      fun j rl krl hrl hkrl => ?_⟩⟩
    have hmem : (rl, krl) ∈ rules.zip krules :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hrl, hkrl⟩)
    have := hall (rl, krl) hmem
    simp only at this
    exact ⟨this.1.1, this.1.2, termCorr_of_check _ _ this.2⟩
  · exact absurd h (by simp)

theorem eqReflBasis_of_check (h : eqReflBasisB env = true) : EqReflBasis env := by
  unfold eqReflBasisB at h
  split at h
  · rename_i cv hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨cv, hf, h.1, h.2⟩
  · exact absurd h (by simp)

/-- The decider is complete: where the basis holds, it says so (what lets a check that takes the
basis as a hypothesis be replaced by this one). -/
theorem eqReflBasisB_of (h : EqReflBasis env) : eqReflBasisB env = true := by
  obtain ⟨cv, hf, hl, ht⟩ := h
  simp [eqReflBasisB, hf, hl, ht]

theorem eqRecBasis_of_check (h : eqRecBasisB env = true) : EqRecBasis env := by
  unfold eqRecBasisB at h
  split at h
  · rename_i cvr mI rP krl hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hmI, hrP⟩, hty⟩, hc⟩, hrhs⟩ := h
    subst hmI hrP
    exact ⟨cvr, krl, hf, hty, hc, hrhs⟩
  · exact absurd h (by simp)

/-- The decider is complete: where the basis holds, it says so. -/
theorem eqRecBasisB_of (h : EqRecBasis env) : eqRecBasisB env = true := by
  obtain ⟨cvr, krl, hf, hty, hc, hrhs⟩ := h
  simp [eqRecBasisB, hf, hty, hc, hrhs]

theorem recTele_of_check {kr : KKey} (h : recTeleB env kr = true) : RecTele env kr := by
  unfold recTeleB at h
  split at h
  · rename_i cvr mI rP krules hf
    split at h
    · rename_i tbs C hs
      refine ⟨cvr, mI, rP, krules, tbs, C, hf, piSplit_spec rP _ _ _ hs,
        piSplit_length rP _ _ _ hs, fun krl hkrl => ?_⟩
      have h1 := List.all_eq_true.mp h krl hkrl
      split at h1
      · rename_i bs b hl
        obtain ⟨e1, e2⟩ := lamSplit_spec _ _ _ _ hl
        exact ⟨bs, b, e1, e2, of_decide_eq_true h1⟩
      · cases h1
    · cases h
  · cases h

theorem recProg_of_check {r : CId} (h : recProgB p κ Sl r = true) : RecProg p κ (· ∈ Sl) r := by
  unfold recProgB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨hS, hN⟩ := h
    refine ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd,
      fun c hc sf' lv' cidx np' nf ty' hdc => ?_, fun hn => ?_⟩
    · have := List.all_eq_true.mp hS c hc
      simp only [hdc, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨hnp, hcs⟩ := this
      refine ⟨hnp, ?_⟩
      split at hcs
      · rename_i rl hrl
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcs
        exact ⟨rl, hrl, hcs.1, hcs.2⟩
      · cases hcs
    · simp only [hn, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hN
      exact hN
  · cases h

theorem recCtorsRaw_of_check {r : CId} (h : recCtorsRawB p env κ r = true) :
    RecCtorsRaw p env κ r := by
  unfold recCtorsRawB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty cvr mI rP krules hd hf
    split at h
    · rename_i dom body m hpb
      split at h
      · rename_i D ls hD
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨hdom, hall⟩ := h
        refine ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, cvr, mI, rP, krules, dom, body, m,
          ls, hd, hf, hpb, hdom, fun krl hkrl => ?_⟩
        have h1 := hall krl hkrl
        split at h1
        · rename_i cvC np' nF hc
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
          obtain ⟨⟨⟨rfl, hl⟩, hhead⟩, hargs⟩ := h1
          exact ⟨cvC, nF, hc, hl, hhead, hargs⟩
        · cases h1
      · cases h
    · cases h
  · cases h

theorem recFields_of_check {kr : KKey} (h : recFieldsB env kr = true) : RecFields env kr := by
  unfold recFieldsB at h
  split at h
  · rename_i cvr mI rP krules hf
    split at h
    · rename_i dom body m hpb
      split at h
      · rename_i D ls hD
        refine ⟨cvr, mI, rP, krules, dom, body, m, D, ls, hf, hpb, hD, fun krl hkrl => ?_⟩
        have h1 := List.all_eq_true.mp h krl hkrl
        split at h1
        · rename_i cvC np nF hc
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          obtain ⟨⟨⟨⟨rfl, rfl⟩, hcl⟩, hdef⟩, h2⟩ := h1
          split at h2
          · rename_i fbs Cc bs b hps hls
            obtain ⟨e1, e2⟩ := lamSplit_spec _ _ _ _ hls
            exact ⟨cvC, fbs, bs, Cc, b, hc, hcl, hdef, piSplit_spec _ _ _ _ hps,
              piSplit_length _ _ _ _ hps, e1, e2, of_decide_eq_true h2⟩
          · cases h2
        · cases h1
      · cases h
    · cases h
  · cases h

theorem recBodies_of_check {r : CId} (h : recBodiesB p env κ lpsOf r = true) :
    RecBodies p env κ lpsOf r := by
  unfold recBodiesB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty cvr mI rP krules hd hf
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hR, hK⟩ := h
    refine ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, cvr, mI, rP, krules, hd, hf,
      fun rl hrl => ?_, hK⟩
    obtain ⟨h1, h2⟩ := hR rl hrl
    refine ⟨?_, h2⟩
    split at h1
    · rename_i t' ht
      refine ⟨t', ht, fun c => ?_⟩
      cases hm : t'.mentions c
      · rfl
      · have hc := mentions_constsOf hm
        rw [List.isEmpty_iff] at h1
        rw [h1] at hc
        cases hc
    · cases h1
  · cases h

theorem recSites_of_check {r : CId} (h : recSitesB p env κ lpsOf r = true) :
    RecSites p env κ lpsOf r := by
  unfold recSitesB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty cvr mI rP krules hd hf
    split at h
    · rename_i dom body m hpb
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hpw, hall⟩ := h
      refine ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, cvr, mI, rP, krules, dom, body, m,
        hd, hf, hpb, hpw, fun j rl krl hrl hkrl => ?_⟩
      have hmem : (rl, krl) ∈ rules.zip krules :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hrl, hkrl⟩)
      have := hall (rl, krl) hmem
      simpa [List.isEmpty_iff] using this
    · cases h
  · cases h

/-- The `recShape` conjunct gives the checked shape, the `Eq.refl` and `Eq.rec` bases at
`Eq.rec`, and at a flat recursor its rules' telescopes, the program side and its rules'
constructors. -/
theorem recShape_of {c : CId} (h : recShapeB p env κ lpsOf Sl c = true) :
    ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? c = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      RecStored p env κ lpsOf c ∧
        (recClassB p env κ c = some .eqRec → EqReflBasis env ∧ EqRecBasis env) ∧
        (recClassB p env κ c = some .flat →
          RecTele env (κ c) ∧ RecProg p κ (· ∈ Sl) c ∧ RecCtorsRaw p env κ c) := by
  intro sf kk lvls np nmot nmin ni ind rules ty hd
  unfold recShapeB at h
  rw [hd] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h4⟩, -⟩ := h
  refine ⟨recStored_of_check h1, fun hk => ?_, fun hk => ?_⟩
  · rcases h2 with h2 | ⟨h2, h3⟩
    · exact absurd hk h2
    · exact ⟨eqReflBasis_of_check h2, eqRecBasis_of_check h3⟩
  · rcases h4 with h4 | ⟨⟨h4, h5⟩, h6⟩
    · exact absurd hk h4
    · exact ⟨recTele_of_check h4, recProg_of_check h5, recCtorsRaw_of_check h6⟩

/-- The `recShape` conjunct gives, at a recursor of class `noParams` (G3, part E), its rules'
telescopes, the program side, its rules' constructors, its rules' fields, its rule bodies and its
rule bodies' sites typed by the direct route. -/
theorem recShapeNoParams_of {c : CId} (h : recShapeB p env κ lpsOf Sl c = true) :
    ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? c = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      recClassB p env κ c = some .noParams →
        RecTele env (κ c) ∧ RecProg p κ (· ∈ Sl) c ∧ RecCtorsRaw p env κ c ∧ RecFields env (κ c) ∧
          RecBodies p env κ lpsOf c ∧ RecSites p env κ lpsOf c := by
  intro sf kk lvls np nmot nmin ni ind rules ty hd hk
  unfold recShapeB at h
  rw [hd] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨-, h7⟩ := h
  rcases h7 with h7 | ⟨⟨⟨⟨⟨h7, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  · exact absurd hk h7
  · exact ⟨recTele_of_check h7, recProg_of_check h8, recCtorsRaw_of_check h9,
      recFields_of_check h10, recBodies_of_check h11, recSites_of_check h12⟩

theorem prim_of {c : CId} (h : primB p env κ c = true) :
    ∀ op, p.table.resolveOf c = some (.prim op) → κ c = primKey op ∧
      ∃ ci, env.find? (primKey op) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
        op.arity ≤ kPis ci.toConstantVal.type := by
  intro op hr
  simp only [primB, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, h⟩ := h
  refine ⟨hk, ?_⟩
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨ci, hf, h.1, h.2⟩
  · exact absurd h (by simp)

theorem ctor_of {c : CId} (h : ctorB p env κ c = true) :
    ∀ sf lvls ind cidx np nf ty, p.decl? c = some (.ctor sf lvls ind cidx np nf ty) →
      ∃ cv, env.find? (κ c) = some (.ctorInfo cv np nf) ∧ np + nf ≤ kPis cv.type := by
  intro sf lvls ind cidx np nf ty hd
  simp only [ctorB, hd] at h
  split at h
  · rename_i cv np' nf' hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hle⟩ := h
    exact ⟨cv, hf, hle⟩
  · exact absurd h (by simp)

theorem caseRec_of {c : CId} (h : caseRecB p env κ c = true) :
    ∀ r, p.table.resolveOf c = some (.case r) →
      (p.table.recKindOf r = some .ordinary ∨ p.table.recKindOf r = some .empty) ∧
        ∃ ci, env.find? (κ c) = some ci ∧ p.headArity (.cases c) ≤ kPis ci.toConstantVal.type := by
  intro r hr
  simp only [caseRecB, hr, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · split at h1
    · rename_i hk; exact .inl hk
    · rename_i hk; exact .inr hk
    · exact absurd h1 (by simp)
  · split at h2
    · rename_i ci hf; exact ⟨ci, hf, of_decide_eq_true h2⟩
    · exact absurd h2 (by simp)

theorem defn_of {c : CId} (h : defnB p env κ Sl c = true) :
    p.table.resolveOf c = none → ∀ lvls ty v, p.decl? c = some (.defn .defn .safe lvls ty v) →
      (∃ cv val hint, env.find? (κ c) = some (.defnInfo cv val hint)) ∧ ConstsIn (· ∈ Sl) v := by
  intro hr lvls ty v hd
  simp only [defnB, hr, hd, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, constsIn_of_check h2⟩
  split at h1
  · rename_i cv val hint hf; exact ⟨cv, val, hint, hf⟩
  · exact absurd h1 (by simp)

theorem eqnNames_of {c : CId} (h : eqnNamesB p Sl c = true) :
    ∀ thm body, p.table.resolveOf c = some (.eqn thm body) → ConstsIn (· ∈ Sl) body := by
  intro thm body hr
  simp only [eqnNamesB, hr] at h
  exact constsIn_of_check h

theorem proj_of {s : CId} (h : projB p env κ Sl s = true) :
    ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) →
      ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → ∀ i, i < nf →
        ∃ entry, env.findProj? (κ s) i = some entry ∧ entry.ctor = κ c := by
  intro sf lvls np ni ty c hd cvC np' nf hf i hi
  simp only [projB, hd, hf, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1 i (List.mem_range.mpr hi)
  split at hall
  · rename_i e he; exact ⟨e, he, of_decide_eq_true hall⟩
  · exact absurd hall (by simp)

theorem projSort_of {s : CId} (h : projB p env κ Sl s = true) :
    ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) → c ∈ Sl →
      ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → 0 < nf →
        NeverProp env (κ s) := by
  intro sf lvls np ni ty c hd hc cvC np' nf hf hnf
  simp only [projB, hd, hf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h.2 with (h0 | hn) | hp
  · omega
  · exact absurd hc hn
  · exact neverProp_of_check hp

theorem boolPin_of {b : Bool} (h : boolPinB p env κ Sl b = true) :
    ∀ c, (if b then p.known.boolTrue else p.known.boolFalse) = some c →
      c ∈ Sl ∧ κ c = (if b then boolTrueName else boolFalseName) ∧
        ∃ cv, env.find? (κ c) = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] := by
  intro c hc
  simp only [boolPinB, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i cv hf; exact ⟨cv, hf, beq_iff_eq.mp h3⟩
  · exact absurd h3 (by simp)

theorem natBasis_of (h : natBasisB env = true) : NatBasis env := by
  simp only [natBasisB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at h1
    · rename_i ci hf; exact ⟨ci, hf, beq_iff_eq.mp h1⟩
    · exact absurd h1 (by simp)
  · split at h2
    · rename_i cv hf
      obtain ⟨a, b, c⟩ := of_decide_eq_true h2
      exact ⟨cv, hf, a, b, c⟩
    · exact absurd h2 (by simp)
  · split at h3
    · rename_i cv hf
      obtain ⟨a, b, c⟩ := of_decide_eq_true h3
      exact ⟨cv, hf, a, b, c⟩
    · exact absurd h3 (by simp)

/-- **The check is sound**: it establishes every fact `GroundFacts` names. -/
theorem groundFacts_of_check {ann : IxCC.Src.Relevance.Ann}
    (h : groundCheck p env κ lpsOf ann Sl = true) :
    GroundFacts p env κ lpsOf ann (· ∈ Sl) := by
  have P : ∀ name b, (name, b) ∈ checkParts p env κ lpsOf ann Sl → b = true :=
    fun _ _ hm => part_of h hm
  have all : ∀ {f : CId → Bool} (name : String), (name, Sl.all f) ∈ checkParts p env κ lpsOf ann Sl →
      ∀ c, c ∈ Sl → f c = true :=
    fun name hm c hc => List.all_eq_true.mp (P name _ hm) c hc
  have hE : EqBasis env := eqBasis_of_check (P "eqBasis" (eqBasisB env) (by simp [checkParts, checkPartsWith]))
  have hpins := P "pins" (pinsB p env κ Sl) (by simp [checkParts, checkPartsWith])
  simp only [pinsB, Bool.and_eq_true] at hpins
  obtain ⟨⟨⟨hz, hs⟩, hbt⟩, hbf⟩ := hpins
  have hfaith : Faith p env κ lpsOf (· ∈ Sl) := by
    refine ⟨fun c hc => stored_of (all "stored" (by simp [checkParts, checkPartsWith]) c hc),
      fun c hc => beq_iff_eq.mp (all (f := lvlsB p lpsOf) "lvls" (by simp [checkParts, checkPartsWith]) c hc),
      fun c hc => of_decide_eq_true (all (f := nodupB lpsOf) "nodup" (by simp [checkParts, checkPartsWith]) c hc),
      fun c g us thm hc => noCsimp_of (all "noCsimp" (by simp [checkParts, checkPartsWith]) c hc) g us thm,
      fun c w op thm hc => noWord_of (all "noWord" (by simp [checkParts, checkPartsWith]) c hc) w op thm,
      { cls := fun r hr sf kk lvls np nmot nmin ni ind rules ty hd =>
          recClass_of (all (f := declOkB p env κ admittedClasses) "declOk"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd
        stored := fun r hr sf kk lvls np nmot nmin ni ind rules ty hd =>
          (recShape_of (all (f := recShapeB p env κ lpsOf Sl) "recShape"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd).1
        eqRefl := fun r hr hk => by
          obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
          exact ((recShape_of (all (f := recShapeB p env κ lpsOf Sl) "recShape"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd).2.1
            hk).1
        eqRec := fun r hr hk => by
          obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
          exact ⟨hE, ((recShape_of (all (f := recShapeB p env κ lpsOf Sl) "recShape"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd).2.1
            hk).2⟩
        flat := fun r hr hk => by
          obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
          exact (recShape_of (all (f := recShapeB p env κ lpsOf Sl) "recShape"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd).2.2
            hk
        noParams := fun r hr hk => by
          obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
          exact recShapeNoParams_of (all (f := recShapeB p env κ lpsOf Sl) "recShape"
            (by simp [checkParts, checkPartsWith]) r hr) sf kk lvls np nmot nmin ni ind rules ty hd
            hk },
      fun c hc => noQuot_of (all (f := declOkB p env κ admittedClasses) "declOk"
        (by simp [checkParts, checkPartsWith]) c hc),
      fun c hc => by
        have := all (f := fun c => p.table.isOpaqueByValue c == false) "notOpaque"
          (by simp [checkParts, checkPartsWith]) c hc
        simpa using this,
      fun c op hc => prim_of (all "prim" (by simp [checkParts, checkPartsWith]) c hc) op,
      fun c hc => ctor_of (all "ctor" (by simp [checkParts, checkPartsWith]) c hc),
      fun c r hc hr => caseRec_of (all "caseRec" (by simp [checkParts, checkPartsWith]) c hc) r hr,
      fun c hc => defn_of (all "defn" (by simp [checkParts, checkPartsWith]) c hc),
      fun c thm body hc hr => eqnNames_of (all "eqnNames" (by simp [checkParts, checkPartsWith]) c hc) thm body hr,
      fun s hc => proj_of (all (f := projB p env κ Sl) "proj" (by simp [checkParts, checkPartsWith]) s hc),
      fun s hc => projSort_of (all (f := projB p env κ Sl) "proj" (by simp [checkParts, checkPartsWith]) s hc),
      fun c hc => by simp only [hc, decide_eq_true_eq] at hz; exact hz,
      fun c hc => by simp only [hc, decide_eq_true_eq] at hs; exact hs, ?_⟩
    intro b c hbc
    cases b
    · exact boolPin_of hbf c hbc
    · exact boolPin_of hbt c hbc
  -- the `eqn` entries
  have heqn : ∀ c thm body, c ∈ Sl → p.table.resolveOf c = some (.eqn thm body) →
      ∃ d, eqnData? env (κ c) (κ thm) = some d ∧ EqnShape env κ c thm d ∧
        TermCorrS κ (lpsOf c) [] body d.body ∧ bvarsLt 0 d.body = true := by
    intro c thm body hc hr
    have h1 := all (f := eqnShapeOkB p env κ) "eqnShape" (by simp [checkParts, checkPartsWith]) c hc
    have h2 := all (f := eqnCorrB p env κ lpsOf) "eqnCorr" (by simp [checkParts, checkPartsWith]) c hc
    have h3 := all (f := eqnClosedB p env κ) "eqnClosed" (by simp [checkParts, checkPartsWith]) c hc
    simp only [eqnShapeOkB, eqnCorrB, eqnClosedB, hr] at h1 h2 h3
    split at h1
    · rename_i d hd
      rw [hd] at h2 h3
      exact ⟨d, hd, eqnShape_of_check hE h1, termCorrS_of_check _ _ _ h2, h3⟩
    · exact absurd h1 (by simp)
  refine ⟨hfaith, natBasis_of (P "natBasis" (natBasisB env) (by simp [checkParts, checkPartsWith])), ?_, ?_, ?_,
    okClosed_of_check (P "okClosed" (okClosedB p ann Sl) (by simp [checkParts, checkPartsWith]))⟩
  · intro c thm body hc hr
    obtain ⟨d, _, hsh, hcorr, _⟩ := heqn c thm body hc hr
    exact ⟨⟨d, hsh⟩, fun d' hsh' => eqnShape_body hsh hsh' ▸ hcorr⟩
  · intro c lvls ty v cv val hint hc hr hd hf
    have h1 := all (f := valueCorrB p env κ lpsOf) "valueCorr" (by simp [checkParts, checkPartsWith]) c hc
    simp only [valueCorrB, hr, hd, hf] at h1
    exact termCorrS_of_check _ _ _ h1
  · intro c t e hc hrp
    cases hrp with
    | value hr hd hf =>
      have h1 := all (f := valueClosedB p env κ) "valueClosed" (by simp [checkParts, checkPartsWith]) c hc
      simp only [valueClosedB, hr, hd, hf] at h1
      exact h1
    | eqn hr hsh =>
      obtain ⟨d, _, hsh', _, hcl⟩ := heqn c _ _ hc hr
      rw [eqnShape_body hsh hsh']
      exact hcl

/-- **The check is sound for the `case` entries**: it establishes `CaseFacts`. -/
theorem caseFacts_of_check {ann : IxCC.Src.Relevance.Ann}
    (h : groundCheck p env κ lpsOf ann Sl = true) : CaseFacts p env κ (· ∈ Sl) := by
  intro c r hc hr hk
  have h1 := List.all_eq_true.mp (part_of (name := "caseShape") (b := Sl.all (caseShapeB p env κ)) h (by simp [checkParts, checkPartsWith])) c hc
  have h2 := List.all_eq_true.mp (part_of (name := "caseProg") (b := Sl.all (caseProgOkB p env κ Sl)) h (by simp [checkParts, checkPartsWith])) c hc
  simp only [caseShapeB, caseProgOkB, hr, hk] at h1 h2
  split at h1
  · rename_i sh hsh
    rw [hsh] at h2
    exact ⟨sh, caseStored_of_check h1, caseProg_of_check h2⟩
  · exact absurd h1 (by simp)

end Lemmas

end IxCC.Grounding
