module

public import ConLeche.Model.Inductives.StructFrame
public import ConLeche.Model.Capstone
import ConLeche.Model.Tiers
public section

/-!
# The direct structure's stage runs, as rows (task #175 W4c, P3 module 3, part 2)

The claims a P carrier answers at one fuel and assignment
(`ClaimsAt`), the three row shapes the direct install reads off them
(inference, sort, definitional equality — each at a context), and
**the opened type** (`opened_of`): a closed, graded type opened at
its own variables yields its `.pi` context, the per-binder readings,
the hereditary gradings and the `CtxOk` correspondences at every
depth — everything a stage's frame walk consumes, in one record.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche ConLeche.Semantics ConLeche.Verify SetTheory ConLeche.SetModel
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The claims at one fuel -/

/-- The claims a P carrier answers at fuel `F` and assignment `φ`. -/
structure ClaimsAt (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (F : Nat) : Prop where
  whnf : WhnfClaim μ m φ F
  defeq : DefEqClaim μ m φ F
  infer : InferClaim μ m φ F
  reads : InferReads m μ φ F
  sort : SortSemAt m μ φ F

/-- A P carrier answers them (the sealed capstone). -/
theorem claimsAt_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (φ : Name → Nat) (F : Nat) : ClaimsAt μ mp.base2 φ F :=
  have h := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp φ) F
  have hr : InferReads mp.base2 μ φ F :=
    inferReads_of hμ (Rules.RulesInputs.ofSem mp φ)
  ⟨h.2.1, h.2.2.1, h.2.2.2, hr, sortSemAt_of_claims h.2.1 h.2.2.2 hr⟩

namespace ClaimsAt

variable {m : EnvModel V env} {F : Nat}

/-- An inference run at a context: the type reads, both readings are
graded, and the subject inhabits the type. -/
theorem inferRow (hc : ClaimsAt μ m φ F) {d : Nat} {e t : Expr}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : inferTypeCore μ env F d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ta, hta⟩ := hc.reads hi hws hb hL hC hea
  obtain ⟨h1, h2, h3⟩ := hc.infer hi hws hb hL hC hea hta
  exact ⟨ta, hta, h1, h2, h3⟩

/-- An inference run whose type is a sort: the subject is graded and
lands in that universe. -/
theorem sortRow (hc : ClaimsAt μ m φ F) {d : Nat} {e t : Expr} {u : Level}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : inferTypeCore μ env F d e = .ok t)
    (hens : ensureSortCore μ env F d t = .ok u)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∀ ρ : Nat → V, Sat V Δ ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) :=
  hc.sort hC hws hb hL hi (ConLeche.ensureSortCore_inv hens) hea

/-- A definitional-equality run at a context: the readings interpret
alike. -/
theorem defEqRow (hc : ClaimsAt μ m φ F) {d : Nat} {a b : Expr}
    {Δ : List AnnotTerm} {aa ba : AnnotTerm}
    (h : ConLeche.isDefEqCore μ env F d a b = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOk m φ d Δ a) (hCb : CtxOk m φ d Δ b)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hbA : denoteMeta m.acval env φ d b = some ba)
    (hoka : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ aa)
    (hokb : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ba) :
    ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ aa = interp V ρ ba :=
  hc.defeq h hwa hba hLa hwb hbb hLb hCa hCb haa hbA hoka hokb

end ClaimsAt

/-! ## The opened type -/

/-- **The opened type record**: a closed, bounded type with a graded
reading, opened at its own variables. -/
structure Opened {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (k : Nat) (e : Expr) (fvs : List Expr) (o : Expr)
    (Γ : List AnnotTerm) (R : AnnotTerm) : Prop where
  /-- the context has one entry per binder -/
  len : Γ.length = k
  /-- the opened body reads to the core at depth `k` -/
  body : denoteMeta m.acval env φ k o = some R
  /-- each variable's annotation reads to its entry at its own depth -/
  doms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
    denoteMeta m.acval env φ i (Expr.fvarTypeD x)
      = some (Γ.getD (k - 1 - i) default)
  /-- the entries are graded under the earlier ones -/
  okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
    WellDenotedV V ρ (Γ.getD (k - 1 - i) default)
  /-- the core is graded under all of them -/
  okR : ∀ ρ : Nat → V, Sat V Γ ρ → WellDenotedV V ρ R
  /-- the variables are indexed by position, annotated at their own
  depth by bounded, leaf-bounded terms over the earlier variables -/
  var : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
    (∃ ty, x = Expr.fvar i ty) ∧
    Expr.WScoped i (Expr.fvarTypeD x) ∧
    (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (Expr.fvarTypeD x) ∧
    ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs
  /-- the opened body is scoped at `k` over the variables -/
  bodyScoped : Expr.WScoped k o ∧ o.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded o ∧
    ∀ l ∈ o.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs
  /-- any term over the variables correlates with the context at its
  depth -/
  ctx : ∀ {i : Nat}, i ≤ k → ∀ {x : Expr}, Expr.WScoped i x →
    (∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
    CtxOk m φ i (Γ.drop (k - i)) x

/-- The opened type record, from the opening, the closedness and the
reading's grading. -/
theorem opened_of {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    {T : AnnotTerm} (hT : denoteMeta m.acval env φ 0 e = some T)
    (hokT : ∀ ρ : Nat → V, WellDenotedV V ρ T) :
    ∃ (Γ : List AnnotTerm) (R : AnnotTerm),
      PiTeleAV k T Γ R ∧ Opened m φ k e fvs o Γ R := by
  obtain ⟨Γ, R, htele, hbody, hdoms⟩ := openPisAtFvars_denotePTele k hop hT
  have hlen : Γ.length = k := htele.length
  have hidx := openPisAtFvars_index k e 0 hop
  have hlenF : fvs.length = k := openPisAtFvars_length k hop
  obtain ⟨hwsF, hwsO⟩ := openPisAtFvars_WScoped k e 0 hop
    (Expr.WScoped.of_not_hasFvar hcl)
  obtain ⟨hbO, hbF⟩ := openPisAtFvars_bounded k hop hb
  have hleaves := openPisAtFvars_leaves k hop
  have hnil : e.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl
  -- a leaf reachable from the opening is an opener
  have hopener : ∀ l, (l ∈ o.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases hleaves l hl with h | h
    · rw [hnil] at h; exact absurd h List.not_mem_nil
    · exact h
  -- an opener's annotation is bounded and leaf-bounded
  have hLB : ∀ y ∈ fvs, Expr.LeavesBounded (Expr.fvarTypeD y) := by
    intro y hy l hl
    have hmem : Expr.fvar l.1 l.2 ∈ fvs := by
      refine hopener l (Or.inr ⟨y, hy, ?_⟩)
      obtain ⟨p, hp⟩ := List.getElem?_of_mem hy
      obtain ⟨ty, rfl⟩ := hidx p y hp
      simp only [Expr.fvarTypeD] at hl
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    have := hbF _ hmem
    simpa [Expr.fvarTypeD] using this
  obtain ⟨hgΓ, hgR⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hokT ρ)
  simp only [List.append_nil] at hgΓ hgR
  refine ⟨Γ, R, htele, ⟨hlen, by simpa using hbody, fun i x hx => by
    simpa using hdoms i x hx, hgΓ, hgR, ?_, ?_, ?_⟩⟩
  · intro i x hx
    have hik : i < k := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      omega
    obtain ⟨ty, rfl⟩ := hidx i x hx
    rw [Nat.zero_add] at *
    have hw := hwsF _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped] at hw
    refine ⟨⟨ty, rfl⟩, hw.2, ?_, hLB _ (List.mem_of_getElem? hx), ?_⟩
    · simpa [Expr.fvarTypeD] using hbF _ (List.mem_of_getElem? hx)
    · intro l hl
      refine hopener l (Or.inr ⟨_, List.mem_of_getElem? hx, ?_⟩)
      simp only [Expr.fvarTypeD] at hl
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
  · refine ⟨by simpa using hwsO, hbO, ?_, fun l hl => hopener l (Or.inl hl)⟩
    intro l hl
    have hmem := hopener l (Or.inl hl)
    have := hbF _ hmem
    simpa [Expr.fvarTypeD] using this
  · intro i hik x hwx hleaf
    exact ctxOk_opened hop hcl hlen (fun i x hx => by simpa using hdoms i x hx)
      hgΓ hik hwx hleaf

end ConLeche.Model
