module

public import IxC.Kernel.Model.Install

public section

/-!
# Theorem values in the fold invariant (lane l5, `thm_val`)

S2's rule N1 (`Red.deltaThm`) unfolds a theorem to its stored value; its
soundness needs the model to equate the value's reading with the theorem's leaf
(`thm_val`, `plans/ixvmc/s2/RULES-GAP.md` section 3). `EnvModelM` keeps no such
equation: the kernel stores a theorem's raw value (`DeclThmRun`), which need not
read. The restated records store the annotated one (`DeclThmRunJ` at a package
with `thmValue v v' = v'`, decision D11), and the restated fold carries

* `ThmValOk mp`: every stored theorem's value resolves in the environment and
  reads, at every assignment, to the theorem's own leaf;

beside `EnvModelM`. A step keeps it when the new model's leaves are the old ones
with one fresh constant added (`ModelExt`, the reflexive-transitive closure of
such conses): the old values' readings survive the cons
(`denoteMeta_cons_mono`), and a new theorem brings its own reading. The value
kinds and the pinned basis blocks expose that relation (`harvest*J`,
`declBasisPB_*`), so the restated dispatch (`Model/FoldJ.lean`) preserves
`ThmValOk`.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **Stored theorem values read to their leaves.** -/
structure ThmValOk {env : Env md} (mp : EnvModelM V μ env) : Prop where
  /-- every stored theorem's value resolves in the environment -/
  resolve : ∀ (cv : ConstantVal md) (v : Expr md),
    ConstantInfo.thmInfo cv v ∈ env.consts → v.constsResolve env = true
  /-- and reads, at every assignment, to the theorem's own leaf -/
  reads : ∀ (ψ : LevelParam → Nat) (cv : ConstantVal md) (v : Expr md),
    ConstantInfo.thmInfo cv v ∈ env.consts →
    denoteMeta mp.base2.acval env ψ 0 v = some (mp.base2.acval cv.name ψ)

/-- The empty environment stores no theorem. -/
theorem ThmValOk.empty (mp : EnvModelM V μ (Env.empty : Env md)) : ThmValOk mp where
  resolve := fun _ _ h => absurd h List.not_mem_nil
  reads := fun _ _ _ h => absurd h List.not_mem_nil

/-- **One fresh cons keeps `ThmValOk`**: the new model's leaves are the old
ones with `A` at the head; every stored theorem's value crosses the head; a
theorem head brings its value's reading at `A`. -/
theorem ThmValOk.cons {env : Env md} {mp : EnvModelM V μ env} (h : ThmValOk mp)
    {c₀ : ConstantInfo md} {A : (LevelParam → Nat) → AnnotTerm}
    {mp₂ : EnvModelM V μ ⟨c₀ :: env.consts⟩}
    (hfresh : env.find? c₀.name = none)
    (hcross : ∀ (cv : ConstantVal md) (v : Expr md),
      ConstantInfo.thmInfo cv v ∈ env.consts → ConsCrossAt c₀ v)
    (hhead : ∀ (cv : ConstantVal md) (v : Expr md), c₀ = .thmInfo cv v →
      v.constsResolve env = true ∧
        ∀ ψ, denoteMeta mp.base2.acval env ψ 0 v = some (A ψ))
    (hac : mp₂.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    ThmValOk mp₂ where
  resolve := by
    intro cv v hmem
    rcases List.mem_cons.mp hmem with h0 | h0
    · exact Expr.constsResolve_mono (hhead cv v h0.symm).1
    · exact Expr.constsResolve_mono (h.resolve cv v h0)
  reads := by
    intro ψ cv v hmem
    have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
      have h0 := hfresh
      rw [Ix.Kernel.Env.find?, List.find?_eq_none] at h0
      intro c hc hn
      exact h0 c hc (by simp [hn])
    rw [hac]
    rcases List.mem_cons.mp hmem with h0 | h0
    · obtain ⟨hr, hrd⟩ := hhead cv v h0.symm
      subst h0
      have hleaf : acvalWith mp.base2.acval (ConstantInfo.thmInfo cv v).name A cv.name = A :=
        acvalWith_self
      rw [hleaf]
      exact denoteMeta_cons_mono hfresh
        (ConsCrossAt.ofNtc (fun _ heq => nomatch heq)) ψ 0
        (constsBound_of_constsResolve _ hr) (hrd ψ)
    · rw [acvalWith_ne (show cv.name ≠ c₀.name from hne _ h0)]
      exact denoteMeta_cons_mono hfresh (hcross cv v h0) ψ 0
        (constsBound_of_constsResolve _ (h.resolve cv v h0)) (h.reads ψ cv v h0)

/-- **Model extension by fresh conses**: `mp₂`'s leaves are `mp₁`'s with
fresh constants added one at a time, each satisfying `ThmValOk.cons`'s side
conditions, and with steps that keep every leaf and change the environment
only where no stored theorem reads it (`swap`: a recursor group's rule lists
attached to its provisioned entries, which stores the same names, the same
theorems and reads every term the same). -/
inductive ModelExt {env₁ : Env md} (mp₁ : EnvModelM V μ env₁) :
    {env₂ : Env md} → EnvModelM V μ env₂ → Prop where
  | refl : ModelExt mp₁ mp₁
  | step {env₂ : Env md} {mp₂ : EnvModelM V μ env₂}
      {c₀ : ConstantInfo md} {A : (LevelParam → Nat) → AnnotTerm}
      {mp₃ : EnvModelM V μ ⟨c₀ :: env₂.consts⟩} :
      ModelExt mp₁ mp₂ →
      env₂.find? c₀.name = none →
      (∀ (cv : ConstantVal md) (v : Expr md),
        ConstantInfo.thmInfo cv v ∈ env₂.consts → ConsCrossAt c₀ v) →
      (∀ (cv : ConstantVal md) (v : Expr md), c₀ = .thmInfo cv v →
        v.constsResolve env₂ = true ∧
          ∀ ψ, denoteMeta mp₂.base2.acval env₂ ψ 0 v = some (A ψ)) →
      mp₃.base2.acval = acvalWith mp₂.base2.acval c₀.name A →
      ModelExt mp₁ mp₃
  | swap {env₂ env₃ : Env md} {mp₂ : EnvModelM V μ env₂} {mp₃ : EnvModelM V μ env₃} :
      ModelExt mp₁ mp₂ →
      (∀ n, (env₂.find? n).isSome = true → (env₃.find? n).isSome = true) →
      (∀ (cv : ConstantVal md) (v : Expr md),
        ConstantInfo.thmInfo cv v ∈ env₃.consts → ConstantInfo.thmInfo cv v ∈ env₂.consts) →
      (∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md),
        denoteMeta mp₂.base2.acval env₂ ψ d e = denoteMeta mp₂.base2.acval env₃ ψ d e) →
      mp₃.base2.acval = mp₂.base2.acval →
      ModelExt mp₁ mp₃

/-- **`ThmValOk` along a model extension.** -/
theorem ThmValOk.of_ext {env₁ env₂ : Env md} {mp₁ : EnvModelM V μ env₁}
    {mp₂ : EnvModelM V μ env₂} (hext : ModelExt mp₁ mp₂) (h : ThmValOk mp₁) :
    ThmValOk mp₂ := by
  induction hext with
  | refl => exact h
  | step _ hfresh hcross hhead hac ih => exact ThmValOk.cons ih hfresh hcross hhead hac
  | swap _ hsome hthms hden hac ih =>
    exact ⟨fun cv v hmem => Expr.constsResolve_of_find hsome (ih.resolve cv v (hthms cv v hmem)),
      fun ψ cv v hmem => by
        rw [hac, ← hden ψ 0 v]
        exact ih.reads ψ cv v (hthms cv v hmem)⟩

/-- Extensions compose. -/
theorem ModelExt.trans {env₁ env₂ env₃ : Env md} {mp₁ : EnvModelM V μ env₁}
    {mp₂ : EnvModelM V μ env₂} {mp₃ : EnvModelM V μ env₃}
    (h₁ : ModelExt mp₁ mp₂) (h₂ : ModelExt mp₂ mp₃) : ModelExt mp₁ mp₃ := by
  induction h₂ with
  | refl => exact h₁
  | step _ hfresh hcross hhead hac ih => exact .step ih hfresh hcross hhead hac
  | swap _ hsome hthms hden hac ih => exact .swap ih hsome hthms hden hac

/-- **A plain cons extends**: a fresh head that is neither a projection table nor
a theorem (every pinned basis constant, a definition, an opaque, an axiom). -/
theorem ModelExt.plain {env₁ env₂ : Env md} {mp₁ : EnvModelM V μ env₁}
    {mp₂ : EnvModelM V μ env₂} (h : ModelExt mp₁ mp₂)
    {c₀ : ConstantInfo md} {A : (LevelParam → Nat) → AnnotTerm}
    {mp₃ : EnvModelM V μ ⟨c₀ :: env₂.consts⟩}
    (hac : mp₃.base2.acval = acvalWith mp₂.base2.acval c₀.name A)
    (hfresh : env₂.find? c₀.name = none)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hnthm : ∀ (cv : ConstantVal md) (v : Expr md), c₀ ≠ .thmInfo cv v := by
      intro _ _ h; exact nomatch h) :
    ModelExt mp₁ mp₃ :=
  .step h hfresh (fun _ _ _ => ConsCrossAt.ofNtc hntc)
    (fun cv v heq => absurd heq (hnthm cv v)) hac

/-- **A cons step's new model, exposed**: some leaf `A` at the head, the old
leaves elsewhere. What the basis helpers return. -/
abbrev ConsLeaf {env : Env md} (mp : EnvModelM V μ env) (c₀ : ConstantInfo md) : Prop :=
  ∃ (A : (LevelParam → Nat) → AnnotTerm) (mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩),
    mp'.base2.acval = acvalWith mp.base2.acval c₀.name A

/-- The cons lemmas' exposed form, with its leaf existential. -/
theorem consLeaf_of {env : Env md} {mp : EnvModelM V μ env} {c₀ : ConstantInfo md}
    {A : (LevelParam → Nat) → AnnotTerm}
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    ConsLeaf mp c₀ :=
  ⟨A, h⟩

/-- **A plain cons, from the start**: the cons lemmas' exposed form, at a head
that is neither a projection table nor a theorem, is a one-step extension. -/
theorem plainExt {env : Env md} (mp : EnvModelM V μ env) {c₀ : ConstantInfo md}
    {A : (LevelParam → Nat) → AnnotTerm}
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hnthm : ∀ (cv : ConstantVal md) (v : Expr md), c₀ ≠ .thmInfo cv v := by
      intro _ _ h; exact nomatch h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩, ModelExt mp mp' :=
  let ⟨mp', hac⟩ := h
  ⟨mp', (ModelExt.refl (mp₁ := mp)).plain hac hfresh hntc hnthm⟩

/-- The cons lemmas' exposed form, with a fact about its leaf. -/
theorem leafWith {env : Env md} {mp : EnvModelM V μ env} {c₀ : ConstantInfo md}
    {A : (LevelParam → Nat) → AnnotTerm}
    {P : ((LevelParam → Nat) → AnnotTerm) → Prop}
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A) (hp : P A) :
    ∃ (A' : (LevelParam → Nat) → AnnotTerm) (mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩),
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A' ∧ P A' :=
  let ⟨mp', hac⟩ := h
  ⟨A, mp', hac, hp⟩

end Ix.Kernel.Model
