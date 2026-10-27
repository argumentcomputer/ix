import Ix.Cert.Composition
import Ix.Cert.StepLaws
import Ix.Cert.ConversionValues

/-! # Strong models satisfy the step laws

A strong model of an environment (`Ix.Kernel.Cached.StrongModel`) satisfies the
step-level recursor rules and capability laws of that environment
(`StepRecRuleLaws`, `StepCapabilityLaws`) at its own public values. The proof has four steps:

* **Each step is a rules-tier derivation.** An ι or projection step is a
  reduction (`Rules.Red.iota`, `Rules.Red.proj`). A structure-η or unit-like step
  is a conversion (`Rules.DefEq.structEta`, `Rules.DefEq.structUnit`).
* **Typed closed terms read graded.** A closed term the rules tier types at the
  full grade has an internal reading (`infer_reads`), and full-grade inference
  grades it (`Model.Rules.infer_sound`).
* **The soundness of derivations gives equal readings.** For a reduction, the
  reduct also reads graded and interprets alike (`Model.Rules.red_sound`). For a
  conversion, both sides interpret alike (`Model.Rules.defeq_sound`).
* **A graded reading is the public denotation** (`ConversionValues.reading_denotes`).
  So both sides denote, and they denote the same set (`DenoteSame`).

The renamed form used for the unchanged-closure case is in
`Ix.Cert.UnchangedStepLaws`. -/

namespace Ix.Cert.StrongStepLaws

open Ix.Kernel Ix.Kernel.Rules Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame Graded)

universe w

variable {md : Mode}

/-! ## Typed terms read -/

/-- **A term the rules tier types at the full grade reads.** The reading
(`denoteMeta`) fails only at an unresolved constant or a constant at the wrong
number of levels, a `let`, a projection without a table and no pair reading, an
unsupported literal, or a form with no reading. A full-grade typing excludes each
of these: it resolves every constant at its arity, types every projection
through its table, types every literal under its support, and checks every
argument (the io grade's unchecked application, `Infer.appSkip`, does not occur). -/
theorem infer_reads {env : Env md} (acval : Key md → (LevelParam → Nat) → AnnotTerm)
    (φ : LevelParam → Nat) :
    ∀ {g : Grade} {d : Nat} {e t : Ix.Kernel.Expr md}, Infer env g d e t → g = .full →
      ∃ ea, denoteMeta acval env φ d e = some ea
  | _, _, _, _, .sort, _ => ⟨_, by rw [denoteMeta]⟩
  | _, _, _, _, .fvar _, _ => ⟨_, by rw [denoteMeta]⟩
  | _, _, _, _, .const hf _ hus, _ => ⟨_, by rw [denoteMeta, hf]; exact ite_eq_left hus⟩
  | _, _, _, _, .natLit h, _ => ⟨_, by rw [denoteMeta]; exact ite_eq_left h⟩
  | _, _, _, _, .strLit h, _ => ⟨_, by rw [denoteMeta]; exact ite_eq_left h⟩
  | _, _, _, _, .forallE hs _ hbs _ _, hg => by
    obtain ⟨ta, hta⟩ := infer_reads acval φ hs hg
    obtain ⟨ba, hba⟩ := infer_reads acval φ hbs hg
    exact ⟨_, by rw [denoteMeta, hta, hba]; rfl⟩
  | _, _, _, _, .lam hs _ hbt _ _ _ _, hg => by
    obtain ⟨ta, hta⟩ := infer_reads acval φ (hs hg) rfl
    obtain ⟨ba, hba⟩ := infer_reads acval φ hbt hg
    exact ⟨_, by rw [denoteMeta, hta, hba]; rfl⟩
  | _, _, _, _, .app htf _ hta _, hg => by
    obtain ⟨fa, hfa⟩ := infer_reads acval φ htf hg
    obtain ⟨aa, haa⟩ := infer_reads acval φ hta hg
    exact ⟨_, by rw [denoteMeta, hfa, haa]; rfl⟩
  | _, _, _, _, .appSkip _ _ _, hg => nomatch hg
  | _, _, _, _, .proj htpe _ _ hent _ _ _, hg => by
    obtain ⟨ea, hea⟩ := infer_reads acval φ htpe hg
    exact ⟨_, by rw [denoteMeta, hea, hent]; rfl⟩

variable {V : Type w} [SetTheory V] {env : Env md}

/-- A closed term is framed at depth 0. -/
theorem _root_.Ix.Cert.TypedClosed.frame {e : Ix.Kernel.Expr md} (h : TypedClosed env e) : Frame 0 e :=
  ConversionValues.frame_of_syntax h.1 h.2.1

/-- **A closed, well-typed term reads graded** in a strong model. -/
theorem _root_.Ix.Cert.TypedClosed.graded (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {e : Ix.Kernel.Expr md} (h : TypedClosed env e) :
    ∃ ea, denoteMeta M.internal.base2.acval env φ 0 e = some ea ∧ Graded V [] ea := by
  obtain ⟨t, ht⟩ := h.2.2
  obtain ⟨ea, read⟩ := infer_reads M.internal.base2.acval φ ht rfl
  have typed := Model.Rules.infer_sound (Model.Rules.RulesInputs.ofSem M.internal φ) ht
  obtain ⟨_, _, _, _, graded, _, _⟩ :=
    typed h.frame (ConversionValues.frame_context M φ h.frame) read
  exact ⟨ea, read, graded⟩

/-! ## Derivations from typed terms denote one set -/

/-- **A reduction of a closed, well-typed term keeps its denotation**: both
sides denote, and denote the same set. -/
theorem red_denoteSame (M : Cached.StrongModel V env) {e e' : Ix.Kernel.Expr md}
    (ht : TypedClosed env e) (hr : Red env 0 e e') : DenoteSame M.model.cval env e e' := by
  intro φ ρ
  obtain ⟨ea, read, graded⟩ := ht.graded M φ
  obtain ⟨frame', -, ea', read', graded', heq⟩ :=
    Model.Rules.red_sound (Model.Rules.RulesInputs.ofSem M.internal φ) hr ht.frame
      (ConversionValues.frame_context M φ ht.frame) read graded
  refine ⟨interp V ρ ea, ConversionValues.reading_denotes M ht.frame read graded ρ, ?_⟩
  rw [heq ρ (Sat_nil V ρ)]
  exact ConversionValues.reading_denotes M frame' read' graded' ρ

/-- **A conversion between closed, well-typed terms is one denotation**: both
sides denote, and denote the same set. -/
theorem defeq_denoteSame (M : Cached.StrongModel V env) {a b : Ix.Kernel.Expr md}
    (ha : TypedClosed env a) (hb : TypedClosed env b) (h : DefEq env 0 a b) :
    DenoteSame M.model.cval env a b := by
  intro φ ρ
  obtain ⟨aa, readA, gradeA⟩ := ha.graded M φ
  obtain ⟨ba, readB, gradeB⟩ := hb.graded M φ
  have eq := Model.Rules.defeq_sound (Model.Rules.RulesInputs.ofSem M.internal φ) h ha.frame
    hb.frame (ConversionValues.frame_context M φ ha.frame)
    (ConversionValues.frame_context M φ hb.frame) readA readB gradeA gradeB ρ (Sat_nil V ρ)
  refine ⟨interp V ρ aa, ConversionValues.reading_denotes M ha.frame readA gradeA ρ, ?_⟩
  rw [eq]
  exact ConversionValues.reading_denotes M hb.frame readB gradeB ρ

/-- Two terms that denote one set denote alike. -/
theorem _root_.Ix.Cert.DenoteSame.denoteAlike {cval : Key md → (LevelParam → Nat) → V} {a b : Ix.Kernel.Expr md}
    (h : DenoteSame cval env a b) : DenoteAlike cval env a b := by
  intro φ ρ v v' hv hv'
  obtain ⟨X, ha, hb⟩ := h φ ρ
  rw [Denotes_functional hv ha, Denotes_functional hv' hb]

/-! ## Each step is a derivation -/

/-- An ι step at a stored recursor is a reduction (`Red.iota`). -/
theorem _root_.Ix.Cert.IotaStep.red {c : Key md} {cv : Ix.Kernel.ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} {rl : RecRule md} {e e' : Ix.Kernel.Expr md}
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (h : IotaStep env c cv mI rP rules rl e e') : Red env 0 e e' := by
  obtain ⟨-, us, major, cj, usj, cvj, cnP, cnF, residual, hhead, hlen, hus, hmajor, hmhead, hctor,
    hrule, hmlen, hfire, hlv, hparams, hcertR, hcertC, hres, hidx, rfl⟩ := h
  exact Red.iota hhead hfind hlen hus hmajor hmhead hctor hrule hmlen hfire hlv hparams hcertR
    hcertC hres hidx

/-- A projection step is a reduction (`Red.proj`). -/
theorem _root_.Ix.Cert.ProjStep.red {sn : Key md} {i : Nat} {e e' : Ix.Kernel.Expr md}
    (h : ProjStep env sn i e e') : Red env 0 e e' := by
  obtain ⟨-, u, entry, us, cvC, nP, nF, rfl, hent, hhead, hi, hlen, hus, hfire, hctor, hcerts,
    rfl⟩ := h
  exact Red.proj hent hhead hi hlen hus hfire hctor hcerts

/-- A structure-η step at a stored family is a conversion (`DefEq.structEta`). -/
theorem _root_.Ix.Cert.StructEtaStep.defEq {T : Key md} {cvT : Ix.Kernel.ConstantVal md} {caps : IndCaps md}
    {a b : Ix.Kernel.Expr md} (hT : env.find? T = some (.indInfo cvT caps))
    (h : StructEtaStep env T cvT caps a b) : DefEq env 0 a b := by
  obtain ⟨-, -, tb, wtb, c, us, cvc, cnP, cnF, us', htb, hwtb, hhead, hctor, hlen, hthead, heta,
    hetaCtor, hresT, hresc, htlen, hlv, hlps, hslots, hus, hcerts, hproj, hparams, hfields⟩ := h
  exact DefEq.structEta htb hwtb hhead hctor hlen hthead hT heta hetaCtor hresT hresc htlen hlv
    hlps hslots hus hcerts hproj hparams hfields

/-- A unit-like step at a stored family is a conversion (`DefEq.structUnit`). -/
theorem _root_.Ix.Cert.StructUnitStep.defEq {T : Key md} {cvT : Ix.Kernel.ConstantVal md} {caps : IndCaps md}
    {a b : Ix.Kernel.Expr md} (hT : env.find? T = some (.indInfo cvT caps))
    (h : StructUnitStep env T cvT caps a b) : DefEq env 0 a b := by
  obtain ⟨-, -, ta, wta, tb, wtb, us', hta, hwta, hthead, hunit, hresT, htlen, hlv, htb, hwtb, hd,
    hcerts⟩ := h
  exact DefEq.structUnit hta hwta hthead hT hunit hresT htlen hlv htb hwtb hd hcerts

/-! ## The laws -/

/-- **A strong model satisfies the step-level recursor rules** of its environment. -/
theorem recRuleLaws (M : Cached.StrongModel V env) : StepRecRuleLaws M.model.cval env :=
  fun _ _ _ _ _ hfind _ _ _ _ _ h => (red_denoteSame M h.1 (h.red hfind)).denoteAlike

/-- **A strong model satisfies the step-level capability laws** of its environment. -/
theorem capabilityLaws (M : Cached.StrongModel V env) : StepCapabilityLaws M.model.cval env :=
  ⟨fun _ _ _ hT _ _ h => (defeq_denoteSame M h.1 h.2.1 (h.defEq hT)).denoteAlike,
    fun _ _ _ hT _ _ h => (defeq_denoteSame M h.1 h.2.1 (h.defEq hT)).denoteAlike,
    fun _ _ _ _ h => (red_denoteSame M h.1 h.red).denoteAlike⟩

end Ix.Cert.StrongStepLaws
