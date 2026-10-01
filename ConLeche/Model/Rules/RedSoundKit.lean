module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitInstall
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Denote.StrLit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.IOLicense

public section

/-!
# The reduction lane's transplanted kit (task #305, lane S-red)

The semantic facts the reduction rules' soundness needs are
**transplanted** here, argument for argument, from the `Model/Steps/*`
rows the DESIGN record names — that tier was deleted at the task #305
closing, and the citations below are its history.  Nothing in this
file mentions a run.

Sections, in the order the rules consume them:

* the level crossing and the assignment-independent literal slots
  (`Model/Annot/BitLevels.lean`'s `acval_*`/`denotePInstLevels`, now
  imported rather than transplanted — that file is impl-free);
* the two `Nat` constructor readings (`Steps/DefEq.lean:99`, `:119`)
  and the literal expansions' blindness (`Steps/Major.lean:66`,
  `Steps/Stuck.lean:540`);
* the δ identity (`delta_of`, `Steps/Whnf.lean:329`);
* **the shared telescope kit** — `hoist_spine`, `frame_spine`,
  `mkAppN_of_fitA`, the `PiChain` guard with `piChain_of_stripPis`
  and `peelPis_of_piChain`, and the stored entry's telescope
  (`Steps/{Stuck,CapsRows,IotaKit,TowerKit}.lean`).  This is the
  LOWEST kit of the four, so a fact more than one lane needs lives
  here and nowhere else.  `DenoteMetaSpine`'s own list algebra,
  `denoteMeta_mkAppN(_inv)` and the tower entry's two readings are
  `Model/Annot/BitLemmas.lean`'s, imported (task #305 closing).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {m : EnvModel V env}

/-! ## The level crossing — `Model/Annot/BitLevels.lean`, imported

`acval_isEmpty`, `acval_oneParam`, `acval_scalar`, `acval_one`,
`acval_natPair` and `denotePInstLevels` were transplanted here under
camelCase names so that the two spellings could coexist while
`Model/Steps/BitLevels.lean` lived.  That file is impl-free and moved to
`Model/Annot/BitLevels.lean` (task #305 closing), so the kit imports it
and there is ONE copy, under that file's own names. -/

/-! ## The two `Nat` constructor readings and the literal expansions -/

theorem denoteMetaNatZeroConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natZeroName [])
      = some (acval ConLeche.natZeroName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? ConLeche.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h2
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [ConLeche.natZeroOk] at h2
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

theorem denoteMetaNatSuccConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natSuccName [])
      = some (acval ConLeche.natSuccName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? ConLeche.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h3
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [ConLeche.natSuccOk] at h3
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- `denoteMeta` is blind to the `Nat`-literal constructor expansion. -/
theorem denoteMeta_natLitToConstructor
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) (d n : Nat) :
    denoteMeta acval env φ d (ConLeche.natLitToConstructor n)
      = denoteMeta acval env φ d (.lit (.natVal n)) := by
  match n with
  | 0 =>
    rw [ConLeche.natLitToConstructor, denoteMetaNatZeroConst hg,
      denoteMeta_natLit hg]
    rfl
  | k + 1 =>
    rw [ConLeche.natLitToConstructor, denoteMeta_app, denoteMetaNatSuccConst hg,
      denoteMeta_natLit hg, denoteMeta_natLit hg]
    rfl

theorem denoteMetaConstNolevels
    {acval : Name → (Name → Nat) → AnnotTerm} {c : Name}
    {ci : ConLeche.ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denoteMeta acval env φ d (.const c [])
      = some (acval c (Level.substFn φ [] [])) := by
  rw [denoteMeta_const hf (by simp [hlp]), hlp]

theorem denoteMetaNilTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listNilName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciN, p, mb, hfN, hlpN, -⟩ := listNil_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciN.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listNilName := by
    simp [levelParamsAt, hfN]
  rw [denoteMeta, denoteMeta_const hfN (by simp [hlpN]),
    denoteMetaConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteMetaConsTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listConsName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciC', p, -, -, -, hfC', hlpC', -⟩ := listCons_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciC'.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listConsName := by
    simp [levelParamsAt, hfC']
  rw [denoteMeta, denoteMeta_const hfC' (by simp [hlpC']),
    denoteMetaConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteMetaStrLitList
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denoteMeta acval env φ d (ConLeche.strLitList cs)
        = some (charListAV
          (.app (acval ConLeche.listNilName
            (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (.app (acval ConLeche.listConsName
            (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (acval ConLeche.charOfNatName (Level.substFn φ [] []))
          (acval ConLeche.natZeroName (Level.substFn φ [] []))
          (acval ConLeche.natSuccName (Level.substFn φ [] []))
          cs) := by
  have hnat : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciF, mb, hfF, hlpF, -⟩ := charOfNat_shape hg
  intro cs
  induction cs with
  | nil =>
    rw [ConLeche.strLitList, charListAV]; exact denoteMetaNilTerm hg d
  | cons c cs ih =>
    rw [ConLeche.strLitList, charListAV, denoteMeta, denoteMeta,
      denoteMetaConsTerm hg d, denoteMeta,
      denoteMetaConstNolevels hfF hlpF d, denoteMeta_natLit hnat, ih]
    rfl

/-- `denoteMeta` is blind to the string-literal constructor expansion. -/
theorem denoteMeta_strLitToConstructor
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) (s : String) :
    denoteMeta acval env φ d (ConLeche.strLitToConstructor s)
      = denoteMeta acval env φ d (.lit (.strVal s)) := by
  obtain ⟨ciO, mb, hfO, hlpO, -⟩ := stringOfList_shape hg
  rw [ConLeche.strLitToConstructor_eq, denoteMeta,
    denoteMetaConstNolevels hfO hlpO d, denoteMetaStrLitList hg d,
    denoteMeta, if_pos hg]
  rfl


/-! ## The application congruence at the reading -/

/-- The frame of a closed atom. -/
theorem frame_atom {d : Nat} {e : Expr} (h : e.fvarLeaves = [])
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true) :
    Frame d e ∧ ∀ (x : Expr), LeavesSub e x :=
  ⟨⟨hw, hb, fun l hl => by rw [h] at hl; exact nomatch hl⟩,
   fun _ l hl => by rw [h] at hl; exact nomatch hl⟩

/-- The two components of a graded application are graded. -/
theorem graded_app {Δa : List AnnotTerm} {f x : AnnotTerm}
    (h : Graded V Δa (.app f x)) : Graded V Δa f ∧ Graded V Δa x :=
  ⟨fun σ hσ =>
      ⟨by have h1 := (h σ hσ).1; rw [WellDenoted_app] at h1; exact h1.1,
        by have h2 := (h σ hσ).2; rw [AnnotValid_app] at h2; exact h2.1⟩,
   fun σ hσ =>
      ⟨by have h1 := (h σ hσ).1; rw [WellDenoted_app] at h1; exact h1.2.1,
        by have h2 := (h σ hσ).2; rw [AnnotValid_app] at h2; exact h2.2⟩⟩


/-- An application's grading depends on its two components only through
their VALUES, so it transfers along equal-valued graded replacements
(the content `whnfCore_app_claim` (`Steps/Whnf.lean:509`) writes inline
at its head slot; stated once, for either slot). -/
theorem appCongrV {σ : Nat → V} {f a f' a' : AnnotTerm}
    (heqf : interp V σ f = interp V σ f')
    (heqa : interp V σ a = interp V σ a')
    (hgf' : WellDenotedV V σ f') (hga' : WellDenotedV V σ a')
    (h : WellDenotedV V σ (.app f a)) : WellDenotedV V σ (.app f' a') := by
  refine ⟨?_, by rw [AnnotValid_app]; exact ⟨hgf'.2, hga'.2⟩⟩
  have h1 := h.1
  rw [WellDenoted_app] at h1 ⊢
  obtain ⟨-, -, v, A, B, h2, h3, h4⟩ := h1
  exact ⟨hgf'.1, hga'.1, v, A, B, heqf ▸ h2, heqa ▸ h3, h4⟩


/-! ## `projAV`'s grading under equal-valued subjects
(`Model/Steps/ProjAVKit.lean` and `projAV_validV`, transplanted) -/

namespace ProjAV

/-- The subject of a graded projection spine is graded. -/
theorem hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (projAV i e) → WellDenoted V σ e
  | 0, e, σ, h => ((WellDenoted_fst V σ e) ▸ h).1
  | i + 1, e, σ, h =>
    ((WellDenoted_snd V σ e) ▸ (hoist (i := i) (e := .snd e) h)).1

/-- The subject of a bit-valid projection spine is bit-valid. -/
theorem validHoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ (projAV i e) → AnnotValid V σ e
  | 0, e, σ, h => (AnnotValid_fst V σ e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValid_snd V σ e) ▸ (validHoist (i := i) (e := .snd e) h)

/-- The uniform projection spelling is bit-valid whenever its subject
is (`projAV_validV`, `Model/Inductives/StructIntro.lean:90`). -/
theorem validV :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ e → AnnotValid V σ (projAV i e)
  | 0, e, σ, h => by
    show AnnotValid V σ (.fst e)
    rw [AnnotValid_fst]
    exact h
  | i + 1, e, σ, h => by
    show AnnotValid V σ (projAV i (.snd e))
    exact validV (by rw [AnnotValid_snd]; exact h)

/-- **`projAV`'s truthfulness transfers to an equal-valued graded
subject.** -/
theorem congr :
    ∀ {i : Nat} {e e' : AnnotTerm} {σ : Nat → V},
      interp V σ e = interp V σ e' → WellDenoted V σ e' →
      WellDenoted V σ (projAV i e) → WellDenoted V σ (projAV i e')
  | 0, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (.fst e')
    have h : WellDenoted V σ (.fst e) := hok
    rw [WellDenoted_fst] at h ⊢
    obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := h
    exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩
  | i + 1, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (projAV i (.snd e'))
    have hok1 : WellDenoted V σ (.snd e) :=
      hoist (i := i) (e := .snd e) hok
    refine congr (i := i) (e := .snd e) (e' := .snd e') ?_ ?_ hok
    · simp only [interp_snd, heq]
    · rw [WellDenoted_snd] at hok1 ⊢
      obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := hok1
      exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩

/-- `WellDenotedV` form of the congruence. -/
theorem congrV {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') (hok' : WellDenotedV V σ e')
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ (projAV i e') :=
  ⟨congr heq hok'.1 hok.1, validV hok'.2⟩

/-- `WellDenotedV` of the subject, off the spine's. -/
theorem hoistV {i : Nat} {e : AnnotTerm} {σ : Nat → V}
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ e :=
  ⟨hoist hok.1, validHoist hok.2⟩

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp_congr {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') :
    interp V σ (projAV i e) = interp V σ (projAV i e') := by
  rw [projAV_interp, projAV_interp, heq]

end ProjAV


/-! ## The β step at the currency (`Steps/Whnf.lean:117-161`, transplanted) -/

/-- **The argument is in the λ's domain**, at a positive kind, from the
application's `WellDenoted` alone (`wellDenoted_beta_dom_pos`). -/
theorem betaDomPos {v : Nat} (hv : v ≠ 0) {A b a : AnnotTerm}
    {ρ : Nat → V} (h : WellDenoted V ρ (.app (.lam v A b) a)) :
    interp V ρ a ∈ˢ interp V ρ A := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, -, v', A', B', hslot, hmem, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, -, B, hfib, -⟩ := hlam
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    have h1 := eq_pt_of_mem_piR_zero hslot
    rw [interp_lam] at h1
    exact lamR_ne_pt hv h1
  have hown : interp V ρ (.lam v A b) ∈ˢ piR v (interp V ρ A) B := by
    rw [interp_lam]
    exact lamR_mem hfib
  rw [piR_dom_unique hv hv' hown hslot]
  exact hmem

/-- A λ's domain annotation is graded when the λ is
(`WellDenotedV.lam_dom`). -/
theorem lamDomV {v : Nat} {A b : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.lam v A b)) : WellDenotedV V ρ A :=
  ⟨by have h1 := h.1; rw [WellDenoted_lam] at h1; exact h1.1,
   by have h2 := h.2; rw [AnnotValid_lam] at h2; exact h2.1⟩

/-- **The graded β step at a positive kind** (`WellDenotedV_beta_pos`). -/
theorem betaPosV {v : Nat} (hv : v ≠ 0) {A b a : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.app (.lam v A b) a)) :
    interp V ρ (.app (.lam v A b) a) = interp V ρ (b.inst a) ∧
      WellDenotedV V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := WellDenoted_beta_pos V hv h.1
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValid_app, AnnotValid_lam] at hv2
  exact (AnnotValid_inst0 V hv2.2).mpr (hv2.1.2 _ (betaDomPos hv h.1))

/-- **The graded β step at kind `0`** (`WellDenotedV_beta_zero`): the
domain membership is the β certificate's. -/
theorem betaZeroV {A b a : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.app (.lam 0 A b) a))
    (hmem : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (.app (.lam 0 A b) a) = interp V ρ (b.inst a) ∧
      WellDenotedV V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := WellDenoted_beta_zero V h.1 hmem
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValid_app, AnnotValid_lam] at hv2
  exact (AnnotValid_inst0 V hv2.2).mpr (hv2.1.2 _ hmem)


/-! ## The telescope walk's one-slot kit
(`Model/Steps/IotaKit.lean:370`, `IotaGate.lean:63,77`, transplanted) -/

/-- **A `TeleFitPA` fit plus the type's grading grades the applied
spine**, and places it in the residual's reading
(`wellDenotedV_mkAppN_of_fitA`). -/
theorem mkAppN_of_fitA {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f rest : AnnotTerm},
      WellDenotedV V ρ Ta → WellDenotedV V ρ f →
      (∀ x ∈ vs, WellDenotedV V ρ x) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      TeleFitPA V ρ Ta vs rest →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) ∧
        interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ interp V ρ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f rest _ hf _ hmem hfit
    cases hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f rest hokT hf hoks hmem hfit
    cases hfit with
    | @cons u v A B _ _ _ hx hfit' =>
      have hokA : WellDenotedV V ρ A :=
        ⟨((WellDenoted_pi V ρ u v A B) ▸ hokT.1).1,
          ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V ρ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V ρ A →
          interp V (cons y ρ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      have hokx : WellDenotedV V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenotedV V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hokx.1, v, interp V ρ A,
            (fun y => interp V (cons y ρ) B), hmem, hx, hfib⟩
        · rw [AnnotValid_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
        rw [interp_inst0, interp_app]
        exact app_mem_piR hmem hx hfib
      exact ih ((WellDenotedV_inst0 hokx).mpr (hokB _ hx)) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-- The head of a graded spine is graded (`wellDenotedV_mkAppN_head`). -/
theorem mkAppN_head {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {f : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN f as) → WellDenotedV V ρ f
  | [], _, h => h
  | a :: as, f, h => by
    have h' : WellDenotedV V ρ (.app f a) := mkAppN_head as h
    exact ⟨((WellDenoted_app V ρ f a) ▸ h'.1).1,
      ((AnnotValid_app V ρ f a) ▸ h'.2).1⟩

/-- **The ι-slot licence, one slot** (`iota_slot_transfer`). -/
theorem slotTransfer {v v' : Nat} {A A' f a : V} {B B' : V → V}
    (hv : v ≠ 0) (hf : f ∈ˢ piR v A B)
    (hslot : f ∈ˢ piR v' A' B') (ha : a ∈ˢ A') : a ∈ˢ A :=
  io_domain_transfer hv hslot ha hf


/-! ## The spine kit — `Model/Annot/BitLemmas.lean`, imported

`DenoteMetaSpine` and its list algebra (`length`, `getD_read`,
`take`, `drop`, `append`, `map_list`, `snoc`, `getD`, `mem`),
`denoteMeta_mkAppN(_inv)` and the tower entry's two readings are
that file's, and there is ONE copy of each (task #305 closing).
What is still stated here is what mentions the rules tier's own
`Graded`/`Frame` abbreviations. -/

/-- Every argument of a graded application spine is graded, and so is
its head (`hoist_spine`). -/
theorem hoist_spine {Δa : List AnnotTerm} :
    ∀ (asa : List AnnotTerm) {fa : AnnotTerm},
      Graded V Δa (AnnotTerm.mkAppN fa asa) →
      Graded V Δa fa ∧ ∀ x ∈ asa, Graded V Δa x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · exact ((WellDenoted_app V ρ fa a) ▸ (happ ρ hρ).1).1
    · exact ((AnnotValid_app V ρ fa a) ▸ (happ ρ hρ).2).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fun ρ hρ =>
          ⟨((WellDenoted_app V ρ fa x) ▸ (happ ρ hρ).1).2.1,
            ((AnnotValid_app V ρ fa x) ▸ (happ ρ hρ).2).2⟩
      · exact hrest x hx'

/-- The frame conditions of every argument of a spine (`frame_spine`). -/
theorem frame_spine {d : Nat} {Δa : List AnnotTerm} {a : Expr}
    (hf : Frame d a) (hC : CtxOk m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Frame d x ∧ CtxOk m φ d Δa x := fun x hx =>
  ⟨⟨hf.1.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hf.2.1 x hx,
      fun l hl => hf.2.2 l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩,
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)⟩

/-! ## The tower entry's telescope (`Steps/TowerKit.lean:46`, `:173`;
the entry's two READINGS are `Model/Annot/BitLemmas.lean`'s) -/

/-- A stored tower entry's body telescope is closed. -/
theorem towerEntry_tele_closed (hwf : ConLeche.EnvWF env) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    (us : List Level) :
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).hasFvar = false ∧
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).looseBVarsBounded 0
      = true := by
  rw [ConLeche.projTele_hasFvar, ConLeche.projTele_looseBVarsBounded,
    Nat.zero_add]
  exact ⟨ConLeche.projEntry_body_hasFvar hwf hfe us,
    ConLeche.projEntry_body_looseBVars hwf hfe us⟩

/-- **The body telescope's reading is depth-free.** -/
theorem towerEntry_tele_at_depth {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) :
    (∀ d : Nat, denoteMeta m.acval env φ d
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) ∧
    ∀ k : Nat, Ta.liftN 1 k = Ta := by
  obtain ⟨hnf, hb⟩ := towerEntry_tele_closed m.wf hfe us
  have hcl : ∀ k : Nat, Ta.liftN 1 k = Ta := fun k =>
    denoteMeta_closed m.acval_erase m.cval_closed hnf hb hTa 1 k
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf hcl hTa, hcl⟩

/-! ## The ∀-chain guard and the fit's un-instantiation
(`Steps/CapsRows.lean:79-180`, `ProjRows.lean:254`, transplanted) -/

/-- The reading's first `n` heads are `.pi` nodes (`PiChain`). -/
@[expose] def PiChain : Nat → AnnotTerm → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ _ _ B => PiChain n B
    | _ => False

theorem piChain_succ_inv {n : Nat} {e : AnnotTerm} (h : PiChain (n + 1) e) :
    ∃ u v A B, e = .pi u v A B ∧ PiChain n B := by
  match e with
  | .pi u v A B => exact ⟨u, v, A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

theorem PiChain.inst : ∀ {n : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    PiChain n e → PiChain n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact ih a (k + 1) hB

/-- **A syntactic ∀-telescope reads to a ∀-chain**
(`piChain_of_stripPis`). -/
theorem piChain_of_stripPis {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm},
      (e.stripPis n).isSome = true →
      denoteMeta acval env φ d e = some ea → PiChain n ea := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro d e ea hs hd
    match e, hs with
    | .bvar _, hs => exact nomatch hs
    | .fvar _ _, hs => exact nomatch hs
    | .sort _, hs => exact nomatch hs
    | .const _ _, hs => exact nomatch hs
    | .app _ _, hs => exact nomatch hs
    | .lam _ _ _, hs => exact nomatch hs
    | .letE _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE ty bd mb, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hd
      simp only [ConLeche.Expr.stripPis, Option.isSome_map] at hs
      exact ih (ConLeche.Expr.stripPis_instantiate1_isSome n 0 hs) hba

/-- A ∀-chain of a list's length peels along it
(`peelPis_of_piChain`).  Shared: the defeq and ι lanes both peel a
stored telescope against a spine. -/
theorem peelPis_of_piChain : ∀ (as : List AnnotTerm) {T : AnnotTerm},
    PiChain as.length T →
      ∃ rest, ConLeche.Model.AnnotTerm.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact peelPis_of_piChain as (PiChain.inst a 0 hB)

/-- **The fit un-instantiates, under the ∀-chain guard**
(`teleFit_of_inst`). -/
theorem teleFit_of_inst {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V ρ (E.inst aa k) L rest →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    obtain rfl : rest = interp V ρ (E.inst aa k) := teleFit_nil_inv h
    rw [interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi] at h
    cases h with
    | cons hmem hfit =>
      refine .cons (by rwa [interp_inst] at hmem) ?_
      have hrec := ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit
      rw [shiftE_succ_cons] at hrec
      rw [cons_instE]
      exact hrec

theorem teleFit_of_inst0 {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V ρ (E.inst aa) L rest) :
    TeleFit V (cons (interp V ρ aa) ρ) E L rest := by
  have := teleFit_of_inst hpc h
  rwa [shiftE_zero_zero, instE_zero] at this

/-- **An annotation-level fit is a value-level fit**
(`teleFit_of_teleFitPA`). -/
theorem teleFit_of_teleFitPA {ρ : Nat → V} :
    ∀ {T : AnnotTerm} {as : List AnnotTerm} {resta : AnnotTerm},
      PiChain as.length T → TeleFitPA V ρ T as resta →
      TeleFit V ρ T (as.map (interp V ρ)) (interp V ρ resta) := by
  intro T as resta hpc h
  revert hpc
  induction h with
  | nil => intro _; exact .nil
  | @cons u v A B rest a as hmem hfit ih =>
    intro hpc
    have hpcB : PiChain as.length B := hpc
    exact .cons hmem (teleFit_of_inst0 (by rw [List.length_map]; exact hpcB)
      (ih (PiChain.inst a 0 hpcB)))


/-! ## The δ identity (`delta_of`, `Steps/Whnf.lean:329`, transplanted) -/

/-- The instantiated form of `AcvalDefnInst`, by the level crossing
(`acvalDefnInst_subst`, `Steps/Whnf.lean:277`). -/
theorem denoteMetaDefnInst {m : EnvModel V env} (hdi : AcvalDefnInst m)
    (φ : Name → Nat) {cv : ConstantVal} {value : Expr} {us : List Level}
    (hmem : ∃ hint : ConLeche.ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) :
    denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval cv.name (Level.substFn φ cv.levelParams us)) := by
  rw [denotePInstLevels m φ cv.levelParams us 0 value]
  exact hdi _ cv value hmem

/-- `delta_core` (`Steps/Whnf.lean:289`), transplanted. -/
private theorem deltaCore (m : EnvModel V env)
    {d : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea : AnnotTerm}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval ci.name (Level.substFn φ cv.levelParams us)))
    (hea : denoteMeta m.acval env φ d e = some ea) :
    denoteMeta m.acval env φ d
        (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs) = some ea := by
  obtain rfl : ci.name = n := by
    rw [ConLeche.Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    ConLeche.Expr.mkAppN_getApp e
  rw [← he] at hea
  refine denoteMeta_mkAppN_swap e.getAppArgs ?_ hea
  intro fa hfa
  rw [hfn, denoteMeta, hfind] at hfa
  simp only [hcvt] at hfa
  rw [if_pos hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  exact denoteMeta_depth_of_closed m.acval_closed
    (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hnofv)
    (fun k => m.acval_closed _ _ k) hval d

/-- **The δ step is invisible to the reading** (`delta_of`,
`Steps/Whnf.lean:329`): the unfolding has the subject's own
annotation. -/
theorem denoteMeta_unfoldDefinition {m : EnvModel V env} (hdi : AcvalDefnInst m)
    {d : Nat} {e e' : Expr} {ea : AnnotTerm}
    (hud : ConLeche.unfoldDefinition env e = some e')
    (hea : denoteMeta m.acval env φ d e = some ea) :
    denoteMeta m.acval env φ d e' = some ea := by
  unfold ConLeche.unfoldDefinition at hud
  split at hud
  · next n us hfn =>
    split at hud
    · next cv value hint hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact deltaCore m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ :=
                m.wf _ (ConLeche.find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (denoteMetaDefnInst hdi φ ⟨hint, ConLeche.find?_mem hfind⟩) hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud


end ConLeche.Model.Rules
