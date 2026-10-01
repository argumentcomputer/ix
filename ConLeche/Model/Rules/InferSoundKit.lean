module

-- lane S-red's kit is the SHARED one: `DenoteMetaSpine`'s list algebra,
-- `denoteMeta_mkAppN(_inv)`, `denoteMeta_proj_inv_tower`,
-- `teleFit_nil_inv` and the tower entry's reading live there
public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Semantics.Hoist
import ConLeche.Semantics.LitStep
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Annot.ValidSpine

public section

/-!
# The S-infer kit (task #305, lane S-infer)

The pieces the inference rules' soundness needs, restated here **by
transplant** from the `Model/Steps/*` rows that carried them until the
task #305 closing deleted that tier (the citations below are their
provenance):

* `wellDenotedV_mkAppN_of_fit` (`Steps/CapsRows.lean:402`) — the
  fit-to-application kit the string chain rides (`teleFit_nil_inv`,
  the spine inversion and the entry-kind inversion come from lane
  S-red's `RedSoundKit.lean`);
* `charList_facts` and `strLitFacts` (`Steps/StrLit.lean:70`, `:176`)
  — the `String`-literal clause's whole content, stated over
  `RulesInputs`' fields (`ConstType`/`AcvalValid`/`NatHeads` are
  `ConstType`/`AcvalValid`/`NatHeads` verbatim).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The `WellDenotedV` splitters (`Steps/InferIO.lean:75`, `:123`, `:142`)

The consumption motive's entry into every non-leaf clause: the io
grade's premise splits hereditarily into the parts' gradings, and at
an application into the **hereditary app slot** the io licence reads.
-/

/-- The `WellDenotedV` ∀-splitter. -/
theorem WellDenotedV.hoist_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenotedV V ρ B) := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_pi V _ u v A B) ▸
      (h _ (Sat_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- The `WellDenotedV` λ-splitter. -/
theorem WellDenotedV.hoist_lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenotedV V ρ b) := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_lam V _ v A b) ▸
      (h _ (Sat_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- The `WellDenotedV` application splitter, the hereditary app slot
included. -/
theorem WellDenotedV.hoist_app {Δa : List AnnotTerm} {f a : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.app f a)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ f) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ a) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        ∃ (v : Nat) (A : V) (B : V → V),
          interp V ρ f ∈ˢ piR v A B ∧ interp V ρ a ∈ˢ A ∧
          (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :=
  ⟨fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).1,
      ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).1⟩,
    fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).2.1,
      ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).2⟩,
    fun ρ hρ => ((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).2.2⟩

/-! ## The fit-to-application kit (`Steps/CapsRows.lean`) -/

theorem wellDenotedV_mkAppN_of_fit {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {σ : Nat → V} {rest : V},
      WellDenotedV V σ Ta → WellDenotedV V ρ f →
      (∀ x ∈ vs, WellDenotedV V ρ x) →
      interp V ρ f ∈ˢ interp V σ Ta →
      TeleFit V σ Ta (vs.map (interp V ρ)) rest →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) ∧
        interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f σ rest _ hf _ hmem hfit
    obtain rfl : rest = interp V σ Ta := teleFit_nil_inv hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f σ rest hokT hf hoks hmem hfit
    simp only [List.map_cons] at hfit
    cases hfit with
    | @cons _ u v A B _ _ _ hx hfit' =>
      have hokA : WellDenotedV V σ A :=
        ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).1,
          ((AnnotValid_pi V σ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp V σ A → WellDenotedV V (cons y σ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V σ A →
          interp V (cons y σ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      have hokx : WellDenotedV V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenotedV V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hokx.1, v, interp V σ A,
            (fun y => interp V (cons y σ) B), hmem, hx, hfib⟩
        · rw [AnnotValid_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp V ρ (.app f x)
          ∈ˢ interp V (cons (interp V ρ x) σ) B := by
        rw [interp_app]
        exact app_mem_piR hmem hx hfib
      -- (`mkAppN f (x :: xs) = mkAppN (.app f x) xs` is definitional)
      exact ih (hokB _ hx) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-! ## The character-list chain (`Steps/StrLit.lean`) -/

/-- **The character-list facts** — `natLit_factsAV`'s companion.  Every
`denoteMeta` character list is graded and inhabits `List Char`'s reading,
by induction on the list from the `nil`/`cons`/`Char.ofNat` head
packages and the two numeral heads. -/
theorem charList_facts {ρ : Nat → V}
    {KL KH KN KC KF Kz Ks KNat : AnnotTerm} {bN b1 b2 b3 bF : Nat}
    (hclL : ∀ σ : Nat → V, interp V σ KL = interp V ρ KL)
    (hclH : ∀ σ : Nat → V, interp V σ KH = interp V ρ KH)
    (hokKH : WellDenotedV V ρ KH) (hokKN : WellDenotedV V ρ KN)
    (hokKC : WellDenotedV V ρ KC) (hokKF : WellDenotedV V ρ KF)
    (hokKz : WellDenotedV V ρ Kz) (hokKs : WellDenotedV V ρ Ks)
    (hCharU : interp V ρ KH ∈ˢ (univ 1 : V))
    (hokTN : WellDenotedV V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AnnotTerm))
    (hmemN : interp V ρ KN ∈ˢ interp V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AnnotTerm))
    (hokTC : WellDenotedV V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AnnotTerm))
    (hmemC : interp V ρ KC ∈ˢ interp V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AnnotTerm))
    (hokTF : WellDenotedV V ρ ((.pi 0 bF KNat KH) : AnnotTerm))
    (hmemF : interp V ρ KF ∈ˢ interp V ρ
      ((.pi 0 bF KNat KH) : AnnotTerm))
    (hz : interp V ρ Kz ∈ˢ interp V ρ KNat)
    (hsucc : interp V ρ Ks
      ∈ˢ piR 1 (interp V ρ KNat) fun _ => interp V ρ KNat) :
    ∀ cs : List Char,
      WellDenotedV V ρ (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs) ∧
        interp V ρ (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs)
          ∈ˢ interp V ρ ((.app KL KH) : AnnotTerm) := by
  -- the sort domain, at the reading's own spelling
  have hCharS : interp V ρ KH ∈ˢ interp V ρ ((.sort 1) : AnnotTerm) := by
    rw [interp_sort]; exact hCharU
  -- one character element: `Char.ofNat` applied to a numeral
  have helem : ∀ c : Char,
      WellDenotedV V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm) ∧
        interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm)
          ∈ˢ interp V ρ KH := by
    intro c
    have hnat := natLit_factsAV hokKz.1 hokKs.1 hz hsucc c.toNat
    have hokNum : WellDenotedV V ρ (natLitAV Kz Ks c.toNat) :=
      ⟨hnat.1, AnnotValid_natLitAV hokKz.2 hokKs.2 c.toNat⟩
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
      [natLitAV Kz Ks c.toNat] hokTF hokKF
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokNum)
      hmemF (TeleFit.cons hnat.2 TeleFit.nil)
    refine ⟨h.1, ?_⟩
    have := h.2
    rwa [hclH (cons (interp V ρ (natLitAV Kz Ks c.toNat)) ρ)] at this
  -- the walk
  intro cs
  induction cs with
  | nil =>
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ) [KH] hokTN hokKN
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokKH)
      hmemN (TeleFit.cons hCharS TeleFit.nil)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp_app, hclL (cons (interp V ρ KH) ρ)] at h2
    rw [interp_app]
    exact h2
  | cons c cs ih =>
    obtain ⟨ihA, ihm⟩ := ih
    obtain ⟨heA, hem⟩ := helem c
    -- the three memberships, at the fit's own environments
    have hm2 : interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm)
        ∈ˢ interp V (cons (interp V ρ KH) ρ) ((.bvar 0) : AnnotTerm) := hem
    have hm3 : interp V ρ
          (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs)
        ∈ˢ interp V
          (cons (interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm))
            (cons (interp V ρ KH) ρ))
          ((.app KL (.bvar 1)) : AnnotTerm) := by
      have hi := ihm
      rw [interp_app] at hi
      rw [interp_app, hclL _]
      exact hi
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
      [KH, .app KF (natLitAV Kz Ks c.toNat),
        charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs]
      hokTC hokKC
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hokKH
        · exact heA
        · exact ihA)
      hmemC
      (TeleFit.cons hCharS (TeleFit.cons hm2 (TeleFit.cons hm3
        TeleFit.nil)))
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp_app, hclL _] at h2
    rw [interp_app]
    exact h2

/-! ## The chain at the environment

The five head packages, read off `ConstType` at the guard's pinned
types.  Note what is *absent*: `List`'s own membership
(`strLit_facts`' `hListMem`) and the four hand-built type gradings —
the P residue delivers a stored type's grading with its reading, so
the only environment facts consumed are the four memberships and
`Char`'s universe membership. -/

/-- **The string chain, at the environment.**  `strLit_facts`' mirror
at the validated-annotation currency. -/
theorem strLitFacts {m : EnvModel V env} (hct : ConstType m φ)
    (hval : AcvalValid m) (hnh : NatHeads m φ)
    (hg : ConLeche.strLitSupported env = true) {d : Nat} {s : String}
    {ea : AnnotTerm}
    (hea : denoteMeta m.acval env φ d (.lit (.strVal s)) = some ea)
    (ρ : Nat → V) :
    WellDenotedV V ρ ea ∧
      interp V ρ ea ∈ˢ
        interp V ρ (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    hTS, hTH, ⟨mbO, hTO⟩, ⟨mbL, hTL⟩, ⟨mbN, hTN⟩,
    ⟨mb1, mb2, mb3, hTC⟩, ⟨mbF, hTF⟩⟩ :=
    ConLeche.strLitSupported_inv hg
  obtain ⟨cvNat, capsNat, cv0, i0, j0, cv1, i1, j1, hfNat, hfZ, hfSc,
    hlpNat, hlpZ, hlpSc, hTNat, hTZ, hTSc⟩ :=
    ConLeche.natLitSupported_inv hs
  rw [denoteMeta, if_pos hg] at hea
  obtain rfl := (Option.some.inj hea).symm
  -- the two `List` level-parameter lists, at the reading's spelling
  have hlpAtN : levelParamsAt env ConLeche.listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env ConLeche.listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  -- every leaf is closed, graded and bit-valid
  have hleafC : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      interp V σ (m.acval n ψ) = interp V ρ (m.acval n ψ) := fun n ψ σ =>
    interp_closed V (by rw [m.acval_erase]; exact m.cval_closed n ψ) σ ρ
  have hleafOk : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      WellDenotedV V σ (m.acval n ψ) := fun n ψ σ =>
    ⟨m.acval_wellDenoted _ _ σ, hval _ _ σ⟩
  -- the stored types' rows, from the `const` residue
  have head : ∀ (n : Name) (ci : ConstantInfo) (us : List Level)
      (ta : AnnotTerm), env.find? n = some ci → ci.isTowerEntry = false →
      us.length = ci.toConstantVal.levelParams.length →
      denoteMeta m.acval env φ 0
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta →
      (∀ σ : Nat → V, WellDenotedV V σ ta) ∧
        ∀ σ : Nat → V,
          interp V σ (m.acval n
              (Level.substFn φ ci.toConstantVal.levelParams us))
            ∈ˢ interp V σ ta := by
    intro n ci us ta hf hnt hlen hta
    obtain ⟨ta', hta', hok, hmem⟩ := hct 0 n ci us hf hnt hlen
    obtain rfl : ta = ta' := Option.some.inj (hta.symm.trans hta')
    exact ⟨hok, hmem⟩
  -- the shared `.const` readings
  have hKL : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.listName [.zero])
      = some (m.acval ConLeche.listName
          (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) :=
    fun D => denoteMeta_const hfL (by simp [hlpL])
  have hKH : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.charName [])
      = some (m.acval ConLeche.charName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfH (by simp [hlpH]), hlpH]
  have hKNat : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.natName [])
      = some (m.acval ConLeche.natName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfNat
      (by simp [ConstantInfo.toConstantVal, hlpNat])]
    simp only [ConstantInfo.toConstantVal, hlpNat]
  have hKS : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfS (by simp [hlpS]), hlpS]
  -- `Char` is a type in `univ 1`
  have hCharU : interp V ρ
      (m.acval ConLeche.charName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have hIH : ciH.toConstantVal.type.instantiateLevelParams
        ciH.toConstantVal.levelParams []
        = Expr.sort (Level.succ Level.zero) := by
      rw [hlpH, hTH]
      simp [Expr.instantiateLevelParams, Level.subst]
    have hR : denoteMeta m.acval env φ 0
        (ciH.toConstantVal.type.instantiateLevelParams
          ciH.toConstantVal.levelParams []) = some ((.sort 1) : AnnotTerm) := by
      rw [hIH, denoteMeta_sort]
      rfl
    have h := (head _ _ _ _ hfH (ConLeche.isTowerEntry_false_of_find? hfH (fun _ _ h => by simp [ConLeche.charName] at h)) (by simp [hlpH]) hR).2 ρ
    rw [hlpH, interp_sort] at h
    exact h
  -- `List.nil`
  have hIN : ciN.toConstantVal.type.instantiateLevelParams
      ciN.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.app (.const ConLeche.listName [Level.zero]) (.bvar 0))
          ⟨Level.substPW [pN] [Level.zero] mbN.pw⟩ := by
    rw [hlpN, hTN]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRN : denoteMeta m.acval env φ 0
      (ciN.toConstantVal.type.instantiateLevelParams
        ciN.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pN] [Level.zero] mbN.pw))
          (.sort 1)
          (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (.bvar 0))) : AnnotTerm) := by
    rw [hIN, denoteMeta_forallE, denoteMeta_sort,
      show (Expr.app (.const ConLeche.listName [Level.zero]) (.bvar 0)).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteMeta_app, hKL, denoteMeta_fvar]
    rfl
  obtain ⟨hokRN, hmemRN⟩ := head _ _ _ _ hfN (ConLeche.isTowerEntry_false_of_find? hfN (fun _ _ h => by simp [ConLeche.listNilName] at h)) (by simp [hlpN]) hRN
  -- `List.cons`
  have hIC : ciC.toConstantVal.type.instantiateLevelParams
      ciC.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩)
          ⟨Level.substPW [pC] [Level.zero] mb1.pw⟩ := by
    rw [hlpC, hTC]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRC : denoteMeta m.acval env φ 0
      (ciC.toConstantVal.type.instantiateLevelParams
        ciC.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb1.pw))
          (.sort 1)
          (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb2.pw)) (.bvar 0)
            (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb3.pw))
              (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 1))
              (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 2))))) : AnnotTerm) := by
    rw [hIC, denoteMeta_forallE, denoteMeta_sort,
      show (Expr.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.forallE (.fvar 0 (Expr.sort (Level.succ Level.zero)))
            (.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩ from rfl,
      denoteMeta_forallE, denoteMeta_fvar,
      show (Expr.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩).instantiate1
          (.fvar (0 + 1) (.fvar 0 (Expr.sort (Level.succ Level.zero))))
        = Expr.forallE
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩ from rfl,
      denoteMeta_forallE, denoteMeta_app, hKL, denoteMeta_fvar,
      show (Expr.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))).instantiate1
          (.fvar (0 + 1 + 1)
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteMeta_app, hKL, denoteMeta_fvar]
    rfl
  obtain ⟨hokRC, hmemRC⟩ := head _ _ _ _ hfC (ConLeche.isTowerEntry_false_of_find? hfC (fun _ _ h => by simp [ConLeche.listConsName] at h)) (by simp [hlpC]) hRC
  -- `Char.ofNat`
  have hIF : ciF.toConstantVal.type.instantiateLevelParams
      ciF.toConstantVal.levelParams []
      = Expr.forallE (.const ConLeche.natName []) (.const ConLeche.charName [])
          ⟨Level.substPW [] [] mbF.pw⟩ := by
    rw [hlpF, hTF]
    simp [Expr.instantiateLevelParams]
  have hRF : denoteMeta m.acval env φ 0
      (ciF.toConstantVal.type.instantiateLevelParams
        ciF.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbF.pw))
          (m.acval ConLeche.natName (Level.substFn φ [] []))
          (m.acval ConLeche.charName (Level.substFn φ [] []))) : AnnotTerm) := by
    rw [hIF, denoteMeta_forallE, hKNat,
      show (Expr.const ConLeche.charName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.const ConLeche.natName []))
        = Expr.const ConLeche.charName [] from rfl, hKH]
    rfl
  obtain ⟨hokRF, hmemRF⟩ := head _ _ _ _ hfF (ConLeche.isTowerEntry_false_of_find? hfF (fun _ _ h => by simp [ConLeche.charOfNatName] at h)) (by simp [hlpF]) hRF
  -- `String.ofList`
  have hIO : ciO.toConstantVal.type.instantiateLevelParams
      ciO.toConstantVal.levelParams []
      = Expr.forallE
          (.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName []))
          (.const ConLeche.stringName [])
          ⟨Level.substPW [] [] mbO.pw⟩ := by
    rw [hlpO, hTO]
    simp [Expr.instantiateLevelParams, Level.subst]
  have hRO : denoteMeta m.acval env φ 0
      (ciO.toConstantVal.type.instantiateLevelParams
        ciO.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbO.pw))
          (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (m.acval ConLeche.charName (Level.substFn φ [] [])))
          (m.acval ConLeche.stringName
            (Level.substFn φ [] []))) : AnnotTerm) := by
    rw [hIO, denoteMeta_forallE, denoteMeta_app, hKL, hKH,
      show (Expr.const ConLeche.stringName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName [])))
        = Expr.const ConLeche.stringName [] from rfl, hKS]
    rfl
  obtain ⟨hokRO, hmemRO⟩ := head _ _ _ _ hfO (ConLeche.isTowerEntry_false_of_find? hfO (fun _ _ h => by simp [ConLeche.stringOfListName] at h)) (by simp [hlpO]) hRO
  -- the numeral heads
  obtain ⟨hz, hsucc⟩ := hnh hs ρ
  -- the chain
  obtain ⟨hclA, hclm⟩ :=
    charList_facts (V := V) (ρ := ρ)
      (KL := m.acval ConLeche.listName
        (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
      (KH := m.acval ConLeche.charName (Level.substFn φ [] []))
      (KN := m.acval ConLeche.listNilName
        (Level.substFn φ (levelParamsAt env ConLeche.listNilName) [Level.zero]))
      (KC := m.acval ConLeche.listConsName
        (Level.substFn φ (levelParamsAt env ConLeche.listConsName) [Level.zero]))
      (KF := m.acval ConLeche.charOfNatName (Level.substFn φ [] []))
      (Kz := m.acval ConLeche.natZeroName (Level.substFn φ [] []))
      (Ks := m.acval ConLeche.natSuccName (Level.substFn φ [] []))
      (KNat := m.acval ConLeche.natName (Level.substFn φ [] []))
      (fun σ => hleafC _ _ σ) (fun σ => hleafC _ _ σ)
      (hleafOk _ _ ρ) (hleafOk _ _ ρ) (hleafOk _ _ ρ) (hleafOk _ _ ρ)
      (hleafOk _ _ ρ) (hleafOk _ _ ρ) hCharU
      (hokRN ρ) (by rw [hlpAtN]; exact hmemRN ρ)
      (hokRC ρ) (by rw [hlpAtC]; exact hmemRC ρ)
      (hokRF ρ) (by
        have := hmemRF ρ
        rwa [hlpF] at this)
      hz hsucc s.toList
  -- the outer `String.ofList` application
  have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
    [charListAV
      (.app (m.acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName) [.zero]))
        (m.acval ConLeche.charName (Level.substFn φ [] [])))
      (.app (m.acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName) [.zero]))
        (m.acval ConLeche.charName (Level.substFn φ [] [])))
      (m.acval ConLeche.charOfNatName (Level.substFn φ [] []))
      (m.acval ConLeche.natZeroName (Level.substFn φ [] []))
      (m.acval ConLeche.natSuccName (Level.substFn φ [] []))
      s.toList]
    (hokRO ρ) (hleafOk _ _ ρ)
    (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hclA)
    (by
      have := hmemRO ρ
      rwa [hlpO] at this)
    (TeleFit.cons (by rw [interp_app]; exact hclm) TeleFit.nil)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [hleafC ConLeche.stringName (Level.substFn φ [] []) _] at h2

/-! ## `projAV`'s hoist (`Steps/ProjAVKit.lean:32`, `:41`, `:80`) -/

/-- The subject of a graded projection spine is graded. -/
theorem WellDenoted_projAV_hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (projAV i e) → WellDenoted V σ e
  | 0, e, σ, h => ((WellDenoted_fst V σ e) ▸ h).1
  | i + 1, e, σ, h =>
    ((WellDenoted_snd V σ e) ▸
      (WellDenoted_projAV_hoist (i := i) (e := .snd e) h)).1

/-- The subject of a bit-valid projection spine is bit-valid. -/
theorem AnnotValid_projAV_hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ (projAV i e) → AnnotValid V σ e
  | 0, e, σ, h => (AnnotValid_fst V σ e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValid_snd V σ e) ▸
      (AnnotValid_projAV_hoist (i := i) (e := .snd e) h)

/-- `WellDenotedV` of the subject, off the spine's. -/
theorem WellDenotedV_projAV_hoist {i : Nat} {e : AnnotTerm} {σ : Nat → V}
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ e :=
  ⟨WellDenoted_projAV_hoist hok.1, AnnotValid_projAV_hoist hok.2⟩

/-! ## The tower-entry kit (`Steps/TowerKit.lean`, `Steps/Stuck.lean`)

The `.proj` rule's reading walk, transplanted: the spine inversion,
the entry-kind inversion, and the fit-free residual — the checker's
`instPisAt` peel of the stored entry type reads to the syntactic peel
of its reading.  The spine relation and its algebra are
`Model/Annot/BitLemmas.lean`'s `DenoteMetaSpine`. -/

/-- **The checker's `instPisAt` peel reads to the syntactic peel of
the type's reading** — `teleFitPA_residual` without the fit: the two
walks step in lockstep (`body.instantiate1 a` against `B.inst a`), and
the per-step content is `denoteMeta_beta`, once. -/
theorem denoteMeta_instPisAt_peel
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {ds : List Expr} {Ta : AnnotTerm}
      {vs : List AnnotTerm},
      Expr.instPisAt args ty = some (ds, rest) →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteMeta acval env φ d ty = some Ta →
      DenoteMetaSpine acval env φ d args vs →
      ∃ restA, denoteMeta acval env φ d rest = some restA ∧
        AnnotTerm.peelPis Ta vs = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest ds Ta vs hpr _ _ hty hsp
    obtain ⟨-, rfl⟩ : ds = [] ∧ rest = ty := by
      simpa [Expr.instPisAt] using hpr.symm
    cases hsp
    exact ⟨Ta, hty, rfl⟩
  | cons a as ih =>
    intro ty rest ds Ta vs hpr hwty hargs hty hsp
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body mb, hpr, hwty, hty => ?_
    -- the peel's own step
    simp only [Expr.instPisAt, Option.map_eq_some_iff] at hpr
    obtain ⟨⟨ds', rest'⟩, hpr', heq⟩ := hpr
    obtain ⟨-, rfl⟩ : dom :: ds' = ds ∧ rest' = rest := by
      simpa using heq
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hty
    have hbody' : denoteMeta acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteMeta_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    obtain ⟨restA, hrestA, hpeel⟩ := ih hpr'
      (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hbody' hsp'
    exact ⟨restA, hrestA, hpeel⟩

/-- **The checker's projection type reads as the telescope's peel**
(task #175 S1): `ProjEntry.typeAt` is the `instPisAt` peel of the body
telescope along the arguments and the subject, so its reading is the
syntactic peel of the telescope's reading along the readings. -/
theorem denoteMeta_typeAt_peel {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm} {d : Nat}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta)
    {targs : List Expr} {pe : Expr} (hlen : targs.length = entry.numParams)
    (hframes : ∀ a ∈ targs ++ [pe], Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    {vs : List AnnotTerm}
    (hsp : DenoteMetaSpine m.acval env φ d (targs ++ [pe]) vs) :
    ∃ restA, denoteMeta m.acval env φ d (entry.typeAt us targs pe) = some restA ∧
      AnnotTerm.peelPis Ta vs = some restA := by
  obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
  exact denoteMeta_instPisAt_peel m.acval_closed (acval_inst_self m) (targs ++ [pe])
    (ConLeche.instPisAt_typeAt entry us hlen pe)
    (Expr.WScoped.of_not_hasFvar (towerEntry_tele_closed m.wf hfe us).1)
    hframes (hTad d) hsp

end ConLeche.Model.Rules
