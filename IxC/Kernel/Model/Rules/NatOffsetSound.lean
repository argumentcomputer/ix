module

public import IxC.Kernel.Model.Rules.Inputs
public import IxC.Kernel.Rules.NatOffset
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.Rules.DefEqSoundKit
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.NatAddRec
import IxC.Kernel.Semantics.LitStep
import IxC.Kernel.Model.Annot.ValidSpine
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Subst

public section

/-!
# The `Nat` offset rules are sound

`Red.natAddSucc`, `Red.natAddZero` and `DefEq.natOffset` read a `Nat` term as an
offset `base + k`. In the model `base + k` is the `k`-fold successor of the base
(`succPow`): `Nat.add x (lit k)` interprets as `succᵏ x` for every `x` in `Nat`, by
`Nat.add`'s two recurrences (`NatOps`, through `natAdd_clauses`) and induction on
`k` (`natAdd_succPow`), and a literal `n` is `succⁿ 0` (`interp_natLitAV`).

The recurrences hold of members of `Nat` only. The first argument of a `Nat.add`
application is one: its slot in the graded subject transfers to the stored
`Nat.add`'s domain, because that domain sits at a graph-regime binder
(`natAddTyOk`, `slotTransfer`). The second argument is a literal. The successor's
argument is a member of `Nat` through the successor's own type (`NatHeads`).

No new model input: `ConstType`, `NatOps`, `NatHeads` and `AcvalValid` are
`RulesInputs` fields. The argument congruence `Red.appArg` is here too: an
application's grading reads its argument only through the argument's value.
-/

namespace Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantInfo ConstantVal ReducibilityHint BinderMeta)
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {m : EnvModel V env}
  {φ : LevelParam → Nat}

/-! ## The argument congruence -/

/-- **`Red.appArg` is sound**: an application's grading reads its argument only
through the argument's value (`appCongrV`). -/
theorem Red.appArg_sound {d : Nat} {f a a' : Expr md}
    (ha : RedSem m φ d a a') : RedSem m φ d (.app f a) (.app f a') := by
  intro hf Δa ea hC hea hg
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨hgf, hga⟩ := Graded.app hg
  obtain ⟨⟨hwa', hba', hLa'⟩, hsuba, aa', haa', hga', heqa⟩ :=
    ha hf.app_arg hC.app_arg haa hga
  have hff := hf.app_fn
  refine ⟨⟨?_, ?_, ?_⟩, ?_, .app fa aa', by rw [denoteMeta_app, hfa, haa']; rfl,
    fun ρ hρ => appCongrV rfl (heqa ρ hρ) (hgf ρ hρ) (hga' ρ hρ) (hg ρ hρ),
    fun ρ hρ => by rw [interp_app, interp_app, heqa ρ hρ]⟩
  · simp only [Expr.WScoped]
    exact ⟨hff.1, hwa'⟩
  · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hff.2.1, hba'⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hff.2.2 l hl
    · exact hLa' l hl
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl hl
    · exact Or.inr (hsuba l hl)

/-! ## Frames -/

theorem Frame.mk_app {d : Nat} {f a : Expr md} (hf : Frame d f) (ha : Frame d a) :
    Frame d (.app f a) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.WScoped]
    exact ⟨hf.1, ha.1⟩
  · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hf.2.1, ha.2.1⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hf.2.2 l hl
    · exact ha.2.2 l hl

theorem frame_const (d : Nat) (c : Key md) (us : List Level) : Frame d (.const c us) :=
  (frame_atom (d := d) (e := (.const c us : Expr md)) (by simp [Expr.fvarLeaves])
    (by simp [Expr.WScoped]) (by simp [Expr.looseBVarsBounded])).1

theorem frame_natLit (d n : Nat) : Frame d (.lit (.natVal n) : Expr md) :=
  (frame_atom (d := d) (e := (.lit (.natVal n) : Expr md)) (by simp [Expr.fvarLeaves])
    (by simp [Expr.WScoped]) (by simp [Expr.looseBVarsBounded])).1

theorem frame_natAddLit {d : Nat} {b : Expr md} (hb : Frame d b) (k : Nat) :
    Frame d (natAddLit b k) := by
  cases k with
  | zero => rw [natAddLit_zero]; exact hb
  | succ k =>
    rw [natAddLit_succ]
    exact Frame.mk_app (Frame.mk_app (frame_const d _ _) hb) (frame_natLit d _)

theorem leavesSub_natAddLit (b : Expr md) (k : Nat) : LeavesSub (natAddLit b k) b := by
  intro l hl
  cases k with
  | zero => rw [natAddLit_zero] at hl; exact hl
  | succ k =>
    rw [natAddLit_succ] at hl
    simpa [Expr.fvarLeaves] using hl

/-! ## Successor powers -/

/-- `sᵏ x`: the `k`-fold application of a successor value. -/
@[expose] noncomputable def succPow (s x : V) : Nat → V
  | 0 => x
  | k + 1 => SetTheory.app s (succPow s x k)

theorem succPow_zero (s x : V) : succPow s x 0 = x := rfl

theorem succPow_succ (s x : V) (k : Nat) :
    succPow s x (k + 1) = SetTheory.app s (succPow s x k) := rfl

theorem succPow_one (s x : V) : succPow s x 1 = SetTheory.app s x := rfl

theorem succPow_add (s x : V) (j : Nat) :
    ∀ k, succPow s (succPow s x j) k = succPow s x (j + k)
  | 0 => rfl
  | k + 1 => congrArg (SetTheory.app s) (succPow_add s x j k)

/-- A literal is a successor power of zero. -/
theorem interp_natLitAV (ρ : Nat → V) (za sa : AnnotTerm) :
    ∀ n, interp V ρ (natLitAV za sa n) = succPow (interp V ρ sa) (interp V ρ za) n
  | 0 => rfl
  | n + 1 => congrArg (SetTheory.app (interp V ρ sa)) (interp_natLitAV ρ za sa n)

/-! ## Literals -/

/-- The numeral spine at the plain assignment's `Nat` leaves. -/
@[expose] def natLitR (m : EnvModel V env) (φ : LevelParam → Nat) (n : Nat) : AnnotTerm :=
  natLitAV (m.acval natZeroName φ) (m.acval natSuccName φ) n

/-- A literal reads to the spine. -/
theorem denoteMeta_natLitR (hs : natLitSupported env = true) (d n : Nat) :
    denoteMeta m.acval env φ d (.lit (.natVal n)) = some (natLitR m φ n) := by
  rw [denoteMeta_natLit hs, show Level.substFn φ [] [] = φ from funext fun _ => rfl]
  rfl

/-- Numerals are graded members of `Nat` (`natLit_factsAV` at the stored heads). -/
theorem natLitR_facts (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    (ρ : Nat → V) (n : Nat) :
    WellDenotedV V ρ (natLitR m φ n) ∧
      interp V ρ (natLitR m φ n) ∈ˢ interp V ρ (m.acval natName φ) := by
  obtain ⟨hz, hsucc⟩ := hin.nat_heads hs ρ
  rw [show Level.substFn φ [] [] = φ from funext fun _ => rfl] at hz hsucc
  have h := natLit_factsAV (V := V) (za := m.acval natZeroName φ)
    (sa := m.acval natSuccName φ) (natA := m.acval natName φ)
    (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ) hz hsucc n
  exact ⟨⟨h.1, AnnotValid_natLitAV (hin.leaf_valid _ _ ρ) (hin.leaf_valid _ _ ρ) n⟩, h.2⟩

/-- Whatever `rawNatLit?` accepts reads to the numeral it reports. -/
theorem denoteMeta_rawNatLitR (hs : natLitSupported env = true) {w : Expr md} {n : Nat}
    (h : Ix.Kernel.rawNatLit? w = some n) (d : Nat) :
    denoteMeta m.acval env φ d w = some (natLitR m φ n) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN, hlpZ, hlpS, -⟩ :=
    Ix.Kernel.natLitSupported_inv hs
  match w, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denoteMeta_natLitR hs d k
  | .const c [], h =>
    simp only [Ix.Kernel.rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      exact denoteMeta_leaf hfZ
        (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams = [] from hlpZ)
    · exact nomatch h

/-- The pinned type `Nat → Nat → Nat`, read at its binder data. -/
theorem denoteMeta_natBinTy (hs : natLitSupported env = true) (mb₁ mb₂ : BinderMeta) :
    denoteMeta m.acval env φ 0 (.forallE (.const natName [])
        (.forallE (.const natName []) (.const natName []) mb₂) mb₁) =
      some (.pi 0 (pwBit φ mb₁.pw) (m.acval natName φ)
        (.pi 0 (pwBit φ mb₂.pw) (m.acval natName φ) (m.acval natName φ))) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN, hlpZ, hlpS, -⟩ :=
    Ix.Kernel.natLitSupported_inv hs
  have hN : ∀ d : Nat, denoteMeta m.acval env φ d (.const natName []) =
      some (m.acval natName φ) := fun d =>
    denoteMeta_leaf hfN
      (show (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams = [] from hlpN)
  rw [denoteMeta_forallE, hN]
  rw [show (Expr.forallE (.const natName []) (.const natName []) mb₂ : Expr md).instantiate1
        (.fvar 0 (.const natName [])) = .forallE (.const natName []) (.const natName []) mb₂
      from Ix.Kernel.Expr.instantiate1_eq_self (by simp [Ix.Kernel.Expr.looseBVarsBounded])]
  rw [denoteMeta_forallE, hN]
  rw [show (Expr.const natName [] : Expr md).instantiate1 (.fvar 1 (.const natName [])) =
        .const natName []
      from Ix.Kernel.Expr.instantiate1_eq_self (by simp [Ix.Kernel.Expr.looseBVarsBounded])]
  rw [hN]
  rfl

/-! ## The stored heads -/

/-- A stored constant without level parameters reads only at no level arguments, to
its leaf. -/
theorem denoteMeta_levelless_inv {d : Nat} {c : Key md} {ci : ConstantInfo md}
    {us : List Level} {r : AnnotTerm}
    (hf : env.find? c = some ci) (hlp : ci.toConstantVal.levelParams = [])
    (h : denoteMeta m.acval env φ d (.const c us) = some r) :
    us = [] ∧ r = m.acval c φ := by
  have h0 := h
  rw [denoteMeta, hf] at h0
  dsimp only at h0
  split at h0
  · next hlen =>
    have hus : us = [] := List.eq_nil_of_length_eq_zero (hlen.trans (by simp [hlp]))
    subst hus
    exact ⟨rfl, (Option.some.inj ((denoteMeta_leaf hf hlp).symm.trans h)).symm⟩
  · exact nomatch h0

/-- The successor's leaf: read, and a function from `Nat` to `Nat` in the graph
regime (`NatHeads`). -/
theorem natSucc_leaf (hin : RulesInputs V m φ) (hs : natLitSupported env = true) :
    (∀ {d : Nat} {us : List Level} {r : AnnotTerm},
      denoteMeta m.acval env φ d (.const natSuccName us) = some r →
        us = [] ∧ r = m.acval natSuccName φ) ∧
    (∀ d : Nat, denoteMeta m.acval env φ d (.const natSuccName []) =
      some (m.acval natSuccName φ)) ∧
    ∀ ρ : Nat → V, interp V ρ (m.acval natSuccName φ) ∈ˢ
      piR 1 (interp V ρ (m.acval natName φ)) (fun _ => interp V ρ (m.acval natName φ)) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN, hlpZ, hlpS, -⟩ :=
    Ix.Kernel.natLitSupported_inv hs
  have hlp : (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams = [] := hlpS
  refine ⟨fun h => denoteMeta_levelless_inv hfS hlp h,
    fun d => denoteMeta_leaf hfS hlp, fun ρ => ?_⟩
  have h := (hin.nat_heads hs ρ).2
  rw [show Level.substFn φ [] [] = φ from funext fun _ => rfl] at h
  exact h

/-- **The stored `Nat.add`, as the offset rules read it** (`natAddTyOk`): a
definition without level parameters whose leaf is a function from `Nat` to
`Nat → Nat` with a graph-regime outer binder. -/
theorem natAdd_head (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) :
    (∃ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
      env.find? natAddName = some (.defnInfo cv v hint) ∧ cv.levelParams = []) ∧
    ∃ b₁ b₂ : Nat, b₁ ≠ 0 ∧ ∀ ρ : Nat → V,
      interp V ρ (m.acval natAddName φ) ∈ˢ
        piR b₁ (interp V ρ (m.acval natName φ))
          (fun _ => piR b₂ (interp V ρ (m.acval natName φ))
            (fun _ => interp V ρ (m.acval natName φ))) ∧
      (b₂ = 0 → ∀ x, x ∈ˢ interp V ρ (m.acval natName φ) →
        interp V ρ (m.acval natName φ) ∈ˢ (univZero : V)) := by
  obtain ⟨n, v, hint, mb₁, mb₂, hf, hnev⟩ := natAddTyOk_inv ht
  refine ⟨⟨_, v, hint, hf, rfl⟩, pwBit φ mb₁.pw, pwBit φ mb₂.pw,
    pwBit_ne_zero_of_isNever hnev φ, fun ρ => ?_⟩
  -- the stored type's reading
  obtain ⟨ta, hta, hokT, hmem⟩ := hin.const_ty 0 natAddName _ [] hf rfl rfl
  have hT : (Expr.forallE (.const natName []) (.forallE (.const natName [])
      (.const natName []) mb₂) mb₁ : Expr md).instantiateLevelParams [] [] =
      .forallE (.const natName []) (.forallE (.const natName []) (.const natName []) mb₂) mb₁ :=
    Ix.Kernel.Expr.instantiateLevelParams_self [] _
  have hta' : denoteMeta m.acval env φ 0
      (.forallE (.const natName []) (.forallE (.const natName []) (.const natName []) mb₂)
        mb₁) = some ta := by
    rw [← hT]
    exact hta
  have hta0 := denoteMeta_natBinTy (m := m) (φ := φ) hs mb₁ mb₂
  obtain rfl := Option.some.inj (hta'.symm.trans hta0)
  have hm := hmem ρ
  simp only [Ix.Kernel.ConstantInfo.toConstantVal,
    show Level.substFn φ [] [] = φ from funext fun _ => rfl] at hm
  refine ⟨?_, ?_⟩
  · rw [interp_pi] at hm
    have hfib : (fun x => interp V (cons x ρ)
          ((.pi 0 (pwBit φ mb₂.pw) (m.acval natName φ) (m.acval natName φ)) : AnnotTerm))
        = fun _ => piR (pwBit φ mb₂.pw) (interp V ρ (m.acval natName φ))
            (fun _ => interp V ρ (m.acval natName φ)) := by
      funext x
      rw [interp_pi]
      congr 1
      · exact leaf_interp_closed m _ φ _ ρ
      · funext y
        exact leaf_interp_closed m _ φ _ ρ
    rw [hfib] at hm
    exact hm
  · intro hz x hx
    have hv := (hokT ρ).2
    rw [AnnotValid_pi] at hv
    have hinner := hv.2.1 x hx
    rw [AnnotValid_pi] at hinner
    have h := hinner.2.2 hz x (by rw [leaf_interp_closed m _ φ (cons x ρ) ρ]; exact hx)
    rwa [leaf_interp_closed m _ φ _ ρ] at h

/-- **An applied `Nat.add`, read and graded**: the head has no level arguments and
reads to the leaf, and the first argument lies in `Nat` (`slotTransfer` at the
graph-regime outer binder). -/
theorem natAdd_app_inv (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) {d : Nat} {us : List Level}
    {b a : Expr md} {ea : AnnotTerm} {Δa : List AnnotTerm}
    (hea : denoteMeta m.acval env φ d (.app (.app (.const natAddName us) b) a) = some ea)
    (hg : Graded V Δa ea) :
    us = [] ∧ ∃ ba aa, denoteMeta m.acval env φ d b = some ba ∧
      denoteMeta m.acval env φ d a = some aa ∧
      ea = .app (.app (m.acval natAddName φ) ba) aa ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ba ∈ˢ interp V ρ (m.acval natName φ) := by
  obtain ⟨⟨cv, v, hint, hfA, hlpA⟩, b₁, b₂, hb₁, hhead⟩ := natAdd_head hin hs ht
  have hlp : (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams = [] := hlpA
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨ca, ba, hca, hba, rfl⟩ := denoteMeta_app_inv hfa
  obtain ⟨rfl, rfl⟩ := denoteMeta_levelless_inv hfA hlp hca
  refine ⟨rfl, ba, aa, hba, haa, rfl, fun ρ hρ => ?_⟩
  have h1 := (hg ρ hρ).1
  rw [WellDenoted_app] at h1
  obtain ⟨h2, -, -⟩ := h1
  rw [WellDenoted_app] at h2
  obtain ⟨-, -, v', A', B', hslot, hba', -⟩ := h2
  exact slotTransfer hb₁ (hhead ρ).1 hslot hba'

/-! ## `Nat.add` at a literal is a successor power -/

/-- **`Nat.add x (lit n)` is `succⁿ x`**, for `x` in `Nat`. -/
theorem natAdd_succPow (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    {cv : ConstantVal md} {v : Expr md} {hint : ReducibilityHint}
    (hf : env.find? natAddName = some (.defnInfo cv v hint)) (ρ : Nat → V) {x : V}
    (hx : x ∈ˢ interp V ρ (m.acval natName φ)) (n : Nat) :
    SetTheory.app (SetTheory.app (interp V ρ (m.acval natAddName φ)) x)
        (interp V ρ (natLitR m φ n)) =
      succPow (interp V ρ (m.acval natSuccName φ)) x n := by
  obtain ⟨h0, hS⟩ := natAdd_clauses m hin.nat_ops hin.nat_heads hf ρ
  induction n with
  | zero => exact h0 x hx
  | succ n ih =>
    have h1 := hS x (interp V ρ (natLitR m φ n)) hx
      (natLitR_facts hin hs ρ n).2
    rw [ih] at h1
    exact h1

/-- **`b + k` (`natAddLit`)**, at a graded member `⟦b⟧` of `Nat`: it reads, is
graded, lies in `Nat` and is `succᵏ ⟦b⟧`. -/
theorem natAddLit_sem (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) {d : Nat} {b : Expr md}
    {ba : AnnotTerm} {Δa : List AnnotTerm}
    (hba : denoteMeta m.acval env φ d b = some ba) (hgb : Graded V Δa ba)
    (hbN : ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ba ∈ˢ interp V ρ (m.acval natName φ))
    (k : Nat) :
    ∃ xa, denoteMeta m.acval env φ d (natAddLit b k) = some xa ∧ Graded V Δa xa ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ xa ∈ˢ interp V ρ (m.acval natName φ) ∧
        interp V ρ xa = succPow (interp V ρ (m.acval natSuccName φ)) (interp V ρ ba) k := by
  obtain ⟨⟨cv, v, hint, hfA, hlpA⟩, b₁, b₂, hb₁, hhead⟩ := natAdd_head hin hs ht
  have hlp : (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams = [] := hlpA
  cases k with
  | zero =>
    rw [natAddLit_zero]
    exact ⟨ba, hba, hgb, fun ρ hρ => ⟨hbN ρ hρ, rfl⟩⟩
  | succ k =>
    rw [natAddLit_succ]
    have key : ∀ ρ : Nat → V, Sat V Δa ρ →
        WellDenotedV V ρ (.app (.app (m.acval natAddName φ) ba) (natLitR m φ (k + 1))) ∧
        interp V ρ (.app (.app (m.acval natAddName φ) ba) (natLitR m φ (k + 1))) ∈ˢ
          interp V ρ (m.acval natName φ) := by
      intro ρ hρ
      have hAm := (hhead ρ).1
      have hAb : SetTheory.app (interp V ρ (m.acval natAddName φ)) (interp V ρ ba) ∈ˢ
          piR b₂ (interp V ρ (m.acval natName φ)) (fun _ => interp V ρ (m.acval natName φ)) :=
        app_mem_piR_pos hb₁ hAm (hbN ρ hρ)
      have hLk := natLitR_facts hin hs ρ (k + 1)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [WellDenoted_app, WellDenoted_app]
        exact ⟨⟨m.acval_wellDenoted _ _ ρ, (hgb ρ hρ).1, b₁, _, _, hAm, hbN ρ hρ,
            fun h => absurd h hb₁⟩,
          hLk.1.1, b₂, _, _, hAb, hLk.2, (hhead ρ).2⟩
      · rw [AnnotValid_app, AnnotValid_app]
        exact ⟨⟨hin.leaf_valid _ _ ρ, (hgb ρ hρ).2⟩, hLk.1.2⟩
      · rw [interp_app]
        exact app_mem_piR hAb hLk.2 (hhead ρ).2
    refine ⟨.app (.app (m.acval natAddName φ) ba) (natLitR m φ (k + 1)), ?_,
      fun ρ hρ => (key ρ hρ).1, fun ρ hρ => ⟨(key ρ hρ).2, ?_⟩⟩
    · rw [denoteMeta_app, denoteMeta_app, denoteMeta_leaf hfA hlp, hba,
        denoteMeta_natLitR hs d (k + 1)]
      rfl
    · exact natAdd_succPow hin hs hfA ρ (hbN ρ hρ) (k + 1)

/-! ## The two reduction rules -/

/-- **`Red.natAddSucc` is sound**: `Nat.add b (lit (k + 1))` and the successor of
`b + k` are both `succᵏ⁺¹ ⟦b⟧`. -/
theorem Red.natAddSucc_sound (hin : RulesInputs V m φ) {d : Nat} {us : List Level}
    {b : Expr md} {k : Nat} (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) :
    RedSem m φ d (.app (.app (.const natAddName us) b) (.lit (.natVal (k + 1))))
      (.app (.const natSuccName []) (natAddLit b k)) := by
  intro hf Δa ea hC hea hg
  obtain ⟨⟨cv, v, hint, hfA, -⟩, -⟩ := natAdd_head hin hs ht
  obtain ⟨-, hKs, hS⟩ := natSucc_leaf hin hs
  obtain ⟨rfl, ba, la, hba, hla, rfl, hbN⟩ := natAdd_app_inv hin hs ht hea hg
  obtain rfl : la = natLitR m φ (k + 1) :=
    Option.some.inj (hla.symm.trans (denoteMeta_natLitR hs d (k + 1)))
  have hfb : Frame d b := hf.app_fn.app_arg
  obtain ⟨hgAb, -⟩ := Graded.app hg
  obtain ⟨-, hgb⟩ := Graded.app hgAb
  obtain ⟨xa, hxa, hgx, hx⟩ := natAddLit_sem hin hs ht hba hgb hbN k
  have hgS : Graded V Δa (.app (m.acval natSuccName φ) xa) := by
    intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      exact ⟨m.acval_wellDenoted _ _ ρ, (hgx ρ hρ).1, 1, _, _, hS ρ, (hx ρ hρ).1,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [AnnotValid_app]
      exact ⟨hin.leaf_valid _ _ ρ, (hgx ρ hρ).2⟩
  refine ⟨Frame.mk_app (frame_const d _ _) (frame_natAddLit hfb k), fun l hl => ?_,
    .app (m.acval natSuccName φ) xa, by rw [denoteMeta_app, hKs d, hxa]; rfl, hgS,
    fun ρ hρ => ?_⟩
  · have hl' : l ∈ (natAddLit b k).fvarLeaves := by simpa [Expr.fvarLeaves] using hl
    have hlb := leavesSub_natAddLit b k l hl'
    simp [Expr.fvarLeaves, hlb]
  · simp only [interp_app]
    rw [(hx ρ hρ).2]
    exact natAdd_succPow hin hs hfA ρ (hbN ρ hρ) (k + 1)

/-- **`Red.natAddZero` is sound**: `Nat.add b a` at `⟦a⟧ = 0` is `⟦b⟧`. -/
theorem Red.natAddZero_sound (hin : RulesInputs V m φ) {d : Nat} {us : List Level}
    {b a w : Expr md} (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true)
    (hw : RedSem m φ d a w) (hn : rawNatLit? w = some 0) :
    RedSem m φ d (.app (.app (.const natAddName us) b) a) b := by
  intro hf Δa ea hC hea hg
  obtain ⟨⟨cv, v, hint, hfA, -⟩, -⟩ := natAdd_head hin hs ht
  obtain ⟨rfl, ba, aa, hba, haa, rfl, hbN⟩ := natAdd_app_inv hin hs ht hea hg
  obtain ⟨hgAb, hga⟩ := Graded.app hg
  obtain ⟨-, hgb⟩ := Graded.app hgAb
  obtain ⟨-, -, wa, hwa, -, heqw⟩ := hw hf.app_arg hC.app_arg haa hga
  obtain rfl : wa = natLitR m φ 0 :=
    Option.some.inj (hwa.symm.trans (denoteMeta_rawNatLitR hs hn d))
  refine ⟨hf.app_fn.app_arg, fun l hl => by simp [Expr.fvarLeaves, hl], ba, hba, hgb,
    fun ρ hρ => ?_⟩
  rw [interp_app, interp_app, heqw ρ hρ]
  exact natAdd_succPow hin hs hfA ρ (hbN ρ hρ) 0

/-! ## Offsets -/

/-- **An offset's meaning**: a framed, read, graded term with the offset
`(base, k)` is `succᵏ ⟦base⟧`; the base is framed, read and graded, and its leaves
are the term's. -/
theorem natOffsetOf_sem (hin : RulesInputs V m φ) (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) :
    ∀ (e : Expr md) {b : Expr md} {k : Nat}, natOffsetOf e = some (b, k) →
      ∀ {d : Nat} {Δa : List AnnotTerm} {ea : AnnotTerm}, Frame d e → CtxOk m φ d Δa e →
        denoteMeta m.acval env φ d e = some ea → Graded V Δa ea →
        Frame d b ∧ LeavesSub b e ∧ ∃ ba, denoteMeta m.acval env φ d b = some ba ∧
          Graded V Δa ba ∧ ∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ ea =
              succPow (interp V ρ (m.acval natSuccName φ)) (interp V ρ ba) k := by
  obtain ⟨hKinv, -, -⟩ := natSucc_leaf hin hs
  obtain ⟨⟨cv, v, hint, hfA, -⟩, -⟩ := natAdd_head hin hs ht
  refine natOffsetOf_rec (fun e ih => ?_)
  intro b k h d Δa ea hf hC hea hg
  rcases natOffsetOf_some h with ⟨rfl, rfl⟩ | ⟨us, x, rfl, hx⟩ | ⟨us, x, n, rfl, hx⟩
  · -- a literal: `succᵏ 0`
    obtain rfl : ea = natLitR m φ k :=
      Option.some.inj (hea.symm.trans (denoteMeta_natLitR hs d k))
    exact ⟨frame_natLit d 0, fun l hl => by simp [Expr.fvarLeaves] at hl, natLitR m φ 0,
      denoteMeta_natLitR hs d 0,
      fun ρ _ => (natLitR_facts hin hs ρ 0).1,
      fun ρ _ => interp_natLitAV ρ (m.acval natZeroName φ) (m.acval natSuccName φ) k⟩
  · -- `Nat.succ x`
    obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denoteMeta_app_inv hea
    obtain ⟨-, rfl⟩ := hKinv hfa
    obtain ⟨-, hgx⟩ := Graded.app hg
    have hfx : Frame d x := hf.app_arg
    have hCx : CtxOk m φ d Δa x := hC.app_arg
    have hsubx : LeavesSub x (.app (.const natSuccName us) x) :=
      fun l hl => by simp [Expr.fvarLeaves, hl]
    rcases natOffsetStep_eq hx with ⟨k', hx', rfl⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨hfb, hsubb, ba, hba, hgb, heq⟩ :=
        ih x (Or.inl ⟨us, rfl⟩) hx' hfx hCx hxa hgx
      refine ⟨hfb, fun l hl => hsubx l (hsubb l hl), ba, hba, hgb, fun ρ hρ => ?_⟩
      rw [interp_app, heq ρ hρ, succPow_succ]
    · refine ⟨hfx, hsubx, xa, hxa, hgx, fun ρ _ => ?_⟩
      rw [interp_app, succPow_one]
  · -- `Nat.add x (lit n)`
    obtain ⟨-, xa, la, hxa, hla, rfl, hxN⟩ := natAdd_app_inv hin hs ht hea hg
    obtain rfl : la = natLitR m φ n :=
      Option.some.inj (hla.symm.trans (denoteMeta_natLitR hs d n))
    obtain ⟨hgAx, -⟩ := Graded.app hg
    obtain ⟨-, hgx⟩ := Graded.app hgAx
    have hfx : Frame d x := hf.app_fn.app_arg
    have hCx : CtxOk m φ d Δa x := hC.app_fn.app_arg
    have hsubx : LeavesSub x (.app (.app (.const natAddName us) x) (.lit (.natVal n))) :=
      fun l hl => by simp [Expr.fvarLeaves, hl]
    have hadd : ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ (.app (.app (m.acval natAddName φ) xa) (natLitR m φ n)) =
          succPow (interp V ρ (m.acval natSuccName φ)) (interp V ρ xa) n :=
      fun ρ hρ => natAdd_succPow hin hs hfA ρ (hxN ρ hρ) n
    rcases natOffsetStep_eq hx with ⟨k', hx', rfl⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨hfb, hsubb, ba, hba, hgb, heq⟩ :=
        ih x (Or.inr ⟨us, n, rfl⟩) hx' hfx hCx hxa hgx
      refine ⟨hfb, fun l hl => hsubx l (hsubb l hl), ba, hba, hgb, fun ρ hρ => ?_⟩
      rw [hadd ρ hρ, heq ρ hρ, succPow_add]
    · exact ⟨hfx, hsubx, xa, hxa, hgx, hadd⟩

/-- **`DefEq.natOffset` is sound**: both sides are `succᵏ` of their bases, and the
bases are equal. -/
theorem DefEq.natOffset_sound (hin : RulesInputs V m φ) {d : Nat} {a b ba bb : Expr md}
    {k : Nat} (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true)
    (ha : natOffsetOf a = some (ba, k)) (hb : natOffsetOf b = some (bb, k))
    (h : DefEqSem m φ d ba bb) : DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba' hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨hfA, hsubA, xa, hxa, hgA, heqA⟩ := natOffsetOf_sem hin hs ht a ha hfa hCa haa hga
  obtain ⟨hfB, hsubB, xb, hxb, hgB, heqB⟩ := natOffsetOf_sem hin hs ht b hb hfb hCb hba hgb
  rw [heqA ρ hρ, heqB ρ hρ,
    h hfA hfB (hCa.of_subset hsubA) (hCb.of_subset hsubB) hxa hxb hgA hgB ρ hρ]

end Ix.Kernel.Model.Rules
