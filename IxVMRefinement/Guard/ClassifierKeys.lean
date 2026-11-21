import IxC.Kernel.Model.ProjGuardCert
import IxC.Kernel.Verify.Cached.NormalizeRef

/-! # The field classifier queries only the keys its input and its answers name

The classifier (`GuardClassifier.head`, `infer`, `sortSignature`, and the telescope walks
`domainSignatures`, `fieldSignatures`) consults its lookup only at the key of a `const` node it
meets. Its operations on terms (`instantiate1Lift`, `liftLooseBVars`, and the level
instantiation and metadata erasure a dictionary applies to its answers) make no new key. So if
every answer at a key of a set `P` names only keys of `P`, a computation on an input that names
only keys of `P` queries only keys of `P`, and its result is the same over any lookup that keeps
the answers at those keys.

* `KeysIn P e`: every `const` key of `e` (a free variable's type included) satisfies `P`, with
  its preservation by the operations above.
* `KeysKept P a b`: `b` keeps `a`'s answers at the keys of `P`, and they name only keys of `P`.
* `head_keys`, `infer_keys`, `sortSignature_keys`, `domainSignatures_keys`,
  `fieldSignatures_keys`: a successful computation over `a` on such an input is the same
  computation over `b`.
-/

namespace IxVM.Refinement.Guard

open Ix.Kernel (Expr Key Level Mode)
open Ix.Kernel.GuardClassifier (Lookup head infer sortSignature domainSignatures fieldSignatures)

/-- **Every constant key of `e` satisfies `P`**, the type of a free variable included. -/
def KeysIn {md : Mode} (P : Key md → Prop) : Expr md → Prop
  | .bvar _ => True
  | .fvar _ ty => KeysIn P ty
  | .sort _ => True
  | .const k _ => P k
  | .app f a => KeysIn P f ∧ KeysIn P a
  | .lam ty b _ => KeysIn P ty ∧ KeysIn P b
  | .forallE ty b _ => KeysIn P ty ∧ KeysIn P b
  | .letE ty v b _ => KeysIn P ty ∧ KeysIn P v ∧ KeysIn P b
  | .lit _ => True
  | .proj _ _ e => KeysIn P e

theorem KeysIn.liftLooseBVars {md : Mode} {P : Key md → Prop} (amt : Nat) :
    ∀ (e : Expr md) (cut : Nat), KeysIn P e → KeysIn P (Expr.liftLooseBVars amt cut e)
  | .bvar _, cut, _ => by rw [Expr.liftLooseBVars]; split <;> trivial
  | .fvar _ _, _, h => h
  | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, cut, ⟨hf, ha⟩ =>
    ⟨KeysIn.liftLooseBVars amt f cut hf, KeysIn.liftLooseBVars amt a cut ha⟩
  | .lam ty b _, cut, ⟨ht, hb⟩ =>
    ⟨KeysIn.liftLooseBVars amt ty cut ht, KeysIn.liftLooseBVars amt b (cut + 1) hb⟩
  | .forallE ty b _, cut, ⟨ht, hb⟩ =>
    ⟨KeysIn.liftLooseBVars amt ty cut ht, KeysIn.liftLooseBVars amt b (cut + 1) hb⟩
  | .letE ty v b _, cut, ⟨ht, hv, hb⟩ =>
    ⟨KeysIn.liftLooseBVars amt ty cut ht, KeysIn.liftLooseBVars amt v cut hv,
      KeysIn.liftLooseBVars amt b (cut + 1) hb⟩
  | .proj _ _ e, cut, he => KeysIn.liftLooseBVars amt e cut he

theorem KeysIn.instantiate1Lift {md : Mode} {P : Key md → Prop} {v : Expr md}
    (hv : KeysIn P v) :
    ∀ (e : Expr md) (d : Nat), KeysIn P e → KeysIn P (e.instantiate1Lift v d)
  | .bvar _, d, _ => by
    rw [Expr.instantiate1Lift]
    split
    · exact KeysIn.liftLooseBVars d v 0 hv
    · split <;> trivial
  | .fvar _ _, _, h => h
  | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, d, ⟨hf, ha⟩ =>
    ⟨KeysIn.instantiate1Lift hv f d hf, KeysIn.instantiate1Lift hv a d ha⟩
  | .lam ty b _, d, ⟨ht, hb⟩ =>
    ⟨KeysIn.instantiate1Lift hv ty d ht, KeysIn.instantiate1Lift hv b (d + 1) hb⟩
  | .forallE ty b _, d, ⟨ht, hb⟩ =>
    ⟨KeysIn.instantiate1Lift hv ty d ht, KeysIn.instantiate1Lift hv b (d + 1) hb⟩
  | .letE ty val b _, d, ⟨ht, hval, hb⟩ =>
    ⟨KeysIn.instantiate1Lift hv ty d ht, KeysIn.instantiate1Lift hv val d hval,
      KeysIn.instantiate1Lift hv b (d + 1) hb⟩
  | .proj _ _ e, d, he => KeysIn.instantiate1Lift hv e d he

theorem KeysIn.instantiateLevelParams {md : Mode} {P : Key md → Prop}
    (ks : List Ix.Kernel.LevelParam) (us : List Level) :
    ∀ (e : Expr md), KeysIn P e → KeysIn P (e.instantiateLevelParams ks us)
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h => h
  | .fvar _ ty, h => KeysIn.instantiateLevelParams ks us ty h
  | .app f a, ⟨hf, ha⟩ =>
    ⟨KeysIn.instantiateLevelParams ks us f hf, KeysIn.instantiateLevelParams ks us a ha⟩
  | .lam ty b _, ⟨ht, hb⟩ =>
    ⟨KeysIn.instantiateLevelParams ks us ty ht, KeysIn.instantiateLevelParams ks us b hb⟩
  | .forallE ty b _, ⟨ht, hb⟩ =>
    ⟨KeysIn.instantiateLevelParams ks us ty ht, KeysIn.instantiateLevelParams ks us b hb⟩
  | .letE ty v b _, ⟨ht, hv, hb⟩ =>
    ⟨KeysIn.instantiateLevelParams ks us ty ht, KeysIn.instantiateLevelParams ks us v hv,
      KeysIn.instantiateLevelParams ks us b hb⟩
  | .proj _ _ e, h => KeysIn.instantiateLevelParams ks us e h

theorem KeysIn.eraseMeta {md : Mode} {P : Key md → Prop} :
    ∀ (e : Expr md), KeysIn P e → KeysIn P e.eraseMeta
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h => h
  | .fvar _ ty, h => KeysIn.eraseMeta ty h
  | .app f a, ⟨hf, ha⟩ => ⟨KeysIn.eraseMeta f hf, KeysIn.eraseMeta a ha⟩
  | .lam ty b _, ⟨ht, hb⟩ => ⟨KeysIn.eraseMeta ty ht, KeysIn.eraseMeta b hb⟩
  | .forallE ty b _, ⟨ht, hb⟩ => ⟨KeysIn.eraseMeta ty ht, KeysIn.eraseMeta b hb⟩
  | .letE ty v b _, ⟨ht, hv, hb⟩ =>
    ⟨KeysIn.eraseMeta ty ht, KeysIn.eraseMeta v hv, KeysIn.eraseMeta b hb⟩
  | .proj _ _ e, h => KeysIn.eraseMeta e h

/-- **`b` keeps `a`'s answers at the keys of `P`, and those answers name only keys of `P`.** -/
structure KeysKept {md : Mode} (P : Key md → Prop) (a b : Lookup md) : Prop where
  typeOf : ∀ k us e, P k → a.typeOf k us = some e → b.typeOf k us = some e ∧ KeysIn P e
  valueOf : ∀ k us e, P k → a.valueOf k us = some e → b.valueOf k us = some e ∧ KeysIn P e

private theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {r : β}
    (h : x.bind f = some r) : ∃ y, x = some y ∧ f y = some r :=
  Option.bind_eq_some_iff.mp h

private theorem some_bind {α β : Type} {x : Option α} {f : α → Option β} {y : α} {r : β}
    (hx : x = some y) (hf : f y = some r) : x.bind f = some r :=
  Option.bind_eq_some_iff.mpr ⟨y, hx, hf⟩

section Transfer

variable {md : Mode} {P : Key md → Prop} {a b : Lookup md}

/-- **Head exposure on a term that names only keys of `P` is the same over `b`**, and its result
names only keys of `P`. -/
theorem head_keys (hk : KeysKept P a b) :
    ∀ fuel e r, KeysIn P e → head a fuel e = some r → head b fuel e = some r ∧ KeysIn P r := by
  intro fuel
  induction fuel with
  | zero => intro e r _ h; simp [head] at h
  | succ fuel ih =>
    intro e r he h
    cases e
    case sort u =>
      simp only [head] at h ⊢
      obtain rfl := Option.some.inj h
      exact ⟨rfl, he⟩
    case forallE ty body m =>
      simp only [head] at h ⊢
      obtain rfl := Option.some.inj h
      exact ⟨rfl, he⟩
    case lam ty body m =>
      simp only [head] at h ⊢
      obtain rfl := Option.some.inj h
      exact ⟨rfl, he⟩
    case const k us =>
      simp only [head] at h ⊢
      obtain ⟨v, hv, hr⟩ := bind_some h
      obtain ⟨hv', hkv⟩ := hk.valueOf k us v he hv
      obtain ⟨hr', hkr⟩ := ih v r hkv hr
      exact ⟨some_bind hv' hr', hkr⟩
    case app f x =>
      simp only [head] at h ⊢
      obtain ⟨y, hy, hr⟩ := bind_some h
      obtain ⟨hy', hky⟩ := ih f y he.1 hy
      cases y
      case lam ty body m =>
        obtain ⟨hr', hkr⟩ := ih _ r (KeysIn.instantiate1Lift he.2 body 0 hky.2) hr
        exact ⟨some_bind hy' hr', hkr⟩
      all_goals exact absurd hr (by simp)
    case letE ty value body m =>
      simp only [head] at h ⊢
      exact ih _ r (KeysIn.instantiate1Lift he.2.1 body 0 he.2.2) h
    all_goals simp [head] at h

/-- **Structural inference on a term and a context that name only keys of `P` is the same over
`b`**, and its result names only keys of `P`. -/
theorem infer_keys (hk : KeysKept P a b) :
    ∀ fuel ctx e r, (∀ x ∈ ctx, KeysIn P x) → KeysIn P e →
      infer a fuel ctx e = some r → infer b fuel ctx e = some r ∧ KeysIn P r := by
  intro fuel
  induction fuel with
  | zero => intro ctx e r _ _ h; simp [infer] at h
  | succ fuel ih =>
    intro ctx e r hctx he h
    cases e
    case sort u =>
      simp only [infer] at h ⊢
      obtain rfl := Option.some.inj h
      exact ⟨rfl, trivial⟩
    case bvar i =>
      simp only [infer] at h ⊢
      refine ⟨h, ?_⟩
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
      exact KeysIn.liftLooseBVars (i + 1) x 0 (hctx x (List.mem_of_getElem? hx))
    case fvar idx ty =>
      simp only [infer] at h ⊢
      obtain rfl := Option.some.inj h
      exact ⟨rfl, he⟩
    case const k us =>
      simp only [infer] at h ⊢
      exact hk.typeOf k us r he h
    case app f x =>
      simp only [infer] at h ⊢
      obtain ⟨tf, htf, h⟩ := bind_some h
      obtain ⟨htf', hktf⟩ := ih ctx f tf hctx he.1 htf
      obtain ⟨y, hy, hr⟩ := bind_some h
      obtain ⟨hy', hky⟩ := head_keys hk fuel tf y hktf hy
      refine ⟨some_bind htf' (some_bind hy' hr), ?_⟩
      cases y
      case forallE ty body m =>
        obtain rfl := Option.some.inj hr
        exact KeysIn.instantiate1Lift he.2 body 0 hky.2
      all_goals exact absurd hr (by simp)
    case forallE ty body m =>
      simp only [infer] at h ⊢
      have hctx' : ∀ x ∈ ty :: ctx, KeysIn P x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hctx x hx
      obtain ⟨tb, htb, h⟩ := bind_some h
      obtain ⟨htb', hktb⟩ := ih (ty :: ctx) body tb hctx' he.2 htb
      obtain ⟨y, hy, hr⟩ := bind_some h
      obtain ⟨hy', -⟩ := head_keys hk fuel tb y hktb hy
      refine ⟨some_bind htb' (some_bind hy' hr), ?_⟩
      cases y
      case sort u =>
        obtain rfl := Option.some.inj hr
        trivial
      all_goals exact absurd hr (by simp)
    case lam ty body m =>
      simp only [infer] at h ⊢
      have hctx' : ∀ x ∈ ty :: ctx, KeysIn P x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hctx x hx
      obtain ⟨tb, htb, hr⟩ := bind_some h
      obtain ⟨htb', hktb⟩ := ih (ty :: ctx) body tb hctx' he.2 htb
      refine ⟨some_bind htb' hr, ?_⟩
      obtain rfl := Option.some.inj hr
      exact ⟨he.1, hktb⟩
    case letE ty value body m =>
      simp only [infer] at h ⊢
      exact ih ctx _ r hctx (KeysIn.instantiate1Lift he.2.1 body 0 he.2.2) h
    all_goals simp [infer] at h

/-- **A field signature on such a term and context is the same over `b`.** -/
theorem sortSignature_keys (hk : KeysKept P a b) {fuel : Nat} {ctx : List (Expr md)}
    {e : Expr md} {s : Level} (hctx : ∀ x ∈ ctx, KeysIn P x) (he : KeysIn P e)
    (h : sortSignature a fuel ctx e = some s) : sortSignature b fuel ctx e = some s := by
  unfold sortSignature at h ⊢
  obtain ⟨t, ht, h⟩ := bind_some h
  obtain ⟨ht', hkt⟩ := infer_keys hk fuel ctx e t hctx he ht
  obtain ⟨y, hy, hr⟩ := bind_some h
  obtain ⟨hy', -⟩ := head_keys hk fuel t y hkt hy
  exact some_bind ht' (some_bind hy' hr)

/-- **The signatures of a telescope's next domains are the same over `b`.** -/
theorem domainSignatures_keys (hk : KeysKept P a b) {fuel : Nat} :
    ∀ (n : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      (∀ x ∈ ctx, KeysIn P x) → KeysIn P e →
      domainSignatures a fuel n ctx e = some l → domainSignatures b fuel n ctx e = some l := by
  intro n
  induction n with
  | zero => intro ctx e l _ _ h; exact h
  | succ n ih =>
    intro ctx e l hctx he h
    cases e <;> simp only [domainSignatures] at h ⊢
    case forallE dom body m =>
      have hctx' : ∀ x ∈ dom :: ctx, KeysIn P x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hctx x hx
      obtain ⟨s, hs, hr⟩ := bind_some h
      obtain ⟨l', hl', hcons⟩ := Option.map_eq_some_iff.mp hr
      exact some_bind (sortSignature_keys hk hctx he.1 hs)
        (Option.map_eq_some_iff.mpr ⟨l', ih _ _ _ hctx' he.2 hl', hcons⟩)
    all_goals first | exact h | exact nomatch h

/-- **The signatures of a constructor telescope's fields are the same over `b`.** -/
theorem fieldSignatures_keys (hk : KeysKept P a b) {fuel : Nat} :
    ∀ (nP nF : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      (∀ x ∈ ctx, KeysIn P x) → KeysIn P e →
      fieldSignatures a fuel nP nF ctx e = some l → fieldSignatures b fuel nP nF ctx e = some l := by
  intro nP
  induction nP with
  | zero => intro nF ctx e l hctx he h; exact domainSignatures_keys hk nF ctx e l hctx he h
  | succ nP ih =>
    intro nF ctx e l hctx he h
    cases e <;> simp only [fieldSignatures] at h ⊢
    case forallE dom body m =>
      have hctx' : ∀ x ∈ dom :: ctx, KeysIn P x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hctx x hx
      exact ih nF _ _ l hctx' he.2 h
    all_goals first | exact h | exact nomatch h

end Transfer

end IxVM.Refinement.Guard
