import IxCC.Lam.Erase.Proof.SimBase
import IxCC.Lam.Erase.Proof.Values

/-! # Saturated special heads after their arguments

Once a saturated spine's arguments are bound (SrcEval's slots; Lam's `let`s
and `Ref`s), SrcEval fires the head and Lam evaluates the form erasure put
in its place. These lemmas relate the two for each head, needing only
lower clock bounds (every nested evaluation follows a charge). The
same lemmas serve saturated spines in place and wrapper bodies, whose
arguments are variables bound to values. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- A bound argument's reference against SrcEval's slot for it: □ is
`irr`, a level holds a related value, a by-name argument is its thunk. -/
inductive RefSlot (I : Input) (G : Key.GKey → GlobalId → Prop) (ls : Levels) (ρ : Src.Env)
    (ρ'' : Env) : Ref → Src.Slot → Prop
  | box {s : Src.Slot} : IrrSlot s → RefSlot I G ls ρ ρ'' .box s
  | lvl {l : Nat} {v : Src.Value} {v' : Val} :
      l < ρ''.length → ρ''[ρ''.length - 1 - l]? = some (.val v') → VR I G v v' →
      RefSlot I G ls ρ ρ'' (.lvl l) (.val v)
  | name {a : Src.Term} : RefSlot I G ls ρ ρ'' (.name a) (.name a ρ ls)

/-- The references agree with the slots wherever the head reads. -/
structure FormArgs (I : Input) (G : Key.GKey → GlobalId → Prop) (h : Head) (ls : Levels)
    (ρ : Src.Env) (ρ'' : Env) (refs : List Ref) (ss : List Src.Slot) : Prop where
  length : ss.length = refs.length
  at_ : ∀ i ref s, refs[i]? = some ref → ss[i]? = some s → headReads I h i = true →
    RefSlot I G ls ρ ρ'' ref s

/-- Reading a level reference is free and gives the related value. -/
theorem RefSlot.eval_lvl {P : Program} {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {cx : Cx}
    {l : Nat} {s : Src.Slot} (h : RefSlot I G ls ρ ρ'' (.lvl l) s) (hd : cx.depth = ρ''.length)
    (k : Nat) :
    ∃ v v', s = .val v ∧ Lam.eval P k ρ'' (cx.lvl l) = .ok v' ∧ VR I G v v' := by
  cases h with
  | lvl _ hg hv =>
    refine ⟨_, _, rfl, ?_, hv⟩
    rw [Cx.lvl_eq, hd, Lam.eval_var_of P k ρ'' hg, Lam.force_val]

/-- A reference that is not a thunk evaluates freely to a value related to
its slot's (forced) value. -/
theorem RefSlot.eval_ref {P : Program} {p : Src.Program} {ls : Levels} {ρ : Src.Env} {ρ'' : Env}
    {cx : Cx} {ref : Ref} {s : Src.Slot} {e : Term} (h : RefSlot I G ls ρ ρ'' ref s)
    (hr : RefR I G cx ref e) (hn : ∀ a, ref ≠ .name a) (hd : cx.depth = ρ''.length) :
    ∃ v v', VR I G v v' ∧ ∀ k, Src.force p k s = .ok v ∧ Lam.eval P k ρ'' e = .ok v' := by
  cases hr with
  | box =>
    cases h with
    | box hs =>
      obtain ⟨t, ρ₀, ls₀, rfl⟩ := hs
      exact ⟨_, _, VR.irr, fun k => ⟨Src.force_val p k _, Lam.eval_box' P k ρ''⟩⟩
  | lvl =>
    cases h with
    | lvl _ hg hv =>
      exact ⟨_, _, hv, fun k => ⟨Src.force_val p k _,
        by rw [Cx.lvl_eq, hd, Lam.eval_var_of P k ρ'' hg, Lam.force_val]⟩⟩
  | name _ => exact absurd rfl (hn _)

namespace Setting

variable (S : Setting)

theorem isQuotCtor_iff (c : CId) :
    S.p.isQuotCtor c = true ↔ ∃ lv ty, S.p.decl? c = some (.quot .ctor lv ty) := by
  simp only [Src.Program.isQuotCtor]
  split
  · next lv ty h => exact ⟨fun _ => ⟨lv, ty, h⟩, fun _ => rfl⟩
  · next h =>
    constructor
    · intro h'; cases h'
    · rintro ⟨lv, ty, h'⟩; exact absurd h' (h lv ty)

theorem vr_quot_inv {c : CId} {ls : Levels} {ps : List Src.Slot} {a : Src.Value} {v' : Val}
    {lv : Nat} {ty : Src.Term} (hq : S.I.decl? c = some (.quot .ctor lv ty))
    (h : VR S.I S.G (.con c ls ps [a]) v') : VR S.I S.G a v' := by
  cases h with
  | quot _ ha => exact ha
  | unboxed hd => rw [hq] at hd; cases hd
  | con hd => rw [hq] at hd; cases hd

/-- `Quot.mk α r a`: its element. -/
theorem quotMk_form {m : Nat} {c : CId} {lv : Nat} {ty : Src.Term}
    (hq : S.I.decl? c = some (.quot .ctor lv ty)) {ls ls' : Levels} {ρ : Src.Env} {ρ'' : Env}
    {cx : Cx} (hd : cx.depth = ρ''.length) {α r a : Src.Slot} {ref : Ref} {e : Term}
    (hs : RefSlot S.I S.G ls ρ ρ'' ref a) (hr : RefR S.I S.G cx ref e) (hn : ∀ a, ref ≠ .name a) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k (.quotMk c) ls' [α, r, a])
      (fun k => Lam.eval S.L k ρ'' e) := by
  obtain ⟨v, v', hvv, hk⟩ := hs.eval_ref hr hn hd (P := S.L) (p := S.p)
  refine (SimUpTo.ok (VR.quot (ls := ls') (ps := [α, r]) hq hvv)).congr (fun k => ?_)
    (fun k => (hk k).2)
  rw [Src.fire_quotMk]; dsimp only; rw [(hk k).1]; rfl

section

variable {S} {m : Nat} (hlt : ∀ m' < m, S.Level m')
include hlt

/-- `Quot.lift α r β f h q`: after the charge, `f` applied to `q`'s element. -/
theorem quotLift_form {c : CId} {ls ls' : Levels} {ρ : Src.Env} {ρ'' : Env} {cx : Cx}
    (hd : cx.depth = ρ''.length) {α r β fs h qs : Src.Slot} {reff refq : Ref} {f x : Term}
    (hsf : RefSlot S.I S.G ls ρ ρ'' reff fs) (hrf : RefR S.I S.G cx reff f)
    (hnf : ∀ a, reff ≠ .name a) (hsq : RefSlot S.I S.G ls ρ ρ'' refq qs)
    (hrq : RefR S.I S.G cx refq x) (hnq : ∀ a, refq ≠ .name a) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k (.quotLift c) ls' [α, r, β, fs, h, qs])
      (fun k => Lam.eval S.L k ρ'' (.tick (.app f x .strict))) := by
  obtain ⟨fv, fv', hfv, hkf⟩ := hsf.eval_ref hrf hnf hd (P := S.L) (p := S.p)
  obtain ⟨qv, qv', hqv, hkq⟩ := hsq.eval_ref hrq hnq hd (P := S.L) (p := S.p)
  refine (SimUpTo.later (n := m) (c₁ := fun k =>
      match qv with
      | .con c' _ _ [a] => if S.p.isQuotCtor c' then Src.apply S.p k fv (.val a) else .stuck
      | _ => .stuck)
    (c₂ := fun k => Lam.apply S.L k fv' (.val qv')) fun m' hm' => ?_).congr
    (fun k => ?_) (fun k => ?_)
  · have hap : S.ApplySim m' := (hlt m' (by omega)).apply
    cases qv with
    | con c' ls₀ ps fs₀ =>
      match fs₀ with
      | [a] =>
        dsimp only
        by_cases hq : S.p.isQuotCtor c' = true
        · simp only [hq, ↓reduceIte]
          obtain ⟨lv, ty, hdq⟩ := (S.isQuotCtor_iff c').1 hq
          exact hap hfv (SR.val (S.vr_quot_inv hdq hqv)) (.inr ⟨_, _, rfl, rfl⟩)
        · simp only [hq, Bool.false_eq_true, ↓reduceIte]
          exact SimUpTo.stuck _
      | [] | _ :: _ :: _ => exact SimUpTo.stuck _
    | _ => exact SimUpTo.stuck _
  · rw [Src.fire_quotLift]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      rw [(hkq k).1]
      cases qv with
      | con c' ls₀ ps fs₀ =>
        match fs₀ with
        | [a] =>
          simp only [Sem.Result.bind_ok]
          split
          · rw [(hkf k).1, Sem.Result.bind_ok]
          · rfl
        | [] | _ :: _ :: _ => rfl
      | _ => rfl
  · rw [Lam.eval_tick]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      rw [Lam.eval_app_strict, (hkf k).2, Sem.Result.bind_ok, (hkq k).2, Sem.Result.bind_ok]

end

/-! ## Primitive and Boolean results -/

section Pins

variable {S} (wf : ProgWF S.I)
include wf

omit wf in
/-- The alias is the identity away from `Decidable`'s constructors. -/
theorem alias_self {c : CId} (hf : ∀ d, S.I.known.decIsFalse = some d → c ≠ d)
    (ht : ∀ d, S.I.known.decIsTrue = some d → c ≠ d) : S.I.alias c = c := by
  simp only [Input.alias]
  split
  · next df dt bf bt hdf hdt _ _ =>
    have e₁ : (c == df) = false := beq_false_of_ne (hf df hdf)
    have e₂ : (c == dt) = false := beq_false_of_ne (ht dt hdt)
    simp [e₁, e₂]
  · rfl

/-- A constructor of an inductive other than `Decidable`'s is its own
alias. -/
theorem alias_of_other {c ind : CId} {sf : Bool} {lv cidx np nf : Nat} {ty : Src.Term}
    (hd : S.I.decl? c = some (.ctor sf lv ind cidx np nf ty))
    (hne : ∀ d sf' lv' ind' cidx' np' nf' ty', (S.I.known.decIsFalse = some d ∨
      S.I.known.decIsTrue = some d) → S.I.decl? d = some (.ctor sf' lv' ind' cidx' np' nf' ty') →
      ind ≠ ind') : S.I.alias c = c := by
  apply alias_self
  · intro d hdf e
    subst e
    obtain ⟨sf', lv', D, np', nf', ty', hdd⟩ := wf.decIsFalse hdf
    exact hne c _ _ _ _ _ _ _ (.inl hdf) hdd (by rw [hd] at hdd; cases hdd; rfl)
  · intro d hdt e
    subst e
    obtain ⟨sf', lv', D, np', nf', ty', hdd⟩ := wf.decIsTrue hdt
    exact hne c _ _ _ _ _ _ _ (.inr hdt) hdd (by rw [hd] at hdd; cases hdd; rfl)

/-- A pinned `Bool` constructor, as SrcEval and Lam build it. -/
theorem vr_bool {c : CId} (hc : S.I.known.boolFalse = some c ∨ S.I.known.boolTrue = some c) :
    VR S.I S.G (.con c [] [] []) (.con (.src c) []) := by
  obtain ⟨sf, lv, B, cidx, np, ty, hd, hother⟩ : ∃ sf lv B cidx np ty,
      S.I.decl? c = some (.ctor sf lv B cidx np 0 ty) ∧
      ∃ c', c' ≠ c ∧ ∃ sf' lv' cidx' np' ty', S.I.decl? c' = some (.ctor sf' lv' B cidx' np' 0 ty') := by
    rcases hc with h | h
    · obtain ⟨sf, lv, B, np, ty, hd, t, _, sf', lv', np', ty', ht⟩ := wf.boolFalse h
      refine ⟨sf, lv, B, 0, np, ty, hd, t, fun e => ?_, sf', lv', 1, np', ty', ht⟩
      subst e; rw [hd] at ht; cases ht
    · obtain ⟨sf, lv, B, np, ty, hd, f, _, sf', lv', np', ty', hf⟩ := wf.boolTrue h
      refine ⟨sf, lv, B, 1, np, ty, hd, f, fun e => ?_, sf', lv', 0, np', ty', hf⟩
      subst e; rw [hd] at hf; cases hf
  obtain ⟨c', hne, sf', lv', cidx', np', ty', hd'⟩ := hother
  have hu : S.I.unbox? B [] = none := by
    cases h : S.I.unbox? B [] with
    | none => rfl
    | some j =>
      obtain ⟨k, hk, _⟩ := unbox?_spec h
      have h₁ := wf.ctorIn hd
      have h₂ := wf.ctorIn hd'
      rw [hk] at h₁ h₂
      have e₁ : c = k := by
        cases cidx with
        | zero => simpa using h₁.symm
        | succ n => simp at h₁
      have e₂ : c' = k := by
        cases cidx' with
        | zero => simpa using h₂.symm
        | succ n => simp at h₂
      exact absurd (e₂.trans e₁.symm) hne
  have hk : S.I.ctorKey c = .src c := by
    simp only [Input.ctorKey]
    rw [alias_of_other wf hd]
    intro d sf₂ lv₂ ind₂ cidx₂ np₂ nf₂ ty₂ hdd hdecl
    exact (wf.decOther (d := c) hdd (match hc with | .inl h => .inl h | .inr h => .inr (.inl h))
      hdecl hd).symm
  rw [← hk]
  exact VR.con hd rfl hu .nil

omit wf in
/-- Literal arguments of related values are the same numbers. -/
theorem natArgs_of_litArgs :
    ∀ {xs : List Src.Value} {vs : List Val} {ns : List Nat}, Forall2 (VR S.I S.G) xs vs →
      Src.litArgs xs = some ns → Lam.natArgs vs = some ns
  | [], [], _, .nil, h => by simp [Src.litArgs] at h; subst h; rfl
  | x :: xs, v :: vs, ns, .cons hx hr, h => by
    cases x with
    | lit n =>
      cases hx
      simp only [Src.litArgs, Option.map_eq_some_iff] at h
      obtain ⟨ns', h', rfl⟩ := h
      simp [Lam.natArgs, natArgs_of_litArgs hr h']
    | _ => simp [Src.litArgs] at h

/-- A primitive's result on related arguments. -/
theorem prim_value_sim {m : Nat} (op : Src.PrimOp) {xs : List Src.Value} {vs : List Val}
    (h : Forall2 (VR S.I S.G) xs vs) :
    SimUpTo (VR S.I S.G) m (fun _ => Src.primValue S.p op xs)
      (fun _ => Lam.primResult S.L.known (Prim.ofSrc op) vs) := by
  simp only [Src.primValue]
  cases hl : Src.litArgs xs with
  | none => exact SimUpTo.stuck _
  | some ns =>
    dsimp only
    simp only [Lam.primResult, natArgs_of_litArgs h hl, prim_sem_ofSrc]
    cases he : op.evalLits ns with
    | none => exact SimUpTo.stuck _
    | some res =>
      cases res with
      | nat n => exact SimUpTo.ok VR.lit
      | bool b =>
        dsimp only
        simp only [Src.Program.boolValue, S.known, Input.lamKnown, input_known]
        cases b with
        | true =>
          simp only [↓reduceIte]
          cases hb : S.p.known.boolTrue with
          | none => exact SimUpTo.stuck _
          | some c => exact SimUpTo.ok (vr_bool wf (.inr (by simpa using hb)))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hb : S.p.known.boolFalse with
          | none => exact SimUpTo.stuck _
          | some c => exact SimUpTo.ok (vr_bool wf (.inl (by simpa using hb)))

end Pins

end Setting

/-! ## A minor applied to its fields -/

/-- The β guards of the first `n` λs of a term, at levels `ls`. -/
def peelOk (ls : Levels) : Nat → Src.Term → Bool
  | 0, _ => true
  | n + 1, .lam b _ t => b.propWhen.allowsBeta ls && peelOk ls n t
  | _ + 1, _ => true

theorem peelUpTo_le : ∀ (n : Nat) (t : Src.Term), (peelUpTo n t).1 ≤ n
  | 0, _ => by simp [peelUpTo]
  | n + 1, .lam _ _ b => by
    have := peelUpTo_le n b
    simp only [peelUpTo]; omega
  | _ + 1, .var _ | _ + 1, .sort _ | _ + 1, .const .. | _ + 1, .app .. | _ + 1, .pi ..
  | _ + 1, .letE .. | _ + 1, .proj .. | _ + 1, .natLit _ | _ + 1, .strLit _ => by
    simp [peelUpTo]

/-- Applying a closure to fields enters its λ-telescope as far as the
fields reach, one charge-free step per field (Src side). -/
theorem applyAll_clo_peel (p : Src.Program) (j : Nat) :
    ∀ (fs : List Src.Slot) (b : Src.Binder) (d body : Src.Term) (ρ : Src.Env) (ls : Levels),
      fs ≠ [] →
      Src.applyAll p (j + 1) (.clo b d body ρ ls) fs =
        if b.propWhen.allowsBeta ls && peelOk ls (peelUpTo (fs.length - 1) body).1 body then
          (Src.eval p j ls ((fs.take ((peelUpTo (fs.length - 1) body).1 + 1)).reverse ++ ρ)
            (peelUpTo (fs.length - 1) body).2).bind
            (Src.applyAll p (j + 1) · (fs.drop ((peelUpTo (fs.length - 1) body).1 + 1)))
        else .stuck
  | [], _, _, _, _, _, h => absurd rfl h
  | [f], b, d, body, ρ, ls, _ => by
    simp only [List.length_singleton, Nat.sub_self, peelUpTo, peelOk, Bool.and_true,
      Nat.zero_add, List.take_one, List.head?_cons, Option.toList_some, List.reverse_singleton,
      List.singleton_append, List.drop_one, List.tail_cons, Src.applyAll_cons, Src.apply_clo,
      later_succ]
    split <;> simp [Src.applyAll_nil, Sem.Result.bind]
  | f :: g :: rest, b, d, body, ρ, ls, _ => by
    rw [Src.applyAll_cons, Src.apply_clo]
    cases body with
    | lam b₂ d₂ body₂ =>
      have ih := applyAll_clo_peel p j (g :: rest) b₂ d₂ body₂ (f :: ρ) ls (by simp)
      simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
      simp only [peelUpTo, peelOk]
      split
      · next hb =>
        rw [later_succ, Src.eval_lam, Sem.Result.bind_ok, ih]
        simp only [hb, Bool.true_and]
        congr 2
        simp [List.take_succ_cons, List.reverse_cons, List.append_assoc]
      · next hb => simp [hb, Sem.Result.bind]
    | _ =>
      simp only [List.length_cons, Nat.add_sub_cancel, peelUpTo, peelOk, Bool.and_true,
        Nat.zero_add, List.take_succ_cons, List.take_zero, List.reverse_singleton,
        List.singleton_append, List.drop_succ_cons, List.drop_zero]
      split <;> simp [Sem.Result.bind]

/-- A by-name minor forced and applied to its fields: after the force's
charge, the body under the peeled λs, then the remaining fields (Src). -/
theorem force_applyAll_peel (p : Src.Program) (mt : Src.Term) (ρs : Src.Env) (lss : Levels)
    (fs : List Src.Slot) (j : Nat) :
    (Src.force p j (.name mt ρs lss)).bind (fun mv => Src.applyAll p j mv fs) =
      (later j fun j' =>
        if peelOk lss (peelUpTo fs.length mt).1 mt then
          Src.eval p j' lss ((fs.take (peelUpTo fs.length mt).1).reverse ++ ρs)
            (peelUpTo fs.length mt).2
        else .stuck).bind
        (fun v => Src.applyAll p j v (fs.drop (peelUpTo fs.length mt).1)) := by
  rw [Src.force_name]
  cases j with
  | zero => rfl
  | succ j =>
    simp only [later_succ]
    cases fs with
    | nil =>
      simp only [List.length_nil, peelUpTo, peelOk, ↓reduceIte, List.take_zero,
        List.reverse_nil, List.nil_append, List.drop_zero]
    | cons f rest =>
      cases mt with
      | lam b₁ d₁ mt₁ =>
        rw [Src.eval_lam, Sem.Result.bind_ok, applyAll_clo_peel p j _ _ _ _ _ _ (by simp)]
        simp only [List.length_cons, Nat.add_sub_cancel, peelUpTo, peelOk]
        split <;> simp_all [Sem.Result.bind]
      | _ =>
        simp [peelUpTo, peelOk]

/-- A case-bound field's level against SrcEval's field slot: a level holds
a related value, □ stands for an `irr` field. -/
inductive FieldSlot (I : Input) (G : Key.GKey → GlobalId → Prop) (ρ₀ : Env) :
    Option Nat → Src.Slot → Prop
  | lvl {l : Nat} {v : Src.Value} {v' : Val} :
      l < ρ₀.length → ρ₀[ρ₀.length - 1 - l]? = some (.val v') → VR I G v v' →
      FieldSlot I G ρ₀ (some l) (.val v)
  | box {s : Src.Slot} : IrrSlot s → FieldSlot I G ρ₀ none s

theorem Forall2.length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem Forall2.append {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {xs' : List α} {ys' : List β}, Forall2 R xs ys →
      Forall2 R xs' ys' → Forall2 R (xs ++ xs') (ys ++ ys')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hr h, h' => .cons hr (h.append h')

theorem Forall2.reverse {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R xs.reverse ys.reverse
  | _, _, .nil => .nil
  | _, _, .cons hr h => by
    simp only [List.reverse_cons]
    exact h.reverse.append (.cons hr .nil)

theorem Forall2.take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R (xs.take n) (ys.take n)
  | 0, _, _, _ => by simp; exact .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons hr h => .cons hr (h.take n)

theorem Forall2.drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R (xs.drop n) (ys.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ h => h.drop n

theorem Forall2.get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ {i : Nat} {x : α}, xs[i]? = some x →
      ∃ y, ys[i]? = some y ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hr _, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hr⟩
  | _, _, .cons _ h, i + 1, _, hi => by simpa using h.get (i := i) (by simpa using hi)

/-- Field slots prepended to an environment, through the matching map
entries. -/
theorem ER.prepend {I : Input} {G : Key.GKey → GlobalId → Prop} {ρ₀ : Env} :
    ∀ {xs : List (Option Nat)} {ys : List Src.Slot}, Forall2 (FieldSlot I G ρ₀) xs ys →
      ∀ {ctx : List (Option Nat)} {ρ : Src.Env}, ER I G ctx ρ ρ₀ → ER I G (xs ++ ctx) (ys ++ ρ) ρ₀
  | _, _, .nil, _, _, h => h
  | _, _, .cons (.lvl hl hg hv) hr, _, _, h => .lvl hl hg (.val hv) (ER.prepend hr h)
  | _, _, .cons (.box hs) hr, _, _, h => .box hs (ER.prepend hr h)

/-- The context under binders mapped to case-bound fields. -/
theorem EnvR.under {I : Input} {G : Key.GKey → GlobalId → Prop} {cx : Cx} {ρ : Src.Env}
    {ρ₀ : Env} (h : EnvR I G cx ρ ρ₀) {slots : List (Option Nat)} {fsl : List Src.Slot}
    (hf : Forall2 (FieldSlot I G ρ₀) slots fsl)
    (hfresh : ∀ l, some l ∈ slots → ∀ sig, cx.minors.lookup l ≠ some sig) :
    EnvR I G (cx.under slots) (fsl.reverse ++ ρ) ρ₀ where
  er := ER.prepend hf.reverse h.er
  depth := h.depth
  minors := by
    intro v l sig hv hl hn
    simp only [Cx.under] at hv hl
    by_cases hvs : v < slots.length
    · rw [List.getElem?_append_left (by simpa using hvs)] at hv
      have : some l ∈ slots := by
        have := List.mem_of_getElem? hv
        simpa using this
      exact absurd hl (hfresh l this sig)
    · have hlen := hf.length
      rw [List.getElem?_append_right (by simp; omega)] at hv
      obtain ⟨s, hs, ht⟩ := h.minors _ l sig hv hl hn
      refine ⟨s, ?_, ht⟩
      rw [List.getElem?_append_right (by simp; omega)]
      simpa [hlen] using hs
  minorsLt := h.minorsLt

theorem fieldArgs_drop (cx : Cx) (fields : List (Option Nat)) (n : Nat) :
    (fieldArgs cx fields).drop n = fieldArgs cx (fields.drop n) := by
  simp [fieldArgs, List.map_drop]

namespace Setting

variable (S : Setting)

section

variable {S} {m : Nat}

/-- A value applied to case-bound fields. -/
theorem fieldApply_sim (hap : S.ApplySim m) {cx : Cx} {ρ₀ : Env} (hd : cx.depth = ρ₀.length) :
    ∀ {fields : List (Option Nat)} {fsl : List Src.Slot}, Forall2 (FieldSlot S.I S.G ρ₀) fields fsl →
      ∀ {f : Src.Value} {f' : Val}, VR S.I S.G f f' →
        SimUpTo (VR S.I S.G) m (fun k => Src.applyAll S.p k f fsl)
          (fun k => Lam.applyArgs S.L k ρ₀ f' (fieldArgs cx fields))
  | _, _, .nil, f, f', hf => (SimUpTo.ok hf).congr (fun k => Src.applyAll_nil S.p k f) (fun _ => rfl)
  | _, _, .cons (.lvl (l := l) (v := v) (v' := v') hl hg hv) hr, f, f', hf => by
    refine (SimUpTo.bind (Lam.apply_mono S.L _ _) (fun w => Lam.applyArgs_mono S.L _ w _)
      (hap hf (SR.val hv) (.inr ⟨_, _, rfl, rfl⟩)) fun w w' hw => fieldApply_sim hap hd hr hw).congr
      (fun k => Src.applyAll_cons S.p k f _ _) (fun k => ?_)
    simp only [fieldArgs, List.map_cons, Lam.applyArgs, Lam.argSlot]
    rw [Cx.lvl_eq, hd, Lam.eval_var_of S.L k ρ₀ hg, Lam.force_val, Sem.Result.bind_ok,
      Sem.Result.bind_ok]
  | _, _, .cons (.box hs) hr, f, f', hf => by
    obtain ⟨t, ρ₁, ls₁, rfl⟩ := hs
    refine (SimUpTo.bind (Lam.apply_mono S.L _ _) (fun w => Lam.applyArgs_mono S.L _ w _)
      (hap hf (SR.val (VR.irr (t := t) (ρ := ρ₁) (ls := ls₁))) (.inr ⟨_, _, rfl, rfl⟩))
      fun w w' hw => fieldApply_sim hap hd hr hw).congr
      (fun k => Src.applyAll_cons S.p k f _ _) (fun k => ?_)
    simp only [fieldArgs, List.map_cons, Lam.applyArgs, Lam.argSlot, Lam.eval_box',
      Sem.Result.bind_ok]

/-- A `casesOn` minor applied to its fields (`minorApp`): SrcEval forces the
minor and applies it; Lam applies the level or □, or enters the peeled
minor body after its `tick`. -/
theorem minor_sim (hlt : ∀ m' < m, S.Level m') (hap : S.ApplySim m) {cx : Cx} {ref : Ref}
    {fields : List (Option Nat)} {body : Term} (hmr : MinorR S.I S.G cx ref fields body)
    {ls : Levels} {ρ : Src.Env} {ρ₀ : Env} (he : EnvR S.I S.G cx ρ ρ₀) (hag : Agree ls cx.prof)
    {sm : Src.Slot} (hrs : RefSlot S.I S.G ls ρ ρ₀ ref sm) {fsl : List Src.Slot}
    (hfs : Forall2 (FieldSlot S.I S.G ρ₀) fields fsl)
    (hfresh : ∀ l, some l ∈ fields → ∀ sig, cx.minors.lookup l ≠ some sig) :
    SimUpTo (VR S.I S.G) m (fun k => (Src.force S.p k sm).bind fun mv => Src.applyAll S.p k mv fsl)
      (fun k => Lam.eval S.L k ρ₀ body) := by
  cases hmr with
  | box =>
    cases hrs with
    | box hs =>
      obtain ⟨t, ρ₁, ls₁, rfl⟩ := hs
      refine (fieldApply_sim hap he.depth hfs (VR.irr (t := t) (ρ := ρ₁) (ls := ls₁))).congr
        (fun k => by rw [Src.force_val, Sem.Result.bind_ok]) (fun k => ?_)
      rw [Lam.eval_apps, Lam.eval_box', Sem.Result.bind_ok]
  | lvl =>
    cases hrs with
    | lvl _ hg hv =>
      refine (fieldApply_sim hap he.depth hfs hv).congr
        (fun k => by rw [Src.force_val, Sem.Result.bind_ok]) (fun k => ?_)
      rw [Lam.eval_apps, Cx.lvl_eq, he.depth, Lam.eval_var_of S.L k ρ₀ hg, Lam.force_val,
        Sem.Result.bind_ok]
  | name hpeel hbd =>
    rename_i mt bd p bd'
    cases hrs with
    | name =>
      have hlen := hfs.length
      have hp : peelUpTo fsl.length mt = (p, bd) := by rw [← hlen]; exact hpeel
      refine (SimUpTo.bind (Lam.eval_mono S.L ρ₀ bd').later
        (fun w => Lam.applyArgs_mono S.L _ w _)
        (SimUpTo.later (n := m) (c₁ := fun j' =>
            if peelOk ls p mt then Src.eval S.p j' ls ((fsl.take p).reverse ++ ρ) bd else .stuck)
          fun m' hm' => ?_)
        fun w w' hw => fieldApply_sim hap he.depth (hfs.drop p) hw).congr
        (fun k => by rw [force_applyAll_peel, hp]) (fun k => ?_)
      · by_cases hok : peelOk ls p mt = true
        · simp only [hok, ↓reduceIte]
          refine (hlt m' (by omega)).tr hbd (he.under (hfs.take p) fun l hl sig => ?_) hag
          exact hfresh l (List.mem_of_mem_take hl) sig
        · simp only [hok, Bool.false_eq_true, ↓reduceIte]
          exact SimUpTo.stuck _
      · rw [Lam.eval_apps, fieldArgs_drop, Lam.eval_tick]; rfl

end

end Setting

end IxCC.Lam.Erase.Proof
