import Compilatrix.Lam.Erase.Proof.Sound
import Compilatrix.Lam.Erase.Proof.Layout

/-! # Erasure's constructor table

Erasure registers a constructor key in its table (`registerCtor`) before it
emits a term with that key, and the table only grows. So every constructor
key in an erased term is in the final table (`RegT`), and each row's arity
is its constructor's kept-field count (`CtorInv`). `CSound x R` is the
monad's judgement for this: `x` keeps every row and the invariant (and the
erased globals, and every id below `next` naming a key: `IdsSurj`), with `R`
of its result against every key-arity relation containing the final table
(like `Sound` for the key table) (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Profile NatMap)

/-- Key-arity relations: key `k` has a row of arity `n`. -/
abbrev CTab := Key.CtorKey → Nat → Prop

/-- The state's table as a relation (row `c` has key `.src c`). -/
def tabOf (s : St) : CTab := fun k n => ∃ c info, s.ctors.get? c = some info ∧ k = .src c ∧
  info.arity = n

/-- A row for `c` of arity `n`: the kept-field count of a constructor that
`alias` maps to `c`. -/
def RowShape (I : Input) (c : CId) (n : Nat) : Prop :=
  ∃ c₀ sf lv ind cidx np nf ty, I.decl? c₀ = some (.ctor sf lv ind cidx np nf ty) ∧
    I.alias c₀ = c ∧ n = I.keptCount c₀ [] nf

/-- The table's invariant: rows keyed by their constructor, of their shape,
listed once each in `ctorOrder`. -/
structure CtorInv (I : Input) (s : St) : Prop where
  rows : ∀ c info, s.ctors.get? c = some info → info.key = .src c ∧ RowShape I c info.arity
  nodup : s.ctorOrder.Nodup
  order : ∀ c, c ∈ s.ctorOrder ↔ (s.ctors.get? c).isSome

theorem CtorInv.empty (I : Input) : CtorInv I {} :=
  ⟨fun _ _ h => by simp [NatMap.get?] at h, List.nodup_nil, fun c => by simp [NatMap.get?]⟩

/-- Every id below `next` names a key. -/
def IdsSurj (s : St) : Prop := ∀ g, g < s.next → ∃ key, keyOf s key = some g

/-- A step keeps every row, the table's invariant, the erased globals, and
every id naming a key. -/
structure CGrows (I : Input) (s s' : St) : Prop where
  ctors : ∀ c info, s.ctors.get? c = some info → s'.ctors.get? c = some info
  inv : CtorInv I s → CtorInv I s'
  globals : s'.globals = s.globals
  surj : IdsSurj s → IdsSurj s'

theorem CGrows.refl (I : Input) (s : St) : CGrows I s s := ⟨fun _ _ h => h, id, rfl, id⟩

theorem CGrows.trans {I : Input} {s₁ s₂ s₃ : St} (h₁ : CGrows I s₁ s₂) (h₂ : CGrows I s₂ s₃) :
    CGrows I s₁ s₃ :=
  ⟨fun c info h => h₂.ctors c info (h₁.ctors c info h), fun h => h₂.inv (h₁.inv h),
    h₂.globals.trans h₁.globals, fun h => h₂.surj (h₁.surj h)⟩

theorem IdsSurj.frame {s s' : St} (hi : s'.ids = s.ids) (hn : s'.next = s.next)
    (h : IdsSurj s) : IdsSurj s' := fun g hg => by
  obtain ⟨key, hk⟩ := h g (hn ▸ hg)
  exact ⟨key, by unfold keyOf at hk ⊢; rw [hi]; exact hk⟩

/-- A step that keeps the table (and the globals). -/
theorem CtorInv.frame {I : Input} {s s' : St} (hc : s'.ctors = s.ctors)
    (ho : s'.ctorOrder = s.ctorOrder) (h : CtorInv I s) : CtorInv I s' :=
  let ⟨h₁, h₂, h₃⟩ := h
  ⟨fun c info h => h₁ c info (hc ▸ h), ho ▸ h₂, fun c => by rw [ho, hc]; exact h₃ c⟩

theorem CGrows.frame {I : Input} {s s' : St} (hc : s'.ctors = s.ctors)
    (ho : s'.ctorOrder = s.ctorOrder) (hg : s'.globals = s.globals) (hi : s'.ids = s.ids)
    (hn : s'.next = s.next) : CGrows I s s' :=
  ⟨fun c info h => by rw [hc]; exact h, CtorInv.frame hc ho, hg, IdsSurj.frame hi hn⟩

theorem tabOf_grows {I : Input} {s s' : St} (h : CGrows I s s') {k : Key.CtorKey} {n : Nat} :
    tabOf s k n → tabOf s' k n := fun ⟨c, info, hc, hk, hn⟩ => ⟨c, info, h.ctors c info hc, hk, hn⟩

/-- `x` succeeds keeping the table's rows and invariant, with `R` of its
result against every relation containing the final table. -/
def CSound {α : Type} (I : Input) (x : M α) (R : α → CTab → Prop) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → CGrows I s s' ∧ ∀ T : CTab, (∀ k n, tabOf s' k n → T k n) →
    R a T

namespace CSound

variable {I : Input} {α β : Type} {R R' : α → CTab → Prop}

theorem imp {x : M α} (h : CSound I x R) (hr : ∀ a T, R a T → R' a T) : CSound I x R' :=
  fun s a s' e => ⟨(h s a s' e).1, fun T hT => hr a T ((h s a s' e).2 T hT)⟩

theorem pure {a : α} (h : ∀ T, R a T) : CSound I (Pure.pure a : M α) R := fun s b s' e => by
  simp only [StateT.run_pure] at e
  cases e
  exact ⟨CGrows.refl I _, fun T _ => h T⟩

theorem bind {R₁ : α → CTab → Prop} {R : β → CTab → Prop} {x : M α} {f : α → M β}
    (hx : CSound I x R₁) (hf : ∀ a, CSound I (f a) fun b T => R₁ a T → R b T) :
    CSound I (x >>= f) R := by
  intro s b s'' e
  obtain ⟨a, s', ex, ef⟩ := Sound.bind_run e
  obtain ⟨g₁, h₁⟩ := hx s a s' ex
  obtain ⟨g₂, h₂⟩ := hf a s' b s'' ef
  exact ⟨g₁.trans g₂, fun T hT => h₂ T hT (h₁ T fun k n h => hT k n (tabOf_grows g₂ h))⟩

theorem throw {e : EraseError} : CSound I (MonadExcept.throw e : M α) R := fun s a s' h => by
  simp [MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at h
  cases h

theorem decline {code message : String} {c : Option CId} :
    CSound I (Erase.decline code message c : M α) R := by
  unfold Erase.decline
  exact bind (R₁ := fun _ _ => True) (fun s a s' e => by
      simp only [StateT.run_get] at e
      cases e
      exact ⟨CGrows.refl I _, fun _ _ => trivial⟩)
    fun _ => throw

theorem decline_bind {code message : String} {c : Option CId} {f : α → M β}
    {R : β → CTab → Prop} : CSound I (Erase.decline code message c >>= f) R :=
  fun s b s'' e => by
    obtain ⟨a, s', hx, _⟩ := Sound.bind_run e
    exact ((decline (I := I) (R := fun _ _ => False) s a s' hx).2 (fun _ _ => True)
      fun _ _ _ => trivial).elim

theorem ite {c : Prop} [Decidable c] {x y : M α} (h₁ : c → CSound I x R) (h₂ : ¬ c → CSound I y R) :
    CSound I (if c then x else y) R := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

theorem mapM {γ : Type} {f : γ → M β} {P : γ → β → CTab → Prop} :
    ∀ {xs : List γ}, (∀ x ∈ xs, CSound I (f x) (P x)) →
      CSound I (xs.mapM f) fun ys T => Forall2 (fun x y => P x y T) xs ys
  | [], _ => pure fun _ => .nil
  | x :: xs, h => by
    rw [List.mapM_cons]
    exact bind (h x List.mem_cons_self) fun y =>
      bind (mapM fun z hz => h z (List.mem_cons_of_mem _ hz)) fun ys =>
        pure fun _ hys hy => .cons hy hys

/-- A list built element by element, each element with `P`. -/
theorem mapM_all {γ : Type} {f : γ → M β} {P : β → CTab → Prop} :
    ∀ {xs : List γ}, (∀ x ∈ xs, CSound I (f x) P) →
      CSound I (xs.mapM f) fun ys T => ∀ y ∈ ys, P y T
  | [], _ => pure fun _ _ h => by cases h
  | x :: xs, h => by
    rw [List.mapM_cons]
    exact bind (h x List.mem_cons_self) fun y =>
      bind (mapM_all fun z hz => h z (List.mem_cons_of_mem _ hz)) fun ys =>
        pure fun _ hys hy z hz => (List.mem_cons.1 hz).elim (fun e => e ▸ hy) (hys z)

theorem get_bind {f : St → M α}
    (h : ∀ s a s', (f s).run s = .ok (a, s') → CGrows I s s' ∧
      ∀ T : CTab, (∀ k n, tabOf s' k n → T k n) → R a T) :
    CSound I (MonadState.get >>= f) R := by
  intro s a s' e
  rw [StateT.run_bind] at e
  simp only [StateT.run_get, pure_bind] at e
  exact h s a s' e

theorem forIn_unit {γ : Type} {f : γ → PUnit → M (ForInStep PUnit)} :
    ∀ {xs : List γ}, (∀ x ∈ xs, ∀ u, CSound I (f x u) fun _ _ => True) →
      CSound I (forIn xs PUnit.unit f) fun _ _ => True
  | [], _ => pure fun _ => trivial
  | x :: xs, h => by
    rw [List.forIn_cons]
    refine bind (h x List.mem_cons_self _) fun r => ?_
    cases r with
    | done b => exact pure fun _ _ => trivial
    | yield b =>
      cases b
      have ih := forIn_unit (f := f) fun y hy u => h y (List.mem_cons_of_mem _ hy) u
      exact ih.imp fun _ _ _ _ => trivial

end CSound

/-! ## The primitive steps -/

theorem csound_globalId (I : Input) (key : Key.GKey) :
    CSound I (globalId key) fun _ _ => True := by
  intro s g s' e
  unfold globalId at e
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at e
  cases hl : ((s.ids.get? key.bucket).getD []).lookup key with
  | some g₀ =>
    rw [hl] at e
    simp only [StateT.run_pure] at e
    cases e
    exact ⟨CGrows.refl I _, fun _ _ => trivial⟩
  | none =>
    rw [hl] at e
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at e
    cases e
    refine ⟨⟨fun _ _ h => h, CtorInv.frame rfl rfl, rfl, fun h g' hg' => ?_⟩, fun _ _ => trivial⟩
    have hnew := fun key' => keyOf_globalId_new s key key' hl
    by_cases e : g' = s.next
    · exact ⟨key, by rw [hnew key]; simp [e]⟩
    · obtain ⟨key', hk'⟩ := h g' (by simp only at hg'; omega)
      refine ⟨key', ?_⟩
      rw [hnew key']
      by_cases e' : key' = key
      · subst e'
        unfold keyOf at hk'
        rw [hl] at hk'
        cases hk'
      · simp [e', hk']

/-- Registering a row of its shape: afterwards the key has that arity. -/
theorem csound_registerCtor (I : Input) (c : CId) (tag arity : Nat) (hs : RowShape I c arity) :
    CSound I (registerCtor c tag arity) fun _ T => T (.src c) arity := by
  unfold registerCtor
  refine CSound.get_bind fun s₀ a s' e => ?_
  cases h : s₀.ctors.get? c with
  | some info =>
    rw [h] at e
    dsimp only at e
    by_cases hc : (info.tag == tag && info.arity == arity) = true
    · simp only [hc, ↓reduceIte, StateT.run_pure] at e
      cases e
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨CGrows.refl I _, fun T hT => hT _ _ ⟨c, info, h, rfl, hc.2⟩⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at e
      exact ((CSound.decline (I := I) (R := fun _ _ => False) s₀ a s' e).2 (fun _ _ => True)
        fun _ _ _ => trivial).elim
  | none =>
    rw [h] at e
    simp only [StateT.run_set] at e
    cases e
    refine ⟨⟨fun c' info' h' => ?_, fun ⟨h₁, h₂, h₃⟩ => ⟨fun c' info' h' => ?_, ?_, fun c' => ?_⟩,
      rfl, id⟩,
      fun T hT => hT _ _ ⟨c, _, NatMap.get?_insert_self _ _ _, rfl, rfl⟩⟩
    · dsimp only
      rw [NatMap.get?_insert_ne]
      · exact h'
      · intro e; subst e; rw [h] at h'; cases h'
    · dsimp only at h'
      rw [NatMap.get?_insert] at h'
      split at h'
      · next e =>
        subst e
        cases h'
        exact ⟨rfl, hs⟩
      · exact h₁ c' info' h'
    · dsimp only
      refine List.nodup_cons.2 ⟨fun hm => ?_, h₂⟩
      have := (h₃ c).1 hm
      rw [h] at this
      cases this
    · dsimp only
      rw [List.mem_cons, h₃ c', NatMap.get?_insert]
      by_cases e : c' = c
      · subst e; simp
      · simp [e]

/-- `alias` keeps a constructor that is neither pinned `Decidable` one. -/
theorem alias_of_notDec {I : Input} {c : CId} (hf : ∀ d, I.known.decIsFalse = some d → d ≠ c)
    (ht : ∀ d, I.known.decIsTrue = some d → d ≠ c) : I.alias c = c := by
  unfold Input.alias
  split
  · next df dt bf bt hdf hdt _ _ =>
    have h₁ : (c == df) = false := beq_false_of_ne fun e => hf df hdf e.symm
    have h₂ : (c == dt) = false := beq_false_of_ne fun e => ht dt hdt e.symm
    simp [h₁, h₂]
  · rfl

theorem keptCount_zero (I : Input) (c : CId) (q : Profile) : I.keptCount c q 0 = 0 := rfl

theorem csound_registerBool (I : Input) (wf : ProgWF I) :
    CSound I (registerBool I) fun _ _ => True := by
  unfold registerBool
  refine CSound.bind (R₁ := fun _ _ => True) (CSound.forIn_unit fun x hx u => ?_)
    fun _ => CSound.pure fun _ _ => trivial
  cases x with
  | none => exact CSound.pure fun _ => trivial
  | some c =>
    dsimp only
    split
    · next sf lv ind cidx np nf ty hd =>
      -- `c` is a pinned `Bool` constructor: no fields, and not a `Decidable` one.
      have hb : I.known.boolFalse = some c ∨ I.known.boolTrue = some c := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h
        · exact .inl h.symm
        · exact .inr h.symm
      have hnf : nf = 0 := by
        rcases hb with h | h
        · obtain ⟨_, _, _, _, _, h₁, _⟩ := wf.boolFalse h
          rw [hd] at h₁; cases h₁; rfl
        · obtain ⟨_, _, _, _, _, h₁, _⟩ := wf.boolTrue h
          rw [hd] at h₁; cases h₁; rfl
      have hne : ∀ d, (I.known.decIsFalse = some d ∨ I.known.decIsTrue = some d) → d ≠ c := by
        intro d hdd e
        subst e
        exact wf.decOther hdd (by rcases hb with h | h; exact .inl h; exact .inr (.inl h)) hd hd rfl
      refine CSound.bind (csound_registerCtor I c cidx 0
        ⟨c, sf, lv, ind, cidx, np, nf, ty, hd, alias_of_notDec (fun d h => hne d (.inl h))
          (fun d h => hne d (.inr h)), by rw [hnf]; rfl⟩) fun _ => CSound.pure fun _ _ => trivial
    · exact CSound.pure fun _ => trivial

/-! ## Constructor keys in terms -/

/-- Every constructor key of `t` has a row in `T`. -/
inductive RegT (T : CTab) : Term → Prop
  | var (i : Nat) : RegT T (.var i)
  | glob (g : GlobalId) : RegT T (.glob g)
  | lam {m : Mode} {c : Ixon.V3.BinderContract} {b : Term} : RegT T b → RegT T (.lam m c b)
  | app {f a : Term} {m : Mode} : RegT T f → RegT T a → RegT T (.app f a m)
  | letE {c : Ixon.V3.LetContract} {v b : Term} : RegT T v → RegT T b → RegT T (.letE c v b)
  | con {k : Key.CtorKey} {fs : List Term} :
      (∃ n, T k n) → (∀ f ∈ fs, RegT T f) → RegT T (.con k fs)
  | case {s : Term} {alts : List Alt} {d : Option Term} :
      RegT T s → (∀ k n b, Alt.mk k n b ∈ alts → ∃ n', T k n') →
      (∀ k n b, Alt.mk k n b ∈ alts → RegT T b) → (∀ t ∈ d, RegT T t) →
      RegT T (.case s alts d)
  | proj {k : Key.CtorKey} {i : Nat} {s : Term} : (∃ n, T k n) → RegT T s → RegT T (.proj k i s)
  | lit (l : Lit) : RegT T (.lit l)
  | prim {p : Prim} {args : List Term} : (∀ a ∈ args, RegT T a) → RegT T (.prim p args)
  | tick {t : Term} : RegT T t → RegT T (.tick t)
  | box : RegT T .box
  | trap : RegT T .trap

namespace RegT

variable {T : CTab}

theorem apps : ∀ {h : Term} {args : List (Term × Mode)}, RegT T h → (∀ a ∈ args, RegT T a.1) →
    RegT T (Term.apps h args)
  | _, [], hh, _ => hh
  | _, (a, m) :: args, hh, ha => by
    unfold Term.apps
    rw [List.foldl_cons]
    exact apps (args := args) (.app hh (ha _ List.mem_cons_self))
      fun b hb => ha b (List.mem_cons_of_mem _ hb)

theorem lams : ∀ {ms : List Mode} {b : Term}, RegT T b → RegT T (Term.lams ms b)
  | [], _, h => h
  | m :: ms, _, h => by
    unfold Term.lams
    rw [List.foldr_cons]
    exact .lam (lams (ms := ms) h)

theorem wrapLets : ∀ {lets : List Term} {b : Term}, (∀ v ∈ lets, RegT T v) → RegT T b →
    RegT T (Erase.wrapLets lets b)
  | [], _, _, hb => hb
  | v :: lets, _, hv, hb => by
    unfold Erase.wrapLets
    rw [List.foldr_cons]
    exact .letE (hv v List.mem_cons_self)
      (wrapLets (lets := lets) (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hb)

theorem setModes : ∀ {ms : List Mode} {t t' : Term}, Term.setModes ms t = some t' → RegT T t →
    RegT T t'
  | [], _, _, e, h => by cases e; exact h
  | m :: ms, .lam m' c b, t', e, h => by
    simp only [Term.setModes, Option.map_eq_some_iff] at e
    obtain ⟨b', hb, rfl⟩ := e
    cases h with
    | lam hb' => exact .lam (setModes hb hb')
  | _ :: _, .var _, _, e, _ | _ :: _, .glob _, _, e, _ | _ :: _, .app .., _, e, _
  | _ :: _, .letE .., _, e, _ | _ :: _, .con .., _, e, _ | _ :: _, .case .., _, e, _
  | _ :: _, .proj .., _, e, _ | _ :: _, .lit _, _, e, _ | _ :: _, .prim .., _, e, _
  | _ :: _, .tick _, _, e, _ | _ :: _, .box, _, e, _ | _ :: _, .trap, _, e, _ => by
    simp [Term.setModes] at e

end RegT

end Compilatrix.Lam.Erase.Proof
