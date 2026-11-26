import IxCC.Src.ArrayOp
import IxCC.Sem.SimUpTo
import IxCC.Sem.Forall2

/-!
# Value models related: parametricity of the array primitives (`IxCC.Sem.ModelRel`)

Design note: `plans/ONE-PIPELINE.md`, section 1.4. The value model itself (`Sem.ValModel`) and the
primitives' meaning over it (`Src.ArrOp.eval`) are in `IxCC/Src/ArrayOp.lean`.

**One proof obligation per pass.** A pass whose value relation is a `ModelRel` between its two
models (literals to equal literals, arrays and `List` values to arrays and `List` values of
related elements, forward) gets every array primitive from one theorem,
`Src.ArrOp.parametric : Parametric`: on related arguments the two models' results are related, a
trap is a trap, and a stuck source asks nothing. Elements are opaque to every operation, sOff the
relation need say nothing about them.

`ArrOp.sim` is the same fact in the shape the clocked simulations use (`Sem.SimUpTo`), with
`ArrOp.eval_ne_timeout` and `ArrOp.eval_ne_resource` (`ArrOp.neverResource`): an array primitive
is one uncharged step that never fails for a resource, as a `Nat` primitive is.
-/

set_option autoImplicit false

namespace IxCC.Sem

/-- **A value relation the primitives respect**: literals to equal literals, arrays and lists to
arrays and lists of related elements, forward (the target reads whatever the source reads). The
value relation of each pass from erasure down is one. -/
structure ModelRel {V W : Type} (M : ValModel V) (N : ValModel W) (R : V → W → Prop) : Prop where
  nat : ∀ n, R (M.nat n) (N.nat n)
  asNat : ∀ {v w n}, R v w → M.asNat v = some n → N.asNat w = some n
  arr : ∀ {xs ys}, Forall2 R xs ys → R (M.arr xs) (N.arr ys)
  asArr : ∀ {v w xs}, R v w → M.asArr v = some xs → ∃ ys, N.asArr w = some ys ∧ Forall2 R xs ys
  list : ∀ {xs ys}, Forall2 R xs ys → R (M.list xs) (N.list ys)
  asList : ∀ {v w xs}, R v w → M.asList v = some xs →
    ∃ ys, N.asList w = some ys ∧ Forall2 R xs ys

namespace Forall2

variable {α β : Type} {R : α → β → Prop}

theorem replicate {a : α} {b : β} (h : R a b) :
    ∀ n, Forall2 R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => .cons h (replicate h n)

theorem set {as : List α} {bs : List β} (h : Forall2 R as bs) {a : α} {b : β} (hab : R a b) :
    ∀ i, Forall2 R (as.set i a) (bs.set i b) := by
  induction h with
  | nil => intro i; exact .nil
  | cons hxy hrest ih =>
    intro i
    cases i with
    | zero => exact .cons hab hrest
    | succ i => exact .cons hxy (ih i)

theorem dropLast {as : List α} {bs : List β} (h : Forall2 R as bs) :
    Forall2 R as.dropLast bs.dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, h.length]
  exact h.take _

theorem get_none {as : List α} {bs : List β} (h : Forall2 R as bs) {i : Nat}
    (hi : as[i]? = none) : bs[i]? = none := by
  rw [List.getElem?_eq_none_iff] at hi ⊢
  rw [← h.length]
  exact hi

theorem extractList {as : List α} {bs : List β} (h : Forall2 R as bs) (start stop : Nat) :
    Forall2 R (Src.ArraySpec.extractList as start stop)
      (Src.ArraySpec.extractList bs start stop) := by
  unfold Src.ArraySpec.extractList
  rw [h.length]
  exact (h.drop start).take _

theorem copySliceList {xs : List α} {xs' : List β} {ys : List α} {ys' : List β}
    (hx : Forall2 R xs xs') (hy : Forall2 R ys ys') (srcOff destOff len : Nat) :
    Forall2 R (Src.ArraySpec.copySliceList xs srcOff ys destOff len)
      (Src.ArraySpec.copySliceList xs' srcOff ys' destOff len) := by
  unfold Src.ArraySpec.copySliceList
  rw [hx.length, hy.length]
  exact ((hy.extractList _ _).append (hx.extractList _ _)).append (hy.extractList _ _)

end Forall2

/-- A clock-independent step whose outcomes refine, as a simulation at every bound. -/
theorem SimUpTo.of_refines {α β : Type} {R : α → β → Prop} {n : Nat} {s : Result α}
    {t : Result β} (h : Result.Refines R s t) (hs : s ≠ .timeout) :
    SimUpTo R n (fun _ => s) (fun _ => t) where
  fwd _ _ _ := ⟨0, h⟩
  tmo _ _ h' := absurd h' hs

end IxCC.Sem

namespace IxCC.Src.ArrOp

open IxCC.Sem (Result ValModel ModelRel Forall2 SimUpTo)

/-- **Parametricity of the array primitives** (the statement): on related arguments the two
models' results are related, a trap is a trap, and a stuck source asks nothing. Each pass's proof
of its primitive case is this at its own value relation. -/
def Parametric : Prop :=
  ∀ (V W : Type) (M : ValModel V) (N : ValModel W) (R : V → W → Prop), ModelRel M N R →
    ∀ (op : ArrOp) (vs : List V) (ws : List W), Forall2 R vs ws →
      Result.Refines R (op.eval M vs) (op.eval N ws)

/-- An array primitive never fails for a resource and never times out (the statement): it is one
uncharged step, as a `Nat` primitive is. -/
def NeverResource : Prop :=
  ∀ (V : Type) (M : ValModel V) (op : ArrOp) (vs : List V),
    op.eval M vs ≠ .timeout ∧ ∀ r, op.eval M vs ≠ .resource r

section

variable {V W : Type} {M : ValModel V} {N : ValModel W} {R : V → W → Prop}

/-! ## Outcomes -/

/-- An array primitive on the wrong number of arguments is stuck. -/
theorem eval_arity (M : ValModel V) (op : ArrOp) (vs : List V) (h : vs.length ≠ op.arity) :
    op.eval M vs = .stuck := by
  cases op <;>
    (rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tl⟩⟩⟩⟩⟩⟩) <;>
    first
      | rfl
      | exact absurd rfl h

theorem eval_ne_timeout (M : ValModel V) (op : ArrOp) (vs : List V) : op.eval M vs ≠ .timeout := by
  intro h
  unfold eval at h
  repeat' split at h
  all_goals exact nomatch h

theorem eval_ne_resource (M : ValModel V) (op : ArrOp) (vs : List V) (r : Sem.Resource) :
    op.eval M vs ≠ .resource r := by
  intro h
  unfold eval at h
  repeat' split at h
  all_goals exact nomatch h

/-- An array primitive returns a value, traps, or is stuck. -/
theorem eval_cases (M : ValModel V) (op : ArrOp) (vs : List V) :
    (∃ v, op.eval M vs = .ok v) ∨ op.eval M vs = .trap ∨ op.eval M vs = .stuck := by
  cases h : op.eval M vs with
  | ok v => exact .inl ⟨v, rfl⟩
  | timeout => exact absurd h (eval_ne_timeout M op vs)
  | resource r => exact absurd h (eval_ne_resource M op vs r)
  | trap => exact .inr (.inl rfl)
  | stuck => exact .inr (.inr rfl)

/-- Only `get` and `set` trap (`mayTrap`). -/
theorem eval_trap {op : ArrOp} {vs : List V} (h : op.eval M vs = .trap) : op.mayTrap = true := by
  cases hop : op.mayTrap with
  | true => rfl
  | false =>
    exfalso
    unfold eval at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases hop; done)

/-- A primitive that cannot trap returns a value or is stuck. -/
theorem eval_pure {op : ArrOp} (hop : op.mayTrap = false) (M : ValModel V) (vs : List V) :
    op.eval M vs = .stuck ∨ ∃ v, op.eval M vs = .ok v := by
  rcases eval_cases M op vs with h | h | h
  · exact .inr h
  · rw [eval_trap h] at hop; cases hop
  · exact .inl h

/-! ## Parametricity, operation by operation -/

private theorem refines_empty (hR : ModelRel M N R) {c : V} {c' : W} (hc : R c c') :
    Result.Refines R (eval M .empty [c]) (eval N .empty [c']) := by
  simp only [eval]
  cases h : M.asNat c with
  | none => exact .stuck
  | some n => simp only [hR.asNat hc h]; exact .ok (hR.arr .nil)

private theorem refines_replicate (hR : ModelRel M N R) {c v : V} {c' v' : W} (hc : R c c')
    (hv : R v v') : Result.Refines R (eval M .replicate [c, v]) (eval N .replicate [c', v']) := by
  simp only [eval]
  cases h : M.asNat c with
  | none => exact .stuck
  | some n => simp only [hR.asNat hc h]; exact .ok (hR.arr (.replicate hv n))

private theorem refines_size (hR : ModelRel M N R) {a : V} {a' : W} (ha : R a a') :
    Result.Refines R (eval M .size [a]) (eval N .size [a']) := by
  simp only [eval]
  cases h : M.asArr a with
  | none => exact .stuck
  | some xs =>
    obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h
    simp only [hys, hxy.length]
    exact .ok (hR.nat _)

private theorem refines_get (hR : ModelRel M N R) {a i : V} {a' i' : W} (ha : R a a')
    (hi : R i i') : Result.Refines R (eval M .get [a, i]) (eval N .get [a', i']) := by
  simp only [eval]
  cases h1 : M.asArr a with
  | none => exact .stuck
  | some xs =>
    cases h2 : M.asNat i with
    | none => exact .stuck
    | some n =>
      obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h1
      simp only [hys, hR.asNat hi h2]
      cases h3 : xs[n]? with
      | none => simp only [hxy.get_none h3]; exact .trap
      | some x =>
        obtain ⟨y, hy, hxy'⟩ := hxy.get h3
        simp only [hy]; exact .ok hxy'

private theorem refines_set (hR : ModelRel M N R) {a i v : V} {a' i' v' : W} (ha : R a a')
    (hi : R i i') (hv : R v v') :
    Result.Refines R (eval M .set [a, i, v]) (eval N .set [a', i', v']) := by
  simp only [eval]
  cases h1 : M.asArr a with
  | none => exact .stuck
  | some xs =>
    cases h2 : M.asNat i with
    | none => exact .stuck
    | some n =>
      obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h1
      simp only [hys, hR.asNat hi h2, ← hxy.length]
      by_cases hlt : n < xs.length
      · simp only [hlt, ↓reduceIte]; exact .ok (hR.arr (hxy.set hv n))
      · simp only [hlt, ↓reduceIte]; exact .trap

private theorem refines_push (hR : ModelRel M N R) {a v : V} {a' v' : W} (ha : R a a')
    (hv : R v v') : Result.Refines R (eval M .push [a, v]) (eval N .push [a', v']) := by
  simp only [eval]
  cases h : M.asArr a with
  | none => exact .stuck
  | some xs =>
    obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h
    simp only [hys]
    exact .ok (hR.arr (hxy.append (.cons hv .nil)))

private theorem refines_pop (hR : ModelRel M N R) {a : V} {a' : W} (ha : R a a') :
    Result.Refines R (eval M .pop [a]) (eval N .pop [a']) := by
  simp only [eval]
  cases h : M.asArr a with
  | none => exact .stuck
  | some xs =>
    obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h
    simp only [hys]
    exact .ok (hR.arr hxy.dropLast)

private theorem refines_append (hR : ModelRel M N R) {a b : V} {a' b' : W} (ha : R a a')
    (hb : R b b') : Result.Refines R (eval M .append [a, b]) (eval N .append [a', b']) := by
  simp only [eval]
  cases h1 : M.asArr a with
  | none => exact .stuck
  | some xs =>
    cases h2 : M.asArr b with
    | none => exact .stuck
    | some zs =>
      obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h1
      obtain ⟨ws, hws, hzw⟩ := hR.asArr hb h2
      simp only [hys, hws]
      exact .ok (hR.arr (hxy.append hzw))

private theorem refines_extract (hR : ModelRel M N R) {a s t : V} {a' s' t' : W} (ha : R a a')
    (hs : R s s') (ht : R t t') :
    Result.Refines R (eval M .extract [a, s, t]) (eval N .extract [a', s', t']) := by
  simp only [eval]
  cases h1 : M.asArr a with
  | none => exact .stuck
  | some xs =>
    cases h2 : M.asNat s with
    | none => exact .stuck
    | some start =>
      cases h3 : M.asNat t with
      | none => exact .stuck
      | some stop =>
        obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h1
        simp only [hys, hR.asNat hs h2, hR.asNat ht h3]
        exact .ok (hR.arr (hxy.extractList start stop))

private theorem refines_copySlice (hR : ModelRel M N R) {a sOff d dOff l : V}
    {a' sOff' d' dOff' l' : W} (ha : R a a') (hso : R sOff sOff') (hd : R d d') (hdo : R dOff dOff') (hl : R l l') :
    Result.Refines R (eval M .copySlice [a, sOff, d, dOff, l])
      (eval N .copySlice [a', sOff', d', dOff', l']) := by
  simp only [eval]
  cases h1 : M.asArr a with
  | none => exact .stuck
  | some xs =>
    cases h2 : M.asNat sOff with
    | none => exact .stuck
    | some srcOff =>
      cases h3 : M.asArr d with
      | none => exact .stuck
      | some zs =>
        cases h4 : M.asNat dOff with
        | none => exact .stuck
        | some destOff =>
          cases h5 : M.asNat l with
          | none => exact .stuck
          | some len =>
            obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h1
            obtain ⟨ws, hws, hzw⟩ := hR.asArr hd h3
            simp only [hys, hws, hR.asNat hso h2, hR.asNat hdo h4, hR.asNat hl h5]
            exact .ok (hR.arr (hxy.copySliceList hzw srcOff destOff len))

private theorem refines_ofList (hR : ModelRel M N R) {a : V} {a' : W} (ha : R a a') :
    Result.Refines R (eval M .ofList [a]) (eval N .ofList [a']) := by
  simp only [eval]
  cases h : M.asList a with
  | none => exact .stuck
  | some xs =>
    obtain ⟨ys, hys, hxy⟩ := hR.asList ha h
    simp only [hys]
    exact .ok (hR.arr hxy)

private theorem refines_toList (hR : ModelRel M N R) {a : V} {a' : W} (ha : R a a') :
    Result.Refines R (eval M .toList [a]) (eval N .toList [a']) := by
  simp only [eval]
  cases h : M.asArr a with
  | none => exact .stuck
  | some xs =>
    obtain ⟨ys, hys, hxy⟩ := hR.asArr ha h
    simp only [hys]
    exact .ok (hR.list hxy)

/-- **Parametricity**, as a rule: on related arguments, the results refine. -/
theorem eval_refines (hR : ModelRel M N R) (op : ArrOp) {vs : List V} {ws : List W}
    (h : Forall2 R vs ws) : Result.Refines R (op.eval M vs) (op.eval N ws) := by
  cases op with
  | empty =>
    rcases h with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
    · exact .stuck
    · exact refines_empty hR h1
    · exact .stuck
  | replicate =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, h4⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact refines_replicate hR h1 h2
    · exact .stuck
  | size =>
    rcases h with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
    · exact .stuck
    · exact refines_size hR h1
    · exact .stuck
  | get =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, h4⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact refines_get hR h1 h2
    · exact .stuck
  | set =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, h5⟩⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact .stuck
    · exact refines_set hR h1 h2 h3
    · exact .stuck
  | push =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, h4⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact refines_push hR h1 h2
    · exact .stuck
  | pop =>
    rcases h with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
    · exact .stuck
    · exact refines_pop hR h1
    · exact .stuck
  | append =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, h4⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact refines_append hR h1 h2
    · exact .stuck
  | extract =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, h5⟩⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact .stuck
    · exact refines_extract hR h1 h2 h3
    · exact .stuck
  | copySlice =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, h7⟩⟩⟩⟩⟩⟩
    · exact .stuck
    · exact .stuck
    · exact .stuck
    · exact .stuck
    · exact .stuck
    · exact refines_copySlice hR h1 h2 h3 h4 h5
    · exact .stuck
  | ofList =>
    rcases h with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
    · exact .stuck
    · exact refines_ofList hR h1
    · exact .stuck
  | toList =>
    rcases h with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
    · exact .stuck
    · exact refines_toList hR h1
    · exact .stuck

/-- Parametricity in the shape the clocked simulations use: one uncharged step at every bound. -/
theorem sim (hR : ModelRel M N R) (op : ArrOp) {vs : List V} {ws : List W}
    (h : Forall2 R vs ws) {n : Nat} :
    SimUpTo R n (fun _ => op.eval M vs) (fun _ => op.eval N ws) :=
  SimUpTo.of_refines (eval_refines hR op h) (eval_ne_timeout M op vs)

end

/-- **Parametricity of the array primitives.** -/
theorem parametric : Parametric := fun _ _ _ _ _ hR op _ _ h => eval_refines hR op h

/-- **An array primitive never times out and never fails for a resource.** -/
theorem neverResource : NeverResource :=
  fun _ M op vs => ⟨eval_ne_timeout M op vs, eval_ne_resource M op vs⟩

end IxCC.Src.ArrOp
