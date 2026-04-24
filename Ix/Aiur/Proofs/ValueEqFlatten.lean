module
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Proofs.IOBufferEquiv

/-!
`ValueEq` ↔ `flattenValue` correspondence.

Auxiliary bridge lemma: the propositional `ValueEq` relation coincides with the
computable `flattenValue` function. Used throughout the preservation proofs to
switch between the two forms as convenient.

Given the single-constructor definition of `ValueEq` (see `Semantics/Relation.lean`
scaffold note), both directions are immediate: `ValueEq.mk` wraps an equality,
and `ValueEq.mk` is the only way to build a proof, so case analysis recovers the
equality.
-/

public section

namespace Aiur

open Source

/-- `ValueEq` and `flattenValue` agree. -/
theorem ValueEq_iff_flattenValue
    (decls : Decls) (funcIdx : Global → Option Nat)
    (v : Value) (t : Typ) (gs : Array G) :
    ValueEq decls funcIdx v t gs ↔ flattenValue decls funcIdx v = gs := by
  constructor
  · intro h
    cases h with
    | mk heq => exact heq
  · intro heq
    exact .mk v t gs heq

/-- Forward direction: `ValueEq` implies the `flattenValue` equality. Often
easier to apply than the `iff` in intro-elimination contexts. -/
theorem ValueEq.flattenValue_eq
    {decls : Decls} {funcIdx : Global → Option Nat}
    {v : Value} {t : Typ} {gs : Array G}
    (h : ValueEq decls funcIdx v t gs) :
    flattenValue decls funcIdx v = gs := by
  cases h with
  | mk heq => exact heq

/-- Backward direction: every value has a canonical flat encoding via
`flattenValue`, and that encoding is a `ValueEq` witness for any `t`. -/
theorem ValueEq.of_flattenValue
    (decls : Decls) (funcIdx : Global → Option Nat)
    (v : Value) (t : Typ) :
    ValueEq decls funcIdx v t (flattenValue decls funcIdx v) :=
  .mk v t (flattenValue decls funcIdx v) rfl

/-! ## `IOBuffer.equiv` equivalence properties.

`IOBuffer.equiv` = `a == b` using a custom `BEq IOBuffer` instance.
The BEq IOKeyInfo + BEq IOBuffer instances are `@[expose]`'d in
`Bytecode/ExecuteFfi.lean`. -/

-- IOBuffer.equiv_refl/symm/trans imported from Proofs/IOBufferEquiv.lean.

/-! ## `InterpResultEq` composition lemmas (sorried except `trans`). -/

/-- Transitivity of `InterpResultEq` composing via a middle source-level result. -/
theorem InterpResultEq.trans
    {decls : Decls} {funcIdx : Global → Option Nat} {retTyp : Typ}
    (src : Except Source.Eval.SourceError (Value × IOBuffer))
    (mid : Except Source.Eval.SourceError (Value × IOBuffer))
    (bc  : Except Bytecode.Eval.BytecodeError (Array G × IOBuffer))
    (h_sm : match src, mid with
            | .ok (v₁, io₁), .ok (v₂, io₂) =>
                flattenValue decls funcIdx v₁ = flattenValue decls funcIdx v₂
                  ∧ IOBuffer.equiv io₁ io₂
            | .error _, .error _ => True
            | _, _ => False)
    (h_mb : InterpResultEq decls funcIdx retTyp mid bc) :
    InterpResultEq decls funcIdx retTyp src bc := by
  unfold InterpResultEq at *
  match src, mid, bc with
  | .ok (v₁, io₁), .ok (v₂, io₂), .ok (gs, io₃) =>
      obtain ⟨hflat, hio12⟩ := h_sm
      obtain ⟨hVEq, hio23⟩ := h_mb
      refine ⟨?_, IOBuffer.equiv_trans hio12 hio23⟩
      cases hVEq with
      | mk h23 => exact ValueEq.mk v₁ retTyp gs (hflat.trans h23)
  | .ok _, .ok _, .error _ => exact h_mb.elim
  | .ok _, .error _, _ => exact h_sm.elim
  | .error _, .ok _, _ => exact h_sm.elim
  | .error _, .error _, .ok _ => trivial
  | .error _, .error _, .error _ => trivial

/-- Pointwise flattenValue-equality helper for `.attach.flatMap` over Value arrays. -/
private theorem attach_flatMap_eq_pw {vs : Array Value}
    {g₁ g₂ : Value → Array G}
    (h : ∀ v ∈ vs, g₁ v = g₂ v) :
    vs.attach.flatMap (fun ⟨v, _⟩ => g₁ v) =
    vs.attach.flatMap (fun ⟨v, _⟩ => g₂ v) := by
  congr 1
  funext ⟨v, hv⟩
  exact h v hv

/-- `flattenValue` agrees under `funcIdx` vs `funcIdx.map remap` for every
value when they agree pointwise on every `.fn g`. -/
theorem flattenValue_transport_remap
    (decls : Decls) (f : Global → Option Nat) (remap : Nat → Nat)
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                     flattenValue decls (fun g' => (f g').map remap) (.fn g)) :
    ∀ (v : Value),
      flattenValue decls f v =
      flattenValue decls (fun g => (f g).map remap) v
  | .unit        => by unfold flattenValue; rfl
  | .field _     => by unfold flattenValue; rfl
  | .pointer _ _ => by unfold flattenValue; rfl
  | .fn g        => hfn_free g
  | .tuple vs    => by
      unfold flattenValue
      exact attach_flatMap_eq_pw
        (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
  | .array vs    => by
      unfold flattenValue
      exact attach_flatMap_eq_pw
        (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
  | .ctor g args => by
      unfold flattenValue
      have h_args : args.attach.flatMap
          (fun ⟨v, _⟩ => flattenValue decls f v) =
        args.attach.flatMap
          (fun ⟨v, _⟩ => flattenValue decls (fun g' => (f g').map remap) v) :=
        attach_flatMap_eq_pw
          (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
      split <;> simp [h_args]
termination_by v => sizeOf v

/-- Transport `ValueEq` across a funcIdx remap. Entry-function return values
are fn-free, which makes the remap-irrelevant (no `.fn` ids to renumber). -/
theorem ValueEq.transport_remap
    {decls : Decls} {f : Global → Option Nat}
    {remap : Nat → Nat} {v : Value} {t : Typ} {gs : Array G}
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                      flattenValue decls (fun g' => (f g').map remap) (.fn g))
    (h : flattenValue decls f v = gs) :
    ValueEq decls (fun g => (f g).map remap) v t gs :=
  .mk v t gs (by rw [← flattenValue_transport_remap decls f remap hfn_free v]; exact h)

/-- Transport `InterpResultEq` across a funcIdx remap. -/
theorem InterpResultEq.transport_remap
    {decls : Decls} {f : Global → Option Nat}
    {remap : Nat → Nat} {retTyp : Typ}
    {src : Except Source.Eval.SourceError (Value × IOBuffer)}
    {bc  : Except Bytecode.Eval.BytecodeError (Array G × IOBuffer)}
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                      flattenValue decls (fun g' => (f g').map remap) (.fn g))
    (h : InterpResultEq decls f retTyp src bc) :
    InterpResultEq decls (fun g => (f g).map remap) retTyp src bc := by
  unfold InterpResultEq at *
  match src, bc with
  | .ok (v, io₁), .ok (gs, io₂) =>
    obtain ⟨hVE, hIO⟩ := h
    refine ⟨?_, hIO⟩
    cases hVE with
    | mk hflat => exact ValueEq.transport_remap hfn_free hflat
  | .ok _, .error _ => exact h.elim
  | .error _, .ok _ => trivial
  | .error _, .error _ => trivial

/-! ## `Flatten.args` composition lemmas. -/

theorem Flatten.args_transport_remap
    (decls : Decls) (f : Global → Option Nat)
    (remap : Nat → Nat) (args : List Value)
    (hfn_free : ∀ v ∈ args,
      flattenValue decls f v = flattenValue decls (fun g' => (f g').map remap) v) :
    Flatten.args decls f args =
      Flatten.args decls (fun g => (f g).map remap) args := by
  unfold Flatten.args
  -- Both sides are `args.foldl (fun acc v => acc ++ flattenValue … v) #[]`.
  -- Pointwise equal step functions on `args` ⇒ equal foldl result.
  suffices h : ∀ (acc : Array G),
      args.foldl (fun a v => a ++ flattenValue decls f v) acc =
      args.foldl (fun a v => a ++ flattenValue decls (fun g => (f g).map remap) v) acc by
    exact h #[]
  induction args with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [hfn_free hd List.mem_cons_self]
    exact ih (fun v hv => hfn_free v (List.mem_cons_of_mem _ hv)) _

theorem Flatten.args_congr (decls : Decls) (f g : Global → Option Nat)
    (args : List Value) (h : f = g) :
    Flatten.args decls f args = Flatten.args decls g args := by
  rw [h]

/-! ## `Value.FnFree` — first-class-function-free values.

A value in this fragment flattens identically under any `funcIdx` mapping,
since `flattenValue` only consults `funcIdx` at `.fn` leaves. -/

/-- `Value.FnFree` — no `.fn` constructor appears anywhere in the value. -/
inductive Value.FnFree : Value → Prop
  | unit : Value.FnFree .unit
  | field (g : G) : Value.FnFree (.field g)
  | pointer (w i : Nat) : Value.FnFree (.pointer w i)
  | tuple {vs : Array Value} :
      (∀ v ∈ vs, Value.FnFree v) → Value.FnFree (.tuple vs)
  | array {vs : Array Value} :
      (∀ v ∈ vs, Value.FnFree v) → Value.FnFree (.array vs)
  | ctor (g : Global) {args : Array Value} :
      (∀ v ∈ args, Value.FnFree v) → Value.FnFree (.ctor g args)

private theorem attach_flatMap_eq {vs : Array Value} {decls : Decls}
    {f₁ f₂ : Global → Option Nat}
    (ih : ∀ v ∈ vs, Value.FnFree v →
      flattenValue decls f₁ v = flattenValue decls f₂ v)
    (hfn : ∀ v ∈ vs, Value.FnFree v) :
    vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls f₁ v) =
    vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls f₂ v) := by
  congr 1
  funext ⟨x, hx⟩
  exact ih x hx (hfn x hx)

/-- For `.fn`-free values the `funcIdx` argument is immaterial — any two
funcIdx mappings give the same `flattenValue` output. -/
theorem flattenValue_funcIdx_irrelevant_of_fnFree
    (decls : Decls) (f₁ f₂ : Global → Option Nat) :
    ∀ (v : Value), v.FnFree →
      flattenValue decls f₁ v = flattenValue decls f₂ v
  | .unit, _ | .field _, _ | .pointer _ _, _ => by unfold flattenValue; rfl
  | .fn _, h => nomatch h
  | .tuple vs, .tuple h => by
    unfold flattenValue
    exact attach_flatMap_eq
      (fun v hv hfv => flattenValue_funcIdx_irrelevant_of_fnFree decls f₁ f₂ v hfv) h
  | .array vs, .array h => by
    unfold flattenValue
    exact attach_flatMap_eq
      (fun v hv hfv => flattenValue_funcIdx_irrelevant_of_fnFree decls f₁ f₂ v hfv) h
  | .ctor g args, .ctor _ h => by
    unfold flattenValue
    have hfm := attach_flatMap_eq
      (fun v hv hfv => flattenValue_funcIdx_irrelevant_of_fnFree decls f₁ f₂ v hfv) h
    split <;> simp [hfm]
termination_by v _ => sizeOf v

/-- `ValueEq` is independent of `funcIdx` for `.fn`-free values. -/
theorem ValueEq.funcIdx_irrelevant_of_fnFree
    {decls : Decls} {f₁ f₂ : Global → Option Nat}
    {v : Value} {t : Typ} {gs : Array G}
    (hfn : v.FnFree)
    (heq : ValueEq decls f₁ v t gs) :
    ValueEq decls f₂ v t gs := by
  obtain ⟨h⟩ := heq
  exact .mk v t gs (by rw [← h]; exact (flattenValue_funcIdx_irrelevant_of_fnFree decls f₁ f₂ v hfn).symm)

/-- `Flatten.args` transport from `FnFree` args. -/
theorem Flatten.args_transport_remap_of_fnFree
    (decls : Decls) (f : Global → Option Nat)
    (remap : Nat → Nat) (args : List Value)
    (hFnFree : ∀ v ∈ args, Value.FnFree v) :
    Flatten.args decls f args =
      Flatten.args decls (fun g => (f g).map remap) args :=
  Flatten.args_transport_remap decls f remap args
    (fun v hv => flattenValue_funcIdx_irrelevant_of_fnFree
                  decls f (fun g => (f g).map remap) v (hFnFree v hv))

/-- Transport `InterpResultEq` across a funcIdx remap when the source result
is known to produce an `FnFree` value on success. -/
theorem InterpResultEq.transport_remap_of_src_fnFree
    {decls : Decls} {f : Global → Option Nat}
    {remap : Nat → Nat} {retTyp : Typ}
    {src : Except Source.Eval.SourceError (Value × IOBuffer)}
    {bc  : Except Bytecode.Eval.BytecodeError (Array G × IOBuffer)}
    (hSrcFnFree : ∀ v io, src = .ok (v, io) → Value.FnFree v)
    (h : InterpResultEq decls f retTyp src bc) :
    InterpResultEq decls (fun g => (f g).map remap) retTyp src bc := by
  unfold InterpResultEq at *
  match src, bc with
  | .ok (v, io₁), .ok (gs, io₂) =>
    obtain ⟨hVE, hIO⟩ := h
    refine ⟨?_, hIO⟩
    cases hVE with
    | mk hflat =>
      have hv : v.FnFree := hSrcFnFree v io₁ rfl
      refine .mk v retTyp gs ?_
      rw [← flattenValue_funcIdx_irrelevant_of_fnFree decls f
          (fun g => (f g).map remap) v hv]
      exact hflat
  | .ok _, .error _ => exact h.elim
  | .error _, .ok _ => trivial
  | .error _, .error _ => trivial

end Aiur

end
