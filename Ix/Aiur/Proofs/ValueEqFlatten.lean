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

/-! ## `Decls.CtorPreserved` — intrinsic decl-level invariant.

Used by `Aiur.Simulation.Decls.R` (`Simulation.lean`) as one of the
correspondence clauses bundling source and concrete decls for the
simulation chain's `step_R_preservation_applyGlobal`. Every monomorphic
source ctor key is also a concrete ctor key (FWD direction); every
concrete ctor entry has SOME source-side ctor preimage (BWD direction,
existential).

The predicate bundles a FWD direction (source `.constructor` with
`dt.params = []` ⟹ concrete `.constructor` at SAME key) AND a
template-name BWD direction (every concrete `.constructor` entry has
SOME source-side `.constructor` preimage at a possibly-mangled-by-
concretizeName key). The BWD clause is essential for the simulation's
`srcNone`/`srcDt` arms in `step_R_preservation_applyGlobal`
(Simulation.lean) — those arms must rule out concrete dispatching
`.constructor` at a key where source has `none`/`.dataType`, which
requires existence of a source preimage.

The FWD clause is guarded by `dt.params = []`. Counterexample under
polymorphic source: `data Option<T> { None, Some(T) }` puts
`decls.getByKey "Option.None" = .constructor poly_dt None_ctor` with
`poly_dt.params = ["T"]`, but `concDecls` only has monomorphic
variants at `concretizeName "Option.None" #[U64] = "Option_U64.None"`
etc. — NOT at bare `"Option.None"`. So the universal FWD direction
would fail without the params-empty guard.

The BWD clause is written existentially: `∃ g_src ...` rather than
demanding `concretizeName g_src tArgs = g_conc` directly. This is
because origin-4 ctor entries (drain's `newDataTypes` ctors) get
written at `dt'.name.pushNamespace c'.nameHead` where `dt'.name =
concretizeName g_orig args` — the relationship is `(concretizeName
g_orig args).pushNamespace c'.nameHead = g_conc`, NOT a single
`concretizeName g_src tArgs = g_conc`. The existential form sidesteps
this distinction by only asserting that SOME source preimage exists
(suffices for ruling out concrete-`.ctor` / source-`none` collisions).

Written intrinsically over `(decls, concDecls)` so neither twin lemma
has to thread the full compilation chain (`t.mkDecls = …` etc.). -/
@[expose] def Decls.CtorPreserved (decls : Source.Decls) (concDecls : Concrete.Decls) :
    Prop :=
  -- FWD direction guarded by `dt.params = []`.
  (∀ g dt c, decls.getByKey g = some (.constructor dt c) → dt.params = [] →
    ∃ dt' c', concDecls.getByKey g = some (.constructor dt' c')) ∧
  -- BWD (template-name shape, existential): every concrete-side
  -- `.constructor` entry has some source-side `.constructor` preimage.
  -- Closure path (in `compile_correct`'s discharge):
  --   step4Lower-backward (concrete `.ctor` → mono `.ctor`) +
  --   `concretizeBuild_ctor_origin` (mono `.ctor` → either typed `.ctor`
  --   at SAME key with `params = []`, OR drain's `newDataTypes` origin
  --   with `g_conc = dt'.name.pushNamespace c'.nameHead`). In origin 1,
  --   `g_src = g_conc`; in origin 4, source has `.ctor` at
  --   `dt_src.name.pushNamespace c.nameHead` where `dt_src` is the
  --   typed-source preimage of `dt'` (via `mkDecls_dt_implies_ctor_keys`
  --   + `checkAndSimplify` source-direction).
  (∀ g_conc cdt cc,
    concDecls.getByKey g_conc = some (.constructor cdt cc) →
    ∃ (g_src : Global) (dt : DataType) (c : Constructor),
      decls.getByKey g_src = some (.constructor dt c))


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

end -- public section
