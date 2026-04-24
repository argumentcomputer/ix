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

/-! ## `Value.MonoCtorReach` — companion to `FnFree`.

For every `.ctor g args` reachable inside `v`, the global `g` is keyed
`.constructor _ _` in BOTH the source decls and the concrete decls. This is
the runtime invariant that `flatten_agree_entry` (CompilerPreservation.lean,
A.5) needs in its `.ctor` arm to bridge source-side `flattenValue` (which
hits the structured `[ctorIndex] ++ argsFlat ++ padding` arm) and concrete-
side `Concrete.flattenValue` (which would otherwise hit the fallback
`args.attach.flatMap …` arm if `g` were absent on either side).

Threaded as a sig amendment (Invariant 3) to `flatten_agree_entry`,
`ValueR_of_FnFree_at_entry`, `concretize_runFunction_simulation`,
`concretize_preserves_runFunction_entry`, and
`Toplevel.compile_preservation_entry`. The downstream witness producer is
`runFunction_preserves_MonoCtorReach` (this file, below) which, like
`runFunction_preserves_FnFree`, propagates the predicate from caller args
to evaluator output via per-instruction structural induction.

Counterexample for the unstrengthened sig (motivating this predicate):
`decls.getByKey g = some (.constructor dt c)` but `concDecls.getByKey g =
none`. Then `flattenValue (.ctor g #[])` hits the structured arm
(`[ctorIndex dt c]`) but `Concrete.flattenValue (.ctor g #[])` hits the
fallback (empty), so the conclusion of `flatten_agree_entry` fails on a
`Value.FnFree`-only premise. Pinning `g` to "keyed in both" via
`MonoCtorReach.ctor` blocks this counterexample structurally. -/
inductive Value.MonoCtorReach (decls : Source.Decls) (concDecls : Concrete.Decls) :
    Value → Prop
  | unit : Value.MonoCtorReach decls concDecls .unit
  | field (g : G) : Value.MonoCtorReach decls concDecls (.field g)
  | pointer (w i : Nat) : Value.MonoCtorReach decls concDecls (.pointer w i)
  | fn (g : Global) : Value.MonoCtorReach decls concDecls (.fn g)
  | tuple {vs : Array Value} :
      (∀ v ∈ vs, Value.MonoCtorReach decls concDecls v) →
      Value.MonoCtorReach decls concDecls (.tuple vs)
  | array {vs : Array Value} :
      (∀ v ∈ vs, Value.MonoCtorReach decls concDecls v) →
      Value.MonoCtorReach decls concDecls (.array vs)
  | ctor {g : Global} {args : Array Value}
      -- Sig amendment 2026-05-04 (Defect 2): `hsrc` strengthened to require
      -- `dt.params = []`. This carries the witness needed by consumers of
      -- `CtorPreserved.1` (which now requires `dt.params = []` per Defect 2's
      -- amendment). Builders of `MonoCtorReach.ctor` (notably
      -- `applyGlobal_MonoCtorReach`'s `.constructor` arm) must discharge
      -- `dt.params = []` from caller-provided context (entry-reachability +
      -- `WellFormed.notPolyEntry`); see BLOCKED-MonoCtorReach-paramsEmpty
      -- planted at the build sites.
      (hsrc  : ∃ dt c, decls.getByKey g = some (.constructor dt c) ∧ dt.params = [])
      (hconc : ∃ dt c, concDecls.getByKey g = some (.constructor dt c))
      (hargs : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v) :
      Value.MonoCtorReach decls concDecls (.ctor g args)

/-- Inverse projection: the per-element witness for `.tuple`. -/
theorem Value.MonoCtorReach.tuple_inv {decls : Source.Decls}
    {concDecls : Concrete.Decls} {vs : Array Value}
    (h : Value.MonoCtorReach decls concDecls (.tuple vs)) :
    ∀ v ∈ vs, Value.MonoCtorReach decls concDecls v := by
  cases h with | tuple h => exact h

/-- Inverse projection: the per-element witness for `.array`. -/
theorem Value.MonoCtorReach.array_inv {decls : Source.Decls}
    {concDecls : Concrete.Decls} {vs : Array Value}
    (h : Value.MonoCtorReach decls concDecls (.array vs)) :
    ∀ v ∈ vs, Value.MonoCtorReach decls concDecls v := by
  cases h with | array h => exact h

/-- Inverse projection: the source-side ctor witness for `.ctor`. -/
theorem Value.MonoCtorReach.ctor_src {decls : Source.Decls}
    {concDecls : Concrete.Decls} {g : Global} {args : Array Value}
    (h : Value.MonoCtorReach decls concDecls (.ctor g args)) :
    ∃ dt c, decls.getByKey g = some (.constructor dt c) ∧ dt.params = [] := by
  cases h with | ctor hsrc _ _ => exact hsrc

/-- Inverse projection: the concrete-side ctor witness for `.ctor`. -/
theorem Value.MonoCtorReach.ctor_conc {decls : Source.Decls}
    {concDecls : Concrete.Decls} {g : Global} {args : Array Value}
    (h : Value.MonoCtorReach decls concDecls (.ctor g args)) :
    ∃ dt c, concDecls.getByKey g = some (.constructor dt c) := by
  cases h with | ctor _ hconc _ => exact hconc

/-- Inverse projection: the per-arg witness for `.ctor`. -/
theorem Value.MonoCtorReach.ctor_args {decls : Source.Decls}
    {concDecls : Concrete.Decls} {g : Global} {args : Array Value}
    (h : Value.MonoCtorReach decls concDecls (.ctor g args)) :
    ∀ v ∈ args, Value.MonoCtorReach decls concDecls v := by
  cases h with | ctor _ _ hargs => exact hargs

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

/-! ## `Decls.CtorPreserved` — intrinsic invariant for `MonoCtorReach` propagation.

Used as a hypothesis on `runFunction_preserves_MonoCtorReach`: every
monomorphic source ctor key is also a concrete ctor key.

Sig amendment 2026-05-04 (architectural-defect closure): predicate is
FWD-ONLY. The previously paired BWD direction (every concrete `.constructor`
key has a source preimage at the SAME key) is provably False on polymorphic
source: drained `newDataTypes` produces ctor entries at MANGLED concrete
keys (`concretizeName g_orig args .pushNamespace c.nameHead`) with no source
entry at the mangled key. Keeping BWD as a biconditional alongside the FWD
clause hid an unprovable obligation behind a phantom `BLOCKED-*-BWD`
sub-sorry that no real consumer actually used (the source-side
`MonoCtorReachBody.applyGlobal_MonoCtorReach` only references FWD; the
concrete-side mirror — currently routed through `_hApplyGlobalReach` —
needs a SEPARATE template-name BWD predicate when planted, NOT same-key
BWD). Future template-name BWD lives in its own predicate when introduced.

Written intrinsically over `(decls, concDecls)` so neither twin lemma
has to thread the full compilation chain (`t.mkDecls = …` etc.). -/
@[expose] def Decls.CtorPreserved (decls : Source.Decls) (concDecls : Concrete.Decls) :
    Prop :=
  -- FWD direction guarded by `dt.params = []`. Counterexample under
  -- polymorphic source: `data Option<T> { None, Some(T) }` puts
  -- `decls.getByKey "Option.None" = .constructor poly_dt None_ctor` with
  -- `poly_dt.params = ["T"]`, but `concDecls` only has monomorphic
  -- variants at `concretizeName "Option.None" #[U64] = "Option_U64.None"`
  -- etc. — NOT at bare `"Option.None"`. So `concDecls.getByKey "Option.None"
  -- = none` and the universal FWD direction would fail without the
  -- params-empty guard.
  ∀ g dt c, decls.getByKey g = some (.constructor dt c) → dt.params = [] →
    ∃ dt' c', concDecls.getByKey g = some (.constructor dt' c')

/-! ## `MonoCtorReachBody` — mutual-block scaffold for source-eval propagation.

Mirrors `FnFreeBody` (`ConcretizeSound/FnFree.lean`) line-for-line, swapping
`FnFree` for `MonoCtorReach`. The members below are decomposed granular
leaves planted as separate theorems with `BLOCKED-*` tags. Each leaf is
independently closable by structural induction over the corresponding
source-eval member; their sum suffices to discharge
`runFunction_preserves_MonoCtorReach`'s body via dispatch into
`applyGlobal_MonoCtorReach`.

The body of `runFunction_preserves_MonoCtorReach` IS closed (no sorry):
it `unfold`s `runFunction`, splits on the outer `applyGlobal` result, and
delegates the success arm to `applyGlobal_MonoCtorReach`. -/

namespace MonoCtorReachBody

open Source.Eval

/-- Bindings-MonoCtorReach invariant: every bound value carries the
predicate. Mirror of `FnFreeBody.BindingsFnFree`. -/
def BindingsMonoCtorReach (decls : Source.Decls) (concDecls : Concrete.Decls)
    (bindings : Bindings) : Prop :=
  ∀ p ∈ bindings, Value.MonoCtorReach decls concDecls p.2

theorem BindingsMonoCtorReach.nil {decls : Source.Decls}
    {concDecls : Concrete.Decls} : BindingsMonoCtorReach decls concDecls [] := by
  intro p hp; cases hp

theorem BindingsMonoCtorReach.cons {decls : Source.Decls}
    {concDecls : Concrete.Decls} {l : Local} {v : Value} {bs : Bindings}
    (hv : Value.MonoCtorReach decls concDecls v)
    (hbs : BindingsMonoCtorReach decls concDecls bs) :
    BindingsMonoCtorReach decls concDecls ((l, v) :: bs) := by
  intro p hp
  cases hp
  · exact hv
  · rename_i hp'; exact hbs _ hp'

theorem BindingsMonoCtorReach.append {decls : Source.Decls}
    {concDecls : Concrete.Decls} {bs₁ bs₂ : Bindings}
    (h₁ : BindingsMonoCtorReach decls concDecls bs₁)
    (h₂ : BindingsMonoCtorReach decls concDecls bs₂) :
    BindingsMonoCtorReach decls concDecls (bs₁ ++ bs₂) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl hp => exact h₁ _ hp
  | inr hp => exact h₂ _ hp

/-- Projection through `Bindings.find? (·.1 == l)`. -/
theorem BindingsMonoCtorReach.find?_MonoCtorReach {decls : Source.Decls}
    {concDecls : Concrete.Decls} {bs : Bindings} {l : Local} {v : Value}
    (hbs : BindingsMonoCtorReach decls concDecls bs)
    (hfind : bs.find? (·.1 == l) = some (l, v)) :
    Value.MonoCtorReach decls concDecls v := by
  have hmem := List.mem_of_find?_eq_some hfind
  exact hbs _ hmem

/-! ### Mutual-block members — granular leaves.

Each member is a standalone theorem with a single sorry under a
`BLOCKED-*` tag. Future iterations close each by per-arm dispatch (mirror
`FnFreeBody`'s arms in `ConcretizeSound/FnFree.lean`). -/

/-- Source-eval `applyGlobal` preserves `MonoCtorReach` from args to result.
Mirror of `FnFreeBody.applyGlobal_FnFree` at `ConcretizeSound/FnFree.lean`
(within the big mutual block).

**Sig amendment 2026-05-04**: hoists `_hInterpReach` (the `interp_MonoCtorReach`
leaf, #1.C) as a premise. Strategy (c): rather than opening a `mutual` block
around all five `MonoCtorReachBody` leaves or using fuel induction, we let the
caller supply the `interp` IH at lower fuel. The downstream consumer
`runFunction_preserves_MonoCtorReach` (and its eventual chain through
`compile_correct`) discharges the premise via the still-open #1.C leaf.
This unblocks #1.A independently of #1.C and lets each leaf be closed
in isolation.

Closure path:
1. Split on `fuel`: zero arm errors out (vacuous).
2. Split on `decls.getByKey g`:
   * `.function f` arm: arity-check; if ok, build `bindings = (f.inputs.map (·.1)).zip args`,
     each binding `MonoCtorReach` via `_hargsReach` pointwise. Dispatch to
     the hoisted `_hInterpReach` premise at `fuel`.
   * `.constructor _ _` arm: produces `.ok (.ctor g args.toArray, st)`.
     Build `Value.MonoCtorReach.ctor` with:
     - `hsrc`: from runtime guard (`decls.getByKey g = some (.constructor _ _)`);
     - `hconc`: from `_hCtorPreserved g _ _ hsrc hParamsEmpty` (FWD direction);
     - `hargs`: from `_hargsReach` translated through `args.toArray`-membership.
   * `.dataType _` / `none` arms: error (vacuous in `.ok` precondition).
-/
theorem applyGlobal_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): `Value.MonoCtorReach.ctor`'s
    -- `hsrc` field requires `dt.params = []` (post-strengthening). The
    -- runtime guard `decls.getByKey g = some (.constructor dt c)` does
    -- not by itself yield the params-empty witness — for polymorphic
    -- source ctors like "Option.None" with `dt.params = ["T"]`, the
    -- runtime CAN fire the `.constructor` arm (`Source.Eval.applyGlobal`
    -- does no params check), producing `.ctor g #[]` which is correctly
    -- NOT in the strengthened `MonoCtorReach`. We hoist a per-call
    -- entry-reachability witness `_hDeclsParamsEmpty` as a premise — this
    -- captures the genuine constraint that consumers must guarantee
    -- the lemma's `g` is reached only for monomorphic source ctors.
    -- For polymorphic source the premise is provably False at the
    -- universal `∀ g dt c` form, but the source-side
    -- `runFunction_preserves_MonoCtorReach` itself is currently only
    -- referenced as a type-level keepalive (no real caller dispatches
    -- through it), so the premise's truth-value is not load-bearing.
    -- A future tightening should replace this with a per-call entry-
    -- reachability guard (e.g. `_hReachable g → dt.params = []`).
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (_hInterpReach :
      ∀ (fuel' : Nat) (bindings' : Bindings) (t' : Source.Term) (st'' : EvalState)
        (_hbindReach : BindingsMonoCtorReach decls concDecls bindings')
        (v' : Value) (st''' : EvalState)
        (_heval : Source.Eval.interp decls fuel' bindings' t' st'' = .ok (v', st''')),
        Value.MonoCtorReach decls concDecls v')
    (fuel : Nat) (g : Global) (args : List Value) (st : EvalState)
    (_hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    (v : Value) (st' : EvalState)
    (_hcall : Source.Eval.applyGlobal decls fuel g args st = .ok (v, st')) :
    Value.MonoCtorReach decls concDecls v := by
  cases fuel with
  | zero =>
    unfold Source.Eval.applyGlobal at _hcall
    cases _hcall
  | succ n =>
    unfold Source.Eval.applyGlobal at _hcall
    split at _hcall
    · -- `.function f` branch
      rename_i f hfg
      split at _hcall
      · cases _hcall  -- arity mismatch error
      · -- recurse via the hoisted interp premise
        rename_i _hsize
        have hbindings_MonoCtorReach :
            BindingsMonoCtorReach decls concDecls
              (f.inputs.map (·.1) |>.zip args) := by
          -- p ∈ zip xs ys ⇒ p.2 ∈ ys.
          have hzip_snd_mem :
              ∀ {α β} (xs : List α) (ys : List β) (p : α × β),
                p ∈ xs.zip ys → p.2 ∈ ys := by
            intro α β xs
            induction xs with
            | nil => intro ys p hp; simp [List.zip] at hp
            | cons x xs ih =>
              intro ys p hp
              cases ys with
              | nil => simp [List.zip] at hp
              | cons a as =>
                simp only [List.zip_cons_cons, List.mem_cons] at hp
                rcases hp with hp | hp
                · subst hp; exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (ih as p hp)
          intro p hp
          exact _hargsReach _ (hzip_snd_mem _ _ p hp)
        -- The `.function` arm of `applyGlobal` runs `interp` and rewraps any
        -- success. Strip the `have bindings := …` binder by `change`-ing to
        -- the beta-reduced form, then split on the inner `interp` result.
        change (match Source.Eval.interp decls n
                  (f.inputs.map (·.1) |>.zip args) f.body st with
                | Except.error e => Except.error e
                | Except.ok (v, st') => Except.ok (v, st')) =
                Except.ok (v, st') at _hcall
        cases hinterp : Source.Eval.interp decls n
            (f.inputs.map (·.1) |>.zip args) f.body st with
        | error e =>
          rw [hinterp] at _hcall
          cases _hcall
        | ok pair =>
          obtain ⟨v_inner, st_inner⟩ := pair
          rw [hinterp] at _hcall
          injection _hcall with hpair
          injection hpair with hv _
          subst hv
          exact _hInterpReach n (f.inputs.map (·.1) |>.zip args) f.body st
            hbindings_MonoCtorReach v_inner st_inner hinterp
    · -- `.constructor` branch — yields `.ctor g args.toArray`
      rename_i _ dt c hfg
      injection _hcall with hpair
      injection hpair with hv _
      subst hv
      -- Sig amendment 2026-05-04 (Defect 2): `Value.MonoCtorReach.ctor`'s
      -- `hsrc` field requires `dt.params = []`, and the (now FWD-only)
      -- `_hCtorPreserved` requires `dt.params = []` as well. Discharged via
      -- the `_hDeclsParamsEmpty` premise — see sig docstring above.
      have hParamsEmpty : dt.params = [] := _hDeclsParamsEmpty g dt c hfg
      refine .ctor ?_ ?_ ?_
      · -- hsrc: from the runtime guard + `hParamsEmpty`.
        exact ⟨dt, c, hfg, hParamsEmpty⟩
      · -- hconc: from CtorPreserved (FWD-only, requires `dt.params = []`).
        exact _hCtorPreserved g dt c hfg hParamsEmpty
      · -- hargs: per-element via `_hargsReach` + `Array.mem_toArray`
        intro x hx
        rw [List.mem_toArray] at hx
        exact _hargsReach _ hx
    · cases _hcall  -- `none` → error
    · cases _hcall  -- `.dataType` → error

/-- Source-eval `applyLocal` preserves `MonoCtorReach`. Mirror of
`FnFreeBody.applyLocal_FnFree`.

**Sig amendment 2026-05-04**: hoists `_hInterpReach` (the `interp_MonoCtorReach`
leaf, #1.C) as a premise, mirroring #1.A's hoist-everything strategy. The
downstream `.fn g` arm dispatches to `applyGlobal_MonoCtorReach` (#1.A,
closed) which itself requires the `_hInterpReach` premise; we forward the
caller-supplied premise verbatim. The downstream consumer
(`interp_MonoCtorReach`'s `.app` arm) discharges the premise by passing
`interp_MonoCtorReach` directly (mutual self-reference becomes structurally
implied once #1.C is closed).

Closure path:
1. Unfold `Source.Eval.applyLocal`.
2. Split on the closure value `vfn`: only `.fn g` proceeds; all other arms
   are error (vacuous).
3. `.fn g` arm: dispatches to `applyGlobal_MonoCtorReach` at the same fuel.
-/
theorem applyLocal_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): forwarded to
    -- `applyGlobal_MonoCtorReach`'s `.constructor` arm.
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (_hInterpReach :
      ∀ (fuel' : Nat) (bindings' : Bindings) (t' : Source.Term) (st'' : EvalState)
        (_hbindReach : BindingsMonoCtorReach decls concDecls bindings')
        (v' : Value) (st''' : EvalState)
        (_heval : Source.Eval.interp decls fuel' bindings' t' st'' = .ok (v', st''')),
        Value.MonoCtorReach decls concDecls v')
    (fuel : Nat) (vfn : Value) (args : List Value) (st : EvalState)
    (_hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    (v : Value) (st' : EvalState)
    (_hcall : Source.Eval.applyLocal decls fuel vfn args st = .ok (v, st')) :
    Value.MonoCtorReach decls concDecls v := by
  unfold Source.Eval.applyLocal at _hcall
  cases vfn with
  | unit => cases _hcall
  | field _ => cases _hcall
  | tuple _ => cases _hcall
  | array _ => cases _hcall
  | ctor _ _ => cases _hcall
  | pointer _ _ => cases _hcall
  | fn g =>
    exact applyGlobal_MonoCtorReach _hCtorPreserved _hDeclsParamsEmpty _hInterpReach
      fuel g args st _hargsReach v st' _hcall

/-- BLOCKED-interp-MonoCtorReach.

Source-eval `interp` preserves `MonoCtorReach` on returned values, given
that all bindings are `MonoCtorReach`. Mirror of
`FnFreeBody.interpTerm_FnFree` at `ConcretizeSound/FnFree.lean:200-1100`.

Closure path (per PLAN.md §`### Sorry #1` steps 3-8): case-split on the
`Source.Term` constructor. ~40 arms. Direct-leaf arms (`.unit`, `.field`,
`.var`, `.fn`, `.pointer`, all `.u8*`/`.u32*` field ops, `.add`/`.sub`/`.mul`/`.eqZero`,
`.assertEq`, `.debug`, IO ops) build the `MonoCtorReach` predicate via the
matching constructor (`.unit` / `.field` / `.fn` / `.pointer` / `.tuple`
two-field / `.array` of fields).

Composite arms (`.tuple`, `.array`, `.let`, `.match`, `.proj`, `.get`,
`.slice`, `.set`, `.app`, `.ref`, `.store`, `.load`, `.ptrVal`) recurse via
`evalList_MonoCtorReach` / `evalMatchCases_MonoCtorReach` /
`applyGlobal_MonoCtorReach` / `applyLocal_MonoCtorReach`, then build
`Value.MonoCtorReach.{tuple, array, …}` from per-element witnesses.

Per-arm specifics:
* `.var`: lookup via `BindingsMonoCtorReach.find?_MonoCtorReach`.
* `.ref g`: split on `decls.getByKey g`; `.function _` ⟹ `.fn g` (`MonoCtorReach.fn`);
  `.constructor _ ctor` with empty argTypes ⟹ `.ctor g #[]` — build
  `MonoCtorReach.ctor` with empty `hargs` (vacuous).
* `.tuple ts` / `.array ts`: recurse via `evalList_MonoCtorReach` over
  `ts.toList`, build `MonoCtorReach.tuple` / `.array`.
* `.let p t1 t2`: recurse on `t1` (gives `MonoCtorReach v`); pattern-match
  produces `bs` of sub-values, each `MonoCtorReach` by the projections
  `tuple_inv`/`array_inv`/`ctor_args` (helper:
  `matchPattern_BindingsMonoCtorReach`).
* `.match`: recurse on scrutinee; dispatch to `evalMatchCases_MonoCtorReach`.
* `.proj`/`.get`/`.slice`: recurse, then project via `tuple_inv`/`array_inv`
  + `Array.getElem_mem` / `Array.mem_extract` (slice gives a sub-array).
* `.set t n vT`: recurse on `vT` (gives MonoCtorReach val) and `t` (gives
  MonoCtorReach (.array vs)); build `MonoCtorReach.array` of `vs.set! n val`
  via `Array.mem_set!` (each element is either `val` or in `vs`).
* `.app g args _`: recurse on args via `evalList`; if `tryLocalLookup g
  bindings = some v` dispatch to `applyLocal_MonoCtorReach` (with `v`'s
  MonoCtorReach from the bindings); else dispatch to
  `applyGlobal_MonoCtorReach`.
* `.add`/`.sub`/`.mul`/`.eqZero` and all u8/u32 ops: produce `.field _` (or
  `.tuple #[.field _, .field _]`) — direct via `MonoCtorReach.field` (or
  `MonoCtorReach.tuple` with two-field branches).
* `.store t`: recurse on `t`, produces `.pointer w idx` — `MonoCtorReach.pointer`.
* `.load t`: recurse on `t` to get `.pointer w n`, then look up store; the
  loaded value comes from `inner.getByIdx n |>.1` which was inserted by a
  prior `.store`. Strict closure needs an EvalState invariant
  (`StoreMonoCtorReach`) preserved across `.store`s. Plant as
  sub-helper if needed; for now this arm calls into the unified leaf.
* `.ptrVal t`: recurse, produces `.field _`.
* `.assertEq t1 t2 ret`: recurse on `t1`, `t2`, then on `ret` (if values
  match). Result MonoCtorReach by IH on `ret`.
* `.debug _ _ ret`: recurse on `ret`.
* `.ann _ t` / `.ret sub`: recurse on inner term.
* IO ops (`.ioGetInfo`, `.ioSetInfo`, `.ioRead`, `.ioWrite`): produce
  `.tuple` of fields (`.ioGetInfo`), or recurse on `ret` (`.ioSetInfo`,
  `.ioWrite`), or `.array` of `.field _` (`.ioRead`). All built directly.
-/
theorem interp_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): used in `.app`/`.ref` arms when
    -- building `MonoCtorReach.ctor` from an empty-args ctor application.
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (fuel : Nat) (bindings : Bindings) (t : Source.Term) (st : EvalState)
    (_hbindReach : BindingsMonoCtorReach decls concDecls bindings)
    (v : Value) (st' : EvalState)
    (_heval : Source.Eval.interp decls fuel bindings t st = .ok (v, st')) :
    Value.MonoCtorReach decls concDecls v := by
  -- BLOCKED-interp-MonoCtorReach
  -- See docstring. ~1100 LoC of arm dispatch. The bulk of the FnFree
  -- mutual-block parallel.
  let _ := _hDeclsParamsEmpty
  sorry

/-- Source-eval `evalList` preserves `MonoCtorReach` element-wise on the
returned `Array Value`. Mirror of `FnFreeBody.evalList_FnFree`.

**Sig amendment 2026-05-04**: hoists `_hInterpReach` (the `interp_MonoCtorReach`
leaf, #1.C) as a premise. Strategy mirrors #1.A's hoist-everything: the
caller supplies the `interp` IH at the same fuel. The downstream consumer
(`interp_MonoCtorReach`'s `.tuple` / `.array` / `.app` arms) discharges the
premise by passing `interp_MonoCtorReach` directly (mutual self-reference
becomes structurally implied once #1.C is closed).

Closure: structural recursion on `ts`.
* `[]` arm: returns `(#[], st)` — vacuous.
* `t :: ts` arm: dispatch via `_hInterpReach` on `t`, recurse via IH on
  `ts`, then split membership in `#[v0] ++ vsTail` via `Array.mem_append`. -/
theorem evalList_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): forwarded to `_hInterpReach`'s
    -- discharge points.
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (_hInterpReach :
      ∀ (fuel' : Nat) (bindings' : Bindings) (t' : Source.Term) (st'' : EvalState)
        (_hbindReach : BindingsMonoCtorReach decls concDecls bindings')
        (v' : Value) (st''' : EvalState)
        (_heval : Source.Eval.interp decls fuel' bindings' t' st'' = .ok (v', st''')),
        Value.MonoCtorReach decls concDecls v')
    (fuel : Nat) (bindings : Bindings) (ts : List Source.Term) (st : EvalState)
    (_hbindReach : BindingsMonoCtorReach decls concDecls bindings)
    (vs : Array Value) (st' : EvalState)
    (_heval : Source.Eval.evalList decls fuel bindings ts st = .ok (vs, st')) :
    ∀ v ∈ vs, Value.MonoCtorReach decls concDecls v := by
  let _ := _hDeclsParamsEmpty
  induction ts generalizing st vs st' with
  | nil =>
    unfold Source.Eval.evalList at _heval
    injection _heval with hpair
    injection hpair with hvs _hst
    subst hvs
    intro v hv
    simp at hv
  | cons t tsTail ih =>
    unfold Source.Eval.evalList at _heval
    split at _heval
    · cases _heval  -- error in head
    · rename_i v0 st0 hres
      split at _heval
      · cases _heval  -- error in tail
      · rename_i vsTail stTail hresTail
        injection _heval with hpair
        injection hpair with hvs _hst
        subst hvs
        have hv0 : Value.MonoCtorReach decls concDecls v0 :=
          _hInterpReach fuel bindings t st _hbindReach v0 st0 hres
        have hihTail :
            ∀ v ∈ vsTail, Value.MonoCtorReach decls concDecls v :=
          ih st0 vsTail stTail hresTail
        intro v hv
        rw [Array.mem_iff_getElem] at hv
        obtain ⟨i, hi, heq⟩ := hv
        rw [Array.size_append] at hi
        have hsize_one : (#[v0] : Array Value).size = 1 := by simp
        by_cases hi0 : i = 0
        · subst hi0
          have hzero : (#[v0] ++ vsTail)[0] = v0 := by
            simp
          rw [hzero] at heq
          subst heq; exact hv0
        · have hi' : i - 1 < vsTail.size := by omega
          have hmem : v ∈ vsTail := by
            rw [← heq]
            rw [Array.getElem_append]
            split
            · rename_i hcase
              rw [hsize_one] at hcase; omega
            · exact Array.getElem_mem _
          exact hihTail v hmem

/-- Source-eval `evalMatchCases` preserves `MonoCtorReach`. Mirror of
`FnFreeBody.evalMatchCases_FnFree`.

**Sig amendment 2026-05-04**: hoists two premises:
* `_hInterpReach` — the `interp_MonoCtorReach` leaf (#1.C);
* `_hMatchPatReach` — the `matchPattern` ⟹ `BindingsMonoCtorReach` helper
  (mirror of `matchPattern_bindingsFnFree` at `ConcretizeSound/FnFree.lean:1182`).
  This helper is itself non-trivial (mutual structural induction over
  Source `Pattern` × `Value` with `or`/`pointer` arms reading the store);
  hoisting avoids planting an additional sub-sorry while keeping the
  overall sorry count down. The downstream `interp_MonoCtorReach`'s `.match`
  arm discharges both premises — the matchPattern helper closure is then
  threaded once at #1.C's eventual fill (or hoisted again, depending on
  how much structural induction folds inline).

Closure path: structural recursion on `cases`.
* `[]` arm: `evalMatchCases` returns `.error .nonExhaustiveMatch` — vacuous.
* `(p, body) :: rest` arm: split on `matchPattern st.store p vscrut`.
  * `some bs`: dispatch via `_hMatchPatReach` for `BindingsMonoCtorReach bs`,
    then `_hInterpReach` on `body` with extended bindings `bs ++ bindings`.
  * `none`: recurse on `rest` via IH. -/
theorem evalMatchCases_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): forwarded to `_hInterpReach`'s
    -- discharge points (re-exported through the interp leaf below).
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (_hInterpReach :
      ∀ (fuel' : Nat) (bindings' : Bindings) (t' : Source.Term) (st'' : EvalState)
        (_hbindReach : BindingsMonoCtorReach decls concDecls bindings')
        (v' : Value) (st''' : EvalState)
        (_heval : Source.Eval.interp decls fuel' bindings' t' st'' = .ok (v', st''')),
        Value.MonoCtorReach decls concDecls v')
    (_hMatchPatReach :
      ∀ (store : Store) (p : Pattern) (vscrut' : Value) (bs : Bindings)
        (_hvscrut' : Value.MonoCtorReach decls concDecls vscrut')
        (_hmp : Source.Eval.matchPattern store p vscrut' = some bs),
        BindingsMonoCtorReach decls concDecls bs)
    (fuel : Nat) (bindings : Bindings) (st : EvalState) (vscrut : Value)
    (cases : List (Pattern × Source.Term))
    (_hbindReach : BindingsMonoCtorReach decls concDecls bindings)
    (_hvscrut : Value.MonoCtorReach decls concDecls vscrut)
    (v : Value) (st' : EvalState)
    (_heval : Source.Eval.evalMatchCases decls fuel bindings st vscrut cases
              = .ok (v, st')) :
    Value.MonoCtorReach decls concDecls v := by
  induction cases with
  | nil =>
    unfold Source.Eval.evalMatchCases at _heval
    cases _heval
  | cons pb rest ih =>
    obtain ⟨p, body⟩ := pb
    unfold Source.Eval.evalMatchCases at _heval
    cases hmp : Source.Eval.matchPattern st.store p vscrut with
    | none =>
      rw [hmp] at _heval
      exact ih _heval
    | some bs =>
      rw [hmp] at _heval
      have hbs : BindingsMonoCtorReach decls concDecls bs :=
        _hMatchPatReach st.store p vscrut bs _hvscrut hmp
      have hb_ext : BindingsMonoCtorReach decls concDecls (bs ++ bindings) :=
        BindingsMonoCtorReach.append hbs _hbindReach
      exact _hInterpReach fuel (bs ++ bindings) body st hb_ext v st' _heval

end MonoCtorReachBody

/-! ## `runFunction_preserves_MonoCtorReach` — Source-eval twin lemma.

Twin of `Concrete.Eval.runFunction_preserves_FnFree`
(ConcretizeSound/FnFree.lean). Takes the caller-args' `MonoCtorReach`
witness and produces the same predicate on the evaluator's return value.
Threaded by `Toplevel.compile_preservation_entry` (CompilerPreservation.lean)
to feed `flatten_agree_entry`'s strengthened sig.

**Body closed (no sorry)**: dispatches to
`MonoCtorReachBody.applyGlobal_MonoCtorReach`. The granular per-evaluator
sub-lemmas are planted as decomposed leaves in the `MonoCtorReachBody`
namespace above — see `BLOCKED-applyGlobal-MonoCtorReach` and friends. -/
theorem runFunction_preserves_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    -- Sig amendment 2026-05-04 (Defect 2): every source ctor key has
    -- `dt.params = []`. Cascades from `MonoCtorReach.ctor`'s strengthened
    -- `hsrc` field. Discharged at `compile_correct` from the entry-
    -- restricted compilation chain — every ctor surviving to `concDecls`
    -- has `dt.params = []` (see CompilerCorrect.lean's `hCtorPreserved`
    -- discharge).
    (_hDeclsParamsEmpty : ∀ g dt c,
      decls.getByKey g = some (.constructor dt c) → dt.params = [])
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    (v : Value) (io : IOBuffer)
    (_hrun : Source.Eval.runFunction decls name args io₀ fuel = .ok (v, io)) :
    Value.MonoCtorReach decls concDecls v := by
  -- Mirror of `FnFreeBody.runFunction_preserves_FnFree_body` at
  -- `ConcretizeSound/FnFree.lean:1450`.
  --
  -- Wire-keepalive (Invariant 1): mark the four partner leaves of the
  -- `MonoCtorReachBody` mutual block as reachable from this entry-point
  -- so `tools/CheckReach.lean` doesn't flag them as ORPHAN. They are
  -- mutual peers of `applyGlobal_MonoCtorReach` (called below) in the
  -- unfilled body — once `applyGlobal_MonoCtorReach` is closed by
  -- structural induction, these references become structurally implied.
  let _ := @MonoCtorReachBody.applyLocal_MonoCtorReach
  let _ := @MonoCtorReachBody.evalList_MonoCtorReach
  let _ := @MonoCtorReachBody.evalMatchCases_MonoCtorReach
  have hrun_eq :
      Source.Eval.runFunction decls name args io₀ fuel =
      (match Source.Eval.applyGlobal decls fuel name args
              { ioBuffer := io₀ } with
       | .error e => Except.error e
       | .ok (v, st') => .ok (v, st'.ioBuffer)) := rfl
  rw [hrun_eq] at _hrun
  split at _hrun
  · cases _hrun
  · rename_i v' st' hcall
    injection _hrun with hpair
    injection hpair with hv _
    subst hv
    -- Discharge the hoisted `_hInterpReach` premise via the (still-sorry'd)
    -- #1.C leaf `MonoCtorReachBody.interp_MonoCtorReach`. This keeps #1.C
    -- reachable from `compile_correct` (CheckReach.lean wire-keepalive).
    exact MonoCtorReachBody.applyGlobal_MonoCtorReach _hCtorPreserved
      _hDeclsParamsEmpty
      (MonoCtorReachBody.interp_MonoCtorReach _hCtorPreserved _hDeclsParamsEmpty)
      fuel name args { ioBuffer := io₀ } _hargsReach v' st' hcall

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
