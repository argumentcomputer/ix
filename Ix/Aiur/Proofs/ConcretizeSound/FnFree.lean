module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.MonoInvariants

/-!
`FnFreeBody` mutual block + `Concrete.Eval.runFunction_preserves_FnFree`.

Extracted from `ConcretizeSound.lean` 2026-04-29. Houses the consolidated
infrastructure for proving the concrete-eval preserves `FnFree` on returns,
parameterised over the four invariants `FirstOrderReturn` / `RefClosed` /
`TermRefsDt` / `TypesNotFunction`.
-/

public section

namespace Aiur

open Source

/-! ### `FnFreeBody` — ported body of `runFunction_preserves_FnFree`.

Ported from `Ix/Aiur/Proofs/FnFreeBodyScratch.lean` 2026-04-24. Houses the
consolidated infrastructure sorry together with the small FnFree lemmas and
the `ref_arm_FnFree` discharger that exercises `TermRefsDt`. The real theorem
below delegates its body to `FnFreeBody.runFunction_preserves_FnFree_body`. -/
def _fnFreeBody_docstub : Unit := ()

namespace FnFreeBody

open Concrete.Eval

/-! #### Small FnFree lemmas used by the trivial arms. -/

/-- FnFree cannot inhabit `.fn _`. -/
theorem FnFree_not_fn (g : Global) : ¬ Value.FnFree (.fn g) := fun h => nomatch h

/-- A unit-tuple value (two fields) is FnFree. -/
theorem FnFree_two_field_tuple (a b : G) :
    Value.FnFree (.tuple #[.field a, .field b]) := by
  refine .tuple ?_
  intro v hv
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .field _
  · exact .field _

/-- An array of `n` field values is FnFree. -/
theorem FnFree_ofFn_field (n : Nat) (f : Fin n → G) :
    Value.FnFree (.array (Array.ofFn fun (i : Fin n) => .field (f i))) := by
  refine .array ?_
  intro v hv
  rw [Array.mem_ofFn] at hv
  obtain ⟨i, hi⟩ := hv
  subst hi
  exact .field _

/-- Bindings-FnFree invariant. Every bound value is `FnFree`. -/
def BindingsFnFree (bindings : Bindings) : Prop :=
  ∀ p ∈ bindings, Value.FnFree p.2

theorem BindingsFnFree.nil : BindingsFnFree [] := by
  intro p hp; cases hp

theorem BindingsFnFree.cons {l : Local} {v : Value} {bs : Bindings}
    (hv : Value.FnFree v) (hbs : BindingsFnFree bs) :
    BindingsFnFree ((l, v) :: bs) := by
  intro p hp
  cases hp
  · exact hv
  · rename_i hp'; exact hbs _ hp'

theorem BindingsFnFree.append {bs₁ bs₂ : Bindings}
    (h₁ : BindingsFnFree bs₁) (h₂ : BindingsFnFree bs₂) :
    BindingsFnFree (bs₁ ++ bs₂) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl hp => exact h₁ _ hp
  | inr hp => exact h₂ _ hp

/-- Projection through `Bindings.find? (·.1 == l)`. -/
theorem BindingsFnFree.find?_FnFree {bs : Bindings} {l : Local} {v : Value}
    (hbs : BindingsFnFree bs)
    (hfind : bs.find? (·.1 == l) = some (l, v)) :
    Value.FnFree v := by
  have hmem := List.mem_of_find?_eq_some hfind
  exact hbs _ hmem

/-! #### `.ref` arm: closed under `TermRefsDt`. -/

/-- Under `TermRefsDt`, evaluating a top-level `.ref g` subterm that appears in
a function body succeeds only at `.ctor g #[]` (zero-arg constructor). Any
other successful shape would require `cd.getByKey g = some (.function _)`,
which `TermRefsDt` rules out at the bound `.ref` node.

This captures the sig-strengthening rationale for the `.ref` arm of the
mutual-induction heart. -/
theorem ref_arm_FnFree
    (cd : Concrete.Decls) (fuel : Nat) (bindings : Bindings)
    (typ : Concrete.Typ) (e : Bool) (g : Global)
    (st : EvalState) (v : Value) (st' : EvalState)
    (hdt : (∃ dt, cd.getByKey g = some (.dataType dt)) ∨
           (∃ dt c, cd.getByKey g = some (.constructor dt c)))
    (heval : Concrete.Eval.interp cd fuel bindings (.ref typ e g) st = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.interp at heval
  -- Discriminate by `cd.getByKey g` via `TermRefsDt` (rules out `.function`).
  split at heval
  · -- `.function` branch — ruled out by TermRefsDt
    rename_i heq
    rcases hdt with ⟨_, hdt⟩ | ⟨_, _, hctor⟩
    · rw [hdt] at heq; cases heq
    · rw [hctor] at heq; cases heq
  · -- `.constructor` branch → splits on `c.argTypes.isEmpty`
    rename_i ctor heq
    split at heval
    · -- empty-arg constructor — yields `.ctor g #[]`
      injection heval with hpair
      injection hpair with hv
      subst hv
      refine .ctor g ?_
      intro x hx
      simp at hx
    · cases heval
  · cases heval  -- `.dataType` branch → error
  · cases heval  -- `none` branch → error

/-! #### Auxiliary: `unflattenValue` produces FnFree (modulo function types).

`unflattenValueBound` is called with `(default : Source.Decls)` (size 0, so
bound = 1) at every `.letLoad`/`.load` site. Under empty decls:

* `.unit`/`.field`/`.pointer`/`.ref`/`.app`: terminal (don't recurse), produce
  `.unit`/`.field`/`.pointer`/`.field`/`.field` — all FnFree.
* `.tuple`/`.array`: recurse with `bound = 0` (so each inner call returns
  `(.unit, 0)`) — everything FnFree.
* `.function`: returns `(.fn ⟨.anonymous⟩, 1)` — NOT FnFree.
* `.mvar _`: returns `(.unit, 0)` — FnFree.

So we need `t ≠ .function _ _` at the OUTER call. The `letLoad`/`load` arms'
`dstTyp` / `t.typ` are `Concrete.Typ`, which `concreteTypToSource` converts
spine-by-spine. The non-`.function` shape is preserved.

For the leaf-arm closure of S1 the strict result we need is: `unflattenValue
(default : Source.Decls) gs offset (concreteTypToSource τ) |>.1 |> Value.FnFree`
under the precondition `τ ≠ .function _ _`. -/

/-- Local alias for the public `Concrete.Typ.NotFunction` predicate from
`ConcreteInvariants.lean`. The `unflattenValue` aux produces FnFree only when
this holds (any function leaf would unflatten to `.fn _`). -/
abbrev NotFunctionTyp : Concrete.Typ → Prop := Concrete.Typ.NotFunction

/-- `Aiur.Typ` analogue, recursive form. -/
inductive NotFunctionATyp : Aiur.Typ → Prop
  | unit : NotFunctionATyp .unit
  | field : NotFunctionATyp .field
  | ref (g) : NotFunctionATyp (.ref g)
  | app (g a) : NotFunctionATyp (.app g a)
  | mvar (n) : NotFunctionATyp (.mvar n)
  | tuple {ts} (h : ∀ t ∈ ts, NotFunctionATyp t) : NotFunctionATyp (.tuple ts)
  | array {t n} (h : NotFunctionATyp t) : NotFunctionATyp (.array t n)
  | pointer {t} (h : NotFunctionATyp t) : NotFunctionATyp (.pointer t)

theorem NotFunctionATyp_concreteTypToSource :
    ∀ {τ : Concrete.Typ},
    NotFunctionTyp τ →
    NotFunctionATyp (concreteTypToSource τ)
  | .unit, _ => by rw [concreteTypToSource]; exact .unit
  | .field, _ => by rw [concreteTypToSource]; exact .field
  | .ref g, _ => by rw [concreteTypToSource]; exact .ref g
  | .tuple ts, h => by
    cases h with
    | tuple hts =>
      rw [concreteTypToSource]
      refine .tuple ?_
      intro t' ht'
      rw [Array.mem_iff_getElem] at ht'
      obtain ⟨i, hi, heq⟩ := ht'
      rw [Array.size_map, Array.size_attach] at hi
      have hmem : ts[i]'hi ∈ ts := Array.getElem_mem hi
      rw [Array.getElem_map, Array.getElem_attach] at heq
      rw [← heq]
      exact NotFunctionATyp_concreteTypToSource (hts _ hmem)
  | .array t _, h => by
    cases h with
    | array h =>
      rw [concreteTypToSource]
      exact .array (NotFunctionATyp_concreteTypToSource h)
  | .pointer t, h => by
    cases h with
    | pointer h =>
      rw [concreteTypToSource]
      exact .pointer (NotFunctionATyp_concreteTypToSource h)
  | .function _ _, h => by cases h
termination_by τ _ => sizeOf τ
decreasing_by
  all_goals first
    | (have hsm := Array.sizeOf_lt_of_mem hmem; grind)
    | decreasing_tactic

/-- `(default : Source.Decls).getByKey g = none` for any `g`. The default
IndexMap has no entries. -/
theorem default_Source_Decls_getByKey (g : Global) :
    (default : Source.Decls).getByKey g = none := by
  unfold IndexMap.getByKey
  simp only [default]
  show (do let x ← (∅ : Std.HashMap Global Nat)[g]?
           Option.map Prod.snd (#[] : Array (Global × Source.Declaration))[x]?) = none
  rw [Std.HashMap.getElem?_empty]
  rfl

/-- `unflattenValueBound (default : Source.Decls) gs bound offset t |>.1 |>
Value.FnFree` whenever the Typ tree contains no `.function _ _` anywhere.

Structural induction on `bound` (0 → `.unit`; succ → per-Typ dispatch). The
`.ref` / `.app` arms collapse to `.field` because `default.getByKey g = none`.
`.tuple` and `.array` arms recurse with the IH at smaller `bound`, using the
recursive `NotFunctionATyp`. -/
theorem unflattenValueBound_FnFree
    (gs : Array G) (bound : Nat) :
    ∀ (offset : Nat) (t : Aiur.Typ),
    NotFunctionATyp t →
    Value.FnFree (unflattenValueBound (default : Source.Decls) gs bound offset t).1 := by
  induction bound with
  | zero =>
    intro offset t _hNF
    unfold unflattenValueBound
    exact .unit
  | succ b ih =>
    intro offset t hNF
    cases t with
    | unit =>
      unfold unflattenValueBound
      exact .unit
    | field =>
      unfold unflattenValueBound
      exact .field _
    | pointer t' =>
      unfold unflattenValueBound
      exact .pointer _ _
    | function _ _ => cases hNF
    | mvar _ =>
      unfold unflattenValueBound
      exact .unit
    | tuple ts =>
      unfold unflattenValueBound
      simp only
      refine .tuple ?_
      cases hNF with
      | tuple htsNF =>
        apply Array.foldl_induction
          (motive := fun (_i : Nat) (acc : Array Value × Nat) =>
            ∀ p ∈ acc.1, Value.FnFree p)
        · intro p hp; simp at hp
        · intro i acc hacc p hp
          -- ts.attach[i] : { x // x ∈ ts }; its .val is some ts elt.
          have hatt_mem : (ts.attach[i.val]).val ∈ ts := (ts.attach[i.val]).property
          rw [Array.mem_push] at hp
          cases hp with
          | inl hin => exact hacc _ hin
          | inr heq =>
            subst heq
            exact ih _ _ (htsNF _ hatt_mem)
    | array t' n =>
      unfold unflattenValueBound
      simp only
      refine .array ?_
      intro v hv
      rw [Array.mem_iff_getElem] at hv
      obtain ⟨i, hi, heq⟩ := hv
      rw [Array.size_ofFn] at hi
      rw [Array.getElem_ofFn] at heq
      cases hNF with
      | array hNFt' =>
        rw [← heq]
        exact ih _ t' hNFt'
    | ref g =>
      unfold unflattenValueBound
      simp only [default_Source_Decls_getByKey]
      exact .field _
    | app g args =>
      unfold unflattenValueBound
      simp only [default_Source_Decls_getByKey]
      exact .field _

/-- Outer interface: `unflattenValue` is `unflattenValueBound` at
`decls.size + 1`, here `(default : Source.Decls).size + 1 = 1`. -/
theorem unflattenValue_FnFree
    (gs : Array G) (offset : Nat) (t : Aiur.Typ)
    (hNF : NotFunctionATyp t) :
    Value.FnFree (unflattenValue (default : Source.Decls) gs offset t).1 := by
  unfold unflattenValue
  exact unflattenValueBound_FnFree gs _ offset t hNF

/-! #### Mutual-induction: per-fuel preservation of `FnFree`.

Six theorems, one per interp-family function. Termination uses the same
`(fuel, role, sizeOf t, ...)` lex measure as the eval functions, so the
mutual recursion type-checks identically.

For per-arm closure status see the `interp_FnFree` body: 30+ arms F=0
(unit/var/field/ref/letVar/letWild/ret/tuple/array/match/proj/get/slice/set/
add/sub/mul/eqZero/store/ptrVal/assertEq/u8*/u32LessThan/debug/ioGetInfo/
ioSetInfo/ioRead/ioWrite/app); 2 arms F=1 with sub-sorry citing
`unflattenValue_FnFree` (`letLoad`, `load`). -/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2000 in
mutual

/-- Preservation through `applyGlobal`. -/
theorem applyGlobal_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (g : Global) (args : List Value) (st : EvalState)
    (hargs : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (st' : EvalState)
    (hcall : Concrete.Eval.applyGlobal cd fuel g args st = .ok (v, st')) :
    Value.FnFree v := by
  cases fuel with
  | zero =>
    unfold Concrete.Eval.applyGlobal at hcall
    cases hcall
  | succ n =>
    unfold Concrete.Eval.applyGlobal at hcall
    split at hcall
    · -- `.function f` branch
      rename_i f hfg
      split at hcall
      · cases hcall  -- arity mismatch error
      · -- recurse into `interp` on `f.body` with bindings from `args`
        rename_i _hsize
        have hbindings_FnFree :
            BindingsFnFree (f.inputs.map (·.1) |>.zip args) := by
          -- p ∈ zip xs ys ⇒ p.2 ∈ ys (zip preserves elements pointwise).
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
          exact hargs _ (hzip_snd_mem _ _ p hp)
        have htermRefsDt : Concrete.Term.RefsDt cd f.body := _hTermRefsDt _ _ hfg
        have htypesNF : Concrete.Term.TypesNotFunction cd f.body := _hTypesNF _ _ hfg
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF n
          (f.inputs.map (·.1) |>.zip args) f.body st hbindings_FnFree htermRefsDt htypesNF
          v st' hcall
    · -- `.constructor` branch — yields `.ctor g args.toArray`
      rename_i _ _ _hfg
      injection hcall with hpair
      injection hpair with hv _
      subst hv
      refine .ctor g ?_
      intro x hx
      rw [Array.mem_toArray] at hx
      exact hargs _ hx
    · cases hcall  -- `none` → error
    · cases hcall  -- `.dataType` → error
termination_by (fuel, 0, 0, 0)

/-- Preservation through `applyLocal`. -/
theorem applyLocal_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (vCallee : Value) (args : List Value) (st : EvalState)
    (hCallee : Value.FnFree vCallee)
    (_hargs : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (st' : EvalState)
    (hcall : Concrete.Eval.applyLocal cd fuel vCallee args st = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.applyLocal at hcall
  cases vCallee with
  | unit => cases hcall
  | field _ => cases hcall
  | tuple _ => cases hcall
  | array _ => cases hcall
  | ctor _ _ => cases hcall
  | fn g =>
    -- vCallee = .fn g, but hCallee : Value.FnFree (.fn g) is False.
    exact (FnFree_not_fn g hCallee).elim
  | pointer _ _ => cases hcall
termination_by (fuel, 1, 0, 0)

/-- Preservation through `interp`. ~37-arm dispatch. Most arms close F=0 via
inversion lemmas + the per-function IH on the corresponding sub-pieces. -/
theorem interp_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (bindings : Bindings) (t : Concrete.Term) (st : EvalState)
    (hb : BindingsFnFree bindings)
    (htRefsDt : Concrete.Term.RefsDt cd t)
    (htTypesNF : Concrete.Term.TypesNotFunction cd t)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.interp cd fuel bindings t st = .ok (v, st')) :
    Value.FnFree v := by
  -- 37-arm dispatch via `cases t`, with inversion-lemma rewrites + IH calls.
  -- Most arms close F=0; recursive ones use the corresponding sibling theorem
  -- in this mutual block (decreasing on `sizeOf t`).
  cases t with
  | unit τ e =>
    -- LEAF: produces .unit
    rw [Concrete.Eval.interp_unit] at heval
    injection heval with hpair
    injection hpair with hv
    subst hv
    exact .unit
  | var τ e l =>
    -- LEAF: bindings lookup
    rw [Concrete.Eval.interp_var] at heval
    cases hfind : bindings.find? (·.1 == l) with
    | none => rw [hfind] at heval; cases heval
    | some lv =>
      rw [hfind] at heval
      obtain ⟨l', vBound⟩ := lv
      injection heval with hpair
      injection hpair with hv
      subst hv
      -- Need l' = l: from `find?_eq_some` predicate. Mem in bindings.
      have hmem : (l', vBound) ∈ bindings := List.mem_of_find?_eq_some hfind
      exact hb _ hmem
  | field τ e g =>
    -- LEAF
    rw [Concrete.Eval.interp_field] at heval
    injection heval with hpair
    injection hpair with hv
    subst hv
    exact .field g
  | ref τ e g =>
    -- LEAF: closed via ref_arm_FnFree using _hTermRefsDt.
    cases htRefsDt with
    | ref hdt => exact ref_arm_FnFree cd fuel bindings τ e g st v st' hdt heval
  | ret τ e r =>
    -- IH(r)
    rw [Concrete.Eval.interp_ret] at heval
    cases htRefsDt with
    | ret hr =>
      cases htTypesNF with
      | ret hrTNF =>
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings r st
          hb hr hrTNF v st' heval
  | tuple τ e ts =>
    -- IH via evalList_FnFree
    rw [Concrete.Eval.interp_tuple] at heval
    cases hres : Concrete.Eval.evalList cd fuel bindings ts.toList st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vs, st''⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      cases htRefsDt with
      | tuple h =>
        cases htTypesNF with
        | tuple hTNF =>
          have hts_refs : ∀ t' ∈ ts.toList, Concrete.Term.RefsDt cd t' := by
            intro t' ht'
            exact h t' (Array.mem_toList_iff.mp ht')
          have hts_typesNF : ∀ t' ∈ ts.toList, Concrete.Term.TypesNotFunction cd t' := by
            intro t' ht'
            exact hTNF t' (Array.mem_toList_iff.mp ht')
          refine .tuple ?_
          intro w hw
          exact evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings
            ts.toList st hb hts_refs hts_typesNF vs st'' hres w hw
  | array τ e ts =>
    -- IH via evalList_FnFree
    rw [Concrete.Eval.interp_array] at heval
    cases hres : Concrete.Eval.evalList cd fuel bindings ts.toList st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vs, st''⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      cases htRefsDt with
      | array h =>
        cases htTypesNF with
        | array hTNF =>
          have hts_refs : ∀ t' ∈ ts.toList, Concrete.Term.RefsDt cd t' := by
            intro t' ht'
            exact h t' (Array.mem_toList_iff.mp ht')
          have hts_typesNF : ∀ t' ∈ ts.toList, Concrete.Term.TypesNotFunction cd t' := by
            intro t' ht'
            exact hTNF t' (Array.mem_toList_iff.mp ht')
          refine .array ?_
          intro w hw
          exact evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings
            ts.toList st hb hts_refs hts_typesNF vs st'' hres w hw
  | letVar τ e l vT b =>
    -- IH(vT) → val-FnFree → BindingsFnFree.cons → IH(b)
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i val sval hres
      cases htRefsDt with
      | letVar hv hb' =>
        cases htTypesNF with
        | letVar hvTNF hbTNF =>
          have hval : Value.FnFree val :=
            interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings vT st
              hb hv hvTNF val sval hres
          have hb_ext : BindingsFnFree ((l, val) :: bindings) :=
            BindingsFnFree.cons hval hb
          exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel ((l, val) :: bindings)
            b sval hb_ext hb' hbTNF v st' heval
  | letWild τ e vT b =>
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i val sval _hres
      cases htRefsDt with
      | letWild _hv hb' =>
        cases htTypesNF with
        | letWild _hvTNF hbTNF =>
          exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings b sval
            hb hb' hbTNF v st' heval
  | letLoad τ e dst dstTyp src b =>
    -- Closes via SD-LoadType: `_hTypesNF` provides the `NotFunction dstTyp`
    -- witness, which lifts to `NotFunctionATyp (concreteTypToSource dstTyp)`
    -- and feeds `unflattenValue_FnFree`. Threaded into BindingsFnFree.cons →
    -- IH(b).
    rw [Concrete.Eval.interp_letLoad] at heval
    cases htRefsDt with
    | letLoad hb' =>
      cases htTypesNF with
      | letLoad hDstNF hbTNF =>
        -- `bindings.find? (·.1 == src)` must produce `.pointer w i`.
        cases hfind : bindings.find? (·.1 == src) with
        | none => rw [hfind] at heval; cases heval
        | some lv =>
          obtain ⟨l', vBound⟩ := lv
          rw [hfind] at heval
          cases vBound with
          | unit | field _ | tuple _ | array _ | ctor _ _ | fn _ =>
            simp at heval
          | pointer w i =>
            simp at heval
            cases hlookup : storeLookup st w i with
            | none => rw [hlookup] at heval; cases heval
            | some gs =>
              rw [hlookup] at heval
              -- `stored = (unflattenValue (default : Source.Decls) gs 0 (concreteTypToSource dstTyp)).1`
              have hStoredFF : Value.FnFree
                  (unflattenValue (default : Source.Decls) gs 0
                    (concreteTypToSource dstTyp)).1 :=
                unflattenValue_FnFree gs 0
                  (concreteTypToSource dstTyp)
                  (NotFunctionATyp_concreteTypToSource hDstNF)
              have hb_ext : BindingsFnFree
                  ((dst, (unflattenValue (default : Source.Decls) gs 0
                      (concreteTypToSource dstTyp)).1) :: bindings) :=
                BindingsFnFree.cons hStoredFF hb
              exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel
                ((dst, (unflattenValue (default : Source.Decls) gs 0
                    (concreteTypToSource dstTyp)).1) :: bindings) b st
                hb_ext hb' hbTNF v st' heval
  | «match» τ e scrutIdx cases defaultOpt =>
    -- Bindings lookup → evalMatchCases_FnFree.
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i lvar scrut hfind
      have hscrut : Value.FnFree scrut := by
        have hmem := List.mem_of_find?_eq_some hfind
        exact hb _ hmem
      cases htRefsDt with
      | «match» hcases hdef =>
        cases htTypesNF with
        | «match» hcasesTNF hdefTNF =>
          exact evalMatchCases_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings st
            scrut cases defaultOpt 0 hb hscrut hcases hdef hcasesTNF hdefTNF v st' heval
  | app τ e g argTms u =>
    -- evalList_FnFree on argTms → applyLocal_FnFree / applyGlobal_FnFree
    rw [Concrete.Eval.interp_app] at heval
    cases hresArgs : Concrete.Eval.evalList cd fuel bindings argTms st with
    | error err => rw [hresArgs] at heval; cases heval
    | ok pair =>
      obtain ⟨argVs, sArgs⟩ := pair
      rw [hresArgs] at heval
      cases htRefsDt with
      | app hargs =>
        cases htTypesNF with
        | app hargsTNF =>
          have hargVs_FnFree : ∀ w ∈ argVs, Value.FnFree w :=
            evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings argTms st
              hb hargs hargsTNF argVs sArgs hresArgs
          cases hLocal : Concrete.Eval.tryLocalLookup g bindings with
          | none =>
            rw [hLocal] at heval
            exact applyGlobal_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel g argVs.toList
              sArgs (fun w hw => hargVs_FnFree w (Array.mem_toList_iff.mp hw)) v st' heval
          | some vCallee =>
            rw [hLocal] at heval
            -- vCallee is from bindings via `tryLocalLookup` (which uses bindings.find?).
            have hCallee : Value.FnFree vCallee := by
              unfold Concrete.Eval.tryLocalLookup at hLocal
              split at hLocal
              · -- .str .anonymous name branch
                rename_i nameStr _heq
                cases hfind : bindings.find? (·.1 == Local.str nameStr) with
                | none =>
                  rw [hfind] at hLocal
                  cases hLocal
                | some lv =>
                  rw [hfind] at hLocal
                  obtain ⟨l', vB⟩ := lv
                  simp [Option.map] at hLocal
                  subst hLocal
                  have hmem := List.mem_of_find?_eq_some hfind
                  exact hb _ hmem
              · cases hLocal
            exact applyLocal_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel vCallee
              argVs.toList sArgs hCallee
              (fun w hw => hargVs_FnFree w (Array.mem_toList_iff.mp hw)) v st' heval
  | add τ e a b =>
    rw [Concrete.Eval.interp_add] at heval
    cases htRefsDt with
    | add ha hb' =>
      cases htTypesNF with
      | add haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | sub τ e a b =>
    rw [Concrete.Eval.interp_sub] at heval
    cases htRefsDt with
    | sub ha hb' =>
      cases htTypesNF with
      | sub haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | mul τ e a b =>
    rw [Concrete.Eval.interp_mul] at heval
    cases htRefsDt with
    | mul ha hb' =>
      cases htTypesNF with
      | mul haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | eqZero τ e a =>
    rw [Concrete.Eval.interp_eqZero] at heval
    cases htRefsDt with
    | eqZero ha =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        cases va with
        | field g =>
          injection heval with hpair
          injection hpair with hv
          subst hv
          exact .field _
        | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | proj τ e a n =>
    rw [Concrete.Eval.interp_proj] at heval
    cases htRefsDt with
    | proj ha =>
      cases htTypesNF with
      | proj haTNF =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a st
            hb ha haTNF va sa hres
        cases va with
        | tuple vs =>
          -- heval : (if h : n < vs.size then .ok (vs[n], sa) else .error _) = .ok (v, st')
          by_cases hidx : n < vs.size
          · simp [hidx] at heval
            have hv : vs[n]'hidx = v := heval.1
            subst hv
            cases hva_ff with
            | tuple h => exact h _ (Array.getElem_mem _)
          · simp [hidx] at heval
        | unit | field _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | get τ e a n =>
    rw [Concrete.Eval.interp_get] at heval
    cases htRefsDt with
    | get ha =>
      cases htTypesNF with
      | get haTNF =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a st
            hb ha haTNF va sa hres
        cases va with
        | array vs =>
          by_cases hidx : n < vs.size
          · simp [hidx] at heval
            have hv : vs[n]'hidx = v := heval.1
            subst hv
            cases hva_ff with
            | array h => exact h _ (Array.getElem_mem _)
          · simp [hidx] at heval
        | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | slice τ e a i j =>
    rw [Concrete.Eval.interp_slice] at heval
    cases htRefsDt with
    | slice ha =>
      cases htTypesNF with
      | slice haTNF =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a st
            hb ha haTNF va sa hres
        cases va with
        | array vs =>
          injection heval with hpair
          injection hpair with hv _
          subst hv
          cases hva_ff with
          | array h =>
            refine .array ?_
            intro w hw
            -- w ∈ (vs.extract i j) → ∃ k, w = vs[i+k] (within bounds).
            have hwmem : w ∈ vs := by
              rw [Array.mem_iff_getElem] at hw
              obtain ⟨k, hk, heqk⟩ := hw
              rw [Array.size_extract] at hk
              rw [Array.getElem_extract] at heqk
              rw [← heqk]
              exact Array.getElem_mem _
            exact h w hwmem
        | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | set τ e a n vT =>
    -- IH on vT, then on a; .array (vs.set! n val) — set! preserves elementwise FnFree.
    rw [Concrete.Eval.interp_set] at heval
    cases htRefsDt with
    | set ha hv =>
      cases htTypesNF with
      | set haTNF hvTNF =>
      cases hresVT : Concrete.Eval.interp cd fuel bindings vT st with
      | error err => rw [hresVT] at heval; cases heval
      | ok pairVT =>
        obtain ⟨val, st1⟩ := pairVT
        rw [hresVT] at heval
        simp only at heval
        have hval_ff : Value.FnFree val :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings vT st
            hb hv hvTNF val st1 hresVT
        cases hresA : Concrete.Eval.interp cd fuel bindings a st1 with
        | error err => rw [hresA] at heval; cases heval
        | ok pairA =>
          obtain ⟨va, st2⟩ := pairA
          rw [hresA] at heval
          have hva_ff : Value.FnFree va :=
            interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a st1
              hb ha haTNF va st2 hresA
          cases va with
          | array vs =>
            by_cases hidx : n < vs.size
            · simp [hidx] at heval
              obtain ⟨hv', _⟩ := heval
              subst hv'
              cases hva_ff with
              | array hvs =>
                refine .array ?_
                intro w hw
                -- `set!` reduces to `setIfInBounds`. Membership is val (at n) or vs elt.
                simp only [Array.set!] at hw
                rw [Array.mem_iff_getElem] at hw
                obtain ⟨k, hk, heqk⟩ := hw
                have hsz : (vs.setIfInBounds n val).size = vs.size := by simp
                have hk' : k < vs.size := hsz ▸ hk
                by_cases hkn : k = n
                · -- At index n the element is val.
                  subst hkn
                  have hget : (vs.setIfInBounds k val)[k]'hk = val := by
                    simp [Array.getElem_setIfInBounds, hk']
                  rw [hget] at heqk
                  subst heqk; exact hval_ff
                · -- At index k ≠ n the element is vs[k].
                  have hkn' : ¬ n = k := fun h => hkn h.symm
                  have hget : (vs.setIfInBounds n val)[k]'hk = vs[k]'hk' := by
                    rw [Array.getElem_setIfInBounds]
                    rw [if_neg hkn']
                  rw [hget] at heqk
                  subst heqk
                  exact hvs _ (Array.getElem_mem _)
            · simp [hidx] at heval
          | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | store τ e a =>
    -- LEAF (output): always .pointer w idx — FnFree.
    rw [Concrete.Eval.interp_store] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      exact .pointer _ _
  | load τ e a =>
    -- Closes via SD-LoadType: `_hTypesNF` provides `NotFunction a.typ`, which
    -- lifts through `concreteTypToSource` into `NotFunctionATyp`. The .pointer
    -- branch's `eltTyp = inner` extraction preserves the predicate; non-pointer
    -- (impossible here, but covered) trivially preserves it.
    rw [Concrete.Eval.interp_load] at heval
    cases htRefsDt with
    | load ha =>
      cases htTypesNF with
      | load hAtyNF haTNF =>
        cases hres : Concrete.Eval.interp cd fuel bindings a st with
        | error err => rw [hres] at heval; cases heval
        | ok pair =>
          obtain ⟨va, sa⟩ := pair
          rw [hres] at heval
          have _hva_ff : Value.FnFree va :=
            interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a st
              hb ha haTNF va sa hres
          cases va with
          | pointer w idx =>
            simp only at heval
            cases hlookup : storeLookup sa w idx with
            | none => rw [hlookup] at heval; cases heval
            | some gs =>
              rw [hlookup] at heval
              simp only at heval
              -- `srcTyp = concreteTypToSource a.typ`; `srcTypNF : NotFunctionATyp srcTyp`.
              have hsrcTypNF : NotFunctionATyp (concreteTypToSource a.typ) :=
                NotFunctionATyp_concreteTypToSource hAtyNF
              -- Get eltTyp = if srcTyp = .pointer inner then inner else srcTyp.
              -- In either case, NotFunctionATyp eltTyp follows.
              cases hsrcCase : concreteTypToSource a.typ with
              | pointer inner =>
                rw [hsrcCase] at heval
                simp at heval
                have hinnerNF : NotFunctionATyp inner := by
                  rw [hsrcCase] at hsrcTypNF
                  cases hsrcTypNF with
                  | pointer h => exact h
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 inner hinnerNF
              | unit =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | field =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | ref g =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | tuple ts =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | array t n =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | function _ _ =>
                rw [hsrcCase] at hsrcTypNF
                cases hsrcTypNF
              | app g a =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
              | mvar n =>
                rw [hsrcCase] at heval
                simp at heval
                obtain ⟨hv', _⟩ := heval
                rw [← hv']
                exact unflattenValue_FnFree gs 0 _
                  (by rw [hsrcCase] at hsrcTypNF; exact hsrcTypNF)
          | unit | field _ | tuple _ | array _ | ctor _ _ | fn _ => cases heval
  | ptrVal τ e a =>
    -- IH(a) gives .pointer; output .field (.ofNat i) — FnFree.
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err =>
      -- heval reduces via interp ptrVal; replace inner via hres.
      unfold Concrete.Eval.interp at heval
      rw [hres] at heval
      cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      unfold Concrete.Eval.interp at heval
      rw [hres] at heval
      cases va with
      | pointer w idx =>
        injection heval with hpair
        injection hpair with hv _
        subst hv
        exact .field _
      | unit | field _ | tuple _ | array _ | ctor _ _ | fn _ => cases heval
  | assertEq τ e a b r =>
    -- IH(a), IH(b), then IH(r)
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i v1 st1 _hres1
      split at heval
      · cases heval
      · rename_i v2 st2 _hres2
        split at heval
        · cases heval
        · cases htRefsDt with
          | assertEq ha hb' hr =>
            cases htTypesNF with
            | assertEq _ _ hrTNF =>
              exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings r
                st2 hb hr hrTNF v st' heval
  | u8BitDecomposition τ e a =>
    rw [Concrete.Eval.interp_u8BitDecomposition] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact FnFree_ofFn_field _ _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8ShiftLeft τ e a =>
    rw [Concrete.Eval.interp_u8ShiftLeft] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8ShiftRight τ e a =>
    rw [Concrete.Eval.interp_u8ShiftRight] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8Xor τ e a b =>
    rw [Concrete.Eval.interp_u8Xor] at heval
    cases htRefsDt with
    | u8Xor ha hb' =>
      cases htTypesNF with
      | u8Xor haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | u8Add τ e a b =>
    rw [Concrete.Eval.interp_u8Add] at heval
    cases htRefsDt with
    | u8Add ha hb' =>
      cases htTypesNF with
      | u8Add haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact FnFree_two_field_tuple _ _
  | u8Sub τ e a b =>
    rw [Concrete.Eval.interp_u8Sub] at heval
    cases htRefsDt with
    | u8Sub ha hb' =>
      cases htTypesNF with
      | u8Sub haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact FnFree_two_field_tuple _ _
  | u8And τ e a b =>
    rw [Concrete.Eval.interp_u8And] at heval
    cases htRefsDt with
    | u8And ha hb' =>
      cases htTypesNF with
      | u8And haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | u8Or τ e a b =>
    rw [Concrete.Eval.interp_u8Or] at heval
    cases htRefsDt with
    | u8Or ha hb' =>
      cases htTypesNF with
      | u8Or haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | u8LessThan τ e a b =>
    rw [Concrete.Eval.interp_u8LessThan] at heval
    cases htRefsDt with
    | u8LessThan ha hb' =>
      cases htTypesNF with
      | u8LessThan haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | u32LessThan τ e a b =>
    rw [Concrete.Eval.interp_u32LessThan] at heval
    cases htRefsDt with
    | u32LessThan ha hb' =>
      cases htTypesNF with
      | u32LessThan haTNF hbTNF =>
        apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings a b st _
          ?_ hb ha hb' haTNF hbTNF v st' heval
        intro x y; exact .field _
  | debug τ e label tOpt r =>
    -- IH(r) — interp_debug is not in the inversion list; use raw unfold.
    unfold Concrete.Eval.interp at heval
    cases htRefsDt with
    | debug _hT hr =>
      cases htTypesNF with
      | debug _hTTNF hrTNF =>
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings r st
          hb hr hrTNF v st' heval
  | ioGetInfo τ e k =>
    -- IH(k); output .tuple #[.field, .field] — FnFree_two_field_tuple.
    rw [Concrete.Eval.interp_ioGetInfo] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings k st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vk, sk⟩ := pair
      rw [hres] at heval
      cases vk with
      | array vs =>
        cases hres' : Concrete.Eval.expectFieldArray vs with
        | none => simp [hres'] at heval
        | some keyGs =>
          simp [hres'] at heval
          cases hres'' : sk.ioBuffer.map[keyGs]? with
          | none => simp [hres''] at heval
          | some info =>
            simp [hres''] at heval
            obtain ⟨hv, _⟩ := heval
            subst hv
            exact FnFree_two_field_tuple _ _
      | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | ioSetInfo τ e k iT lT r =>
    -- IH(k), IH(iT), IH(lT), IH(r). Eventually reaches IH(r).
    unfold Concrete.Eval.interp at heval
    -- Eval order is k -> iT -> lT, then match on result shapes, then IH(r).
    split at heval
    · cases heval
    · rename_i vk stk _hresk
      split at heval
      · cases heval
      · rename_i vi sti _hresi
        split at heval
        · cases heval
        · rename_i vl stl _hresl
          split at heval
          · -- happy path matching .array vs, .field iG, .field lG
            split at heval
            · cases heval  -- expectFieldArray = none
            · split at heval
              · cases heval  -- key already set
              · cases htRefsDt with
                | ioSetInfo _hk _hi _hl hr =>
                  cases htTypesNF with
                  | ioSetInfo _ _ _ hrTNF =>
                    exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings r _
                      hb hr hrTNF v st' heval
          all_goals cases heval
  | ioRead τ e idx n =>
    -- IH(idx); output .array (..|>.map .field).
    rw [Concrete.Eval.interp_ioRead] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings idx st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vIdx, sidx⟩ := pair
      rw [hres] at heval
      cases vIdx with
      | field g =>
        by_cases hbnd : g.val.toNat + n > sidx.ioBuffer.data.size
        · simp [hbnd] at heval
        · simp [hbnd] at heval
          obtain ⟨hv, _⟩ := heval
          subst hv
          refine .array ?_
          intro w hw
          -- w ∈ (data.map .field).extract _ _ →
          -- ∃ k, w = (data.map .field)[i] = .field _.
          rw [Array.mem_iff_getElem] at hw
          obtain ⟨k, hk, heqk⟩ := hw
          have : w ∈ Array.map Value.field sidx.ioBuffer.data := by
            rw [Array.mem_iff_getElem]
            -- (extract data i j)[k] = data[i+k] (when in bounds).
            rw [Array.getElem_extract] at heqk
            refine ⟨g.val.toNat + k, ?_, heqk⟩
            rw [Array.size_extract] at hk
            rw [Array.size_map]
            omega
          rw [Array.mem_map] at this
          obtain ⟨g', _, heq⟩ := this
          subst heq
          exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | ioWrite τ e d r =>
    -- IH(d), IH(r).
    rw [Concrete.Eval.interp_ioWrite] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings d st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vd, sd⟩ := pair
      rw [hres] at heval
      cases vd with
      | array vs =>
        cases hres' : Concrete.Eval.expectFieldArray vs with
        | none => simp [hres'] at heval
        | some dataGs =>
          simp [hres'] at heval
          cases htRefsDt with
          | ioWrite _hd hr =>
            cases htTypesNF with
            | ioWrite _ hrTNF =>
              exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings r _
                hb hr hrTNF v st' heval
      | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
termination_by (fuel, 2, sizeOf t, 0)
decreasing_by all_goals first | decreasing_tactic | grind [sizeOf_toList_lt]

/-- Helper: bindings produced by `matchPattern` are FnFree whenever `scrut` is.
The bindings come from `(vars.zip vs).toList` (ref/tuple/array) or `[]`
(wildcard/field). The `.snd` projection of each pair is in `vs`, which is
FnFree-elementwise from `hscrut`. -/
theorem matchPattern_bindingsFnFree {p : Concrete.Pattern} {scrut : Value}
    {bs : Bindings} (hscrut : Value.FnFree scrut)
    (h : Concrete.Eval.matchPattern p scrut = some bs) :
    BindingsFnFree bs := by
  -- Inline pointwise zip.snd-membership helper.
  have hzip_snd_mem :
      ∀ {α β} (xs : Array α) (ys : Array β) (p : α × β),
        p ∈ (xs.zip ys).toList → p.2 ∈ ys := by
    intro α β xs ys p hp
    rw [Array.toList_zip] at hp
    -- hp : p ∈ List.zip xs.toList ys.toList
    have : ∀ {α β} (xs : List α) (ys : List β) (p : α × β),
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
    have hL := this _ _ _ hp
    exact Array.mem_toList_iff.mp hL
  cases p with
  | wildcard =>
    simp [Concrete.Eval.matchPattern] at h
    subst h
    intro x hx; cases hx
  | field g =>
    cases scrut with
    | field g' =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · injection h with h
        subst h
        intro x hx; cases hx
      · cases h
    | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | ref g vars =>
    cases scrut with
    | ctor g' vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · split at h
        · cases h
        · injection h with h
          subst h
          intro p hp
          have hr := hzip_snd_mem vars vs p hp
          cases hscrut with
          | ctor _ hvs => exact hvs _ hr
    | unit | field _ | tuple _ | array _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | tuple vars =>
    cases scrut with
    | tuple vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · injection h with h
        subst h
        intro p hp
        have hr := hzip_snd_mem vars vs p hp
        cases hscrut with
        | tuple hvs => exact hvs _ hr
    | unit | field _ | ctor _ _ | array _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | array vars =>
    cases scrut with
    | array vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · injection h with h
        subst h
        intro p hp
        have hr := hzip_snd_mem vars vs p hp
        cases hscrut with
        | array hvs => exact hvs _ hr
    | unit | field _ | ctor _ _ | tuple _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h

/-- Preservation through `evalMatchCases`. -/
theorem evalMatchCases_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (bindings : Bindings) (st : EvalState) (scrut : Value)
    (cases : Array (Concrete.Pattern × Concrete.Term)) (defaultOpt : Option Concrete.Term)
    (i : Nat)
    (hb : BindingsFnFree bindings)
    (hscrut : Value.FnFree scrut)
    (hcasesRefs : ∀ pc ∈ cases, Concrete.Term.RefsDt cd pc.2)
    (hdefRefs : ∀ d, defaultOpt = some d → Concrete.Term.RefsDt cd d)
    (hcasesTypesNF : ∀ pc ∈ cases, Concrete.Term.TypesNotFunction cd pc.2)
    (hdefTypesNF : ∀ d, defaultOpt = some d → Concrete.Term.TypesNotFunction cd d)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.evalMatchCases cd fuel bindings st scrut cases defaultOpt i
        = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.evalMatchCases at heval
  by_cases hi : i < cases.size
  · rw [dif_pos hi] at heval
    cases hmp : Concrete.Eval.matchPattern cases[i].fst scrut with
    | none =>
      rw [hmp] at heval
      simp at heval
      -- recursive call on i+1
      exact evalMatchCases_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings st
        scrut cases defaultOpt (i + 1) hb hscrut hcasesRefs hdefRefs
        hcasesTypesNF hdefTypesNF v st' heval
    | some bs =>
      rw [hmp] at heval
      simp at heval
      -- happy path: interp on cases[i].snd with bs ++ bindings
      have hbs_FnFree : BindingsFnFree bs := matchPattern_bindingsFnFree hscrut hmp
      have hb_ext : BindingsFnFree (bs ++ bindings) := BindingsFnFree.append hbs_FnFree hb
      have hcase_refs : Concrete.Term.RefsDt cd cases[i].snd :=
        hcasesRefs _ (Array.getElem_mem hi)
      have hcase_typesNF : Concrete.Term.TypesNotFunction cd cases[i].snd :=
        hcasesTypesNF _ (Array.getElem_mem hi)
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel (bs ++ bindings)
        cases[i].snd st hb_ext hcase_refs hcase_typesNF v st' heval
  · rw [dif_neg hi] at heval
    cases hd : defaultOpt with
    | none => rw [hd] at heval; cases heval
    | some body =>
      rw [hd] at heval
      have hbody_refs : Concrete.Term.RefsDt cd body := hdefRefs body hd
      have hbody_typesNF : Concrete.Term.TypesNotFunction cd body := hdefTypesNF body hd
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings body st
        hb hbody_refs hbody_typesNF v st' heval
termination_by (fuel, 2, sizeOf cases + sizeOf defaultOpt, cases.size - i)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
       have h := Array.sizeOf_get cases i ‹_›
       have hpair : sizeOf cases[i].snd ≤ sizeOf cases[i] := by
         rcases hcp : cases[i] with ⟨a, b⟩
         show sizeOf b ≤ sizeOf (a, b)
         simp [Prod.mk.sizeOf_spec]
       omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right
       omega)

/-- Preservation through `evalList`. -/
theorem evalList_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (bindings : Bindings) (ts : List Concrete.Term) (st : EvalState)
    (hb : BindingsFnFree bindings)
    (htsRefs : ∀ t ∈ ts, Concrete.Term.RefsDt cd t)
    (htsTypesNF : ∀ t ∈ ts, Concrete.Term.TypesNotFunction cd t)
    (vs : Array Value) (st' : EvalState)
    (heval : Concrete.Eval.evalList cd fuel bindings ts st = .ok (vs, st')) :
    ∀ v ∈ vs, Value.FnFree v :=
  match ts, heval with
  | [], heval => by
    unfold Concrete.Eval.evalList at heval
    injection heval with hpair
    injection hpair with hvs _hst
    subst hvs
    intro v hv
    simp at hv
  | (t :: tsTail), heval => by
    unfold Concrete.Eval.evalList at heval
    split at heval
    · cases heval  -- error
    · rename_i v0 st0 hres
      split at heval
      · cases heval  -- error in tail
      · rename_i vsTail stTail hresTail
        injection heval with hpair
        injection hpair with hvs hst
        subst hvs hst
        -- v0 is FnFree by interp_FnFree IH on t.
        have ht_refs : Concrete.Term.RefsDt cd t := htsRefs _ (List.mem_cons_self)
        have ht_typesNF : Concrete.Term.TypesNotFunction cd t :=
          htsTypesNF _ (List.mem_cons_self)
        have hv0 : Value.FnFree v0 :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings t st
            hb ht_refs ht_typesNF v0 st0 hres
        have hts_refs : ∀ t' ∈ tsTail, Concrete.Term.RefsDt cd t' := by
          intro t' ht'mem
          exact htsRefs _ (List.mem_cons_of_mem _ ht'mem)
        have hts_typesNF : ∀ t' ∈ tsTail, Concrete.Term.TypesNotFunction cd t' := by
          intro t' ht'mem
          exact htsTypesNF _ (List.mem_cons_of_mem _ ht'mem)
        have hihTail :=
          evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel bindings tsTail st0
            hb hts_refs hts_typesNF vsTail stTail hresTail
        intro v hv
        rw [Array.mem_iff_getElem] at hv
        obtain ⟨i, hi, heq⟩ := hv
        rw [Array.size_append] at hi
        have hsize_one : (#[v0] : Array Value).size = 1 := by simp
        by_cases hi0 : i = 0
        · subst hi0
          have hzero : (#[v0] ++ vsTail)[0] = v0 := by
            simp [Array.getElem_append]
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
termination_by (fuel, 2, sizeOf ts, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
       simp only [List.cons.sizeOf_spec]; omega)

/-- Preservation through `evalBinField`. The closure `k` here always returns
either `.field _` or `.tuple #[.field _, .field _]`, both FnFree. -/
theorem evalBinField_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (fuel : Nat) (bindings : Bindings) (t1 t2 : Concrete.Term) (st : EvalState)
    (k : G → G → Value)
    (hk : ∀ a b, Value.FnFree (k a b))
    (hb : BindingsFnFree bindings)
    (ht1Refs : Concrete.Term.RefsDt cd t1) (ht2Refs : Concrete.Term.RefsDt cd t2)
    (ht1TypesNF : Concrete.Term.TypesNotFunction cd t1)
    (ht2TypesNF : Concrete.Term.TypesNotFunction cd t2)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.evalBinField cd fuel bindings t1 t2 st k = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.evalBinField at heval
  split at heval
  · cases heval  -- error
  · rename_i v1_st1 hres1
    obtain ⟨v1, st1⟩ := v1_st1
    split at heval
    · cases heval  -- error
    · rename_i v2_st2 hres2
      obtain ⟨v2, st2⟩ := v2_st2
      -- match on v1, v2 — closure k returns its result only when both are .field.
      split at heval
      · -- both .field
        rename_i a b
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact hk a b
      · cases heval  -- type mismatch
termination_by (fuel, 2, sizeOf t1 + sizeOf t2 + 1, 0)

end

/-! #### Main body — closes via `applyGlobal_FnFree`. -/

/-- Main result. Sig matches `Concrete.Eval.runFunction_preserves_FnFree`
(post-TermRefsDt absorption). Reduces to `applyGlobal_FnFree` from the
mutual block above. -/
theorem runFunction_preserves_FnFree_body
    (cd : Concrete.Decls)
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (io : IOBuffer)
    (_hrun : Concrete.Eval.runFunction cd name args io₀ fuel = .ok (v, io)) :
    Value.FnFree v := by
  -- Unfold runFunction: it's a let-binding + outer match. Reduce by hand.
  have hrun_eq :
      Concrete.Eval.runFunction cd name args io₀ fuel =
      (match Concrete.Eval.applyGlobal cd fuel name args { ioBuffer := io₀ } with
       | .error e => Except.error e
       | .ok (v, st') => .ok (v, st'.ioBuffer)) := rfl
  rw [hrun_eq] at _hrun
  split at _hrun
  · cases _hrun
  · rename_i v' st' hcall
    injection _hrun with hpair
    injection hpair with hv _
    subst hv
    exact applyGlobal_FnFree cd _hFOR _hRefClosed _hTermRefsDt _hTypesNF fuel name args
      { ioBuffer := io₀ } _hargsFnFree v' st' hcall

end FnFreeBody

/-- Concrete-eval preserves `FnFree` on returns when args are FnFree, the
decls have first-order inputs/outputs (ruling out `.fn`-valued returns via
`.ref g` where `g` is a function key), and the decls' function bodies are
well-typed. Type-soundness consequence: well-typed first-order program returns
first-order values. BLOCKED ON: type-preservation theorem through
`Concrete.Eval.runFunction` — needs an inductive over fuel + recursion through
callees. -/
theorem Concrete.Eval.runFunction_preserves_FnFree
    (cd : Concrete.Decls)
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    -- Sig strengthened (2026-04-24, SORRY_AUDIT_AGENT1.md §1): `.ref g` in
    -- concrete types must resolve to a `.dataType` (not `.function`), else
    -- `.ref fSelf` with `f.output = .ref fSelf` satisfies `FirstOrderReturn`
    -- yet evaluates to `.fn fSelf` — counterexample to FALSE-as-stated.
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    -- Sig strengthened (2026-04-24, `FnFreeSigFixScratch`): TYPE-level
    -- `RefClosed` insufficient because `Concrete.Term.ref g` TERM evaluates
    -- to `.fn g` when `g` names a function. `TermRefsDt` rules that out.
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    -- Sig strengthened (2026-04-28, SD-LoadType): `letLoad` and `load` arms
    -- read from `unflattenValue` whose result is `.fn _` whenever the carrier
    -- type contains `.function`. This invariant rules that out.
    (_hTypesNF : Concrete.Decls.TypesNotFunction cd)
    (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (io : IOBuffer)
    (_hrun : Concrete.Eval.runFunction cd name args io₀ fuel = .ok (v, io)) :
    Value.FnFree v :=
  FnFreeBody.runFunction_preserves_FnFree_body
    cd name args io₀ fuel _hFOR _hRefClosed _hTermRefsDt _hTypesNF _hargsFnFree v io _hrun

end Aiur

end -- public section
