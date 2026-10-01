import Compilatrix.Rt.Proof.Publish
import Compilatrix.Cfg.Proof.Lang
import Compilatrix.Sem.View

/-!
# Lir as a language: the lowered program loaded into a region (M2.7)

The `Lang` binding of the lowered program (`Rt.Loaded`), on the input every
Phase 1 level shares (root index, `Nat` arguments):

* **Entry convention.** Entry `i.1` (one per Cfg export, in export order) is
  applied as Anf applies a root (`Sem.entryRun`): exactly its parameter
  count calls it; fewer arguments give a value with no observation; more
  call it on the first ones and are stuck.
* **A call** (`Loaded.call`): an argument at or above `2^63` has no tagged
  word, and the call fails with `natOverflow` (the native wrapper's status
  3); otherwise `cx_init` runs over the model region (`Model`: context
  pointer, size, budget, memory), then the entry's function on the tagged
  words (`natWord`) in the memory `cx_init` leaves.
* **Observation.** The result word is read back at the entry's readback
  type (`Rt.readback`, fuel the region's size in words): the value is the
  observation itself (`Val := Option Obs`).

`Rt.lower_refines`: for a program `Rt.lower` and the pipeline's switch
check accept, on a model region `cx_init` accepts (`RegionOk`, `Region`),
the loaded program refines Cfg viewed at the roots' readback types
(`viewOf`: the source observation relabelled by tag, `tagify`, at a root
with a type; nothing at a root without; a result `tagify` rejects is stuck,
so it imposes nothing). The bridge between the two observations is
`tagify_value`: a Cfg value related to a word whose observation `tagify`
accepts is `Typed` at the type, and reads back, at every fuel and in Own
(`H.readback`), as `tagify` relabels it; `result_view` is the same through
`Rt.result_readback` for a final result, and `tagify_fir` at Fir
(`Fir.obsV` against `Fir.readback`, which `Own.readback_den` carries to
Own). Phase 1 reads `Nat` and field-less constructors (`Bool`): `tagify`
accepts nothing else.
-/

set_option autoImplicit false

namespace Compilatrix.Rt

open Compilatrix.Lir (Word)
open Compilatrix.Sem (Result ClockMono Obs Lang Sim)
open Compilatrix.Rt.Proof
open Compilatrix.Rt.Lower (Tables tables)

/-! ## The language -/

/-- How a root is entered and read back: its Lir function, its parameter
count, and its readback signature and type (`none`: read back as
nothing). -/
structure Entry where
  fn : Lir.FunId
  params : Nat
  ty : Option (Sig × FoTy)

/-- The machine the lowered program runs in: the context pointer and the
region size `cx_init` checks, its budget argument, and the memory. -/
structure Model where
  ctx : Word
  size : Word
  budget : Word
  mem : X86.Memory

/-- The readback fuel: the region's size in words (04 §6). -/
def Model.fuel (M : Model) : Nat := M.size.toNat / 8

/-- A lowered program with its entries, loaded into a machine. -/
structure Loaded where
  program : Lir.Program
  init : Lir.FunId
  entries : List Entry
  model : Model

/-- A result read back at an entry's type: one word, read back. -/
def Entry.observe (e : Entry) (fuel : Nat) (vals : List Word) (m : X86.Memory) : Option Obs :=
  match e.ty, vals with
  | some (sig, ty), [w] => readback sig fuel m ty w
  | _, _ => none

/-- `Nat` inputs as tagged words, if each is below `2^63`. -/
def natWords (ns : List Nat) : Option (List Word) := ns.mapM natWord

/-- A call of an entry on exactly its arguments (see the module note). -/
def Loaded.call (S : Loaded) (e : Entry) (ns : List Nat) (k : Nat) : Result (Option Obs) :=
  match natWords ns with
  | none => .resource .natOverflow
  | some ws =>
    (Lir.eval { S.program with main := S.init } k [S.model.size, S.model.budget] S.model.mem S.model.ctx).bind
      fun r => (Lir.eval { S.program with main := e.fn } k ws r.2 S.model.ctx).map
        fun r' => e.observe S.model.fuel r'.1 r'.2

/-- A run of entry `i.1` on the `Nat` inputs `i.2`, applied as Anf applies
a root. -/
def Loaded.run (S : Loaded) (i : Nat × List Nat) (k : Nat) : Result (Option Obs) :=
  match S.entries[i.1]? with
  | some e => Sem.entryRun e.params none (S.call e) i.2 k
  | none => .stuck

theorem Loaded.call_mono (S : Loaded) (e : Entry) (ns : List Nat) : ClockMono (S.call e ns) := by
  unfold Loaded.call
  split
  · exact ClockMono.const _
  · exact ClockMono.bind (Lir.eval_mono _ _ _ _) fun _ =>
      ClockMono.bind (Lir.eval_mono _ _ _ _) fun _ => ClockMono.const _

instance : Lang (Nat × List Nat) Loaded where
  Val := Option Obs
  run := Loaded.run
  mono S i := by
    unfold Loaded.run
    split
    · exact Sem.entryRun_mono (fun ns => S.call_mono _ ns) _
    · exact ClockMono.const _
  obs := id

theorem Loaded.lang_run (S : Loaded) (i : Nat × List Nat) : Lang.run S i = S.run i := rfl

/-! ## The view at the roots' readback types -/

/-- A source observation at a readback type, as the runtime reads it back:
a `Nat`, or a constructor without fields whose table tag the signature lists
without fields (`none` otherwise: Phase 1 reads back nothing else). -/
def tagify (T : List Lam.CtorInfo) (sig : Sig) : FoTy → Obs → Option Obs
  | .nat, .nat n => some (.nat n)
  | .ind i, .ctor cid [] =>
    match Fir.CtorInfo.ofKey T (.src cid) with
    | some c => if sig.ctor? i c.tag = some [] then some (.ctor c.tag []) else none
    | none => none
  | _, _ => none

/-- The view of the front half: at a root with a readback type, the source
observation relabelled by `tagify` (a result it rejects is stuck); at a root
without one, nothing. -/
def viewOf (T : List Lam.CtorInfo) (tys : Nat → Option (Sig × FoTy)) (r : Nat) (o : Option Obs) :
    Option (Option Obs) :=
  match tys r with
  | none => some none
  | some (sig, ty) => (o.bind (tagify T sig ty)).map some

/-- The entries of a lowered program: one per root, in export order. -/
def entriesOf (C : Cfg.Program) (roots : List (Lir.FunId × String)) (tys : Nat → Option (Sig × FoTy)) :
    List Entry :=
  roots.zipIdx.map fun (p, r) => { fn := p.1, params := ((C.fun? p.1).map (·.params.length)).getD 0, ty := tys r }

/-- A lowered program loaded into a machine, its roots read back at
`tys`. -/
def Loaded.ofLowered (C : Cfg.Program) (L : Lowered) (tys : Nat → Option (Sig × FoTy)) (M : Model) : Loaded :=
  { program := L.program, init := L.init, entries := entriesOf C L.roots tys, model := M }

theorem entriesOf_get (C : Cfg.Program) (roots : List (Lir.FunId × String)) (tys : Nat → Option (Sig × FoTy))
    (r : Nat) :
    (entriesOf C roots tys)[r]? =
      (roots[r]?).map fun p => { fn := p.1, params := ((C.fun? p.1).map (·.params.length)).getD 0, ty := tys r } := by
  unfold entriesOf
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases roots[r]? <;> simp

/-! ## The lowering's shape -/

/-- `Rt.lower` numbers `cx_init` after the program's functions and keeps
its roots in export order. -/
theorem lower_shape {cfg : Config} {P : Cfg.Program} {L : Lowered} (h : lower cfg P = .ok L) :
    L.init = P.size ∧ L.roots.map (·.1) = P.exports := by
  unfold lower at h
  cases hm : P.exports.head? with
  | none => simp [hm, throw, throwThe, MonadExceptOf.throw] at h
  | some main =>
    simp only [hm, bind, Except.bind] at h
    cases hr : P.funs.toList.find? (P.size ≤ ·.1) with
    | some p => simp [hr, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hr] at h
      split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨rfl, ?_⟩
        simp [List.map_map, Function.comp_def]

/-! ## Arguments -/

theorem natWords_rel {T : Tables} {Pw : List Word} :
    ∀ {ns : List Nat} {ws : List Word}, natWords ns = some ws → ListRel (ValRel T Pw) (Own.litArgs ns) ws
  | [], ws, h => by
    simp only [natWords, List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact .nil
  | n :: ns, ws, h => by
    simp only [natWords, List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    exact .cons hw (natWords_rel hws)

/-! ## The observation bridge -/

theorem toFir_lit {H : Own.Heap} {k : Nat} {v : Own.RVal} {l : Lam.Lit} (h : Own.toFir H k v = some (.lit l)) :
    v = .lit l := by
  cases v with
  | lit l' => simp only [Own.toFir, Option.some.injEq, Fir.Val.lit.injEq] at h; rw [h]
  | ctor0 c => simp [Own.toFir] at h
  | erased => simp [Own.toFir] at h
  | loc ℓ =>
    cases k with
    | zero => simp [Own.toFir] at h
    | succ k =>
      simp only [Own.toFir] at h
      split at h
      · simp at h
      · cases h

theorem obsList_nil {fs : List Fir.Val} (h : Fir.obsList fs = some []) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    simp only [Fir.obsList] at h
    split at h <;> simp at h

/-- **The observation bridge** (Cfg → Lir): a Cfg value related to a word
under the heap invariant, whose observation `tagify` relabels at a readback
type, is `Typed` at that type and reads back as the relabelling, at every
fuel in the runtime and in Own. -/
theorem tagify_value {T : Tables} {Pw : List Word} {H : Own.Heap} {ctx : Word} {m : X86.Memory}
    {v : Own.RVal} {w : Word} {sig : Sig} {ty : FoTy} {o o' : Obs}
    (hv : ValRel T Pw v w) (hheap : HeapInv T Pw H ctx m) (ho : Own.obsV (v, H) = some o)
    (ht : tagify T.ctors sig ty o = some o') :
    Typed sig H ty v ∧ (∀ fuel, readback sig fuel m ty w = some o') ∧ H.readback v = some o' := by
  simp only [Own.obsV, Own.Heap.value?, Option.bind_eq_some_iff] at ho
  obtain ⟨fv, hfv, ho⟩ := ho
  cases v with
  | lit l =>
    cases l with
    | str s => exact absurd hv id
    | nat n =>
      simp only [Own.toFir, Option.some.injEq] at hfv
      subst hfv
      simp only [Fir.obsV, Option.some.injEq] at ho
      subst ho
      cases ty with
      | nat =>
        simp only [tagify, Option.some.injEq] at ht
        subst ht
        exact ⟨.nat, fun _ => readback_nat hv, by simp [Own.Heap.readback, Own.Heap.value?, Own.toFir, Fir.readback]⟩
      | ind i => simp [tagify] at ht
  | ctor0 c =>
    simp only [Own.toFir, Option.some.injEq] at hfv
    subst hfv
    obtain ⟨rfl, hc, hf⟩ := hv
    simp only [Fir.obsV] at ho
    split at ho
    · rename_i cid hkey
      simp only [Fir.obsList, Option.map_some, Option.some.injEq] at ho
      subst ho
      cases ty with
      | nat => simp [tagify] at ht
      | ind i =>
        simp only [tagify] at ht
        rw [← hkey, hc.table] at ht
        simp only at ht
        split at ht
        · rename_i hsig
          simp only [Option.some.injEq] at ht
          subst ht
          have htag : c.tag < natLimit := Nat.lt_of_le_of_lt hc.tag (by decide)
          have har : (c.arity == 0) = true := hf
          refine ⟨.ctor0 hsig, fun _ => readback_ctor0 htag hsig, ?_⟩
          simp only [Own.Heap.readback, Own.Heap.value?, Own.toFir, Option.bind_some, Fir.readback,
            List.length_nil]
          rw [if_pos (by simpa using har)]
          rfl
        · cases ht
    · cases ho
  | erased =>
    simp only [Own.toFir, Option.some.injEq] at hfv
    subst hfv
    simp [Fir.obsV] at ho
  | loc ℓ =>
    exfalso
    obtain ⟨bump, limit, hA⟩ := hheap
    simp only [Own.toFir, Own.Heap.cell?] at hfv
    split at hfv
    · rename_i rc mode b hcell
      obtain ⟨fs, hfs, rfl⟩ := Option.map_eq_some_iff.1 hfv
      obtain ⟨-, hca, -, -⟩ := hA.cell hv hcell
      have hlen := toFirList_length hfs
      simp only [Fir.obsV] at ho
      split at ho
      · obtain ⟨os, hos, rfl⟩ := Option.map_eq_some_iff.1 ho
        cases ty with
        | nat => simp [tagify] at ht
        | ind i =>
          cases os with
          | nil =>
            have := obsList_nil hos
            subst this
            have hfl := hca.fieldless
            have har := hca.arity
            simp only [Fir.CtorInfo.fieldless, beq_eq_false_iff_ne, ne_eq] at hfl
            simp at hlen
            exact hfl (by rw [← har, ← hlen])
          | cons _ _ => simp [tagify] at ht
      · cases ho
    · cases hfv

/-- **The bridge at Fir**: a Fir value whose constructors are the table's,
with their field counts, reads back (`Fir.readback`, by tag) as `tagify`
relabels its observation (`Fir.obsV`, by source constructor). With
`Own.readback_den` it is Own's readback of a value that denotes it. -/
theorem tagify_fir {T : List Lam.CtorInfo} {sig : Sig} {ty : FoTy} {fv : Fir.Val} {o o' : Obs}
    (hc : ∀ c fs, fv = .ctor c fs → Fir.CtorInfo.ofKey T c.key = some c ∧ c.arity = fs.length)
    (ho : Fir.obsV fv = some o) (ht : tagify T sig ty o = some o') : Fir.readback fv = some o' := by
  cases fv with
  | lit l =>
    cases l with
    | nat n =>
      simp only [Fir.obsV, Option.some.injEq] at ho
      subst ho
      cases ty with
      | nat => simp only [tagify, Option.some.injEq] at ht; subst ht; rfl
      | ind i => simp [tagify] at ht
    | str s =>
      simp only [Fir.obsV, Option.some.injEq] at ho
      subst ho
      cases ty <;> simp [tagify] at ht
  | ctor c fs =>
    obtain ⟨hkey, har⟩ := hc c fs rfl
    simp only [Fir.obsV] at ho
    split at ho
    · rename_i cid hcid
      obtain ⟨os, hos, rfl⟩ := Option.map_eq_some_iff.1 ho
      cases ty with
      | nat => simp [tagify] at ht
      | ind i =>
        cases os with
        | cons _ _ => simp [tagify] at ht
        | nil =>
          have hfs := obsList_nil hos
          subst hfs
          simp only [tagify] at ht
          rw [← hcid, hkey] at ht
          simp only at ht
          split at ht
          · simp only [Option.some.injEq] at ht
            subst ht
            simp only [Fir.readback, List.length_nil]
            rw [if_pos (by simpa using har)]
            rfl
          · cases ht
    · cases ho
  | erased => simp [Fir.obsV] at ho

/-- **The final result through `Rt.result_readback`**: a Cfg result related
by `Res` whose observation `tagify` accepts at the root's readback type is
`Typed` at it, and the runtime's readback at Own's fuel is Own's readback,
the relabelled observation. -/
theorem result_view {P : Cfg.Program} {ctx : Word} {v : Own.RVal} {H : Own.Heap} {vals : List Word}
    {m : X86.Memory} {sig : Sig} {ty : FoTy} {o o' : Obs} (hres : Res P ctx (v, H) (vals, m))
    (ho : Own.obsV (v, H) = some o) (ht : tagify P.ctors sig ty o = some o') :
    Typed sig H ty v ∧ ∃ w, vals = [w] ∧ readback sig (H.size + 1) m ty w = H.readback v ∧
      H.readback v = some o' := by
  obtain ⟨Pw, w, -, hv, hheap⟩ := id hres
  obtain ⟨hty, -, hrb⟩ := tagify_value (T := tables P) hv hheap ho ht
  obtain ⟨w', hw', hrb'⟩ := result_readback hres hty
  exact ⟨hty, w', hw', hrb', hrb⟩

/-- The view's report for a final Cfg result is the entry's read-back
observation of the related Lir result. -/
theorem view_observe {C : Cfg.Program} {ctx : Word} {tys : Nat → Option (Sig × FoTy)} {r : Nat}
    {v : Own.RVal × Own.Heap} {vals : List Word} {m : X86.Memory} {o : Option Obs} (f p fuel : Nat)
    (hres : Res C ctx v (vals, m)) (hview : viewOf C.ctors tys r (Own.obsV v) = some o) :
    ({ fn := f, params := p, ty := tys r } : Entry).observe fuel vals m = o := by
  obtain ⟨Pw, w, hw, hv, hheap⟩ := hres
  simp only at hw hv hheap
  subst hw
  unfold viewOf at hview
  unfold Entry.observe
  cases hty : tys r with
  | none => rw [hty] at hview; simp only [Option.some.injEq] at hview; exact hview
  | some st =>
    obtain ⟨sig, ty⟩ := st
    rw [hty] at hview
    simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at hview
    obtain ⟨o', ⟨o₀, ho₀, ht⟩, rfl⟩ := hview
    exact (tagify_value (T := tables C) hv hheap ho₀ ht).2.1 fuel

/-! ## Cfg → Lir on every input -/

/-- What a Cfg result and a call's result are to each other: the view of
the Cfg result is the call's, or rejects it. -/
def CallRel (C : Cfg.Program) (tys : Nat → Option (Sig × FoTy)) (r : Nat) (v : Own.RVal × Own.Heap)
    (o : Option Obs) : Prop :=
  Sem.viewResult (viewOf C.ctors tys) r (Own.obsV v) = .ok o ∨
    Sem.viewResult (viewOf C.ctors tys) r (Own.obsV v) = .stuck

/-- An exact-arity call simulates Cfg's run of the root. -/
theorem call_sim {cfg : Config} {C : Cfg.Program} {L : Lowered} (h : lower cfg C = .ok L)
    (hsw : switchesOk C = true) (tys : Nat → Option (Sig × FoTy)) {M : Model}
    (hok : RegionOk M.ctx M.size) (hreg : Region M.mem M.ctx M.size) (r f p : Nat) (ns : List Nat) :
    Sim (CallRel C tys r) (· + 1) (fun k => Cfg.run .immortal C k f (Own.litArgs ns) {})
      (fun k => (Loaded.ofLowered C L tys M).call { fn := f, params := p, ty := tys r } ns k) := by
  cases hws : natWords ns with
  | none =>
    refine Sim.ofEq (Sim.to_resource .natOverflow) (fun _ => rfl) fun k => ?_
    simp [Loaded.call, hws]
  | some ws =>
    obtain ⟨left, mem', hinit, -, hsim⟩ := init_correct_checked h hsw (budget := M.budget) hok hreg
    have hs := (hsim (g := f) (natWords_rel (T := tables C) (Pw := []) hws)).map_right
      fun r' => ({ fn := f, params := p, ty := tys r } : Entry).observe M.fuel r'.1 r'.2
    refine Sim.ofEq (hs.mono ?_) (fun _ => rfl) fun k => ?_
    · rintro v o ⟨⟨vals, m⟩, hres, rfl⟩
      unfold CallRel Sem.viewResult
      split
      · rename_i o' hview
        exact .inl (by rw [view_observe f p M.fuel hres hview])
      · exact .inr rfl
    · simp only [Loaded.call, hws, Loaded.ofLowered]
      rw [(lower_shape h).1, hinit k, Sem.Result.bind_ok]

/-- **Cfg → Lir refines** (M2.7): on a model region `cx_init` accepts, the
loaded program refines Cfg viewed at the roots' readback types, for a
program `Rt.lower` and the pipeline's switch check accept. -/
theorem lower_refines {cfg : Config} {C : Cfg.Program} {L : Lowered} (h : lower cfg C = .ok L)
    (hsw : switchesOk C = true) (tys : Nat → Option (Sig × FoTy)) {M : Model}
    (hok : RegionOk M.ctx M.size) (hreg : Region M.mem M.ctx M.size) :
    Sem.Refines (⟨C, viewOf C.ctors tys⟩ : Sem.Viewed Cfg.Program) (Loaded.ofLowered C L tys M) := by
  refine Sem.Refines.of_sim (R := Eq) (fun _ _ h => h) fun i => ?_
  obtain ⟨r, ns⟩ := i
  have hshape := (lower_shape h).2
  change ∃ f, Sim Eq f (fun k => (Cfg.cfgRun C (r, ns) k).bind fun v => Sem.viewResult (viewOf C.ctors tys) r (Own.obsV v))
    ((Loaded.ofLowered C L tys M).run (r, ns))
  unfold Cfg.cfgRun Loaded.run
  simp only [Loaded.ofLowered, entriesOf_get]
  have hroot : L.roots[r]?.map (·.1) = C.exports[r]? := by rw [← hshape, List.getElem?_map]
  cases hex : C.exports[r]? with
  | none =>
    rw [hex] at hroot
    rw [Option.map_eq_none_iff.1 hroot]
    exact ⟨id, Sim.of_stuck⟩
  | some f₀ =>
    rw [hex] at hroot
    obtain ⟨⟨f, s⟩, hl, hf⟩ := Option.map_eq_some_iff.1 hroot
    simp only at hf
    subst hf
    rw [hl]
    simp only [Option.map_some]
    cases hfd : C.fun? f with
    | none => exact ⟨id, Sim.of_stuck⟩
    | some fd =>
      simp only [Option.map_some, Option.getD_some]
      refine ⟨(· + 1), ?_⟩
      have hcs := call_sim h hsw tys hok hreg r f fd.params.length
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        refine (hcs ns).bind_left (fun v o hvo => ?_) fun _ => Sem.viewResult_ne_timeout _ _ _
        rcases hvo with h' | h' <;> rw [h']
        · exact .ok rfl
        · exact .stuck
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          have hv : Sem.Result.Refines Eq (Sem.viewResult (viewOf C.ctors tys) r (Own.obsV (.erased, {})))
              (.ok (none : Option Obs)) := by
            rw [Own.obsV_erased]
            unfold Sem.viewResult viewOf
            cases tys r with
            | none => exact .ok rfl
            | some st => exact .stuck
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte, Sem.Result.bind_ok]
            exact Sim.const_refines hv
          · simp only [hn, ↓reduceIte]
            exact Sim.ofEq (Sim.later_refines hv fun _ h => nomatch h) (fun k => Sem.later_bind _ _ _)
              fun _ => rfl
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          refine Sim.ofEq (Sim.bindStuck (R' := Eq) (g := fun _ _ => .stuck) (hcs (ns.take fd.params.length))
            fun _ _ _ => rfl) (fun k => Sem.bind_stuck_bind _ _) fun _ => rfl

/-- `lower_refines` in the traced shape (decision D-1). -/
theorem lower_refines_traced {cfg : Config} {C : Cfg.Program} {L : Lowered} (h : lower cfg C = .ok L)
    (hsw : switchesOk C = true) (tys : Nat → Option (Sig × FoTy)) {M : Model}
    (hok : RegionOk M.ctx M.size) (hreg : Region M.mem M.ctx M.size) :
    Sem.TRefines (⟨C, viewOf C.ctors tys⟩ : Sem.Viewed Cfg.Program) (Loaded.ofLowered C L tys M) :=
  Sem.Refines.ofPure (lower_refines h hsw tys hok hreg)

end Compilatrix.Rt
