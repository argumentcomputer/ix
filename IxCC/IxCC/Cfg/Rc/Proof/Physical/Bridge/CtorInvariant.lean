import IxCC.Rt.Proof.Heap
import IxCC.Own.Rc.Proof.Shape

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof (CtorOk)

/-- Table compatibility of immediates is independent of heap liveness. A
location entry, including a stale one, makes no claim about its cell. -/
def ValueCtorOk (tables : Rt.Lower.Tables) : RVal → Prop
  | .ctor0 c => CtorOk tables c ∧ c.fieldless = true
  | _ => True

def BodyCtorOk (tables : Rt.Lower.Tables) (body : Body) : Prop :=
  CtorOk tables body.ctor ∧ body.ctor.fieldless = false ∧
    ∀ value ∈ body.fields, ValueCtorOk tables value

def HeapCtorOk (tables : Rt.Lower.Tables) (heap : Heap) : Prop :=
  ∀ location refs mode body, heap.cell? location = some (.live refs mode body) →
    BodyCtorOk tables body

def EnvCtorOk (tables : Rt.Lower.Tables) (env : Own.Env) : Prop :=
  ∀ x value, env.get? x = some value → ValueCtorOk tables value

theorem heapCtorOk_empty (tables : Rt.Lower.Tables) : HeapCtorOk tables {} := by
  intro l rc m b h
  simp [Heap.cell?] at h

theorem HeapCtorOk.sameBodies {tables : Rt.Lower.Tables} {H H' : Heap}
    (before : HeapCtorOk tables H) (same : SameBodies H H') : HeapCtorOk tables H' := by
  intro l rc m b cell
  have equal := same.2 l
  rw [cell] at equal
  cases old : H.cell? l with
  | none => simp [old, body?] at equal
  | some c =>
    cases c with
    | dead => simp [old, body?] at equal
    | live refs mode body =>
      simp only [old, Option.bind_some, body?, Option.some.injEq] at equal
      subst body
      exact before l refs mode b old

theorem HeapCtorOk.changeCount {tables : Rt.Lower.Tables} {H H' : Heap}
    (before : HeapCtorOk tables H) {f : Nat → Option Nat} {value : RVal}
    (effect : changeCount f H value = some H') : HeapCtorOk tables H' :=
  before.sameBodies (changeCount_sameBodies effect)

theorem HeapCtorOk.free {tables : Rt.Lower.Tables} {H : Heap}
    (before : HeapCtorOk tables H) {l : Nat} (bound : l < H.size) :
    HeapCtorOk tables (setCell H l .dead) := by
  intro k refs mode body cell
  rw [setCell_cell H l _ bound k] at cell
  by_cases equal : l = k
  · simp [equal] at cell
  · rw [if_neg equal] at cell
    exact before k refs mode body cell

theorem HeapCtorOk.alloc {tables : Rt.Lower.Tables} {H : Heap} {body : Body}
    (before : HeapCtorOk tables H) (compatible : BodyCtorOk tables body) :
    HeapCtorOk tables (H.alloc .rc body).2 := by
  intro l refs mode b cell
  have bound := Own.Proof.cell?_some cell
  have size := Own.Proof.alloc_size .rc H body
  by_cases old : l < H.size
  · rw [(Own.Proof.Ext.alloc .rc H body).2 l old] at cell
    exact before l refs mode b cell
  · have equal : l = H.size := by omega
    subst l
    rw [Own.Proof.alloc_cell] at cell
    simp only [AllocPol.mode, Option.some.injEq, Cell.live.injEq] at cell
    rcases cell with ⟨rfl, rfl, rfl⟩
    exact compatible

theorem HeapCtorOk.releaseOne {tables : Rt.Lower.Tables} {H H' : Heap}
    {value : RVal} {pending pending' : List RVal} (before : HeapCtorOk tables H)
    (effect : Own.Rc.releaseOne H value pending = some (H', pending')) : HeapCtorOk tables H' := by
  cases value with
  | loc l =>
    cases cell : H.cell? l with
    | none => simp [Own.Rc.releaseOne, cell] at effect
    | some c =>
      cases c with
      | dead => simp [Own.Rc.releaseOne, cell] at effect
      | live refs mode body =>
        cases mode with
        | static =>
          simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
          rcases effect with ⟨rfl, rfl⟩
          exact before
        | dyn =>
          cases refs with
          | zero => simp [Own.Rc.releaseOne, cell] at effect
          | succ refs =>
            cases refs with
            | zero =>
              simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
              rcases effect with ⟨rfl, rfl⟩
              exact before.free (Own.Proof.cell?_some cell)
            | succ refs =>
              simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
              rcases effect with ⟨rfl, rfl⟩
              exact before.sameBodies (sameBodies_set cell)
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at effect
    rcases effect with ⟨rfl, rfl⟩
    exact before

/-- Preservation follows the actual terminating release worklist. It adds no
operation-success requirement to callers that already derive release. -/
theorem HeapCtorOk.dropAll {tables : Rt.Lower.Tables} (H : Heap) (pending : List RVal)
    {H' : Heap} (before : HeapCtorOk tables H)
    (effect : Own.Rc.dropAll H pending = some H') : HeapCtorOk tables H' := by
  match pending with
  | [] =>
    simp only [Own.Rc.dropAll, Option.some.injEq] at effect
    subst H'
    exact before
  | value :: tail =>
    cases step : Own.Rc.releaseOne H value tail with
    | none =>
      rw [Own.Rc.dropAll, step] at effect
      cases effect
    | some result =>
      rcases result with ⟨next, rest⟩
      rw [Own.Rc.dropAll, step] at effect
      exact HeapCtorOk.dropAll next rest (before.releaseOne step) effect
termination_by (mass H, pending.length)
decreasing_by exact releaseOne_decreases step







end IxCC.Cfg.Rc.Proof.Physical.Bridge
