import Compilatrix.Anf.Proof.Pass.RenLevel

/-! # Pruning is correct

On a program whose global ids are exactly `0 … size - 1` (`GlobalsBelow`
and `Dense`), `Prune.run` keeps the globals `reach` finds (the roots and
everything they reference, `run_seen`), renumbers them densely in order and
renames every reference; the kept globals sit at their new ids with renamed
bodies, so the renaming simulation applies (`Setting`, `refines`) and the
pruned program refines its input (`run_refines`, M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf

namespace Prune.Proof

open Compilatrix.Anf.Rel (Pw)

theorem filterMap_getElem? {α β : Type} {f : α → Option β} : ∀ {l : List α},
    (∀ x ∈ l, ∃ y, f x = some y) → ∀ i : Nat, (l.filterMap f)[i]? = (l[i]?).bind f
  | [], _, i => by simp
  | x :: l, h, i => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    simp only [List.filterMap_cons, hy]
    cases i with
    | zero => simp [hy]
    | succ i => simpa using filterMap_getElem? (fun z hz => h z (List.mem_cons_of_mem _ hz)) i

theorem zipIdx_keys {α : Type} (l : List α) : (l.zipIdx.map fun p => (p.2, p.1)).map (·.1) = List.range l.length := by
  apply List.ext_getElem?
  intro j
  simp only [List.map_map, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_range]
  by_cases hj : j < l.length
  · simp [hj]
  · simp [hj]

theorem zipIdx_fst {α : Type} (l : List α) : l.zipIdx.map (·.1) = l := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  cases l[j]? <;> rfl

theorem withGlobals_global (P : Program) (gs : List GDef) (i : Nat) :
    (P.withGlobals gs).global? i = gs[i]? := by
  show (Src.NatMap.ofList (gs.zipIdx.map fun (p : GDef × Nat) => (p.2, p.1))).get? i = gs[i]?
  have hn : ((gs.zipIdx.map fun (p : GDef × Nat) => (p.2, p.1)).map (·.1)).Nodup := by
    rw [zipIdx_keys]; exact List.nodup_range
  cases hgi : gs[i]? with
  | some gd =>
    refine Src.NatMap.get?_ofList hn (List.mem_map.2 ⟨(gd, i), List.mem_zipIdx_iff_getElem?.2 hgi, rfl⟩)
  | none =>
    cases hx : (Src.NatMap.ofList (gs.zipIdx.map fun (p : GDef × Nat) => (p.2, p.1))).get? i with
    | none => rfl
    | some x =>
      have := Convert.Proof.natMap_ofList_mem hn hx
      obtain ⟨⟨gd, j⟩, hm, he⟩ := List.mem_map.1 this
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [List.mem_zipIdx_iff_getElem?] at hm
      rw [hm] at hgi; cases hgi

/-- `reach`'s fuel in `run`. -/
def fuelOf (P : Program) : Nat :=
  P.size + P.globalList.foldl (fun n (p : GlobalId × GDef) => n + p.2.body.refs.length) 0 + P.roots.length + 1

/-- The globals `run` keeps, in order. -/
def keptOf (P : Program) : List GlobalId := (List.range P.size).filter (reach P (fuelOf P) P.roots .leaf).contains

/-- The renumbering. -/
def renOf (P : Program) : Src.NatMap Nat := Src.NatMap.ofList (keptOf P).zipIdx

theorem run_eq' (P : Program) : run P =
    { P.withGlobals ((keptOf P).filterMap fun g =>
        (P.global? g).map fun gd => { gd with body := Exp.rename (renOf P) gd.body }) with
      roots := P.roots.map fun r => (renOf P).getD r r } := rfl

variable {P : Program}

theorem keptOf_nodup (P : Program) : (keptOf P).Nodup := List.filter_sublist.nodup List.nodup_range

theorem renOf_kept {g : GlobalId} {i : Nat} (hi : (keptOf P)[i]? = some g) : (renOf P).getD g g = i := by
  unfold Src.NatMap.getD renOf
  rw [Src.NatMap.get?_ofList (by rw [zipIdx_fst]; exact keptOf_nodup P) (List.mem_zipIdx_iff_getElem?.2 hi)]
  rfl

/-- The renaming setting of a pruning. -/
def setting (hb : P.GlobalsBelow) (hd : P.Dense) : Setting where
  P := P
  Q := run P
  S := reach P (fuelOf P) P.roots .leaf
  m := renOf P
  known := rfl
  closed g gd hg hgd := fun h hh => (run_seen hb).1 g hg h (by unfold refsOf; rw [hgd]; exact hh)
  glob g gd hg hgd := by
    have hlt := hb g gd hgd
    have hmem : g ∈ keptOf P := List.mem_filter.2 ⟨List.mem_range.2 hlt, hg⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    rw [renOf_kept hi, run_eq' P]
    show (P.withGlobals _).global? i = _
    rw [withGlobals_global, filterMap_getElem? _ i, hi]
    · simp [hgd]
    · intro x hx
      obtain ⟨hx1, -⟩ := List.mem_filter.1 hx
      obtain ⟨gdx, hgdx⟩ := hd x (List.mem_range.1 hx1)
      exact ⟨_, by rw [hgdx]; rfl⟩

/-- **Pruning is correct**: on a program whose ids are exactly the globals
below its size, the pruned program refines it and has that shape again. -/
theorem run_refines (hw : P.WF) : (run P).WF ∧ Sem.Refines P (run P) := by
  obtain ⟨hb, hd⟩ := hw
  have hgl : ∀ i, (run P).global? i = ((keptOf P).filterMap fun g =>
      (P.global? g).map fun gd => { gd with body := Exp.rename (renOf P) gd.body })[i]? := by
    intro i; rw [run_eq' P]; exact withGlobals_global P _ i
  have hsize : (run P).size = ((keptOf P).filterMap fun g =>
      (P.global? g).map fun gd => { gd with body := Exp.rename (renOf P) gd.body }).length := by
    rw [run_eq' P]; rfl
  refine ⟨⟨fun i gd h => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [hgl] at h
    rw [hsize]
    exact (List.getElem?_eq_some_iff.1 h).1
  · rw [hsize] at hi
    exact ⟨_, by rw [hgl]; exact List.getElem?_eq_getElem hi⟩
  · exact Prune.Proof.refines (X := setting hb hd) (by show (run P).roots = _; rw [run_eq' P]; rfl)
      fun r hr => (run_seen hb).2 r hr


/-- Pruning as a pass (no certificate). -/
def prunePass : Sem.Transform Program Program where
  name := "prune"
  pre P := P.WF
  run P _ := pure (run P)
  post Q := Q.WF
  correct P _ Q hw h := by cases h; exact run_refines hw

/-! ## The traced shape (decision D-1) -/

theorem run_refines_traced (hw : P.WF) : Sem.TRefines P (run P) :=
  Sem.Refines.ofPure (run_refines hw).2

/-- Pruning as a traced pass. -/
def pruneTPass : Sem.TTransform Program Program := prunePass.lift

end Prune.Proof

end Compilatrix.Anf
