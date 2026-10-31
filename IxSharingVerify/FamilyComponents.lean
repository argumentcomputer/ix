import IxSharingVerify.FamilyCost
import IxC.Kernel.Audit.Axioms

/-! The uncertain components always pass their check.

`uncertainComponents` joins, with a union-find, every uncertain term with
the uncertain terms reachable below it through terms that are neither
certain-stored nor uncertain, then groups the uncertain terms by their final
root. This module proves that the result is a sorted partition of the
uncertain terms whose labels are separated by the certain-stored terms, so
`componentsChecked` accepts it on every well-formed DAG. The family route
therefore runs no partition check; the reference route's never refuses. -/

namespace Ix.Sharing.Verify.Components

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (CP NodeArity setBang_getElem! child_eq_getElem)

/-! ## Union-find -/

/-- Parent pointers over `0..n-1` that never point up. -/
structure UfWF (n : Nat) (uf : Array Nat) : Prop where
  size : uf.size = n
  down : ∀ x, x < n → uf[x]! ≤ x

theorem ufChase_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) :
    ∀ fuel x, x < n → x < fuel →
      ufChase uf fuel x ≤ x ∧ uf[ufChase uf fuel x]! = ufChase uf fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x _ h; omega
  | succ fuel ih =>
    intro x hx hf
    rw [ufChase.eq_2]
    by_cases root : (uf[x]! == x) = true
    · rw [ite_eq_left root]
      exact ⟨Nat.le_refl _, by simpa using root⟩
    · rw [ite_eq_right root]
      have hq : uf[x]! ≠ x := by simpa using root
      have hle := wf.down x hx
      obtain ⟨below, isRoot⟩ := ih uf[x]! (by omega) (by omega)
      exact ⟨by omega, isRoot⟩

theorem ufChase_fuel {n : Nat} {uf : Array Nat} (wf : UfWF n uf) :
    ∀ f g x, x < n → x < f → x < g → ufChase uf f x = ufChase uf g x := by
  intro f
  induction f with
  | zero => intro g x _ h; omega
  | succ f ih =>
    intro g x hx hf hg
    cases g with
    | zero => omega
    | succ g =>
      rw [ufChase.eq_2, ufChase.eq_2]
      by_cases root : (uf[x]! == x) = true
      · rw [ite_eq_left root, ite_eq_left root]
      · rw [ite_eq_right root, ite_eq_right root]
        have hq : uf[x]! ≠ x := by simpa using root
        have := wf.down x hx
        exact ih g uf[x]! (by omega) (by omega) (by omega)

theorem ufFind_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x : Nat} (hx : x < n) :
    ufFind uf x ≤ x ∧ uf[ufFind uf x]! = ufFind uf x :=
  ufChase_spec wf _ x hx (by rw [wf.size]; omega)

theorem ufFind_lt {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x : Nat} (hx : x < n) :
    ufFind uf x < n :=
  Nat.lt_of_le_of_lt (ufFind_spec wf hx).1 hx

theorem ufFind_of_root {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x : Nat} (root : uf[x]! = x) :
    ufFind uf x = x := by
  unfold ufFind
  rw [wf.size, ufChase.eq_2]
  rw [ite_eq_left (by simpa using root)]

theorem ufFind_step {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x : Nat} (hx : x < n)
    (h : uf[x]! ≠ x) : ufFind uf x = ufFind uf uf[x]! := by
  unfold ufFind
  rw [wf.size, ufChase.eq_2]
  rw [ite_eq_right (by simpa using h)]
  have := wf.down x hx
  exact ufChase_fuel wf n (n + 1) uf[x]! (by omega) (by omega) (by omega)

theorem ufFind_idem {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x : Nat} (hx : x < n) :
    ufFind uf (ufFind uf x) = ufFind uf x :=
  ufFind_of_root wf (ufFind_spec wf hx).2

/-- Pointing root `b` at the smaller root `a` sends exactly the class of `b`
to `a`. -/
theorem ufFind_set {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {a b : Nat} (hb : b < n)
    (hab : a < b) (ra : uf[a]! = a) (rb : uf[b]! = b) :
    UfWF n (uf.set! b a) ∧
      ∀ x, x < n → ufFind (uf.set! b a) x = if ufFind uf x = b then a else ufFind uf x := by
  have size : (uf.set! b a).size = n := by rw [size_setBang, wf.size]
  have bInside : b < uf.size := by rw [wf.size]; exact hb
  have atB : (uf.set! b a)[b]! = a := by
    rw [setBang_getElem!]; simp [bInside]
  have other : ∀ y, y ≠ b → (uf.set! b a)[y]! = uf[y]! := by
    intro y hy
    rw [setBang_getElem!]
    simp [Ne.symm hy]
  have wf' : UfWF n (uf.set! b a) := by
    refine ⟨size, fun x hx => ?_⟩
    by_cases hxb : x = b
    · subst hxb; rw [atB]; omega
    · rw [other x hxb]; exact wf.down x hx
  refine ⟨wf', ?_⟩
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    by_cases root : uf[x]! = x
    · rw [ufFind_of_root wf root]
      by_cases hxb : x = b
      · subst hxb
        rw [ite_eq_left rfl, ufFind_step wf' hx (by rw [atB]; omega), atB]
        exact ufFind_of_root wf' (by rw [other a (by omega)]; exact ra)
      · rw [ite_eq_right hxb]
        exact ufFind_of_root wf' (by rw [other x hxb]; exact root)
    · have hxb : x ≠ b := fun h => root (h ▸ rb)
      have below : uf[x]! < x := by have := wf.down x hx; omega
      rw [ufFind_step wf' hx (by rw [other x hxb]; exact root), other x hxb,
        ufFind_step wf hx root]
      exact ih uf[x]! below (by omega)

/-- Joining `x` and `y` puts them in one class and keeps every shared class. -/
theorem ufUnion_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) {x y : Nat} (hx : x < n)
    (hy : y < n) :
    UfWF n (ufUnion uf x y) ∧ ufFind (ufUnion uf x y) x = ufFind (ufUnion uf x y) y ∧
      ∀ u v, u < n → v < n → ufFind uf u = ufFind uf v →
        ufFind (ufUnion uf x y) u = ufFind (ufUnion uf x y) v := by
  have ax := ufFind_spec wf hx
  have ay := ufFind_spec wf hy
  have xLt := ufFind_lt wf hx
  have yLt := ufFind_lt wf hy
  unfold ufUnion
  dsimp only
  by_cases same : ufFind uf x = ufFind uf y
  · rw [ite_eq_right (by simp [same])]
    exact ⟨wf, same, fun _ _ _ _ h => h⟩
  · rw [ite_eq_left (by simpa using same)]
    by_cases lower : ufFind uf x < ufFind uf y
    · rw [ite_eq_left lower]
      obtain ⟨wf', find'⟩ := ufFind_set wf yLt lower ax.2 ay.2
      refine ⟨wf', ?_, ?_⟩
      · rw [find' x hx, find' y hy, ite_eq_right same, ite_eq_left rfl]
      · intro u v hu hv h
        rw [find' u hu, find' v hv, h]
    · rw [ite_eq_right lower]
      have higher : ufFind uf y < ufFind uf x := by omega
      obtain ⟨wf', find'⟩ := ufFind_set wf xLt higher ay.2 ax.2
      refine ⟨wf', ?_, ?_⟩
      · rw [find' x hx, find' y hy, ite_eq_left rfl, ite_eq_right (Ne.symm same)]
      · intro u v hu hv h
        rw [find' u hu, find' v hv, h]

/-- Join `t` with every element of `rs`, in order. -/
def unionAll (t : Nat) (uf : Array Nat) (rs : List Nat) : Array Nat :=
  rs.foldl (fun uf r => ufUnion uf t r) uf

/-- Joining `t` with every root of a list puts them in its class and keeps
every shared class. -/
theorem unionAll_spec {n : Nat} {t : Nat} (ht : t < n) :
    ∀ (rs : List Nat) (uf : Array Nat), UfWF n uf → (∀ r ∈ rs, r < n) →
      UfWF n (unionAll t uf rs) ∧
        (∀ r ∈ rs, ufFind (unionAll t uf rs) t = ufFind (unionAll t uf rs) r) ∧
        ∀ u v, u < n → v < n → ufFind uf u = ufFind uf v →
          ufFind (unionAll t uf rs) u = ufFind (unionAll t uf rs) v := by
  intro rs
  induction rs with
  | nil => intro uf wf _; exact ⟨wf, fun _ h => absurd h List.not_mem_nil, fun _ _ _ _ h => h⟩
  | cons r rest ih =>
    intro uf wf bound
    have step : unionAll t uf (r :: rest) = unionAll t (ufUnion uf t r) rest := rfl
    rw [step]
    obtain ⟨wf1, joined, mono1⟩ := ufUnion_spec wf ht (bound r List.mem_cons_self)
    obtain ⟨wf2, joined2, mono2⟩ :=
      ih (ufUnion uf t r) wf1 (fun r' h => bound r' (List.mem_cons_of_mem _ h))
    refine ⟨wf2, ?_, fun u v hu hv h => mono2 u v hu hv (mono1 u v hu hv h)⟩
    intro r' member
    rcases List.mem_cons.mp member with rfl | later
    · exact mono2 t r' ht (bound r' List.mem_cons_self) joined
    · exact joined2 r' later

/-! ## The component pass -/

/-- `z` is an uncertain term reachable from `t` through terms that are
neither certain-stored nor uncertain (`t` itself included, `z` excluded). -/
inductive Low (dag : Dag) (cls : Array UClass) : Nat → Nat → Prop
  | self {t : Nat} : cls[t]! = .uncertain → Low dag cls t t
  | down {t c z : Nat} : cls[t]! ≠ .certainStored → cls[t]! ≠ .uncertain →
      c ∈ (dag.node t).children → Low dag cls c z → Low dag cls t z

/-- The pass state after the terms below `k`. -/
structure PassInv (dag : Dag) (cls : Array UClass) (k : Nat) (uf : Array Nat)
    (reps : Array (Array Nat)) : Prop where
  wf : UfWF dag.size uf
  repsSize : reps.size = dag.size
  repsBound : ∀ u, u < dag.size → ∀ r ∈ reps[u]!.toList, r < dag.size
  covers : ∀ u, u < k → cls[u]! ≠ .certainStored → ∀ z, Low dag cls u z →
    ∃ r ∈ reps[u]!.toList, ufFind uf r = ufFind uf z
  joined : ∀ y, y < k → cls[y]! = .uncertain → ∀ c ∈ (dag.node y).children, ∀ z,
    Low dag cls c z → ufFind uf y = ufFind uf z

theorem low_le {dag : Dag} (hcp : CP dag.nodes) {cls : Array UClass} {t z : Nat}
    (h : Low dag cls t z) : t < dag.size → z ≤ t := by
  induction h with
  | self _ => intro _; exact Nat.le_refl _
  | @down t c z _ _ member _ ih =>
    intro ht
    have hc : c < t := hcp t ht c (by rw [← dag_node_eq ht]; exact member)
    have := ih (by omega)
    omega

theorem low_uncertain {dag : Dag} {cls : Array UClass} {t z : Nat} (h : Low dag cls t z) :
    cls[z]! = .uncertain := by
  induction h with
  | self h => exact h
  | down _ _ _ _ ih => exact ih

theorem low_of_uncertain {dag : Dag} {cls : Array UClass} {t z : Nat} (h : Low dag cls t z)
    (ht : cls[t]! = .uncertain) : z = t := by
  cases h with
  | self _ => rfl
  | down _ notUnc _ _ => exact absurd ht notUnc

/-- Add the current root of `r` unless it is already present. -/
def pushRoot (uf acc : Array Nat) (r : Nat) : Array Nat :=
  if acc.contains (ufFind uf r) then acc else acc.push (ufFind uf r)

/-- Add the current roots of one child's representatives. -/
def addReps (uf : Array Nat) (reps : Array (Array Nat)) (acc : Array Nat) (c : Nat) : Array Nat :=
  reps[c]!.foldl (pushRoot uf) acc

theorem addReps_eq (uf : Array Nat) (reps : Array (Array Nat)) (acc : Array Nat) (c : Nat) :
    addReps uf reps acc c = reps[c]!.toList.foldl (pushRoot uf) acc := by
  unfold addReps
  rw [Array.foldl_toList]

theorem childRoots_eq (uf : Array Nat) (reps : Array (Array Nat)) (children : Array Nat) :
    childRoots uf reps children = children.toList.foldl (addReps uf reps) #[] := by
  rw [Array.foldl_toList]
  rfl

theorem pushFold_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) :
    ∀ (rs : List Nat) (acc : Array Nat), (∀ ρ ∈ acc.toList, ρ < n ∧ ufFind uf ρ = ρ) →
      (∀ r ∈ rs, r < n) →
      (∀ ρ ∈ acc.toList, ρ ∈ (rs.foldl (pushRoot uf) acc).toList) ∧
        (∀ r ∈ rs, ufFind uf r ∈ (rs.foldl (pushRoot uf) acc).toList) ∧
        ∀ ρ ∈ (rs.foldl (pushRoot uf) acc).toList, ρ < n ∧ ufFind uf ρ = ρ := by
  intro rs
  induction rs with
  | nil => intro acc good _; exact ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil, good⟩
  | cons r rest ih =>
    intro acc good bound
    simp only [List.foldl_cons]
    have rLt := bound r List.mem_cons_self
    have step : ∀ ρ ∈ (pushRoot uf acc r).toList, ρ < n ∧ ufFind uf ρ = ρ := by
      intro ρ member
      unfold pushRoot at member
      split at member
      · exact good ρ member
      · rw [Array.toList_push, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact good ρ old
        · exact ⟨ufFind_lt wf rLt, ufFind_idem wf rLt⟩
    have added : ufFind uf r ∈ (pushRoot uf acc r).toList := by
      unfold pushRoot
      split
      · rename_i inside
        exact Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp inside)
      · simp
    have kept : ∀ ρ ∈ acc.toList, ρ ∈ (pushRoot uf acc r).toList := by
      intro ρ member
      unfold pushRoot
      split
      · exact member
      · simp [member]
    obtain ⟨keeps, found, good'⟩ := ih _ step (fun r' h => bound r' (List.mem_cons_of_mem _ h))
    refine ⟨fun ρ member => keeps ρ (kept ρ member), ?_, good'⟩
    intro r' member
    rcases List.mem_cons.mp member with rfl | later
    · exact keeps _ added
    · exact found r' later

theorem addFold_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) (reps : Array (Array Nat)) :
    ∀ (cs : List Nat) (acc : Array Nat), (∀ ρ ∈ acc.toList, ρ < n ∧ ufFind uf ρ = ρ) →
      (∀ c ∈ cs, ∀ r ∈ reps[c]!.toList, r < n) →
      (∀ c ∈ cs, ∀ r ∈ reps[c]!.toList, ufFind uf r ∈ (cs.foldl (addReps uf reps) acc).toList) ∧
        ∀ ρ ∈ (cs.foldl (addReps uf reps) acc).toList, ρ < n ∧ ufFind uf ρ = ρ := by
  intro cs
  induction cs with
  | nil => intro acc good _; exact ⟨fun _ h => absurd h List.not_mem_nil, good⟩
  | cons c rest ih =>
    intro acc good bound
    simp only [List.foldl_cons]
    obtain ⟨_, found, good'⟩ := pushFold_spec wf reps[c]!.toList acc good (bound c List.mem_cons_self)
    rw [← addReps_eq] at found good'
    have persist : ∀ (cs' : List Nat) (acc' : Array Nat) (ρ : Nat), ρ ∈ acc'.toList →
        ρ ∈ (cs'.foldl (addReps uf reps) acc').toList := by
      intro cs'
      induction cs' with
      | nil => intro _ _ h; exact h
      | cons d more ihd =>
        intro acc' ρ h
        simp only [List.foldl_cons]
        apply ihd
        have keepAll : ∀ (rs : List Nat) (a : Array Nat), ρ ∈ a.toList →
            ρ ∈ (rs.foldl (pushRoot uf) a).toList := by
          intro rs
          induction rs with
          | nil => intro _ h; exact h
          | cons r more ihr =>
            intro a h
            simp only [List.foldl_cons]
            apply ihr
            unfold pushRoot
            split
            · exact h
            · simp [h]
        rw [addReps_eq]
        exact keepAll _ _ h
    obtain ⟨found', good''⟩ := ih (addReps uf reps acc c) good'
      (fun c' h => bound c' (List.mem_cons_of_mem _ h))
    refine ⟨?_, good''⟩
    intro c' member r rm
    rcases List.mem_cons.mp member with rfl | later
    · exact persist rest _ _ (found r rm)
    · exact found' c' later r rm

theorem childRoots_spec {n : Nat} {uf : Array Nat} (wf : UfWF n uf) (reps : Array (Array Nat))
    (children : Array Nat) (bound : ∀ c ∈ children.toList, ∀ r ∈ reps[c]!.toList, r < n) :
    (∀ c ∈ children.toList, ∀ r ∈ reps[c]!.toList, ufFind uf r ∈ (childRoots uf reps children).toList) ∧
      ∀ ρ ∈ (childRoots uf reps children).toList, ρ < n ∧ ufFind uf ρ = ρ := by
  rw [childRoots_eq]
  exact addFold_spec wf reps children.toList #[] (fun _ h => by simp at h) bound

theorem componentStep_inv {dag : Dag} (hcp : CP dag.nodes) (cls : Array UClass) {k : Nat}
    (hk : k < dag.size) {uf : Array Nat} {reps : Array (Array Nat)}
    (inv : PassInv dag cls k uf reps) :
    PassInv dag cls (k + 1) (componentStep dag cls (uf, reps) k).1
      (componentStep dag cls (uf, reps) k).2 := by
  have childLt : ∀ c ∈ (dag.node k).children.toList, c < k := by
    intro c member
    exact hcp k hk c (by rw [← dag_node_eq hk]; exact Array.mem_toList_iff.mp member)
  unfold componentStep
  by_cases stored : (cls[k]! == .certainStored) = true
  · rw [ite_eq_left stored]
    have isStored := uclass_eq_of_beq stored
    refine ⟨inv.wf, inv.repsSize, inv.repsBound, ?_, ?_⟩
    · intro u hu notStored z low
      by_cases huk : u = k
      · subst huk; exact absurd isStored notStored
      · exact inv.covers u (by omega) notStored z low
    · intro y hy unc c member z low
      by_cases hyk : y = k
      · subst hyk; rw [isStored] at unc; cases unc
      · exact inv.joined y (by omega) unc c member z low
  · rw [ite_eq_right stored]
    have notStored : cls[k]! ≠ .certainStored := fun h => stored (by rw [h]; rfl)
    dsimp only
    have rootsBound : ∀ c ∈ (dag.node k).children.toList, ∀ r ∈ reps[c]!.toList, r < dag.size :=
      fun c member r rm => inv.repsBound c (by have := childLt c member; omega) r rm
    obtain ⟨found, roots⟩ := childRoots_spec inv.wf reps (dag.node k).children rootsBound
    -- Every uncertain term below a child is joined with some found root.
    have reached : ∀ c ∈ (dag.node k).children, ∀ z, Low dag cls c z →
        ∃ ρ ∈ (childRoots uf reps (dag.node k).children).toList, ufFind uf ρ = ufFind uf z := by
      intro c member z low
      have cLt := childLt c (Array.mem_toList_iff.mpr member)
      have cNotStored : cls[c]! ≠ .certainStored := by
        cases low with
        | self h => rw [h]; intro h'; cases h'
        | down h _ _ _ => exact h
      obtain ⟨r, rm, same⟩ := inv.covers c cLt cNotStored z low
      have rLt := inv.repsBound c (by omega) r rm
      refine ⟨ufFind uf r, found c (Array.mem_toList_iff.mpr member) r rm, ?_⟩
      rw [ufFind_idem inv.wf rLt, same]
    have keepSize : (reps.set! k #[k]).size = dag.size := by rw [size_setBang, inv.repsSize]
    by_cases uncertain : (cls[k]! == .uncertain) = true
    · rw [ite_eq_left uncertain]
      have isUnc := uclass_eq_of_beq uncertain
      have asList : (childRoots uf reps (dag.node k).children).foldl (fun uf r => ufUnion uf k r) uf =
          unionAll k uf (childRoots uf reps (dag.node k).children).toList := by
        unfold unionAll
        rw [Array.foldl_toList]
      rw [asList]
      obtain ⟨wf', joinedK, mono⟩ := unionAll_spec hk
        (childRoots uf reps (dag.node k).children).toList uf inv.wf
        (fun ρ member => (roots ρ member).1)
      have zLt : ∀ c ∈ (dag.node k).children, ∀ z, Low dag cls c z → z < dag.size := by
        intro c member z low
        have cLt := childLt c (Array.mem_toList_iff.mpr member)
        have := low_le hcp low (by omega)
        omega
      refine ⟨wf', keepSize, ?_, ?_, ?_⟩
      · intro u hu r rm
        rw [setBang_getElem!] at rm
        split at rm
        · simp at rm; omega
        · exact inv.repsBound u hu r rm
      · intro u hu uNotStored z low
        rw [setBang_getElem!]
        by_cases huk : u = k
        · rw [ite_eq_left ⟨huk.symm, by rw [inv.repsSize]; exact hk⟩]
          have uUnc : cls[u]! = .uncertain := by rw [huk]; exact isUnc
          have zEq : z = u := low_of_uncertain low uUnc
          refine ⟨k, by simp, ?_⟩
          rw [zEq, huk]
        · rw [ite_eq_right (fun h => huk h.1.symm)]
          obtain ⟨r, rm, same⟩ := inv.covers u (by omega) uNotStored z low
          have uLt : u < dag.size := by omega
          exact ⟨r, rm, mono r z (inv.repsBound u uLt r rm) (Nat.lt_of_le_of_lt (low_le hcp low uLt) uLt) same⟩
      · intro y hy unc c member z low
        have zBound := zLt
        by_cases hyk : y = k
        · subst hyk
          obtain ⟨ρ, ρm, same⟩ := reached c member z low
          have ρLt := (roots ρ ρm).1
          rw [joinedK ρ ρm]
          exact mono ρ z ρLt (zLt c member z low) same
        · have yLt : y < dag.size := by omega
          have cLt : c < dag.size := by
            have := hcp y yLt c (by rw [← dag_node_eq yLt]; exact member)
            omega
          exact mono y z yLt (Nat.lt_of_le_of_lt (low_le hcp low cLt) cLt)
            (inv.joined y (by omega) unc c member z low)
    · rw [ite_eq_right uncertain]
      have notUnc : cls[k]! ≠ .uncertain := fun h => uncertain (by rw [h]; rfl)
      refine ⟨inv.wf, by rw [size_setBang, inv.repsSize], ?_, ?_, ?_⟩
      · intro u hu r rm
        rw [setBang_getElem!] at rm
        split at rm
        · exact (roots r rm).1
        · exact inv.repsBound u hu r rm
      · intro u hu uNotStored z low
        rw [setBang_getElem!]
        by_cases huk : u = k
        · subst huk
          rw [ite_eq_left ⟨rfl, by rw [inv.repsSize]; exact hk⟩]
          cases low with
          | self h => exact absurd h notUnc
          | down _ _ member below => exact reached _ member z below
        · rw [ite_eq_right (fun h => huk h.1.symm)]
          exact inv.covers u (by omega) uNotStored z low
      · intro y hy unc c member z low
        by_cases hyk : y = k
        · subst hyk; exact absurd unc notUnc
        · exact inv.joined y (by omega) unc c member z low

theorem componentPass_inv {dag : Dag} (hcp : CP dag.nodes) (cls : Array UClass) :
    ∀ k, k ≤ dag.size →
      PassInv dag cls k
        ((List.range k).foldl (componentStep dag cls) (Array.range dag.size, Array.replicate dag.size #[])).1
        ((List.range k).foldl (componentStep dag cls) (Array.range dag.size, Array.replicate dag.size #[])).2 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨⟨by simp, fun x hx => by simp [hx]⟩, by simp, ?_, ?_, ?_⟩
    · intro u hu r rm
      simp [hu] at rm
    · intro u hu; omega
    · intro y hy; omega
  | succ k ih =>
    intro hk
    rw [foldl_range_succ]
    exact componentStep_inv hcp cls (by omega) (ih (by omega))

/-- After the pass, an uncertain term shares its root with every uncertain
term reachable below it through non-certain-stored terms. -/
theorem componentPass_reach {dag : Dag} (hwf : DagWF dag) {cls : Array UClass}
    {O : Nat → Bool} (isOpaque : ∀ u, u < dag.size → (O u = true ↔ cls[u]! = .certainStored))
    (uf : Array Nat) (reps : Array (Array Nat)) (inv : PassInv dag cls dag.size uf reps) :
    ∀ y, y < dag.size → cls[y]! ≠ .certainStored → ∀ v, cls[v]! = .uncertain →
      NReach (Prep.ofDag dag) O y v → ∃ z, Low dag cls y z ∧ ufFind uf z = ufFind uf v := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy notStored v unc reach
    rcases reach.head with same | ⟨k, hk, (⟨hO, same⟩ | ⟨hO, rest⟩)⟩
    · rw [same] at unc ⊢
      exact ⟨y, .self unc, rfl⟩
    · simp only [ofDag_dag] at hk hO same
      have cLt := hwf.childAt_lt hy hk
      have := (isOpaque _ (by omega)).mp hO
      rw [same, this] at unc
      cases unc
    · simp only [ofDag_dag] at hk hO rest
      have cLt := hwf.childAt_lt hy hk
      have cNotStored : cls[(dag.node y).child k]! ≠ .certainStored := by
        intro h; rw [(isOpaque _ (by omega)).mpr h] at hO; cases hO
      have arity := hwf.arity y hy
      rw [← dag_node_eq hy] at arity
      have member : (dag.node y).child k ∈ (dag.node y).children := by
        rw [child_eq_getElem _ k (by omega)]
        exact Array.getElem_mem _
      obtain ⟨z, low, same⟩ := ih _ cLt (by omega) cNotStored v unc rest
      by_cases yUnc : cls[y]! = .uncertain
      · refine ⟨y, .self yUnc, ?_⟩
        rw [← same]
        exact inv.joined y hy yUnc _ member z low
      · exact ⟨z, .down notStored yUnc member low, same⟩

/-! ## Grouping by root -/

section Group

/-- The grouping state after the terms below `k`. -/
structure GroupInv (n : Nat) (cls : Array UClass) (root : Nat → Nat) (k : Nat)
    (slot : Array (Option Nat)) (comps : Array (Array Nat)) : Prop where
  slotSize : slot.size = n
  members : ∀ i, i < comps.size → comps[i]!.toList ≠ [] ∧ comps[i]!.toList.Pairwise (· < ·) ∧
    ∀ t ∈ comps[i]!.toList, t < k ∧ cls[t]! = .uncertain ∧ slot[root t]! = some i
  slots : ∀ (r i : Nat), slot[r]! = some i → i < comps.size
  listed : ∀ t, t < k → cls[t]! = .uncertain → ∃ i, i < comps.size ∧ t ∈ comps[i]!.toList

end Group

theorem modify_getElem! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (f : α → α) :
    (a.modify i f)[j]! = if i = j ∧ i < a.size then f a[j]! else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.modify i f) j (by simpa using hj), Array.getElem_modify,
      getElem!_pos a j hj]
    by_cases hij : i = j
    · subst hij; simp [hj]
    · simp [hij]
  · rw [getElem!_neg (a.modify i f) j (by simpa using hj), getElem!_neg a j hj]
    split
    · rename_i h; exact absurd (h.1 ▸ h.2) hj
    · rfl

theorem push_getElem!_lt {α : Type} [Inhabited α] (a : Array α) (v : α) {j : Nat} (hj : j < a.size) :
    (a.push v)[j]! = a[j]! := by
  rw [getElem!_pos (a.push v) j (by simp; omega), Array.getElem_push_lt hj, getElem!_pos a j hj]

theorem push_getElem!_size {α : Type} [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by simp)]
  simp

theorem groupStep_inv {n : Nat} {cls : Array UClass} {root : Nat → Nat}
    (rootLt : ∀ t, t < n → cls[t]! = .uncertain → root t < n) {k : Nat} (hk : k < n)
    {slot : Array (Option Nat)} {comps : Array (Array Nat)} (inv : GroupInv n cls root k slot comps) :
    GroupInv n cls root (k + 1) (groupStep cls root (slot, comps) k).1
      (groupStep cls root (slot, comps) k).2 := by
  unfold groupStep
  by_cases unc : (cls[k]! == .uncertain) = true
  · rw [ite_eq_left unc]
    have isUnc := uclass_eq_of_beq unc
    have ρLt := rootLt k hk isUnc
    dsimp only
    cases found : slot[root k]! with
    | some i =>
      dsimp only
      have iLt := inv.slots _ _ found
      refine ⟨inv.slotSize, ?_, ?_, ?_⟩
      · intro j hj
        rw [Array.size_modify] at hj
        rw [modify_getElem!]
        by_cases hij : i = j
        · subst hij
          rw [ite_eq_left ⟨rfl, iLt⟩]
          try dsimp only
          obtain ⟨nonempty, increasing, elements⟩ := inv.members i iLt
          refine ⟨by simp, ?_, ?_⟩
          · rw [Array.toList_push]
            refine List.pairwise_append.mpr ⟨increasing, List.pairwise_singleton _ _, ?_⟩
            intro a am b bm
            rw [List.mem_singleton] at bm
            subst bm
            exact (elements a am).1
          · intro t ht
            rw [Array.toList_push, List.mem_append, List.mem_singleton] at ht
            rcases ht with old | rfl
            · obtain ⟨tLt, tUnc, tSlot⟩ := elements t old
              exact ⟨by omega, tUnc, tSlot⟩
            · exact ⟨by omega, isUnc, found⟩
        · rw [ite_eq_right (fun h => hij h.1)]
          obtain ⟨nonempty, increasing, elements⟩ := inv.members j hj
          exact ⟨nonempty, increasing, fun t ht =>
            let e := elements t ht; ⟨by omega, e.2.1, e.2.2⟩⟩
      · intro r i' h
        rw [Array.size_modify]
        exact inv.slots r i' h
      · intro t ht tUnc
        by_cases htk : t = k
        · subst htk
          refine ⟨i, by rw [Array.size_modify]; exact iLt, ?_⟩
          rw [modify_getElem!, ite_eq_left ⟨rfl, iLt⟩]
          simp
        · obtain ⟨j, jLt, member⟩ := inv.listed t (by omega) tUnc
          refine ⟨j, by rw [Array.size_modify]; exact jLt, ?_⟩
          rw [modify_getElem!]
          split
          · simp only [Array.toList_push]
            exact List.mem_append_left _ member
          · exact member
    | none =>
      dsimp only
      have fresh : ∀ t j, j < comps.size → t ∈ comps[j]!.toList → root t ≠ root k := by
        intro t j hj ht same
        have := ((inv.members j hj).2.2 t ht).2.2
        rw [same, found] at this
        cases this
      have slotInside : root k < slot.size := by rw [inv.slotSize]; exact ρLt
      refine ⟨by rw [size_setBang, inv.slotSize], ?_, ?_, ?_⟩
      · intro j hj
        simp only [Array.size_push] at hj
        by_cases last : j = comps.size
        · subst last
          rw [push_getElem!_size]
          refine ⟨by simp, by simp, ?_⟩
          intro t ht
          simp at ht
          subst ht
          refine ⟨by omega, isUnc, ?_⟩
          rw [setBang_getElem!, ite_eq_left ⟨rfl, slotInside⟩]
        · have jLt : j < comps.size := by omega
          rw [push_getElem!_lt _ _ jLt]
          obtain ⟨nonempty, increasing, elements⟩ := inv.members j jLt
          refine ⟨nonempty, increasing, fun t ht => ?_⟩
          obtain ⟨tLt, tUnc, tSlot⟩ := elements t ht
          refine ⟨by omega, tUnc, ?_⟩
          rw [setBang_getElem!, ite_eq_right (fun h => fresh t j jLt ht h.1.symm)]
          exact tSlot
      · intro r i' h
        rw [setBang_getElem!] at h
        simp only [Array.size_push]
        split at h
        · cases h; omega
        · have := inv.slots r i' h; omega
      · intro t ht tUnc
        by_cases htk : t = k
        · subst htk
          refine ⟨comps.size, by simp, ?_⟩
          rw [push_getElem!_size]
          simp
        · obtain ⟨j, jLt, member⟩ := inv.listed t (by omega) tUnc
          refine ⟨j, by simp; omega, ?_⟩
          rw [push_getElem!_lt _ _ jLt]
          exact member
  · rw [ite_eq_right unc]
    have notUnc : cls[k]! ≠ .uncertain := fun h => unc (by rw [h]; rfl)
    refine ⟨inv.slotSize, ?_, inv.slots, ?_⟩
    · intro i hi
      obtain ⟨nonempty, increasing, elements⟩ := inv.members i hi
      exact ⟨nonempty, increasing, fun t ht => let e := elements t ht; ⟨by omega, e.2.1, e.2.2⟩⟩
    · intro t ht tUnc
      by_cases htk : t = k
      · subst htk; exact absurd tUnc notUnc
      · exact inv.listed t (by omega) tUnc

theorem groupByRoot_inv {n : Nat} {cls : Array UClass} {root : Nat → Nat}
    (rootLt : ∀ t, t < n → cls[t]! = .uncertain → root t < n) :
    ∀ k, k ≤ n →
      GroupInv n cls root k ((List.range k).foldl (groupStep cls root) (Array.replicate n none, #[])).1
        ((List.range k).foldl (groupStep cls root) (Array.replicate n none, #[])).2 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨by simp, fun i hi => by simp at hi, ?_, fun t ht => by omega⟩
    intro r i h
    by_cases hr : r < n
    · simp [hr] at h
    · simp [hr] at h
  | succ k ih =>
    intro hk
    rw [foldl_range_succ]
    exact groupStep_inv rootLt (by omega) (ih (by omega))

/-! ## Labels -/

theorem componentLabels_spec {n : Nat} {comps : Array (Array Nat)}
    (disjoint : ∀ i j t, i < comps.size → j < comps.size → t ∈ comps[i]!.toList →
      t ∈ comps[j]!.toList → i = j) :
    ∀ t, t < n → ∀ i, (componentLabels n comps)[t]! = some i ↔ i < comps.size ∧ t ∈ comps[i]!.toList := by
  -- Labels after the first `m` components.
  have prefixLabels : ∀ m, m ≤ comps.size → ∀ t, t < n → ∀ i,
      ((List.range m).foldl (fun acc i => comps[i]!.foldl (fun acc t => acc.set! t (some i)) acc)
          (Array.replicate n none))[t]! = some i ↔ i < m ∧ t ∈ comps[i]!.toList := by
    intro m
    induction m with
    | zero =>
      intro _ t ht i
      simp [getElem!_def, ht]
    | succ m ih =>
      intro hm t ht i
      rw [foldl_range_succ]
      have sizeKeep : ∀ m', ((List.range m').foldl
          (fun acc i => comps[i]!.foldl (fun acc t => acc.set! t (some i)) acc)
          (Array.replicate n none)).size = n := by
        intro m'
        induction m' with
        | zero => simp
        | succ m' ihm =>
          rw [foldl_range_succ, ← Array.foldl_toList, foldl_setBang_const_size, ihm]
      rw [← Array.foldl_toList, foldl_setBang_const, sizeKeep]
      by_cases inside : t ∈ comps[m]!.toList
      · rw [ite_eq_left ⟨inside, ht⟩]
        constructor
        · intro h; cases h; exact ⟨by omega, inside⟩
        · rintro ⟨iLt, member⟩
          have := disjoint i m t (by omega) (by omega) member inside
          rw [this]
      · rw [ite_eq_right (fun h => inside h.1), ih (by omega) t ht i]
        constructor
        · rintro ⟨iLt, member⟩; exact ⟨by omega, member⟩
        · rintro ⟨iLt, member⟩
          refine ⟨?_, member⟩
          by_cases him : i = m
          · subst him; exact absurd member inside
          · omega
  intro t ht i
  unfold componentLabels
  rw [← Array.foldl_toList, Array.toList_range]
  exact prefixLabels comps.size (Nat.le_refl _) t ht i

/-! ## Label separation -/

/-- `x` records no label or exactly `ℓ`. -/
def Within (x : Option (Option Nat)) (ℓ : Nat) : Prop := x = none ∨ x = some (some ℓ)

theorem within_join {a b : Option (Option Nat)} {ℓ : Nat} (ha : Within a ℓ) (hb : Within b ℓ) :
    Within (labelJoin a b) ℓ := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [labelJoin, Within]

theorem within_foldl {α : Type} (g : α → Option (Option Nat)) {ℓ : Nat} :
    ∀ (l : List α) (init : Option (Option Nat)), Within init ℓ → (∀ a ∈ l, Within (g a) ℓ) →
      Within (l.foldl (fun v a => labelJoin v (g a)) init) ℓ := by
  intro l
  induction l with
  | nil => intro init h _; exact h
  | cons x xs ih =>
    intro init h hg
    simp only [List.foldl_cons]
    exact ih _ (within_join h (hg x List.mem_cons_self)) (fun a ha => hg a (List.mem_cons_of_mem _ ha))

theorem labeled_foldl {α : Type} (g : α → Option (Option Nat)) {ℓ : Nat} :
    ∀ (l : List α), (∀ a ∈ l, Within (g a) ℓ) →
      l.foldl (fun v a => labelJoin v (g a)) (some (some ℓ)) = some (some ℓ) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hg
    simp only [List.foldl_cons]
    rcases hg x List.mem_cons_self with h | h
    · rw [h]; simp only [labelJoin]; exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    · rw [h]; simp only [labelJoin, ↓reduceIte]; exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))

/-- A term from which every reachable label is `ℓ` records at most `ℓ`. -/
theorem reachLabels_within {dag : Dag} (hwf : DagWF dag) (opq : Nat → Bool)
    (lab : Nat → Option Nat) (ℓ : Nat) :
    ∀ y, y < dag.size → (∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ', lab v = some ℓ' → ℓ' = ℓ) →
      Within (reachLabels dag opq lab)[y]! ℓ := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy only
    rw [reachLabels_spec hwf opq lab hy]
    unfold labelRow
    rw [← Array.foldl_toList]
    apply within_foldl
    · cases hl : lab y with
      | none => left; rfl
      | some ℓ' => right; rw [only y .refl ℓ' hl]; rfl
    · intro c member
      have hc := hwf.child_lt hy (Array.mem_toList_iff.mp member)
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      have arity := hwf.arity y hy
      rw [← dag_node_eq hy] at arity
      have kArity : k < ((Prep.ofDag dag).dag.node y).head.arity := by
        simp only [ofDag_dag]; omega
      have childEq : ((Prep.ofDag dag).dag.node y).child k = (dag.node y).children[k] := by
        simp only [ofDag_dag]; exact child_eq_getElem _ k hk
      have edge : NReach (Prep.ofDag dag) opq y (dag.node y).children[k] := by
        rw [← childEq]; exact NReach.edge kArity
      split
      · cases hlc : lab (dag.node y).children[k] with
        | none => left; rfl
        | some ℓ' => right; rw [only _ edge ℓ' hlc]; rfl
      · rename_i notOpq
        apply ih _ hc (by omega)
        intro v reach ℓ' hl
        exact only v (NReach.of_child (by simpa using notOpq) ⟨k, kArity, childEq⟩ reach) ℓ' hl

theorem reachLabels_labeled {dag : Dag} (hwf : DagWF dag) (opq : Nat → Bool)
    (lab : Nat → Option Nat) {ℓ y : Nat} (hy : y < dag.size) (own : lab y = some ℓ)
    (only : ∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ', lab v = some ℓ' → ℓ' = ℓ) :
    (reachLabels dag opq lab)[y]! = some (some ℓ) := by
  rw [reachLabels_spec hwf opq lab hy]
  unfold labelRow
  rw [← Array.foldl_toList, own]
  apply labeled_foldl
  intro c member
  have hc := hwf.child_lt hy (Array.mem_toList_iff.mp member)
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  have arity := hwf.arity y hy
  rw [← dag_node_eq hy] at arity
  have kArity : k < ((Prep.ofDag dag).dag.node y).head.arity := by
    simp only [ofDag_dag]; omega
  have childEq : ((Prep.ofDag dag).dag.node y).child k = (dag.node y).children[k] := by
    simp only [ofDag_dag]; exact child_eq_getElem _ k hk
  have edge : NReach (Prep.ofDag dag) opq y (dag.node y).children[k] := by
    rw [← childEq]; exact NReach.edge kArity
  split
  · cases hlc : lab (dag.node y).children[k] with
    | none => left; rfl
    | some ℓ' => right; rw [only _ edge ℓ' hlc]; rfl
  · rename_i notOpq
    apply reachLabels_within hwf opq lab ℓ _ (by omega)
    intro v reach ℓ' hl
    exact only v (NReach.of_child (by simpa using notOpq) ⟨k, kArity, childEq⟩ reach) ℓ' hl

/-! ## The component check -/

/-- `componentsChecked` accepts the actual uncertain components of every
well-formed DAG, for any classification whose certain-stored terms are the
isOpaque ones. -/
theorem componentsChecked_ok {dag : Dag} (hwf : DagWF dag) (cls : Array UClass) (opaq : Array Bool)
    (isOpaque : ∀ u, u < dag.size → (opaq[u]! = true ↔ cls[u]! = .certainStored)) :
    componentsChecked dag cls opaq (uncertainComponents dag cls)
      (componentLabels dag.size (uncertainComponents dag cls)) = true := by
  have pass := componentPass_inv hwf.precede cls dag.size (Nat.le_refl _)
  generalize hst : (List.range dag.size).foldl (componentStep dag cls)
    (Array.range dag.size, Array.replicate dag.size #[]) = st at pass
  have compsEq : uncertainComponents dag cls = groupByRoot dag.size cls (ufFind st.1) := by
    unfold uncertainComponents
    dsimp only
    rw [hst]
  have rootLt : ∀ t, t < dag.size → cls[t]! = .uncertain → ufFind st.1 t < dag.size :=
    fun t ht _ => ufFind_lt pass.wf ht
  have group := groupByRoot_inv (cls := cls) (root := ufFind st.1) rootLt dag.size (Nat.le_refl _)
  generalize hg : (List.range dag.size).foldl (groupStep cls (ufFind st.1))
    (Array.replicate dag.size none, #[]) = g at group
  have compsEq' : uncertainComponents dag cls = g.2 := by
    rw [compsEq]; unfold groupByRoot; rw [hg]
  rw [compsEq']
  -- Facts about the groups.
  have disjoint : ∀ (i j t : Nat), i < g.2.size → j < g.2.size → t ∈ g.2[i]!.toList →
      t ∈ g.2[j]!.toList → i = j := by
    intro i j t hi hj ti tj
    have a := ((group.members i hi).2.2 t ti).2.2
    have b := ((group.members j hj).2.2 t tj).2.2
    rw [a] at b
    exact Option.some.inj b
  have labels := componentLabels_spec (n := dag.size) disjoint
  have elem : ∀ (i j : Nat), j < g.2[i]!.size → g.2[i]![j]! ∈ g.2[i]!.toList := by
    intro i j hj
    rw [getElem!_pos g.2[i]! j hj]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hj)
  have incr : ∀ (i j : Nat), i < g.2.size → j + 1 < g.2[i]!.size → g.2[i]![j]! < g.2[i]![j + 1]! := by
    intro i j hi hj
    have pw := List.pairwise_iff_getElem.mp (group.members i hi).2.1 j (j + 1)
      (by simp; omega) (by simpa using hj) (by omega)
    rw [getElem!_pos g.2[i]! j (by omega), getElem!_pos g.2[i]! (j + 1) hj]
    simpa using pw
  unfold componentsChecked
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    simp only [Array.size_range] at hi
    rw [Array.getElem_range, List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    obtain ⟨tLt, tUnc, _⟩ := (group.members i hi).2.2 _ (elem i j hj)
    have lab := (labels _ tLt i).mpr ⟨hi, elem i j hj⟩
    try dsimp only
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨decide_eq_true tLt, by rw [tUnc]; exact uclass_beq_self _⟩,
      by rw [lab]; exact beq_self_eq_true _⟩, decide_eq_true (fun h => incr i j hi h)⟩
  · rw [Array.all_eq_true]
    intro t ht
    simp only [Array.size_range] at ht
    rw [Array.getElem_range]
    by_cases tUnc : cls[t]! = .uncertain
    · obtain ⟨i, iLt, member⟩ := group.listed t ht tUnc
      have lab := (labels t ht i).mpr ⟨iLt, member⟩
      rw [lab]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨iLt, Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp member)⟩
    · have differ : (cls[t]! == .uncertain) = false := by
        cases h : (cls[t]! == .uncertain)
        · rfl
        · exact absurd (uclass_eq_of_beq h) tUnc
      simp [bne, differ]
  · unfold labelsSeparated
    rw [Array.all_eq_true']
    intro y member
    rw [Array.mem_filter, Array.mem_range] at member
    obtain ⟨yLt, yUnc'⟩ := member
    have yUnc := uclass_eq_of_beq yUnc'
    obtain ⟨i, iLt, yIn⟩ := group.listed y yLt yUnc
    have lab := (labels y yLt i).mpr ⟨iLt, yIn⟩
    dsimp only
    rw [lab]
    simp only [beq_iff_eq]
    apply reachLabels_labeled hwf _ _ yLt lab
    intro v reach ℓ' hl
    have vLe := NReach.le_of_wf hwf reach yLt
    have vLt : v < dag.size := by omega
    obtain ⟨jLt, vIn⟩ := (labels v vLt ℓ').mp hl
    have vUnc := ((group.members ℓ' jLt).2.2 v vIn).2.1
    have yNotStored : cls[y]! ≠ .certainStored := by rw [yUnc]; intro h'; cases h'
    obtain ⟨z, low, same⟩ := componentPass_reach hwf (O := (opaq[·]!)) isOpaque st.1 st.2 pass
      y yLt yNotStored v vUnc reach
    rw [low_of_uncertain low yUnc] at same
    have ySlot := ((group.members i iLt).2.2 y yIn).2.2
    have vSlot := ((group.members ℓ' jLt).2.2 v vIn).2.2
    rw [same, vSlot] at ySlot
    exact Option.some.inj ySlot

end Ix.Sharing.Verify.Components

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel

/-- The family stage's components pass the partition check on every
well-formed DAG. -/
theorem stage_componentsChecked (width : Nat) (ex : Expanded) (wf : DagWF ex.dag) :
    componentsChecked ex.dag (stg width ex).cls (stg width ex).opaq (stg width ex).comps
      (componentLabels ex.dag.size (stg width ex).comps) = true := by
  have comps : (stg width ex).comps = uncertainComponents ex.dag (stg width ex).cls := rfl
  rw [comps]
  apply Ix.Sharing.Verify.Components.componentsChecked_ok wf
  intro u hu
  rw [stage_opaq, decide_eq_true_iff, initial_cs_mem, ← (stage_cls_theta width ex).1]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Verify.Components.componentsChecked_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.stage_componentsChecked [propext, Classical.choice, Quot.sound]
