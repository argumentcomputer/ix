import IxCC.Own.Rc.Heap

set_option autoImplicit false

namespace IxCC.Own.Rc

/-! ## Exact root and field accounting for final release

The plain counted fragment has no references to static locations. Static and
immediate operations remain no-ops, but their ownership policy is outside this
numeric invariant. `Balance` is a component of `Holds`, not the whole invariant:
well-formed bodies, acyclicity and positive live counts still need to accompany
it in the checker refinement. -/

def refsIn (l : Nat) : List RVal → Nat
  | [] => 0
  | v :: vs => (if v = .loc l then 1 else 0) + refsIn l vs

def fieldRefs (l : Nat) : Cell → Nat
  | .live _ _ b => refsIn l b.fields
  | .dead => 0

def total (f : Cell → Nat) : List Cell → Nat
  | [] => 0
  | c :: cs => f c + total f cs

def edgeCount (H : Heap) (l : Nat) : Nat := total (fieldRefs l) H.cells.toList

def Balance (H : Heap) (external : Nat → Nat) (pending : List RVal) : Prop :=
  ∀ l, dynCount H l = external l + refsIn l pending + edgeCount H l

theorem refsIn_append (l : Nat) (xs ys : List RVal) :
    refsIn l (xs ++ ys) = refsIn l xs + refsIn l ys := by
  induction xs with
  | nil => simp [refsIn]
  | cons x xs ih => simp [refsIn, ih, Nat.add_assoc]

theorem total_set {xs : List Cell} {i : Nat} {old : Cell} (f : Cell → Nat)
    (h : xs[i]? = some old) (c : Cell) :
    total f (xs.set i c) + f old = total f xs + f c := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst old; simp [total, Nat.add_comm, Nat.add_left_comm]
    | succ i =>
      have hi : xs[i]? = some old := by simpa using h
      have he := ih hi
      simp only [List.set_cons_succ, total]
      omega

/-- Removing a live parent transfers exactly its outgoing references out of
the live heap graph. Natural subtraction is avoided so no underflow is hidden. -/
theorem edgeCount_free {H : Heap} {l rc : Nat} {m : OMode} {b : Body}
    (hc : H.cell? l = some (.live rc m b)) (k : Nat) :
    edgeCount (setCell H l .dead) k + refsIn k b.fields = edgeCount H k := by
  have he := total_set (fieldRefs k)
    (xs := H.cells.toList) (i := l) (old := .live rc m b)
    (by simpa [Heap.cell?] using hc) .dead
  simpa [edgeCount, setCell, Array.set!_eq_setIfInBounds,
    Array.toList_setIfInBounds, fieldRefs] using he

/-- One final release: remove the consumed parent before queuing its fields.
The exact count invariant ensures no other root or incoming edge still owns
that parent; in particular, it rules out a self-edge without an extra premise. -/
theorem balance_free {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l : Nat} {b : Body} (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: pending)) :
    Balance (setCell H l .dead) external (b.fields ++ pending) := by
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  intro k
  have he := edgeCount_free hc k
  have h := hb k
  simp only [refsIn] at h
  simp only [refsIn_append]
  by_cases hk : l = k
  · subst k
    have hn : dynCount H l = 1 := by simp [dynCount, hc]
    have hz : dynCount (setCell H l .dead) l = 0 := by
      simp [dynCount, setCell_cell H l .dead hl]
    simp only [ite_true] at h
    rw [hz]
    omega
  · have hn : dynCount (setCell H l .dead) k = dynCount H k := by
      simp [dynCount, setCell_cell H l .dead hl, hk]
    have hv : RVal.loc l ≠ RVal.loc k := by intro e; cases e; exact hk rfl
    simp only [if_neg hv] at h
    rw [hn]
    omega

/-- A single iterative release step. The returned list is the remaining
worklist, with a final parent's fields queued only after marking it dead.
Invalid dynamic counts and dead/missing locations reject explicitly. -/
def releaseOne (H : Heap) (v : RVal) (pending : List RVal) : Option (Heap × List RVal) :=
  match v with
  | .loc l => match H.cell? l with
    | some (.live 0 .dyn _) => none
    | some (.live 1 .dyn b) => some (setCell H l .dead, b.fields ++ pending)
    | some (.live (rc + 2) .dyn b) => some (setCell H l (.live (rc + 1) .dyn b), pending)
    | some (.live _ .static _) => some (H, pending)
    | _ => none
  | _ => some (H, pending)

theorem releaseOne_final {H : Heap} {l : Nat} {b : Body}
    (hc : H.cell? l = some (.live 1 .dyn b)) (pending : List RVal) :
    releaseOne H (.loc l) pending = some (setCell H l .dead, b.fields ++ pending) := by
  simp [releaseOne, hc]

/-- Final release preserves actual root/worklist/heap-edge counts, for the
same checked operation that will drive the complete release loop. -/
theorem releaseOne_final_balance {H : Heap} {external : Nat → Nat}
    {pending : List RVal} {l : Nat} {b : Body}
    (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: pending)) :
    ∃ H' pending', releaseOne H (.loc l) pending = some (H', pending') ∧
      Balance H' external pending' :=
  ⟨_, _, releaseOne_final hc pending, balance_free hc hb⟩

theorem edgeCount_set_count {H : Heap} {l rc rc' : Nat} {m : OMode} {b : Body}
    (hc : H.cell? l = some (.live rc m b)) (k : Nat) :
    edgeCount (setCell H l (.live rc' m b)) k = edgeCount H k := by
  have he := total_set (fieldRefs k)
    (xs := H.cells.toList) (i := l) (old := .live rc m b)
    (by simpa [Heap.cell?] using hc) (.live rc' m b)
  have he' : edgeCount (setCell H l (.live rc' m b)) k + refsIn k b.fields =
      edgeCount H k + refsIn k b.fields := by
    simpa [edgeCount, setCell, Array.set!_eq_setIfInBounds,
      Array.toList_setIfInBounds, fieldRefs] using he
  omega

theorem balance_shared {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l rc : Nat} {b : Body} (hc : H.cell? l = some (.live (rc + 2) .dyn b))
    (hb : Balance H external (.loc l :: pending)) :
    Balance (setCell H l (.live (rc + 1) .dyn b)) external pending := by
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  intro k
  have h := hb k
  rw [edgeCount_set_count hc k]
  by_cases hk : l = k
  · subst k
    have hn : dynCount H l = rc + 2 := by simp [dynCount, hc]
    have hn' : dynCount (setCell H l (.live (rc + 1) .dyn b)) l = rc + 1 := by
      simp [dynCount, setCell_cell H l _ hl l]
    simp [refsIn] at h
    rw [hn']
    omega
  · have hn : dynCount (setCell H l (.live (rc + 1) .dyn b)) k = dynCount H k := by
      simp [dynCount, setCell_cell H l _ hl k, hk]
    have hv : RVal.loc l ≠ RVal.loc k := by intro e; cases e; exact hk rfl
    simp [refsIn, hv] at h
    rw [hn]
    exact h

/-- A balanced pending reference always has a legal release step. This also
rules out pending references to missing, dead, zero-count or static locations
in this plain counted fragment. -/
theorem releaseOne_balance {H : Heap} {external : Nat → Nat} {v : RVal}
    {pending : List RVal} (hb : Balance H external (v :: pending)) :
    ∃ H' pending', releaseOne H v pending = some (H', pending') ∧
      Balance H' external pending' := by
  cases v with
  | loc l =>
    have hp := hb l
    simp [refsIn] at hp
    have hn : 0 < dynCount H l := by omega
    cases hc : H.cell? l with
    | none => simp [dynCount, hc] at hn
    | some c =>
      cases c with
      | dead => simp [dynCount, hc] at hn
      | live rc m b =>
        cases m with
        | static => simp [dynCount, hc] at hn
        | dyn =>
          cases rc with
          | zero => simp [dynCount, hc] at hn
          | succ rc =>
            cases rc with
            | zero => exact releaseOne_final_balance hc hb
            | succ rc =>
              refine ⟨_, _, ?_, balance_shared hc hb⟩
              simp [releaseOne, hc]
  | lit l =>
    refine ⟨H, pending, rfl, ?_⟩
    simpa [Balance, refsIn] using hb
  | ctor0 c =>
    refine ⟨H, pending, rfl, ?_⟩
    simpa [Balance, refsIn] using hb
  | erased =>
    refine ⟨H, pending, rfl, ?_⟩
    simpa [Balance, refsIn] using hb

def cellMass : Cell → Nat
  | .live rc .dyn _ => rc
  | _ => 0

def mass (H : Heap) : Nat := total cellMass H.cells.toList

theorem mass_set {H : Heap} {l : Nat} {old : Cell}
    (hc : H.cell? l = some old) (c : Cell) :
    mass (setCell H l c) + cellMass old = mass H + cellMass c := by
  have he := total_set cellMass (xs := H.cells.toList) (i := l) (old := old)
    (by simpa [Heap.cell?] using hc) c
  simpa [mass, setCell, Array.set!_eq_setIfInBounds,
    Array.toList_setIfInBounds] using he

theorem mass_free_lt {H : Heap} {l : Nat} {b : Body}
    (hc : H.cell? l = some (.live 1 .dyn b)) : mass (setCell H l .dead) < mass H := by
  have he := mass_set hc .dead
  simp only [cellMass] at he
  omega

theorem mass_dec_lt {H : Heap} {l rc : Nat} {b : Body}
    (hc : H.cell? l = some (.live (rc + 2) .dyn b)) :
    mass (setCell H l (.live (rc + 1) .dyn b)) < mass H := by
  have he := mass_set hc (.live (rc + 1) .dyn b)
  simp only [cellMass] at he
  omega

/-- Every successful step decreases dynamic count mass, or leaves the heap
unchanged and consumes an immediate/static worklist entry. No fuel is needed. -/
theorem releaseOne_decreases {H H' : Heap} {v : RVal} {pending pending' : List RVal}
    (h : releaseOne H v pending = some (H', pending')) :
    Prod.Lex Nat.lt Nat.lt (mass H', pending'.length) (mass H, (v :: pending).length) := by
  cases v with
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [releaseOne, hc] at h
    | some c =>
      cases c with
      | dead => simp [releaseOne, hc] at h
      | live rc m b =>
        cases m with
        | static =>
          simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          apply Prod.Lex.right
          simp
        | dyn =>
          cases rc with
          | zero => simp [releaseOne, hc] at h
          | succ rc =>
            cases rc with
            | zero =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Prod.Lex.left _ _ (mass_free_lt hc)
            | succ rc =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Prod.Lex.left _ _ (mass_dec_lt hc)
  | lit l | ctor0 l =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply Prod.Lex.right
    simp
  | erased =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply Prod.Lex.right
    simp

/-- Complete iterative release, with no source-semantic clock or artificial
fuel. Invalid states return `none`; termination holds even outside `Balance`.
The heap's abstract locations remain append-only; reclamation marks them dead. -/
def dropAll (H : Heap) (pending : List RVal) : Option Heap :=
  match pending with
  | [] => some H
  | v :: ps =>
    match h : releaseOne H v ps with
    | none => none
    | some (H', ps') => dropAll H' ps'
termination_by (mass H, pending.length)
decreasing_by exact releaseOne_decreases h

/-- The complete release loop succeeds on a balanced worklist and consumes
all pending references while retaining exactly the external/root reference
mass plus surviving heap edges. No extra operation-success premise is needed. -/
theorem dropAll_balance (H : Heap) (pending : List RVal) {external : Nat → Nat}
    (hb : Balance H external pending) :
    ∃ H', dropAll H pending = some H' ∧ Balance H' external [] := by
  match hPending : pending with
  | [] => exact ⟨H, by simp [hPending, dropAll], by simpa [hPending] using hb⟩
  | v :: ps =>
    have hb0 : Balance H external (v :: ps) := by simpa [hPending] using hb
    obtain ⟨H', ps', hstep, hb'⟩ := releaseOne_balance hb0
    obtain ⟨H'', hdrop, hend⟩ := dropAll_balance H' ps' hb'
    refine ⟨H'', ?_, hend⟩
    rw [dropAll, hstep]
    exact hdrop
termination_by (mass H, pending.length)
decreasing_by
  have hd := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hd with hd | ⟨he, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

end IxCC.Own.Rc
