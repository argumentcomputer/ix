import Ix.Ixon.BlockOrder
import Ix.Ixon.Projection.Theorems

namespace Ixon.BlockOrder

open Ix.Kernel

/-! ## Recursor blocks in motive order -/

open Ix.Kernel.Reader in
/-- `recursorMotive` is the motive the Ixon reader indexes a recursor under:
whenever the reader's analysis (`Reader.analyseRecursor`) succeeds,
it reads the same motive, so a recursor block in motive order is a block the
reader regroups without permuting it. -/
theorem recursorMotive_of_analyse {store owner c r m carriers major}
    (h : analyseRecursor store owner c r = some (m, carriers, major)) :
    recursorMotive c r = some m := by
  unfold analyseRecursor at h
  unfold recursorMotive
  cases hs : stripAll c
      (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat + 1) r.typ with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨doms, body⟩ := p
    cases hd : appHead c spineFuel body with
    | var k =>
      simp only [hs, hd, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h ⊢
      obtain ⟨u, hu, rest⟩ := Option.bind_eq_some_iff.mp h
      rw [Option.bind_eq_some_iff]
      refine ⟨u, hu, ?_⟩
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, _, _, _, _, _, hm, _⟩ := rest
      exact congrArg some hm
    | _ => simp [hs, hd] at h

/-- The members, from `start` on, are recursors in motive order: the one at
position `start + j` eliminates motive `start + j` (`recursorMotive`, as the
reader reads it) and declares `size` motives. -/
def MotivesFrom (source : Ixon.Constant) (size start : Nat)
    (members : List Ixon.MutConst) : Prop :=
  ∀ j (h : j < members.length), ∃ r, members[j] = .recr r ∧ r.motives.toNat = size ∧
    recursorMotive source r = some (start + j)

/-- A recursor block in motive order: member `j` eliminates motive `j`, and
every member declares one motive per member of the block. -/
def MotiveOrdered (source : Ixon.Constant) (members : Array Ixon.MutConst) : Prop :=
  MotivesFrom source members.size 0 members.toList

theorem motivesFrom_cons (source : Ixon.Constant) (size start : Nat)
    (member : Ixon.MutConst) (rest : List Ixon.MutConst) :
    MotivesFrom source size start (member :: rest) ↔
      (∃ r, member = .recr r ∧ r.motives.toNat = size ∧ recursorMotive source r = some start) ∧
        MotivesFrom source size (start + 1) rest := by
  constructor
  · intro h
    obtain ⟨r, hr, hm, hmot⟩ := h 0 (by simp)
    refine ⟨⟨r, by simpa using hr, hm, by simpa using hmot⟩, fun j hj => ?_⟩
    obtain ⟨r, hr, hm, hmot⟩ := h (j + 1) (by simp; omega)
    exact ⟨r, by simpa using hr, hm, by rw [hmot]; congr 1; omega⟩
  · rintro ⟨⟨r, rfl, hm, hmot⟩, h⟩ j hj
    cases j with
    | zero => exact ⟨r, rfl, hm, by simpa using hmot⟩
    | succ j =>
      obtain ⟨r', hr', hm', hmot'⟩ := h j (by simp at hj; omega)
      exact ⟨r', by simpa using hr', hm', by rw [hmot']; congr 1; omega⟩

theorem checkMotives_ok_iff (owner : Address) (source : Ixon.Constant) (size : Nat) :
    ∀ (start : Nat) (members : List Ixon.MutConst),
      checkMotives owner source size start members = .ok () ↔ MotivesFrom source size start members
  | start, [] => by simp [checkMotives, MotivesFrom]
  | start, member :: rest => by
    rw [motivesFrom_cons, ← checkMotives_ok_iff owner source size (start + 1) rest]
    cases member with
    | recr r =>
      by_cases ok : r.motives.toNat = size ∧ recursorMotive source r = some start
      · simp [checkMotives, ok]
      · have bad : (r.motives.toNat == size && recursorMotive source r == some start) = false := by
          simpa [Bool.and_eq_true, beq_iff_eq] using ok
        simp only [checkMotives, bad]
        simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
        intro hm hmot
        exact absurd ⟨hm, hmot⟩ ok
    | defn _ | indc _ =>
      simp [checkMotives, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem checkMotiveOrder_ok_iff (owner : Address) (source : Ixon.Constant)
    (members : Array Ixon.MutConst) :
    checkMotives owner source members.size 0 members.toList = .ok () ↔
      MotiveOrdered source members :=
  checkMotives_ok_iff owner source members.size 0 members.toList

/-- A record's order: a recursor block in motive order, any other record
unconstrained. -/
def OrderedRecord (pair : Address × Ixon.Constant) : Prop :=
  match pair.2.info with
  | .muts members => if members.all isRecursor then MotiveOrdered pair.2 members else True
  | _ => True

theorem checkRecord_ok_iff (owner : Address) (source : Ixon.Constant) :
    checkRecord owner source = .ok () ↔ OrderedRecord (owner, source) := by
  rcases source with ⟨info, sharing, refs, univs⟩
  cases info with
  | muts members =>
    by_cases recursors : members.all isRecursor
    · simp only [checkRecord, OrderedRecord, recursors, ite_true]
      exact checkMotiveOrder_ok_iff owner _ members
    · simp [checkRecord, OrderedRecord, recursors]
  | _ => simp [checkRecord, OrderedRecord]

end Ixon.BlockOrder
