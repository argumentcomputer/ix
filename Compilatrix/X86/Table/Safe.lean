import Compilatrix.X86.Table.Rows

/-!
# Row safety preconditions

Each row's `safe` field is a decidable precondition under which its
semantic function cannot fault. `Op.safe_ok` proves that for every row, so a
compiler that establishes `safe` (a nonzero divisor above `div`'s high half,
defined flags for `jcc`, `setcc` and `cmovcc`) knows the row succeeds on its
inputs. The rows without a precondition never fault semantically; they can
still fault on memory, which footprints and permissions handle.
-/

namespace Compilatrix.X86

namespace Table

theorem aluSem_ok (operation : AluOp) (width : Width) (input : SemIn) :
    ∃ out, aluSem operation width input = .ok out := by
  unfold aluSem
  split <;> exact ⟨_, rfl⟩

theorem cmpSem_ok (width : Width) (input : SemIn) : ∃ out, cmpSem width input = .ok out := by
  unfold cmpSem
  split <;> exact ⟨_, rfl⟩

theorem Arith.sem_ok (arith : Arith) (width : Width) (input : SemIn) :
    ∃ out, arith.sem width input = .ok out := by
  cases hoperation : arith.operation with
  | some operation => simpa [Arith.sem, hoperation] using aluSem_ok operation width input
  | none => simpa [Arith.sem, hoperation] using cmpSem_ok width input

theorem moveSem_ok (input : SemIn) : ∃ out, moveSem input = .ok out := by
  unfold moveSem
  split <;> exact ⟨_, rfl⟩

theorem zeroExtendSem_ok (source : Width) (input : SemIn) : ∃ out, zeroExtendSem source input = .ok out := by
  unfold zeroExtendSem
  split <;> exact ⟨_, rfl⟩

theorem mulSem_ok (width : Width) (input : SemIn) : ∃ out, mulSem width input = .ok out := by
  unfold mulSem
  split <;> exact ⟨_, rfl⟩

theorem testSem_ok (width : Width) (input : SemIn) : ∃ out, testSem width input = .ok out := by
  unfold testSem
  split <;> exact ⟨_, rfl⟩

theorem shiftSem_ok (operation : ShiftOp) (width : Width) (input : SemIn) :
    ∃ out, shiftSem operation width input = .ok out := by
  unfold shiftSem
  split <;> exact ⟨_, rfl⟩

/-- `div` succeeds under its precondition: a nonzero divisor above the high
half of the dividend. -/
theorem divSem_ok (width : Width) (input : SemIn) (safe : divSafe width input = true) :
    ∃ out, divSem width input = .ok out := by
  obtain ⟨args, flags⟩ := input
  match args, safe with
  | [divisor, low, high], safe =>
      simp only [divSafe, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at safe
      have fits : ((width.truncate divisor).toNat == 0 ||
          decide ((width.truncate divisor).toNat ≤ (width.truncate high).toNat)) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not, Nat.not_le]
        exact safe
      simp only [divSem, fits, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl⟩
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => exact ⟨_, rfl⟩

theorem jccSem_ok (condition : Condition) (input : SemIn) (safe : (input.flags.test condition).isSome = true) :
    ∃ out, jccSem condition input = .ok out := by
  obtain ⟨args, flags⟩ := input
  obtain ⟨holds, found⟩ := Option.isSome_iff_exists.mp safe
  simp only at found
  simp [jccSem, found]

theorem setccSem_ok (condition : Condition) (input : SemIn) (safe : (input.flags.test condition).isSome = true) :
    ∃ out, setccSem condition input = .ok out := by
  obtain ⟨args, flags⟩ := input
  obtain ⟨holds, found⟩ := Option.isSome_iff_exists.mp safe
  simp only at found
  simp [setccSem, found]

theorem cmovSem_ok (condition : Condition) (input : SemIn) (safe : (input.flags.test condition).isSome = true) :
    ∃ out, cmovSem condition input = .ok out := by
  obtain ⟨args, flags⟩ := input
  obtain ⟨holds, found⟩ := Option.isSome_iff_exists.mp safe
  simp only at found
  match args with
  | [destination, source] => simp [cmovSem, found]
  | [] | [_] | _ :: _ :: _ :: _ => exact ⟨_, rfl⟩

end Table

open Table in
/-- Every row's semantics succeeds under the row's safety precondition
(`safe_ok`, note 05 §8.6): `div` with a nonzero divisor above the high half,
the flag readers with their condition's flags defined, and every other row
unconditionally. -/
theorem Op.safe_ok (o : Op) (input : SemIn) (safe : (desc o).safe input = true) :
    ∃ out, (desc o).sem input = .ok out := by
  cases hmn : o.mn <;> cases hform : o.form <;>
    simp only [desc, hmn, hform, arithDesc, movDesc, movzxDesc, leaDesc, imulDesc, testDesc, shiftDesc, divDesc,
      setccDesc, cmovDesc, pushDesc, popDesc, callDesc, jmpDesc, retDesc, jccDesc] at safe ⊢
  all_goals first
    | exact Arith.sem_ok _ _ _
    | exact moveSem_ok _
    | exact zeroExtendSem_ok _ _
    | exact mulSem_ok _ _
    | exact testSem_ok _ _
    | exact shiftSem_ok _ _ _
    | exact divSem_ok _ _ safe
    | exact setccSem_ok _ _ safe
    | exact cmovSem_ok _ _ safe
    | exact jccSem_ok _ _ safe
    | exact ⟨_, rfl⟩

end Compilatrix.X86
