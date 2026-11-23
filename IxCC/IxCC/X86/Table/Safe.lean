import IxCC.X86.Table.Rows

/-!
# Row safety preconditions

Each row's `safe` field is a decidable precondition under which its
semantic function cannot fault. `Op.safe_ok` proves that for every row, so a
compiler that establishes `safe` (a nonzero divisor above `div`'s high half,
defined flags for `jcc`, `setcc` and `cmovcc`) knows the row succeeds on its
inputs. The rows without a precondition never fault semantically; they can
still fault on memory, which footprints and permissions handle.
-/

namespace IxCC.X86

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

theorem signExtendSem_ok (source : Width) (input : SemIn) : ∃ out, signExtendSem source input = .ok out := by
  unfold signExtendSem
  split <;> exact ⟨_, rfl⟩

theorem notSem_ok (input : SemIn) : ∃ out, notSem input = .ok out := by
  unfold notSem
  split <;> exact ⟨_, rfl⟩

theorem negSem_ok (width : Width) (input : SemIn) : ∃ out, negSem width input = .ok out := by
  unfold negSem
  split <;> exact ⟨_, rfl⟩

theorem bswapSem_ok (width : Width) (input : SemIn) : ∃ out, bswapSem width input = .ok out := by
  unfold bswapSem
  split <;> exact ⟨_, rfl⟩

theorem adcSem_ok (width : Width) (input : SemIn) (safe : input.flags.carry.isSome = true) :
    ∃ out, adcSem width input = .ok out := by
  obtain ⟨args, flags⟩ := input
  obtain ⟨cf, hcf⟩ := Option.isSome_iff_exists.mp safe
  simp only at hcf
  match args with
  | [left, right] => simp [adcSem, hcf]
  | [] | [_] | _ :: _ :: _ :: _ => exact ⟨_, rfl⟩

theorem sbbSem_ok (width : Width) (input : SemIn) (safe : input.flags.carry.isSome = true) :
    ∃ out, sbbSem width input = .ok out := by
  obtain ⟨args, flags⟩ := input
  obtain ⟨cf, hcf⟩ := Option.isSome_iff_exists.mp safe
  simp only at hcf
  match args with
  | [left, right] => simp [sbbSem, hcf]
  | [] | [_] | _ :: _ :: _ :: _ => exact ⟨_, rfl⟩

theorem bsrSem_ok (width : Width) (input : SemIn) : ∃ out, bsrSem width input = .ok out := by
  obtain ⟨args, flags⟩ := input
  match args with
  | [oldDst, src] =>
      simp only [bsrSem]
      split <;> exact ⟨_, rfl⟩
  | [] | [_] | _ :: _ :: _ :: _ => exact ⟨_, rfl⟩

theorem mulSem_ok (width : Width) (input : SemIn) : ∃ out, mulSem width input = .ok out := by
  unfold mulSem
  split <;> exact ⟨_, rfl⟩

theorem umulSem_ok (width : Width) (input : SemIn) : ∃ out, umulSem width input = .ok out := by
  unfold umulSem
  split <;> exact ⟨_, rfl⟩

theorem testSem_ok (width : Width) (input : SemIn) : ∃ out, testSem width input = .ok out := by
  unfold testSem
  split <;> exact ⟨_, rfl⟩

theorem shiftSem_ok (operation : ShiftOp) (width : Width) (input : SemIn) :
    ∃ out, shiftSem operation width input = .ok out := by
  unfold shiftSem
  split <;> exact ⟨_, rfl⟩

theorem rotateSem_ok (operation : RotateOp) (width : Width) (input : SemIn) :
    ∃ out, rotateSem operation width input = .ok out := by
  unfold rotateSem
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
(`safe_ok`): `div` with a nonzero divisor above the high half,
the flag readers with their condition's flags defined, and every other row
unconditionally. -/
theorem Op.safe_ok (o : Op) (input : SemIn) (safe : (desc o).safe input = true) :
    ∃ out, (desc o).sem input = .ok out := by
  cases hmn : o.mn with
  | add | or | and | sub | xor | cmp =>
      cases hform : o.form <;> simp only [desc, hmn, hform, arithDesc] at safe ⊢ <;> exact Arith.sem_ok _ _ _
  | adc =>
      cases hform : o.form <;> simp only [desc, hmn, hform, adcDesc, carryArithDesc] at safe ⊢ <;> exact adcSem_ok _ _ safe
  | sbb =>
      cases hform : o.form <;> simp only [desc, hmn, hform, sbbDesc, carryArithDesc] at safe ⊢ <;> exact sbbSem_ok _ _ safe
  | test =>
      cases hform : o.form <;> simp only [desc, hmn, hform, testDesc] at safe ⊢ <;> exact testSem_ok _ _
  | not => simp only [desc, hmn, notDesc] at safe ⊢; exact notSem_ok _
  | neg => simp only [desc, hmn, negDesc] at safe ⊢; exact negSem_ok _ _
  | shl | shr | sar =>
      cases hform : o.form <;> simp only [desc, hmn, hform, shiftDesc] at safe ⊢ <;> exact shiftSem_ok _ _ _
  | rol | ror =>
      cases hform : o.form <;> simp only [desc, hmn, hform, rotateDesc] at safe ⊢ <;> exact rotateSem_ok _ _ _
  | bswap => simp only [desc, hmn, bswapDesc] at safe ⊢; exact bswapSem_ok _ _
  | bsr => simp only [desc, hmn, bsrDesc] at safe ⊢; exact bsrSem_ok _ _
  | mov =>
      cases hform : o.form <;> simp only [desc, hmn, hform, movDesc] at safe ⊢ <;> exact moveSem_ok _
  | movzx => simp only [desc, hmn, movzxDesc] at safe ⊢; exact zeroExtendSem_ok _ _
  | movsx => simp only [desc, hmn, movsxDesc] at safe ⊢; exact signExtendSem_ok _ _
  | movsxd => simp only [desc, hmn, movsxdDesc] at safe ⊢; exact signExtendSem_ok _ _
  | lea => simp only [desc, hmn, leaDesc] at safe ⊢; exact moveSem_ok _
  | imul =>
      cases hform : o.form <;> simp only [desc, hmn, hform, imulDesc] at safe ⊢ <;> exact mulSem_ok _ _
  | mul => simp only [desc, hmn, umulDesc] at safe ⊢; exact umulSem_ok _ _
  | div => simp only [desc, hmn, divDesc] at safe ⊢; exact divSem_ok _ _ safe
  | setcc => simp only [desc, hmn, setccDesc] at safe ⊢; exact setccSem_ok _ _ safe
  | cmovcc => simp only [desc, hmn, cmovDesc] at safe ⊢; exact cmovSem_ok _ _ safe
  | push => simp only [desc, hmn, pushDesc] at safe ⊢; exact moveSem_ok _
  | pop => simp only [desc, hmn, popDesc] at safe ⊢; exact moveSem_ok _
  | call => simp only [desc, hmn, callDesc] at safe ⊢; exact ⟨_, rfl⟩
  | jmp => simp only [desc, hmn, jmpDesc] at safe ⊢; exact ⟨_, rfl⟩
  | ret => simp only [desc, hmn, retDesc] at safe ⊢; exact ⟨_, rfl⟩
  | jcc => simp only [desc, hmn, jccDesc] at safe ⊢; exact jccSem_ok _ _ safe

end IxCC.X86
