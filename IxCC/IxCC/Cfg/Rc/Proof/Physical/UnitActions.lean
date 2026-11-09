import IxCC.Own.Plain.Syntax

/-! Producer fact supporting the explicit first native fragment: every emitted
increment is one token. General abstract inc n remains a separate operation. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Own.Plain

def unitAction : Action → Bool
  | .inc _ n => n == 1
  | .dec _ => true

mutual
def unitCode : Code → Bool
  | .act a k => unitAction a && unitCode k
  | .bind _ _ k => unitCode k
  | .jp _ _ _ _ b k => unitCode b && unitCode k
  | .case _ alts d => unitAlts alts && unitOpt d
  | .jmp .. | .ret .. | .tcall .. | .trap => true
def unitAlts : List Alt → Bool
  | [] => true
  | .mk _ b :: rest => unitCode b && unitAlts rest
def unitOpt : Option Code → Bool
  | none => true
  | some c => unitCode c
end

theorem copies_unit (args : List Fir.Arg) : (copies args).all unitAction = true := by
  induction args with
  | nil => rfl
  | cons a args ih => cases a <;> simp [copies, unitAction, ih]

theorem drops_unit (captured live : List Fir.Var) : (drops captured live).all unitAction = true := by
  induction live with
  | nil => rfl
  | cons x live ih =>
    rw [drops]
    split
    · exact ih
    · simpa only [List.all_cons, unitAction, Bool.true_and] using ih

theorem prefix_unit (as : List Action) (k : Code) :
    unitCode (actionPrefix as k) = (as.all unitAction && unitCode k) := by
  induction as with
  | nil => simp [actionPrefix]
  | cons a as ih => simp [actionPrefix, unitCode, ih, Bool.and_assoc]

theorem moveCopies_unit (seen : List Fir.Var) (args : List Fir.Arg) :
    (moveCopies seen args).all unitAction = true := by
  induction args generalizing seen with
  | nil => rfl
  | cons a args ih =>
    cases a with
    | var x =>
      rw [moveCopies]
      split
      · simpa only [List.all_cons, unitAction, beq_self_eq_true, Bool.true_and] using ih seen
      · exact ih (x :: seen)
    | lit _ | erased => exact ih seen

theorem transfer_unit (live imm captured : List Fir.Var) (args : List Fir.Arg) (k : Code) :
    unitCode (transfer live imm captured args k) = unitCode k := by
  simp [transfer, transferActions, prefix_unit, moveCopies_unit, drops_unit]

mutual
theorem lowerCode_unit (live : List Fir.Var) (joins : Joins) :
    ∀ c (imm : List Fir.Var := []), unitCode (lowerCode live joins c imm) = true
  | .bind x r k, imm => by
    cases r with
    | proj y _ _ =>
      dsimp only [lowerCode]
      cases imm.contains y <;> simp [unitCode, unitAction, lowerCode_unit]
    | _ => simp [lowerCode, prefix_unit, copies_unit, unitCode, unitAction, lowerCode_unit]
  | .jp j ps rec b k, imm => by simp [lowerCode, unitCode, lowerCode_unit]
  | .jmp .., imm => by simp [lowerCode, transfer_unit, unitCode]
  | .case x alts d, imm => by simp [lowerCode, unitCode, lowerAlts_unit, lowerOpt_unit]
  | .ret .., imm | .tcall .., imm => by simp [lowerCode, transfer_unit, unitCode]
  | .trap, imm => by simp [lowerCode, transfer_unit, unitCode]
theorem lowerAlts_unit (live : List Fir.Var) (joins : Joins) :
    ∀ alts (imm : List Fir.Var := []), unitAlts (lowerAlts live joins alts imm) = true
  | [], _ => rfl
  | .mk key b :: rest, imm => by simp [lowerAlts, unitAlts, lowerCode_unit, lowerAlts_unit]
theorem lowerOpt_unit (live : List Fir.Var) (joins : Joins) :
    ∀ d (imm : List Fir.Var := []), unitOpt (lowerOpt live joins d imm) = true
  | none, _ => rfl
  | some c, imm => lowerCode_unit live joins c imm
end


end IxCC.Cfg.Rc
