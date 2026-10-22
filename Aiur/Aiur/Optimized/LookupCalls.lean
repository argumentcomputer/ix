import Aiur.Optimized.LookupPayloads

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

structure CallSlot (ctx : Context F) where
  channel : String
  result : WireValue Witness
  payload : Payload ctx

def CallSlot.emit {ctx : Context F} (call : CallSlot ctx) : Circuit.Send F :=
  ⟨call.channel, call.payload.wires, call.result, call.payload.guard.expr⟩

def CallSlot.claims {ctx : Context F} (call : CallSlot ctx) (a : Witness → F) : List (Circuit.Message F) :=
  if call.payload.guard.expr.denote a = 1 then [call.emit.message a] else []

def CallSlot.Compatible {ctx : Context F} (left right : CallSlot ctx) : Prop :=
  left.channel = right.channel ∧ left.result = right.result ∧
    left.payload.wires.map wireShape = right.payload.wires.map wireShape

instance {ctx : Context F} (left right : CallSlot ctx) : Decidable (left.Compatible right) := by
  unfold CallSlot.Compatible
  infer_instance

def CallSlot.join {ctx : Context F} (left right : CallSlot ctx)
    (different : left.payload.guard.exclusive right.payload.guard = true) : CallSlot ctx :=
  ⟨left.channel, left.result, left.payload.join right.payload different⟩

theorem CallSlot.join_claims {ctx : Context F} {left right : CallSlot ctx}
    (different : left.payload.guard.exclusive right.payload.guard = true)
    (shape : left.Compatible right) {a : Witness → F} (valid : ctx.Valid a) :
    (left.join right different).claims a = left.claims a ++ right.claims a := by
  have leftMessage (active : left.payload.guard.expr.denote a = 1) :
      (left.join right different).emit.message a = left.emit.message a := by
    have same := Payload.join_left different shape.2.2 valid active
    exact congrArg (fun args => Circuit.Message.mk left.channel args (left.result.map a)) same
  have rightMessage (active : right.payload.guard.expr.denote a = 1) :
      (left.join right different).emit.message a = right.emit.message a := by
    have same := Payload.join_right different shape.2.2 valid active
    simpa only [CallSlot.emit, CallSlot.join, Circuit.Send.message, denoteWires, shape.1, shape.2.1] using
      congrArg (fun args => Circuit.Message.mk left.channel args (left.result.map a)) same
  rcases left.payload.guard.boolean a valid with l | l
  · rcases right.payload.guard.boolean a valid with r | r
    · simp [CallSlot.claims, CallSlot.join, Payload.join, Guard.join, Scalar.Circuit.ArithExpr.denote, l, r]
    · rw [CallSlot.claims, if_pos (by simpa [CallSlot.join, Payload.join, Guard.join,
        Scalar.Circuit.ArithExpr.denote, l] using r), rightMessage r]
      simp [CallSlot.claims, l, r]
  · have r := Guard.exclusive_sound different valid (by rw [l]; exact one_ne_zero)
    rw [CallSlot.claims, if_pos (by simp [CallSlot.join, Payload.join, Guard.join,
      Scalar.Circuit.ArithExpr.denote, l, r]), leftMessage l]
    simp [CallSlot.claims, l, r]

def callClaims {ctx : Context F} (a : Witness → F) (calls : List (CallSlot ctx)) : List (Circuit.Message F) :=
  calls.flatMap (fun call => call.claims a)

theorem callClaims_inactive {ctx : Context F} {right : CallSlot ctx} {gap : List (CallSlot ctx)}
    (different : gap.all (fun call => right.payload.guard.exclusive call.payload.guard) = true)
    {a : Witness → F} (valid : ctx.Valid a) (active : right.payload.guard.expr.denote a = 1) :
    callClaims a gap = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro call member
  have zero := Guard.exclusive_sound (List.all_eq_true.mp different call member) valid
    (by rw [active]; exact one_ne_zero)
  simp [CallSlot.claims, zero]

/-- Moving the right slot across a gap preserves premise order only when its
activation excludes every slot in that gap. Simultaneous calls retain their
separate occurrences, even when their messages happen to agree. -/
theorem CallSlot.join_across {ctx : Context F} {left right : CallSlot ctx} {gap : List (CallSlot ctx)}
    (different : left.payload.guard.exclusive right.payload.guard = true)
    (shape : left.Compatible right)
    (crossing : gap.all (fun call => right.payload.guard.exclusive call.payload.guard) = true)
    {a : Witness → F} (valid : ctx.Valid a) :
    (left.join right different).claims a ++ callClaims a gap =
      left.claims a ++ callClaims a gap ++ right.claims a := by
  rw [CallSlot.join_claims different shape valid]
  by_cases active : right.payload.guard.expr.denote a = 1
  · rw [callClaims_inactive crossing valid active]; simp
  · simp [CallSlot.claims, active]

def insertCall {ctx : Context F} (right : CallSlot ctx) : List (CallSlot ctx) → List (CallSlot ctx)
  | [] => [right]
  | left :: rest =>
    if left.Compatible right then
      if different : left.payload.guard.exclusive right.payload.guard = true then
        if rest.all (fun call => right.payload.guard.exclusive call.payload.guard) then
          left.join right different :: rest
        else left :: insertCall right rest
      else left :: insertCall right rest
    else left :: insertCall right rest

theorem insertCall_claims {ctx : Context F} (right : CallSlot ctx) (calls : List (CallSlot ctx))
    {a : Witness → F} (valid : ctx.Valid a) :
    callClaims a (insertCall right calls) = callClaims a calls ++ right.claims a := by
  induction calls with
  | nil => simp [insertCall, callClaims]
  | cons left rest ih =>
    unfold insertCall
    split
    · split
      · split
        · exact CallSlot.join_across (by assumption) (by assumption) (by assumption) valid
        · simpa only [callClaims, List.flatMap_cons, List.append_assoc] using congrArg (left.claims a ++ ·) ih
      · simpa only [callClaims, List.flatMap_cons, List.append_assoc] using congrArg (left.claims a ++ ·) ih
    · simpa only [callClaims, List.flatMap_cons, List.append_assoc] using congrArg (left.claims a ++ ·) ih

def mergeCalls {ctx : Context F} (calls : List (CallSlot ctx)) : List (CallSlot ctx) :=
  calls.foldl (fun acc call => insertCall call acc) []

theorem mergeCalls_claims {ctx : Context F} (calls : List (CallSlot ctx))
    {a : Witness → F} (valid : ctx.Valid a) : callClaims a (mergeCalls calls) = callClaims a calls := by
  have fold (rest acc : List (CallSlot ctx)) :
      callClaims a (rest.foldl (fun acc call => insertCall call acc) acc) = callClaims a acc ++ callClaims a rest := by
    induction rest generalizing acc with
    | nil => simp [callClaims]
    | cons call rest ih =>
      rw [List.foldl_cons, ih, insertCall_claims call acc valid]
      simp only [callClaims, List.flatMap_cons, List.append_assoc]
  simpa only [mergeCalls, callClaims, List.flatMap_nil, List.nil_append] using fold calls []

theorem emitCalls_claims {ctx : Context F} (calls : List (CallSlot ctx)) (a : Witness → F) :
    (calls.map CallSlot.emit).filterMap (fun send =>
      if send.enable.denote a = 1 then some (send.message a) else none) = callClaims a calls := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
    simp only [List.map_cons, List.filterMap_cons, callClaims, List.flatMap_cons, CallSlot.claims]
    by_cases active : call.payload.guard.expr.denote a = 1 <;>
      simp_all [CallSlot.emit, callClaims, CallSlot.claims]

end Aiur.Optimized.LookupMerging
