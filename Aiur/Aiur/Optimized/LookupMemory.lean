import Aiur.Optimized.LookupPayloads

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

/-- Pack the address as a separate field wire. The stored value keeps its full
nominal type and width, so unrelated ROM layouts cannot accidentally merge. -/
def memoryWords (address : Polynomial F) (value : WireValue (Polynomial F)) : List (WireValue (Polynomial F)) :=
  [WireValue.field address, value]

def unpackMemory (zero : α) (wires : List (WireValue α)) : α × WireValue α :=
  match wires with
  | address :: value :: _ => (address.words.headD zero, value)
  | _ => (zero, ⟨.tuple [], []⟩)

omit [DecidableEq F] in
theorem unpackMemory_denote (wires : List (WireValue (Polynomial F))) (a : Witness → F) :
    unpackMemory (0 : F) (denoteWires a wires) =
      ((unpackMemory (.const 0) wires).1.denote a,
       (unpackMemory (.const 0) wires).2.map (Circuit.ArithExpr.denote a)) := by
  cases wires with
  | nil => rfl
  | cons address rest =>
    cases rest with
    | nil => rfl
    | cons value rest =>
      rcases address with ⟨type, words⟩
      cases words <;> rfl

def Payload.emitMemory {ctx : Context F} (p : Payload ctx) : Circuit.MemoryLookup F :=
  let (address, value) := unpackMemory (.const 0) p.wires
  ⟨address, value, p.guard.expr⟩

theorem Payload.emitMemory_valid {ctx : Context F} (p : Payload ctx) (rom : WireROM F) (a : Witness → F) :
    p.emitMemory.Valid rom a ↔
      (p.guard.expr.denote a = 1 → unpackMemory (0 : F) (denoteWires a p.wires) ∈ rom.entries) := by
  rw [unpackMemory_denote]
  rfl

theorem Payload.join_memory {ctx : Context F} {left right : Payload ctx}
    (different : left.guard.exclusive right.guard = true)
    (shape : left.wires.map wireShape = right.wires.map wireShape)
    {a : Witness → F} (valid : ctx.Valid a) (rom : WireROM F) :
    (left.join right different).emitMemory.Valid rom a ↔
      left.emitMemory.Valid rom a ∧ right.emitMemory.Valid rom a := by
  rw [Payload.emitMemory_valid, Payload.emitMemory_valid, Payload.emitMemory_valid]
  rcases left.guard.boolean a valid with l | l
  · rcases right.guard.boolean a valid with r | r
    · simp [Payload.join, Guard.join, Scalar.Circuit.ArithExpr.denote, l, r]
    · rw [Payload.join_right different shape valid r]
      simp [Payload.join, Guard.join, Scalar.Circuit.ArithExpr.denote, l, r]
  · have r := Guard.exclusive_sound different valid (by rw [l]; exact one_ne_zero)
    rw [Payload.join_left different shape valid l]
    simp [Payload.join, Guard.join, Scalar.Circuit.ArithExpr.denote, l, r]

def memoryValid {ctx : Context F} (rom : WireROM F) (a : Witness → F) (slots : List (Payload ctx)) : Prop :=
  ∀ slot ∈ slots, slot.emitMemory.Valid rom a

@[simp] theorem memoryValid_cons {ctx : Context F} (rom : WireROM F) (a : Witness → F)
    (slot : Payload ctx) (slots : List (Payload ctx)) :
    memoryValid rom a (slot :: slots) ↔ slot.emitMemory.Valid rom a ∧ memoryValid rom a slots := by
  simp only [memoryValid, List.forall_mem_cons]

def insertMemory {ctx : Context F} (right : Payload ctx) : List (Payload ctx) → List (Payload ctx)
  | [] => [right]
  | left :: rest =>
    if left.wires.map wireShape = right.wires.map wireShape then
      if different : left.guard.exclusive right.guard = true then
        left.join right different :: rest
      else left :: insertMemory right rest
    else left :: insertMemory right rest

theorem insertMemory_valid {ctx : Context F} (right : Payload ctx) (slots : List (Payload ctx))
    {a : Witness → F} (valid : ctx.Valid a) (rom : WireROM F) :
    memoryValid rom a (insertMemory right slots) ↔ memoryValid rom a slots ∧ right.emitMemory.Valid rom a := by
  induction slots with
  | nil => simp [insertMemory, memoryValid]
  | cons left rest ih =>
    unfold insertMemory
    split
    · split
      · rw [memoryValid_cons, memoryValid_cons, Payload.join_memory (by assumption) (by assumption) valid]
        tauto
      · rw [memoryValid_cons, memoryValid_cons, ih]; tauto
    · rw [memoryValid_cons, memoryValid_cons, ih]; tauto

def mergeMemory {ctx : Context F} (slots : List (Payload ctx)) : List (Payload ctx) :=
  slots.foldl (fun acc slot => insertMemory slot acc) []

theorem mergeMemory_valid {ctx : Context F} (slots : List (Payload ctx))
    {a : Witness → F} (valid : ctx.Valid a) (rom : WireROM F) :
    memoryValid rom a (mergeMemory slots) ↔ memoryValid rom a slots := by
  have fold (rest acc : List (Payload ctx)) :
      memoryValid rom a (rest.foldl (fun acc slot => insertMemory slot acc) acc) ↔
        memoryValid rom a acc ∧ memoryValid rom a rest := by
    induction rest generalizing acc with
    | nil => simp [memoryValid]
    | cons slot rest ih =>
      rw [List.foldl_cons, ih, insertMemory_valid slot acc valid, memoryValid_cons]
      tauto
  simpa only [mergeMemory, memoryValid, List.not_mem_nil, false_implies, implies_true, true_and] using fold slots []

end Aiur.Optimized.LookupMerging
