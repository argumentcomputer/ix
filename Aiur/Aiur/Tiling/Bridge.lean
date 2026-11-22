import Aiur.Tiling.Enables

/-!
# From logical chips to lookup circuits

`lower` is the lookup-circuit form of an activated physical chip, the
encoding the STARK backends use:

* the receive `push(-mult, [CALL, id f, inputs, output])`, with
  `(1 - sel)·mult = 0` added to the activated chip's constraints;
* every send `push(enable, [CALL, id g, args, result])`;
* every memory lookup `push(enable, [ROM, width, address, value])`.

`checkMemo_of_balanced` turns satisfying rows of the lowered chips whose
lookups balance (against the entry request, the fixed tables and the ROM)
into weighted rows that `Grouping.Plan.checkMemo` accepts. Field balance
yields a providing row for every required claim; the integer weights are
then chosen by `Balance.weigh`, as in the completeness proof of the memo
checker.
-/

namespace Aiur.Tiling.Bridge

open Aiur.Circuit
open Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

def CALL : Nat := 1
def ROM : Nat := 2

def encode (idOf : String → Nat) (m : Message F) : List F :=
  (CALL : F) :: (idOf m.channel : F) :: (m.args.flatMap WireValue.words ++ m.result.words)

def encodeRom (e : F × WireValue F) : List F :=
  (ROM : F) :: (e.2.words.length : F) :: e.1 :: e.2.words

def receiveLookup (idOf : String → Nat) (a : Chip F) (mult : Var) : Lookup F :=
  ⟨.sub (.const 0) (.var mult), .const (CALL : F) :: .const (idOf a.name : F) ::
    ((a.inputs.flatMap WireValue.words).map .var ++ a.output.words)⟩

def sendLookup (idOf : String → Nat) (s : Send F) : Lookup F :=
  ⟨s.enable, .const (CALL : F) :: .const (idOf s.channel : F) ::
    (s.args.flatMap WireValue.words ++ s.result.words.map .var)⟩

def memoryLookup (m : MemoryLookup F) : Lookup F :=
  ⟨m.enable, .const (ROM : F) :: .const (m.value.words.length : F) :: m.address :: m.value.words⟩

/-- The lookup circuit of the activated chip `Activation.compile c`: selector
`c.numVars`, receive multiplicity `c.numVars + 1`. -/
def lower (idOf : String → Nat) (c : Chip F) : Tiling.Circuit F where
  width := c.numVars + 2
  constraints := (Activation.compile c).constraints ++
    [.mul (.sub (.const 1) (.var c.numVars)) (.var (c.numVars + 1))]
  lookups := receiveLookup idOf (Activation.compile c) (c.numVars + 1) ::
    ((Activation.compile c).sends.map (sendLookup idOf) ++
      (Activation.compile c).memory.map memoryLookup)

/-! ## Tuples -/

theorem receive_tuple (idOf : String → Nat) (a : Chip F) (mult : Var) (w : Var → F) :
    (receiveLookup idOf a mult).tuple w = encode idOf (a.conclusion w) := by
  simp [receiveLookup, Lookup.tuple, encode, Chip.conclusion, Scalar.Circuit.ArithExpr.denote,
    List.map_flatMap, List.flatMap_map, Function.comp_def, WireValue.map]

theorem send_tuple (idOf : String → Nat) (s : Send F) (w : Var → F) :
    (sendLookup idOf s).tuple w = encode idOf (s.message w) := by
  simp [sendLookup, Lookup.tuple, encode, Send.message, Scalar.Circuit.ArithExpr.denote,
    List.map_flatMap, List.flatMap_map, Function.comp_def, WireValue.map]

theorem memory_tuple (m : MemoryLookup F) (w : Var → F) :
    (memoryLookup m).tuple w = encodeRom (m.address.denote w, m.value.map (Circuit.ArithExpr.denote w)) := by
  simp [memoryLookup, Lookup.tuple, encodeRom, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, WireValue.map]

/-- `checkEnables` discharges `Boolean` on every row of the lowered chip. -/
theorem boolean_of_lower {bound : Nat} (small : SmallCast F bound) {idOf : String → Nat}
    {c : Chip F} (ok : checkEnables bound c = true)
    {w : Var → F} (holds : (lower idOf c).Holds w) : Boolean c w :=
  boolean_of_checkEnables small ok fun q hq => holds q (List.mem_append_left _ hq)

/-- Equal encodings of messages with equal shapes and channels are equal. -/
theorem encode_inj {idOf : String → Nat} {m m' : Message F} (same : encode idOf m = encode idOf m')
    (channel : m.channel = m'.channel) (shapes : Erasure.messageShape m = Erasure.messageShape m') :
    m = m' := by
  apply Erasure.flatten_injective shapes
  simp only [encode, List.cons.injEq] at same
  have argLength : (m.args.flatMap WireValue.words).length = (m'.args.flatMap WireValue.words).length := by
    have := congrArg (fun s => (s.1.map Prod.snd).sum) shapes
    simp only [Erasure.messageShape, List.map_map] at this
    rw [List.length_flatMap, List.length_flatMap]
    simpa [Erasure.shape, Function.comp_def] using this
  obtain ⟨args, result⟩ := List.append_inj same.2.2 argLength
  simp [Erasure.flatten, channel, args, result]

/-! ## Hypotheses -/

/-- Lookups of all instances, plus the entry request. -/
def lookupCount (insts : List (Chip F × (Var → F))) : Nat :=
  (insts.map fun p => p.1.sends.length + p.1.memory.length).sum + 1

def channels (source : Circuit.System F) (chips : List (Chip F)) (root : Message F) : List String :=
  chips.map Chip.name ++ chips.flatMap (fun c => c.sends.map Send.channel) ++
    source.mapClaims.map Message.channel ++ [root.channel]

/-- Static, decidable facts about the physical chips that make the tuple
encoding injective on the claims that can meet on the bus. -/
structure Shaped (source : Circuit.System F) (chips : List (Chip F)) (idOf : String → Nat)
    (root : Message F) (bound : Nat) : Prop where
  calls : ∀ c ∈ chips, ∀ s ∈ c.sends, ∀ c' ∈ chips, c'.name = s.channel →
    (s.args.map Erasure.shape, Erasure.shape s.result) = Erasure.signature c'
  maps : ∀ c ∈ chips, ∀ s ∈ c.sends, ∀ mc ∈ source.mapClaims, mc.channel = s.channel →
    Erasure.messageShape mc = (s.args.map Erasure.shape, Erasure.shape s.result)
  rootChip : ∀ c ∈ chips, c.name = root.channel → Erasure.messageShape root = Erasure.signature c
  rootMaps : ∀ mc ∈ source.mapClaims, mc.channel = root.channel →
    Erasure.messageShape mc = Erasure.messageShape root
  memory : ∀ c ∈ chips, ∀ m ∈ c.memory, m.value.type = .tuple (List.replicate m.value.words.length .field)
  ids : ∀ x ∈ channels source chips root, ∀ y ∈ channels source chips root, idOf x = idOf y → x = y
  idBound : ∀ x ∈ channels source chips root, idOf x < bound

/-- Executable check of `Shaped`. -/
def Shaped.check (source : Circuit.System F) (chips : List (Chip F)) (idOf : String → Nat)
    (root : Message F) (bound : Nat) : Bool :=
  let ch := channels source chips root
  (chips.all fun c => c.sends.all fun s => chips.all fun c' =>
    !(c'.name == s.channel) ||
      decide ((s.args.map Erasure.shape, Erasure.shape s.result) = Erasure.signature c')) &&
  (chips.all fun c => c.sends.all fun s => source.mapClaims.all fun mc =>
    !(mc.channel == s.channel) ||
      decide (Erasure.messageShape mc = (s.args.map Erasure.shape, Erasure.shape s.result))) &&
  (chips.all fun c => !(c.name == root.channel) ||
    decide (Erasure.messageShape root = Erasure.signature c)) &&
  (source.mapClaims.all fun mc => !(mc.channel == root.channel) ||
    decide (Erasure.messageShape mc = Erasure.messageShape root)) &&
  (chips.all fun c => c.memory.all fun m =>
    decide (m.value.type = .tuple (List.replicate m.value.words.length .field))) &&
  (ch.all fun x => ch.all fun y => !(idOf x == idOf y) || x == y) &&
  (ch.all fun x => decide (idOf x < bound))

theorem Shaped.of_check {source : Circuit.System F} {chips : List (Chip F)} {idOf : String → Nat}
    {root : Message F} {bound : Nat} (h : Shaped.check source chips idOf root bound = true) :
    Shaped source chips idOf root bound := by
  simp only [Shaped.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨calls, maps⟩, rootChip⟩, rootMaps⟩, memory⟩, ids⟩, idBound⟩ := h
  refine ⟨?_, ?_, ?_, ?_, memory, ?_, idBound⟩
  · intro c hc s hs c' hc' name
    exact (calls c hc s hs c' hc').resolve_left (not_not.mpr name)
  · intro c hc s hs mc hmc name
    exact (maps c hc s hs mc hmc).resolve_left (not_not.mpr name)
  · intro c hc name
    exact (rootChip c hc).resolve_left (not_not.mpr name)
  · intro mc hmc name
    exact (rootMaps mc hmc).resolve_left (not_not.mpr name)
  · intro x hx y hy eq
    exact (ids x hx y hy).resolve_left (not_not.mpr eq)

/-! ## Ledger coefficients -/

theorem rowLedger_apply (C : Tiling.Circuit F) (w : Var → F) (t : List F) :
    C.rowLedger w t =
      (C.lookups.map fun l => if l.tuple w = t then l.multiplicity.denote w else 0).sum := by
  simp only [Tiling.Circuit.rowLedger, Tiling.System.ledger_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp [Lookup.entry, Finsupp.single_apply]

def recvCoef (idOf : String → Nat) (p : Chip F × (Var → F)) (t : List F) : F :=
  if encode idOf (p.1.conclusion p.2) = t then -p.2 (p.1.numVars + 1) else 0

def sendVals (idOf : String → Nat) (p : Chip F × (Var → F)) (t : List F) : List F :=
  (Activation.compile p.1).sends.map fun s =>
    if encode idOf (s.message p.2) = t then s.enable.denote p.2 else 0

def memVals (p : Chip F × (Var → F)) (t : List F) : List F :=
  (Activation.compile p.1).memory.map fun m =>
    if encodeRom (m.address.denote p.2, m.value.map (Circuit.ArithExpr.denote p.2)) = t then m.enable.denote p.2
    else 0

theorem lower_apply (idOf : String → Nat) (p : Chip F × (Var → F)) (t : List F) :
    (lower idOf p.1).rowLedger p.2 t = recvCoef idOf p t + (sendVals idOf p t).sum + (memVals p t).sum := by
  rw [rowLedger_apply]
  simp only [lower, List.map_cons, List.map_append, List.map_map, List.sum_cons, List.sum_append,
    add_assoc]
  congr 1
  · rw [receive_tuple, Activation.conclusion_eq]
    simp [recvCoef, receiveLookup, Scalar.Circuit.ArithExpr.denote]
  · congr 1
    · simp only [sendVals, Function.comp_def, send_tuple]; rfl
    · simp only [memVals, Function.comp_def, memory_tuple]; rfl

theorem zero_one_sum {bound : Nat} (small : SmallCast F bound) (l : List F)
    (bits : ∀ x ∈ l, x = 0 ∨ x = 1) (one : (1 : F) ∈ l) (short : l.length < bound) : l.sum ≠ 0 := by
  have count : ∀ l : List F, (∀ x ∈ l, x = 0 ∨ x = 1) → l.sum = (l.count 1 : F) := by
    intro l bits
    induction l with
    | nil => simp
    | cons x l ih =>
        rw [List.sum_cons, ih (fun y hy => bits y (by simp [hy])), List.count_cons]
        rcases bits x (by simp) with rfl | rfl
        · simp
        · simp; ring
  rw [count l bits]
  intro h
  have pos := List.count_pos_iff.mpr one
  have le := List.count_le_length (a := (1 : F)) (l := l)
  have := small _ (by omega) h
  omega

theorem exists_ne_zero_of_sum {l : List F} (h : l.sum ≠ 0) : ∃ x ∈ l, x ≠ 0 := by
  by_contra none
  push Not at none
  exact h (List.sum_eq_zero none)

theorem sum_flatMap' {α : Type} (l : List α) (g : α → List F) :
    (l.flatMap g).sum = (l.map fun x => (g x).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem nat_sum_map_le {α : Type} (l : List α) {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      have := h x (by simp)
      have := ih (fun y hy => h y (by simp [hy]))
      omega

/-! ## Balance at one tuple -/

section Main

variable {source : Circuit.System F} {id : String → Except String Nat}

/-- Rows of the lowered single chips of a plan, with balanced lookups. -/
structure Wide (plan : Grouping.Plan source id) (idOf : String → Nat) (bound : Nat)
    (rom : WireROM F) (root : Message F) (insts : List (Chip F × (Circuit.Var → F)))
    (tables : Ledger F) : Prop where
  chips : ∀ p ∈ insts, p.1 ∈ plan.singles
  holds : ∀ p ∈ insts, (lower idOf p.1).Holds p.2
  small : SmallCast F bound
  enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true
  tags : 2 < bound
  count : lookupCount insts < bound
  shaped : Shaped source plan.singles idOf root bound
  romPacked : ∀ e ∈ rom.entries, e.2.type = .tuple (List.replicate e.2.words.length .field)
  tableSupport : ∀ t, tables t ≠ 0 →
    (∃ mc ∈ source.mapClaims, t = encode idOf mc) ∨ ∃ e ∈ rom.entries, t = encodeRom e
  balanced : (insts.map fun p => (lower idOf p.1).rowLedger p.2).sum +
    Finsupp.single (encode idOf root) 1 + tables = 0

variable {plan : Grouping.Plan source id} {idOf : String → Nat} {bound : Nat} {rom : WireROM F}
  {root : Message F} {insts : List (Chip F × (Circuit.Var → F))} {tables : Ledger F}
  (W : Wide plan idOf bound rom root insts tables)
include W

theorem Wide.at (t : List F) :
    (insts.map fun p => recvCoef idOf p t + (sendVals idOf p t).sum + (memVals p t).sum).sum +
      (if encode idOf root = t then 1 else 0) + tables t = 0 := by
  have := congrArg (fun x : Ledger F => x t) W.balanced
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, Tiling.System.ledger_list_sum,
    List.map_map, Finsupp.single_apply] at this
  rw [← this]
  congr 3
  apply List.map_congr_left
  intro p _
  exact (lower_apply idOf p t).symm

theorem Wide.boolean {p : Chip F × (Circuit.Var → F)} (hp : p ∈ insts) : Boolean p.1 p.2 :=
  boolean_of_lower W.small (W.enablesOk _ (W.chips p hp)) (W.holds p hp)

theorem Wide.call_ne_rom : (CALL : F) ≠ (ROM : F) := by
  intro h
  have := W.small.inj (a := CALL) (b := ROM) (by simp [CALL]; have := W.tags; omega)
    (by simp [ROM]; exact W.tags) h
  simp [CALL, ROM] at this

theorem Wide.parts {p : Chip F × (Circuit.Var → F)} (hp : p ∈ insts) :
    Circuit.Satisfies (Activation.compile p.1).constraints p.2 ∧
      (1 - p.2 p.1.numVars) * p.2 (p.1.numVars + 1) = 0 := by
  have h := W.holds p hp
  refine ⟨fun q hq => h q (List.mem_append_left _ hq), ?_⟩
  have := h _ (List.mem_append_right _ (List.mem_singleton_self _))
  simpa [Scalar.Circuit.ArithExpr.denote] using this

theorem Wide.memVals_bits {p : Chip F × (Circuit.Var → F)} (hp : p ∈ insts) (t : List F) :
    ∀ x ∈ memVals p t, x = 0 ∨ x = 1 := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  split
  · exact (W.boolean hp).2 m hm
  · exact Or.inl rfl

theorem Wide.sendVals_bits {p : Chip F × (Circuit.Var → F)} (hp : p ∈ insts) (t : List F) :
    ∀ x ∈ sendVals idOf p t, x = 0 ∨ x = 1 := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  split
  · exact (W.boolean hp).1 s hs
  · exact Or.inl rfl

theorem Wide.memLength : (insts.flatMap fun p => memVals p (t : List F)).length < bound := by
  have := W.count
  simp only [lookupCount] at this
  simp only [List.length_flatMap, memVals, List.length_map, Activation.compile] at *
  have le : (insts.map fun p => p.1.memory.length).sum ≤
      (insts.map fun p => p.1.sends.length + p.1.memory.length).sum :=
    nat_sum_map_le _ (fun p _ => Nat.le_add_left _ _)
  omega

theorem Wide.sendLength :
    (insts.flatMap (fun p => sendVals idOf p (t : List F)) ++ [(0 : F)]).length < bound := by
  have := W.count
  simp only [lookupCount] at this
  simp only [List.length_append, List.length_flatMap, sendVals, List.length_map, Activation.compile,
    List.length_singleton] at *
  have le : (insts.map fun p => p.1.sends.length).sum ≤
      (insts.map fun p => p.1.sends.length + p.1.memory.length).sum :=
    nat_sum_map_le _ (fun p _ => Nat.le_add_right _ _)
  omega

/-- Every enabled memory lookup reads an entry of the ROM. -/
theorem Wide.memory_valid {p : Chip F × (Circuit.Var → F)} (hp : p ∈ insts) :
    ∀ m ∈ (Activation.compile p.1).memory, MemoryLookup.Valid rom p.2 m := by
  intro m hm enabled
  set t := encodeRom (m.address.denote p.2, m.value.map (Circuit.ArithExpr.denote p.2))
  have bal := W.at t
  have callZero : ∀ m' : Message F, encode idOf m' ≠ t := by
    intro m' h
    have := congrArg List.head? h
    simp [encode, t, encodeRom] at this
    exact W.call_ne_rom this
  have recv0 : ∀ q, recvCoef idOf q t = 0 := fun q => by simp [recvCoef, callZero]
  have send0 : ∀ q, (sendVals idOf q t).sum = 0 := fun q => by
    apply List.sum_eq_zero; intro x hx
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
    simp [callZero]
  simp only [recv0, send0, zero_add, callZero, ite_false, add_zero] at bal
  have sumNe : (insts.flatMap fun q => memVals q t).sum ≠ 0 := by
    apply zero_one_sum W.small
    · intro x hx
      obtain ⟨q, hq, hx⟩ := List.mem_flatMap.mp hx
      exact W.memVals_bits hq t x hx
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨m, hm, by simp [t, enabled]⟩⟩
    · exact W.memLength
  rw [sum_flatMap'] at sumNe
  have tablesNe : tables t ≠ 0 := by
    intro h; rw [h, add_zero] at bal; exact sumNe bal
  rcases W.tableSupport t tablesNe with ⟨mc, _, eq⟩ | ⟨e, he, eq⟩
  · exact absurd eq.symm (callZero mc)
  · have typeM : m.value.type = .tuple (List.replicate m.value.words.length .field) := by
      simp only [Activation.compile, List.mem_map] at hm
      obtain ⟨m0, hm0, rfl⟩ := hm
      exact W.shaped.memory p.1 (W.chips p hp) m0 hm0
    simp only [t, encodeRom, List.cons.injEq] at eq
    obtain ⟨_, _, addr, words⟩ := eq
    have : e = (m.address.denote p.2, m.value.map (Circuit.ArithExpr.denote p.2)) := by
      obtain ⟨ea, ev⟩ := e
      simp only at addr words
      have ty := W.romPacked _ he
      simp only at ty
      cases ev
      simp only [WireValue.map, WireValue.mk.injEq, Prod.mk.injEq] at *
      refine ⟨addr.symm, ?_, words.symm⟩
      rw [ty, typeM, ← words]; simp
    rw [← this]; exact he

omit W in
theorem conclusion_shape (c : Chip F) (w : Circuit.Var → F) :
    Erasure.messageShape (c.conclusion w) = Erasure.signature c := by
  simp [Erasure.messageShape, Erasure.signature, Chip.conclusion, List.map_map, Function.comp_def]

omit W in
theorem message_shape (s : Send F) (w : Circuit.Var → F) :
    Erasure.messageShape (s.message w) = (s.args.map Erasure.shape, Erasure.shape s.result) := by
  simp [Erasure.messageShape, Send.message, List.map_map, Function.comp_def]

omit W in
/-- A requirement of the activated chip is the message of one of the chip's own sends. -/
theorem requirement_send {c : Chip F} {w : Circuit.Var → F} {q : Message F}
    (h : q ∈ (Activation.compile c).requirements w) :
    ∃ s ∈ c.sends, q = s.message w ∧
      ∃ s' ∈ (Activation.compile c).sends, s'.enable.denote w = 1 ∧ s'.message w = q := by
  simp only [Chip.requirements, List.mem_filterMap] at h
  obtain ⟨s', hs', found⟩ := h
  split at found
  · rename_i enabled
    simp only [Option.some.injEq] at found
    simp only [Activation.compile, List.mem_map] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    refine ⟨s, hs, ?_, _, List.mem_map.mpr ⟨s, hs, rfl⟩, enabled, found⟩
    rw [← found]; simp [Activation.send, Send.message]
  · simp at found

/-- A claim the memo checker requires, other than a fixed-table claim, is
the conclusion of some active row. -/
theorem Wide.provider {q : Message F} (notStatic : ¬ source.MapClaim q)
    (required : q = root ∨ ∃ p ∈ insts, q ∈ (Activation.compile p.1).requirements p.2) :
    ∃ p ∈ insts, p.2 p.1.numVars = 1 ∧ p.1.conclusion p.2 = q := by
  have qChannel : q.channel ∈ channels source plan.singles root := by
    rcases required with rfl | ⟨p, hp, hq⟩
    · simp [channels]
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      simp only [channels, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inr ⟨p.1, W.chips p hp, s, hs, rfl⟩))
  have chipShape : ∀ c ∈ plan.singles, c.name = q.channel →
      Erasure.messageShape q = Erasure.signature c := by
    intro c hc name
    rcases required with rfl | ⟨p, hp, hq⟩
    · exact W.shaped.rootChip c hc name
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      rw [message_shape]
      exact W.shaped.calls p.1 (W.chips p hp) s hs c hc name
  have mapShape : ∀ mc ∈ source.mapClaims, mc.channel = q.channel →
      Erasure.messageShape mc = Erasure.messageShape q := by
    intro mc hmc name
    rcases required with rfl | ⟨p, hp, hq⟩
    · exact W.shaped.rootMaps mc hmc name
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      rw [message_shape]
      exact W.shaped.maps p.1 (W.chips p hp) s hs mc hmc name
  have idEq : ∀ x ∈ channels source plan.singles root, ∀ y ∈ channels source plan.singles root,
      (idOf x : F) = (idOf y : F) → x = y := fun x hx y hy h =>
    W.shaped.ids x hx y hy (W.small.inj (W.shaped.idBound x hx) (W.shaped.idBound y hy) h)
  set t := encode idOf q
  have bal := W.at t
  have romZero : ∀ e : F × WireValue F, encodeRom e ≠ t := by
    intro e h
    have := congrArg List.head? h
    simp [encode, t, encodeRom] at this
    exact W.call_ne_rom this.symm
  have mem0 : ∀ p, (memVals p t).sum = 0 := fun p => by
    apply List.sum_eq_zero; intro x hx
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    simp [romZero]
  have tables0 : tables t = 0 := by
    by_contra ne
    rcases W.tableSupport t ne with ⟨mc, hmc, eq⟩ | ⟨e, _, eq⟩
    · have ids := congrArg (fun l => l.tail.head?) eq
      simp [encode, t] at ids
      have same : q.channel = mc.channel := idEq _ qChannel _ (by
        simp only [channels, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨mc, hmc, rfl⟩)) ids
      have := encode_inj eq.symm same.symm (mapShape mc hmc same.symm)
      exact notStatic (this ▸ hmc)
    · exact romZero e eq.symm
  simp only [mem0, add_zero, tables0] at bal
  have split : (insts.map fun p => recvCoef idOf p t + (sendVals idOf p t).sum).sum =
      (insts.map fun p => recvCoef idOf p t).sum + (insts.map fun p => (sendVals idOf p t).sum).sum := by
    rw [← List.sum_map_add]
  rw [split] at bal
  have ySum : (insts.flatMap (fun p => sendVals idOf p t) ++
      [if encode idOf root = t then (1 : F) else 0]).sum ≠ 0 := by
    apply zero_one_sum W.small
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
        exact W.sendVals_bits hp t x hx
      · simp only [List.mem_singleton] at hx; split at hx <;> simp [hx]
    · rcases required with rfl | ⟨p, hp, hq⟩
      · simp [t]
      · obtain ⟨s, _, _, s', hs', enabled, msg⟩ := requirement_send hq
        refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨s', hs', ?_⟩⟩)
        simp [t, msg, enabled]
    · simpa using W.sendLength (t := t)
  rw [List.sum_append, List.sum_singleton, sum_flatMap'] at ySum
  have recvNe : (insts.map fun p => recvCoef idOf p t).sum ≠ 0 := by
    intro h
    apply ySum
    rw [h, zero_add] at bal
    exact bal
  obtain ⟨x, hx, ne⟩ := exists_ne_zero_of_sum recvNe
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  simp only [recvCoef] at ne
  split at ne
  · rename_i enc
    have mult : p.2 (p.1.numVars + 1) ≠ 0 := fun h => ne (by simp [h])
    have active : p.2 p.1.numVars = 1 := by
      have := (W.parts hp).2
      rcases mul_eq_zero.mp this with h | h
      · exact (sub_eq_zero.mp h).symm
      · exact absurd h mult
    refine ⟨p, hp, active, ?_⟩
    have ids := congrArg (fun l => l.tail.head?) enc
    simp [encode, t, Chip.conclusion] at ids
    have pChannel : p.1.name ∈ channels source plan.singles root := by
      simp only [channels, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨p.1, W.chips p hp, rfl⟩))
    have same : p.1.name = q.channel := idEq _ pChannel _ qChannel ids
    apply encode_inj enc same
    rw [conclusion_shape]
    exact (chipShape p.1 (W.chips p hp) same).symm
  · exact absurd rfl ne

omit W in
theorem find_single (plan : Grouping.Plan source id) {c : Chip F} (hc : c ∈ plan.singles) :
    plan.singles.find? (·.name == c.name) = some c := by
  cases found : plan.singles.find? (·.name == c.name) with
  | none =>
      have := List.find?_eq_none.mp found c hc
      simp at this
  | some c' =>
      have mem := List.mem_of_find?_eq_some found
      have name := List.find?_some found
      simp only [beq_iff_eq] at name
      have a := plan.certificate.1 c hc
      have b := plan.certificate.1 c' mem
      rw [name, a] at b
      rw [Option.some.inj b]

omit W in
theorem mapM_map_ok {α β γ ε : Type} (l : List α) (h : α → β) (f : β → Except ε γ) (k : α → γ)
    (ok : ∀ x ∈ l, f (h x) = .ok (k x)) : (l.map h).mapM f = .ok (l.map k) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.map_cons, List.mapM_cons, ok x (by simp),
        ih (fun y hy => ok y (by simp [hy]))]
      rfl

omit W in
theorem zip_fst {α β γ : Type} (g : α → β) :
    ∀ (xs : List α) (ys : List (β × γ)), ys.map Prod.fst = xs.map g →
      ∀ x ∈ xs.zip ys, x.2.1 = g x.1
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, hx => by simp at hx
  | a :: xs, b :: ys, h, x, hx => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact zip_fst g xs ys h.2 x hx

/-- Rows of the lowered chips with balanced lookups are accepted by the memo
checker of the plan, with integer weights chosen by `Balance.weigh`. -/
theorem Wide.checkMemo (activated : plan.WellFormedActivation)
    (context : source.checkContext rom root = .ok ()) :
    ∃ rows : List (WeightedRow F), rows.length ≤ insts.length ∧
      plan.checkMemo rom root rows = .ok () := by
  let actives := insts.filter fun p => p.2 p.1.numVars = 1
  let rowOf : Chip F × (Circuit.Var → F) → Circuit.Row F := fun p =>
    Row.ofAssignment p.1.name (p.1.numVars + 1) p.2
  let claimsOf : Chip F × (Circuit.Var → F) → RuleClaims (Message F) := fun p =>
    ((Activation.compile p.1).conclusion p.2, (Activation.compile p.1).requirements p.2)
  let rules := actives.map claimsOf
  let static : Message F → Bool := fun c => decide (source.MapClaim c)
  let weighted := Balance.weigh (Balance.required static root rules) rules
  have fst : weighted.map Prod.fst = actives.map claimsOf := Balance.weigh_rules _ _
  have len : weighted.length = actives.length := by
    simpa using congrArg List.length fst
  have activeMem : ∀ p ∈ actives, p ∈ insts ∧ p.2 p.1.numVars = 1 := fun p hp => by
    simpa [actives] using hp
  have weighOk : ∀ x ∈ actives.zip weighted,
      plan.weigh rom ⟨rowOf x.1, x.2.2⟩ = .ok (some x.2) := by
    intro x hx
    have hp := activeMem x.1 (List.of_mem_zip hx).1
    have claim := zip_fst claimsOf actives weighted fst x hx
    obtain ⟨formed, formedA⟩ := activated x.1.1 (W.chips _ hp.1)
    have finite := Chip.finiteAssignment formedA x.1.2 rom
    have valid : (Activation.compile x.1.1).ValidAssignment rom x.1.2 :=
      ⟨(W.parts hp.1).1, W.memory_valid hp.1⟩
    have check : (Activation.compile x.1.1).checkRow rom (rowOf x.1) = .ok (claimsOf x.1) := by
      apply Chip.checkRow_iff.mpr
      refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, (finite.1.mp valid)⟩, ?_⟩
      simp only [claimsOf]
      exact Prod.ext finite.2.1 finite.2.2
    have sel : (rowOf x.1).assignment x.1.1.numVars = 1 := by
      simp only [rowOf]
      rw [Row.ofAssignment_agree x.1.1.name (x.1.1.numVars + 1) x.1.2 x.1.1.numVars (Nat.lt_succ_self _)]
      exact hp.2
    have named : (rowOf x.1).chip = x.1.1.name := rfl
    simp only [Grouping.Plan.weigh, Grouping.Plan.inspectRow, named,
      find_single plan (W.chips _ hp.1), check, sel, ite_true]
    rw [show x.2 = (x.2.1, x.2.2) from rfl, claim]
  let rows : List (WeightedRow F) := (actives.zip weighted).map fun x => ⟨rowOf x.1, x.2.2⟩
  have mapped : rows.mapM (plan.weigh rom) = .ok (weighted.map some) := by
    have := mapM_map_ok (actives.zip weighted) (fun x => (⟨rowOf x.1, x.2.2⟩ : WeightedRow F))
      (plan.weigh rom) (fun x => some x.2) weighOk
    rw [this, show (fun x : (Chip F × (Circuit.Var → F)) × (RuleClaims (Message F) × Int) => some x.2) =
      some ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by omega)]
  have active : Grouping.activeRules (weighted.map some) = weighted := by
    simp [Grouping.activeRules, List.filterMap_map]
  have covered : ∀ claim ∈ Balance.required static root rules, ∃ rule ∈ rules, rule.1 = claim := by
    intro claim hclaim
    simp only [Balance.required, List.mem_filter, Bool.not_eq_true', static,
      decide_eq_false_iff_not] at hclaim
    obtain ⟨member, notStatic⟩ := hclaim
    have required : claim = root ∨ ∃ p ∈ insts, claim ∈ (Activation.compile p.1).requirements p.2 := by
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · obtain ⟨rule, hrule, hc⟩ := List.mem_flatMap.mp member
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrule
        exact Or.inr ⟨p, (activeMem p hp).1, hc⟩
    obtain ⟨p, hp, act, conc⟩ := W.provider notStatic required
    exact ⟨claimsOf p, List.mem_map.mpr ⟨p, by simp [actives, hp, act], rfl⟩, conc⟩
  refine ⟨rows, by simp [rows, len]; exact List.length_filter_le _ _, ?_⟩
  have zero := Balance.weigh_balanced (static := static) (root := root) covered
  simp only [Grouping.Plan.checkMemo, context, mapped, active]
  simp only [weighted]
  simp [static] at zero ⊢
  exact zero

end Main



end Aiur.Tiling.Bridge
