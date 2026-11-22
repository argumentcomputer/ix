import Aiur.Tiling.Compiled
import Aiur.Library.Field.BN254.Prime

/-!
# Grouped circuits

`lowerGroup g` is the lookup circuit of a checked function group
(`Grouping.Layout`), as the STARK backends build it from the trace's group
record (`circuits.rs`, `grouping.rs`): main width `g.width + 1` (the last
column is the receive multiplicity), the group's constraints and
`(1 − activation)·mult = 0`, the receive `push(−mult, receive)` and one
`push(enable, args)` per shared send slot.

Group messages are zero-padded to the longest member's, so a group row's
tuples equal the selected member's only up to trailing zeros. The balance the
theorems take is therefore the multi-stark one, keyed by `trimZeros`
(`Trim.lean`): `mapDomain trimZeros (…) = 0`.

A group row with activation `0` has zero multiplicity and silent sends
(`Checked.padding_sound`); one with activation `1` has a selected member `m`,
and its trimmed ledger is the trimmed ledger of `m`'s activated chip at the
projected assignment (`Checked` packets). So every grouped stage reduces to
*virtual single rows* `(chip, assignment, multiplicity)` (`Inst`), and
`WideT` is `Bridge.Wide` over virtual rows with the trimmed balance. Memo rows
of virtual rows of a group are the group's own rows, which
`Grouping.Plan.checkMemo` inspects through the layout.
-/

namespace Aiur.Tiling.Grouped

open Aiur.Circuit
open Aiur.Optimized
open Bridge

variable {F : Type} [Field F] [DecidableEq F]

/-! ## The lowering -/

/-- The lookup circuit of a checked group; variable `g.width` is the receive
multiplicity. -/
def lowerGroup (g : Grouping.Layout F) : Tiling.Circuit F where
  width := g.width + 1
  constraints := g.constraints ++ [.mul (.sub (.const 1) g.activation) (.var g.width)]
  lookups := ⟨.sub (.const 0) (.var g.width), g.receive⟩ ::
    g.sends.map fun s => ⟨s.enable, s.args⟩

/-! ## Trailing zeros -/

omit [DecidableEq F] in
theorem getD_cons_succ (a : F) (t : List F) (i : Nat) : (a :: t).getD (i + 1) 0 = t.getD i 0 := by
  simp [List.getD_eq_getElem?_getD]

omit [DecidableEq F] in
theorem getD_cons_zero (a : F) (t : List F) : (a :: t).getD 0 0 = a := by
  simp [List.getD_eq_getElem?_getD]

omit [DecidableEq F] in
theorem getD_nil (i : Nat) : ([] : List F).getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem trimZeros_eq_nil : ∀ {t : List F}, trimZeros t = [] ↔ ∀ i, t.getD i 0 = 0
  | [] => by simp [trimZeros, getD_nil]
  | a :: t => by
      simp only [trimZeros]
      constructor
      · intro h
        split at h
        · rename_i hz
          intro i
          cases i with
          | zero => rw [getD_cons_zero]; exact hz.1
          | succ i => rw [getD_cons_succ]; exact trimZeros_eq_nil.mp hz.2 i
        · simp at h
      · intro h
        have a0 : a = 0 := by simpa [getD_cons_zero] using h 0
        have rest : trimZeros t = [] := trimZeros_eq_nil.mpr fun i => by
          simpa [getD_cons_succ] using h (i + 1)
        simp [a0, rest]

/-- Two tuples meet on the multi-stark bus exactly when they agree as
zero-extended sequences. -/
theorem trimZeros_eq_iff : ∀ {t u : List F}, trimZeros t = trimZeros u ↔ ∀ i, t.getD i 0 = u.getD i 0
  | [], u => by
      rw [show trimZeros ([] : List F) = [] from rfl, eq_comm, trimZeros_eq_nil]
      simp [getD_nil, eq_comm]
  | a :: t, [] => by
      rw [show trimZeros ([] : List F) = [] from rfl, trimZeros_eq_nil]
      simp [getD_nil]
  | a :: t, b :: u => by
      have split : (∀ i, (a :: t).getD i 0 = (b :: u).getD i 0) ↔
          a = b ∧ ∀ i, t.getD i 0 = u.getD i 0 := by
        constructor
        · intro h
          exact ⟨by simpa [getD_cons_zero] using h 0, fun i => by simpa [getD_cons_succ] using h (i + 1)⟩
        · rintro ⟨rfl, h⟩ i
          cases i with
          | zero => rfl
          | succ i => simpa [getD_cons_succ] using h i
      rw [split, ← trimZeros_eq_iff (t := t) (u := u)]
      simp only [trimZeros]
      split <;> split
      · rename_i ha hb
        simp [ha.1, hb.1, ha.2, hb.2]
      · rename_i ha hb
        simp only [List.nil_eq, reduceCtorEq, false_iff, not_and]
        intro e
        subst e
        intro rest
        exact hb ⟨ha.1, rest ▸ ha.2⟩
      · rename_i ha hb
        simp only [reduceCtorEq, false_iff, not_and]
        intro e
        subst e
        intro rest
        exact ha ⟨hb.1, rest.symm ▸ hb.2⟩
      · simp

omit [DecidableEq F] in
/-- `word` (zero-extended reads of an argument list) at an assignment. -/
theorem word_denote (ps : List (Scalar.Circuit.ArithExpr F)) (a : Nat → F) (i : Nat) :
    (Grouping.word ps i).denote a = (ps.map (·.denote a)).getD i 0 := by
  simp only [Grouping.word, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[i]? <;> simp [Scalar.Circuit.ArithExpr.denote]

theorem trim_of_words {ps qs : List (Scalar.Circuit.ArithExpr F)} {a b : Nat → F}
    (h : ∀ i, (Grouping.word ps i).denote a = (Grouping.word qs i).denote b) :
    trimZeros (ps.map (·.denote a)) = trimZeros (qs.map (·.denote b)) :=
  trimZeros_eq_iff.mpr fun i => by rw [← word_denote, ← word_denote]; exact h i

/-! ## Ledgers of tuple lists -/

noncomputable def pairsLedger (xs : List (List F × F)) : Ledger F :=
  (xs.map fun x => Finsupp.single x.1 x.2).sum

theorem pairsLedger_zero : ∀ {xs : List (List F × F)}, (∀ i, (xs.getD i ([], 0)).2 = 0) →
    pairsLedger xs = 0
  | [], _ => by simp [pairsLedger]
  | x :: xs, h => by
      have hx : x.2 = 0 := by simpa using h 0
      have rest := pairsLedger_zero (xs := xs) fun i => by simpa using h (i + 1)
      simp only [pairsLedger, List.map_cons, List.sum_cons] at rest ⊢
      rw [rest, hx]
      simp

/-- Lists that agree position by position (zero-extended) in multiplicity and
trimmed tuple have the same trimmed ledger. -/
theorem pairsLedger_trim : ∀ {xs ys : List (List F × F)},
    (∀ i, (xs.getD i ([], 0)).2 = (ys.getD i ([], 0)).2 ∧
      trimZeros (xs.getD i ([], 0)).1 = trimZeros (ys.getD i ([], 0)).1) →
    Finsupp.mapDomain trimZeros (pairsLedger xs) = Finsupp.mapDomain trimZeros (pairsLedger ys)
  | [], ys, h => by
      rw [pairsLedger_zero (xs := ys) fun i => by simpa using (h i).1.symm]
      simp [pairsLedger]
  | x :: xs, [], h => by
      rw [pairsLedger_zero (xs := x :: xs) fun i => by simpa using (h i).1]
      simp [pairsLedger]
  | x :: xs, y :: ys, h => by
      have head := h 0
      simp only [List.getD_cons_zero] at head
      have rest := pairsLedger_trim (xs := xs) (ys := ys) fun i => by simpa using h (i + 1)
      simp only [pairsLedger, List.map_cons, List.sum_cons, Finsupp.mapDomain_add,
        Finsupp.mapDomain_single] at rest ⊢
      rw [rest, head.1, head.2]

/-! ## Virtual single rows -/

/-- A virtual single row: a chip, the activated chip's assignment and the
receive multiplicity. -/
abbrev Inst (F : Type) := Chip F × (Var → F) × F

/-- The lookups of the lowered chip at a virtual row (`Bridge.lower` with
the receive multiplicity replaced by `p.2.2`). -/
noncomputable def instLedger (idOf : String → Nat) (p : Inst F) : Ledger F :=
  Finsupp.single (encode idOf (p.1.conclusion p.2.1)) (-p.2.2) +
    ((Activation.compile p.1).sends.map fun s =>
      Finsupp.single (encode idOf (s.message p.2.1)) (s.enable.denote p.2.1)).sum +
    ((Activation.compile p.1).memory.map fun m =>
      Finsupp.single (encodeRom (m.address.denote p.2.1, m.value.map (Circuit.ArithExpr.denote p.2.1)))
        (m.enable.denote p.2.1)).sum

theorem lower_instLedger (idOf : String → Nat) (c : Chip F) (w : Var → F) :
    (Bridge.lower idOf c).rowLedger w = instLedger idOf (c, w, w (c.numVars + 1)) := by
  ext t
  rw [lower_apply idOf (c, w) t]
  simp only [instLedger, Finsupp.add_apply, Tiling.System.ledger_list_sum, List.map_map,
    recvCoef, sendVals, memVals, Finsupp.single_apply, Function.comp_def]

/-! ## Trimmed coefficients -/

def recvK (idOf : String → Nat) (p : Inst F) (k : List F) : F :=
  if trimZeros (encode idOf (p.1.conclusion p.2.1)) = k then -p.2.2 else 0

def sendK (idOf : String → Nat) (p : Inst F) (k : List F) : List F :=
  (Activation.compile p.1).sends.map fun s =>
    if trimZeros (encode idOf (s.message p.2.1)) = k then s.enable.denote p.2.1 else 0

def memK (p : Inst F) (k : List F) : List F :=
  (Activation.compile p.1).memory.map fun m =>
    if trimZeros (encodeRom (m.address.denote p.2.1, m.value.map (Circuit.ArithExpr.denote p.2.1))) = k
    then m.enable.denote p.2.1 else 0

theorem mapDomain_list_sum {α : Type} (f : List F → List F) (l : List α) (g : α → Ledger F) :
    Finsupp.mapDomain f (l.map g).sum = (l.map fun x => Finsupp.mapDomain f (g x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [Finsupp.mapDomain_add, ih]

theorem instLedger_trim (idOf : String → Nat) (p : Inst F) (k : List F) :
    Finsupp.mapDomain trimZeros (instLedger idOf p) k =
      recvK idOf p k + (sendK idOf p k).sum + (memK p k).sum := by
  simp only [instLedger, Finsupp.mapDomain_add, mapDomain_list_sum, Finsupp.mapDomain_single,
    Finsupp.add_apply, Tiling.System.ledger_list_sum, List.map_map, Function.comp_def,
    Finsupp.single_apply, recvK, sendK, memK]

/-- A nonzero trimmed entry of a ledger comes from a nonzero entry. -/
theorem exists_of_mapDomain {L : Ledger F} {k : List F}
    (h : Finsupp.mapDomain trimZeros L k ≠ 0) : ∃ u, L u ≠ 0 ∧ trimZeros u = k := by
  have mem : k ∈ (Finsupp.mapDomain trimZeros L).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨u, hu, e⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support mem)
  exact ⟨u, Finsupp.mem_support_iff.mp hu, e⟩

omit [DecidableEq F] in
theorem encode_getD_one (idOf : String → Nat) (m : Message F) :
    (encode idOf m).getD 1 0 = (idOf m.channel : F) := by
  simp [encode, List.getD_eq_getElem?_getD]

omit [DecidableEq F] in
theorem encodeRom_getD_one (e : F × WireValue F) :
    (encodeRom e).getD 1 0 = (e.2.words.length : F) := by
  simp [encodeRom, List.getD_eq_getElem?_getD]

omit [DecidableEq F] in
theorem encode_length (idOf : String → Nat) {m m' : Message F}
    (shapes : Erasure.messageShape m = Erasure.messageShape m') :
    (encode idOf m).length = (encode idOf m').length := by
  simp only [Erasure.messageShape, Prod.mk.injEq] at shapes
  have args := congrArg (fun l => (l.map Prod.snd).sum) shapes.1
  have result := congrArg Prod.snd shapes.2
  simp only [List.map_map, Function.comp_def, Erasure.shape] at args result
  simp only [encode, List.length_cons, List.length_append, List.length_flatMap, result]
  simp only [args]

/-! ## The trimmed bridge -/

section Main

variable {source : Circuit.System F}

/-- Virtual single rows over `chips`, with the multi-stark (trimmed) balance. -/
structure WideT (source : Circuit.System F) (chips : List (Chip F)) (idOf : String → Nat)
    (bound : Nat) (rom : WireROM F) (root : Message F) (insts : List (Inst F))
    (tables : Ledger F) : Prop where
  chipsIn : ∀ p ∈ insts, p.1 ∈ chips
  sat : ∀ p ∈ insts, Scalar.Circuit.Satisfies (Activation.compile p.1).constraints p.2.1
  mult : ∀ p ∈ insts, (1 - p.2.1 p.1.numVars) * p.2.2 = 0
  small : SmallCast F bound
  enablesOk : ∀ c ∈ chips, checkEnables bound c = true
  tags : 2 < bound
  count : (insts.map fun p => p.1.sends.length + p.1.memory.length).sum + 1 < bound
  shaped : Shaped source chips idOf root bound
  romPacked : ∀ e ∈ rom.entries, e.2.type = .tuple (List.replicate e.2.words.length .field)
  romWidth : ∀ e ∈ rom.entries, e.2.words.length < bound
  memWidth : ∀ c ∈ chips, ∀ m ∈ c.memory, m.value.words.length < bound
  tableSupport : ∀ t, tables t ≠ 0 →
    (∃ mc ∈ source.mapClaims, t = encode idOf mc) ∨ ∃ e ∈ rom.entries, t = encodeRom e
  balanced : Finsupp.mapDomain trimZeros
    ((insts.map (instLedger idOf)).sum + Finsupp.single (encode idOf root) 1 + tables) = 0

variable {chips : List (Chip F)} {idOf : String → Nat} {bound : Nat} {rom : WireROM F}
  {root : Message F} {insts : List (Inst F)} {tables : Ledger F}
  (W : WideT source chips idOf bound rom root insts tables)
include W

theorem WideT.at (k : List F) :
    (insts.map fun p => recvK idOf p k + (sendK idOf p k).sum + (memK p k).sum).sum +
      (if trimZeros (encode idOf root) = k then 1 else 0) +
      Finsupp.mapDomain trimZeros tables k = 0 := by
  have := congrArg (fun x : Ledger F => x k) W.balanced
  simp only [Finsupp.mapDomain_add, mapDomain_list_sum, Finsupp.add_apply, Finsupp.coe_zero,
    Pi.zero_apply, Tiling.System.ledger_list_sum, List.map_map, Function.comp_def,
    Finsupp.mapDomain_single, Finsupp.single_apply, instLedger_trim] at this
  exact this

theorem WideT.boolean {p : Inst F} (hp : p ∈ insts) : Boolean p.1 p.2.1 :=
  boolean_of_checkEnables W.small (W.enablesOk _ (W.chipsIn p hp)) (W.sat p hp)

theorem WideT.call_ne_rom : (Bridge.CALL : F) ≠ (Bridge.ROM : F) := by
  intro h
  have := W.small.inj (a := Bridge.CALL) (b := Bridge.ROM) (by simp [Bridge.CALL]; have := W.tags; omega)
    (by simp [Bridge.ROM]; exact W.tags) h
  simp [Bridge.CALL, Bridge.ROM] at this

theorem WideT.call_ne_zero : (Bridge.CALL : F) ≠ 0 := by simp [Bridge.CALL]

theorem WideT.rom_ne_zero : (Bridge.ROM : F) ≠ 0 := by
  intro h
  have := W.small Bridge.ROM (by simp [Bridge.ROM]; exact W.tags) h
  simp [Bridge.ROM] at this

/-- A message tuple and a ROM tuple never meet. -/
theorem WideT.call_rom (m : Message F) (e : F × WireValue F) :
    trimZeros (encode idOf m) ≠ trimZeros (encodeRom e) := by
  intro h
  have := trimZeros_head h (by simp [encode]) W.call_ne_zero
  simp [encodeRom] at this
  exact W.call_ne_rom this.symm

theorem WideT.memK_bits {p : Inst F} (hp : p ∈ insts) (k : List F) :
    ∀ x ∈ memK p k, x = 0 ∨ x = 1 := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  split
  · exact (W.boolean hp).2 m hm
  · exact Or.inl rfl

theorem WideT.sendK_bits {p : Inst F} (hp : p ∈ insts) (k : List F) :
    ∀ x ∈ sendK idOf p k, x = 0 ∨ x = 1 := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  split
  · exact (W.boolean hp).1 s hs
  · exact Or.inl rfl

theorem WideT.memLength (k : List F) : (insts.flatMap fun p => memK p k).length < bound := by
  have := W.count
  simp only [List.length_flatMap, memK, List.length_map, Activation.compile] at *
  have le : (insts.map fun p => p.1.memory.length).sum ≤
      (insts.map fun p => p.1.sends.length + p.1.memory.length).sum :=
    nat_sum_map_le _ (fun p _ => Nat.le_add_left _ _)
  omega

theorem WideT.sendLength (k : List F) :
    (insts.flatMap (fun p => sendK idOf p k) ++ [(0 : F)]).length < bound := by
  have := W.count
  simp only [List.length_append, List.length_flatMap, sendK, List.length_map, Activation.compile,
    List.length_singleton] at *
  have le : (insts.map fun p => p.1.sends.length).sum ≤
      (insts.map fun p => p.1.sends.length + p.1.memory.length).sum :=
    nat_sum_map_le _ (fun p _ => Nat.le_add_right _ _)
  omega

/-- Every enabled memory lookup of a virtual row reads an entry of the ROM. -/
theorem WideT.memory_valid {p : Inst F} (hp : p ∈ insts) :
    ∀ m ∈ (Activation.compile p.1).memory, MemoryLookup.Valid rom p.2.1 m := by
  intro m hm enabled
  set x := (m.address.denote p.2.1, m.value.map (Circuit.ArithExpr.denote p.2.1))
  set k := trimZeros (encodeRom x)
  have bal := W.at k
  have recv0 : ∀ q, recvK idOf q k = 0 := fun q => by simp [recvK, k, W.call_rom]
  have send0 : ∀ q, (sendK idOf q k).sum = 0 := fun q => by
    apply List.sum_eq_zero; intro y hy
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hy
    simp [k, W.call_rom]
  simp only [recv0, send0, zero_add, k, W.call_rom, ite_false, add_zero] at bal
  have sumNe : (insts.flatMap fun q => memK q k).sum ≠ 0 := by
    apply zero_one_sum W.small
    · intro y hy
      obtain ⟨q, hq, hy⟩ := List.mem_flatMap.mp hy
      exact W.memK_bits hq k y hy
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨m, hm, by simp [k, x, enabled]⟩⟩
    · exact W.memLength k
  rw [sum_flatMap'] at sumNe
  have tablesNe : Finsupp.mapDomain trimZeros tables k ≠ 0 := by
    intro h; rw [h, add_zero] at bal; exact sumNe bal
  obtain ⟨u, hu, eu⟩ := exists_of_mapDomain tablesNe
  have typeM : m.value.type = .tuple (List.replicate m.value.words.length .field) ∧
      m.value.words.length < bound := by
    simp only [Activation.compile, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨W.shaped.memory p.1 (W.chipsIn p hp) m0 hm0, W.memWidth p.1 (W.chipsIn p hp) m0 hm0⟩
  rcases W.tableSupport u hu with ⟨mc, _, eq⟩ | ⟨e, he, eq⟩
  · subst eq; exact absurd eu (W.call_rom mc x)
  · subst eq
    have one := trimZeros_eq_iff.mp eu 1
    rw [encodeRom_getD_one, encodeRom_getD_one] at one
    have wlen : e.2.words.length = x.2.words.length :=
      W.small.inj (W.romWidth e he) (by simpa [x, WireValue.map] using typeM.2) one
    have same : encodeRom e = encodeRom x :=
      trimZeros_inj_of_length (by simp [encodeRom, wlen]) eu
    simp only [encodeRom, List.cons.injEq] at same
    obtain ⟨_, _, addr, words⟩ := same
    have : e = x := by
      obtain ⟨ea, ev⟩ := e
      simp only at addr words
      have ty := W.romPacked _ he
      simp only at ty
      cases ev
      simp only [x, WireValue.map, WireValue.mk.injEq, Prod.mk.injEq] at *
      refine ⟨addr, ?_, words⟩
      rw [ty, typeM.1, words]; simp
    rw [← this]; exact he

/-- A claim the memo checker requires, other than a fixed-table claim, is the
conclusion of some active virtual row. -/
theorem WideT.provider {q : Message F} (notStatic : ¬ source.MapClaim q)
    (required : q = root ∨ ∃ p ∈ insts, q ∈ (Activation.compile p.1).requirements p.2.1) :
    ∃ p ∈ insts, p.2.1 p.1.numVars = 1 ∧ p.1.conclusion p.2.1 = q := by
  have qChannel : q.channel ∈ channels source chips root := by
    rcases required with rfl | ⟨p, hp, hq⟩
    · simp [channels]
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      simp only [channels, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inr ⟨p.1, W.chipsIn p hp, s, hs, rfl⟩))
  have chipShape : ∀ c ∈ chips, c.name = q.channel →
      Erasure.messageShape q = Erasure.signature c := by
    intro c hc name
    rcases required with rfl | ⟨p, hp, hq⟩
    · exact W.shaped.rootChip c hc name
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      rw [message_shape]
      exact W.shaped.calls p.1 (W.chipsIn p hp) s hs c hc name
  have mapShape : ∀ mc ∈ source.mapClaims, mc.channel = q.channel →
      Erasure.messageShape mc = Erasure.messageShape q := by
    intro mc hmc name
    rcases required with rfl | ⟨p, hp, hq⟩
    · exact W.shaped.rootMaps mc hmc name
    · obtain ⟨s, hs, rfl, _⟩ := requirement_send hq
      rw [message_shape]
      exact W.shaped.maps p.1 (W.chipsIn p hp) s hs mc hmc name
  have idEq : ∀ x ∈ channels source chips root, ∀ y ∈ channels source chips root,
      (idOf x : F) = (idOf y : F) → x = y := fun x hx y hy h =>
    W.shaped.ids x hx y hy (W.small.inj (W.shaped.idBound x hx) (W.shaped.idBound y hy) h)
  set k := trimZeros (encode idOf q)
  have bal := W.at k
  have mem0 : ∀ p, (memK p k).sum = 0 := fun p => by
    apply List.sum_eq_zero; intro x hx
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    have := W.call_rom q (m.address.denote p.2.1, m.value.map (Circuit.ArithExpr.denote p.2.1))
    simp [k, Ne.symm this]
  have tables0 : Finsupp.mapDomain trimZeros tables k = 0 := by
    by_contra ne
    obtain ⟨u, hu, eu⟩ := exists_of_mapDomain ne
    rcases W.tableSupport u hu with ⟨mc, hmc, eq⟩ | ⟨e, _, eq⟩
    · subst eq
      have ids := trimZeros_eq_iff.mp eu 1
      rw [encode_getD_one, encode_getD_one] at ids
      have same : mc.channel = q.channel := idEq _ (by
        simp only [channels, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨mc, hmc, rfl⟩)) _ qChannel ids
      have shapes := mapShape mc hmc same
      have eqT := trimZeros_inj_of_length (encode_length idOf shapes) eu
      exact notStatic (encode_inj eqT same shapes ▸ hmc)
    · subst eq; exact W.call_rom q e eu.symm
  simp only [mem0, add_zero, tables0] at bal
  have split : (insts.map fun p => recvK idOf p k + (sendK idOf p k).sum).sum =
      (insts.map fun p => recvK idOf p k).sum + (insts.map fun p => (sendK idOf p k).sum).sum := by
    rw [← List.sum_map_add]
  rw [split] at bal
  have ySum : (insts.flatMap (fun p => sendK idOf p k) ++
      [if trimZeros (encode idOf root) = k then (1 : F) else 0]).sum ≠ 0 := by
    apply zero_one_sum W.small
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
        exact W.sendK_bits hp k x hx
      · simp only [List.mem_singleton] at hx; split at hx <;> simp [hx]
    · rcases required with rfl | ⟨p, hp, hq⟩
      · simp [k]
      · obtain ⟨s, _, _, s', hs', enabled, msg⟩ := requirement_send hq
        refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨s', hs', ?_⟩⟩)
        simp [k, msg, enabled]
    · simpa using W.sendLength k
  rw [List.sum_append, List.sum_singleton, sum_flatMap'] at ySum
  have recvNe : (insts.map fun p => recvK idOf p k).sum ≠ 0 := by
    intro h
    apply ySum
    rw [h, zero_add] at bal
    exact bal
  obtain ⟨x, hx, ne⟩ := exists_ne_zero_of_sum recvNe
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  simp only [recvK] at ne
  split at ne
  · rename_i enc
    have mult : p.2.2 ≠ 0 := fun h => ne (by simp [h])
    have active : p.2.1 p.1.numVars = 1 := by
      have := W.mult p hp
      rcases mul_eq_zero.mp this with h | h
      · exact (sub_eq_zero.mp h).symm
      · exact absurd h mult
    refine ⟨p, hp, active, ?_⟩
    have ids := trimZeros_eq_iff.mp enc 1
    rw [encode_getD_one, encode_getD_one] at ids
    have pChannel : p.1.name ∈ channels source chips root := by
      simp only [channels, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨p.1, W.chipsIn p hp, rfl⟩))
    have same : p.1.name = q.channel := idEq _ pChannel _ qChannel (by simpa [Chip.conclusion] using ids)
    have shapes : Erasure.messageShape (p.1.conclusion p.2.1) = Erasure.messageShape q := by
      rw [conclusion_shape]
      exact (chipShape p.1 (W.chipsIn p hp) same).symm
    exact encode_inj (trimZeros_inj_of_length (encode_length idOf shapes) enc) same shapes
  · exact absurd rfl ne

/-- Virtual rows with a trimmed balance are accepted by the memo checker of
the plan, given, for every active row whose memory lookups are valid, a
physical row the plan inspects to its rule. -/
theorem WideT.checkMemo {id : String → Except String Nat} (plan : Grouping.Plan source id)
    (context : source.checkContext rom root = .ok ())
    (rowOf : ∀ p ∈ insts, p.2.1 p.1.numVars = 1 →
      (∀ m ∈ (Activation.compile p.1).memory, MemoryLookup.Valid rom p.2.1 m) →
      ∃ row, plan.inspectRow rom row =
        .ok (some ((Activation.compile p.1).conclusion p.2.1, (Activation.compile p.1).requirements p.2.1))) :
    ∃ rows : List (WeightedRow F), rows.length ≤ insts.length ∧
      plan.checkMemo rom root rows = .ok () := by
  classical
  let actives := insts.filter fun p => p.2.1 p.1.numVars = 1
  let claimsOf : Inst F → RuleClaims (Message F) := fun p =>
    ((Activation.compile p.1).conclusion p.2.1, (Activation.compile p.1).requirements p.2.1)
  have activeMem : ∀ p ∈ actives, p ∈ insts ∧ p.2.1 p.1.numVars = 1 := fun p hp => by
    simpa [actives] using hp
  let rowFor : Inst F → Circuit.Row F := fun p =>
    if h : p ∈ insts ∧ p.2.1 p.1.numVars = 1 then
      Classical.choose (rowOf p h.1 h.2 (W.memory_valid h.1)) else ⟨"", []⟩
  have rowFor_spec : ∀ p ∈ actives, plan.inspectRow rom (rowFor p) = .ok (some (claimsOf p)) := by
    intro p hp
    have h := activeMem p hp
    simp only [rowFor, h, and_self, dite_true]
    exact Classical.choose_spec (rowOf p h.1 h.2 (W.memory_valid h.1))
  let rules := actives.map claimsOf
  let static : Message F → Bool := fun c => decide (source.MapClaim c)
  let weighted := Balance.weigh (Balance.required static root rules) rules
  have fst : weighted.map Prod.fst = actives.map claimsOf := Balance.weigh_rules _ _
  have len : weighted.length = actives.length := by
    simpa using congrArg List.length fst
  have weighOk : ∀ x ∈ actives.zip weighted,
      plan.weigh rom ⟨rowFor x.1, x.2.2⟩ = .ok (some x.2) := by
    intro x hx
    have hp := (List.of_mem_zip hx).1
    have claim := zip_fst claimsOf actives weighted fst x hx
    simp only [Grouping.Plan.weigh, rowFor_spec x.1 hp]
    rw [show x.2 = (x.2.1, x.2.2) from rfl, claim]
  let rows : List (WeightedRow F) := (actives.zip weighted).map fun x => ⟨rowFor x.1, x.2.2⟩
  have mapped : rows.mapM (plan.weigh rom) = .ok (weighted.map some) := by
    have := mapM_map_ok (actives.zip weighted) (fun x => (⟨rowFor x.1, x.2.2⟩ : WeightedRow F))
      (plan.weigh rom) (fun x => some x.2) weighOk
    rw [this, show (fun x : Inst F × (RuleClaims (Message F) × Int) => some x.2) =
      some ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by omega)]
  have active : Grouping.activeRules (weighted.map some) = weighted := by
    simp [Grouping.activeRules, List.filterMap_map]
  have covered : ∀ claim ∈ Balance.required static root rules, ∃ rule ∈ rules, rule.1 = claim := by
    intro claim hclaim
    simp only [Balance.required, List.mem_filter, Bool.not_eq_true', static,
      decide_eq_false_iff_not] at hclaim
    obtain ⟨member, notStatic⟩ := hclaim
    have required : claim = root ∨ ∃ p ∈ insts, claim ∈ (Activation.compile p.1).requirements p.2.1 := by
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

/-! ## Group rows -/

section Groups

variable {sources : List (Chip F)} {id : String → Except String Nat}

/-- The lookups of a group row as tuple/multiplicity pairs. -/
def groupPairs (g : Grouping.Layout F) (a : Var → F) : List (List F × F) :=
  (g.receive.map (·.denote a), -a g.width) ::
    g.sends.map fun s => (s.args.map (·.denote a), s.enable.denote a)

theorem lowerGroup_rowLedger (g : Grouping.Layout F) (a : Var → F) :
    (lowerGroup g).rowLedger a = pairsLedger (groupPairs g a) := by
  simp [Tiling.Circuit.rowLedger, lowerGroup, Lookup.entry, Lookup.tuple, pairsLedger, groupPairs,
    List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]

/-- The lookups of a virtual row as tuple/multiplicity pairs. -/
def instPairs (idOf : String → Nat) (p : Inst F) : List (List F × F) :=
  (encode idOf (p.1.conclusion p.2.1), -p.2.2) ::
    ((Activation.compile p.1).sends.map (fun s => (encode idOf (s.message p.2.1), s.enable.denote p.2.1)) ++
      (Activation.compile p.1).memory.map fun m =>
        (encodeRom (m.address.denote p.2.1, m.value.map (Circuit.ArithExpr.denote p.2.1)),
          m.enable.denote p.2.1))

theorem instLedger_pairs (idOf : String → Nat) (p : Inst F) :
    instLedger idOf p = pairsLedger (instPairs idOf p) := by
  simp [instLedger, pairsLedger, instPairs, List.map_map, Function.comp_def, add_assoc]

omit [DecidableEq F] in
theorem getD_map_default {α : Type} (l : List α) (f : α → List F × F) (d : α) (i : Nat)
    (hd : f d = ([], 0)) : (l.map f).getD i ([], 0) = f (l[i]?.getD d) := by
  rw [← hd, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- What `Grouping.messages` emits, in the encoding of `Bridge.lower`. -/
theorem messages_ok (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) {c : Chip F}
    {provided : List (Scalar.Circuit.ArithExpr F)} {required : List (Grouping.Lookup F)}
    (h : Grouping.messages id c = .ok (provided, required)) :
    provided = (receiveLookup idOf c 0).args ∧
      required.map (fun l => (l.enable, l.args)) =
        c.sends.map (fun s => (s.enable, (sendLookup idOf s).args)) ++
          c.memory.map fun m => (m.enable, (memoryLookup m).args) := by
  unfold Grouping.messages at h
  cases hc : id c.name with
  | error e => simp [hc, bind, Except.bind] at h
  | ok call =>
      simp only [hc, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i sends hs
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have callEq := idOk _ _ hc
        subst callEq
        refine ⟨by simp [receiveLookup, Bridge.CALL], ?_⟩
        rw [List.map_append]
        congr 1
        · have rel := mapM_ok_iff.mp hs
          clear hs hc
          revert rel
          generalize c.sends = l
          intro rel
          induction rel with
          | nil => rfl
          | @cons s l ss ls head _ ih =>
              simp only [List.map_cons, ih]
              split at head
              · cases head
              · rename_i callee hch
                simp only [Except.ok.injEq] at head
                subst head
                have := idOk _ _ hch
                subst this
                simp [sendLookup, Bridge.CALL]
        · simp [List.map_map, Function.comp_def, memoryLookup, Bridge.ROM]

/-- `Checked.packet_sound` without the memory part of `ValidRow`. -/
theorem packet_active (checked : Grouping.Checked sources id) (m : Grouping.Member F)
    (hm : m ∈ checked.layout.members) (a : Nat → F)
    (valid : Scalar.Circuit.Satisfies checked.layout.constraints a)
    (act : checked.layout.activation.denote a = 1) (active : a m.selector = 1) :
    (∀ n ∈ checked.layout.members, a n.selector = Grouping.selected (some m.selector) n) ∧
    ∃ provided required, Grouping.messages id m.origin = .ok (provided, required) ∧
      Grouping.SamePackets checked.layout a provided required (fun v => a (m.columns[v]?.getD 0)) := by
  obtain ⟨n, hn, _, selectors⟩ := checked.layout.select checked.certificate.shapes a valid act
  have sameSelector : n.selector = m.selector := by
    have h := selectors m hm
    by_contra hne
    simp [Grouping.selected, hne, active] at h
  have same := checked.certificate.unique n hn m hm sameSelector
  subst n
  refine ⟨selectors, ?_⟩
  have back := checked.layout.back_sound checked.certificate.shapes a valid (some m.selector) selectors
  have hc := checked.packets m hm
  unfold Grouping.Member.PacketCertificate at hc
  cases result : Grouping.messages id m.origin with
  | error error => simp [result] at hc
  | ok pair =>
      obtain ⟨provided, required⟩ := pair
      simp only [result] at hc
      refine ⟨provided, required, rfl, ?_⟩
      simpa only [back, Grouping.Member.project, Scalar.Circuit.ArithExpr.denote] using hc.1.sound a

/-- The projected assignment of member `m`. -/
def project (m : Grouping.Member F) (a : Var → F) : Var → F := fun v => a (m.columns[v]?.getD 0)

/-- The virtual row of member `m` at group row `a`. -/
def memberInst (g : Grouping.Layout F) (m : Grouping.Member F) (a : Var → F) : Inst F :=
  (m.origin, project m a, a g.width)

theorem project_selector (checked : Grouping.Checked sources id) {m : Grouping.Member F}
    (hm : m ∈ checked.layout.members) (a : Var → F) :
    project m a m.origin.numVars = a m.selector := by
  simp only [project]
  rw [(checked.certificate.shapes m hm).1]
  rfl

/-- The activated source chip's constraints hold at the selected member's
projection. -/
theorem member_sat (checked : Grouping.Checked sources id) {m : Grouping.Member F}
    (hm : m ∈ checked.layout.members) {a : Var → F}
    (valid : Scalar.Circuit.Satisfies checked.layout.constraints a) (active : a m.selector = 1) :
    Scalar.Circuit.Satisfies (Activation.compile m.origin).constraints (project m a) := by
  have h := checked.layout.member_constraints m hm a valid
  intro p hp
  have mem : Grouping.gate m.sourceSelector m.privateCols p ∈
      (Grouping.member m.source m.sourceSelector m.privateCols).constraints :=
    List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have := h _ mem
  have on : project m a m.sourceSelector = 1 := by
    rw [show m.sourceSelector = m.origin.numVars from rfl, project_selector checked hm]; exact active
  have on' : (fun v => a (m.columns[v]?.getD 0)) m.sourceSelector = 1 := on
  exact (Grouping.gate_active m.sourceSelector m.privateCols p _ on').symm.trans this

/-- A group row's trimmed ledger: zero when its activation is zero, the
selected member's virtual row's otherwise. -/
theorem group_row (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (checked : Grouping.Checked sources id) {a : Var → F} (holds : (lowerGroup checked.layout).Holds a) :
    Finsupp.mapDomain trimZeros ((lowerGroup checked.layout).rowLedger a) = 0 ∨
      ∃ m ∈ checked.layout.members, Scalar.Circuit.Satisfies checked.layout.constraints a ∧
        checked.layout.activation.denote a = 1 ∧ a m.selector = 1 ∧
        Finsupp.mapDomain trimZeros ((lowerGroup checked.layout).rowLedger a) =
          Finsupp.mapDomain trimZeros (instLedger idOf (memberInst checked.layout m a)) := by
  set g := checked.layout with hg
  have valid : Scalar.Circuit.Satisfies g.constraints a := fun q hq => holds q (List.mem_append_left _ hq)
  have multC : (1 - g.activation.denote a) * a g.width = 0 := by
    have := holds _ (List.mem_append_right _ (List.mem_singleton_self _))
    simpa [Scalar.Circuit.ArithExpr.denote] using this
  have boolean : g.activation.denote a = 0 ∨ g.activation.denote a = 1 := by
    have h := Grouping.exclusive_sum (g.exclusive checked.certificate.shapes a valid)
    simpa [Grouping.Layout.activation, Grouping.sum_denote, Function.comp_def,
      Scalar.Circuit.ArithExpr.denote] using h
  rcases boolean with off | on
  · left
    have mult0 : a g.width = 0 := by simpa [off] using multC
    have packets := checked.padding_sound a valid off
    rw [lowerGroup_rowLedger, pairsLedger_zero]
    · simp
    intro i
    cases i with
    | zero => simp [groupPairs, mult0]
    | succ i =>
        simp only [groupPairs, List.getD_cons_succ]
        rw [getD_map_default _ _ ⟨.const 0, []⟩ i (by simp [Scalar.Circuit.ArithExpr.denote])]
        have := (packets.2 i).1
        simpa [Grouping.Layout.slot, Grouping.lookupAt, Scalar.Circuit.ArithExpr.denote] using this
  · right
    obtain ⟨n, hn, active, _⟩ := g.select checked.certificate.shapes a valid on
    refine ⟨n, hn, valid, on, active, ?_⟩
    obtain ⟨_, provided, required, msgs, same⟩ := packet_active checked n hn a valid on active
    obtain ⟨recv, reqs⟩ := messages_ok idOf idOk msgs
    have sel : project n a n.origin.numVars = 1 := by rw [project_selector checked hn]; exact active
    rw [lowerGroup_rowLedger, instLedger_pairs]
    apply pairsLedger_trim
    intro i
    cases i with
    | zero =>
        simp only [groupPairs, instPairs, memberInst, List.getD_cons_zero, true_and]
        rw [trim_of_words same.1, recv, ← receive_tuple idOf n.origin 0]
        rfl
    | succ i =>
        simp only [groupPairs, instPairs, memberInst, List.getD_cons_succ]
        rw [getD_map_default _ _ ⟨.const 0, []⟩ i (by simp [Scalar.Circuit.ArithExpr.denote])]
        have target : (Activation.compile n.origin).sends.map
              (fun s => (encode idOf (s.message (project n a)), s.enable.denote (project n a))) ++
            (Activation.compile n.origin).memory.map (fun m =>
              (encodeRom (m.address.denote (project n a),
                m.value.map (Circuit.ArithExpr.denote (project n a))), m.enable.denote (project n a))) =
            required.map fun l => (l.args.map (·.denote (project n a)), l.enable.denote (project n a)) := by
          have := congrArg (List.map fun x : Scalar.Circuit.ArithExpr F × List (Scalar.Circuit.ArithExpr F) =>
            (x.2.map (·.denote (project n a)), x.1.denote (project n a))) reqs
          simp only [List.map_map, Function.comp_def, List.map_append] at this
          rw [this]
          simp only [Activation.compile, List.map_map, Function.comp_def]
          congr 1
          · apply List.map_congr_left; intro s _
            refine Prod.ext ?_ ?_
            · show encode idOf ((Activation.send n.origin.numVars s).message (project n a)) =
                (sendLookup idOf s).tuple (project n a)
              rw [send_tuple]; rfl
            · exact Activation.polynomial_active _ _ _ sel
          · apply List.map_congr_left; intro m _
            refine Prod.ext ?_ ?_
            · show encodeRom ((m.address.denote (project n a)),
                  m.value.map (Circuit.ArithExpr.denote (project n a))) =
                (memoryLookup m).tuple (project n a)
              rw [memory_tuple]
            · exact Activation.polynomial_active _ _ _ sel
        rw [target, getD_map_default _ _ ⟨.const 0, []⟩ i (by simp [Scalar.Circuit.ArithExpr.denote])]
        have h := same.2 i
        refine ⟨?_, ?_⟩
        · have := h.1
          simp only [Grouping.Layout.slot, Grouping.lookupAt] at this
          exact this
        · have := trim_of_words h.2
          simp only [Grouping.Layout.slot, Grouping.lookupAt] at this
          exact this

end Groups

/-! ## Memo rows of group members -/

section Plan

variable {source : Circuit.System F} {id : String → Except String Nat}

/-- The chips a grouped stage proves: the singles and every group's members. -/
def allChips (plan : Grouping.Plan source id) : List (Chip F) :=
  plan.singles ++ plan.groups.flatMap (·.sources)

/-- Physical circuit names are distinct, so a group row is inspected by its own
layout. -/
def circuitNames (plan : Grouping.Plan source id) : List String :=
  plan.singles.map Chip.name ++ plan.groups.map (·.checked.layout.name)

theorem origin_mem {sources : List (Chip F)} (checked : Grouping.Checked sources id)
    {m : Grouping.Member F} (hm : m ∈ checked.layout.members) : m.origin ∈ sources := by
  rw [← checked.certificate.sources_eq]
  exact List.mem_map.mpr ⟨m, hm, rfl⟩

theorem origin_allChips (plan : Grouping.Plan source id) {packed : Grouping.Packed F id}
    (hp : packed ∈ plan.groups) {m : Grouping.Member F} (hm : m ∈ packed.checked.layout.members) :
    m.origin ∈ allChips plan :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨packed, hp, origin_mem packed.checked hm⟩)

/-- The group row of an active member is inspected to the member's activated
rule, once the member's memory lookups are valid. -/
theorem group_inspect (plan : Grouping.Plan source id) (names : (circuitNames plan).Nodup)
    {packed : Grouping.Packed F id} (hp : packed ∈ plan.groups)
    {m : Grouping.Member F} (hm : m ∈ packed.checked.layout.members) {a : Var → F}
    (valid : Scalar.Circuit.Satisfies packed.checked.layout.constraints a)
    (act : packed.checked.layout.activation.denote a = 1) (active : a m.selector = 1) {rom : WireROM F}
    (memory : ∀ l ∈ (Activation.compile m.origin).memory, MemoryLookup.Valid rom (project m a) l) :
    plan.inspectRow rom (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a) =
      .ok (some ((Activation.compile m.origin).conclusion (project m a),
        (Activation.compile m.origin).requirements (project m a))) := by
  have fin := packed.checked.finite
  have agree : ∀ v < packed.checked.layout.width, (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment v = a v :=
    fun v hv => Row.ofAssignment_agree _ _ _ _ hv
  have conR : Scalar.Circuit.Satisfies packed.checked.layout.constraints (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment := by
    intro q hq
    have same := (fin.1 q hq).denote a
    simp only [Optimized.Polynomial.denote_subst, Grouping.restrict_denote packed.checked.layout.width _ a packed.checked.layout.name] at same
    exact same.trans (valid q hq)
  have actR : packed.checked.layout.activation.denote (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment = 1 := by
    have same := fin.2.1.denote a
    simp only [Optimized.Polynomial.denote_subst, Grouping.restrict_denote packed.checked.layout.width _ a packed.checked.layout.name] at same
    exact same.trans act
  have viewR : ∀ n ∈ packed.checked.layout.members, (packed.checked.layout.view n).denote (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment =
      (packed.checked.layout.view n).denote a := fun n hn => by
    simpa only [Grouping.Payload.denote_subst, Grouping.restrict_denote packed.checked.layout.width _ a packed.checked.layout.name] using
      (fin.2.2 n hn).2.denote a
  have selR : ∀ n ∈ packed.checked.layout.members, (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment n.selector = a n.selector :=
    fun n hn => agree _ (fin.2.2 n hn).1
  obtain ⟨selectors, -⟩ := packet_active packed.checked m hm a valid act active
  have uniq : ∀ n ∈ packed.checked.layout.members, a n.selector = 1 → n = m := by
    intro n hn on
    have h := selectors n hn
    rw [on] at h
    have : m.selector = n.selector := by
      by_contra ne
      simp [Grouping.selected, ne] at h
    exact packed.checked.certificate.unique n hn m hm this.symm
  have payload := packed.checked.certificate.payload_project m hm a valid selectors
  have on : project m a m.origin.numVars = 1 := by rw [project_selector packed.checked hm]; exact active
  have memValid : ((packed.checked.layout.view m).denote (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment).MemoryValid rom := by
    rw [viewR m hm, payload, Grouping.ofChip_memory]
    intro l hl en
    have := memory _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
    apply this
    show (Activation.polynomial m.origin.numVars l.enable).denote (project m a) = 1
    rw [Activation.polynomial_active _ _ _ on]; exact en
  have validRow : packed.checked.layout.ValidRow rom (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment :=
    ⟨conR, actR, fun n hn on' => by
      rw [selR n hn] at on'
      rw [uniq n hn on']
      exact memValid⟩
  obtain ⟨n1, n2, disj⟩ := List.nodup_append.mp names
  have noSingle : plan.singles.find? (·.name == packed.checked.layout.name) = none := by
    apply List.find?_eq_none.mpr
    intro c hc same
    simp only [beq_iff_eq] at same
    exact disj _ (List.mem_map.mpr ⟨c, hc, rfl⟩) _ (List.mem_map.mpr ⟨packed, hp, rfl⟩) same
  have grp : plan.groups.find? (·.checked.layout.name == packed.checked.layout.name) = some packed := by
    cases hf : plan.groups.find? (·.checked.layout.name == packed.checked.layout.name) with
    | none =>
        have := List.find?_eq_none.mp hf packed hp
        simp at this
    | some q =>
        have hq := List.mem_of_find?_eq_some hf
        have name := List.find?_some hf
        simp only [beq_iff_eq] at name
        rw [List.inj_on_of_nodup_map n2 hq hp name]
  have findM : packed.checked.layout.members.find? (fun n => decide ((Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment n.selector = 1)) =
      some m := by
    cases hf : packed.checked.layout.members.find? (fun n => decide ((Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).assignment n.selector = 1)) with
    | none =>
        have := List.find?_eq_none.mp hf m hm
        simp [selR m hm, active] at this
    | some n =>
        have hn := List.mem_of_find?_eq_some hf
        have sel := List.find?_some hf
        simp only [decide_eq_true_eq, selR n hn] at sel
        rw [uniq n hn sel]
  unfold Grouping.Plan.inspectRow
  have chipName : (Row.ofAssignment packed.checked.layout.name packed.checked.layout.width a).chip = packed.checked.layout.name := rfl
  rw [chipName, noSingle]
  simp only [grp]
  unfold Grouping.Layout.inspectRow
  rw [if_pos ⟨Row.ofAssignment_length _ _ _, conR⟩, if_neg (by rw [actR]; exact one_ne_zero)]
  simp only [findM]
  rw [if_pos validRow, viewR m hm, payload, Grouping.ofChip_root, Grouping.ofChip_requirements,
    Activation.requirements_active _ _ on]
  rfl

/-- The group cost bound: lookups of every member of the group. -/
def groupCost (packed : Grouping.Packed F id) : Nat :=
  (packed.sources.map fun c => c.sends.length + c.memory.length).sum

omit [DecidableEq F] in
theorem le_sum_of_mem' {α : Type} {l : List α} {f : α → Nat} {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-- The group rows of a stage as virtual rows: at most one per row, with the
same trimmed ledger. -/
theorem group_virtual (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) :
    ∀ {gs : List (Grouping.Packed F id × (Var → F))},
    (∀ x ∈ gs, (lowerGroup x.1.checked.layout).Holds x.2) →
    ∃ V : List (Inst F), V.length ≤ gs.length ∧
      (V.map fun p => p.1.sends.length + p.1.memory.length).sum ≤ (gs.map fun x => groupCost x.1).sum ∧
      (∀ p ∈ V, ∃ x ∈ gs, ∃ m ∈ x.1.checked.layout.members,
        Scalar.Circuit.Satisfies x.1.checked.layout.constraints x.2 ∧
        x.1.checked.layout.activation.denote x.2 = 1 ∧ x.2 m.selector = 1 ∧
        p = memberInst x.1.checked.layout m x.2) ∧
      Finsupp.mapDomain trimZeros (gs.map fun x => (lowerGroup x.1.checked.layout).rowLedger x.2).sum =
        Finsupp.mapDomain trimZeros (V.map (instLedger idOf)).sum
  | [], _ => ⟨[], le_rfl, le_rfl, by simp, by simp⟩
  | x :: gs, holds => by
      obtain ⟨V, len, cost, from_, ledger⟩ := group_virtual idOf idOk (gs := gs)
        (fun y hy => holds y (List.mem_cons_of_mem _ hy))
      rcases group_row idOf idOk x.1.checked (holds x (List.mem_cons_self ..)) with zero | ⟨m, hm, valid, act, active, eq⟩
      · refine ⟨V, by simp only [List.length_cons]; omega,
          by simp only [List.map_cons, List.sum_cons]; omega, fun p hp => ?_, ?_⟩
        · obtain ⟨y, hy, rest⟩ := from_ p hp
          exact ⟨y, List.mem_cons_of_mem _ hy, rest⟩
        · simp only [List.map_cons, List.sum_cons, Finsupp.mapDomain_add, zero, zero_add, ledger]
      · refine ⟨memberInst x.1.checked.layout m x.2 :: V, by simp only [List.length_cons]; omega, ?_,
          fun p hp => ?_, ?_⟩
        · have le : m.origin.sends.length + m.origin.memory.length ≤ groupCost x.1 :=
            le_sum_of_mem' (f := fun c : Chip F => c.sends.length + c.memory.length)
              (origin_mem x.1.checked hm)
          simp only [List.map_cons, List.sum_cons, memberInst]
          omega
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨x, List.mem_cons_self .., m, hm, valid, act, active, rfl⟩
          · obtain ⟨y, hy, rest⟩ := from_ p hp
            exact ⟨y, List.mem_cons_of_mem _ hy, rest⟩
        · simp only [List.map_cons, List.sum_cons, Finsupp.mapDomain_add, eq, ledger]

end Plan

/-! ## Shared map tables

The compiler's map layout: one table per input-table height, shared by every
map over it. Row `i` holds fixed cells; map `k` of the table has main count
column `k` and the lookup `push(−count_k, [CALL, id_k, cells_k(i)])`, where
`cells_k` are fixed columns (input and output cells, possibly shared with other
maps). Padding rows repeat a genuine row. Soundness needs only that every row's
tuple of every map is an encoded map claim (`SharedTable.check`). -/

section Shared

/-- A shared map table: per map its callable id and fixed column indices. -/
structure SharedTable (F : Type) where
  fixedWidth : Nat
  maps : List (Nat × List Nat)
  rows : Nat
  fixed : Nat → Nat → F

def sharedMapCircuit (fixedWidth : Nat) (maps : List (Nat × List Nat)) : Tiling.Circuit F where
  width := maps.length
  fixedWidth := fixedWidth
  constraints := []
  lookups := maps.zipIdx.map fun x => ⟨.sub (.const 0) (.var x.2),
    .const (Bridge.CALL : F) :: .const (x.1.1 : F) :: x.1.2.map fun c => .var (maps.length + c)⟩

def SharedTable.air (T : SharedTable F) : WideStage.Air F :=
  ⟨sharedMapCircuit T.fixedWidth T.maps, T.rows, T.fixed⟩

/-- The tuple map `m` looks up on row `i`. -/
def SharedTable.tuple (T : SharedTable F) (i : Nat) (m : Nat × List Nat) : List F :=
  (Bridge.CALL : F) :: (m.1 : F) :: m.2.map (T.fixed i)

/-- Every row's tuple of every map is a claim. -/
def SharedTable.check (claims : List (List F)) (T : SharedTable F) : Bool :=
  (List.range T.rows).all fun i => T.maps.all fun m => claims.contains (T.tuple i m)

/-- `check` with a hash set of the claims (`checkFast_eq`). -/
def SharedTable.checkFast [Hashable F] (claims : List (List F)) (T : SharedTable F) : Bool :=
  let set := Std.HashSet.ofList claims
  (List.range T.rows).all fun i => T.maps.all fun m => set.contains (T.tuple i m)

theorem SharedTable.checkFast_eq [Hashable F] (claims : List (List F)) (T : SharedTable F) :
    T.checkFast claims = T.check claims := by
  simp only [SharedTable.checkFast, SharedTable.check, Std.HashSet.contains_ofList]

theorem SharedTable.support {T : SharedTable F} {claims : List (List F)} (ok : T.check claims = true)
    (main : Nat → Scalar.Circuit.Var → F) {i : Nat} (hi : i < T.rows) {t : List F}
    (ht : T.air.circuit.rowLedger (T.air.assign main i) t ≠ 0) : t ∈ claims := by
  obtain ⟨l, hl, hne⟩ := WideStage.exists_of_sum_ne ht
  simp only [SharedTable.air, sharedMapCircuit, List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  simp only [Lookup.entry, Finsupp.single_apply] at hne
  split at hne
  · rename_i eq
    subst eq
    have mem := List.fst_mem_of_mem_zipIdx hx
    simp only [SharedTable.check, List.all_eq_true, List.mem_range, List.contains_iff_mem] at ok
    have := ok i hi x.1 mem
    convert this using 1
    simp [Lookup.tuple, SharedTable.tuple, WideStage.Air.assign_apply, Scalar.Circuit.ArithExpr.denote,
      SharedTable.air, sharedMapCircuit, List.map_map, Function.comp_def]
  · exact absurd rfl hne

theorem shared_support {Ts : List (SharedTable F)} {claims : List (List F)}
    (ok : ∀ T ∈ Ts, T.check claims = true) (main : Nat → Nat → Scalar.Circuit.Var → F) (t : List F)
    (ht : WideStage.stageLedger (Ts.map SharedTable.air) main t ≠ 0) : t ∈ claims := by
  refine WideStage.stage_support (P := (· ∈ claims)) ?_ t ht
  intro x hx i hi u hu
  rw [← List.map_zipIdx] at hx
  obtain ⟨⟨T, j⟩, hT, rfl⟩ := List.mem_map.mp hx
  exact SharedTable.support (ok T (List.fst_mem_of_mem_zipIdx hT)) (main j) hi hu

end Shared

/-! ## End to end -/

section Sound

/-- **End to end, grouped wide stage, any rows.** Rows of lowered single
chips (`Bridge.lower`) and of lowered groups (`lowerGroup`), the map tables
over the encoded map claims and the ROM tables, whose lookups balance on the
multi-stark bus (keyed by `trimZeros`) against the entry request, prove the
entry call; the ROM is the one the ROM traces hold. -/
theorem grouped_heap_sound_insts {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {sInsts : List (Chip F × (Var → F))} (chipsIn : ∀ p ∈ sInsts, p.1 ∈ plan.singles)
    (sHold : ∀ p ∈ sInsts, (Bridge.lower idOf p.1).Holds p.2)
    {gInsts : List (Grouping.Packed F id × (Var → F))} (groupsIn : ∀ x ∈ gInsts, x.1 ∈ plan.groups)
    (gHold : ∀ x ∈ gInsts, (lowerGroup x.1.checked.layout).Holds x.2)
    (capacity : sInsts.length + gInsts.length ≤ 2 ^ 39)
    {mapLedger : Ledger F}
    (mapSupport : ∀ t, mapLedger t ≠ 0 → t ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : lookupCount sInsts + (gInsts.map fun x => groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) (allChips plan) idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (balanced : Finsupp.mapDomain trimZeros
      ((sInsts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
        (gInsts.map fun x => (lowerGroup x.1.checked.layout).rowLedger x.2).sum + mapLedger +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  set rom := WideStage.wideRom roms mainR
  have valid : rom.Valid := WideStage.wideRom_valid widths (fun r hr i hi i' hi' e =>
    small.inj (by have := romCaps r hr; omega) (by have := romCaps r hr; omega) e) mainR
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set tables := mapLedger +
    WideStage.stageLedger (WideStage.romAirs roms) mainR
  obtain ⟨V, lenV, costV, fromV, ledgerV⟩ := group_virtual idOf idOk gHold
  let S : List (Inst F) := sInsts.map fun p => (p.1, p.2, p.2 (p.1.numVars + 1))
  have sLedger : S.map (instLedger idOf) = sInsts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2 := by
    simp only [S, List.map_map]
    apply List.map_congr_left
    intro p _
    exact (lower_instLedger idOf p.1 p.2).symm
  have singleAll : ∀ c ∈ plan.singles, c ∈ allChips plan := fun c hc => List.mem_append_left _ hc
  have W : WideT (Depth.system cfg prepared.system) (allChips plan) idOf bound (Erasure.rawROM rom) root
      (S ++ V) tables := {
    chipsIn := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact singleAll _ (chipsIn q hq)
      · obtain ⟨x, hx, m, hm, -, -, -, rfl⟩ := fromV p hp
        exact origin_allChips plan (groupsIn x hx) hm
    sat := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact fun c hc => sHold q hq c (List.mem_append_left _ hc)
      · obtain ⟨x, hx, m, hm, sat, -, active, rfl⟩ := fromV p hp
        exact member_sat x.1.checked hm sat active
    mult := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have := sHold q hq _ (List.mem_append_right _ (List.mem_singleton_self _))
        simpa [Scalar.Circuit.ArithExpr.denote] using this
      · obtain ⟨x, hx, m, hm, -, -, active, rfl⟩ := fromV p hp
        simp [memberInst, project_selector x.1.checked hm, active]
    small := small
    enablesOk := enablesOk
    tags := tags
    count := by
      have e : ((S ++ V).map fun p => p.1.sends.length + p.1.memory.length).sum =
          (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum +
            (V.map fun p => p.1.sends.length + p.1.memory.length).sum := by
        simp only [S, List.map_append, List.sum_append, List.map_map, Function.comp_def]
      simp only [lookupCount] at lookups
      omega
    shaped := Shaped.of_check shaped
    romPacked := WideStage.rawROM_packed rom
    romWidth := by
      intro e he
      simp only [Erasure.rawROM, List.mem_map] at he
      obtain ⟨⟨addr, ws⟩, hw, rfl⟩ := he
      simp only [rom, WideStage.wideRom, List.mem_flatMap, List.mem_map, List.mem_range] at hw
      obtain ⟨x, hx, i, _, eq⟩ := hw
      simp only [Prod.mk.injEq] at eq
      obtain ⟨-, rfl⟩ := eq
      simp only [Erasure.pack_words, WideStage.romWords_length]
      exact romWidths x.1 (List.fst_mem_of_mem_zipIdx hx)
    memWidth := memWidth
    tableSupport := fun t ht => by
      simp only [tables, Finsupp.add_apply] at ht
      by_cases hm : mapLedger t = 0
      · rw [hm, zero_add] at ht
        exact Or.inr (WideStage.romAirs_support roms mainR t ht)
      · obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapSupport t hm)
        exact Or.inl ⟨mc, hmc, e.symm⟩
    balanced := by
      have e : ((S ++ V).map (instLedger idOf)).sum + Finsupp.single (encode idOf root) 1 + tables =
          ((S.map (instLedger idOf)).sum + tables + Finsupp.single (encode idOf root) 1) +
            (V.map (instLedger idOf)).sum := by
        simp only [List.map_append, List.sum_append]; abel
      rw [e, Finsupp.mapDomain_add, ← ledgerV, ← Finsupp.mapDomain_add, sLedger, ← balanced]
      congr 1
      simp only [tables]
      abel }
  obtain ⟨rows, length, checked⟩ := W.checkMemo plan context' (fun p hp act mem => by
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
      have hc := chipsIn q hq
      obtain ⟨_, formedA⟩ := activated q.1 hc
      have finite := Chip.finiteAssignment formedA q.2 (Erasure.rawROM rom)
      have validA : (Activation.compile q.1).ValidAssignment (Erasure.rawROM rom) q.2 := ⟨W.sat _ hp, mem⟩
      refine ⟨Row.ofAssignment q.1.name (q.1.numVars + 1) q.2, ?_⟩
      have check : (Activation.compile q.1).checkRow (Erasure.rawROM rom)
          (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2) =
            .ok ((Activation.compile q.1).conclusion q.2, (Activation.compile q.1).requirements q.2) := by
        apply Chip.checkRow_iff.mpr
        refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, finite.1.mp validA⟩, ?_⟩
        exact Prod.ext finite.2.1 finite.2.2
      have sel : (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2).assignment q.1.numVars = 1 := by
        rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]; exact act
      have named : (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2).chip = q.1.name := rfl
      simp only [Grouping.Plan.inspectRow, named, find_single plan hc, check, sel, ite_true]
    · obtain ⟨x, hx, m, hm, sat, actG, active, rfl⟩ := fromV p hp'
      exact ⟨_, group_inspect plan names (groupsIn x hx) hm sat actG active mem⟩)
  have total : rows.length ≤ 2 ^ 39 := by
    have : (S ++ V).length ≤ sInsts.length + gInsts.length := by
      simp only [S, List.length_append, List.length_map]; omega
    omega
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside total characteristic checked arguments decoded⟩


/-! ## Group tables -/

section Tables

variable {id : String → Except String Nat}

/-- The table of a group with its row count; it has no fixed columns. -/
def groupAir (x : Grouping.Packed F id × Nat) : WideStage.Air F :=
  ⟨lowerGroup x.1.checked.layout, x.2, fun _ _ => 0⟩

def groupAirs (gs : List (Grouping.Packed F id × Nat)) : List (WideStage.Air F) := gs.map groupAir

/-- The rows of all group tables. -/
def groupRows (gs : List (Grouping.Packed F id × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F) :
    List (Grouping.Packed F id × (Scalar.Circuit.Var → F)) :=
  gs.zipIdx.flatMap fun x => (List.range x.1.2).map fun i => (x.1.1, (groupAir x.1).assign (main x.2) i)

theorem groupAirs_ledger (gs : List (Grouping.Packed F id × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F) :
    WideStage.stageLedger (groupAirs gs) main =
      ((groupRows gs main).map fun x => (lowerGroup x.1.checked.layout).rowLedger x.2).sum := by
  simp only [WideStage.stageLedger, groupAirs, ← List.map_zipIdx, List.map_map, groupRows,
    Tiling.System.sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_def, Prod.map, _root_.id, WideStage.Air.ledger, List.map_map]
  rfl

theorem mem_groupRows {gs : List (Grouping.Packed F id × Nat)} {main : Nat → Nat → Scalar.Circuit.Var → F}
    {x : Grouping.Packed F id × (Scalar.Circuit.Var → F)} (hx : x ∈ groupRows gs main) :
    ∃ y ∈ gs.zipIdx, ∃ i < y.1.2, x = (y.1.1, (groupAir y.1).assign (main y.2) i) := by
  simp only [groupRows, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨y, hy, i, hi, rfl⟩ := hx
  exact ⟨y, hy, i, hi, rfl⟩

theorem groupRows_holds {gs : List (Grouping.Packed F id × Nat)} {main : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (groupAirs gs) main) :
    ∀ x ∈ groupRows gs main, (lowerGroup x.1.checked.layout).Holds x.2 := by
  intro x hx
  obtain ⟨y, hy, i, hi, rfl⟩ := mem_groupRows hx
  have hy' : Prod.map groupAir _root_.id y ∈ (groupAirs gs).zipIdx := by
    rw [groupAirs, ← List.map_zipIdx]
    exact List.mem_map_of_mem hy
  exact holds _ hy' i hi

theorem groupRows_in {gs : List (Grouping.Packed F id × Nat)} {main : Nat → Nat → Scalar.Circuit.Var → F}
    {x : Grouping.Packed F id × (Scalar.Circuit.Var → F)} (hx : x ∈ groupRows gs main) :
    ∃ y ∈ gs, x.1 = y.1 := by
  obtain ⟨y, hy, _, _, rfl⟩ := mem_groupRows hx
  exact ⟨y.1, List.fst_mem_of_mem_zipIdx hy, rfl⟩

theorem length_groupRows (gs : List (Grouping.Packed F id × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F) :
    (groupRows gs main).length = (gs.map (·.2)).sum := by
  simp only [groupRows, List.length_flatMap, List.length_map, List.length_range]
  exact WideStage.sum_zipIdx gs (·.2)

omit [Field F] [DecidableEq F] in
theorem nat_sum_flatMap {α : Type} (l : List α) (f : α → List Nat) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem cost_groupRows (gs : List (Grouping.Packed F id × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F) :
    ((groupRows gs main).map fun x => groupCost x.1).sum = (gs.map fun x => x.2 * groupCost x.1).sum := by
  rw [groupRows, List.map_flatMap, nat_sum_flatMap]
  simp only [List.map_map, Function.comp_def, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul]
  exact WideStage.sum_zipIdx gs fun x => x.2 * groupCost x.1

end Tables

/-- **End to end, grouped wide stage.** One table per unit (`unitAir`), one per
group (`groupAir`: `lowerGroup` with its row count), the map tables and the
ROM tables; every row satisfies its circuit and all lookups balance on the
multi-stark bus against the entry request. -/
theorem grouped_heap_sound {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) (allChips plan) idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  rw [WideStage.unitAirs_ledger unrolled, groupAirs_ledger] at balanced
  exact grouped_heap_sound_insts compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf idOk names
    (fun p hp => by obtain ⟨u, hu, e⟩ := WideStage.unitInsts_chip hp; rw [e]; exact chipsIn u hu)
    (fun p hp => WideStage.unitInsts_holds holds hp)
    (fun x hx => by obtain ⟨y, hy, e⟩ := groupRows_in hx; rw [e]; exact groupsIn y hy)
    (groupRows_holds holdsG)
    (by rw [WideStage.length_unitInsts, length_groupRows]; exact capacity)
    (WideStage.mapAirs_support _ mapCap mainM) widths romCaps romWidths small tags
    (by rw [WideStage.lookupCount_unitInsts, cost_groupRows]; exact lookups) characteristic shaped context
    enablesOk memWidth balanced

/-- `grouped_heap_sound` with the compiler's shared map tables (`SharedTable`,
checked by `SharedTable.check`) in place of `mapAirs`. With `groups = []` it is
the wide theorem for an ungrouped stage over those tables. -/
theorem grouped_heap_sound_shared {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {shared : List (SharedTable F)}
    (sharedOk : ∀ T ∈ shared, T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) (allChips plan) idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (shared.map SharedTable.air) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  rw [WideStage.unitAirs_ledger unrolled, groupAirs_ledger] at balanced
  exact grouped_heap_sound_insts compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf idOk names
    (fun p hp => by obtain ⟨u, hu, e⟩ := WideStage.unitInsts_chip hp; rw [e]; exact chipsIn u hu)
    (fun p hp => WideStage.unitInsts_holds holds hp)
    (fun x hx => by obtain ⟨y, hy, e⟩ := groupRows_in hx; rw [e]; exact groupsIn y hy)
    (groupRows_holds holdsG)
    (by rw [WideStage.length_unitInsts, length_groupRows]; exact capacity)
    (shared_support sharedOk mainM) widths romCaps romWidths small tags
    (by rw [WideStage.lookupCount_unitInsts, cost_groupRows]; exact lookups) characteristic shaped context
    enablesOk memWidth balanced

/-- `shaped` and `context` over every chip of a grouped plan, from the compiled
artifact (`Compiled.shaped_of_compiled_on`). -/
theorem static_of_compiled_grouped {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    {name : String} (entry : name ∈ entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (idOf : String → Nat) {bound : Nat}
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound) :
    Shaped.check (Depth.system cfg prepared.system) (allChips plan) idOf root bound = true ∧
      (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok () := by
  have entry' : name ∈ compiled.artifact.entries := by
    rw [(Optimized.compile_stages compiled.compiled).2.2.1]; exact entry
  have entryChip := Compiled.compile_entry_chip compiled.compiled entry
  have sub : ∀ c ∈ allChips plan, c ∈ (Depth.system cfg prepared.system).chips := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_of_find?_eq_some (plan.certificate.1 c hc)
    · obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
      exact List.mem_of_find?_eq_some (plan.certificate.2.1 p hp c hc)
  exact ⟨Compiled.Shaped.check_of (Compiled.shaped_of_compiled_on prepared certified sub entry' signed
      rooted outside entryPlain entryChip idOf bound chanIds chanBound),
    Compiled.context_of_compiled prepared certified rooted entryPlain entryChip⟩

/-- `grouped_heap_sound` with `shaped` and `context` from the compiled artifact. -/
theorem grouped_heap_sound_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨shaped, context⟩ := static_of_compiled_grouped compiled prepared certified plan entry signed
    rooted outside entryPlain idOf chanIds chanBound
  exact grouped_heap_sound compiled prepared certified plan activated entry signed rooted outside arguments
    decoded idOf idOk names chipsIn unrolled groupsIn capacity widths romCaps romWidths small tags lookups
    characteristic shaped context enablesOk memWidth holds holdsG balanced

/-- `grouped_heap_sound_shared` with `shaped` and `context` from the compiled artifact. -/
theorem grouped_heap_sound_shared_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {shared : List (SharedTable F)}
    (sharedOk : ∀ T ∈ shared, T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (shared.map SharedTable.air) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨shaped, context⟩ := static_of_compiled_grouped compiled prepared certified plan entry signed
    rooted outside entryPlain idOf chanIds chanBound
  exact grouped_heap_sound_shared compiled prepared certified plan activated entry signed rooted outside arguments
    decoded idOf idOk names chipsIn unrolled groupsIn capacity sharedOk widths romCaps romWidths small tags lookups
    characteristic shaped context enablesOk memWidth holds holdsG balanced

end Sound

/-! ## Goldilocks and BN254 -/

section Fields

open Aiur.Library.U32.Goldilocks (modulus)

local notation "GF" => ZMod modulus

/-- `grouped_heap_sound_compiled` over Goldilocks. -/
theorem grouped_heap_sound_goldilocks_compiled {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)} {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed GF id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result  :=
  grouped_heap_sound_compiled compiled prepared certified plan activated entry signed rooted outside
    entryPlain arguments decoded idOf idOk names chipsIn unrolled groupsIn capacity widths romCaps romWidths
    (Goldilocks.smallCast hbound) tags lookups (Goldilocks.characteristic hbits) chanIds chanBound enablesOk memWidth holds holdsG balanced

end Fields

section BN

local notation "BF" => ZMod Aiur.Library.Field.BN254.modulus

local instance : Fact (Nat.Prime Aiur.Library.Field.BN254.modulus) := ⟨Aiur.Library.Field.BN254.modulus_prime⟩

theorem bn254_two_pow_63_lt : 2 ^ 63 < Aiur.Library.Field.BN254.modulus := by
  unfold Aiur.Library.Field.BN254.modulus; norm_num

theorem bn254_smallCast {bound : Nat} (hbound : bound ≤ 2 ^ 63) : SmallCast BF bound :=
  smallCast_zmod _ (by have := bn254_two_pow_63_lt; omega)

theorem bn254_characteristic {cfg : Depth.Config} (hbits : cfg.bits ≤ 24) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : BF) ≠ 0 := by
  intro n positive le e
  have : 2 ^ 39 * 2 ^ cfg.bits ≤ 2 ^ 39 * 2 ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbits)
  have h63 : (2 : Nat) ^ 39 * 2 ^ 24 = 2 ^ 63 := by norm_num
  have small : SmallCast BF (2 ^ 63 + 1) :=
    smallCast_zmod _ (by have := bn254_two_pow_63_lt; omega)
  have := small n (by omega) e
  omega

/-- `grouped_heap_sound_compiled` over BN254 (CompressGL, CompressBN). -/
theorem grouped_heap_sound_bn254_compiled {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)} {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed BF id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → BF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result  :=
  grouped_heap_sound_compiled compiled prepared certified plan activated entry signed rooted outside
    entryPlain arguments decoded idOf idOk names chipsIn unrolled groupsIn capacity widths romCaps romWidths
    (bn254_smallCast hbound) tags lookups (bn254_characteristic hbits) chanIds chanBound enablesOk memWidth holds holdsG balanced

end BN

end Aiur.Tiling.Grouped
