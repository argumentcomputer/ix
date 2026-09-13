/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupMessages
import Ix.Aiur.Proofs.LookupShapes
import Ix.Aiur.Proofs.Execution
import Ix.Aiur.Proofs.Memory

/-!
Function execution, immutable memory facts and byte operations from one
mixed pool of zero-padded lookup messages.

The native function, memory and thirteen byte channels determine the
provider family. Query widths and the actual structural call checks prevent
padding aliases. Only reachable calls need a checked shape; an active row's
local execution determines its return width and propagates the callee checks.
Byte lookups from the same pool bound all call ranks and gaps, giving finite
execution by strict rank increase.

The pool retains arbitrary field provider multiplicities, inactive rows and
all consumer kinds. It assumes local row interpretation, exact padded
balance, and explicit query-count and width bounds. Extraction of these
obligations from native AIR and cryptographic verification is still required.
-/

namespace Aiur.AIR

open Bytecode.AIR

structure LookupTables where
  functions : List FunctionRow
  memoryWidths : List Nat
  memory : Nat → Array MemoryRow
  byte1 : Byte1Kind → Fin 256 → G
  byte2 : Byte2Kind → Fin 65536 → G

def LookupTables.providers (tables : LookupTables) : List (Provider (List G)) :=
  mapProviders functionMessage (functionProviders tables.functions) ++
  tables.memoryWidths.flatMap (fun width =>
    mapProviders (fun request => memoryMessage width request.1 request.2)
      (memoryProviders (tables.memory width))) ++
  byte1Providers tables.byte1 ++ byte2Providers tables.byte2

theorem LookupTables.provider_cases {tables : LookupTables} {provider : Provider (List G)}
    (member : provider ∈ tables.providers) :
    (∃ row ∈ tables.functions, provider = (functionMessage row.request, row.multiplicity)) ∨
    (∃ width ∈ tables.memoryWidths, ∃ i : Fin (tables.memory width).size,
      provider = (memoryMessage width (tables.memory width)[i].pointer
        (tables.memory width)[i].contents, (tables.memory width)[i].multiplicity)) ∨
    (∃ kind : Byte1Kind, ∃ row : Fin 256,
      provider = (byte1Request kind (G.ofNat row.val) (byte1Outputs kind row), tables.byte1 kind row)) ∨
    (∃ kind : Byte2Kind, ∃ row : Fin 65536,
      provider = (byte2Request kind (byteRangeMessage row).1 (byteRangeMessage row).2
        (byte2Outputs kind row), tables.byte2 kind row)) := by
  simp only [LookupTables.providers, List.mem_append] at member
  rcases member with ((function | memory) | byte1) | byte2
  · obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp function
    obtain ⟨row, rowMember, rowEq⟩ := List.mem_map.mp originalMember
    subst original
    exact Or.inl ⟨row, rowMember, equal.symm⟩
  · obtain ⟨width, widthMember, originalMember⟩ := List.mem_flatMap.mp memory
    obtain ⟨original, rowMember, equal⟩ := List.mem_map.mp originalMember
    obtain ⟨row, rowEq⟩ := List.mem_ofFn.mp rowMember
    subst original
    exact Or.inr (Or.inl ⟨width, widthMember, row, equal.symm⟩)
  · obtain ⟨kind, _, rowMember⟩ := List.mem_flatMap.mp byte1
    obtain ⟨row, equal⟩ := List.mem_ofFn.mp rowMember
    exact Or.inr (Or.inr (Or.inl ⟨kind, row, equal.symm⟩))
  · obtain ⟨kind, _, rowMember⟩ := List.mem_flatMap.mp byte2
    obtain ⟨row, equal⟩ := List.mem_ofFn.mp rowMember
    exact Or.inr (Or.inr (Or.inr ⟨kind, row, equal.symm⟩))

theorem Byte1Kind.channel_range (kind : Byte1Kind) :
    2 ≤ kind.channel.n ∧ kind.channel.n ≤ 4 := by
  cases kind <;> decide +kernel

theorem Byte2Kind.channel_range (kind : Byte2Kind) :
    5 ≤ kind.channel.n ∧ kind.channel.n ≤ 14 := by
  cases kind <;> decide +kernel

theorem padMessage_channel {width : Nat} {left right : List G}
    (positive : 0 < width) (same : padMessage width left = padMessage width right) :
    left[0]?.getD 0 = right[0]?.getD 0 := by
  have first := congrArg (fun message => message[0]?.getD 0) same
  simpa only [padMessage_read left 0 positive, padMessage_read right 0 positive] using first

theorem LookupTables.function_provider {tables : LookupTables} {provider : Provider (List G)}
    (member : provider ∈ tables.providers) (channel : provider.1[0]?.getD 0 = 0) :
    ∃ row ∈ tables.functions, provider = (functionMessage row.request, row.multiplicity) := by
  rcases tables.provider_cases member with function | ⟨width, _, i, equal⟩ |
      ⟨kind, row, equal⟩ | ⟨kind, row, equal⟩
  · exact function
  · subst provider
    have bad := congrArg G.n channel
    change 1 = 0 at bad
    omega
  · subst provider
    have bad := congrArg G.n channel
    change kind.channel.n = 0 at bad
    have range := kind.channel_range
    omega
  · subst provider
    have bad := congrArg G.n channel
    change kind.channel.n = 0 at bad
    have range := kind.channel_range
    omega

theorem LookupTables.memory_provider {tables : LookupTables} {provider : Provider (List G)}
    (member : provider ∈ tables.providers) (channel : provider.1[0]?.getD 0 = 1) :
    ∃ width ∈ tables.memoryWidths, ∃ i : Fin (tables.memory width).size,
      provider = (memoryMessage width (tables.memory width)[i].pointer
        (tables.memory width)[i].contents, (tables.memory width)[i].multiplicity) := by
  rcases tables.provider_cases member with ⟨row, _, equal⟩ | memory |
      ⟨kind, row, equal⟩ | ⟨kind, row, equal⟩
  · subst provider
    have bad := congrArg G.n channel
    change 0 = 1 at bad
    omega
  · exact memory
  · subst provider
    have bad := congrArg G.n channel
    change kind.channel.n = 1 at bad
    have range := kind.channel_range
    omega
  · subst provider
    have bad := congrArg G.n channel
    change kind.channel.n = 1 at bad
    have range := kind.channel_range
    omega

theorem LookupTables.byte1_provider {tables : LookupTables} {provider : Provider (List G)}
    {kind : Byte1Kind} (member : provider ∈ tables.providers)
    (channel : provider.1[0]?.getD 0 = kind.channel) :
    ∃ row : Fin 256,
      provider = (byte1Request kind (G.ofNat row.val) (byte1Outputs kind row), tables.byte1 kind row) := by
  have range := kind.channel_range
  rcases tables.provider_cases member with ⟨row, _, equal⟩ | ⟨width, _, i, equal⟩ |
      ⟨providedKind, row, equal⟩ | ⟨providedKind, row, equal⟩
  · subst provider
    have bad := congrArg G.n channel
    change 0 = kind.channel.n at bad
    omega
  · subst provider
    have bad := congrArg G.n channel
    change 1 = kind.channel.n at bad
    omega
  · subst provider
    have same := Byte1Kind.channel_injective channel
    subst providedKind
    exact ⟨row, rfl⟩
  · subst provider
    have bad := congrArg G.n channel
    change providedKind.channel.n = kind.channel.n at bad
    have providedRange := providedKind.channel_range
    omega

theorem LookupTables.byte2_provider {tables : LookupTables} {provider : Provider (List G)}
    {kind : Byte2Kind} (member : provider ∈ tables.providers)
    (channel : provider.1[0]?.getD 0 = kind.channel) :
    ∃ row : Fin 65536,
      provider = (byte2Request kind (byteRangeMessage row).1 (byteRangeMessage row).2
        (byte2Outputs kind row), tables.byte2 kind row) := by
  have range := kind.channel_range
  rcases tables.provider_cases member with ⟨row, _, equal⟩ | ⟨width, _, i, equal⟩ |
      ⟨providedKind, row, equal⟩ | ⟨providedKind, row, equal⟩
  · subst provider
    have bad := congrArg G.n channel
    change 0 = kind.channel.n at bad
    omega
  · subst provider
    have bad := congrArg G.n channel
    change 1 = kind.channel.n at bad
    omega
  · subst provider
    have bad := congrArg G.n channel
    change providedKind.channel.n = kind.channel.n at bad
    have providedRange := providedKind.channel_range
    omega
  · subst provider
    have same := Byte2Kind.channel_injective channel
    subst providedKind
    exact ⟨row, rfl⟩

theorem functionMessage_minimum (request : Call) : 3 ≤ (functionMessage request).length := by
  simp only [functionMessage, List.length_cons, List.length_append, List.length_nil]
  omega

theorem padded_functionMessage_index {width : Nat} {left right : Call}
    (leftBound : left.function < gSize.toNat) (rightBound : right.function < gSize.toNat)
    (widthBound : (functionMessage left).length ≤ width)
    (same : padMessage width (functionMessage left) = padMessage width (functionMessage right)) :
    left.function = right.function := by
  have minimum := functionMessage_minimum left
  have key := congrArg (fun message => message[1]?.getD 0) same
  rw [padMessage_read (functionMessage left) 1 (by omega),
    padMessage_read (functionMessage right) 1 (by omega)] at key
  exact G.ofNat_injective_below leftBound rightBound key

/-- The query's structural return check and the provider's local execution
determine the same message width, even when some callees never return. -/
theorem padded_functionMessage_reflects {width : Nat} {program : Bytecode.Toplevel}
    {memory : Memory} {request provided : Call} {calls : List Call}
    (programBound : program.functions.size < gSize.toNat)
    (shape : request.LookupShape program)
    (execution : RunFunction program memory provided calls)
    (widthBound : (functionMessage request).length ≤ width)
    (same : padMessage width (functionMessage request) = padMessage width (functionMessage provided)) :
    request = provided := by
  obtain ⟨callee, present, constrained, inputSize, returnSize⟩ := shape
  have requestBound : request.function < gSize.toNat :=
    Nat.lt_trans (Array.getElem?_eq_some_iff.mp present).choose programBound
  cases execution with
  | function supplied arity body =>
    have providedBound : provided.function < gSize.toNat :=
      Nat.lt_trans (Array.getElem?_eq_some_iff.mp supplied).choose programBound
    have index := padded_functionMessage_index requestBound providedBound widthBound same
    have calleeEq := Option.some.inj ((index ▸ present).symm.trans supplied)
    subst callee
    have inputEq : request.inputs.size = provided.inputs.size := inputSize.symm.trans arity
    have outputEq : request.outputs.size = provided.outputs.size :=
      (body.return_size request.outputs.size returnSize).symm
    have lengths : (functionMessage request).length = (functionMessage provided).length := by
      simp only [functionMessage, List.length_cons, List.length_append, Array.length_toList,
        inputEq, outputEq]
    have raw := padMessage_injective_of_length widthBound lengths same
    exact functionMessage_injective (arities := fun _ => (request.inputs.size, request.outputs.size))
      ⟨requestBound, rfl, rfl⟩ ⟨providedBound, inputEq.symm, outputEq.symm⟩ raw

/-- One mixed padded pool. Only consumer counts are bounded; provider
multiplicities are arbitrary field elements. Message widths are checked on
queries, without imposing a global output-arity table on function rows. -/
structure GlobalLookups (tables : LookupTables) (width : Nat) (queries : List (List G)) : Prop where
  balance : PaddedLookupBalance width queries tables.providers
  count : queries.length < gSize.toNat
  widths : ∀ query ∈ queries, query.length ≤ width

theorem GlobalLookups.function_provider {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory}
    (valid : ∀ row ∈ tables.functions, row.Valid program memory)
    (programBound : program.functions.size < gSize.toNat)
    {request : Call} (shape : request.LookupShape program)
    (queried : functionMessage request ∈ queries) :
    ∃ row ∈ tables.functions, row.request = request ∧ row.selector = 1 := by
  obtain ⟨provider, member, same, nonzero⟩ :=
    paddedLookupBalance_provider global.balance global.count queried
  have widthBound := global.widths _ queried
  have minimum := functionMessage_minimum request
  have channel := padMessage_channel (by omega : 0 < width) same
  obtain ⟨row, rowMember, equal⟩ := tables.function_provider member channel
  subst provider
  have active := (valid row rowMember).active_of_nonzero nonzero
  have exactCall := padded_functionMessage_reflects programBound shape
    ((valid row rowMember).execution active) widthBound same.symm
  exact ⟨row, rowMember, exactCall.symm, active⟩

theorem GlobalLookups.byte1 {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {kind : Byte1Kind} {input : G} {outputs : Array G}
    (sized : outputs.size = kind.outputSize)
    (queried : byte1Request kind input outputs ∈ queries) :
    input.n < 256 ∧ outputs = kind.result input := by
  obtain ⟨provider, member, same, _⟩ :=
    paddedLookupBalance_provider global.balance global.count queried
  have shape := byte1Request_shape (fun _ => (0, 0)) kind input outputs sized
  have widthBound := global.widths _ queried
  have minimum := shape.1
  have channel := padMessage_channel (by omega : 0 < width) same
  obtain ⟨row, equal⟩ := tables.byte1_provider member channel
  subst provider
  have raw := (padMessage_injective_of_shape shape
    (byte1Request_shape _ kind _ _ (byte1Outputs_size kind row)) widthBound same.symm).symm
  obtain ⟨_, tail⟩ := List.cons.inj raw
  obtain ⟨sameInput, sameOutputs⟩ := List.cons.inj tail
  have below : row.val < gSize.toNat := Nat.lt_trans row.isLt (by decide)
  constructor
  · rw [← sameInput, G.n_ofNat, Nat.mod_eq_of_lt below]
    exact row.isLt
  · rw [← sameInput]
    exact (Array.toList_inj.mp sameOutputs).symm.trans (byte1Outputs_correct kind row)

theorem GlobalLookups.byte2 {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {kind : Byte2Kind} {x y : G} {outputs : Array G}
    (sized : outputs.size = kind.outputSize)
    (queried : byte2Request kind x y outputs ∈ queries) :
    x.n < 256 ∧ y.n < 256 ∧ outputs = kind.result x y := by
  obtain ⟨provider, member, same, _⟩ :=
    paddedLookupBalance_provider global.balance global.count queried
  have shape := byte2Request_shape (fun _ => (0, 0)) kind x y outputs sized
  have widthBound := global.widths _ queried
  have minimum := shape.1
  have channel := padMessage_channel (by omega : 0 < width) same
  obtain ⟨row, equal⟩ := tables.byte2_provider member channel
  subst provider
  have raw := (padMessage_injective_of_shape shape
    (byte2Request_shape _ kind _ _ _ (byte2Outputs_size kind row)) widthBound same.symm).symm
  obtain ⟨_, tail⟩ := List.cons.inj raw
  obtain ⟨sameX, tail⟩ := List.cons.inj tail
  obtain ⟨sameY, sameOutputs⟩ := List.cons.inj tail
  rw [← sameX, ← sameY]
  refine ⟨(byteRangeMessage_bounded row).1, (byteRangeMessage_bounded row).2, ?_⟩
  exact (Array.toList_inj.mp sameOutputs).symm.trans (byte2Outputs_correct kind row)

theorem GlobalLookups.memory_fact {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    (valid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {size : Nat} {pointer : G} {contents : Array G}
    (sizeBound : size < gSize.toNat) (sized : contents.size = size)
    (queried : memoryMessage size pointer contents ∈ queries) :
    memoryFacts tables.memory size pointer contents := by
  obtain ⟨provider, member, same, nonzero⟩ :=
    paddedLookupBalance_provider global.balance global.count queried
  have shape := memoryMessage_shape (fun _ => (0, 0)) size pointer contents sizeBound sized
  have widthBound := global.widths _ queried
  have minimum := shape.1
  have channel := padMessage_channel (by omega : 0 < width) same
  obtain ⟨providedSize, sizeMember, row, equal⟩ := tables.memory_provider member channel
  subst provider
  have raw := (padMessage_injective_of_shape shape
    (memoryMessage_shape _ providedSize _ _ (canonical _ sizeMember)
      ((valid providedSize).widths row row.isLt)) widthBound same.symm).symm
  obtain ⟨sameSize, tail⟩ := List.cons.inj (List.cons.inj raw).2
  have sizeEq := G.ofNat_injective_below (canonical _ sizeMember) sizeBound sameSize
  subst providedSize
  obtain ⟨samePointer, sameContents⟩ := List.cons.inj tail
  have active : (tables.memory size)[row].selector = 1 := by
    rcases (valid size).selectors row row.isLt with inactive | active
    · exact False.elim (nonzero (inactive_multiplicity_zero inactive
        ((valid size).activity row row.isLt)))
    · exact active
  exact ⟨row, row.isLt, active, samePointer, Array.toList_inj.mp sameContents⟩

theorem GlobalLookups.memory_consistent {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    (valid : ∀ size, MemoryRowsValid size (tables.memory size))
    (heights : ∀ size, (tables.memory size).size < gSize.toNat)
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {size : Nat} {pointer : G} {left right : Array G}
    (sizeBound : size < gSize.toNat) (leftSize : left.size = size) (rightSize : right.size = size)
    (queriedLeft : memoryMessage size pointer left ∈ queries)
    (queriedRight : memoryMessage size pointer right ∈ queries) : left = right :=
  memoryFacts_functional tables.memory valid heights
    (global.memory_fact valid canonical sizeBound leftSize queriedLeft)
    (global.memory_fact valid canonical sizeBound rightSize queriedRight)

theorem GlobalLookups.byte1_step {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    (memory : Memory) {kind : Byte1Kind} {values : Array G}
    {index : Bytecode.ValIdx} {input : G} {outputs : Array G}
    (read : values[index]? = some input) (sized : outputs.size = kind.outputSize)
    (queried : byte1Request kind input outputs ∈ queries) :
    Step memory (kind.op index) values (values ++ outputs) [] := by
  obtain ⟨range, correct⟩ := global.byte1 sized queried
  apply Step.primitive (advice := #[])
  rw [correct]
  exact byte1_primitive read range

theorem GlobalLookups.byte2_step {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    (memory : Memory) {kind : Byte2Kind} {values : Array G}
    {left right : Bytecode.ValIdx} {x y : G} {outputs : Array G}
    (readX : values[left]? = some x) (readY : values[right]? = some y)
    (sized : outputs.size = kind.outputSize)
    (queried : byte2Request kind x y outputs ∈ queries) :
    Step memory (kind.op left right) values
      (values ++ kind.extendOutputs x y outputs) [] := by
  obtain ⟨rangeX, rangeY, correct⟩ := global.byte2 sized queried
  apply Step.primitive (advice := #[])
  rw [correct]
  exact byte2_primitive readX readY rangeX rangeY

def rangeMessage (pair : G × G) : List G := byte2Request .range pair.1 pair.2 #[]

theorem GlobalLookups.rank_bytes {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    (bytes : Fin 6 → G) (queried : (rankByteQueries bytes).map rangeMessage ⊆ queries) :
    ∀ i, (bytes i).n < 256 := by
  have pairRange : ∀ pair ∈ rankByteQueries bytes, pair.1.n < 256 ∧ pair.2.n < 256 := by
    intro pair member
    have result := global.byte2 (kind := .range) (outputs := #[]) rfl
      (queried (List.mem_map.mpr ⟨pair, member, rfl⟩))
    exact ⟨result.1, result.2.1⟩
  have p0 := pairRange _ (by simp [rankByteQueries] : (bytes 0, bytes 1) ∈ rankByteQueries bytes)
  have p1 := pairRange _ (by simp [rankByteQueries] : (bytes 2, bytes 3) ∈ rankByteQueries bytes)
  have p2 := pairRange _ (by simp [rankByteQueries] : (bytes 4, bytes 5) ∈ rankByteQueries bytes)
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p0.1
  · exact p0.2
  · exact p1.1
  · exact p1.2
  · exact p2.1
  · exact p2.2

theorem FunctionRow.Valid.global_rank_bounded {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {row : FunctionRow}
    (valid : row.Valid program memory) (member : row ∈ tables.functions) (active : row.selector = 1)
    (queried : (functionByteQueries tables.functions).map rangeMessage ⊆ queries) :
    row.request.rank.n < callRankBound := by
  rw [valid.rank active]
  apply packRank_lt
  apply global.rank_bytes
  intro message messageMember
  obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp messageMember
  apply queried
  exact List.mem_map.mpr ⟨pair, functionByteQueries_member member active
    (List.mem_append_left _ pairMember), equal⟩

theorem FunctionRow.Valid.global_call_order {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {row : FunctionRow}
    (valid : row.Valid program memory) (member : row ∈ tables.functions) (active : row.selector = 1)
    (queried : (functionByteQueries tables.functions).map rangeMessage ⊆ queries)
    {edge : Call × (Fin 6 → G)} (called : edge ∈ row.calls)
    (childBound : edge.1.rank.n < callRankBound) :
    row.request.rank.n < edge.1.rank.n := by
  have gapBound : (packRank edge.2).n < callRankBound := by
    apply packRank_lt
    apply global.rank_bytes
    intro message messageMember
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp messageMember
    apply queried
    exact List.mem_map.mpr ⟨pair, functionByteQueries_member member active
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨edge, called, pairMember⟩)), equal⟩
  exact active_call_order_strict active
    (valid.global_rank_bounded global member active queried)
    childBound gapBound (valid.order edge called)

/-- Reachable rows execute finitely using one global padded lookup balance.
Only the current request is assumed to have a checked call shape; structural
program validation propagates that fact to its children. -/
theorem GlobalLookups.rows_execute {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {roots : List Call}
    (programValid : program.validateLookupShapes = true)
    (valid : ∀ row ∈ tables.functions, row.Valid program memory)
    (functionsQueried : (functionQueries roots tables.functions).map functionMessage ⊆ queries)
    (bytesQueried : (functionByteQueries tables.functions).map rangeMessage ⊆ queries)
    {row : FunctionRow} (member : row ∈ tables.functions) (active : row.selector = 1)
    (shape : row.request.LookupShape program) : Execution program memory row.request := by
  have programBound : program.functions.size < gSize.toNat := by
    have checked := programValid
    simp only [Bytecode.Toplevel.validateLookupShapes, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1
  have all : ∀ n : Nat, ∀ row : FunctionRow,
      callRankBound - row.request.rank.n = n → row ∈ tables.functions → row.selector = 1 →
      row.request.LookupShape program → Execution program memory row.request := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro parent measure member active shape
      have body := (valid parent member).execution active
      have children : ∀ child ∈ parent.requests, child.LookupShape program := by
        obtain ⟨callee, present, constrained, _, _⟩ := shape
        exact body.calls_lookupShape programValid present constrained
      apply Execution.function body
      intro child called
      obtain ⟨edge, edgeMember, edgeEq⟩ := List.mem_map.mp called
      obtain ⟨provider, providerMember, same, providerActive⟩ :=
        global.function_provider valid programBound (children child called)
          (functionsQueried (List.mem_map.mpr
            ⟨child, functionQueries_member member active called, rfl⟩))
      have childBound := (valid provider providerMember).global_rank_bounded
        global providerMember providerActive bytesQueried
      have order := (valid parent member).global_call_order global member active bytesQueried
        edgeMember (by simpa only [edgeEq, ← same] using childBound)
      rw [edgeEq, ← same] at order
      have smaller : callRankBound - provider.request.rank.n < n := by omega
      rw [← same]
      exact ih _ smaller provider rfl providerMember providerActive (same ▸ children child called)
  exact all _ row rfl member active shape

theorem GlobalLookups.roots_execute {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {roots : List Call}
    (programValid : program.validateLookupShapes = true)
    (valid : ∀ row ∈ tables.functions, row.Valid program memory)
    (functionsQueried : (functionQueries roots tables.functions).map functionMessage ⊆ queries)
    (bytesQueried : (functionByteQueries tables.functions).map rangeMessage ⊆ queries)
    {request : Call} (shape : request.LookupShape program) (root : request ∈ roots) :
    Execution program memory request := by
  have programBound : program.functions.size < gSize.toNat := by
    have checked := programValid
    simp only [Bytecode.Toplevel.validateLookupShapes, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1
  obtain ⟨row, member, same, active⟩ := global.function_provider valid programBound shape
    (functionsQueried (List.mem_map.mpr ⟨request, List.mem_append_left _ root, rfl⟩))
  rw [← same]
  exact global.rows_execute programValid valid functionsQueried bytesQueried member active (same ▸ shape)

end Aiur.AIR

namespace Aiur.BoundVerifier

open AIR Bytecode.AIR

theorem Backend.root_lookupShape {selection : Selection} (backend : Backend selection)
    (input : Array G) (arity : input.size = selection.inputSize) :
    Call.LookupShape backend.compiled.bytecode ⟨selection.function, input, selection.success, 0⟩ :=
  ⟨backend.entry, backend.present, backend.constrained, backend.arity.trans arity.symm,
    backend.returnArity⟩

theorem claim_padding (selection : Selection)
    (width : Nat) (input : Array G) :
    padMessage width (functionMessage ⟨selection.function, input, selection.success, 0⟩) =
      padMessage width (buildClaim selection.function input selection.success).toList := by
  have encoding : functionMessage ⟨selection.function, input, selection.success, 0⟩ =
      (buildClaim selection.function input selection.success).toList ++ [0] := by
    simp only [functionMessage, buildClaim, Array.toList_append, List.cons_append,
      List.nil_append, functionChannel]
    rfl
  rw [encoding]
  exact padMessage_append_zero _

/-- The selected success request has a finite AIR execution once its local
row and mixed lookup obligations are discharged. This is still conditional
on those obligations, not a theorem about public verifier acceptance. -/
theorem Backend.global_execution {selection : Selection} (backend : Backend selection)
    {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries) {memory : Memory}
    (input : Array G) (arity : input.size = selection.inputSize)
    (valid : ∀ row ∈ tables.functions, row.Valid backend.compiled.bytecode memory)
    (functionsQueried : (functionQueries [⟨selection.function, input, selection.success, 0⟩]
      tables.functions).map functionMessage ⊆ queries)
    (bytesQueried : (functionByteQueries tables.functions).map rangeMessage ⊆ queries) :
    Execution backend.compiled.bytecode memory ⟨selection.function, input, selection.success, 0⟩ :=
  global.roots_execute backend.lookupShapes valid functionsQueried bytesQueried
    (backend.root_lookupShape input arity) List.mem_cons_self

end Aiur.BoundVerifier
