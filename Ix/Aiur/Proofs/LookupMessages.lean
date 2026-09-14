/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ByteLookups

/-!
Exact lookup messages from their zero-padded representations.

The first two fields determine message length through the native channel
and function-arity schema. Padding is then injective, and exact balance
passes through padding and channel filtering. Zero-weight providers may
contain arbitrary data. Function and memory encodings recover the typed
messages used by execution and memory-table proofs.

These results do not extract padded balance from the cryptographic verifier.
Connecting all native active rows to the function-arity schema is also an
obligation; an arbitrary bytecode program need not have uniform returns.
-/

namespace Aiur.AIR

def padMessage (width : Nat) (message : List G) : List G :=
  List.ofFn fun i : Fin width => message[i.val]?.getD 0

theorem padMessage_length (width : Nat) (message : List G) :
    (padMessage width message).length = width := List.length_ofFn

theorem padMessage_read {width : Nat} (message : List G) (i : Nat) (hi : i < width) :
    (padMessage width message)[i]?.getD 0 = message[i]?.getD 0 := by
  simp only [padMessage, List.getElem?_ofFn, dif_pos hi, Option.getD_some]

theorem padMessage_injective_of_length {width : Nat} {left right : List G}
    (bounded : left.length ≤ width) (lengths : left.length = right.length)
    (same : padMessage width left = padMessage width right) : left = right := by
  apply List.ext_getElem lengths
  intro i hi hj
  have equal := congrArg (fun message => message[i]?.getD 0) same
  rw [padMessage_read left i (by omega), padMessage_read right i (by omega)] at equal
  simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] using equal

/-- The message length is determined by its first two entries. -/
def HasMessageShape (widths : G → G → Nat) (message : List G) : Prop :=
  2 ≤ message.length ∧ message.length = widths (message[0]?.getD 0) (message[1]?.getD 0)

theorem padMessage_injective_of_shape {width : Nat} {widths : G → G → Nat}
    {left right : List G} (leftShape : HasMessageShape widths left)
    (rightShape : HasMessageShape widths right) (bounded : left.length ≤ width)
    (same : padMessage width left = padMessage width right) : left = right := by
  have minimum := leftShape.1
  have first := congrArg (fun message => message[0]?.getD 0) same
  have second := congrArg (fun message => message[1]?.getD 0) same
  rw [padMessage_read left 0 (by omega), padMessage_read right 0 (by omega)] at first
  rw [padMessage_read left 1 (by omega), padMessage_read right 1 (by omega)] at second
  apply padMessage_injective_of_length bounded _ same
  rw [leftShape.2, rightShape.2, first, second]

def mapProviders (encode : α → β) (providers : List (Provider α)) : List (Provider β) :=
  providers.map fun provider => (encode provider.1, provider.2)

theorem count_map_of_matching [DecidableEq α] [DecidableEq β]
    (encode : α → β) (message : α) (queries : List α)
    (matching : ∀ query ∈ queries, encode query = encode message ↔ query = message) :
    (queries.map encode).count (encode message) = queries.count message := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    have head := matching query List.mem_cons_self
    have tail := ih (fun value member => matching value (List.mem_cons_of_mem query member))
    simp only [List.map_cons, List.count_cons, beq_iff_eq, head, tail]

theorem suppliedWeight_map_of_matching [DecidableEq α] [DecidableEq β]
    (encode : α → β) (message : α) (providers : List (Provider α))
    (matching : ∀ provider ∈ providers,
      provider.2 ≠ 0 → (encode provider.1 = encode message ↔ provider.1 = message)) :
    suppliedWeight (encode message) (mapProviders encode providers) =
      suppliedWeight message providers := by
  induction providers with
  | nil => rfl
  | cons provider providers ih =>
    have tail := ih (fun value member => matching value (List.mem_cons_of_mem provider member))
    change (if encode provider.1 = encode message then
      provider.2 + suppliedWeight (encode message) (mapProviders encode providers)
      else suppliedWeight (encode message) (mapProviders encode providers)) =
      (if provider.1 = message then provider.2 + suppliedWeight message providers
        else suppliedWeight message providers)
    by_cases zero : provider.2 = 0
    · simp only [zero, G.zero_add, ite_self, tail]
    · have head := matching provider List.mem_cons_self zero
      simp only [head, tail]

theorem suppliedWeight_eq_zero_of_absent [DecidableEq α] (message : α)
    (providers : List (Provider α))
    (absent : ∀ provider ∈ providers, provider.2 ≠ 0 → provider.1 ≠ message) :
    suppliedWeight message providers = 0 := by
  induction providers with
  | nil => rfl
  | cons provider providers ih =>
    have tail := ih (fun value member => absent value (List.mem_cons_of_mem provider member))
    change (if provider.1 = message then provider.2 + suppliedWeight message providers
      else suppliedWeight message providers) = 0
    by_cases zero : provider.2 = 0
    · simpa only [zero, G.zero_add, ite_self] using tail
    · have head := absent provider List.mem_cons_self zero
      simpa only [if_neg head] using tail

theorem exactLookupBalance_of_injective_on [DecidableEq α] [DecidableEq β]
    (encode : α → β) (admissible : α → Prop)
    (injective : ∀ {left right}, admissible left → admissible right →
      encode left = encode right → left = right)
    {queries : List α} {providers : List (Provider α)}
    (queriesAdmissible : ∀ query ∈ queries, admissible query)
    (providersAdmissible : ∀ provider ∈ providers, provider.2 ≠ 0 → admissible provider.1)
    (balanced : ExactLookupBalance (queries.map encode) (mapProviders encode providers)) :
    ExactLookupBalance queries providers := by
  intro message
  by_cases valid : admissible message
  · have queryMatching : ∀ query ∈ queries,
        encode query = encode message ↔ query = message := by
      intro query member
      exact ⟨injective (queriesAdmissible query member) valid, congrArg encode⟩
    have providerMatching : ∀ provider ∈ providers,
        provider.2 ≠ 0 → (encode provider.1 = encode message ↔ provider.1 = message) := by
      intro provider member nonzero
      exact ⟨injective (providersAdmissible provider member nonzero) valid, congrArg encode⟩
    have result := balanced (encode message)
    rw [count_map_of_matching encode message queries queryMatching,
      suppliedWeight_map_of_matching encode message providers providerMatching] at result
    exact result
  · have absent : message ∉ queries := fun member => valid (queriesAdmissible message member)
    rw [List.count_eq_zero.mpr absent, suppliedWeight_eq_zero_of_absent message providers]
    · rfl
    · intro provider member nonzero equal
      exact valid (equal ▸ providersAdmissible provider member nonzero)

theorem suppliedWeight_filter [DecidableEq α] (keep : α → Bool) (message : α)
    (providers : List (Provider α)) :
    suppliedWeight message (providers.filter fun provider => keep provider.1) =
      if keep message then suppliedWeight message providers else 0 := by
  induction providers with
  | nil => simp only [suppliedWeight, List.filter_nil, List.foldr_nil, ite_self]
  | cons provider providers ih =>
    by_cases same : provider.1 = message
    · by_cases retained : keep message = true
      · simp only [List.filter_cons, same, retained, ↓reduceIte, suppliedWeight, List.foldr_cons] at *
        rw [ih]
      · have dropped : keep message = false := Bool.eq_false_iff.mpr retained
        simp only [List.filter_cons, same, dropped, Bool.false_eq_true, ↓reduceIte]
        simpa only [dropped, Bool.false_eq_true, ↓reduceIte] using ih
    · by_cases retained : keep provider.1 = true
      · simp only [List.filter_cons, retained, ↓reduceIte, suppliedWeight,
          List.foldr_cons, if_neg same] at *
        exact ih
      · have dropped : keep provider.1 = false := Bool.eq_false_iff.mpr retained
        simp only [List.filter_cons, dropped, Bool.false_eq_true, ↓reduceIte]
        simpa only [suppliedWeight, List.foldr_cons, if_neg same] using ih

/-- Restrict global exact balance to any collection of message channels. -/
theorem ExactLookupBalance.filter [DecidableEq α] {queries : List α}
    {providers : List (Provider α)} (balanced : ExactLookupBalance queries providers)
    (keep : α → Bool) :
    ExactLookupBalance (queries.filter keep) (providers.filter fun provider => keep provider.1) := by
  intro message
  rw [suppliedWeight_filter]
  by_cases retained : keep message = true
  · rw [if_pos retained, List.count_filter retained, balanced]
  · rw [if_neg retained]
    have absent : message ∉ queries.filter keep := fun member =>
      retained (List.mem_filter.mp member).2
    rw [List.count_eq_zero.mpr absent]
    rfl

def PaddedLookupBalance (width : Nat) (queries : List (List G))
    (providers : List (Provider (List G))) : Prop :=
  ExactLookupBalance (queries.map (padMessage width)) (mapProviders (padMessage width) providers)

/-- A bounded query has a nonzero provider with the same padded message.
No message-shape hypothesis is needed for this first extraction step. -/
theorem paddedLookupBalance_provider {width : Nat} {queries : List (List G)}
    {providers : List (Provider (List G))} (balanced : PaddedLookupBalance width queries providers)
    (bounded : queries.length < gSize.toNat) {message : List G} (queried : message ∈ queries) :
    ∃ provider ∈ providers, padMessage width provider.1 = padMessage width message ∧ provider.2 ≠ 0 := by
  obtain ⟨provider, member, same, nonzero⟩ := exactLookupBalance_provider balanced
    (by simpa only [List.length_map] using bounded) (List.mem_map.mpr ⟨message, queried, rfl⟩)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst provider
  exact ⟨original, originalMember, same, nonzero⟩

theorem paddedLookupBalance_exact {width : Nat} (widths : G → G → Nat)
    {queries : List (List G)} {providers : List (Provider (List G))}
    (queryShapes : ∀ query ∈ queries, HasMessageShape widths query ∧ query.length ≤ width)
    (providerShapes : ∀ provider ∈ providers, provider.2 ≠ 0 →
      HasMessageShape widths provider.1 ∧ provider.1.length ≤ width)
    (balanced : PaddedLookupBalance width queries providers) :
    ExactLookupBalance queries providers := by
  apply exactLookupBalance_of_injective_on (padMessage width)
    (fun message => HasMessageShape widths message ∧ message.length ≤ width) _
    queryShapes providerShapes balanced
  intro left right hl hr same
  exact padMessage_injective_of_shape hl.1 hr.1 hl.2 same

/-- Input and output widths for each function index. -/
abbrev FunctionArities := Nat → Nat × Nat

def functionMessage (request : Bytecode.AIR.Call) : List G :=
  0 :: G.ofNat request.function ::
    (request.inputs.toList ++ request.outputs.toList ++ [request.rank])

def memoryMessage (width : Nat) (pointer : G) (contents : Array G) : List G :=
  1 :: G.ofNat width :: pointer :: contents.toList

def Byte1Kind.outputSize : Byte1Kind → Nat
  | .bits => 8
  | .shiftLeft | .shiftRight => 1

def Byte2Kind.outputSize : Byte2Kind → Nat
  | .range => 0
  | .mul | .split7 | .split4 => 2
  | _ => 1

/-- Length of a native message, determined by its channel and second field.
Function messages include the final call-order rank. -/
def lookupMessageWidth (arities : FunctionArities) (channel key : G) : Nat :=
  match channel.n with
  | 0 => 3 + (arities key.n).1 + (arities key.n).2
  | 1 => 3 + key.n
  | 2 => 10
  | 3 | 4 => 3
  | 5 | 6 | 7 | 8 | 9 | 10 => 4
  | 11 => 3
  | 12 | 13 | 14 => 5
  | _ => 0

def FunctionMessageValid (arities : FunctionArities) (request : Bytecode.AIR.Call) : Prop :=
  request.function < gSize.toNat ∧
    request.inputs.size = (arities request.function).1 ∧
    request.outputs.size = (arities request.function).2

theorem functionMessage_shape (arities : FunctionArities) (request : Bytecode.AIR.Call)
    (valid : FunctionMessageValid arities request) :
    HasMessageShape (lookupMessageWidth arities) (functionMessage request) := by
  obtain ⟨indexBound, inputs, outputs⟩ := valid
  simp only [HasMessageShape, functionMessage, List.length_cons, List.length_append,
    List.length_nil, Array.length_toList, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, lookupMessageWidth, G.n_ofNat,
    Nat.mod_eq_of_lt indexBound]
  change _ ∧ _ = 3 + (arities request.function).1 + (arities request.function).2
  omega

theorem memoryMessage_shape (arities : FunctionArities) (width : Nat)
    (pointer : G) (contents : Array G) (bounded : width < gSize.toNat)
    (sized : contents.size = width) :
    HasMessageShape (lookupMessageWidth arities) (memoryMessage width pointer contents) := by
  simp only [HasMessageShape, memoryMessage, List.length_cons, Array.length_toList,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    lookupMessageWidth, G.n_ofNat, Nat.mod_eq_of_lt bounded]
  change _ ∧ _ = 3 + width
  omega

theorem byte1Request_shape (arities : FunctionArities) (kind : Byte1Kind) (input : G)
    (outputs : Array G) (sized : outputs.size = kind.outputSize) :
    HasMessageShape (lookupMessageWidth arities) (byte1Request kind input outputs) := by
  cases kind <;>
    simp only [Byte1Kind.outputSize] at sized <;>
    simp only [HasMessageShape, byte1Request, List.length_cons, Array.length_toList,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      lookupMessageWidth, Byte1Kind.channel, sized] <;> exact ⟨by decide +kernel, rfl⟩

theorem byte2Request_shape (arities : FunctionArities) (kind : Byte2Kind) (x y : G)
    (outputs : Array G) (sized : outputs.size = kind.outputSize) :
    HasMessageShape (lookupMessageWidth arities) (byte2Request kind x y outputs) := by
  cases kind <;>
    simp only [Byte2Kind.outputSize] at sized <;>
    simp only [HasMessageShape, byte2Request, List.length_cons, Array.length_toList,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      lookupMessageWidth, Byte2Kind.channel, sized] <;> exact ⟨by decide +kernel, rfl⟩

theorem byte1Outputs_size (kind : Byte1Kind) (row : Fin 256) :
    (byte1Outputs kind row).size = kind.outputSize := by
  cases kind <;> simp only [byte1Outputs, Byte1Kind.outputSize, Array.size_ofFn,
    List.size_toArray, List.length_cons, List.length_nil]

theorem byte2Outputs_size (kind : Byte2Kind) (row : Fin 65536) :
    (byte2Outputs kind row).size = kind.outputSize := by
  cases kind <;> simp only [byte2Outputs, Byte2Kind.outputSize,
    List.size_toArray, List.length_cons, List.length_nil]

theorem functionMessage_injective {arities : FunctionArities}
    {left right : Bytecode.AIR.Call}
    (validLeft : FunctionMessageValid arities left)
    (validRight : FunctionMessageValid arities right)
    (same : functionMessage left = functionMessage right) : left = right := by
  obtain ⟨lf, li, lo, lr⟩ := left
  obtain ⟨rf, ri, ro, rr⟩ := right
  obtain ⟨lb, lis, los⟩ := validLeft
  obtain ⟨rb, ris, ros⟩ := validRight
  obtain ⟨index, values⟩ := List.cons.inj (List.cons.inj same).2
  have index := G.ofNat_injective_below lb rb index
  change lf = rf at index
  subst rf
  have inputSize : li.toList.length = ri.toList.length := by
    simp only [Array.length_toList]
    exact lis.trans ris.symm
  change (li.toList ++ lo.toList) ++ [lr] = (ri.toList ++ ro.toList) ++ [rr] at values
  obtain ⟨data, rank⟩ := List.append_inj' values rfl
  obtain ⟨input, output⟩ := List.append_inj data inputSize
  have input := Array.toList_inj.mp input
  have output := Array.toList_inj.mp output
  have rank := (List.cons.inj rank).1
  subst ri
  subst ro
  subst rr
  rfl

theorem exactLookupBalance_functionMessages (arities : FunctionArities)
    {queries : List Bytecode.AIR.Call} {providers : List (Provider Bytecode.AIR.Call)}
    (queryShapes : ∀ query ∈ queries, FunctionMessageValid arities query)
    (providerShapes : ∀ provider ∈ providers, provider.2 ≠ 0 →
      FunctionMessageValid arities provider.1)
    (balanced : ExactLookupBalance (queries.map functionMessage) (mapProviders functionMessage providers)) :
    ExactLookupBalance queries providers :=
  exactLookupBalance_of_injective_on functionMessage (FunctionMessageValid arities)
    (fun left right same => functionMessage_injective left right same)
    queryShapes providerShapes balanced

theorem memoryMessage_injective {width : Nat} {left right : G × Array G}
    (same : memoryMessage width left.1 left.2 = memoryMessage width right.1 right.2) :
    left = right := by
  obtain ⟨pointer, contents⟩ := List.cons.inj (List.cons.inj (List.cons.inj same).2).2
  exact Prod.ext pointer (Array.toList_inj.mp contents)

theorem exactLookupBalance_memoryMessages (width : Nat)
    {queries : List (G × Array G)} {providers : List (Provider (G × Array G))}
    (balanced : ExactLookupBalance (queries.map fun request => memoryMessage width request.1 request.2)
      (mapProviders (fun request => memoryMessage width request.1 request.2) providers)) :
    ExactLookupBalance queries providers :=
  exactLookupBalance_of_injective_on (fun request => memoryMessage width request.1 request.2)
    (fun _ => True) (fun _ _ same => memoryMessage_injective same)
    (fun _ _ => True.intro) (fun _ _ _ => True.intro) balanced

/-- Root messages omit the final rank field; appending its fixed zero does
not change any padded lookup message. -/
theorem padMessage_append_zero {width : Nat} (message : List G) :
    padMessage width (message ++ [0]) = padMessage width message := by
  apply congrArg List.ofFn
  funext i
  by_cases inside : i.val < message.length
  · simp only [List.getElem?_append_left inside]
  · rw [List.getElem?_append_right (by omega)]
    have outside : message[i.val]? = none := List.getElem?_eq_none (by omega)
    rw [outside, Option.getD_none]
    by_cases last : i.val = message.length
    · simp only [last, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    · rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
      rfl

/-- Without an output-arity check, the last output of one request can be
the rank of a shorter return. This holds at every padding width. -/
theorem functionMessage_rank_alias (width : Nat) :
    let output : Bytecode.AIR.Call := ⟨0, #[], #[7], 0⟩
    let rank : Bytecode.AIR.Call := ⟨0, #[], #[], 7⟩
    output ≠ rank ∧ padMessage width (functionMessage output) =
      padMessage width (functionMessage rank) := by
  constructor
  · decide +kernel
  · change padMessage width ([0, 0, 7] ++ [0]) = padMessage width [0, 0, 7]
    exact padMessage_append_zero _

end Aiur.AIR
