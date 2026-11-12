import Ix.IxVM.Refinement.Deserialize
import IxC.Ixon.Verify.BoundedConstant

/-! # The Deserialize slice: the binder-data section

A record's last field is its binder-data section, which IxC reads with
`Ixon.getBinders`:

```
section := nblocks:TagN0 block[nblocks]
block   := ekind:u8 eidx:TagN0 variant:TagN0 nnodes:TagN0 node[nnodes]
node    := b | b k:TagN0 p[k]:TagN0 (tag 2) | 0x03 v:TagN0
b       := tag | input << 3 | result << 6   (tag 0 never, 1 zero, 2 ifAllZero, 4 undecided)
```

IxVM reads it with `IxonDeserialize::get_binders` and its helpers
(`get_binder_node` and, for a byte with a mode other than the default,
`get_moded_binder_node`, `get_binder_node_list`, `get_binder_block`,
`get_binder_block_list`). Each terminating derivation of one of them on a byte
stream refines IxC's codec on the same bytes: IxC's reader succeeds, consumes
the same bytes, and returns the data the Aiur values represent
(`RepBinderNode`, `RepBinderBlock`):

* `getBinderNode_refines_at`, `getModedBinderNode_refines_at`: `Ixon.getBinderNode`;
* `getBinderNodeList_refines_at`: `Ixon.getArray Ixon.getBinderNode count`;
* `getBinderBlock_refines_at`: `Ixon.getBinderBlock`;
* `getBinderBlockList_refines_at`: `Ixon.getArray Ixon.getBinderBlock count`;
* `getBinders_refines_at`, `getBinders_refines`: `Ixon.getBinders`.

IxVM's reader also asserts the record's and the section's local canonical form
(the record's level count below 2^32, range-checked by `max_lvls` before the
section is read and passed here as `lvls`; a known `ekind`, a block's index and
variant below 2^32, a root block at variant 0, no empty block or parameter list,
parameters strictly ascending and below the level count, blocks strictly
ascending). Those assertions only narrow what IxVM accepts, so the proofs pass
over them: they need only that an assertion leaves the heap extended. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace IxVM.Refinement.Deserialize

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.TagN

set_option linter.unusedSimpArgs false

/-! ## Representations -/

/-- The prepared enum symbol for `Lists::Node<Ixon::BinderNode>`. -/
abbrev binderNodeListEnum : String :=
  instanceName [] "Lists::Node" (some [(.named "Ixon::BinderNode" [])])

/-- The prepared enum symbol for `Lists::Node<Ixon::BinderBlock>`. -/
abbrev binderBlockListEnum : String :=
  instanceName [] "Lists::Node" (some [(.named "Ixon::BinderBlock" [])])

/-- Canonical `SourceValue F` representation of an `Ixon.BinderNode` in
`h : Heap F`: an `Ixon::BinderNode` value whose binder variants carry their
mode's wire code (`AllMode.toCode`) as a field, whose `IfAllZero` parameters
are a heap list of `UInt64::U64`s and whose `Share` variant is a `UInt64::U64`. -/
inductive RepBinderNode (h : Heap F) : Ixon.BinderNode → SourceValue F → Prop where
  | never (m : Ixon.AllMode) :
      RepBinderNode h (.never m)
        (.construct "Ixon::BinderNode" "Never" [.field ((m.toCode.toNat : Nat) : F)])
  | zero (m : Ixon.AllMode) :
      RepBinderNode h (.zero m)
        (.construct "Ixon::BinderNode" "Zero" [.field ((m.toCode.toNat : Nat) : F)])
  | ifAllZero {params : List UInt64} {ptr : SourceValue F} (m : Ixon.AllMode)
      (rep : Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h params ptr) :
      RepBinderNode h (.ifAllZero params.toArray m)
        (.construct "Ixon::BinderNode" "IfAllZero" [ptr, .field ((m.toCode.toNat : Nat) : F)])
  | share (variant : UInt64) :
      RepBinderNode h (.share variant)
        (.construct "Ixon::BinderNode" "Share" [u64Value variant.toNat])
  | undecided (m : Ixon.AllMode) :
      RepBinderNode h (.undecided m)
        (.construct "Ixon::BinderNode" "Undecided" [.field ((m.toCode.toNat : Nat) : F)])

theorem RepBinderNode.mono {h₁ h₂ : Heap F} {n : Ixon.BinderNode} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepBinderNode h₁ n v) : RepBinderNode h₂ n v := by
  cases rep with
  | never m => exact .never m
  | zero m => exact .zero m
  | ifAllZero m r => exact .ifAllZero m (r.mono Aiur.Library.repU64_heapMono₂ ext)
  | share variant => exact .share variant
  | undecided m => exact .undecided m

theorem repBinderNode_heapMono₂ : HeapMono₂ RepBinderNode :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- A binder node whose mode field is a value equal to its mode's code. -/
theorem RepBinderNode.never_of {h : Heap F} {m : Ixon.AllMode} {x : F} {c : Nat}
    (hc : m.toCode.toNat = c) (hx : x = (c : F)) :
    RepBinderNode h (.never m) (.construct "Ixon::BinderNode" "Never" [.field x]) := by
  subst hx; rw [← hc]; exact .never m

theorem RepBinderNode.zero_of {h : Heap F} {m : Ixon.AllMode} {x : F} {c : Nat}
    (hc : m.toCode.toNat = c) (hx : x = (c : F)) :
    RepBinderNode h (.zero m) (.construct "Ixon::BinderNode" "Zero" [.field x]) := by
  subst hx; rw [← hc]; exact .zero m

theorem RepBinderNode.ifAllZero_of {h : Heap F} {params : List UInt64} {ptr : SourceValue F}
    {m : Ixon.AllMode} {x : F} {c : Nat} (hc : m.toCode.toNat = c) (hx : x = (c : F))
    (rep : Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h params ptr) :
    RepBinderNode h (.ifAllZero params.toArray m)
      (.construct "Ixon::BinderNode" "IfAllZero" [ptr, .field x]) := by
  subst hx; rw [← hc]; exact .ifAllZero m rep

theorem RepBinderNode.undecided_of {h : Heap F} {m : Ixon.AllMode} {x : F} {c : Nat}
    (hc : m.toCode.toNat = c) (hx : x = (c : F)) :
    RepBinderNode h (.undecided m) (.construct "Ixon::BinderNode" "Undecided" [.field x]) := by
  subst hx; rw [← hc]; exact .undecided m

/-- Canonical `SourceValue F` representation of an `Ixon.BinderBlock` in
`h : Heap F`: an `Ixon::BinderBlock::Mk` of its kind as a field (`0` for a root,
`1` for a sharing entry), its index and variant as `UInt64::U64`s, and its
nodes as a heap list of `RepBinderNode`s. -/
def RepBinderBlock (h : Heap F) (b : Ixon.BinderBlock) (v : SourceValue F) : Prop :=
  ∃ nodesPtr, v = .construct "Ixon::BinderBlock" "Mk"
      [.field ((if b.shared then 1 else 0 : Nat) : F), u64Value b.index.toNat,
        u64Value b.variant.toNat, nodesPtr] ∧
    Aiur.Library.List.RepList binderNodeListEnum RepBinderNode h b.nodes.toList nodesPtr

theorem RepBinderBlock.mono {h₁ h₂ : Heap F} {b : Ixon.BinderBlock} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepBinderBlock h₁ b v) : RepBinderBlock h₂ b v := by
  obtain ⟨nodesPtr, rfl, nodesRep⟩ := rep
  exact ⟨nodesPtr, rfl, nodesRep.mono repBinderNode_heapMono₂ ext⟩

theorem repBinderBlock_heapMono₂ : HeapMono₂ RepBinderBlock :=
  fun _ _ _ _ ext rep => rep.mono ext

/-! ## IxC's reader on the same bytes -/

/-- **IxC's `Bool` reader on a byte below 2** returns whether the byte is 1. -/
theorem getBool_of_drop_cons {bytes : List UInt8} {i : Nat} {b : UInt8} {rest : List UInt8}
    (hcons : bytes.drop i = b :: rest) (hb : b.toNat < 2) :
    Ixon.Serialize.get (α := Bool) { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok (decide (b.toNat = 1)) { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
  obtain ⟨hu8, -, -⟩ := getU8_of_drop_cons hcons
  change (EStateM.bind Ixon.getU8 _) _ = _
  rw [EStateM.bind, hu8]
  obtain hb0 | hb1 : b.toNat = 0 ∨ b.toNat = 1 := by omega
  · obtain rfl : b = 0 := UInt8.ext hb0
    rfl
  · obtain rfl : b = 1 := UInt8.ext hb1
    rfl

/-- The binder mode whose wire code is `c` (`< 7`). -/
def binderModeOfCode : Nat → Ixon.BinderMode
  | 0 => .many
  | 1 => .borrowed
  | 2 => .unique
  | 3 => .uniqueBorrowed
  | 4 => .once
  | 5 => .onceBorrowed
  | _ => .erased

/-- The result mode whose wire code is `c` (`< 4`). -/
def resultModeOfCode : Nat → Ixon.ResultMode
  | 0 => .shared
  | 1 => .borrowed
  | 2 => .unique
  | _ => .uniqueBorrowed

/-- The mode of a binder node's byte `b` (its bits 3 to 7). -/
def allModeOfByte (b : Nat) : Ixon.AllMode :=
  ⟨binderModeOfCode (b / 8 % 8), resultModeOfCode (b / 64)⟩

/-- **A node byte whose input code is not 7** decodes (`AllMode.ofCode?` of its
high five bits) to `allModeOfByte`, whose code is those bits. -/
theorem allModeOfByte_spec : ∀ n, n < 256 → n / 8 % 8 ≠ 7 →
    Ixon.AllMode.ofCode? (UInt8.ofNat n >>> 3) = some (allModeOfByte n) ∧
      (allModeOfByte n).toCode.toNat = n / 8 := by
  decide +kernel

theorem nodeByte_beq3 : ∀ n, n < 256 → n ≠ 3 → (UInt8.ofNat n == 3) = false := by
  decide +kernel

theorem nodeByte_tag0 : ∀ n, n < 256 → n % 8 = 0 → (UInt8.ofNat n &&& 7) = 0 := by
  decide +kernel

theorem nodeByte_tag1 : ∀ n, n < 256 → n % 8 = 1 → (UInt8.ofNat n &&& 7) = 1 := by
  decide +kernel

theorem nodeByte_tag2 : ∀ n, n < 256 → n % 8 = 2 → (UInt8.ofNat n &&& 7) = 2 := by
  decide +kernel

theorem nodeByte_tag4 : ∀ n, n < 256 → n % 8 = 4 → (UInt8.ofNat n &&& 7) = 4 := by
  decide +kernel

/-- **IxC's node reader on a binder's byte** `b` (not a share's, its input code
not 7): the node of its tag at `allModeOfByte b`, after the tag's payload. -/
theorem getBinderNode_binder {σ σ' : Ixon.GetState} {b : UInt8}
    (hu8 : Ixon.getU8 σ = .ok b σ') (h3 : b.toNat ≠ 3) (hin : b.toNat / 8 % 8 ≠ 7) :
    (b.toNat % 8 = 0 → Ixon.getBinderNode σ = .ok (.never (allModeOfByte b.toNat)) σ') ∧
    (b.toNat % 8 = 1 → Ixon.getBinderNode σ = .ok (.zero (allModeOfByte b.toNat)) σ') ∧
    (b.toNat % 8 = 4 → Ixon.getBinderNode σ = .ok (.undecided (allModeOfByte b.toNat)) σ') ∧
    (b.toNat % 8 = 2 → ∀ {t : Ixon.TagN} {σ2 σ3 : Ixon.GetState} {ps : List UInt64},
      Ixon.getTagN 0 σ' = .ok t σ2 → Ixon.getTagN0Values t.value.toNat σ2 = .ok ps σ3 →
      Ixon.getBinderNode σ = .ok (.ifAllZero ps.toArray (allModeOfByte b.toNat)) σ3) := by
  have hb := b.toNat_lt
  have hm : Ixon.AllMode.ofCode? (b >>> 3) = some (allModeOfByte b.toNat) := by
    have := (allModeOfByte_spec b.toNat hb hin).1
    rwa [UInt8.ofNat_toNat] at this
  have hbeq : (b == 3) = false := by
    have := nodeByte_beq3 b.toNat hb h3
    rwa [UInt8.ofNat_toNat] at this
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht t σ2 σ3 ps hok2 hok3 => ?_⟩
  · have hand : b &&& 7 = 0 := by
      have := nodeByte_tag0 b.toNat hb ht
      rwa [UInt8.ofNat_toNat] at this
    simp only [Ixon.getBinderNode, bind, EStateM.bind, hu8, hbeq, hm, hand, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  · have hand : b &&& 7 = 1 := by
      have := nodeByte_tag1 b.toNat hb ht
      rwa [UInt8.ofNat_toNat] at this
    simp only [Ixon.getBinderNode, bind, EStateM.bind, hu8, hbeq, hm, hand, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  · have hand : b &&& 7 = 4 := by
      have := nodeByte_tag4 b.toNat hb ht
      rwa [UInt8.ofNat_toNat] at this
    simp only [Ixon.getBinderNode, bind, EStateM.bind, hu8, hbeq, hm, hand, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  · have hand : b &&& 7 = 2 := by
      have := nodeByte_tag2 b.toNat hb ht
      rwa [UInt8.ofNat_toNat] at this
    simp only [Ixon.getBinderNode, bind, EStateM.bind, hu8, hbeq, hm, hand, Bool.false_eq_true,
      ↓reduceIte, hok2, hok3]
    rfl

/-- **IxC's node reader on the share byte 3**: the share node of the variant
that follows. -/
theorem getBinderNode_share {σ σ' σ2 : Ixon.GetState} {t : Ixon.TagN}
    (hu8 : Ixon.getU8 σ = .ok 3 σ') (hok2 : Ixon.getTagN 0 σ' = .ok t σ2) :
    Ixon.getBinderNode σ = .ok (.share t.value) σ2 := by
  have h3 : ((3 : UInt8) == 3) = true := by decide
  simp only [Ixon.getBinderNode, bind, EStateM.bind, hu8, h3, eq_self_iff_true, ↓reduceIte, hok2]
  rfl

/-! ## Nodes -/

/-- The binding of `let [b0, …, b7] = UInt8::bit_decomposition(x)`. -/
theorem matchPattern_bits8 {types : Types} {heap : Heap F} {x : Nat} {bs : Environment F Nat}
    (mt : W.matchPattern types heap
      (.array [(.bind "b0"), (.bind "b1"), (.bind "b2"), (.bind "b3"),
               (.bind "b4"), (.bind "b5"), (.bind "b6"), (.bind "b7")])
      (.tuple [.field ((x % 2 : Nat) : F), .field ((x / 2 % 2 : Nat) : F),
        .field ((x / 4 % 2 : Nat) : F), .field ((x / 8 % 2 : Nat) : F),
        .field ((x / 16 % 2 : Nat) : F), .field ((x / 32 % 2 : Nat) : F),
        .field ((x / 64 % 2 : Nat) : F), .field ((x / 128 % 2 : Nat) : F)]) = .ok (some bs)) :
    bs = [("b0", .field ((x % 2 : Nat) : F)), ("b1", .field ((x / 2 % 2 : Nat) : F)),
      ("b2", .field ((x / 4 % 2 : Nat) : F)), ("b3", .field ((x / 8 % 2 : Nat) : F)),
      ("b4", .field ((x / 16 % 2 : Nat) : F)), ("b5", .field ((x / 32 % 2 : Nat) : F)),
      ("b6", .field ((x / 64 % 2 : Nat) : F)), ("b7", .field ((x / 128 % 2 : Nat) : F))] := by
  rw [matchPattern_array] at mt
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Option.some.injEq] at mt
  exact mt.symm

/-- **Every terminating derivation of `IxonDeserialize::get_moded_binder_node`**
on a node byte `b` above 4 (read by IxC's `getU8` at `i`) refines
`Ixon.getBinderNode` at `i`: the byte is a binder's (tag 0, 1, 2 or 4) whose
input code is not 7, and the node carries its mode's code. -/
theorem getModedBinderNode_refines_at {bytes : List UInt8} {i : Nat} {b : UInt8}
    {stream lvls r : SourceValue F} {h h' : Heap F}
    (hu8 : Ixon.getU8 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok b { idx := i + 1, bytes := ⟨bytes.toArray⟩ })
    (hb5 : 4 < b.toNat)
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop (i + 1)) stream)
    (ev : EvalFn W "IxonDeserialize::get_moded_binder_node"
      [.field ((b.toNat : Nat) : F), stream, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (node : Ixon.BinderNode) (n : Nat) (nodeVal restPtr : SourceValue F),
      Ixon.getBinderNode { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok node { idx := i + 1 + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [nodeVal, restPtr] ∧
      RepBinderNode h' node nodeVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + 1 + n)) restPtr := by
  have hext := ev.heap_extends
  have hb : b.toNat < 256 := b.toNat_lt
  have body := ev.function_inv IxVM.IxonDeserialize.get_moded_binder_node.lookup
    (by simp [IxVM.IxonDeserialize.get_moded_binder_node, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_moded_binder_node] at body
  -- let [b0, b1, b2, b3, b4, b5, b6, b7] = UInt8::bit_decomposition(byte)
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, rfl⟩ := u8BitDecomposition_refines hb callee9
  obtain rfl := matchPattern_bits8 mt4
  -- assert_eq!(b3 * b4 * b5, 0, ...)
  obtain ⟨_, m16, bs17, d18, mt19, d20⟩ := d5.letValue_inv
  obtain ⟨vs21, args22, app23⟩ := d18.builtin_inv
  obtain ⟨v24, vs25, m26, rfl, d27, args28⟩ := args22.cons_inv
  obtain ⟨x34, y5, _, d_m34, d_b5, op1⟩ := d27.binary_inv
  obtain ⟨y3, y4, _, d_b3, d_b4, op2⟩ := d_m34.binary_inv
  obtain ⟨l3, rfl⟩ := d_b3.var_inv; simp at l3; subst l3
  obtain ⟨l4, rfl⟩ := d_b4.var_inv; simp at l4; subst l4
  obtain ⟨l5, rfl⟩ := d_b5.var_inv; simp at l5; subst l5
  simp only [evalBinOp, Except.ok.injEq] at op2; subst op2
  simp only [evalBinOp, Except.ok.injEq] at op1; subst op1
  obtain ⟨v29, vs30, m31, rfl, d32, args33⟩ := args28.cons_inv
  obtain ⟨rfl, rfl⟩ := d32.literal_inv
  obtain ⟨rfl, rfl⟩ := args33.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte, Value.field.injEq] at app23
  split_ifs at app23 with hprod
  have hin : b.toNat / 8 % 8 ≠ 7 := by
    intro h7
    have e3 : b.toNat / 8 % 2 = 1 := by omega
    have e4 : b.toNat / 16 % 2 = 1 := by omega
    have e5 : b.toNat / 32 % 2 = 1 := by omega
    rw [e3, e4, e5] at hprod
    simp at hprod
  rw [matchPattern_wildcard] at mt19
  simp only [Except.ok.injEq, Option.some.injEq] at mt19; subst mt19
  -- let mode = b3 + 2 * b4 + 4 * b5 + 8 * b6 + 16 * b7
  obtain ⟨vmode, m40, bs41, d42, mt43, d44⟩ := d20.letValue_inv
  obtain ⟨s4, t7, _, d_s4, d_t7, opA4⟩ := d42.binary_inv
  obtain ⟨k7, w7, _, d_k7, d_w7, opM7⟩ := d_t7.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k7.literal_inv
  obtain ⟨l7, rfl⟩ := d_w7.var_inv; simp at l7; subst l7
  obtain ⟨s3, t6, _, d_s3, d_t6, opA3⟩ := d_s4.binary_inv
  obtain ⟨k6, w6, _, d_k6, d_w6, opM6⟩ := d_t6.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k6.literal_inv
  obtain ⟨l6, rfl⟩ := d_w6.var_inv; simp at l6; subst l6
  obtain ⟨s2, t5, _, d_s2, d_t5, opA2⟩ := d_s3.binary_inv
  obtain ⟨k5, w5, _, d_k5, d_w5, opM5⟩ := d_t5.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k5.literal_inv
  obtain ⟨l5', rfl⟩ := d_w5.var_inv; simp at l5'; subst l5'
  obtain ⟨w3, t4, _, d_w3, d_t4, opA1⟩ := d_s2.binary_inv
  obtain ⟨l3', rfl⟩ := d_w3.var_inv; simp at l3'; subst l3'
  obtain ⟨k4, w4, _, d_k4, d_w4, opM4⟩ := d_t4.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k4.literal_inv
  obtain ⟨l4', rfl⟩ := d_w4.var_inv; simp at l4'; subst l4'
  simp only [evalBinOp, Except.ok.injEq] at opM4; subst opM4
  simp only [evalBinOp, Except.ok.injEq] at opA1; subst opA1
  simp only [evalBinOp, Except.ok.injEq] at opM5; subst opM5
  simp only [evalBinOp, Except.ok.injEq] at opA2; subst opA2
  simp only [evalBinOp, Except.ok.injEq] at opM6; subst opM6
  simp only [evalBinOp, Except.ok.injEq] at opA3; subst opA3
  simp only [evalBinOp, Except.ok.injEq] at opM7; subst opM7
  simp only [evalBinOp, Except.ok.injEq] at opA4; subst opA4
  rw [matchPattern_bind] at mt43
  simp only [Except.ok.injEq, Option.some.injEq] at mt43; subst mt43
  -- match b0 + 2 * b1 + 4 * b2
  obtain ⟨vt, m50, bs51, body52, d53, sel54, d55⟩ := d44.matchValue_inv
  obtain ⟨u2, t2, _, d_u2, d_t2, opB2⟩ := d53.binary_inv
  obtain ⟨k2, w2, _, d_k2, d_w2, opN2⟩ := d_t2.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k2.literal_inv
  obtain ⟨lw2, rfl⟩ := d_w2.var_inv; simp at lw2; subst lw2
  obtain ⟨w0, t1, _, d_w0, d_t1, opB1⟩ := d_u2.binary_inv
  obtain ⟨lw0, rfl⟩ := d_w0.var_inv; simp at lw0; subst lw0
  obtain ⟨k1, w1, _, d_k1, d_w1, opN1⟩ := d_t1.binary_inv
  obtain ⟨rfl, rfl⟩ := d_k1.literal_inv
  obtain ⟨lw1, rfl⟩ := d_w1.var_inv; simp at lw1; subst lw1
  simp only [evalBinOp, Except.ok.injEq] at opN1; subst opN1
  simp only [evalBinOp, Except.ok.injEq] at opB1; subst opB1
  simp only [evalBinOp, Except.ok.injEq] at opN2; subst opN2
  simp only [evalBinOp, Except.ok.injEq] at opB2; subst opB2
  -- the tag and the mode as numbers
  have hsplit3 := congrArg (fun n : Nat => (n : F))
    (show b.toNat % 8 = b.toNat % 2 + 2 * (b.toNat / 2 % 2) + 4 * (b.toNat / 4 % 2) by omega)
  have hsplit8 := congrArg (fun n : Nat => (n : F))
    (show b.toNat / 8 = b.toNat / 8 % 2 + 2 * (b.toNat / 16 % 2) + 4 * (b.toNat / 32 % 2) +
      8 * (b.toNat / 64 % 2) + 16 * (b.toNat / 128 % 2) by omega)
  push_cast at hsplit3 hsplit8
  have hcode := (allModeOfByte_spec b.toNat hb hin).2
  obtain ⟨hnever, hzero, hundec, hiaz⟩ := getBinderNode_binder hu8 (by omega) hin
  rcases selectArm_literal_inv sel54 with ⟨hc0, rfl, rfl⟩ | ⟨_, sel55⟩
  · -- tag 0: `never`
    have ht : b.toNat % 8 = 0 :=
      (natCast_eq_zero_iff (by omega)).mp
        (Eq.trans hsplit3 (Eq.trans (by ring) (Value.field.inj hc0)))
    obtain ⟨vs60, args61, rfl⟩ := d55.tuple_inv
    obtain ⟨v62, vs63, m64, rfl, d65, args66⟩ := args61.cons_inv
    obtain ⟨vs67, args68, rfl⟩ := d65.construct_inv
    obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args68.cons_inv
    obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
    obtain ⟨rfl, rfl⟩ := args73.nil_inv
    obtain ⟨v75, vs76, m77, rfl, d78, args79⟩ := args66.cons_inv
    obtain ⟨l80, rfl⟩ := d78.var_inv; simp at l80; subst l80
    obtain ⟨rfl, rfl⟩ := args79.nil_inv
    refine ⟨hext, .never (allModeOfByte b.toNat), 0, _, stream, by simpa using hnever ht, rfl,
      ?_, by simpa using Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum hext rep⟩
    simp only [instanceName_plain_some]
    exact RepBinderNode.never_of hcode (Eq.trans (by ring) hsplit8.symm)
  · rcases selectArm_literal_inv sel55 with ⟨hc1, rfl, rfl⟩ | ⟨_, sel56⟩
    · -- tag 1: `zero`
      have ht : b.toNat % 8 = 1 :=
        (natCast_eq_one_iff (by omega)).mp
          (Eq.trans hsplit3 (Eq.trans (by ring) (Value.field.inj hc1)))
      obtain ⟨vs60, args61, rfl⟩ := d55.tuple_inv
      obtain ⟨v62, vs63, m64, rfl, d65, args66⟩ := args61.cons_inv
      obtain ⟨vs67, args68, rfl⟩ := d65.construct_inv
      obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args68.cons_inv
      obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
      obtain ⟨rfl, rfl⟩ := args73.nil_inv
      obtain ⟨v75, vs76, m77, rfl, d78, args79⟩ := args66.cons_inv
      obtain ⟨l80, rfl⟩ := d78.var_inv; simp at l80; subst l80
      obtain ⟨rfl, rfl⟩ := args79.nil_inv
      refine ⟨hext, .zero (allModeOfByte b.toNat), 0, _, stream, by simpa using hzero ht, rfl,
        ?_, by simpa using Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum hext rep⟩
      simp only [instanceName_plain_some]
      exact RepBinderNode.zero_of hcode (Eq.trans (by ring) hsplit8.symm)
    · rcases selectArm_literal_inv sel56 with ⟨hc2, rfl, rfl⟩ | ⟨_, sel57⟩
      · -- tag 2: `ifAllZero params`
        have ht : b.toNat % 8 = 2 :=
          (natCast_eq_ofNat_iff (n := 2) (by omega) (by decide)).mp
            (Eq.trans hsplit3 (Eq.trans (by ring) (Value.field.inj hc2)))
        -- let (count, s2) = get_tagn0(s)
        obtain ⟨v40, m41, bs42, d43, mt44, d45⟩ := d55.letValue_inv
        obtain ⟨vs46, m47, args48, callee49⟩ := d43.call_inv
        obtain ⟨v50, vs51, m52, rfl, d53', args54⟩ := args48.cons_inv
        obtain ⟨l55, rfl⟩ := d53'.var_inv; simp at l55; subst l55
        obtain ⟨rfl, rfl⟩ := args54.nil_inv
        rw [instanceName_plain_some] at callee49
        obtain ⟨rfl, t, n2, restPtr2, hok2, -, hrep2, rfl⟩ := getTagN0_refines_at rep callee49
        obtain rfl := matchPattern_tuple2_bind rfl mt44
        -- assert_eq!(UInt64::is_zero(count), 0, ...)
        obtain ⟨v60, m61, bs62, d63, mt64, d65⟩ := d45.letValue_inv
        rw [matchPattern_wildcard] at mt64
        simp only [Except.ok.injEq, Option.some.injEq] at mt64; subst mt64
        have ext63 := d63.heap_extends
        -- let (params, s3) = get_u64_list(s2, count)
        obtain ⟨v70, m71, bs72, d73, mt74, d75⟩ := d65.letValue_inv
        obtain ⟨vs76, m77, args78, callee79⟩ := d73.call_inv
        obtain ⟨v80, vs81, m82, rfl, d83, args84⟩ := args78.cons_inv
        obtain ⟨l85, rfl⟩ := d83.var_inv; simp at l85; subst l85
        obtain ⟨v86, vs87, m88, rfl, d89, args90⟩ := args84.cons_inv
        obtain ⟨l91, rfl⟩ := d89.var_inv; simp at l91; subst l91
        obtain ⟨rfl, rfl⟩ := args90.nil_inv
        rw [instanceName_plain_some] at callee79
        obtain ⟨-, params, n3, listPtr, restPtr3, hok3, -, rfl, listRep, hrep3⟩ :=
          getU64List_refines_at t.value.toNat t.value.toNat_lt
            (Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext63 hrep2) callee79
        obtain rfl := matchPattern_tuple2_bind rfl mt74
        -- assert_params_canonical(params, lvls)
        obtain ⟨v92, m93, bs94, d95, mt96, d97⟩ := d75.letValue_inv
        rw [matchPattern_wildcard] at mt96
        simp only [Except.ok.injEq, Option.some.injEq] at mt96; subst mt96
        have ext95 := d95.heap_extends
        -- (IfAllZero(params, mode), s3)
        obtain ⟨vs98, args99, rfl⟩ := d97.tuple_inv
        obtain ⟨v100, vs101, m102, rfl, d103, args104⟩ := args99.cons_inv
        obtain ⟨vs105, args106, rfl⟩ := d103.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v112, vs112, m112, rfl, d112, args112⟩ := args111.cons_inv
        obtain ⟨l112', rfl⟩ := d112.var_inv; simp at l112'; subst l112'
        obtain ⟨rfl, rfl⟩ := args112.nil_inv
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args104.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        refine ⟨hext, .ifAllZero params.toArray (allModeOfByte b.toNat), n2 + n3, _, restPtr3,
          ?_, rfl, ?_, ?_⟩
        · rw [show i + 1 + (n2 + n3) = i + 1 + n2 + n3 by omega]
          exact hiaz ht hok2 hok3
        · simp only [instanceName_plain_some]
          exact RepBinderNode.ifAllZero_of hcode (Eq.trans (by ring) hsplit8.symm)
            (listRep.mono Aiur.Library.repU64_heapMono₂ ext95)
        · rw [show i + 1 + (n2 + n3) = i + 1 + n2 + n3 by omega]
          exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext95 hrep3
      · rcases selectArm_literal_inv sel57 with ⟨hc4, rfl, rfl⟩ | ⟨_, sel58⟩
        · -- tag 4: the undecided node
          have ht : b.toNat % 8 = 4 :=
            (natCast_eq_ofNat_iff (n := 4) (by omega) (by decide)).mp
              (Eq.trans hsplit3 (Eq.trans (by ring) (Value.field.inj hc4)))
          obtain ⟨vs60, args61, rfl⟩ := d55.tuple_inv
          obtain ⟨v62, vs63, m64, rfl, d65, args66⟩ := args61.cons_inv
          obtain ⟨vs67, args68, rfl⟩ := d65.construct_inv
          obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args68.cons_inv
          obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
          obtain ⟨rfl, rfl⟩ := args73.nil_inv
          obtain ⟨v75, vs76, m77, rfl, d78, args79⟩ := args66.cons_inv
          obtain ⟨l80, rfl⟩ := d78.var_inv; simp at l80; subst l80
          obtain ⟨rfl, rfl⟩ := args79.nil_inv
          refine ⟨hext, .undecided (allModeOfByte b.toNat), 0, _, stream, by simpa using hundec ht,
            rfl, ?_, by simpa using Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum hext rep⟩
          simp only [instanceName_plain_some]
          exact RepBinderNode.undecided_of hcode (Eq.trans (by ring) hsplit8.symm)
        · simp [SourceSemantics.selectArm] at sel58

/-- **Every terminating derivation of `IxonDeserialize::get_binder_node` at
reader offset `i`** refines `Ixon.getBinderNode` at `i`, returning a
`RepBinderNode` value and the advanced stream pointer. -/
theorem getBinderNode_refines_at {bytes : List UInt8} {i : Nat}
    {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_binder_node" [stream, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (node : Ixon.BinderNode) (n : Nat) (nodeVal restPtr : SourceValue F),
      Ixon.getBinderNode { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok node { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [nodeVal, restPtr] ∧
      RepBinderNode h' node nodeVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  have hext := ev.heap_extends
  have body := ev.function_inv IxVM.IxonDeserialize.get_binder_node.lookup
    (by simp [IxVM.IxonDeserialize.get_binder_node, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_binder_node] at body
  -- let (tag, s) = read_byte(stream)
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, b, rest, restPtr1, hcons, hrep1, rfl⟩ := readByte_refines rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨hu8, hdrop, -⟩ := getU8_of_drop_cons hcons
  rw [← hdrop] at hrep1
  have hb : b.toNat < 256 := b.toNat_lt
  -- match UInt8::to_field(tag)
  obtain ⟨v16, m17, bs18, body19, d20, sel21, d22⟩ := d5.matchValue_inv
  obtain ⟨vs23, m24, args25, callee26⟩ := d20.call_inv
  obtain ⟨v27, vs28, m29, rfl, d30, args31⟩ := args25.cons_inv
  obtain ⟨l32, rfl⟩ := d30.var_inv; simp at l32; subst l32
  obtain ⟨rfl, rfl⟩ := args31.nil_inv
  rw [instanceName_plain_some] at callee26
  obtain ⟨rfl, rfl⟩ := u8ToField_refines callee26
  rcases selectArm_literal_inv sel21 with ⟨hc0, rfl, rfl⟩ | ⟨hn0, sel1⟩
  · -- byte 0: `never`, default mode
    obtain rfl : b = 0 := UInt8.ext ((natCast_eq_zero_iff hb).mp (Value.field.inj hc0))
    obtain ⟨vs40, args41, rfl⟩ := d22.tuple_inv
    obtain ⟨v42, vs43, m44, rfl, d45, args46⟩ := args41.cons_inv
    obtain ⟨vs47, args48, rfl⟩ := d45.construct_inv
    obtain ⟨v47, vs47', m47, rfl, d47, args47⟩ := args48.cons_inv
    obtain ⟨rfl, rfl⟩ := d47.literal_inv
    obtain ⟨rfl, rfl⟩ := args47.nil_inv
    obtain ⟨v49, vs50, m51, rfl, d52, args53⟩ := args46.cons_inv
    obtain ⟨l54, rfl⟩ := d52.var_inv; simp at l54; subst l54
    obtain ⟨rfl, rfl⟩ := args53.nil_inv
    refine ⟨hext, .never (allModeOfByte (0 : UInt8).toNat), 1, _, restPtr1,
      (getBinderNode_binder hu8 (by decide) (by decide)).1 (by decide), rfl, ?_, hrep1⟩
    simp only [instanceName_plain_some]
    exact RepBinderNode.never_of (c := 0) (by decide) Nat.cast_zero.symm
  · rcases selectArm_literal_inv sel1 with ⟨hc1, rfl, rfl⟩ | ⟨hn1, sel2⟩
    · -- byte 1: `zero`, default mode
      obtain rfl : b = 1 := UInt8.ext ((natCast_eq_one_iff hb).mp (Value.field.inj hc1))
      obtain ⟨vs40, args41, rfl⟩ := d22.tuple_inv
      obtain ⟨v42, vs43, m44, rfl, d45, args46⟩ := args41.cons_inv
      obtain ⟨vs47, args48, rfl⟩ := d45.construct_inv
      obtain ⟨v47, vs47', m47, rfl, d47, args47⟩ := args48.cons_inv
      obtain ⟨rfl, rfl⟩ := d47.literal_inv
      obtain ⟨rfl, rfl⟩ := args47.nil_inv
      obtain ⟨v49, vs50, m51, rfl, d52, args53⟩ := args46.cons_inv
      obtain ⟨l54, rfl⟩ := d52.var_inv; simp at l54; subst l54
      obtain ⟨rfl, rfl⟩ := args53.nil_inv
      refine ⟨hext, .zero (allModeOfByte (1 : UInt8).toNat), 1, _, restPtr1,
        (getBinderNode_binder hu8 (by decide) (by decide)).2.1 (by decide), rfl, ?_, hrep1⟩
      simp only [instanceName_plain_some]
      exact RepBinderNode.zero_of (c := 0) (by decide) Nat.cast_zero.symm
    · rcases selectArm_literal_inv sel2 with ⟨hc2, rfl, rfl⟩ | ⟨hn2, sel3⟩
      · -- byte 2: `ifAllZero params`, default mode
        obtain rfl : b = 2 :=
          UInt8.ext ((natCast_eq_ofNat_iff (n := 2) hb (by decide)).mp (Value.field.inj hc2))
        -- let (count, s2) = get_tagn0(s)
        obtain ⟨v40, m41, bs42, d43, mt44, d45⟩ := d22.letValue_inv
        obtain ⟨vs46, m47, args48, callee49⟩ := d43.call_inv
        obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args48.cons_inv
        obtain ⟨l55, rfl⟩ := d53.var_inv; simp at l55; subst l55
        obtain ⟨rfl, rfl⟩ := args54.nil_inv
        rw [instanceName_plain_some] at callee49
        obtain ⟨rfl, t, n2, restPtr2, hok2, -, hrep2, rfl⟩ := getTagN0_refines_at hrep1 callee49
        obtain rfl := matchPattern_tuple2_bind rfl mt44
        -- assert_eq!(UInt64::is_zero(count), 0, ...)
        obtain ⟨v60, m61, bs62, d63, mt64, d65⟩ := d45.letValue_inv
        rw [matchPattern_wildcard] at mt64
        simp only [Except.ok.injEq, Option.some.injEq] at mt64; subst mt64
        have ext63 := d63.heap_extends
        -- let (params, s3) = get_u64_list(s2, count)
        obtain ⟨v70, m71, bs72, d73, mt74, d75⟩ := d65.letValue_inv
        obtain ⟨vs76, m77, args78, callee79⟩ := d73.call_inv
        obtain ⟨v80, vs81, m82, rfl, d83, args84⟩ := args78.cons_inv
        obtain ⟨l85, rfl⟩ := d83.var_inv; simp at l85; subst l85
        obtain ⟨v86, vs87, m88, rfl, d89, args90⟩ := args84.cons_inv
        obtain ⟨l91, rfl⟩ := d89.var_inv; simp at l91; subst l91
        obtain ⟨rfl, rfl⟩ := args90.nil_inv
        rw [instanceName_plain_some] at callee79
        obtain ⟨-, params, n3, listPtr, restPtr3, hok3, -, rfl, listRep, hrep3⟩ :=
          getU64List_refines_at t.value.toNat t.value.toNat_lt
            (Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext63 hrep2) callee79
        obtain rfl := matchPattern_tuple2_bind rfl mt74
        -- assert_params_canonical(params, lvls)
        obtain ⟨v92, m93, bs94, d95, mt96, d97⟩ := d75.letValue_inv
        rw [matchPattern_wildcard] at mt96
        simp only [Except.ok.injEq, Option.some.injEq] at mt96; subst mt96
        have ext95 := d95.heap_extends
        -- (IfAllZero(params, 0), s3)
        obtain ⟨vs98, args99, rfl⟩ := d97.tuple_inv
        obtain ⟨v100, vs101, m102, rfl, d103, args104⟩ := args99.cons_inv
        obtain ⟨vs105, args106, rfl⟩ := d103.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v112, vs112, m112, rfl, d112, args112⟩ := args111.cons_inv
        obtain ⟨rfl, rfl⟩ := d112.literal_inv
        obtain ⟨rfl, rfl⟩ := args112.nil_inv
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args104.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        refine ⟨hext, .ifAllZero params.toArray (allModeOfByte (2 : UInt8).toNat), 1 + n2 + n3, _,
          restPtr3, ?_, rfl, ?_, ?_⟩
        · rw [show i + (1 + n2 + n3) = i + 1 + n2 + n3 by omega]
          exact (getBinderNode_binder hu8 (by decide) (by decide)).2.2.2 (by decide) hok2 hok3
        · simp only [instanceName_plain_some]
          exact RepBinderNode.ifAllZero_of (c := 0) (by decide) Nat.cast_zero.symm
            (listRep.mono Aiur.Library.repU64_heapMono₂ ext95)
        · rw [show i + (1 + n2 + n3) = i + 1 + n2 + n3 by omega]
          exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext95 hrep3
      · rcases selectArm_literal_inv sel3 with ⟨hc3, rfl, rfl⟩ | ⟨hn3, sel4⟩
        · -- byte 3: a share node
          obtain rfl : b = 3 :=
            UInt8.ext ((natCast_eq_ofNat_iff (n := 3) hb (by decide)).mp (Value.field.inj hc3))
          -- let (variant, s2) = get_tagn0(s)
          obtain ⟨v40, m41, bs42, d43, mt44, d45⟩ := d22.letValue_inv
          obtain ⟨vs46, m47, args48, callee49⟩ := d43.call_inv
          obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args48.cons_inv
          obtain ⟨l55, rfl⟩ := d53.var_inv; simp at l55; subst l55
          obtain ⟨rfl, rfl⟩ := args54.nil_inv
          rw [instanceName_plain_some] at callee49
          obtain ⟨rfl, t, n2, restPtr2, hok2, -, hrep2, rfl⟩ := getTagN0_refines_at hrep1 callee49
          obtain rfl := matchPattern_tuple2_bind rfl mt44
          -- (Share(variant), s2)
          obtain ⟨vs56, args57, rfl⟩ := d45.tuple_inv
          obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args57.cons_inv
          obtain ⟨vs63, args64, rfl⟩ := d61.construct_inv
          obtain ⟨v65, vs66, m67, rfl, d68, args69⟩ := args64.cons_inv
          obtain ⟨l70, rfl⟩ := d68.var_inv; simp at l70; subst l70
          obtain ⟨rfl, rfl⟩ := args69.nil_inv
          obtain ⟨v71, vs72, m73, rfl, d74, args75⟩ := args62.cons_inv
          obtain ⟨l76, rfl⟩ := d74.var_inv; simp at l76; subst l76
          obtain ⟨rfl, rfl⟩ := args75.nil_inv
          refine ⟨hext, .share t.value, 1 + n2, _, restPtr2, ?_, rfl, ?_, ?_⟩
          · rw [show i + (1 + n2) = i + 1 + n2 by omega]
            exact getBinderNode_share hu8 hok2
          · simp only [instanceName_plain_some]
            exact .share t.value
          · rw [show i + (1 + n2) = i + 1 + n2 by omega]
            exact hrep2
        · rcases selectArm_literal_inv sel4 with ⟨hc4, rfl, rfl⟩ | ⟨hn4, sel5⟩
          · -- byte 4: the undecided node, default mode
            obtain rfl : b = 4 :=
              UInt8.ext ((natCast_eq_ofNat_iff (n := 4) hb (by decide)).mp (Value.field.inj hc4))
            obtain ⟨vs40, args41, rfl⟩ := d22.tuple_inv
            obtain ⟨v42, vs43, m44, rfl, d45, args46⟩ := args41.cons_inv
            obtain ⟨vs47, args48, rfl⟩ := d45.construct_inv
            obtain ⟨v47, vs47', m47, rfl, d47, args47⟩ := args48.cons_inv
            obtain ⟨rfl, rfl⟩ := d47.literal_inv
            obtain ⟨rfl, rfl⟩ := args47.nil_inv
            obtain ⟨v49, vs50, m51, rfl, d52, args53⟩ := args46.cons_inv
            obtain ⟨l54, rfl⟩ := d52.var_inv; simp at l54; subst l54
            obtain ⟨rfl, rfl⟩ := args53.nil_inv
            refine ⟨hext, .undecided (allModeOfByte (4 : UInt8).toNat), 1, _, restPtr1,
              (getBinderNode_binder hu8 (by decide) (by decide)).2.2.1 (by decide), rfl, ?_, hrep1⟩
            simp only [instanceName_plain_some]
            exact RepBinderNode.undecided_of (c := 0) (by decide) Nat.cast_zero.symm
          · -- any other byte: a binder at a mode other than the default
            obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel5
            have hb5 : 4 < b.toNat := by
              have h0 : b.toNat ≠ 0 := fun e => hn0 (by rw [e]; simp)
              have h1 : b.toNat ≠ 1 := fun e => hn1 (by rw [e]; simp)
              have h2 : b.toNat ≠ 2 := fun e => hn2 (by rw [e]; simp)
              have h3 : b.toNat ≠ 3 := fun e => hn3 (by rw [e]; simp)
              have h4 : b.toNat ≠ 4 := fun e => hn4 (by rw [e]; simp)
              omega
            obtain ⟨vs40, m41, args42, callee43⟩ := d22.call_inv
            obtain ⟨v44, vs45, m46, rfl, d47, args48⟩ := args42.cons_inv
            obtain ⟨l49, rfl⟩ := d47.var_inv; simp at l49; subst l49
            obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args48.cons_inv
            obtain ⟨l55, rfl⟩ := d53.var_inv; simp at l55; subst l55
            obtain ⟨v56, vs57, m58, rfl, d59, args60⟩ := args54.cons_inv
            obtain ⟨l61, rfl⟩ := d59.var_inv; simp at l61; subst l61
            obtain ⟨rfl, rfl⟩ := args60.nil_inv
            rw [instanceName_plain_some] at callee43
            obtain ⟨ext1, node, n, nodeVal, restPtr, hok, rfl, nodeRep, hrep⟩ :=
              getModedBinderNode_refines_at hu8 hb5 hrep1 callee43
            exact ⟨hext, node, 1 + n, nodeVal, restPtr, by rw [← Nat.add_assoc]; exact hok, rfl,
              nodeRep, by rw [← Nat.add_assoc]; exact hrep⟩

/-- **Every terminating derivation of `IxonDeserialize::get_binder_node_list`
at reader offset `i`** refines `Ixon.getArray Ixon.getBinderNode count` at
`i`, allocating a `RepList binderNodeListEnum RepBinderNode` of the nodes and
advancing the stream pointer by the consumed bytes. -/
theorem getBinderNodeList_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_binder_node_list" [stream, u64Value count, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (nodes : Array Ixon.BinderNode) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getArray Ixon.getBinderNode count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok nodes { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList binderNodeListEnum RepBinderNode h' nodes.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    have hext := ev.heap_extends
    have body := ev.function_inv IxVM.IxonDeserialize.get_binder_node_list.lookup
      (by simp [IxVM.IxonDeserialize.get_binder_node_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_binder_node_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      refine ⟨hext, #[], 0, _, stream,
        by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep binderNodeListEnum RepBinderNode _,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (Heap.Extends.snoc _ _) rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have hext := ev.heap_extends
    have body := ev.function_inv IxVM.IxonDeserialize.get_binder_node_list.lookup
      (by simp [IxVM.IxonDeserialize.get_binder_node_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_binder_node_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · -- let (node, s) = get_binder_node(stream, lvls)
        obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨v46, vs47, m48, rfl, d49, args50⟩ := args44.cons_inv
        obtain ⟨l51, rfl⟩ := d49.var_inv; simp at l51; subst l51
        obtain ⟨rfl, rfl⟩ := args50.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨-, node, n1, nodeVal, restPtr1, hok1, rfl, nodeRep, hrep1⟩ :=
          getBinderNode_refines_at rep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        -- let (rest, s2) = get_binder_node_list(s, UInt64::saturating_pred(count), lvls)
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨v85, vs86, m87, rfl, d88, args89⟩ := args74.cons_inv
        obtain ⟨l90, rfl⟩ := d88.var_inv; simp at l90; subst l90
        obtain ⟨rfl, rfl⟩ := args89.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext2, tailNodes, n2, tailListPtr, restPtr2, hok2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain rfl := matchPattern_tuple2_bind rfl mt58
        -- ((&(Lists::Node::Cons(node, rest))), s2)
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
        obtain ⟨l124, rfl⟩ := d122.var_inv; simp at l124; subst l124
        obtain ⟨rfl, rfl⟩ := args123.nil_inv
        rw [value_type_construct]
        have consRep := Aiur.Library.List.allocCons_rep binderNodeListEnum repBinderNode_heapMono₂
          (nodeRep.mono ext2) tailListRep
        simp only [Aiur.Library.List.allocCons] at consRep
        refine ⟨hext, #[node] ++ tailNodes, n1 + n2, _, restPtr2, ?_, rfl, ?_, ?_⟩
        · rw [Ixon.Verify.BoundedConstant.getArray_succ]
          simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
        · simpa using consRep
        · rw [← Nat.add_assoc]
          exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (Heap.Extends.snoc _ _) hrep2
      · exact (hc28 rfl).elim

/-! ## Blocks -/

/-- **Every terminating derivation of `IxonDeserialize::get_binder_block` at
reader offset `i`** refines `Ixon.getBinderBlock` at `i`, returning a
`RepBinderBlock` value and the advanced stream pointer. -/
theorem getBinderBlock_refines_at {bytes : List UInt8} {i : Nat}
    {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_binder_block" [stream, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (block : Ixon.BinderBlock) (n : Nat) (blockVal restPtr : SourceValue F),
      Ixon.getBinderBlock { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok block { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [blockVal, restPtr] ∧
      RepBinderBlock h' block blockVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  have hext := ev.heap_extends
  have body := ev.function_inv IxVM.IxonDeserialize.get_binder_block.lookup
    (by simp [IxVM.IxonDeserialize.get_binder_block, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_binder_block] at body
  -- let (ekind, s) = read_byte(stream)
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, b, rest, restPtr1, hcons, hrep1, rfl⟩ := readByte_refines rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨-, hdrop, -⟩ := getU8_of_drop_cons hcons
  rw [← hdrop] at hrep1
  have hb : b.toNat < 256 := b.toNat_lt
  -- assert_wire_bool(ekind)
  obtain ⟨v16, m17, bs18, d19, mt20, d21⟩ := d5.letValue_inv
  rw [matchPattern_wildcard] at mt20
  simp only [Except.ok.injEq, Option.some.injEq] at mt20; subst mt20
  obtain ⟨vs22, m23, args24, callee25⟩ := d19.call_inv
  obtain ⟨v26, vs27, m28, rfl, d29, args30⟩ := args24.cons_inv
  obtain ⟨l31, rfl⟩ := d29.var_inv; simp at l31; subst l31
  obtain ⟨rfl, rfl⟩ := args30.nil_inv
  rw [instanceName_plain_some] at callee25
  obtain ⟨hb2, rfl, rfl⟩ := assertWireBool_refines hb callee25
  have hshared := getBool_of_drop_cons hcons hb2
  -- let shared = UInt8::to_field(ekind)
  obtain ⟨v32, m33, bs34, d35, mt36, d37⟩ := d21.letValue_inv
  obtain ⟨vs38, m39, args40, callee41⟩ := d35.call_inv
  obtain ⟨v42, vs43, m44, rfl, d45, args46⟩ := args40.cons_inv
  obtain ⟨l47, rfl⟩ := d45.var_inv; simp at l47; subst l47
  obtain ⟨rfl, rfl⟩ := args46.nil_inv
  rw [instanceName_plain_some] at callee41
  obtain ⟨rfl, rfl⟩ := u8ToField_refines callee41
  rw [matchPattern_bind] at mt36
  simp only [Except.ok.injEq, Option.some.injEq] at mt36; subst mt36
  -- let (eidx, s2) = get_tagn0(s)
  obtain ⟨v48, m49, bs50, d51, mt52, d53⟩ := d37.letValue_inv
  obtain ⟨vs54, m55, args56, callee57⟩ := d51.call_inv
  obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
  obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
  obtain ⟨rfl, rfl⟩ := args62.nil_inv
  rw [instanceName_plain_some] at callee57
  obtain ⟨rfl, t1, n1, restPtr2, hok1, -, hrep2, rfl⟩ := getTagN0_refines_at hrep1 callee57
  obtain rfl := matchPattern_tuple2_bind rfl mt52
  -- let (variant, s3) = get_tagn0(s2)
  obtain ⟨v64, m65, bs66, d67, mt68, d69⟩ := d53.letValue_inv
  obtain ⟨vs70, m71, args72, callee73⟩ := d67.call_inv
  obtain ⟨v74, vs75, m76, rfl, d77, args78⟩ := args72.cons_inv
  obtain ⟨l79, rfl⟩ := d77.var_inv; simp at l79; subst l79
  obtain ⟨rfl, rfl⟩ := args78.nil_inv
  rw [instanceName_plain_some] at callee73
  obtain ⟨rfl, t2, n2, restPtr3, hok2, -, hrep3, rfl⟩ := getTagN0_refines_at hrep2 callee73
  obtain rfl := matchPattern_tuple2_bind rfl mt68
  -- UInt32::less_than_fields(UInt64::to_field(eidx), UInt64::to_field(variant)): both below 2^32
  obtain ⟨v200, m201, bs202, d203, mt204, d205⟩ := d69.letValue_inv
  rw [matchPattern_wildcard] at mt204
  simp only [Except.ok.injEq, Option.some.injEq] at mt204; subst mt204
  have ext203 := d203.heap_extends
  -- assert_eq!((1 - shared) * (1 - UInt64::is_zero(variant)), 0, ...)
  obtain ⟨v80, m81, bs82, d83, mt84, d85⟩ := d205.letValue_inv
  rw [matchPattern_wildcard] at mt84
  simp only [Except.ok.injEq, Option.some.injEq] at mt84; subst mt84
  have ext83 := d83.heap_extends
  -- let (count, s4) = get_tagn0(s3)
  obtain ⟨v86, m87, bs88, d89, mt90, d91⟩ := d85.letValue_inv
  obtain ⟨vs92, m93, args94, callee95⟩ := d89.call_inv
  obtain ⟨v96, vs97, m98, rfl, d99, args100⟩ := args94.cons_inv
  obtain ⟨l101, rfl⟩ := d99.var_inv; simp at l101; subst l101
  obtain ⟨rfl, rfl⟩ := args100.nil_inv
  rw [instanceName_plain_some] at callee95
  obtain ⟨rfl, t3, n3, restPtr4, hok3, -, hrep4, rfl⟩ :=
    getTagN0_refines_at (Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (ext203.trans ext83) hrep3)
      callee95
  obtain rfl := matchPattern_tuple2_bind rfl mt90
  -- assert_eq!(UInt64::is_zero(count), 0, ...)
  obtain ⟨v102, m103, bs104, d105, mt106, d107⟩ := d91.letValue_inv
  rw [matchPattern_wildcard] at mt106
  simp only [Except.ok.injEq, Option.some.injEq] at mt106; subst mt106
  have ext105 := d105.heap_extends
  -- let (nodes, s5) = get_binder_node_list(s4, count, lvls)
  obtain ⟨v108, m109, bs110, d111, mt112, d113⟩ := d107.letValue_inv
  obtain ⟨vs114, m115, args116, callee117⟩ := d111.call_inv
  obtain ⟨v118, vs119, m120, rfl, d121, args122⟩ := args116.cons_inv
  obtain ⟨l123, rfl⟩ := d121.var_inv; simp at l123; subst l123
  obtain ⟨v124, vs125, m126, rfl, d127, args128⟩ := args122.cons_inv
  obtain ⟨l129, rfl⟩ := d127.var_inv; simp at l129; subst l129
  obtain ⟨v130, vs131, m132, rfl, d133, args134⟩ := args128.cons_inv
  obtain ⟨l135, rfl⟩ := d133.var_inv; simp at l135; subst l135
  obtain ⟨rfl, rfl⟩ := args134.nil_inv
  rw [instanceName_plain_some] at callee117
  obtain ⟨-, nodes, n4, nodesPtr, restPtr5, hok4, rfl, nodesRep, hrep5⟩ :=
    getBinderNodeList_refines_at t3.value.toNat t3.value.toNat_lt
      (Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext105 hrep4) callee117
  obtain rfl := matchPattern_tuple2_bind rfl mt112
  -- (Ixon::BinderBlock::Mk(shared, eidx, variant, nodes), s5)
  obtain ⟨vs136, args137, rfl⟩ := d113.tuple_inv
  obtain ⟨v138, vs139, m140, rfl, d141, args142⟩ := args137.cons_inv
  obtain ⟨vs143, args144, rfl⟩ := d141.construct_inv
  obtain ⟨v145, vs146, m147, rfl, d148, args149⟩ := args144.cons_inv
  obtain ⟨l150, rfl⟩ := d148.var_inv; simp at l150; subst l150
  obtain ⟨v151, vs152, m153, rfl, d154, args155⟩ := args149.cons_inv
  obtain ⟨l156, rfl⟩ := d154.var_inv; simp at l156; subst l156
  obtain ⟨v157, vs158, m159, rfl, d160, args161⟩ := args155.cons_inv
  obtain ⟨l162, rfl⟩ := d160.var_inv; simp at l162; subst l162
  obtain ⟨v163, vs164, m165, rfl, d166, args167⟩ := args161.cons_inv
  obtain ⟨l168, rfl⟩ := d166.var_inv; simp at l168; subst l168
  obtain ⟨rfl, rfl⟩ := args167.nil_inv
  obtain ⟨v169, vs170, m171, rfl, d172, args173⟩ := args142.cons_inv
  obtain ⟨l174, rfl⟩ := d172.var_inv; simp at l174; subst l174
  obtain ⟨rfl, rfl⟩ := args173.nil_inv
  have hsharedVal : ((if decide (b.toNat = 1) then 1 else 0 : Nat) : F) = (b.toNat : F) := by
    obtain hb0 | hb1 : b.toNat = 0 ∨ b.toNat = 1 := by omega
    · rw [hb0]; rfl
    · rw [hb1]; rfl
  refine ⟨hext, ⟨decide (b.toNat = 1), t1.value, t2.value, nodes⟩, 1 + n1 + n2 + n3 + n4, _,
    restPtr5, ?_, rfl, ⟨nodesPtr, ?_, nodesRep⟩, ?_⟩
  · rw [show i + (1 + n1 + n2 + n3 + n4) = i + 1 + n1 + n2 + n3 + n4 by omega]
    simp [Ixon.getBinderBlock, bind, EStateM.bind, hshared, hok1, hok2, hok3, hok4, pure,
      EStateM.pure]
  · simp only [instanceName_plain_some, hsharedVal]
  · rw [show i + (1 + n1 + n2 + n3 + n4) = i + 1 + n1 + n2 + n3 + n4 by omega]
    exact hrep5

/-- **Every terminating derivation of `IxonDeserialize::get_binder_block_list`
at reader offset `i`** refines `Ixon.getArray Ixon.getBinderBlock count` at
`i`, allocating a `RepList binderBlockListEnum RepBinderBlock` of the blocks
and advancing the stream pointer by the consumed bytes. -/
theorem getBinderBlockList_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_binder_block_list" [stream, u64Value count, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (blocks : Array Ixon.BinderBlock) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getArray Ixon.getBinderBlock count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok blocks { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList binderBlockListEnum RepBinderBlock h' blocks.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    have hext := ev.heap_extends
    have body := ev.function_inv IxVM.IxonDeserialize.get_binder_block_list.lookup
      (by simp [IxVM.IxonDeserialize.get_binder_block_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_binder_block_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      refine ⟨hext, #[], 0, _, stream,
        by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep binderBlockListEnum RepBinderBlock _,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (Heap.Extends.snoc _ _) rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have hext := ev.heap_extends
    have body := ev.function_inv IxVM.IxonDeserialize.get_binder_block_list.lookup
      (by simp [IxVM.IxonDeserialize.get_binder_block_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_binder_block_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · -- let (block, s) = get_binder_block(stream, lvls)
        obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨v46, vs47, m48, rfl, d49, args50⟩ := args44.cons_inv
        obtain ⟨l51, rfl⟩ := d49.var_inv; simp at l51; subst l51
        obtain ⟨rfl, rfl⟩ := args50.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨-, block, n1, blockVal, restPtr1, hok1, rfl, blockRep, hrep1⟩ :=
          getBinderBlock_refines_at rep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        -- let (rest, s2) = get_binder_block_list(s, UInt64::saturating_pred(count), lvls)
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨v85, vs86, m87, rfl, d88, args89⟩ := args74.cons_inv
        obtain ⟨l90, rfl⟩ := d88.var_inv; simp at l90; subst l90
        obtain ⟨rfl, rfl⟩ := args89.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext2, tailBlocks, n2, tailListPtr, restPtr2, hok2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain rfl := matchPattern_tuple2_bind rfl mt58
        -- ((&(Lists::Node::Cons(block, rest))), s2)
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
        obtain ⟨l124, rfl⟩ := d122.var_inv; simp at l124; subst l124
        obtain ⟨rfl, rfl⟩ := args123.nil_inv
        rw [value_type_construct]
        have consRep := Aiur.Library.List.allocCons_rep binderBlockListEnum repBinderBlock_heapMono₂
          (blockRep.mono ext2) tailListRep
        simp only [Aiur.Library.List.allocCons] at consRep
        refine ⟨hext, #[block] ++ tailBlocks, n1 + n2, _, restPtr2, ?_, rfl, ?_, ?_⟩
        · rw [Ixon.Verify.BoundedConstant.getArray_succ]
          simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
        · simpa using consRep
        · rw [← Nat.add_assoc]
          exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (Heap.Extends.snoc _ _) hrep2
      · exact (hc28 rfl).elim

/-! ## The section -/

/-- **Every terminating derivation of `IxonDeserialize::get_binders` at reader
offset `i`** refines `Ixon.getBinders` at `i`: IxC reads the same section from
the same bytes, and the blocks IxVM returns represent it
(`RepList binderBlockListEnum RepBinderBlock`). -/
theorem getBinders_refines_at {bytes : List UInt8} {i : Nat}
    {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_binders" [stream, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (blocks : Array Ixon.BinderBlock) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getBinders { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok blocks { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList binderBlockListEnum RepBinderBlock h' blocks.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  have hext := ev.heap_extends
  have body := ev.function_inv IxVM.IxonDeserialize.get_binders.lookup
    (by simp [IxVM.IxonDeserialize.get_binders, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_binders] at body
  -- let (len, s) = get_tagn0(stream)
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok1, -, hrep1, rfl⟩ := getTagN0_refines_at rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  -- let (blocks, s2) = get_binder_block_list(s, len, lvls)
  obtain ⟨v16, m17, bs18, d19, mt20, d21⟩ := d5.letValue_inv
  obtain ⟨vs22, m23, args24, callee25⟩ := d19.call_inv
  obtain ⟨v26, vs27, m28, rfl, d29, args30⟩ := args24.cons_inv
  obtain ⟨l31, rfl⟩ := d29.var_inv; simp at l31; subst l31
  obtain ⟨v32, vs33, m34, rfl, d35, args36⟩ := args30.cons_inv
  obtain ⟨l37, rfl⟩ := d35.var_inv; simp at l37; subst l37
  obtain ⟨v38, vs39, m40, rfl, d41, args42⟩ := args36.cons_inv
  obtain ⟨l43, rfl⟩ := d41.var_inv; simp at l43; subst l43
  obtain ⟨rfl, rfl⟩ := args42.nil_inv
  rw [instanceName_plain_some] at callee25
  obtain ⟨-, blocks, n2, listPtr, restPtr2, hok2, rfl, listRep, hrep2⟩ :=
    getBinderBlockList_refines_at t.value.toNat t.value.toNat_lt hrep1 callee25
  obtain rfl := matchPattern_tuple2_bind rfl mt20
  -- assert_blocks_ascending(blocks)
  obtain ⟨v44, m45, bs46, d47, mt48, d49⟩ := d21.letValue_inv
  rw [matchPattern_wildcard] at mt48
  simp only [Except.ok.injEq, Option.some.injEq] at mt48; subst mt48
  have ext47 := d47.heap_extends
  -- (blocks, s2)
  obtain ⟨vs50, args51, rfl⟩ := d49.tuple_inv
  obtain ⟨v52, vs53, m54, rfl, d55, args56⟩ := args51.cons_inv
  obtain ⟨l57, rfl⟩ := d55.var_inv; simp at l57; subst l57
  obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
  obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
  obtain ⟨rfl, rfl⟩ := args62.nil_inv
  refine ⟨hext, blocks, n1 + n2, listPtr, restPtr2, ?_, rfl,
    listRep.mono repBinderBlock_heapMono₂ ext47, ?_⟩
  · simp [Ixon.getBinders, bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
  · rw [← Nat.add_assoc]
    exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext47 hrep2

/-- **Every terminating derivation of `IxonDeserialize::get_binders` from the
start of `bytes`** refines `Ixon.getBinders (start bytes)`. -/
theorem getBinders_refines {bytes : List UInt8} {stream lvls r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_binders" [stream, lvls] h r h') :
    Heap.Extends h h' ∧
    ∃ (blocks : Array Ixon.BinderBlock) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getBinders (start bytes) = .ok blocks { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList binderBlockListEnum RepBinderBlock h' blocks.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  simpa [start] using getBinders_refines_at (i := 0) (by simpa using rep) ev

end IxVM.Refinement.Deserialize
