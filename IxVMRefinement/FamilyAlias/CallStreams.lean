import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.IxonDeserialize0
import IxVMRefinement.Ingress.Stream
import Ix.IxVM.Refinement.TagNWide

/-! # The payload stream `check_family` reads

`KernelModeled::check_family` reads its payload as a byte stream (`read_payload`): the family
record's address, the advice list (`get_count`, `get_addrs`), the witnesses (`get_count`,
`check_witnesses`), then the models of the types, the constructors and the recursors
(`get_addrs`, three times). `Decl.get_addrs_spec` reads an address list off a stream; this module
carries the stream through the reads before the models, one lemma per function:

* `get_count_stream`: `KernelModeled::get_count` (`IxonDeserialize::get_tagn0`, then
  `UInt64::to_field`);
* `read_byte_stream`: `IxonDeserialize::read_byte`;
* `walk_path_stream`, `walk_from_block_stream`: a dependency path's steps
  (`KernelModeled::walk_path`, `walk_from_block`);
* `check_witness_stream`: one witness, of each of its four kinds
  (`KernelModeled::check_witness`);
* `check_witnesses_stream`: the witness loop (`KernelModeled::check_witnesses`).

Each states only that what the function returns as the rest of the stream is a stream, at the
heap it returns. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false

/-- **`KernelModeled::get_count`** leaves a stream: `IxonDeserialize::get_tagn0` reads a header
off it (`TagN.getTagN0_refines`) and `UInt64::to_field` only extends the heap. -/
theorem get_count_stream {s x_n x_s2 : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::get_count" [s] h (.tuple [x_n, x_s2]) h' cs) :
    ∃ bytes' : List UInt8, Ingress.Stream h' bytes' x_s2 := by
  match Obs.«KernelModeled::get_count».obs ev with
  | .run (x_s2 := y) (ev14 := e1) (he40 := hr) (ev52 := e2) (he68 := hh) .. =>
    obtain ⟨hm, t, n, restPtr, -, -, hrest, htup⟩ := TagN.getTagN0_refines hs e1.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup hr
    obtain ⟨-, hy⟩ := htup
    obtain ⟨-, hx⟩ := hr
    subst hh hm
    rw [hx, hy]
    exact ⟨_, Ingress.Stream.mono e2.heap_extends hrest⟩

/-- **`IxonDeserialize::read_byte`** leaves a stream: the tail of the stream's first cell. -/
theorem read_byte_stream {s x_b x_s2 : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "IxonDeserialize::read_byte" [s] h (.tuple [x_b, x_s2]) h' cs) :
    ∃ bytes' : List UInt8, Ingress.Stream h' bytes' x_s2 := by
  match Obs.«IxonDeserialize::read_byte».obs ev with
  | .run (ld11 := ld) (he30 := hr) (he45 := hh) .. =>
    subst hh
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    obtain ⟨-, hx⟩ := hr
    rcases Ingress.stream_inv hs ld with ⟨-, hv⟩ | ⟨b, bs, tail, -, hv, htail⟩
    · injection hv with _ hc
      exact absurd hc (by decide)
    · injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      rw [hx, hargs.2]
      exact ⟨bs, htail⟩

/-- The heap of `KernelModeled::walk_path`'s step to the next record extends. -/
private theorem walk_path_seg1_extends {c st s2 rc cur s n passed r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (sg : Obs.«KernelModeled::walk_path».Seg1 c st s2 rc cur s n passed h r h' cs) :
    Heap.Extends h h' := by
  match sg with
  | .n0 (ev116 := ev) .. => exact ev.heap_extends
  | .other (ev213 := e1) (ev199 := e2) (ev249 := e3) .. =>
    exact e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)

/-- **`KernelModeled::walk_path`** at a count read as a field leaves a stream (by induction on the
count). -/
theorem walk_path_stream_field :
    ∀ (k : Nat) {rc cur s passed r : SourceValue F} {n : F} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = k → Ingress.Stream h bytes s →
      ObsFn W "KernelModeled::walk_path" [rc, cur, s, .field n, passed] h r h' cs →
      ∃ (x s' p : SourceValue F) (bytes' : List UInt8), r = .tuple [x, s', p] ∧
        Ingress.Stream h' bytes' s'
  | 0, rc, cur, s, passed, r, n, bytes, h, h', cs, hk, hs, ev => by
    match Obs.«KernelModeled::walk_path».obs ev with
    | .n0 (ev_qmmrohoe := e1) (he19 := hr) (he34 := hh) .. =>
      subst hh
      exact ⟨cur, s, _, bytes, hr, hs.mono e1.heap_extends⟩
    | .other (hne36 := hne) .. =>
      exact absurd (congrArg Value.field ((ZMod.val_eq_zero n).mp hk)) hne
  | k + 1, rc, cur, s, passed, r, n, bytes, h, h', cs, hk, hs, ev => by
    match Obs.«KernelModeled::walk_path».obs ev with
    | .n0 (hv14 := hv) .. =>
      injection hv with hn
      subst hn
      simp at hk
    | .other (hne36 := hne) (ev53 := e1) (ev88 := e2) (sg284 := sg)
        (ev_kkbmepwt := e4) (op_lhbokqvf := op) (ev290 := e3) .. =>
      have hn0 : n ≠ 0 := fun e => hne (congrArg Value.field e)
      obtain rfl := Lib.sub_one_inv op
      have hpred : ZMod.val (n - 1) = k := by
        have := Lib.val_sub_one hn0
        omega
      obtain ⟨b1, hs1⟩ := get_count_stream hs e1
      exact walk_path_stream_field k hpred
        (((hs1.mono e2.heap_extends).mono (walk_path_seg1_extends sg)).mono e4.heap_extends) e3

/-- **`KernelModeled::walk_path`** leaves a stream. -/
theorem walk_path_stream {rc cur s x_n passed r : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::walk_path" [rc, cur, s, x_n, passed] h r h' cs) :
    ∃ (x s' p : SourceValue F) (bytes' : List UInt8), r = .tuple [x, s', p] ∧
      Ingress.Stream h' bytes' s' := by
  match Obs.«KernelModeled::walk_path».obs ev with
  | .n0 (hv14 := hv) .. =>
    subst hv
    exact walk_path_stream_field _ rfl hs ev
  | .other (op_lhbokqvf := op) .. =>
    obtain ⟨n, _, rfl, -⟩ := NatAux.binop_fields op
    exact walk_path_stream_field _ rfl hs ev

/-- **`KernelModeled::walk_from_block`** leaves a stream. -/
theorem walk_from_block_stream {rc blk s x_n x_stop x_s2 x_passed : SourceValue F}
    {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::walk_from_block" [rc, blk, s, x_n] h
      (.tuple [x_stop, x_s2, x_passed]) h' cs) :
    ∃ bytes' : List UInt8, Ingress.Stream h' bytes' x_s2 := by
  match Obs.«KernelModeled::walk_from_block».obs ev with
  | .run (ev25 := e1) (ev46 := e2) .. =>
    obtain ⟨x, s', p, b', hr, hs'⟩ := walk_path_stream (hs.mono e1.heap_extends) e2
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    rw [hr.2.1]
    exact ⟨b', hs'⟩

/-- The heap of `KernelModeled::check_witness`'s computed projection address extends. -/
private theorem check_witness_seg1_extends {c1 s5 idx s4 iblock s3 passed n s2 rc blk x kind s
    r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (sg : Obs.«KernelModeled::check_witness».Seg1 c1 s5 idx s4 iblock s3 passed n s2 rc blk x kind
      s h r h' cs) : Heap.Extends h h' := by
  match sg with
  | .n0 (ev623 := ev) .. => exact ev.heap_extends
  | .other (ev650 := ev) .. => exact ev.heap_extends

/-- **`KernelModeled::check_witness`** leaves a stream, at each of its four kinds: a basis
role's reference (the stream as given), a dependency path's stop, a container's recursor, and a
projection of a block a path reaches. -/
theorem check_witness_stream {rc blk x kind s r : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::check_witness" [rc, blk, x, kind, s] h r h' cs) :
    ∃ bytes' : List UInt8, Ingress.Stream h' bytes' r := by
  match Obs.«KernelModeled::check_witness».obs ev with
  | .n0 (ev28 := e1) (ev69 := e2) (ev109 := e3) (ev146 := e4) (he164 := hr) (he165 := hh) .. =>
    subst hr hh
    exact ⟨bytes, hs.mono (e1.heap_extends.trans (e2.heap_extends.trans
      (e3.heap_extends.trans e4.heap_extends)))⟩
  | .n1 (ev185 := e1) (ev_lbttumfo := e2) (ev282 := e3) (ev_kzxwtasl := e4)
      (ev_scicdnpr := e5) (ev_krpcbbcl := e6) (ev_mvspkqrl := e7) (he307 := hr)
      (he308 := hh) .. =>
    subst hr hh
    obtain ⟨b1, hs1⟩ := get_count_stream hs e1
    obtain ⟨b2, hs2⟩ := walk_from_block_stream hs1 e2
    exact ⟨b2, hs2.mono (e3.heap_extends.trans (e4.heap_extends.trans (e5.heap_extends.trans
      (e6.heap_extends.trans e7.heap_extends))))⟩
  | .n2 (ev328 := e1) (ev_dpuowbtw := e2) (ev414 := e3) (ev_yqkzbtyw := e4) (he440 := hr)
      (he441 := hh) .. =>
    subst hr hh
    obtain ⟨b1, hs1⟩ := get_count_stream hs e1
    obtain ⟨b2, hs2⟩ := walk_from_block_stream hs1 e2
    exact ⟨b2, hs2.mono (e3.heap_extends.trans e4.heap_extends)⟩
  | .n3 (ev461 := e1) (ev_ndaajwbz := e2) (ev547 := e3) (ev582 := e4) (sg692 := sg)
      (ev717 := e5) (ev_gwtfngxo := e6) (ev_xxjagmga := e7) (he742 := hr) (he743 := hh) .. =>
    subst hr hh
    obtain ⟨b1, hs1⟩ := get_count_stream hs e1
    obtain ⟨b2, hs2⟩ := walk_from_block_stream hs1 e2
    obtain ⟨b3, hs3⟩ := get_count_stream hs2 e3
    obtain ⟨b4, hs4⟩ := get_count_stream hs3 e4
    exact ⟨b4, (hs4.mono (check_witness_seg1_extends sg)).mono
      (e5.heap_extends.trans (e6.heap_extends.trans e7.heap_extends))⟩

/-- **`KernelModeled::check_witnesses`** at a count read as a field leaves a stream (by
induction on the count). -/
theorem check_witnesses_stream_field :
    ∀ (k : Nat) {rc blk s r : SourceValue F} {n : F} {bytes : List UInt8} {h h' : Heap F}
      {cs : List (Call F)},
      ZMod.val n = k → Ingress.Stream h bytes s →
      ObsFn W "KernelModeled::check_witnesses" [rc, blk, s, .field n] h r h' cs →
      ∃ (xs s' : SourceValue F) (bytes' : List UInt8), r = .tuple [xs, s'] ∧
        Ingress.Stream h' bytes' s'
  | 0, rc, blk, s, r, n, bytes, h, h', cs, hk, hs, ev => by
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (he19 := hr) (hm29 := hm) (he40 := hh) .. =>
      subst hh hm
      exact ⟨_, s, bytes, hr, hs.mono (Heap.Extends.snoc _ _)⟩
    | .other (hne42 := hne) .. =>
      exact absurd (congrArg Value.field ((ZMod.val_eq_zero n).mp hk)) hne
  | k + 1, rc, blk, s, r, n, bytes, h, h', cs, hk, hs, ev => by
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (hv14 := hv) .. =>
      injection hv with hn
      subst hn
      simp at hk
    | .other (hne42 := hne) (ev59 := e1) (ev94 := e2) (ev_updedcyj := e2') (ev167 := e3)
        (ev129 := e4) (op235 := op) (ev196 := e5) (he254 := hr) (hm264 := hm) (he291 := hh) .. =>
      have hn0 : n ≠ 0 := fun e => hne (congrArg Value.field e)
      obtain rfl := Lib.sub_one_inv op
      have hpred : ZMod.val (n - 1) = k := by
        have := Lib.val_sub_one hn0
        omega
      obtain ⟨a, rem, x_t, x_s2', -, htup, -, hs1, -, -⟩ := Decl.get_address_spec hs e1
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨-, hx2⟩ := htup
      rw [← hx2] at hs1
      obtain ⟨b2, hs2⟩ := read_byte_stream hs1 e2
      obtain ⟨b3, hs3⟩ := check_witness_stream ((hs2.mono e2'.heap_extends).mono e3.heap_extends) e4
      obtain ⟨xs, s', b4, hr', hs4⟩ := check_witnesses_stream_field k hpred hs3 e5
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr'
      obtain ⟨-, hs'⟩ := hr'
      subst hh hm
      refine ⟨_, _, b4, hr, ?_⟩
      rw [hs']
      exact hs4.mono (Heap.Extends.snoc _ _)

/-- **`KernelModeled::check_witnesses`** leaves a stream. -/
theorem check_witnesses_stream {rc blk s x_n x_out x_s5 : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)} (hs : Ingress.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::check_witnesses" [rc, blk, s, x_n] h (.tuple [x_out, x_s5]) h'
      cs) :
    ∃ bytes' : List UInt8, Ingress.Stream h' bytes' x_s5 := by
  have key : ∀ n : F, x_n = .field n → ∃ bytes' : List UInt8, Ingress.Stream h' bytes' x_s5 := by
    intro n hn
    subst hn
    obtain ⟨xs, s', b', hr, hs'⟩ := check_witnesses_stream_field _ rfl hs ev
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    rw [hr.2]
    exact ⟨b', hs'⟩
  match Obs.«KernelModeled::check_witnesses».obs ev with
  | .n0 (hv14 := hv) .. => exact key 0 hv
  | .other (op235 := op) .. =>
    obtain ⟨n, _, hn, -⟩ := NatAux.binop_fields op
    exact key n hn

end IxVM.Refinement.Typing.FamilyAlias
