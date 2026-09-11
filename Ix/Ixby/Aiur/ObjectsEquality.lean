module
public import Ix.Ixby.Aiur.ObjectsIdentity
import all Ix.Aiur.Goldilocks

/-! Compiled constructor-ID equality, including full-width semantic decoding.

The structural certificate checks the emitted comparator. Raw comparison is
exact for all Goldilocks limbs; agreement with semantic constructor identities
requires successful range-checked decoding. This is a bytecode component proof,
not a general compiler, admission, or AIR correctness theorem.
-/

namespace Ix.Ixby.AiurBackend.ObjectsEquality

-- Structural equality is private to this diagnostic certificate.
deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval
open Ix.Ixby
open Ix.Ixby.AiurBackend.ObjectsMemory Ix.Ixby.AiurBackend.ObjectsRefinement
open Ix.Ixby.AiurBackend.ObjectsTable Ix.Ixby.AiurBackend.ObjectsParser
open Ix.Ixby.AiurBackend.ObjectsIdentity

theorem field_n_injective {a b : G} (equal : a.n = b.n) : a = b := by
  apply Subtype.ext
  exact UInt64.toNat_inj.mp equal

theorem field_bound (a : G) : a.n < goldilocksModulus := by
  have modulus : gSize.toNat = goldilocksModulus := by decide
  simpa only [UInt64.lt_iff_toNat_lt, modulus] using a.property

theorem field_of_nat_mod (n : Nat) : (G.ofNat n).n = n % goldilocksModulus := by
  have same : G.ofNat (n % goldilocksModulus) = G.ofNat n := by
    change G.ofNat (n % gSize.toNat) = G.ofNat n
    simp [G.ofNat]
  rw [← same]
  exact field_of_nat_exact _ (Nat.mod_lt _ (by decide))

/-- Subtraction followed by the emitted zero test is exact over the whole
canonical field, not merely over u32 limbs. -/
theorem field_sub_zero (a b : G) : (a - b).n = 0 ↔ a = b := by
  have ha := field_bound a
  have hb := field_bound b
  have sub : (a - b).n = (a.n + goldilocksModulus - b.n) % goldilocksModulus :=
    field_of_nat_mod _
  rw [sub]
  constructor
  · intro zero
    apply field_n_injective
    by_cases order : a.n < b.n
    · rw [Nat.mod_eq_of_lt (by omega)] at zero
      omega
    · have difference : a.n + goldilocksModulus - b.n = (a.n - b.n) + goldilocksModulus := by omega
      rw [difference, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at zero
      omega
  · rintro rfl
    simp

def fieldEq (a b : G) : G := if (a - b).val == 0 then 1 else 0

theorem field_eq_exact (a b : G) : fieldEq a b = if a = b then 1 else 0 := by
  have zero : ((a - b).val == 0) = true ↔ a = b := by
    simpa [G.n, ← UInt64.toNat_inj] using field_sub_zero a b
  simp only [fieldEq, zero]

theorem bit_product (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : G) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

/-- Ten actual field registers: eight digest limbs followed by member/tag.
This representation imposes no byte/u32 invariant by itself. -/
structure RawId where
  a : G
  b : G
  c : G
  d : G
  e : G
  f : G
  g : G
  h : G
  member : G
  tag : G
  deriving DecidableEq

def RawId.flat (id : RawId) : Array G :=
  #[id.a, id.b, id.c, id.d, id.e, id.f, id.g, id.h, id.member, id.tag]
def RawId.digest (id : RawId) : List G := [id.a, id.b, id.c, id.d, id.e, id.f, id.g, id.h]
def RawId.decode (id : RawId) : Option CtorId := decodeId id.flat.toList

/-- Right-associated product in the compiler's actual operation order. -/
def rawEq (a b : RawId) : G :=
  fieldEq a.a b.a * (fieldEq a.b b.b * (fieldEq a.c b.c * (fieldEq a.d b.d *
    (fieldEq a.e b.e * (fieldEq a.f b.f * (fieldEq a.g b.g * (fieldEq a.h b.h *
      (fieldEq a.member b.member * fieldEq a.tag b.tag))))))))

theorem raw_eq_exact (a b : RawId) : rawEq a b = if a = b then 1 else 0 := by
  cases a; cases b
  simp only [rawEq, field_eq_exact, bit_product, RawId.mk.injEq]

def idEqPairOps : Array Aiur.Bytecode.Op :=
  #[.sub 0 10, .eqZero 20, .sub 1 11, .eqZero 22, .sub 2 12, .eqZero 24,
    .sub 3 13, .eqZero 26, .sub 4 14, .eqZero 28, .sub 5 15, .eqZero 30,
    .sub 6 16, .eqZero 32, .sub 7 17, .eqZero 34, .sub 8 18, .eqZero 36,
    .sub 9 19, .eqZero 38]

def idEqProductOps : Array Aiur.Bytecode.Op :=
  #[.mul 37 39, .mul 35 40, .mul 33 41, .mul 31 42,
    .mul 29 43, .mul 27 44, .mul 25 45, .mul 23 46, .mul 21 47]

def idEqBody (selector : Nat) : Aiur.Bytecode.Block := {
  ops := idEqPairOps ++ idEqProductOps,
  ctrl := .return selector #[48] }

def diffRegisters (a b : RawId) : Array G :=
  #[a.a - b.a, fieldEq a.a b.a, a.b - b.b, fieldEq a.b b.b,
    a.c - b.c, fieldEq a.c b.c, a.d - b.d, fieldEq a.d b.d,
    a.e - b.e, fieldEq a.e b.e, a.f - b.f, fieldEq a.f b.f,
    a.g - b.g, fieldEq a.g b.g, a.h - b.h, fieldEq a.h b.h,
    a.member - b.member, fieldEq a.member b.member, a.tag - b.tag, fieldEq a.tag b.tag]

private theorem eval_sub (t : Bytecode.Toplevel) (fuel left right : Nat) (st : EvalState)
    (a b : G) (ha : st.map[left]? = some a) (hb : st.map[right]? = some b) :
    Aiur.Bytecode.Eval.evalOp t fuel (.sub left right) st =
      .ok { st with map := st.map.push (a - b) } := by
  simp [Aiur.Bytecode.Eval.evalOp, readIdx, ha, hb, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem eval_zero (t : Bytecode.Toplevel) (fuel idx : Nat) (st : EvalState)
    (a : G) (ha : st.map[idx]? = some a) :
    Aiur.Bytecode.Eval.evalOp t fuel (.eqZero idx) st =
      .ok { st with map := st.map.push (if a.val == 0 then 1 else 0) } := by
  simp [Aiur.Bytecode.Eval.evalOp, readIdx, ha, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem eval_mul (t : Bytecode.Toplevel) (fuel left right : Nat) (st : EvalState)
    (a b : G) (ha : st.map[left]? = some a) (hb : st.map[right]? = some b) :
    Aiur.Bytecode.Eval.evalOp t fuel (.mul left right) st =
      .ok { st with map := st.map.push (a * b) } := by
  simp [Aiur.Bytecode.Eval.evalOp, readIdx, ha, hb, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option maxRecDepth 4096 in
private theorem id_eq_pairs_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState) (a b : RawId) :
    runOps t fuel idEqPairOps { st with map := a.flat ++ b.flat } 0 =
      .ok { st with map := (a.flat ++ b.flat) ++ diffRegisters a b } := by
  simp [idEqPairOps, RawId.flat, diffRegisters, fieldEq, run_ops_list, eval_sub, eval_zero,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option maxRecDepth 4096 in
private theorem id_eq_products_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (st : EvalState) (a b : RawId) :
    ∃ after, evalBlock t fuel ⟨idEqProductOps, .return selector #[48]⟩
        { st with map := (a.flat ++ b.flat) ++ diffRegisters a b } =
      .error (.earlyReturn #[rawEq a b] after) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  simp [idEqProductOps, RawId.flat, diffRegisters, rawEq, evalBlock, run_ops_list, eval_mul,
    readIdx, readIdxs, evalCtrl, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- All twenty sub/zero operations and nine products, with the exact return
register and unchanged memory/I/O. The body itself makes no calls. -/
theorem id_eq_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (st : EvalState) (a b : RawId) :
    ∃ after, evalBlock t fuel (idEqBody selector) { st with map := a.flat ++ b.flat } =
      .error (.earlyReturn #[if a = b then 1 else 0] after) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨after, executed, memory, io⟩ := id_eq_products_eval t fuel selector st a b
  refine ⟨after, ?_, memory, io⟩
  simpa only [idEqBody, evalBlock, run_ops_append, id_eq_pairs_eval t fuel st a b, Except.bind,
    raw_eq_exact] using executed

/-- Decidable structural equality binds every operation and output. Layout
metadata unused by the evaluator is intentionally not certified. -/
def checkIdEq (f : Aiur.Bytecode.Function) (selector : Nat) : Bool :=
  match f.body.ctrl with
  | .return found outs => decide (f.layout.inputSize = 20 ∧
      f.body.ops = (idEqBody selector).ops ∧ found = selector ∧ outs = #[48])
  | _ => false

theorem id_eq_checked (f : Aiur.Bytecode.Function) (selector : Nat)
    (checked : checkIdEq f selector = true) :
    f.layout.inputSize = 20 ∧ f.body = idEqBody selector := by
  unfold checkIdEq at checked
  split at checked
  · rename_i found outs ctrl
    obtain ⟨input, ops, selectorEq, outsEq⟩ := of_decide_eq_true checked
    refine ⟨input, ?_⟩
    cases f with
    | mk b layout entry constrained => cases b; simp_all [idEqBody]
  · simp at checked

theorem id_eq_call (t : Bytecode.Toplevel) (fuel selector comparer : Nat)
    (st : EvalState) (f : Aiur.Bytecode.Function) (function : t.functions[comparer]? = some f)
    (checked : checkIdEq f selector = true) (a b : RawId) (args : Array Nat)
    (arguments : readIdxs st args = .ok (a.flat ++ b.flat)) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call comparer args 1 unconstrained) st =
      .ok { st with map := st.map.push (if a = b then 1 else 0) } := by
  obtain ⟨after, executed, memory, io⟩ := id_eq_eval t fuel selector st a b
  obtain ⟨input, body⟩ := id_eq_checked f selector checked
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  have arity : (a.flat ++ b.flat).size = 20 := rfl
  simp [Aiur.Bytecode.Eval.evalOp, arguments, Bind.bind, Except.bind,
    Pure.pure, Except.pure, bound, found, input, body, executed, memory, io,
    arity, appendMap, setIoBuffer]

theorem raw_decode_bounds (raw : RawId) (id : CtorId) (decoded : raw.decode = some id) :
    ∀ limb ∈ raw.flat.toList, limb.n < limbBase := by
  change decodeId [raw.a, raw.b, raw.c, raw.d, raw.e, raw.f, raw.g, raw.h, raw.member, raw.tag] = some id at decoded
  simp only [decodeId] at decoded
  split at decoded
  · rename_i bounded
    change ∀ limb ∈ [raw.a, raw.b, raw.c, raw.d, raw.e, raw.f, raw.g, raw.h, raw.member, raw.tag],
      limb.n < limbBase
    simpa only [List.all_eq_true, decide_eq_true_eq] using bounded
  · simp at decoded

/-- Validated u32 limb bounds make natural little-endian packing injective;
without decoding, raw fields must not be treated as semantic names. -/
theorem raw_decode_injective (a b : RawId) (id : CtorId)
    (left : a.decode = some id) (right : b.decode = some id) : a = b := by
  have leftRange := raw_decode_bounds a id left
  have rightRange := raw_decode_bounds b id right
  obtain ⟨leftBlock, leftMember, leftTag⟩ :=
    decode_id_exact a.a a.b a.c a.d a.e a.f a.g a.h a.member a.tag id left
  obtain ⟨rightBlock, rightMember, rightTag⟩ :=
    decode_id_exact b.a b.b b.c b.d b.e b.f b.g b.h b.member b.tag id right
  have bounded (raw : RawId) (ranges : ∀ limb ∈ raw.flat.toList, limb.n < limbBase) :
      ∀ limb ∈ raw.digest.map G.n, limb < limbBase := by
    intro limb member
    obtain ⟨field, mem, rfl⟩ := List.mem_map.mp member
    apply ranges field
    exact List.mem_append_left [raw.member, raw.tag] mem
  have packed : packLimbs (a.digest.map G.n) = packLimbs (b.digest.map G.n) :=
    leftBlock.symm.trans rightBlock
  have values := pack_limbs_injective (bounded a leftRange) (bounded b rightRange) rfl packed
  have digest : a.digest = b.digest := (List.map_inj_right (fun _ _ => field_n_injective)).mp values
  have member : a.member = b.member := field_n_injective (leftMember.symm.trans rightMember)
  have tag : a.tag = b.tag := field_n_injective (leftTag.symm.trans rightTag)
  have flat : a.flat = b.flat := by
    change a.digest.toArray ++ #[a.member, a.tag] = b.digest.toArray ++ #[b.member, b.tag]
    rw [digest, member, tag]
  cases a; cases b
  simpa [RawId.flat, RawId.mk.injEq] using flat

theorem raw_semantic_eq (a b : RawId) (leftId rightId : CtorId)
    (left : a.decode = some leftId) (right : b.decode = some rightId) :
    a = b ↔ leftId = rightId := by
  constructor
  · rintro rfl
    exact Option.some.inj (left.symm.trans right)
  · rintro rfl
    exact raw_decode_injective a b leftId left right

theorem id_eq_semantic (a b : RawId) (leftId rightId : CtorId)
    (left : a.decode = some leftId) (right : b.decode = some rightId) :
    rawEq a b = if leftId = rightId then 1 else 0 := by
  simp only [raw_eq_exact, raw_semantic_eq a b leftId rightId left right]

/-- Checked compiled comparison at the actual Call boundary agrees with full
semantic constructor-ID equality and preserves all preexisting caller state. -/
theorem checked_id_eq_call (t : Bytecode.Toplevel) (fuel selector comparer : Nat)
    (st : EvalState) (f : Aiur.Bytecode.Function) (function : t.functions[comparer]? = some f)
    (checked : checkIdEq f selector = true) (a b : RawId) (args : Array Nat)
    (arguments : readIdxs st args = .ok (a.flat ++ b.flat))
    (leftId rightId : CtorId) (left : a.decode = some leftId) (right : b.decode = some rightId)
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call comparer args 1 unconstrained) st =
      .ok { st with map := st.map.push (if leftId = rightId then 1 else 0) } := by
  simpa only [raw_semantic_eq a b leftId rightId left right] using
    id_eq_call t fuel selector comparer st f function checked a b args arguments unconstrained

end
end
end Ix.Ixby.AiurBackend.ObjectsEquality
