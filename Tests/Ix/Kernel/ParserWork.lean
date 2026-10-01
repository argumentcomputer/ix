/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.WorkAdmission
import Tests.Ix.Kernel.ByteAdmission

/-! The parser's work accounting (`Ix.Ixon.Verify.Work`): the metered parser
agrees with production on outcome and cursor, and the exact work of
malformed and well-formed inputs is pinned, at elaboration. -/

open Ix.Ixon.Verify Tests.Ix.Kernel.IxonFixtures

namespace Tests.Ix.Kernel.ParserWork

def sameOutcome [BEq α] : Work.Outcome α → Work.Outcome α → Bool
  | .ok left ls, .ok right rs => left == right && ls.idx == rs.idx && ls.bytes == rs.bytes
  | .error left ls, .error right rs => left == right && ls.idx == rs.idx && ls.bytes == rs.bytes
  | _, _ => false

def sameExcept [BEq α] : Except String α → Except String α → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

def checked [BEq α] (metered : Work.M α) (production : Ixon.GetM α)
    (credit : Nat) (input : ByteArray) (offset : Nat := 0) : Bool :=
  let state : Ixon.GetState := { bytes := input, idx := offset }
  let parsed := metered state
  let stop := Work.finish parsed.1
  sameOutcome parsed.1 (production state) && stop.bytes == input &&
    offset ≤ stop.idx && stop.idx ≤ input.size &&
    parsed.2 ≤ 16 * (stop.idx - offset) + credit + 1

def exactExprCost (value : Ixon.Expr) (expected : Nat) : Bool :=
  let input := Ixon.serExpr value
  match Work.expr { bytes := input } with
  | (.ok result stop, work) => result == value && stop.idx == input.size && work == expected
  | _ => false

-- Exact accounting controls pin the metric itself, beyond agreement with
-- production values. Zero-cost or omitted constructor/collection charges
-- cannot satisfy these expectations.
#guard [Ixon.Expr.sort 0, .var 0, .str 0, .nat 0, .share 0].all fun e => exactExprCost e 3
#guard [0, 1, 2, 7].all fun n => exactExprCost (.ref 0 (Array.replicate n 0)) (5 + 5 * n)
#guard [0, 1, 2, 7].all fun n => exactExprCost (.recur 0 (Array.replicate n 0)) (5 + 5 * n)
#guard [1, 2, 7].all fun n =>
  exactExprCost ((List.range n).foldl (fun e _ => .app e (.var 0)) (.var 0)) (5 + 5 * n)
#guard [1, 2, 7].all fun n =>
  exactExprCost ((List.range n).foldl (fun e _ => .lam .many (.sort 0) e) (.var 0)) (5 + 8 * n)
#guard [1, 2, 7].all fun n =>
  exactExprCost ((List.range n).foldl (fun e _ => .all .many .shared (.sort 0) e) (.var 0)) (5 + 9 * n)
-- A v3 let reads one binder-contract byte after its flags.
#guard exactExprCost (.letE (.lean false) (.sort 0) (.var 0) (.var 0)) 13

#guard match Work.tag0 { bytes := ⟨#[0x88]⟩ } with
  | (.error reason stop, work) => reason == "getU64TrimmedLE: len > 8" && stop.idx == 1 && work == 1
  | _ => false
#guard match Work.tag0 { bytes := ⟨#[0x87, 255, 255, 255, 255, 255, 255, 255, 255]⟩ } with
  | (.ok value stop, work) => value.size == 18446744073709551615 && stop.idx == 9 && work == 18
  | _ => false
#guard (List.range 8).all fun n =>
  match Work.tag0 { bytes := (⟨#[0x87]⟩ : ByteArray) ++ ⟨Array.replicate n 255⟩ } with
  | (.error reason stop, work) => reason == "EOF" && stop.idx == n + 1 && work == n + 2
  | _ => false

-- The first array element is complete. The second fails inside a let after
-- parsing its binder contract and type. Its work must be retained, and the
-- claimed array count must not cause extra iterations or allocation.
#guard [2, 64, 18446744073709551615].all fun count =>
  match Work.array Work.expr count { bytes := ⟨#[0x10, 0xA0, 0x03, 0x10]⟩ } with
  | (.error reason stop, work) => reason == "EOF" && stop.idx == 4 && work == 12
  | _ => false
-- A let binder byte outside the sixteen v3 contracts fails before its type.
#guard match Work.array Work.expr 2 { bytes := ⟨#[0x10, 0xA0, 0x10]⟩ } with
  | (.error reason stop, work) => reason == "invalid binder contract 16" && stop.idx == 3 && work == 8
  | _ => false
-- Ixon v3 checks a claimed spine length against the remaining bytes first.
#guard match Work.expr { bytes := ⟨#[0x72, 0x10]⟩ } with
  | (.error reason stop, work) =>
    reason == "count exceeds remaining bytes" && stop.idx == 1 && work == 2
  | _ => false

-- Ixon v3 rejects a claimed count larger than the remaining bytes before
-- reading any element: the stop index is right after the count's tag (and the
-- reference index for `ref`/`recur`).
def expressionCountBombs : List (ByteArray × Nat × Nat) :=
  [((Ixon.runPut do
      Ixon.putTag4 ⟨7, 18446744073709551615⟩
      Ixon.putExpr (.var 0)), 9, 18)] ++
    [8, 9].map (fun flag => ((Ixon.runPut do
      Ixon.putTag4 ⟨flag, 18446744073709551615⟩
      Ixon.putU8 3
      Ixon.putExpr (.var 0)), 9, 18)) ++
    [2, 3].map (fun flag => ((Ixon.runPut do
      Ixon.putTag4 ⟨flag, 18446744073709551615⟩
      Ixon.putTag0 ⟨0⟩
      Ixon.putTag0 ⟨0⟩), 10, 20))

#guard expressionCountBombs.all fun (input, stopIdx, expected) =>
  checked Work.expr Ixon.getExpr 0 input &&
    match Work.expr { bytes := input } with
    | (.error reason stop, work) =>
      reason == "count exceeds remaining bytes" && stop.idx == stopIdx && work == expected
    | _ => false

def expressionCases : List Ixon.Expr := [
  .var 18446744073709551615, .ref 2 #[0, 1, 127, 128], .recur 3 #[7, 8],
  .prj 2 1 (.var 0), .app (.app (.var 0) (.var 1)) (.var 2),
  .lam .linear (.sort 0) (.lam .affine (.var 0) (.var 1)),
  .all .many .unique (.sort 0) (.all .erased .shared (.var 0) (.var 1)),
  .letE (.lean true) (.sort 0) (.var 0) (.letE (.borrow false .linear) (.var 0) (.var 0) (.var 0))]

-- Check every truncation from a nonzero cursor, including complete reads
-- with an untouched suffix, and all single-byte tags/malformed branches.
#guard expressionCases.all fun value =>
  let input := Ixon.serExpr value
  (List.range (input.size + 1)).all fun size =>
    checked Work.expr Ixon.getExpr 0 ((⟨#[0xff, 0xee]⟩ : ByteArray) ++ input.extract 0 size) 2
#guard expressionCases.all fun value =>
  checked Work.expr Ixon.getExpr 0 ((⟨#[0xff, 0xee]⟩ : ByteArray) ++ Ixon.serExpr value ++ ⟨#[0xdd]⟩) 2
#guard (List.range 256).all fun byte =>
  let input : ByteArray := ⟨#[byte.toUInt8]⟩
  checked Work.tag0 Ixon.getTag0 0 input && checked Work.tag2 Ixon.getTag2 0 input &&
    checked Work.tag4 Ixon.getTag4 0 input && checked Work.expr Ixon.getExpr 0 input

#guard match Work.univ 64 { bytes := Codec.successorBomb } with
  | (.error reason stop, work) =>
    reason == "getUnivBounded: expanded-node budget exhausted" && stop.idx == 9 && work == 18
  | _ => false
#guard match Work.univ 3 { bytes := ⟨#[0x40, 0]⟩ } with
  | (.error reason stop, work) => reason == "EOF" && stop.idx == 2 && work == 10
  | _ => false
#guard match Work.univArray 2 4 { bytes := ⟨#[0, 0x40, 0]⟩ } with
  | (.error reason stop, work) => reason == "EOF" && stop.idx == 3 && work == 17
  | _ => false
#guard [(1, 10), (31, 70), (32, 74), (256, 524)].all fun (count, cost) =>
  match Work.univ (count + 1) { bytes := Ixon.serUniv (.addSucc count .zero) } with
  | (.ok (value, remaining) _, work) => value == .addSucc count .zero && remaining == 0 && work == cost
  | _ => false

#guard Codec.boundedUniverses.all fun value =>
  let input := Ixon.serUniv value
  [0, value.nodeCount - 1, value.nodeCount, value.nodeCount + 1].all fun budget =>
    (List.range (input.size + 1)).all fun size =>
      checked (Work.univ budget) (Ixon.Bounded.getUniv budget) (2 * budget)
        ((⟨#[0xff, 0xee]⟩ : ByteArray) ++ input.extract 0 size) 2

def recordChecked (maxBytes budget : Nat) (input : ByteArray) : Bool :=
  let parsed := Work.record maxBytes budget input
  sameExcept parsed.1 (Ixon.Bounded.deConstant maxBytes budget input) &&
    parsed.2 ≤ 16 * input.size + 2 * budget + 3

def recordCases : List Ixon.Constant := variants.map Prod.snd ++
  [sharedIdentity, Codec.sharedUniverseBudget, ⟨.muts #[], #[], #[], #[]⟩]

#guard (Work.record 0 0 ⟨#[]⟩).2 == 3
#guard (Work.record 0 0 ⟨#[0]⟩).2 == 1
#guard (Work.record 256 0 (Ixon.serConstant ⟨.muts #[], #[], #[], #[]⟩)).2 == 13
#guard [(0, 14), (16, 54), (31, 86), (32, 93)].all fun (budget, work) =>
  (Work.record 256 budget (Ixon.serConstant Codec.sharedUniverseBudget)).2 == work
#guard recordCases.all fun value =>
  let input := Ixon.serConstant value
  let budget := Ixon.Bounded.univNodes value.univs
  sameExcept (Work.record input.size budget input).1 (.ok value)
#guard recordCases.all fun value =>
  let input := Ixon.serConstant value
  let budget := Ixon.Bounded.univNodes value.univs
  (List.range (input.size + 1)).all fun size =>
    let part := input.extract 0 size
    recordChecked input.size budget part &&
      checked (Work.constant budget) (Ixon.Bounded.getConstant budget) (2 * budget)
        ((⟨#[0xff, 0xee]⟩ : ByteArray) ++ part) 2
#guard recordCases.all fun value =>
  let input := Ixon.serConstant value
  [0, input.size - 1, input.size].all fun maxBytes =>
    [0, Ixon.Bounded.univNodes value.univs].all fun budget =>
      recordChecked maxBytes budget input && recordChecked (maxBytes + 1) budget (input.push 0xff)
#guard Codec.alternateSpellings.all (recordChecked 256 64)
#guard recordChecked 256 64 (Codec.recordUnivsPayload 18446744073709551615 ⟨#[]⟩)
#guard recordChecked 256 64 (Codec.recordUnivsPayload 2 (Ixon.serUniv .zero ++ Codec.successorBomb))

def sameStage : Except _root_.Ix.Ixon.Admission.Error _root_.Ix.Kernel.Ingress.Constants →
    Except _root_.Ix.Ixon.Admission.Error _root_.Ix.Kernel.Ingress.Constants → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => decide (left = right)
  | _, _ => false

def stageChecked (limits : _root_.Ix.Ixon.Admission.Limits) (records : _root_.Ix.Ixon.Admission.Records) : Bool :=
  let parsed := Work.Admission.parserStage limits records []
  sameStage parsed.1 (do _root_.Ix.Ixon.Admission.preflight limits records []; _root_.Ix.Ixon.Admission.decodeRecords limits records) &&
    parsed.2 ≤ 16 * limits.maxTotalBytes + limits.maxRecords * (2 * limits.maxRecordUnivNodes + 3)

#guard stageChecked ByteAdmission.limits (ByteAdmission.encode variants)
#guard stageChecked ByteAdmission.limits (ByteAdmission.one ++ [(address 2, ⟨#[]⟩)])
#guard stageChecked ByteAdmission.limits (ByteAdmission.one ++ [(address 2, Codec.nonminimalSharingCount)])
#guard (Work.Admission.parserStage { ByteAdmission.limits with maxRecords := 0 }
  [(address 1, ⟨#[]⟩)] []).2 == 0
#guard (Work.Admission.parserStage { ByteAdmission.limits with maxTotalBytes := 0 }
  [(address 1, ⟨#[0xff]⟩)] []).2 == 0

-- A failed canonical record terminates the batch. Trailing records contribute
-- no parser work; the work of earlier records and the failed record remains.
#guard
  let initial := ByteAdmission.one ++ [(address 2, Codec.nonminimalSharingCount)]
  let first := Work.Admission.parserStage ByteAdmission.limits initial []
  let more := Work.Admission.parserStage ByteAdmission.limits
    (initial ++ ByteAdmission.encode variants) []
  first.2 > 3 && first.2 == more.2 && sameStage first.1 more.1

end Tests.Ix.Kernel.ParserWork
