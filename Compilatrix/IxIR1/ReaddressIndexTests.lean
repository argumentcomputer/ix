import Compilatrix.Coverage.Snapshot
import Compilatrix.Tools.Check

/-! Compiled comparisons against the retained list builder and certificate
predicates. Canonical bytes, complete maps, and artifact order are compared;
the reference and indexed audits also check deliberately malformed results. -/

namespace Compilatrix.IxIR1.ReaddressIndexTests

open Lean Ixon ReaddressAll Tools.Check

def snapshot (result : ReaddressAll.Result) : Json :=
  Json.mkObj [
    ("artifacts", toJson (result.artifacts.map Coverage.ir1Artifact)),
    ("declarations", Coverage.ir1Entries result.declarations),
    ("main", Coverage.byteJson result.main.bytes),
    ("address_map", toJson result.addressMap), ("reserved", toJson result.reserved)]

def auditParity (result : ReaddressAll.Result) (raw : List (Address × Decl))
    (main : Code) : IO Bool := do
  let prepared := result.prepareAudit raw
  let semantic := prepared.val.semanticAudit result raw main
  let rebuilt := semantic && prepared.val.rebuildImageAudit result raw main
  need (semantic == result.semanticAudit raw main && rebuilt == result.rebuildSemanticAudit raw main)
    "indexed address audits differ from the transparent predicates"
  return semantic && rebuilt

private structure Case where
  name : String
  reserved : List Address := []
  raw : List (Address × Decl) := []
  main : Code := .ret .erased
  accepted : Bool := true

private def compare (test : Case) : IO Json := do
  let reference := runReferenceCertified test.reserved test.raw test.main
  let indexed := runCertified test.reserved test.raw test.main
  match reference, indexed with
  | .ok before, .ok after =>
      need test.accepted s!"{test.name}: both addressers accepted a forbidden input"
      need (snapshot before.val == snapshot after.val) s!"{test.name}: indexed address artifact differs"
      need (← auditParity after.val test.raw test.main) s!"{test.name}: successful result failed its audit"
      return Json.mkObj [("name", toJson test.name), ("status", toJson "accepted"),
        ("artifacts", toJson after.val.artifacts.length),
        ("declarations", toJson after.val.declarations.length),
        ("map_entries", toJson after.val.addressMap.length)]
  | .error before, .error after =>
      need (!test.accepted && before == after) s!"{test.name}: address rejection differs: {before} / {after}"
      return Json.mkObj [("name", toJson test.name), ("status", toJson "rejected"), ("reason", toJson after)]
  | _, _ => throw (IO.userError s!"{test.name}: reference and indexed acceptance differ")

private def key (byte : UInt8) : Address := Address.replicate byte
private def plain : Decl := .fn ⟨0, .shared, true, .ret (.lit (.nat 7))⟩
private def call (address : Address) : Decl :=
  .fn ⟨0, .shared, true, .letOp (.call address #[]) (.ret .erased)⟩

def run : IO Json := do
  let a := key 0xa1
  let b := key 0xa2
  let c := key 0xa3
  let d := key 0xa4
  let external := key 0xee
  let self ← checked (MutualBlock.run [] [(a, call a)])
  let member := self.derivedAddresses.head!
  let cycle := [(a, call b), (b, call a)]
  let tests : List Case := [
    { name := "empty" },
    { name := "duplicate-unused-reserved", reserved := [external, external] },
    { name := "distinct-stable-externs", raw := [(a, .extern 1), (b, .extern 1)] },
    { name := "ordinary-deduplication", raw := [(a, plain), (b, plain)] },
    { name := "explicit-self-block", raw := [(a, call a)] },
    { name := "address-free-callSelf", raw := [(a, .fn ⟨0, .shared, true,
        .letOp (.callSelf #[]) (.ret .erased)⟩)] },
    { name := "mutual-member-order", raw := cycle },
    { name := "reversed-mutual-members", raw := cycle.reverse },
    { name := "mutual-block-deduplication", raw := [(a, call a), (b, call b)] },
    { name := "dependency-before-user", raw := (c, call a) :: cycle },
    { name := "external-reference", reserved := [external], raw := [(a, call external)] },
    { name := "duplicate-producer-first-match", accepted := false,
      raw := [(a, plain), (b, .extern 1), (b, .extern 2), (a, .extern 3)] },
    { name := "reserved-producer-first-match", accepted := false,
      reserved := [b, a], raw := [(a, plain), (b, plain)] },
    { name := "ordinary-protected-content", accepted := false,
      reserved := [plain.address], raw := [(a, plain)] },
    { name := "ordinary-transient-content", accepted := false, raw := [(plain.address, plain)] },
    { name := "ordinary-external-capture", accepted := false, raw := [(a, plain)],
      main := .letOp (.extern plain.address #[]) (.ret .erased) },
    { name := "block-protected-identity", accepted := false,
      reserved := [self.blockAddress], raw := [(a, call a)] },
    { name := "block-protected-member", accepted := false,
      reserved := [member], raw := [(a, call a)] },
    { name := "block-transient-identity", accepted := false,
      raw := [(a, call a), (self.blockAddress, .extern 0)] },
    { name := "block-transient-member", accepted := false,
      raw := [(a, call a), (member, .extern 0)] }]
  let cases ← tests.mapM compare
  let mapping : Readdress.Renaming := [(a, c), (a, d), (b, c)]
  let forward := Readdress.Renaming.Index.ofList mapping
  let backward := Readdress.Renaming.reverseIndex mapping
  need (forward.apply a == c && forward.apply external == external &&
    AddressEnv.lookup backward c == some a && (AddressEnv.lookup backward external).isNone)
    "indexed renaming changed duplicate precedence or misses"
  let raw := [(a, plain), (b, plain), (c, call a)]
  let main := .letOp (.call c #[]) (.ret .erased)
  let original ← checked (ReaddressAll.run [] raw main)
  let mutations : List (String × ReaddressAll.Result) := [
    ("missing-map-entry", { original with addressMap := original.addressMap.drop 1 }),
    ("extra-map-entry", { original with addressMap := original.addressMap ++ [(d, external)] }),
    ("conflicting-first-map-binding", { original with
      addressMap := (a, external) :: original.addressMap.drop 1 }),
    ("changed-main", { original with main := .ret .erased }),
    ("missing-artifact", { original with artifacts := original.artifacts.drop 1 }),
    ("duplicate-artifact", { original with artifacts := original.artifacts ++ original.artifacts }),
    ("transient-artifact", { original with artifacts := .stable a (.extern 0) :: original.artifacts }),
    ("noncanonical-artifact-key", { original with artifacts := [.ordinary d plain] }),
    ("rewritten-reserved-identity", { original with reserved := [a] })]
  for (name, changed) in mutations do
    need (!(← auditParity changed raw main)) s!"{name}: malformed address result passed both audits"
  need (!(← auditParity original (raw ++ [(a, .extern 0)]) main))
    "duplicate raw row passed the result audit"
  let cyclic ← checked (ReaddressAll.run [] cycle (.ret .erased))
  let block ← present cyclic.blocks.head? "cyclic comparison emitted no mutual block"
  let changed : ReaddressAll.Result := { cyclic with artifacts := [
    .mutual { block with members := block.members.map fun entry => (entry.1, plain) }] }
  need (!(← auditParity changed cycle (.ret .erased))) "changed mutual materialization passed the result audit"
  return Json.mkObj [("cases", toJson cases),
    ("lookup_precedence_and_misses", toJson true),
    ("malformed_result_rejections", toJson (mutations.length + 2))]

end Compilatrix.IxIR1.ReaddressIndexTests
