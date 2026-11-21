import IxAI
import IxAI.Examples
import IxAI.TrainClaim
import IxAI.Float
import IxAICore
import IxAIData.Scorer
import IxAIVerify.Ixon

/-!
Build-time tests: every `#guard` is evaluated when this library builds, so `lake build` fails if
any pipeline property regresses.
-/

namespace IxAITest

open IxAI IxAI.Examples

def proj : Project := (runSubmissions project).1
def outcomes : List Outcome := (runSubmissions project).2

def isAccepted : Outcome → Bool
  | .accepted _ => true
  | _ => false

def rejectedWith (o : Outcome) (f : Verdict → Bool) : Bool :=
  match o with
  | .rejected v => f v
  | _ => false

/-! ### Orchestration -/

-- A proof citing a lemma that is not yet accepted fails; the same proof succeeds later.
#guard rejectedWith (outcomes.getD 0 .unknownGoal) fun | .illTyped _ => true | _ => false
#guard isAccepted (outcomes.getD 6 .unknownGoal)
-- The weakened statement, the hole and the unlisted axiom are each rejected for the right reason.
#guard rejectedWith (outcomes.getD 2 .unknownGoal) fun | .wrongTarget .. => true | _ => false
#guard rejectedWith (outcomes.getD 3 .unknownGoal) fun | .hole => true | _ => false
#guard rejectedWith (outcomes.getD 4 .unknownGoal) fun | .policyViolation _ => true | _ => false
#guard proj.progress == (3, 3)
#guard proj.openGoals.isEmpty
-- A renamed duplicate becomes reuse, not a new constant.
#guard match (proj.submitHelper "w" duplicateHelper).2 with
  | .deduplicated n => n == "andComm"
  | _ => false
#guard (proj.submitHelper "w" duplicateHelper).1.store.entries.length == proj.store.entries.length
-- Submitting for an already-proved goal does no work.
#guard match (proj.submit "w" "andComm" ⟨"again", andComm, andCommProof⟩).2 with
  | .alreadyProved _ => true
  | _ => false

/-! ### Store, tasks and training -/

#guard proj.store.checkAll
#guard proj.store.entries.all fun e => e.axioms.isEmpty
-- `chain`'s task interface exposes `impTrans` (its dependency) but not `chain` or `andComm`.
#guard
  let t := mkTask proj.store (proj.store.findByStmt? (Address.ofStmt chain)).get! .standard
  t.interface.map (·.addr) == [impTransAddr]
-- Honest reference proofs pass on every task; every hack fails on every task.
#guard
  let tasks := proj.store.entries.map (mkTask proj.store · .standard)
  (runEpisode tasks honest).acceptRate == 1.0 && (runEpisode tasks hacker).acceptRate == 0.0
-- Reusing an allowed axiom *name* for another statement is still a policy violation.
#guard
  let t := mkTask proj.store proj.store.entries.head! ⟨[axiomId "Classical.choice" Stmt.top]⟩
  match reward t ⟨"abuse", t.targetStmt, .ax "Classical.choice" t.targetStmt⟩ with
  | .policyViolation _ => true
  | _ => false
#guard
  let d : DatasetClaim := ⟨proj.store.root, proj.store.entries.map (·.addr), []⟩
  d.holdsIn proj.store

/-! ### Certificates and light clients -/

#guard
  match proj.certify mock ((proj.goalFor? "chain").get!) with
  | some cert => lightClientAccepts mock proj.store.root chain [] cert
  | none => false
-- A certificate for one statement does not verify another, unproved one.
#guard
  match proj.certify mock ((proj.goalFor? "chain").get!) with
  | some cert => !lightClientAccepts mock proj.store.root (Stmt.atom 9) [] cert
  | none => false
-- No certificate is produced for a statement the store does not prove.
#guard (proj.certify mock ⟨"bogus", Stmt.atom 9⟩).isNone
-- Membership paths verify for every entry, and fail against another entry's leaf.
#guard proj.store.entries.all fun e =>
  match proj.store.membership? e.addr with
  | some path => path.verify proj.store.root e.addr
  | none => false
#guard
  match proj.store.membership? impTransAddr with
  | some path => !path.verify proj.store.root (proj.store.entries.getLast!.addr)
  | none => false

/-! ### BLAKE3 -/

-- The native hash agrees with the pure Lean specification of BLAKE3 used by Ix.
#guard (blake3 "abc".toUTF8).hex ==
  "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
#guard ["", "abc", String.ofList (List.replicate 3000 'x')].all fun s =>
  (blake3 s.toUTF8).bytes.data.toList == (Blake3.Pure.digest s.toUTF8.data.toList).toList
-- Different kinds of object never share an address, even with equal encodings.
#guard digestOf "stmt" (3 : Nat) != digestOf "item" (3 : Nat)

/-! ### Merkle roots (version 2) -/

def leafN (n : Nat) : Digest := digestOf "test/leaf" n
def leaves (n : Nat) : List Digest := (List.range n).map leafN
def la : Digest := leafN 1
def lb : Digest := leafN 2
def lc : Digest := leafN 3

-- The root binds the leaf count: a repeated last leaf is a different list with a different root.
#guard merkleRootV2 [la, lb, lc] != merkleRootV2 [la, lb, lc, lc]
#guard (List.range 9).all fun n => merkleRootV2 (leaves n) != merkleRootV2 (leaves (n + 1))
-- An index out of range is rejected, however the path is labelled.
#guard !({ merklePathV2 [la, lb, lc] 2 with index := 6 }).verify (merkleRootV2 [la, lb, lc]) lc
#guard !({ merklePathV2 [la, lb, lc] 2 with index := 3 }).verify (merkleRootV2 [la, lb, lc]) lc
-- A wrong count, a wrong leaf, or a sibling too many or too few is rejected.
#guard !({ merklePathV2 [la, lb, lc] 2 with count := 4 }).verify (merkleRootV2 [la, lb, lc]) lc
#guard !(merklePathV2 [la, lb, lc] 1).verify (merkleRootV2 [la, lb, lc]) la
#guard
  let p := merklePathV2 [la, lb, lc] 2
  !({ p with siblings := p.siblings ++ [la] }).verify (merkleRootV2 [la, lb, lc]) lc &&
    !({ p with siblings := p.siblings.dropLast }).verify (merkleRootV2 [la, lb, lc]) lc
-- Every honest path of every tree up to 17 leaves verifies.
#guard (List.range 18).all fun n =>
  (List.range n).all fun i => (merklePathV2 (leaves n) i).verify (merkleRootV2 (leaves n)) (leafN i)
-- Version 1, kept only for recorded roots, has the collision version 2 removes.
#guard merkleRootV1 [la, lb, lc] == merkleRootV1 [la, lb, lc, lc]

/-! ### Curation: an unaddressed name refuses the item -/

section Curation
open IxAIData

def fixtureNames : Std.HashMap String Digest :=
  (({} : Std.HashMap String Digest).insert "bad" (leafN 10)).insert "sorryAx" (leafN 11)
def fixtureThm : Premise Digest := ⟨leafN 10, 0, 0, { consts := [], kinds := [] }⟩
-- The extraction fixture of the review: item `bad` whose one axiom, `UnmappedAxiom`, has no address.
def fixtureItem : Item Digest := itemOf fixtureNames fixtureThm "" "UnmappedAxiom" "0"
def fixturePolicy : Policy Digest := { sorryAx := leafN 11, allowedAxioms := [] }
def fixtureEx : Extraction :=
  { modules := #[⟨"Mathlib.Test", []⟩], library := #[(fixtureThm, "bad")], items := #[(fixtureItem, "bad")]
    unjoined := fixtureItem.unresolved, names := fixtureNames, addrNames := {} }

#guard fixtureItem.unresolved == 1
#guard acceptance fixturePolicy fixtureItem == some .unresolvedName
#guard (curate fixtureEx fixturePolicy (fun _ => false)).accepted.isEmpty
#guard (curate fixtureEx fixturePolicy (fun _ => false)).refusals.lookup .unresolvedName == some 1
-- An item whose names all resolve is still accepted.
#guard accepted fixturePolicy (itemOf fixtureNames fixtureThm "bad" "" "0")

end Curation

section Ranking
open IxAIData

/-- Module lists, each module listed after its imports (as `reachability` requires), with
repeated imports. -/
def reachFixture (n : Nat) : Array Module :=
  (Array.range n).map fun i =>
    ⟨s!"M{i}", if i == 0 then [] else [(i * 7 + 3) % i, (i * i + 5) % i, i / 2, i - 1, i - 1]⟩

/-- `reachBits` against the specification `reachability`, every entry and every row. -/
def reachAgrees (ms : Array Module) : Bool :=
  let spec := reachability ms
  let r := reachBits ms
  let n := ms.size
  ((List.range (n + 2)).all fun i => (List.range (n + 2)).all fun k => r.get i k == ((spec[i]?.getD #[])[k]?.getD false)) &&
    (List.range n).all fun i => r.row i == (List.range n).toArray.filter ((spec[i]!)[·]!)

#guard [0, 1, 7, 8, 9, 17, 40].all fun n => reachAgrees (reachFixture n)

/-- Scores with many ties. -/
def tieScores (n m : Nat) : Array Int := (Array.range n).map fun i => Int.ofNat (i * 37 % m) - 3

-- `topBy` gives the first `k` of the sorted ranking, so the first 30 of a longer top are the top 30.
#guard [(0, 7), (1, 5), (29, 11), (60, 13)].all fun (n, m) =>
  let ss := tieScores n m
  let sorted := rankBy ((Array.range n).map fun i => (ss[i]!, i))
  [0, 1, 30, 50, 80].all (fun k => topBy k n (scoreBefore ss) == sorted.extract 0 k) &&
    topBy 30 n (scoreBefore ss) == (topBy 50 n (scoreBefore ss)).extract 0 30

-- The `k` nearest references of `thmStats`, in any order of filling.
#guard [3, 40].all fun n =>
  let sims : Array (Int × Nat) := (Array.range n).map fun i => (Int.ofNat (i * 13 % 7), (i * 31) % 1009)
  let lt := fun (a b : Int × Nat) => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)
  [0, 1, 8, 50].all fun k =>
    (topBy k sims.size fun a b => lt sims[a]! sims[b]!).map (sims[·]!) == (sims.qsort lt).extract 0 k

#guard [(0, []), (10, [3, 3, 1, 9, 0, 1]), (100, (List.range 60).map (· * 7 % 100) ++ (List.range 60).map (· * 3 % 100))].all
  fun (n, xs) => markedPositions n xs.toArray == (dedupNat xs).qsort (· < ·)

end Ranking

/-! ### Decisions -/

#guard approvalGate.decide ⟨[950, 30, 20]⟩ == .approve
#guard approvalGate.decide ⟨[600, 300, 100]⟩ == .escalate
#guard approvalGate.decide ⟨[100, 450, 450]⟩ == .reject
#guard (ChoiceAnswer.concentration ⟨[1000, 0, 0]⟩) == 1000
#guard (ChoiceAnswer.concentration ⟨[334, 333, 333]⟩) < 5

/-! ### Certified training (small config, so the tests stay fast) -/

def tinyData : Dataset := Dataset.generate 42 60 3
def tinyCfg : TrainConfig :=
  { seed := 7, hidden := 4, lrRaw := 1, epochs := 2, batchSize := 20, bound := 1 <<< 20 }
def tinyRun : List (Link (MLP Fx) (List Nat)) := tinyCfg.run tinyData
def tinyClaim : TrainClaim :=
  { datasetRoot := tinyData.root, config := tinyCfg,
    finalCommit := (chainEnd tinyCfg.init tinyRun).commit }

-- Labels are decided, and the dataset is reproducible from its seed.
#guard tinyData.check
#guard (Dataset.generate 42 60 3).root == tinyData.root
#guard tinyRun.length == 6
-- The honest run verifies and ends at the specified weights.
#guard verifyRun tinyClaim tinyData tinyRun
#guard chainEnd tinyCfg.init tinyRun == (tinyCfg.spec tinyData : MLP Fx)
-- Changing one weight in one step is rejected.
#guard
  let bad := tinyRun.modify 3 fun l => { l with after := { l.after with b2 := ⟨l.after.b2.raw + 1⟩ } }
  !verifyRun tinyClaim tinyData bad
-- Reordering batches is rejected even when every step is computed correctly.
#guard
  let swapped := tinyCfg.schedule tinyData.items.size |>.reverse
  let links := (swapped.foldl (init := ((tinyCfg.init : MLP Fx), #[])) fun (m, acc) idx =>
    let m' := tinyCfg.stepFn tinyData m idx; (m', acc.push ⟨m, idx, m'⟩)).2.toList
  !verifyRun { tinyClaim with finalCommit := (chainEnd tinyCfg.init links).commit } tinyData links
-- A claim against a different dataset root is rejected.
#guard !verifyRun { tinyClaim with datasetRoot := default } tinyData tinyRun
-- bfloat16: the honest run verifies too.
#guard verifyRun { tinyClaim with
    finalCommit := (chainEnd tinyCfg.init (tinyCfg.run tinyData : List (Link (MLP BF16) (List Nat)))).commit }
  tinyData (tinyCfg.run tinyData : List (Link (MLP BF16) (List Nat)))
-- In bfloat16, a sequence of rounded additions depends on the order: 1 + 1 + 1024 − 1024 is 0,
-- but 1024 − 1024 + 1 + 1 is 2. The exactly accumulated dot product gives 2 either way.
#guard
  let vs : List BF16 := [Arith.ofInt 1, Arith.ofInt 1, Arith.ofInt 1024, Arith.ofInt (-1024)]
  let seq := fun (l : List BF16) => l.foldl Arith.add Arith.zero
  seq vs != seq vs.reverse &&
    (sumExact vs : BF16) == sumExact vs.reverse && (sumExact vs : BF16) == Arith.ofInt 2
-- Exact accumulation: the rounded dot product does not depend on the order of the terms.
#guard
  let xs : List Fx := [⟨300⟩, ⟨-77⟩, ⟨1⟩, ⟨255⟩]
  let ys : List Fx := [⟨-5⟩, ⟨129⟩, ⟨-1000⟩, ⟨3⟩]
  (Arith.dot xs ys : Fx) == Arith.dot xs.reverse ys.reverse

/-! ### Digests: 32 bytes, hexadecimal in either case -/

def someDigest : Digest := leafN 1
#guard Digest.ofHex? someDigest.hex == some someDigest
#guard Digest.ofHex? someDigest.hex.toUpper == some someDigest
#guard (Digest.ofHex? (String.ofList (someDigest.hex.toList.drop 2))).isNone
#guard (Digest.ofHex? (someDigest.hex ++ "00")).isNone
#guard (Digest.ofHex? ("g" ++ String.ofList (someDigest.hex.toList.drop 1))).isNone
#guard (Digest.ofBytes? (ByteArray.mk (Array.replicate 31 0))).isNone
#guard (Digest.ofBytes? (ByteArray.mk (Array.replicate 33 0))).isNone
#guard (Digest.ofBytes? (ByteArray.mk (Array.replicate 32 0))).isSome
#guard someDigest.wellFormed && (blake3 ByteArray.empty).wellFormed

/-! ### The reward goal's statement, read from compiled Ixon

`goalConstant` is the compiled `IxAIReward.goal` of the `identity` task with the proof `by decide`,
as `ix compile` stored it: a theorem whose type is a shared reference to `IxAIReward.target`. -/

def bytesOfHex (s : String) : ByteArray :=
  let rec go : List Char → List UInt8
    | a :: b :: rest =>
      let v := fun (c : Char) => if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
      (v a * 16 + v b).toUInt8 :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

def goalConstant : ByteArray := bytesOfHex (
  "d00900b0732008b0b37221020073210901200d722000b0b3b172210c01200db1042001200771200673210a0020056471" ++
  "200b6472200f71200e722003b2b2b11011157bc3898f06e3e6f2ca83411efd0d43b8846b57d2f6088e18f3447ddc3b28" ++
  "146cd5021f71b614377375e3c910f80723fb1e7e89b51bf94725c008f1f8c572173299c76efa82e689210a09e49ad09c" ++
  "14ee1108f2da8d355ef9333b1583a1d51f5b18dca6ea3dfd40459ef980beebd0df797d45c74fc687939cb87246e315ba" ++
  "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e21335e1cc809f6f076521a43f85068d5592" ++
  "220407c0532b6a08952f40d8523d04bc9b8173f3e8d336abec134b1a1f64c9fdd21edfc385c36c03366700c0cee939dc" ++
  "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762bd7e9c85d35b4c18d6960d8a717ac38f" ++
  "7ebdca29cb79348fbfcbf268dd5f2cd8c37d6290e00fb865fb5db7bce18fd69e6d1674ad573724b85466ea9f7578a207" ++
  "cb84bffa6d7092a309630214af29d9ec4e35cd5e0003eb9cdf75ee484e24925bce0d0a2c5431725b402acffa7790043d" ++
  "c50b8e69aad04861636fb759dc27ed68d494dc601386ba8e8f0b711fe62a2d60ab60c6488c8cf6ce97796ebc3ad5fefb" ++
  "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4ec83c43dbf960e5635c7b56f6077543f" ++
  "08b10988dfec1ab40209387cf3fd001ef81c195f53231f0b3d8f6fd088c3480ef9abcdc35bc442e0763e2e8197ae8130" ++
  "02000100")

def identityTarget : Digest :=
  (Digest.ofHex? "146cd5021f71b614377375e3c910f80723fb1e7e89b51bf94725c008f1f8c572").getD default

/-- A version-4 `.ixe` holding exactly `consts`, with no blobs, names or metadata. -/
def ixeOf (consts : List (Digest × ByteArray)) : ByteArray :=
  -- Ixon's TagN with no flag bits, for values below 16512.
  let n := fun (v : Nat) => if v < 128 then ByteArray.mk #[v.toUInt8]
    else ByteArray.mk #[(128 + (v - 128) / 256).toUInt8, ((v - 128) % 256).toUInt8]
  consts.foldl (fun acc (a, c) => acc ++ a.bytes ++ n c.size ++ c)
    (ByteArray.mk #[0xE4] ++ ByteArray.mk (Array.replicate 32 0) ++ ByteArray.mk #[0, 0, 0] ++
      n consts.length)

def withByte (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray := b.set! i v

def judgeGoal (c : ByteArray) (target : Digest) : Bool :=
  (IxAIVerify.Ixon.checkGoalType (ixeOf [(blake3 c, c)]) (blake3 c) target).toBool

-- The fixture is the constant at the address `ix addr-of` reports for `IxAIReward.goal`.
#guard (blake3 goalConstant).hex == "60cc345698311eb6e9f35f6c19bdef80e577f066c3c91e89528ac500bcdca192"
#guard judgeGoal goalConstant identityTarget
-- Another target is refused.
#guard !judgeGoal goalConstant someDigest
-- A goal whose type is another shared expression (`Share(1)`, a reference to another constant).
#guard goalConstant.get! 3 == 0xB0 && !judgeGoal (withByte goalConstant 3 0xB1) identityTarget
-- A definition rather than a theorem, and a universe-polymorphic theorem.
#guard !judgeGoal (withByte goalConstant 1 0x05) identityTarget
#guard !judgeGoal (withByte goalConstant 2 0x01) identityTarget
-- Truncated or extended bytes do not parse.
#guard !judgeGoal (goalConstant.extract 0 (goalConstant.size - 1)) identityTarget
#guard !judgeGoal (goalConstant.push 0) identityTarget
-- Bytes stored under an address that is not their BLAKE3 are refused.
#guard !(IxAIVerify.Ixon.checkGoalType
  (ixeOf [(blake3 goalConstant, withByte goalConstant 200 0)]) (blake3 goalConstant) identityTarget).toBool
-- A goal missing from the environment is refused.
#guard !(IxAIVerify.Ixon.checkGoalType (ixeOf []) (blake3 goalConstant) identityTarget).toBool

end IxAITest
