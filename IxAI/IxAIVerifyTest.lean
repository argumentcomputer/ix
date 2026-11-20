import IxAIVerify
import Lean.Elab.Command

/-!
Build-time tests of the verification layer: every `#guard` (and every `#eval` that throws on
failure) runs when this library builds.
-/

namespace IxAIVerifyTest

open IxAI IxAIVerify Lean

/-! ### Trajectories are checked against the consumer's job, not the submitted header -/

def ds : DataSpec := {}

/-- The review's submission: the expected job with 0 epochs and no steps. -/
def zeroEpochs : String :=
  "\n".intercalate [configLine { defaultConfig with epochs := 0 }, "format fx", dataLine ds ds.generate] ++ "\n"

def defaultJob : TrajectoryJob := ⟨defaultConfig, {}, "fx"⟩

#guard (namedJobs.lookup "default").map (·.digest) == some defaultJob.digest

#guard !(checkTrajectory defaultJob none none zeroEpochs).accepted
-- By digest: the zero-epoch header names a job whose digest is not the expected one.
#guard !(checkTrajectory defaultJob (some defaultJob.digest) none zeroEpochs).accepted

def tinyCfg : TrainConfig :=
  { seed := 7, hidden := 4, lrRaw := 1, epochs := 2, batchSize := 20, bound := 1 <<< 20 }
def tinyData : DataSpec := { seed := 42, n := 60, depth := 3 }
def tinyJob : TrajectoryJob := ⟨tinyCfg, tinyData, "fx"⟩
def tinyText : String := trajectory (α := Fx) "fx" tinyCfg tinyData tinyData.generate
def tinyFinal : Digest :=
  (chainEnd tinyCfg.init (tinyCfg.run tinyData.generate : List (Link (MLP Fx) (List Nat)))).commit

-- The honest run of the expected job is accepted, by name and by digest, and binds its weights.
#guard (checkTrajectory tinyJob none none tinyText).accepted
#guard (checkTrajectory tinyJob (some tinyJob.digest) (some tinyFinal) tinyText).accepted
-- Returned weights other than the verified result are rejected.
#guard !(checkTrajectory tinyJob none (some default) tinyText).accepted
-- The same run submitted against a different expected job is rejected.
#guard !(checkTrajectory { tinyJob with config := { tinyCfg with epochs := 3 } } none none tinyText).accepted
#guard !(checkTrajectory { tinyJob with format := "bf16" } none none tinyText).accepted
-- Dropping the last step is rejected: the schedule is the job's.
#guard
  let ls := tinyText.splitOn "\n" |>.filter (· ≠ "")
  !(checkTrajectory tinyJob none none ("\n".intercalate (ls.take (ls.length - 2)) ++ "\n")).accepted

/-! ### Aiur artifact framing -/

#guard Ixon.nat 0 == [0]
#guard Ixon.nat 127 == [127]
#guard Ixon.nat 128 == [128, 0]
#guard Ixon.nat 16511 == [191, 255]
#guard Ixon.nat 16512 == [192, 0, 0]
-- The wrapper carries the package and no arguments; the receipt-side split finds it again.
#guard
  let pkg : ByteArray := ⟨(Ixon.packageMagic ++ Ixon.nat 2 ++ [1, 2, 3]).toArray⟩
  let exec : ByteArray := ⟨(Ixon.executionMagic ++ Ixon.nat 2).toArray⟩ ++ pkg ++
    ⟨(Ixon.nats [5, 300] ++ Ixon.nats [] ++ Ixon.nat 0).toArray⟩
  Ixon.isPackage pkg && (Ixon.programOf exec [5, 300]).map (·.data) == some pkg.data &&
    (Ixon.wrapPackage pkg).size == 9 + pkg.size + 3

/-! ### The dataset root of the commitment -/

#guard match configNamed? "tiny" with
  | some c => datasetRoot c != datasetRoot { c with trainSize := c.trainSize + 1 }
  | none => false

/-! ### Submissions: exactly one term, no escape hatches -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let accept := ["by decide", "by\n  simp", "rfl", "(by decide : True)"]
  let reject :=
    ["by decide\n\n#eval IO.FS.writeFile \"/tmp/x\" \"proof text executed IO\"",
     "by exact cheat\naxiom cheat {p : Prop} : p",
     "by native_decide",
     "by decide +native",
     "by run_tac pure ()",
     "by\n  set_option maxHeartbeats 0 in decide",
     "(IO.FS.writeFile \"/tmp/x\" \"\" : IO Unit) |> fun _ => trivial",
     "by decide\ntheorem other : True := trivial",
     "by decide\n@[simp] theorem other : True := trivial",
     "by decide\ninitialize pure ()",
     "",
     "by decide )"]
  for p in accept do
    if let .error e := checkSubmission env p then throwError s!"refused an honest proof {repr p}: {e}"
  for p in reject do
    if (checkSubmission env p).toOption.isSome then throwError s!"accepted {repr p}"


/-! ### Trajectory parsing is strict -/

def tinyLines : List String := tinyText.splitOn "\n" |>.filter (· ≠ "")

/-- The trajectory with line `i` replaced by `f` of it. -/
def editLine (i : Nat) (f : String → String) : List String :=
  tinyLines.zipIdx.map fun (l, k) => if k == i then f l else l

def parsesFx (ls : List String) : Bool :=
  (parseLinks (α := Fx) tinyCfg ls).toOption.isSome

#guard parsesFx tinyLines
-- A negative header value is refused, not read as 0.
#guard (parseHeader ["config -7 4 1 2 20 1048576", "data 42 60 3 " ++ tinyData.generate.root.hex]).toOption.isNone
#guard (parseHeader ["config 7 4 1 -2 20 1048576", "data 42 60 3 " ++ tinyData.generate.root.hex]).toOption.isNone
#guard (parseHeader ["config 7 4 1 2 20 1048576", "data -42 60 3 " ++ tinyData.generate.root.hex]).toOption.isNone
#guard (parseHeader ["config 7 4 1 2 20 1048576", "data 42 60 3 " ++ tinyData.generate.root.hex]).toOption.isSome
-- Two config lines, or a format line with extra words, are refused.
#guard (parseHeader ["config 7 4 1 2 20 1048576", "config 7 4 1 3 20 1048576",
  "data 42 60 3 " ++ tinyData.generate.root.hex]).toOption.isNone
#guard (parseHeader ["config 7 4 1 2 20 1048576", "format fx bf16",
  "data 42 60 3 " ++ tinyData.generate.root.hex]).toOption.isNone
-- A negative batch index is refused.
#guard !parsesFx (editLine 3 (· ++ " -1"))
-- A `w` line with an extra parameter is refused, though `MLP.ofList` would ignore it.
#guard !parsesFx (editLine 4 (· ++ " 0"))
#guard !(checkTrajectory tinyJob none none ("\n".intercalate (editLine 4 (· ++ " 0")) ++ "\n")).accepted
-- Lines must alternate `step`, `w`; unknown records are refused.
#guard !parsesFx (tinyLines.take 3 ++ [tinyLines[4]!, tinyLines[3]!] ++ tinyLines.drop 5)
#guard !parsesFx (tinyLines ++ ["item 1 0 0 0 0 0 0 0 0"])
#guard !parsesFx (tinyLines.map fun l => if l.startsWith "step " then "steps" ++ String.ofList (l.toList.drop 4) else l)
-- Words must be canonical integers.
#guard !parsesFx (editLine 4 fun l => "w +" ++ String.ofList (l.toList.drop 2))
-- An IEEE word must be a bit pattern that reads back to itself.
#guard (Wire.ofWire (α := BF16) (-1)).isNone
#guard (Wire.ofWire (α := BF16) 0x3f80).isSome

/-! ### Step names never collide -/

#guard stepName 0 == "step-000" && stepName 7 == "step-007" && stepName 999 == "step-999"
#guard stepName 1000 == "step-1000" && stepName 12345 == "step-12345"
#guard ((List.range 1200).map stepName).eraseDups.length == 1200

/-! ### Canonical, range-checked weights -/

#guard canonicalInt? "0" == some 0 && canonicalInt? "-5" == some (-5) && canonicalInt? "4319" == some 4319
#guard ["", "-", "+5", "007", "-0", "00", "1e3", "5 ", "0x10", "--1"].all (canonicalInt? · |>.isNone)
#guard (parseInts ["1", "-2"]).toOption == some [1, -2]
#guard (parseInts ["1", "+2"]).toOption.isNone
#guard words "1\t-2  3\r" == ["1", "-2", "3"]

def zeros : List Int := List.replicate (paramCount 16) 0

#guard (checkModelWords 16 zeros).toOption.isSome
#guard (checkModelWords 16 (zeros.set 5 4319)).toOption.isSome
#guard (checkModelWords 16 (zeros.set 5 (-4096))).toOption.isSome
#guard (checkModelWords 16 (zeros.set 5 4320)).toOption.isNone
#guard (checkModelWords 16 (zeros.set 5 (-4097))).toOption.isNone
-- An alias of a weight modulo the field is out of range, so it can never share a proof.
#guard (checkModelWords 16 (zeros.set 5 (3 + goldilocks))).toOption.isNone
#guard (checkModelWords 16 (zeros.drop 1)).toOption.isNone
#guard outOfRange [0, 1, 5000, -5000] == some (2, 5000)

/-! ### Route outcomes -/

def route (kind : String) (status : RouteStatus) : RouteResult := { kind, status, detail := [] }

-- Only unknown kinds: nothing implemented, so neither missing evidence nor proved.
#guard trainingVerdict [route "train-tree" .incomplete] == ⟨false, false, false⟩
#guard outcomeOf false (trainingVerdict [route "train-tree" .incomplete]).incomplete false true == .predicted
#guard trainingVerdict [route "aiur-steps" .incomplete] == ⟨false, false, true⟩
#guard trainingVerdict [route "aiur-steps" .incomplete, route "aiur-exec" .attested] == ⟨false, false, false⟩
-- A rejected route rejects the package even when another route verified.
#guard trainingVerdict [route "aiur-train" .verified, route "aiur-steps" .rejected] == ⟨true, true, false⟩
#guard outcomeOf true false true true == .rejected
#guard outcomeOf false false true true == .proved
#guard outcomeOf false true false false == .incomplete

/-! ### Reading Ixon -/

-- The TagN reader inverts the writer.
#guard [0, 1, 127, 128, 300, 16511, 16512, 81919, 81920, 2 ^ 24 + 5, 2 ^ 32 + 7, 2 ^ 63].all fun v =>
  (Ixon.tagN0.run { bytes := ⟨(Ixon.nat v).toArray⟩ }).toOption.map (fun (x, c) => (x, c.pos)) ==
    some (v, (Ixon.nat v).length)

def addr (k : Nat) : Digest := ⟨ByteArray.mk (Array.replicate 32 k.toUInt8)⟩

def specD : Digest := addr 1
def bindingD : Digest := addr 2
def constD : Digest := addr 3
def policy : ClaimPolicy := { spec := specD, binding := bindingD }

/-- A stored proof: proof tag `F0 + variant`, then the claim's scope and payload, then 3 proof
bytes. -/
def storedProof (variant validator : UInt8) (axioms assumptions : Option Digest) : ByteArray :=
  ⟨#[0xF0 + variant, 4, validator]⟩ ++ specD.bytes ++ bindingD.bytes ++ Ixon.optAddrBytes axioms ++
    constD.bytes ++ Ixon.optAddrBytes assumptions ++ ⟨#[3, 7, 7, 7]⟩

-- The exact claim: the stored proof's claim bytes are the policy's `Check` claim, byte for byte.
#guard match Ixon.checkProofClaim (storedProof 1 3 none none) with
  | .ok c => c == policy.expected constD &&
      (policy.expected constD).ser.data == #[0xE4] ++ ((storedProof 1 3 none none).extract 1 101).data
  | .error _ => false
-- A claim that assumes its binding, depends on assumptions or user axioms, or is not a Check claim,
-- is not the policy's claim.
#guard match Ixon.checkProofClaim (storedProof 1 4 none none) with
  | .ok c => c != policy.expected constD && claimDifference c (policy.expected constD) ==
      ["assumes its role binding instead of validating it"]
  | .error _ => false
#guard match Ixon.checkProofClaim (storedProof 1 3 none (some (addr 9))) with
  | .ok c => c != policy.expected constD
  | .error _ => false
#guard match Ixon.checkProofClaim (storedProof 1 3 (some (addr 9)) none) with
  | .ok c => c != policy.expected constD
  | .error _ => false
#guard (Ixon.checkProofClaim (storedProof 0 3 none none)).toOption.isNone

def tRef (k : Nat) : Ixon.Term := .ref (addr k) []

-- Template matching binds holes consistently and only to closed terms.
#guard Ixon.matchTemplate 2 (.app (.app (tRef 10) (.var 1)) (.var 0)) (.app (.app (tRef 10) (tRef 11)) (tRef 12))
  == some #[tRef 11, tRef 12]
#guard Ixon.matchTemplate 1 (.app (.var 0) (.var 0)) (.app (tRef 11) (tRef 12)) == none
#guard Ixon.matchTemplate 1 (.app (.var 0) (.var 0)) (.app (tRef 11) (tRef 11)) == some #[tRef 11]
#guard Ixon.matchTemplate 1 (.all 0 (tRef 5) (.app (.var 0) (.var 1))) (.all 0 (tRef 5) (.app (.var 0) (tRef 11)))
  == some #[tRef 11]
#guard Ixon.matchTemplate 1 (.all 0 (tRef 5) (.app (.var 0) (.var 1))) (.all 0 (tRef 5) (.app (.var 0) (.var 0)))
  == none
#guard Ixon.matchTemplate 1 (.app (tRef 10) (.var 0)) (.app (tRef 13) (tRef 11)) == none
#guard match Ixon.Term.ofJson (Ixon.Term.all 17 (.sort (.succ .zero)) (.app (tRef 4) (.nat 300))).toJson with
  | .ok t => t == .all 17 (.sort (.succ .zero)) (.app (tRef 4) (.nat 300))
  | .error _ => false

/-! ### The model is read from its Ixon literal -/

def enc : ModelEncoding :=
  { modelMk := addr 20, listCons := addr 21, listNil := addr 22, fxMk := addr 23, intOfNat := addr 24,
    intNegSucc := addr 25 }

def litList (xs : List Ixon.Term) : Ixon.Term :=
  xs.foldr (fun x acc => .app (.app (.app (.ref enc.listCons [.zero]) (tRef 99)) x) acc)
    (.app (.ref enc.listNil [.zero]) (tRef 99))

def litFx (x : IxAICore.Fx) : Ixon.Term :=
  .app (.ref enc.fxMk []) (match x.raw with
    | .ofNat n => .app (.ref enc.intOfNat []) (.nat n)
    | .negSucc n => .app (.ref enc.intNegSucc []) (.nat n))

def litModel (m : IxAICore.Model) : Ixon.Term :=
  .app (.app (.app (.app (.ref enc.modelMk []) (litList (m.w1.map (litList ∘ List.map litFx))))
    (litList (m.b1.map litFx))) (litList (m.w2.map (litList ∘ List.map litFx)))) (litList (m.b2.map litFx))

def sampleModel : IxAICore.Model := modelOfRaw 2 ((List.range (paramCount 2)).map fun i => (i : Int) - 20)

#guard (decodeModel enc (litModel sampleModel)).toOption == some sampleModel
#guard (decodeModel enc (litModel encodingSample)).toOption == some encodingSample
-- Another constructor in place of `Int.negSucc` is not a model literal.
#guard (decodeModel { enc with intNegSucc := addr 26 } (litModel sampleModel)).toOption.isNone

/-! ### One source for the deployed theorems and their templates -/

#guard String.join ((claimTemplates.filter (·.outputs.isEmpty)).map (·.theoremSource)) ==
  "/-- The deployed system never publishes a false formula. -/\n" ++
  "theorem deployedPublishSound (f : Formula) (h : Triage.act ⟨200⟩ trainedOutput f = .publish) :\n" ++
  "    f.valid = true :=\n  Triage.act_publish_sound _ _ f h\n\n" ++
  "/-- The deployed system publishes only formulas its model is confident about. -/\n" ++
  "theorem deployedPublishConfident (f : Formula) (h : Triage.act ⟨200⟩ trainedOutput f = .publish) :\n" ++
  "    Triage.confidence trainedOutput f ≥ 200 :=\n  Triage.act_publish_confident _ _ f h\n\n" ++
  "/-- The deployed system defers exactly when its model is not confident. -/\n" ++
  "theorem deployedDeferIff (f : Formula) :\n" ++
  "    Triage.act ⟨200⟩ trainedOutput f = .defer ↔ Triage.confidence trainedOutput f < 200 :=\n" ++
  "  Triage.act_defer_iff _ _ f\n\n"
-- Every certified decision is about a formula inside the gate's domain (atoms `P0 … P2`).
#guard receiptFormulas.all (·.inScope)

#guard claimTemplates.map (·.id) == ["cardCertified", "decision0", "decision1", "decision2", "decision3",
  "deployedPublishSound", "deployedPublishConfident", "deployedDeferIff"]

/-! ### Receipts name proofs by claim -/

#guard receiptProof [Json.mkObj [("claim", "decision1"), ("proof", "a")],
  Json.mkObj [("name", "IxAICertified.full.decision10"), ("proof", "b")]] "decision1" == some "a"
#guard receiptProof [Json.mkObj [("name", "IxAICertified.full.decision10"), ("proof", "b")]] "decision1" == none
#guard receiptProof [Json.mkObj [("name", "IxAICertified.full.decision1"), ("proof", "c")]] "decision1" == some "c"

/-! ### A commitment that is not UTF-8 is refused, not a panic -/

#eval show IO Unit from do
  let (h, path) ← IO.FS.createTempFile
  h.write ⟨#[0x7b, 0xff, 0xfe, 0x7d]⟩
  h.flush
  let tools : Tools := { verifyClaim := "/nonexistent", aiurExecCheck := "/nonexistent",
                         plonkVerify := "/nonexistent", aiurJoinCheck := "/nonexistent", ixw := "/nonexistent",
                         ixStore := "/nonexistent" }
  let (o, _) ← verifyPackage tools path path none "/nonexistent"
  IO.FS.removeFile path
  unless o == .rejected do throw (IO.userError "a non-UTF-8 commitment was not refused")

/-! ### The worker pool keeps order and runs every job -/

#eval show IO Unit from do
  let out ← runPool 3 ((List.range 50).map fun i => pure (i * i))
  unless out == (List.range 50).map (fun i => i * i) do throw (IO.userError "runPool lost order")
  let empty ← runPool 4 ([] : List (IO Nat))
  unless empty.isEmpty do throw (IO.userError "runPool invented a result")

/-! ### The compressed certificate's statement is the one Ix's pipeline proves

The digests are those of the three certificates in `.truthmines/aiur`: one `train_tree` execution
(`single`), 600 `Fixed::step` executions (`aiurexec`) and 30 `Fixed::train_block` executions
(`aiurexec-block`). Each statement and its public inputs are the ones the pipeline's terminal
stage recorded (`ladder/plonk/summary.json`), and the root claim's and wrapper claim's encodings
hash to the files the pipeline read and wrote (`top/root/root-claims.bin`,
`ladder/wrap/out/claims.bin`). -/

section Compression
open Compression

def hx (s : String) : Digest := (Digest.ofHex? s).getD default

def wrapKeyV3 : Digest := hx "1bc0cd05e3d1ad8d0cf6248dc8f398a007cb845b571b2d1cf66d67cc6ba6ad3f"

structure Certified where
  keys : ExecKeys
  identity : Digest
  output : Digest
  statement : String
  limbs : Nat × Nat

def single : Certified :=
  { keys := { aggregator := hx "8ee3db8db9920078be199d7eb54bd234559cabf3cb55a0f6e87cf055cacd38b4", aggregatorEntry := 0
              program := hx "fb9463a29b997d7c81996ee380be10f52230c3f97c0936a82fae9a3e63d3bfa7", programEntry := 0 }
    identity := hx "041e4ea258bc4b5fb7d71c2a4007b346ad2c0e60393034711d0740ff69a01ab7"
    output := hx "32ec9beaa13afc453500a9b6a9504461bf152329caf38a252440183873bcf081"
    statement := "2771ff4840978d61b6c93ae8f35ea8ad0821ef5ee9d1d2473820affe18f889a0"
    limbs := (230830675013842123813295254630471528743, 213392856013084323673301806045434159368) }

def steps600 : Certified :=
  { keys := { aggregator := hx "6638d08dde6721e6682b47fc2f64468f8aaa58203abc6078551abb750aa89c5a", aggregatorEntry := 0
              program := hx "425433fea85958a1dae08e05665035cbdd1124f304f191370eedcb3647b72c75", programEntry := 0 }
    identity := hx "fb7c4fd49a8108ee74e773ff8f97e15c8d2877e46b309b1ba2a105799ea48960"
    output := hx "df9df4eb42b107e9747e0b234a020bb2c2743b2f8e2e81f2e1c96c1a74cc9a98"
    statement := "1c67d287c859381935ed397c1a3626558bda7d2821a965a6331f3c0a9c074071"
    limbs := (113182784270839165377699429132855830300, 150535224862269833386811202499105381003) }

def blocks30 : Certified :=
  { keys := { aggregator := hx "4c900afcbf306d3cc8f602aae0df73649e10ef7951ed6955fbb480420ac3c285", aggregatorEntry := 0
              program := hx "d46caf1e358f9e28744a1163b2d25b2ea4de331870fcc78e1625119edfa1da58", programEntry := 0 }
    identity := hx "13ae716950a4c1af699bd58002e87777b2cbde76bd917b7b7a5051914364951c"
    output := hx "025949281a84932f637134d1ebba00323c4edd20c0939928b1376d7268692cc8"
    statement := "8b28f4f9358b5140f65cb5f99b845b9b743f268dd5170deb1e3a7271711b9d7a"
    limbs := (206505527996502523364869932234380159115, 162981562705501265259758953046240280436) }

def Certified.computed (c : Certified) : Digest :=
  terminalStatement wrapKeyV3 c.keys.aggregator (execRootClaim c.keys.aggregatorEntry c.identity c.output)

#guard [single, steps600, blocks30].all fun c => blake3 (execIdentity c.keys) == c.identity
#guard [single, steps600, blocks30].all fun c => c.computed.hex == c.statement
#guard [single, steps600, blocks30].all fun c => statementLimbs c.computed == c.limbs
-- The intermediate encodings are the pipeline's files, byte for byte.
#guard (blake3 (claimsBytes [execRootClaim 0 single.identity single.output])).hex ==
  "5ab1c89cf7e7ba64d27dc2d1873d5ae35d0833334003a1a3f4338dcc1f29b29f"
#guard digestWords (wrapStatement single.keys.aggregator [execRootClaim 0 single.identity single.output]) ==
  [291005204, 2114785893, 314007924, 1812752202, 2747156362, 140639374, 4064400764, 2018726209]
#guard (blake3 (claimsBytes [wrapClaimPrefix ++ List.replicate 8 0 ++
    digestWords (wrapStatement single.keys.aggregator [execRootClaim 0 single.identity single.output])])).hex ==
  "0a2d3d77cf461acf736f8b66f2cff7b73daf183575dfd19290f1d8342ee035f4"
-- Any change of key, claim word or wrapper changes the statement.
#guard single.computed != terminalStatement wrapKeyV3 steps600.keys.aggregator
  (execRootClaim 0 single.identity single.output)
#guard single.computed != terminalStatement wrapKeyV3 single.keys.aggregator
  (execRootClaim 1 single.identity single.output)
#guard single.computed != terminalStatement wrapKeyV3 single.keys.aggregator
  (execRootClaim 0 single.identity steps600.output)
#guard single.computed != terminalStatement single.keys.program single.keys.aggregator
  (execRootClaim 0 single.identity single.output)

/-! Encodings and trees, against their definitions in the fork's `aiur_exec_check`. -/

#guard (u64le 0x0102030405060708).data == #[8, 7, 6, 5, 4, 3, 2, 1]
#guard (u64le (2 ^ 64 + 5)).data == (u64le 5).data
#guard fieldWord (-1) == 18446744069414584320
#guard (encWords [-1, 2]).data == (u64le 18446744069414584320 ++ u64le 2).data
#guard (enc16 [-32768, 0, 32767]).map (·.data) == some #[0, 0, 0, 128, 255, 255]
#guard (enc16 [32768]).isNone
#guard (enc16 [-32769]).isNone

def la : Digest := blake3 "a".toUTF8
def lb : Digest := blake3 "b".toUTF8
def lc : Digest := blake3 "c".toUTF8

-- The aggregation's data tree carries an odd node up; `FixedTree` splits ⌊n/2⌋ | ⌈n/2⌉.
#guard execDataRoot [la] == la
#guard execDataRoot [la, lb, lc] == execNode (execNode la lb) lc
#guard execDataRoot [la, lb, lc, la] == execNode (execNode la lb) (execNode lc la)
#guard treeRoot [la, lb, lc] == blake3 (la.bytes ++ (blake3 (lb.bytes ++ lc.bytes)).bytes)
#guard execNode la lb != blake3 (la.bytes ++ lb.bytes)

-- Shapes: counts, and the data each one hashes.
#guard (execData .steps 2 [([1], [2]), ([3], [4])]).toOption ==
  some (2, execNode (blake3 (encWords [1, 2, 2])) (blake3 (encWords [3, 4, 2])))
#guard (execData (.blocks 2) 2 [([1], [2]), ([3], [4])]).toOption ==
  some (1, blake3 (encWords [2, 1, 3, 2, 4]))
#guard (execData (.blocks 2) 2 [([1], [2])]).toOption == none
#guard (execData (.tree [[5]]) 2 [([1], [2])]).toOption ==
  some (1, blake3 (encWords (2 :: (blake3 ((enc16 [5, 1, 2]).getD .empty)).bytes.toList.map fun b => (b.toNat : Int))))
#guard (execData (.tree [[5], [6]]) 2 [([1], [2])]).toOption == none
#guard (execData .steps 2 []).toOption == none

-- The keys `aiur_exec_check` prints.
#guard parseExecKeys s!"[aiur/gpu] noise\nkey: aggregator {single.keys.aggregator.hex} entry 0\nok: x\nkey: program {single.keys.program.hex} entry 0\n" ==
  some single.keys
#guard parseExecKeys s!"key: aggregator {single.keys.aggregator.hex} entry 0\n" == none
#guard parseExecKeys s!"key: aggregator {single.keys.aggregator.hex} entry x\nkey: program {single.keys.program.hex} entry 0\n" == none

end Compression

/-! ### The combined certificate's statement

`.truthmines/combined/cert/full`: the joined root's key has BLAKE3 `79894717…` (`root/root-vk.bin`),
and `root/root-claims.bin` is the 160 bytes below. The terminal statement and public inputs are
the ones the pipeline recorded (`plonk/plonk/summary.json`). -/

section Combined
open Compression Combined

def rootClaimsBin : ByteArray :=
  ["0100000000000000120000000000000001000000000000000000000000000000",
   "b51918f4000000001b0e663b000000008329f5a900000000453db17700000000",
   "97c682d600000000cd0e2ca2000000007e0f432800000000c7e2fe1700000000",
   "a667a62500000000b39caed0000000000211a9ee0000000055bd9aa900000000",
   "4446076300000000d536c6fa0000000075d651c5000000003b097b1900000000"].foldl
    (fun b h => b ++ (hx h).bytes) .empty

def joinedRootKey : Digest := hx "798947179cf837f378820476df87c3149d67b5bf4e229e89c264e2c061620635"

#guard rootClaimsBin.size == 160
#guard (rootClaimOf rootClaimsBin).map (·.take 2) == some [1, 0]
#guard (rootClaimOf rootClaimsBin).map (fun c => (terminalStatement wrapKeyV3 joinedRootKey c).hex) ==
  some "3b9edda783a3ec5ccf1a4f5b0d807d9653386ddb8c6e99cca49de4f69b954def"
#guard (rootClaimOf rootClaimsBin).map (fun c => statementLimbs (terminalStatement wrapKeyV3 joinedRootKey c)) ==
  some (200035833681708382128580466406695214651, 318088332286507901115742028151330256979)
-- Another root key, or the run's own root claim in place of the joined one, changes the statement.
#guard (rootClaimOf rootClaimsBin).map (fun c => (terminalStatement wrapKeyV3 blocks30.keys.aggregator c).hex) !=
  some "3b9edda783a3ec5ccf1a4f5b0d807d9653386ddb8c6e99cca49de4f69b954def"
#guard (terminalStatement wrapKeyV3 joinedRootKey (execRootClaim 0 blocks30.identity blocks30.output)).hex !=
  "3b9edda783a3ec5ccf1a4f5b0d807d9653386ddb8c6e99cca49de4f69b954def"

-- A claims file is read back only when it is exactly `claimsBytes` of canonical words.
#guard decodeClaims (claimsBytes [[1, 2], [3]]) == some [[1, 2], [3]]
#guard decodeClaims (claimsBytes []) == some []
#guard decodeClaims (rootClaimsBin.extract 0 152) == none
#guard decodeClaims (rootClaimsBin ++ u64le 0) == none
#guard decodeClaims (claimsBytes [[goldilocks.toNat]]) == none
#guard decodeClaims (claimsBytes [[goldilocks.toNat - 1]]) == some [[goldilocks.toNat - 1]]
#guard decodeClaims (u64le 1 ++ u64le 3 ++ u64le 7) == none
#guard rootClaimOf (claimsBytes [List.replicate 18 0, List.replicate 18 0]) == none
#guard rootClaimOf (claimsBytes [List.replicate 17 0]) == none

-- `aiur_join_check`'s verdict.
def joinOut : String :=
  "ok: the certificate's root key is ix_aggr's, recompiled from the pinned artifact\n" ++
  s!"ok: the theorem's statement references IxAICore.train ({wrapKeyV3.hex})\n" ++
  s!"ok: the theorem's statement references IxAIAiur.fullConfig ({joinedRootKey.hex})\n" ++
  "PROVED (under the hypotheses below): environment claim 45 holds.\n" ++
  "hypotheses: STARK acceptance implies memo-checker acceptance (Ix's Audit boundary); soundness of ix_aggr; the claim encoding enc, checked here rather than in Lean.\n"

#guard (parseJoinVerdict joinOut).map (·.hypotheses) == some
  ["STARK acceptance implies memo-checker acceptance (Ix's Audit boundary)", "soundness of ix_aggr",
   "the claim encoding enc, checked here rather than in Lean"]
#guard (parseJoinVerdict joinOut).map (·.references) == some
  [("IxAICore.train", wrapKeyV3), ("IxAIAiur.fullConfig", joinedRootKey)]
#guard (parseJoinVerdict joinOut).map (·.oks.length) == some 3
#guard (parseJoinVerdict joinOut).bind (·.assumed) == none
#guard ((parseJoinVerdict (joinOut ++ "assumed: T is an axiom\n")).bind (·.assumed)).isSome
#guard (parseJoinVerdict ((joinOut.splitOn "PROVED").headD "")).isNone
#guard (parseJoinVerdict ((joinOut.splitOn "hypotheses:").headD "")).isNone
#guard parseReference "ok: the theorem's statement references IxAICore.train" == none
#guard parseReference s!"ok: the theorem's statement references IxAICore.train ({wrapKeyV3.hex}" == none

end Combined

end IxAIVerifyTest
