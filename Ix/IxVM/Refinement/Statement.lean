import Ix.IxVM.Refinement.Claim
import Ix.IxVM.Refinement.Observe
import IxVM.Program
import Aiur.Optimized.EndToEnd
import Aiur.Library.Bytes.Correctness

/-! # The IxVM ↔ IxC refinement statement

Track B, Phase 2 (`plans/ixvm-certification-gap.md`). Statements
(`def … : Prop`), the observation they read, and the glue to the backend
headline; nothing here proves the refinement. Frozen in
`Ix.IxVM.Refinement.Audit`.

## The object

`IxVM.program` (`IxVM/IxVM/Program.lean`), prepared for the entry
`IxVM::verify_claim` alone (`Aiur.Modules.prepare IxVM.program [verifyClaim]`,
the preparation `ixvm check-claim`, `export-claim` and `export-claim-trace`
make). `verify_claim(digest: [Field; 8])` reads the claim's bytes on IO
channel 0, checks that their BLAKE3 digest packs to `digest`, decodes the
claim and checks it (`KernelClaim::run_claim`).

## The semantics

The backend headline (`Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound`,
frozen in `Aiur.Audit`) concludes `Modules.Prepared.EvalFn`: the source
semantics of the prepared world, from the empty heap. A `hint` there (IO
reads included: `ixvm.io.info`, `ixvm.io.read`, `ixvm.io.claim`, …)
evaluates to any constant of its type, and two evaluations of one hint need
not agree, so a statement over every derivation holds for every hint and IO
world. The statements here range over its observed form,
`Modules.Prepared.ObsFn` (`Ix.IxVM.Refinement.Observe`): the same derivations
with their calls recorded (`EvalFn.observe`, `ObsFn.erase`).

## The statement (decision D2, revised by the owner, 2026-11-08)

`VerifyClaimSoundIn`: for every observed `verify_claim` derivation on `d`,
every claim byte string whose digest packs to `d`, and every authentic view
that covers the claim, the claim holds in the view, **or the derivation
hashed a second preimage** of the claim's bytes or of data the view holds
(`View.HashedCollision`): a byte string passed to the program's BLAKE3
(`Blake3::hash`) in that derivation, with the same pure BLAKE3 hash as the
data and different from it. Fooling a reader therefore requires computing a
second preimage of the reader's data.

**D2's existential form is false** in this semantics, so it is not stated.
It said that some environment, addressed by BLAKE3, is accepted by IxC for
the claim. IxVM loads a record each time it needs one
(`Ingress::get_ci` → `load_verified_constant`, with no per-run cache), and two
loads of one address may return different bytes that both pass the BLAKE3
check. Such pairs exist by counting, including two valid records
`def x : Nat := n` and `def x : Nat := m` with `n ≠ m` and one address. A
derivation that unfolds `x` to `n` in one place and to `m` in another accepts
`t : x = n ∧ x = m`, which no consistent environment makes IxC accept. A
disjunct "or some BLAKE3 collision exists" would not help: one exists by
counting, so the disjunct says nothing. The escape here is a byte string
the derivation itself hashed.

## The levels

* `SourceSound P`: every observed `verify_claim` derivation gives `P`. The
  obligation Phases 3 and 4 discharge.
* `CircuitSoundUntied P`: from the circuit, under the headline's hypotheses
  and the named acyclicity hypothesis `AcyclicDerivation` (Track A), some
  observed derivation gives `P`. Proved from `SourceSound P`
  (`circuitSoundUntied_of_sourceSound`). Its calls are not tied to the trace.
* `CircuitSound P`: as above, with every observed call's arguments
  represented in the trace's ROM (`CallsInROM`), so the escape's byte string
  is read off the trace. It needs the strengthened headline
  `ObservedHeadline`, a named obligation (`circuitSound_of_sourceSound`).
-/

namespace IxVM.Refinement

open Ix (Claim)
open Aiur.Generic.SourceSemantics (Call)

/-! ## Public input -/

/-- `verify_claim`'s public input: the claim digest as eight field elements. -/
abbrev Digest := Fin 8 → IxVM.F

/-- **A digest as `verify_claim`'s public input**: eight words, word `i` the
little-endian value of bytes `4i … 4i+3` (`Blake3::pack_digest` of the
digest's words; `IxVM.ClaimHarness.packedDigestKey` on the host). Each word
is below `2^32`, so packing is injective on 32-byte digests. -/
def packDigest (a : Address) : Digest := fun i =>
  let byte (k : Nat) : Nat := (a.hash.data.getD k 0).toNat
  ((byte (4 * i.val) + 256 * byte (4 * i.val + 1) + 65536 * byte (4 * i.val + 2) +
    16777216 * byte (4 * i.val + 3) : Nat) : IxVM.F)

/-- The source value of a `[Field; 8]` argument. -/
def digestValue (d : Digest) : Aiur.SourceValue IxVM.F :=
  .tuple (List.ofFn fun i => .field (d i))

/-- The entry the statements are about. -/
def verifyClaim : String := "IxVM::verify_claim"

/-! ## The escape: what the derivation hashed -/

/-- **The program's BLAKE3**: `Blake3::hash(input: ByteStream)`. Every hash
the program computes is a call to it: `Blake3::verify_bytes_against`
(records, blobs, the role table), `Blake3::bytes_to_addr` (assumption-tree
nodes) and `KernelClaim::run_claim` (the claim's bytes). -/
def blake3Hash : String := "Blake3::hash"

/-- **A byte string the derivation hashed**: the input of one of its calls to
`blake3Hash`, read off the heap at the call as a byte stream
(`Aiur.Library.Bytes.RepByteStream`). -/
def Hashed (calls : List (Call IxVM.F)) (bytes : ByteArray) : Prop :=
  ∃ c ∈ calls, c.name = blake3Hash ∧ ∃ (input : Aiur.SourceValue IxVM.F) (enumName : String),
    c.args = [input] ∧ Aiur.Library.Bytes.RepByteStream enumName c.heap bytes.data.toList input

/-- **A second preimage the derivation hashed**: a byte string the derivation
hashed (`Hashed`) that has the same pure BLAKE3 hash as data the view holds
(`View.Preimage`) or as one of `extra` (the claim's bytes), and differs from
it. -/
def View.HashedCollision (V : View) (extra : List ByteArray) (calls : List (Call IxVM.F)) : Prop :=
  ∃ (x : Address) (held bytes : ByteArray),
    (V.Preimage x held ∨ (held ∈ extra ∧ Address.blake3Pure held = x)) ∧
      Hashed calls bytes ∧ bytes ≠ held ∧ Address.blake3Pure bytes = x

/-! ## What acceptance means -/

/-- **`verify_claim` accepting `d`, with the calls `calls`, for every reader**:
for every byte string whose pure BLAKE3 digest packs to `d` and that decodes
(`Ix.Claim.de`) to a claim `c`, and every authentic view that covers `c`: the
claim holds in the view, or the calls hashed a second preimage of those bytes
or of the view's data. -/
def IxVMClaimSpecIn (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim) (V : View),
    Claim.de bytes = .ok c → packDigest (Address.blake3Pure bytes) = d →
      V.Authentic → c.Covers V → c.HoldsIn V ∨ V.HashedCollision [bytes] calls

/-! ## Source level -/

/-- **Source-level soundness of `verify_claim` for `P`**: for the IxVM
program prepared for `verify_claim`, every observed source-semantics
derivation of `verify_claim(d)` (any hints, any result, any final heap) gives
`P` of its calls and `d`. -/
def SourceSound (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ prepared : Aiur.Modules.Prepared IxVM.program,
    Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared →
    ∀ (d : Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
      (calls : List (Call IxVM.F)),
      prepared.ObsFn verifyClaim [digestValue d] value heap calls → P calls d

/-- **The main statement** (D2 as revised): every observed `verify_claim`
derivation satisfies `IxVMClaimSpecIn` of its calls. -/
def VerifyClaimSoundIn : Prop :=
  SourceSound IxVMClaimSpecIn

/-- **Every derivation**: a source-level statement holds of the observed form
of every `EvalFn` derivation. -/
theorem SourceSound.eval {P : List (Call IxVM.F) → Digest → Prop} (sound : SourceSound P)
    {prepared : Aiur.Modules.Prepared IxVM.program}
    (prepared_eq : Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared)
    {d : Digest} {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F}
    (evaluated : prepared.EvalFn verifyClaim [digestValue d] value heap) :
    ∃ calls, prepared.ObsFn verifyClaim [digestValue d] value heap calls ∧ P calls d := by
  obtain ⟨calls, observed⟩ := Aiur.Modules.Prepared.EvalFn.observe evaluated
  exact ⟨calls, observed, sound prepared prepared_eq d value heap calls observed⟩

/-- **Every hint and IO world**: a source-level statement holds of every run
of the executable source semantics, whatever its hint provider and fuel. -/
theorem SourceSound.run {P : List (Call IxVM.F) → Digest → Prop} (sound : SourceSound P)
    {prepared : Aiur.Modules.Prepared IxVM.program}
    (prepared_eq : Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared)
    {d : Digest} {fuel : Nat} {hints : prepared.environment.source.HintProvider}
    {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F}
    (executed : prepared.run verifyClaim [digestValue d] fuel hints = .ok (value, heap)) :
    ∃ calls, prepared.ObsFn verifyClaim [digestValue d] value heap calls ∧ P calls d :=
  sound.eval prepared_eq (Aiur.Modules.Prepared.run_heap_spec executed)

/-! ## Circuit level -/

/-- **The acyclicity hypothesis** (Track A, `plans/acyclicity-options.md`
§7.11). A STARK proof gives rows with balanced lookups, a memo table that may
be cyclic (`Aiur.Circuit.MemoDerivation`); acyclicity of that table gives
this finite derivation over the activated grouped circuits, which is what
the backend headline assumes (`derived`). Track A's depth columns and rank
lemma are to discharge it; until then it is a hypothesis. -/
def AcyclicDerivation {F : Type} [Field F] [DecidableEq F] {program : Aiur.Modules.Program F}
    {prepared : Aiur.Modules.Prepared program} (compiled : Aiur.Optimized.ModulesArtifact prepared)
    {physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact}
    {id : String → Except String Nat} (plan : Aiur.Optimized.Grouping.Plan physical.system id)
    (rom : Aiur.WidthROM F) (root : Aiur.Circuit.Message F) : Prop :=
  plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom)
    (Aiur.Circuit.Erasure.message compiled.circuit.system root)

/-- **The trace's memory**, decoded: the ROM the headline represents values
in. -/
abbrev traceROM {F : Type} [Field F] [DecidableEq F] {program : Aiur.Modules.Program F}
    {prepared : Aiur.Modules.Prepared program} (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (rom : Aiur.WidthROM F) : Aiur.ROM F :=
  Aiur.WireROM.decode compiled.specialized.program.enums
    (Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom)

/-- **The trace carries the calls**: every argument of every call is
represented in the trace's memory (`Aiur.Represents`), so a byte stream a
call received is read off the memory table's rows. -/
def CallsInROM {F : Type} (rom : Aiur.ROM F) (calls : List (Call F)) : Prop :=
  ∀ c ∈ calls, ∀ v ∈ c.args, ∃ w, Aiur.Represents rom c.heap v w

/-- **Circuit-level soundness for `P`, not tied to the trace**: for the IxVM
program prepared for `verify_claim`, any optimized compilation, its physical
deduplication and any grouping plan with well-formed activation, any valid
ROM, and any signed root message on `verify_claim`'s channel whose arguments
decode to `d`: if `AcyclicDerivation` holds of the root, then some observed
derivation of `verify_claim(d)` gives `P` of its calls. These are the
headline's hypotheses, with its `derived` named. -/
def CircuitSoundUntied (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ prepared : Aiur.Modules.Prepared IxVM.program,
    Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared →
    ∀ {id : String → Except String Nat} (compiled : Aiur.Optimized.ModulesArtifact prepared)
      (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
      (plan : Aiur.Optimized.Grouping.Plan physical.system id),
      plan.WellFormedActivation →
      ∀ {entry : Aiur.Modules.Selection IxVM.program prepared.environment.assembly.instances},
        prepared.find? verifyClaim = some entry →
      ∀ {rom : Aiur.WidthROM IxVM.F}, rom.Valid →
      ∀ (d : Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
        {result : Aiur.Value IxVM.F},
        Aiur.Circuit.Erasure.Signed compiled.circuit.system
            { channel := entry.resolved.name, args := wires, result := output } →
        AcyclicDerivation compiled plan rom
            { channel := entry.resolved.name, args := wires, result := output } →
        Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues [digestValue d]) →
        Aiur.WireValue.decode compiled.specialized.program.enums output = some result →
        ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F) (calls : List (Call IxVM.F)),
          prepared.ObsFn verifyClaim [digestValue d] value heap calls ∧ P calls d

/-- **Circuit-level soundness for `P`, tied to the trace**: as
`CircuitSoundUntied`, and the observed derivation's calls are carried by the
trace's memory (`CallsInROM`). -/
def CircuitSound (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ prepared : Aiur.Modules.Prepared IxVM.program,
    Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared →
    ∀ {id : String → Except String Nat} (compiled : Aiur.Optimized.ModulesArtifact prepared)
      (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
      (plan : Aiur.Optimized.Grouping.Plan physical.system id),
      plan.WellFormedActivation →
      ∀ {entry : Aiur.Modules.Selection IxVM.program prepared.environment.assembly.instances},
        prepared.find? verifyClaim = some entry →
      ∀ {rom : Aiur.WidthROM IxVM.F}, rom.Valid →
      ∀ (d : Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
        {result : Aiur.Value IxVM.F},
        Aiur.Circuit.Erasure.Signed compiled.circuit.system
            { channel := entry.resolved.name, args := wires, result := output } →
        AcyclicDerivation compiled plan rom
            { channel := entry.resolved.name, args := wires, result := output } →
        Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues [digestValue d]) →
        Aiur.WireValue.decode compiled.specialized.program.enums output = some result →
        ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F) (calls : List (Call IxVM.F)),
          prepared.ObsFn verifyClaim [digestValue d] value heap calls ∧
            CallsInROM (traceROM compiled rom) calls ∧ P calls d

/-- **The main statement at the circuit, tied to the trace.** -/
def VerifyClaimCircuitSoundIn : Prop :=
  CircuitSound IxVMClaimSpecIn

/-- **The main statement at the circuit, not tied to the trace.** -/
def VerifyClaimCircuitSoundInUntied : Prop :=
  CircuitSoundUntied IxVMClaimSpecIn

/-- **The backend obligation (named, not proved)**: the headline
`grouped_activated_heap_sound`, for every program, concluding an *observed*
derivation whose calls the trace's memory carries, beside the result's
representation it concludes today. Today's headline gives only `EvalFn`,
with no tie between the derivation's calls and the rows. -/
def ObservedHeadline : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}
    {program : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared program}
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id),
    plan.WellFormedActivation →
    ∀ {external : String}
      {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
    ∀ {rom : Aiur.WidthROM F}, rom.Valid →
    ∀ {args : List (Aiur.SourceValue F)} {result : Aiur.Value F} {wires : List (Aiur.WireValue F)}
      {output : Aiur.WireValue F},
      Aiur.Circuit.Erasure.Signed compiled.circuit.system
          { channel := entry.resolved.name, args := wires, result := output } →
      AcyclicDerivation compiled plan rom
          { channel := entry.resolved.name, args := wires, result := output } →
      Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args) →
      Aiur.WireValue.decode compiled.specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue F) (heap : Aiur.Heap F) (calls : List (Call F)),
        prepared.ObsFn external args value heap calls ∧
          Aiur.Represents (traceROM compiled rom) heap value result ∧
          CallsInROM (traceROM compiled rom) calls

/-- **The untied circuit statement follows from the source statement**
through today's headline and `EvalFn.observe`. -/
theorem circuitSoundUntied_of_sourceSound {P : List (Call IxVM.F) → Digest → Prop}
    (sound : SourceSound P) : CircuitSoundUntied P := by
  intro prepared prepared_eq id compiled physical plan activated entry selected rom valid d
    wires output result signed derived arguments decoded
  obtain ⟨value, heap, evaluated, -⟩ :=
    Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound compiled physical plan activated
      selected valid signed derived arguments decoded
  obtain ⟨calls, observed, holds⟩ := sound.eval prepared_eq evaluated
  exact ⟨value, heap, calls, observed, holds⟩

/-- **The tied circuit statement follows from the source statement and the
backend obligation.** -/
theorem circuitSound_of_sourceSound {P : List (Call IxVM.F) → Digest → Prop}
    (headline : ObservedHeadline) (sound : SourceSound P) : CircuitSound P := by
  intro prepared prepared_eq id compiled physical plan activated entry selected rom valid d
    wires output result signed derived arguments decoded
  obtain ⟨value, heap, calls, observed, -, carried⟩ :=
    headline compiled physical plan activated selected valid signed derived arguments decoded
  exact ⟨value, heap, calls, observed, carried,
    sound prepared prepared_eq d value heap calls observed⟩

theorem verifyClaimCircuitSoundInUntied_of_soundIn (sound : VerifyClaimSoundIn) :
    VerifyClaimCircuitSoundInUntied :=
  circuitSoundUntied_of_sourceSound sound

theorem verifyClaimCircuitSoundIn_of_soundIn (headline : ObservedHeadline)
    (sound : VerifyClaimSoundIn) : VerifyClaimCircuitSoundIn :=
  circuitSound_of_sourceSound headline sound

end IxVM.Refinement
