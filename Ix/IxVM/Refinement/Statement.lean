import Ix.IxVM.Refinement.Claim
import Aiur.Generic.Observe
import IxVM
import Aiur.Optimized.Observed
import Aiur.Library.Bytes.Correctness

/-! # The IxVM ↔ IxC refinement statement

Statements
(`def … : Prop`), the observation they read, and the glue to the backend
headline; nothing here proves the refinement. Frozen in
`Ix.IxVM.Refinement.Audit`.

## The object

`IxVM.source` (`IxVM/IxVM/Source.lean`) combines `IxVM.program` with its
certified static tables. The program and all exporters use the same named
function definitions, elaborated once from the DSL in `IxVM/IxVM/Source/`.
Neither the statements nor the exporters run the module frontend or the DSL
elaborators (`Source.world` uses the kernel-computable `Generic.elaborateConst`
for consts). The `ixvm-source` test independently prepares the imported DSL
metadata and compares the full program, static tables, and exported bytecode.
`lake exe ixvm/ixvm-proof-gen --check` checks the derived proof scripts.

`verify_claim(digest: [Field; 8])` reads the claim's bytes on IO channel 0,
checks that their BLAKE3 digest packs to `digest`, decodes the claim and
checks it (`KernelClaim::run_claim`).

## The semantics

The backend headline's Generic form
(`Aiur.Optimized.Physical.Prepared.native_heap_sound_observed`, Track A)
concludes `Generic.SourceSemantics.ObsFn source.world`: the source semantics
of a checked source's world, from the empty heap, with its calls recorded. A `hint` there
(IO reads included: `ixvm.io.info`, `ixvm.io.read`, `ixvm.io.claim`, …)
evaluates to any constant of its type, and two evaluations of one hint need
not agree, so a statement over every derivation holds for every hint and IO
world. The statements range over that observed form
(`Aiur.Generic.Observe`): the derivations of `Generic.SourceSemantics.EvalFn`
with their calls recorded (`EvalFn.observe`, `ObsFn.erase`).

## The statement

`VerifyClaimSoundIn`: for every observed `verify_claim` derivation on `d`,
every claim byte string whose digest packs to `d`, and every authentic view
that covers the claim, the claim holds in the view, **or the derivation
hashed a second preimage** of the claim's bytes or of data the view holds, or a
preimage of the zero padding address (`View.HashedCollision`): a byte string
passed to the program's BLAKE3 (`Blake3::hash`) in that derivation, with the
same pure BLAKE3 hash as the data and different from it (or a held or hashed
preimage of `Ix.HostAdmission.Merkle.padding`). Fooling a reader therefore
requires computing a second preimage of the reader's data or a preimage of zero.

**An existential form is false** in this semantics, so it is not stated:
that some environment, addressed by BLAKE3, is accepted by IxC for
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
* `CircuitSound P` (the main circuit statement): from the circuit compiled
  from the prepared source, over the certified depth pass and a valid ROM of
  at most `2^39` entries, rows the grouped, activated memo checker accepts
  with at most `2^39` rows give an observed
  derivation whose calls the trace's memory carries (`CallsInROM`), so the
  escape's byte string is read off the trace; it gives `P`. No acyclicity is
  assumed. Proved from `SourceSound P` (`circuitSound_of_sourceSound`),
  through Track A's memo-checker soundness and observed headline.
* `CircuitSoundAssuming P`: the same over circuits without the depth pass,
  with the named acyclicity hypothesis `AcyclicDerivation` in place of the
  memo checker. Proved from `SourceSound P` through the observed headline
  (`observedHeadline`, the Phase 2 obligation `ObservedHeadline`, now
  proved).
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

/-- **The byte-stream enum** of the prepared program: the instance symbol of
`Lists::Node<UInt8::U8>` (`UInt8::U8` is an opaque `Field`), the enum
`Blake3::hash`'s parameter points to. The audit checks it against the
prepared program. -/
def byteStreamEnum : String := "${\"name\":\"Lists::Node\",\"types\":[\"field\"]}"

/-- **A byte string the derivation hashed**: the input of one of its calls to
`blake3Hash`, read off the heap at the call as a byte stream of
`byteStreamEnum` (`Aiur.Library.Bytes.RepByteStream`): exactly the bytes
`Blake3::hash` received. -/
def Hashed (calls : List (Call IxVM.F)) (bytes : ByteArray) : Prop :=
  ∃ c ∈ calls, c.name = blake3Hash ∧ ∃ input : Aiur.SourceValue IxVM.F,
    c.args = [input] ∧ Aiur.Library.Bytes.RepByteStream byteStreamEnum c.heap bytes.data.toList input

/-- **A second preimage the derivation hashed, or a preimage of the zero
padding address**: a byte string the derivation hashed (`Hashed`) that has the
same pure BLAKE3 hash as data the view holds (`View.Preimage`), as one of
`extra` (the claim's bytes), or as another byte string the derivation hashed,
and differs from it; or a byte string held by the view or hashed by the
derivation whose pure BLAKE3 hash is `Ix.HostAdmission.Merkle.padding` (the
zero address). -/
def View.HashedCollision (V : View) (extra : List ByteArray) (calls : List (Call IxVM.F)) : Prop :=
  (∃ (x : Address) (held bytes : ByteArray),
    (V.Preimage x held ∨ (held ∈ extra ∧ Address.blake3Pure held = x) ∨
      (Hashed calls held ∧ Address.blake3Pure held = x)) ∧
      Hashed calls bytes ∧ bytes ≠ held ∧ Address.blake3Pure bytes = x) ∨
  ∃ bytes, (V.Preimage Ix.HostAdmission.Merkle.padding bytes ∨ Hashed calls bytes) ∧
    Address.blake3Pure bytes = Ix.HostAdmission.Merkle.padding

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

/-- **The prepared IxVM source** the statements are about. -/
abbrev source : Aiur.Generic.Source IxVM.F := IxVM.source

/-- **Source-level soundness of `verify_claim` for `P`**: every observed
source-semantics derivation of `verify_claim(d)` in the prepared source's
world (any hints, any result, any final heap) gives `P` of its calls and
`d`. -/
def SourceSound (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ (d : Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
    (calls : List (Call IxVM.F)),
    Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim [digestValue d] []
      value heap calls → P calls d

/-- **The main statement**: every observed `verify_claim`
derivation satisfies `IxVMClaimSpecIn` of its calls. -/
def VerifyClaimSoundIn : Prop :=
  SourceSound IxVMClaimSpecIn

/-- **Every derivation**: a source-level statement holds of the observed form
of every `EvalFn` derivation. -/
theorem SourceSound.eval {P : List (Call IxVM.F) → Digest → Prop} (sound : SourceSound P)
    {d : Digest} {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F}
    (evaluated : Aiur.Generic.SourceSemantics.EvalFn IxVM.source.world verifyClaim
      [digestValue d] [] value heap) :
    ∃ calls, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim
      [digestValue d] [] value heap calls ∧ P calls d := by
  obtain ⟨calls, observed⟩ := evaluated.observe
  exact ⟨calls, observed, sound d value heap calls observed⟩

/-- **Every hint and IO world**: a source-level statement holds of every run
of the executable source semantics, whatever its hint provider and fuel. -/
theorem SourceSound.run {P : List (Call IxVM.F) → Digest → Prop} (sound : SourceSound P)
    {d : Digest} {fuel : Nat} {hints : IxVM.source.HintProvider}
    {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F}
    (executed : IxVM.source.run verifyClaim [digestValue d] fuel hints = .ok (value, heap)) :
    ∃ calls, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim
      [digestValue d] [] value heap calls ∧ P calls d :=
  sound.eval (Aiur.Generic.Source.run_spec executed).2

/-! ## Circuit level -/

/-- **Circuit-level soundness for `P`** (the main circuit statement): for the
checked source specialized for `verify_claim`, any optimized compilation and
its physical deduplication, any depth configuration with gap words of at
most 24 bits that the depth pass certifies (`Depth.Certified`, as
`Depth.plan` builds it),
any grouping plan over the depth pass with well-formed activation, any valid
ROM of at most `2^39` entries, any signed message on `verify_claim`'s channel
whose arguments decode to `d`, and any rows, at most `2^39` of them, that the
grouped, activated memo checker accepts for a root outside the depth pass's
names that erases to that message: some observed derivation of
`verify_claim(d)`, whose calls the trace's memory carries (`CallsInROM`), gives
`P` of its calls. No acyclicity is assumed: the depth words make every accepted
memo graph acyclic (Track A, `Depth.plan_checkMemo_sound`).

Both bounds come from the verifiers' batch row bound (`MAX_BATCH_ROWS = 2^39`,
summed over every shard and every active circuit, the memory circuits
included): the rows are rows of the batch, and so is every entry of the ROM,
one per active row of its width's memory circuit. -/
def CircuitSound (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ {id : String → Except String Nat}
    {specialized : Aiur.Generic.Specialized IxVM.source [verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config},
    Aiur.Optimized.Depth.Certified cfg physical.system → cfg.bits ≤ 24 →
    ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
    plan.WellFormedActivation →
    ∀ {rom : Aiur.WidthROM IxVM.F}, rom.Valid → rom.entries.length ≤ 2 ^ 39 →
    ∀ (d : Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
      {result : Aiur.Value IxVM.F},
      Aiur.Circuit.Erasure.Signed compiled.system
          { channel := verifyClaim, args := wires, result := output } →
    ∀ {root : Aiur.Circuit.Message IxVM.F},
      Aiur.Optimized.Depth.erase cfg root =
          Aiur.Circuit.Erasure.message compiled.system
            { channel := verifyClaim, args := wires, result := output } →
      root.channel ∉ cfg.names →
    ∀ {rows : List (Aiur.Circuit.WeightedRow IxVM.F)}, rows.length ≤ 2 ^ 39 →
      plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok () →
      Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues [digestValue d]) →
      Aiur.WireValue.decode specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F) (calls : List (Call IxVM.F)),
        Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim [digestValue d] []
          value heap calls ∧
          Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧ P calls d

/-- **The acyclicity hypothesis** of the assumption-based form: the finite
derivation of the root over the activated grouped circuits, which the
assumption-based headline assumes (`derived`). A STARK proof gives rows with
balanced lookups, a memo table that may be cyclic; `CircuitSound` replaces
this hypothesis with the memo checker over the depth pass. -/
def AcyclicDerivation {F : Type} [Field F] [DecidableEq F] {s : Aiur.Generic.Source F}
    {entries : List String} {specialized : Aiur.Generic.Specialized s entries}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    {physical : Aiur.Optimized.Physical.Prepared compiled.artifact}
    {id : String → Except String Nat} (plan : Aiur.Optimized.Grouping.Plan physical.system id)
    (rom : Aiur.WidthROM F) (root : Aiur.Circuit.Message F) : Prop :=
  plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom)
    (Aiur.Circuit.Erasure.message compiled.system root)

/-- **Circuit-level soundness for `P`, assuming acyclicity** (the secondary
form, for circuits without the depth pass): as `CircuitSound`, over a grouping
plan of the physical circuits themselves, with `AcyclicDerivation` of the root
in place of the memo checker and the row bound. -/
def CircuitSoundAssuming (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ {id : String → Except String Nat}
    {specialized : Aiur.Generic.Specialized IxVM.source [verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id),
    plan.WellFormedActivation →
    ∀ {rom : Aiur.WidthROM IxVM.F}, rom.Valid →
    ∀ (d : Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
      {result : Aiur.Value IxVM.F},
      Aiur.Circuit.Erasure.Signed compiled.system
          { channel := verifyClaim, args := wires, result := output } →
      AcyclicDerivation compiled plan rom { channel := verifyClaim, args := wires, result := output } →
      Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues [digestValue d]) →
      Aiur.WireValue.decode specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F) (calls : List (Call IxVM.F)),
        Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim [digestValue d] []
          value heap calls ∧
          Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧ P calls d

/-- **The main statement at the circuit.** -/
def VerifyClaimCircuitSoundIn : Prop :=
  CircuitSound IxVMClaimSpecIn

/-- **The main statement at the circuit, assuming acyclicity.** -/
def VerifyClaimCircuitSoundInAssuming : Prop :=
  CircuitSoundAssuming IxVMClaimSpecIn

/-- **The observed headline, assuming acyclicity**, for every checked source:
the Generic headline `grouped_activated_native_heap_sound`, concluding an
*observed* derivation whose calls the trace's memory carries, beside the
result's representation. Phase 2 named it as the backend obligation; Track A
proved it (`observedHeadline`). -/
def ObservedHeadline : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}
    {s : Aiur.Generic.Source F} {entries : List String}
    {specialized : Aiur.Generic.Specialized s entries}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id),
    plan.WellFormedActivation →
    ∀ {name : String}, name ∈ entries →
    ∀ {rom : Aiur.WidthROM F}, rom.Valid →
    ∀ {args : List (Aiur.SourceValue F)} {result : Aiur.Value F} {wires : List (Aiur.WireValue F)}
      {output : Aiur.WireValue F},
      Aiur.Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
      AcyclicDerivation compiled plan rom { channel := name, args := wires, result := output } →
      Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues args) →
      Aiur.WireValue.decode specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue F) (heap : Aiur.Heap F) (calls : List (Call F)),
        Aiur.Generic.SourceSemantics.ObsFn s.world name args [] value heap calls ∧
          Aiur.Represents (compiled.traceROM rom) heap value result ∧
          Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls

/-- **The observed headline holds**: Track A's
`Physical.Prepared.grouped_activated_native_heap_sound_observed`. -/
theorem observedHeadline : ObservedHeadline := by
  intro F _ _ id s entries specialized compiled physical plan activated name entry rom valid args
    result wires output signed derived arguments decoded
  exact physical.grouped_activated_native_heap_sound_observed compiled plan activated entry valid
    signed derived arguments decoded

/-- **The circuit statement follows from the source statement** through Track
A's generic-level observed headline over the depth pass
(`Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`:
memo-checker soundness, `Depth.plan_checkMemo_sound`, with Goldilocks'
characteristic for 24-bit words). -/
theorem circuitSound_of_sourceSound {P : List (Call IxVM.F) → Digest → Prop}
    (sound : SourceSound P) : CircuitSound P := by
  intro id specialized compiled physical cfg certified bits plan activated rom valid _ d wires output
    result signed root rooted outside rows bound checked arguments decoded
  obtain ⟨value, heap, calls, observed, -, carried⟩ :=
    physical.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated (List.mem_singleton.mpr rfl) valid signed rooted outside bound checked
      arguments decoded
  exact ⟨value, heap, calls, observed, carried, sound d value heap calls observed⟩

/-- **The assumption-based circuit statement follows from the source
statement** through `observedHeadline`. -/
theorem circuitSoundAssuming_of_sourceSound {P : List (Call IxVM.F) → Digest → Prop}
    (sound : SourceSound P) : CircuitSoundAssuming P := by
  intro id specialized compiled physical plan activated rom valid d wires output result signed
    derived arguments decoded
  obtain ⟨value, heap, calls, observed, -, carried⟩ :=
    observedHeadline compiled physical plan activated (List.mem_singleton.mpr rfl) valid signed
      derived arguments decoded
  exact ⟨value, heap, calls, observed, carried, sound d value heap calls observed⟩

theorem verifyClaimCircuitSoundIn_of_soundIn (sound : VerifyClaimSoundIn) :
    VerifyClaimCircuitSoundIn :=
  circuitSound_of_sourceSound sound

theorem verifyClaimCircuitSoundInAssuming_of_soundIn (sound : VerifyClaimSoundIn) :
    VerifyClaimCircuitSoundInAssuming :=
  circuitSoundAssuming_of_sourceSound sound

end IxVM.Refinement
