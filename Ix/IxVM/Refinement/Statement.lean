import Ix.IxVM.Refinement.Claim
import IxVM.Program
import Aiur.Optimized.EndToEnd

/-! # The IxVM ↔ IxC refinement statement

Track B, Phase 2 (`plans/ixvm-certification-gap.md`). Statements only
(`def … : Prop`); nothing here proves them. Frozen in
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
semantics `Generic.SourceSemantics.EvalFn` of the prepared program's world,
from the empty heap. A `hint` there (IO reads included: `ixvm.io.info`,
`ixvm.io.read`, `ixvm.io.claim`, …) evaluates to **any** constant of its
type, and two evaluations of one hint need not agree. So a statement over
every `EvalFn` derivation holds for every hint and IO world: every
executable hint provider's run is such a derivation
(`Modules.Prepared.run_heap_spec`; see `SourceSound.run`).

## The statements

* `SourceSound P`: every `verify_claim` derivation on `d` gives `P d`. The
  obligation Phases 3 and 4 discharge.
* `CircuitSound P`: the same from the circuit, under the headline's
  hypotheses and the named acyclicity hypothesis `AcyclicDerivation`
  (Track A). `circuitSound_of_sourceSound` composes the two with the headline.
* `P` is `IxVMClaimSpec` (decision D2's existential form) or
  `IxVMClaimSpecIn` (the collision corollary, per view).
-/

namespace IxVM.Refinement

open Ix (Claim)

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

/-! ## What acceptance should mean -/

/-- **`verify_claim` succeeding on `d`, in decision D2's form**: some byte
string whose pure BLAKE3 digest packs to `d` decodes (`Ix.Claim.de`) to a
claim, and that claim holds in some authentic view (`Ix.Claim.Holds`). -/
def IxVMClaimSpec (d : Digest) : Prop :=
  ∃ (bytes : ByteArray) (c : Claim),
    packDigest (Address.blake3Pure bytes) = d ∧ Claim.de bytes = .ok c ∧ c.Holds

/-- **The collision corollary, per view**: for every byte string whose digest
packs to `d` and decodes to a claim `c`, and every authentic view that covers
`c`, the claim holds in the view, or there is a second preimage of the
claim's bytes or of data the view holds (`View.Collision`). -/
def IxVMClaimSpecIn (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim) (V : View),
    Claim.de bytes = .ok c → packDigest (Address.blake3Pure bytes) = d →
      V.Authentic → c.Covers V → c.HoldsIn V ∨ V.Collision [bytes]

/-! ## Source level -/

/-- **Source-level soundness of `verify_claim` for `P`**: for the IxVM
program prepared for `verify_claim`, every source-semantics derivation of
`verify_claim(d)` (any hints, any result, any final heap) gives `P d`. -/
def SourceSound (P : Digest → Prop) : Prop :=
  ∀ prepared : Aiur.Modules.Prepared IxVM.program,
    Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared →
    ∀ (d : Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F),
      prepared.EvalFn verifyClaim [digestValue d] value heap → P d

/-- **The main statement (D2)**: every `verify_claim` derivation on `d`
satisfies `IxVMClaimSpec d`. -/
def VerifyClaimSound : Prop :=
  SourceSound IxVMClaimSpec

/-- **The collision corollary**: every `verify_claim` derivation on `d`
satisfies `IxVMClaimSpecIn d`. -/
def VerifyClaimSoundIn : Prop :=
  SourceSound IxVMClaimSpecIn

/-- **Every hint and IO world**: a source-level statement holds of every run
of the executable source semantics, whatever its hint provider and fuel. -/
theorem SourceSound.run {P : Digest → Prop} (sound : SourceSound P)
    {prepared : Aiur.Modules.Prepared IxVM.program}
    (prepared_eq : Aiur.Modules.prepare IxVM.program [verifyClaim] = .ok prepared)
    {d : Digest} {fuel : Nat} {hints : prepared.environment.source.HintProvider}
    {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F}
    (executed : prepared.run verifyClaim [digestValue d] fuel hints = .ok (value, heap)) : P d :=
  sound prepared prepared_eq d value heap (Aiur.Modules.Prepared.run_heap_spec executed)

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

/-- **Circuit-level soundness of `verify_claim` for `P`**: for the IxVM
program prepared for `verify_claim`, any optimized compilation of it, its
physical deduplication and any grouping plan with well-formed activation,
any valid ROM, and any signed root message on `verify_claim`'s channel whose
arguments decode to `d`: if `AcyclicDerivation` holds of the root, then
`P d`. These are the headline's hypotheses, with its `derived` named. -/
def CircuitSound (P : Digest → Prop) : Prop :=
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
        P d

/-- **The main statement at the circuit**: D2's form, under the acyclicity
hypothesis. -/
def VerifyClaimCircuitSound : Prop :=
  CircuitSound IxVMClaimSpec

/-- **The collision corollary at the circuit**, under the acyclicity
hypothesis. -/
def VerifyClaimCircuitSoundIn : Prop :=
  CircuitSound IxVMClaimSpecIn

/-- **The statements compose with the backend headline**: source-level
soundness gives circuit-level soundness through
`Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound`. -/
theorem circuitSound_of_sourceSound {P : Digest → Prop} (sound : SourceSound P) :
    CircuitSound P := by
  intro prepared prepared_eq id compiled physical plan activated entry selected rom valid d
    wires output result signed derived arguments decoded
  obtain ⟨value, heap, evaluated, -⟩ :=
    Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound compiled physical plan activated
      selected valid signed derived arguments decoded
  exact sound prepared prepared_eq d value heap evaluated

theorem verifyClaimCircuitSound_of_sound (sound : VerifyClaimSound) : VerifyClaimCircuitSound :=
  circuitSound_of_sourceSound sound

theorem verifyClaimCircuitSoundIn_of_soundIn (sound : VerifyClaimSoundIn) :
    VerifyClaimCircuitSoundIn :=
  circuitSound_of_sourceSound sound

end IxVM.Refinement
