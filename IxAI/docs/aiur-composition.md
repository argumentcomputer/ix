# One certificate for a training run: Aiur execution plus IxVM

## Problem

Certifying `train spec config = W` by kernel evaluation inside IxVM re-runs every SGD step as
Lean term reduction: unfolding `Model.step`, `List.zipWith`, `Fx.dot`, `Int` arithmetic, recursor
matches and substitution, each reduction a row of the IxVM trace. For the full triage model
(600 steps, 16 hidden units) that is ~6 GPU-hours spread over 400 shards. The dedicated Aiur
circuit `Fixed::step` proves the same 600 steps in 32 s. The gap is interpretation overhead, and
it grows with the model, so kernel evaluation does not scale past toy sizes.

## Design

Keep IxVM for what is about types and proofs (spec, safety theorems for all weights, card,
chain lemmas), and prove the computation with the dedicated circuit, joined by a one-time
refinement theorem.

1. **Refinement theorem** (Lean, checked once by IxVM as an ordinary `check` claim):

   ```
   theorem Fixed.train_refines :
     ∀ args value heap calls,
       ObsFn Fixed.source.world `Fixed.train (encode config data) [] value heap calls →
       decode value = train spec config
   ```

   Hints are universally quantified in `ObsFn`, so the proof rests on the circuit's checks.
   The arithmetic core is already proved in `ix/aiur/FixedSoundness.lean`
   (`shr8_sound`, `sign_offset_sound`, `zero_test_sound`). The rest is inversion lemmas per
   function, as `IxVMRefinement/` does for IxVM (generalise `IxVM/IxVM/ObsGen.lean`, which is
   hard-coded to `IxVM.program`), plus value-bound bookkeeping (`|s| < 2^55`) and induction over
   the step loop. Estimate: 1–3k lines, mostly generated.

2. **One execution for training**: `Fixed::train` runs the whole schedule, giving one STARK
   proof with public IO `(encode config data, encode W)`, instead of 600 step proofs.

3. **Aggregation protocol extension, generic in the program** (a one-time Ix change):
   - a third `ChildKind`, `aiur`, alongside `ixvm | aggr` (`Ix/Aggr/Protocol.lean:38`,
     `crates/aggregate-controller/src/protocol.rs:3`), whose child is verified under a verifying key
     supplied as data rather than one fixed in `allowedBlob` (`Ix/Aggr/Protocol.lean:17-28`);
   - a claim kind `aiurExec (program vk : Address) (input output : Bytes)` in `Ix/Claim.lean`,
     binding the program's digest, the key digest and the IO.

   The root then states: the environment's theorems hold, and program `P` executed on
   `(config, data)` to `W`. With `Fixed.train_refines` (a theorem about `P`) in the environment,
   a verifier concludes `train spec config = W`.

   Because the key is data, new circuits, models and fixes to `Fixed` change neither IxVM nor
   `ix_aggr`: existing typechecking proofs and the compression keys stay valid.

   **Key-to-program binding.** The claim must not let a proof under some key `V` stand for program
   `P` unless `V = keygen P`. Key generation is deterministic, so a verifier recomputes `V` from `P`
   once per program and caches it, which puts keygen in the trusted toolchain alongside the IxVM key.
   A later strengthening proves `V = keygen P` inside the certificate.

## Trust

`Aiur.Optimized.Physical.Prepared.native_heap_sound_observed` (STARK acceptance implies source
semantics, `Aiur/Aiur/Audit.lean:1732`) is a property of the proof system, trusted at the same
level IxVM's own soundness is today; it is not re-checked inside each certificate. The trusted
base grows by the `aiurExec` claim encoding and deterministic key generation, not by the model.

## Alternatives rejected

- **Circuits called by lookup from IxVM** (a per-model role, or a generic fixed-point library
  justified by checked refinement theorems): one tight proof, but Aiur programs are static, so every
  new or changed circuit changes IxVM's digest and verifying key and invalidates all typechecking
  proofs and compression keys. Training must evolve without touching the typechecker.
- **Two separate certificates** (IxVM for the theorems, a separately compressed Aiur proof for
  training): works today with no protocol change, but the verifier must check two proofs and
  match their statements by hand; not one succinct certificate.

## Order of work

1. `Fixed.step_refines`, then `Fixed.train` and `Fixed.train_refines` (Lean only; small gated
   elaborations).
2. `aiurExec` claim and key-as-data `ChildKind.aiur` on an Ix branch, with a test aggregating one IxVM shard
   and one `Fixed::train` proof.
3. Full model: one training proof plus the environment shards, aggregated, then PLONK.
