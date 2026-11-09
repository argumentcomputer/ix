# Kernel-Bridge Adequacy Model (`Models/KernelBridge`)

This standalone Lake package proves Stage C adequacy for closed first-order `Nat` programs,
connecting `IxCC`'s source evaluator (`IxCC.Src.eval` / `IxCC.Src.run`), recheck pipeline
(`IxCC.Recheck.run` / `IxCC.Recheck.sound_nat`), and byte-level claim verifier
(`IxCC.CompileClaim.verifyBytes` / `IxCC.CompileClaim.verifyBytes_immortal_sound`)
to `IxCK`'s certified kernel reduction (`Ix.Kernel.Rules.Red`) and set-theoretic
denotation (`Ix.Kernel.Denotes` in `Model.ofEnvModelM mp` obtained from
`Ix.Kernel.Cached.checkDecls_sound`).

It lives outside the production `IxCC` import root so `IxCC` never imports `IxCK`'s
model tier directly.

## Structure

- [`IxKernelBridge/NatBridge.lean`](IxKernelBridge/NatBridge.lean):
  - **Layer 1 (`srcRun_to_red`)**: Simultaneous de Bruijn substitution (`subst`) commuting
    with `Expr.instantiate1`, kernel environment basis predicate `natBasisStored`,
    derived multi-step `Red` lemmas for δ-unfolding (`red_delta_const`), `Nat.rec`
    ι-reduction (`red_natRec_zero`, `red_natRec_succ`), and `Nat.casesOn` reduction
    (`red_natCasesOn_zero`, `red_natCasesOn_succ`), relational term/head/constant/value
    translation (`RelTerm`, `RelHead`, `RelConstStep`, `RelVal`, `RelSlot`, `RelSlots`),
    and fuel-strong simulation (`sim_all`: `eval_sim`, `apply_sim`, `force_sim`, `fire_sim`,
    `headValue_sim`, `evalConst_sim`) culminating in `srcRun_to_red`.
  - **Layer 2 (`red_to_denotes_nat`, `infer_red_to_denotes_nat`)**: Connects closed
    `Red env 0 e w` with `rawNatLit? w = some out` to set-theoretic denotation
    `Denotes (Model.ofEnvModelM mp).cval env φ ρ` via `RulesInputs.ofSem mp φ`,
    `red_sound`, `infer_sound`, `Denotes_of_denoteMeta`, and `Denotes.natLit`.
  - **Layer 3 (`srcRun_to_denotes_nat`, `srcRun_infer_to_denotes_nat`,
    `checkDecls_srcRun_denotes_nat`, `checkDecls_recheck_x86_denotes_nat`,
    `checkDecls_verifyBytes_immortal_denotes_nat`)**: End-to-end capstone theorems
    composing `Ix.Kernel.Cached.checkDecls_sound`, `srcRun_to_red`, `red_to_denotes_nat`,
    `IxCC.Recheck.sound_nat`, and `IxCC.CompileClaim.verifyBytes_immortal_sound`.
- [`IxKernelBridge/Audit.lean`](IxKernelBridge/Audit.lean):
  - Direct constant-closure dependency audit confirming that `srcRun_to_red`,
    `red_to_denotes_nat`, `infer_red_to_denotes_nat`, `srcRun_to_denotes_nat`,
    `srcRun_infer_to_denotes_nat`, `checkDecls_srcRun_denotes_nat`, and
    `checkDecls_recheck_x86_denotes_nat` depend only on `[propext, Classical.choice, Quot.sound]`,
    plus `#guard_msgs in #print axioms` fences for all Layer 1–3 theorems.

## Build

From `Models/KernelBridge` (after building `IxCK` and `IxCC`):

```sh
lake build
```
