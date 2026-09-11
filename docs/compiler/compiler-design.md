# Compiler design

The compiler refines executable Ixon semantics through explicit intermediate
languages. Its implementation and proofs live in `Ix/Compiler`.

| Layer | Role |
| --- | --- |
| `Ixon` | Source expressions, declarations, canonical sharing, serialization, addresses, and usage checking. |
| `IxIR0` | Erased, curried, call-by-value semantics with address-indexed globals and explicit external oracles. |
| `IxIR1` | Calls, partial applications, heap operations, ownership worlds, and reference-count costs. |
| `IxIR2` | Checked consuming operations, reuse credits, borrowed-call attachments, and source-pipeline refinement. |
| `X86` | Selected bounded native families, instruction and byte semantics, encoders, object generation, and execution checks. |

The public theorem inventory is checked in `Ix/Compiler/Fence.lean`. Each
theorem's premises determine its supported source, heap, resource, and external
oracle conditions. The presence of a backend module does not establish native
correctness for every source program.

## Ownership, borrowing, and callable values

Usage annotations distinguish erased, affine, linear, and reusable arguments.
Shared values can be duplicated through the reference-count discipline; unique
values require exclusive ownership. Saturated calls to known functions can
carry stronger ownership contracts than shared partial applications. Borrowed
attachments validate their lender lifetime and resource behavior separately.

### Freeze, duplication, and mixed fields

The ordinary lowerer does not implicitly convert unique values into shared
values. Such a conversion would need an explicit operation with ownership and
cost rules. A projection or shared callable representation cannot silently
publish an owned unique child. See the [restriction table](lowering-restrictions.md).

## Identity and proofs

Canonical source and IR serializations determine content addresses. The port
preserves the existing hash domain strings and native symbol names. Hash-dependent
identity results state their collision premises; evaluator refinements carry
their own semantic premises. External oracles are parameters of the model.

The compiler's source syntax and the consistency model's syntax are currently
separate types. Transport from these compiler stages or the production `Ix.Kernel`
checker to `Ix.Theory` requires additional refinement proofs. The component's
[trust ledger](trusted-extern-ledger.md) describes the native and specification
assumptions that remain in execution claims.
