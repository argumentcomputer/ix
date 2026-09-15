# Aiur witness-heap bytecode execution

Checked bytecode rows now give concrete execution meaning to the
[logical-trace derivation](aiur-backend.md). For a fixed pinned
`Aiur.Bytecode.Toplevel`, `Trace.Validated.public_bytecode` proves:

> A validated trace, rows satisfying the bytecode replay rules, and the
> existing static row certificate give a finite execution of each public
> function claim against the same extracted witness heap and allowed advice.

The implementation is [OracleEval](../Compilatrix/Aiur/OracleEval.lean),
[BytecodeEvalW](../Compilatrix/Aiur/BytecodeEvalW.lean), and
[BytecodeSound](../Compilatrix/Aiur/BytecodeSound.lean). It covers all 34
operations and four controls at the unchanged upstream revision
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`.

The static certificate still records facts about trace rows. Proving those
facts from the bytecode component checker and the keyed AIR remains separate
work. The local replay and logical gadget model are not an AIR extraction
or conformance theorem. No production IxVM proof-acceptance claim follows
from this milestone.

## Local replay

`OracleEval.runFunction` takes a toplevel, consumer limits, a function index,
flat inputs, and a finite answer tape (`List (List G)`). It executes the
function's actual body using indexed registers and an explicit continuation
stack. It returns the outcome, the ordered list of exact lookup demands,
and the ordered advice observations. Every tape entry must be consumed.

The local machine does not enter a callee's body. A constrained call records
the complete function index, inputs, and supplied outputs as a demand. The
finite execution relation subsequently requires an execution of that callee.
Both constrained and unconstrained calls check that the callee exists and
that its input arity agrees. Result arity comes from the call instruction.

Each operation below consumes one answer-tape entry. All other operations
consume none.

| Operation | Answer entry | Resulting obligation |
| --- | --- | --- |
| Constrained call | Exactly `outputSize` fields | Exact function message |
| Unconstrained call | Exactly `outputSize` fields | Allowed advice |
| Store | One pointer field | Exact memory message with the stored contents |
| Load | Exactly `size` fields | Exact memory message with the loaded contents |
| Byte/u32 gadget | Its complete logical outputs | Exact logical gadget message |
| `u8RangeCheck` | An empty list | Byte-range gadget demand; the entry is still consumed |
| `ioGetInfo` | Two fields | Allowed advice; no host buffer lookup is assumed |
| `ioRead` | Exactly the declared number of fields | Allowed advice |
| Big-integer div/mod hint | Two pointer fields | Allowed advice; no arithmetic equation is assumed |
| Field-to-bytes hint | Eight fields | Allowed advice; byte range and canonicality are not implied |
| Field-inverse hint | One field | Allowed advice; the inverse equation is not implied |
| Unconstrained u32 add/add3 | Four fields | Allowed advice plus a computed fifth output |

Arithmetic and equality assertions compute over the pinned Goldilocks type.
`u32ToField` packs four fields in little-endian order. The u32 add instructions
also require four operands in each input array. They append the four supplied
fields and compute the virtual carry:

```text
carry = (packed inputs sum - packed supplied fields) * (2^32)^(-1)
```

The inverse constant is kernel-checked. Packing introduces no byte-range
condition, and this carry need not be a bit until constrained code checks it.
The replay rejects missing value indices instead of supplying default zeros.
It also rejects wrong input, reply, word-operand, and continuation arities.

`ioSetInfo`, `ioWrite`, and `debug` have no constrained output or effect in
the pinned builder. They leave this local state unchanged. This boundary
certifies function observations, not evolution of the honest host IO buffer.

## Return and shared continuations

Outcomes distinguish function `return` from continuation `yield`, retaining
the selector and output fields. A function return discards every pending
continuation. A yield resumes the closest pending continuation, checks its
declared output size, restores its pre-branch register namespace, and appends
only the yielded fields. Demands and advice from the branch remain recorded.
At the function boundary, both outcome forms supply the function outputs,
matching the reference evaluator's treatment of a root yield.

For example, with registers `[0, 10]`, a branch may append local `99` and
then yield `7`. The continuation sees `[0, 10, 7]`; adding its second and
third values produces `17`. Case-local `99` does not occupy the yielded slot.
An ordinary match forwards a yield to the closest enclosing continuation.
Cases are selected in order, with the first matching label winning.

## Memory, advice, and primitive meanings

`BytecodeEvalW` is a finite inductive execution relation. Its function rule
requires an actual successful local replay, allowed advice, and executions
of every demanded message. Memory and gadget messages have concrete leaf
rules. This expands constrained recursive calls while allowing shared
providers and repeated demands.

Every memory observation uses one `Memory.Heap`. The heap maps a width and
field pointer to complete contents; the contents must have that width.
Stores and loads use the same rule. A load needs no preceding store, and a
store may return pointer seven. Equal contents may occur at two different
pointers. A coherent self-referential cell remains valid. Heap acyclicity,
datatype tags, and typed pointer layouts require additional evidence.

An `AdviceOracle` is an executable allowed-answer predicate. The tape
supplies the choices, and `AdviceAllowed` records that every observation
passes the predicate. The unrestricted instance allows every answer of the
instruction's required shape. Repeated identical requests can receive
different answers. A hint's name supplies no mathematical fact: assertions,
memory observations, and gadgets must establish any facts the program uses.
Hint-produced pointers can name cells already present in the witness heap;
the model does not run an allocator inside the hint.

Logical gadget payloads concatenate complete inputs and outputs. Their tags
are local semantic identifiers, not Rust AIR channel numbers:

| Tags | Meaning |
| --- | --- |
| 0, 1, 2 | Byte bit decomposition, shift left, shift right |
| 3, 4, 5, 6 | Byte xor, add with carry, multiply with high byte, subtract with borrow |
| 7, 8, 9 | Byte and, or, less-than |
| 10 | u32 less-than |
| 11, 12, 13 | Byte xor split at 7, xor split at 4, pair range-check |

Primitive providers check exact payload arities, byte/u32 input ranges, and
the concrete mathematical outputs. A malformed input cannot become valid
through machine-word truncation. Relating these logical operations to
affine outputs, shared physical tables, and the u32 comparison's six range
lookups is part of the future AIR adapter.

## Checked interfaces and limits

`OracleEval.check` retains proof of the complete successful replay.
`OracleEval.checkRow` checks that a provider's replay has exactly its claimed
outputs and ordered demands, and that all its advice is allowed. Memory and
gadget providers must be leaves. Only active providers with nonzero field
multiplicity are execution premises; the independent trace checker enforces
activity, balance, the characteristic bound, and memory coherence.

`checkRows` takes one tape per trace row. `validateRows` returns `CheckedRows`,
retaining its row facts. `CheckedRows.public_bytecode` composes those facts
with `Trace.Validated` and the supplied `StaticCertificate`. Local replay can
accept a balanced cyclic trace; that trace cannot obtain the static
certificate needed by this theorem.

Default limits apply separately to each replay:

| Limit | Default |
| --- | ---: |
| Local machine transitions | 65,536 |
| Registers and copied operand fields | 65,536 |
| Answer-tape entries | 65,536 |
| Total fields in the supplied tape | 1,048,576 |
| Recorded demand/advice fields, including scalar tags and indices | 1,048,576 |

Observation charges are checked before extending the logs. Reply lengths
are checked against the supplied lists; an enormous declared output size
does not cause an allocation of that size. The transition budget is local
replay fuel, not a source recursion measure or STARK height policy.
`run_add_fuel` and `runFunction_add_fuel` prove that increasing it preserves
a successful result. These are admission bounds, not a machine-time theorem.
Use the separate bytecode reader and trace structural limits at ingress;
this API adds no binary trace or answer-tape parser.

## Validation and remaining work

```sh
lake build Compilatrix.Aiur CompilatrixTests.Aiur.Execution.Proofs \
  CompilatrixTests.Fences.AiurExecution tests-aiur
lake exe tests-aiur
nix build .#checks.x86_64-linux.aiur
```

The execution suite adds 276 assertions, with an explicit inventory check
for all 34 opcode tags. It covers all controls, recursive traces, arbitrary
and duplicate-content pointers, incorrect primitive providers, unchecked and
checked hints, virtual carry, continuation scope, nested early returns,
malformed arities/indices, and resource boundaries. The kernel examples
include complete counter and ranked-mutual executions and universal
impossibility of static certificates for locally accepted cyclic attacks.
Thirty-nine new exact axiom fences use only ordinary logical axioms. The
existing trace, wire, native, and proof gates remain required.

The upstream pure IO-type split still blocks unchanged importing of
`BytecodeEval`. Refinement to that honest evaluator remains to be proved;
in particular, witness pointers are not equated with insertion indices, and
the reference's IO effects and hint allocations need a representation
relation. Certificate-checker soundness, the production IxVM export and
constraint dump, keyed AIR extraction, artifact/source bindings, primitive
conformance, and Ixon/DSL lowering remain explicit subsequent obligations.
