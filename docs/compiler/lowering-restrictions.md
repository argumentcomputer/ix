# Current lowering restrictions

The ordinary `IxIR0` to `IxIR1` lowerer rejects the following unsupported
ownership and callable forms. `Ix.Compiler.IxIR1.Lower.RestrictionKind.all`
enumerates all six cases; executable witnesses pin their diagnostics.

| Restriction | Reason |
| --- | --- |
| No implicit freeze | A unique value cannot enter a shared argument, binding, or result without a justified ownership conversion. |
| No general unique destructuring | Extracting a unique child must consume the parent and account for every remaining field. The separate checked unique-list endpoint handles its supported schemas. |
| Shared, all-reusable function values | Shared partial applications duplicate their stored arguments. Saturated known calls have separate ownership contracts. |
| No unique captures | A shared closure cannot retain an exclusively owned captured value. |
| Mode-monomorphic ordinary recursors | The ordinary recursor representation does not carry the argument and result ownership information needed for general unique recursion. |
| Saturated-only `recSelf` | A recursive self reference has an arity and direct-call meaning; it has no general escaping or partially applied closure representation. |

The separate unique-list and borrowed-call compiler attachments validate their
own source schemas, lifetime conditions, and resource contracts. They do not
remove these ordinary-lowering restrictions. A rejected program has no native
correctness claim through the rejected path.
