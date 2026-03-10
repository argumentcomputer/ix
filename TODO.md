Aiur is a zkDSL, fully declarative, without mutation os dynamic indexing. But it's armed with rich datatypes and unbounded recursion.
The Aiur frontend is a Lean-embedded DSL, implemented in `Ix/Aiur` and whose syntax is defined in `Ix/Aiur/Meta.lean`.
More examples of non-trivial Aiur programs can be found in `Ix/IxVM`.

We're implementing a zkVM, a kernel for Lean 4 in Aiur so we can generate zk proofs of typechecking.
We have WIP reference implementations of this kernel in `Ix/Kernel` and `src/ix/kernel`.
The current implementation of this kernel in Aiur is in `Ix/IxVM/Kernel.lean`.

Note that the kernel works on certain datatypes, but the data that the zkVM will receive as serialized bytes will be deserialized as `Ixon` nodes.
Therefore we need to convert Ixon to the types used by the kernel.

This conversion is implemented in `Ix/Kernel/Convert.lean` and `src/ix/kernel/convert.rs`. Now we need the corresponding implementation in Aiur.
Do it in a new file `Ix/IxVM/Convert.lean`.
