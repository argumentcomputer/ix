# Verifiable voting demo

Three voters cast salted ballots. The organizer publishes their receipt hashes,
the tally, and an IxVM evaluation proof. Each voter can check that their receipt
appears exactly once in the list consumed by the agreed election program.

**Use synthetic ballots.** The current Aiur/multi-stark backend uses a non-hiding
polynomial commitment scheme. This example demonstrates verifiable computation
and ballot inclusion; it does not yet provide cryptographic vote secrecy.
Salting protects against guessing a vote from its receipt alone, not leakage
through a non-zero-knowledge proof.

## One-command showcase

```sh
lake exe Apps.ZKVoting.Demo
```

This builds the app, creates three fresh ballots, generates a real proof,
verifies voter 1's inclusion, and demonstrates tampering rejection. It retains
the public artifacts in a temporary directory and prints its path. The executable
prints prover setup and proof generation times separately on each run, excluding
compilation and subsequent verification.

Pass a new directory to retain the artifacts at a specific location:

```sh
lake exe Apps.ZKVoting.Demo /tmp/voting-demo
```

## Generate an election

Prepare an election in a new directory. The default ballots are Alice, Alice,
Bob; optional candidate arguments let you choose another example:

```sh
lake exe Apps.ZKVoting.Prover /tmp/voting-demo alice alice bob
```

The prover first executes the claim, generates a proof, and verifies it before
writing `election.proof`. It refuses to overwrite an existing directory. With no
arguments, `lake exe Apps.ZKVoting.Prover` uses the default ballots and creates a
temporary output directory.

The directory contains:

- `board.json`: the ordered receipt list and public tally.
- `election.proof`: the claim and its actual proof.
- `voter-1.receipt`, etc.: copies of the receipts the simulated voters keep.

No ballot bodies, salts, or private `.ixe` environment are written. In a real
application, voters create their own salted ballot definitions and retain their
receipts independently. Here the prover simulates that submission phase in one
process; receipt files are a presentation convenience, not an identity system.

For a quick rehearsal without generating a proof:

```sh
lake exe Apps.ZKVoting.Prover /tmp/voting-rehearsal --execute-only
```

This runs the real IxVM evaluation, but **does not produce a verifiable election**.
The verifier requires a proof and rejects a rehearsal directory.

## Verify an election

Show the public board, then verify as voter 1:

```sh
cat /tmp/voting-demo/board.json
lake exe Apps.ZKVoting.Verifier /tmp/voting-demo /tmp/voting-demo/voter-1.receipt --show-tampering
```

The verifier displays the complete ballot list, verifies the proof, confirms the
voter's inclusion exactly once, and prints `Alice 2 | Bob 1 | Charlie 0`.
It then demonstrates rejection of changed totals, a substituted ballot, an
omitted ballot, a duplicate ballot, and a corrupted proof. These demonstrations
also try reusing the proof after rewriting its claim to match a forged tally.
They alter in-memory copies; the files remain usable for another presentation.

You can copy just `board.json` and `election.proof` to another machine with the
same application version. The verifier needs no private environment or ballot
openings. A voter brings their independently retained receipt file. Supplying a
missing receipt makes verification fail even if the remaining election is valid.

## What is proved

Each ballot is an ordinary safe definition of `Ballot`, containing a randomly
generated 256-bit salt and a candidate. Its receipt is the BLAKE3 address of its
Ixon constant bytes. Two votes for Alice have different receipts.

Both prover and verifier compile the same `runElection` definition. From the
public ordered list, the verifier reconstructs an input definition whose body is
`runElection [ballot₁, ballot₂, …]`, where each ballot reference is its published
receipt hash. It independently compiles the expected output definition from the
public tally and requires an exact, unconditional `Eval(input, output, none)`
claim. It then verifies the proof against that claim's digest.

IxVM authenticates each referenced ballot's bytes, checks the input and its
dependencies, and evaluates the election. A malicious organizer cannot substitute
another program, append hidden votes, or alter a ballot behind an unchanged hash.
The verifier rejects duplicate receipts and checks the tally total as well.

This does not establish voter eligibility, enforce one person/one vote, prevent
coercion, or force inclusion of an omitted ballot. Inclusion checks let an omitted
voter detect that omission. The tally itself can also disclose choices in a very
small election.

The self-contained application regression tests run through both IxVM execution
backends and generate a real proof to test verification and replay rejection:

```sh
lake exe Apps.ZKVoting.Tests
```
