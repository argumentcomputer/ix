# Differential tester for the mode checker: design (MT, 2026-11-13, draft 2)

Object under test: `checkBodies {}` against `runR`, unmodified, at `6db9089a7`, imported from
`~/runs/ixcc/mo-mt`'s kernel package. The tester is a Lake package of ours (`probes/MT/difftest`,
source `IxCC/plans/mt/difftest/`) with `require «ix-kernel» from "../../../mo-mt/IxC"`, reusing the
built `.lake/kernel` and linking one executable. If Lake will not reuse those artifacts, the fallback
is interpreted, as `Findings.lean` was. Jobs go through `run.sh MT-dt-*`, capped at 8 GB.

**1. Grammar, bounds, staying defined.**
- Types:
  - `Nat` (leaf);
  - `E`, two field-less constructors (imm);
  - `L` = List Nat, `LF` = List (Nat → Nat) (val, two constructors);
  - `B`, one inherited `L` field;
  - `S`, one `@shared` `L` field;
  - `K`, an erased `L` field and a `Nat` field;
  - `P`, two `Nat` fields;
  - `W`, a one-field wrapper of `Nat` (leaf);
  - `A = B` hypotheses (irr);
  - arrows `A →(m,r) B` over these.
- Classes, skeletons and `noLeaf` come from the types by the reader's own rules: `noLeafType`'s rule,
  `readSkel`'s. So finding 1's `Nat` behaviour is reproduced, not chosen.
- Fixed helpers: `consume`, `len`, `callTwice`, polymorphic `id`, `const` and `mkK` (class `val`,
  skeleton `unknown` at their type parameters).
- User definitions: 1 to 4, each using only earlier ones. Parameters 0 to 5 (5 so that a 6-ary call
  exists), any of the 7 binder modes; results any of the 4.
- Body depth ≤ 5, ≤ 40 nodes. Lists in inputs have ≤ 3 elements.
- Productions, type-directed:
  - variable;
  - call of a constant, constructor or primitive: saturated, partial, or over-applied when the result
    is an arrow;
  - λ, captures computed as their `lam` helper does;
  - `let` with all 8 `LetMode`s;
  - projection;
  - case on `L/B/S/K/P/W/E`, with λ-telescope or non-λ alternatives and extra arguments;
  - cast (an `Eq` case with an `irr` major);
  - literal, static, extern call.
- Staying defined: every term is typed in this universe, so `conform`, `select`, arities and
  constructors never mismatch. There are no `.stuck` constants and no recursion except `len`'s, on
  bounded lists, so every run terminates. A `stuck` run, or one out of fuel at fuel 100000, is a
  generator defect: counted, sampled, and expected below 1 %. Checker declines are counted.

**2. Inputs and externs, decided.**
- Inputs by parameter type:
  - `Nat`: a fresh number cell `.ref l l []`;
  - `E`: `.imm (.con c)`;
  - data types: fresh cells, fields by class, an erased field as `irr`;
  - erased or `irr` parameters: `irr`;
  - an arrow: a partial application of a program constant whose remaining interface the skeleton
    admits (`papSkel`, `Skel.admits`), with immediate or number arguments.
- Caps equal locations; `nextCap` is the heap size; every value is unconfined; cells point only to
  earlier cells. A unique argument's owned cells are fresh. Plain arguments share a sub-list in some
  cases, and numbers may be shared, as `OwnReach` allows.
- `inputsOkB`, a decision procedure transcribing `InputsOk` (HeapOk, ArgOk, ClosureAt/DefaultPaps,
  OwnTree, disjointness by DFS on the acyclic heap), must accept every input. A rejection counts as a
  generator bug.
- Externs, from a family argued `ExternOk` for every call:
  - a fresh number;
  - the identity at a plain parameter;
  - building a constructor from the arguments (finding 5's shape);
  - a fresh reference with a stale capability (finding 14's shape).
- Every call actually made is checked by `externOkB` (its clauses for that call). A run with a failing
  call is not covered.
- Flagged stream `ill-typed`: inputs and externs that pass `inputsOkB` and `externOkB` but put a value
  outside its field's class: a list where `Nat` is expected, a number or a partial application where data
  is expected. Its counters and hits are kept apart.

**3. Fuels.** `f₀` is the least fuel at which the fuel-100000 run of that program, seed and input is not
out of fuel. Small runs (`f₀` ≤ 128) are tried at every fuel 0 to 2·f₀ + 16, then at 1000 and 100000.
Larger runs are tried at 0..64, 128, 256, 1000 and 100000. `runR` is not monotone in fuel (finding 7),
so any change of outcome after the first value is recorded.

**4. What is recorded.**
- **Counterexample**: the checker accepts every body of `P`, and for some seed body, typed input passing
  `inputsOkB`, covered externs and fuel, the run is a violation. The record holds seed, index, body,
  input, the fuel band and the kind.
- Counted, not findings:
  - refuses and no run violates at any fuel tried: the completeness datum, histogrammed by the refusal's
    witness;
  - refuses and violates;
  - accepts and is clean;
  - declines;
  - generator defects;
  - not covered;
  - non-monotone fuel.
- The ill-typed stream has the same categories, separately.

**5. Shrinking.** Greedy, to a fixpoint. Steps:
- drop a definition, a parameter or an argument;
- replace a subterm by a variable or a smaller term of its type;
- set a mode to the default;
- shorten the input lists.

A step is kept while the program stays typed, the checker still accepts, `inputsOkB` holds and some
fuel gives the same violation kind. The result is 1-minimal for these steps. Output: the `Prog` as Lean
source pasteable into `Findings.lean`, its input and fuels, and the `(seed, index)` that regenerates it.

**6. First test.** SplitMix64 written in the file: case `i` of seed `s` draws from `mix(s, i)` alone.
Seeds 1 to 8 are fixed, with N programs each; N is set by the first measurement, then frozen. The
generator knows no finding. Recognisers written afterwards classify shrunk hits; for example:
- F2: a closure capturing a borrowed leaf, at a `noLeaf` arrow parameter of a leaf-result call;
- F7: `erasedRead` only below some fuel;
- F12: a primitive's partial application, returned.

Pass: hits recognised as each of 2, 7, 8, 9, 10, 11 and 12. Unrecognised hits are listed as candidates.

Reach of the grammar, honestly:
- 1, 2, 3, 7–13: in the default stream;
- 5 and 14: with the extern family;
- 15: only in the ill-typed stream;
- 4: not reachable. It needs two programs (the oracle's and the canonical). A `--lossy-classes` variant
  (check with deep formers at `val`, run the canonical program) would model it with our model of the
  oracle, not theirs. I would build it last, if wanted;
- 6: not reachable (records and the reader, not `Prog`);
- the 2^20 truncation: not reachable.

**7. Cost and results.** Measured so far: `Findings.lean`'s 249 runs and 30 checks took about 0.3 s
beyond Lean's start-up, interpreted. Estimate per program: 1 check plus about 3 seeds × 3 inputs × 70
fuels ≈ 600 runs. That is about 1 minute per thousand programs interpreted, and a few seconds compiled;
it will be measured on the first job and reported. Output:
- box `~/runs/ixcc/logs/MT-dt-<seed>.log` (configuration echoed, tallies);
- `probes/MT/difftest/out/<seed>/` (one Lean file per shrunk hit, a tally file), copied to
  `IxCC/plans/mt/difftest/out/`;
- a section "Differential tester" in `resource-cert/mode/RUNS.md`.

Disk under 300 MB.
