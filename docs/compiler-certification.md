# Certifying the Lean → Ix compiler: what `compile-certify` establishes

This document describes the compiler-certification lane (`Ix/CompileCert/**`) as it runs on real
compiler output: the two theorems it decides (W and S), the receipts they use and how far each is
trusted, and how to run the certifier. It does not describe what each Lean name denotes after
compilation (the output contract); that belongs to `docs/compiler-passes.md`.

The certified checker (`IxC/**`) proves Ix environments consistent: an environment it admits has a
set-theoretic model. The lane relates a Lean environment to the compiled Ixon environment so that
this consistency result speaks about the Lean declarations.

## 1. The two theorems

### 1.1 W: the compiled bytes are a faithful reading of the Lean declarations

For an *input* (a closed set of Lean declarations, the compiled records they reach, the name map
from Lean names to records), the decision `checkIndexed` (equivalently the list-based
`checkCompiled`) returns an `AcceptedAssociation` exactly when:

- the exact record bytes are admitted by the certified checker (`checkBytes`: decoding, reading,
  the verified fold);
- the source is closed and uniquely named, and the map covers it (`DirectDomain`);
- every Lean declaration's independent export (`directExport`: names through the map, universes
  canonicalised under a proved semantic guard, binder names and `mdata` erased) equals an entry of
  the certified reader's output (definition hints quotiented; a projection function of a
  structure-like the reader rewrites is compared with the raw record through the reader's proved
  `projRewrite` relation);
- whole inductive blocks match and every touched definition group is covered.

`checkIndexed_sound` (`Ix/CompileCert/Indexed.lean`) states this; `faithful_sound` is the same
statement for `checkCompiled`. W says the compiled constant *is* the Lean declaration, read through
the export. It does not by itself say that the Lean declaration's meaning is the compiled
constant's meaning in a model: that is S.

### 1.2 S: the Lean declarations' model is the pull-back of the compiled environment's model

For the same input, S takes in addition the **normalised source installation**
(`SourceNormalizedInstallation`): the Lean declarations exported under their own names, completed
with the certified modeller's helper declarations, projection functions of non-direct
structure-likes lowered to recursor form (each with a lowering receipt), and folded by the
certified checker itself. The decision `decideStrongCone` (`Ix/CompileCert/StrongCone.lean`)
checks, between the installed source environment and the admitted target environment plus
certifier-proposed support declarations, that names agree with the accepted map, that every
installed source row has a target row under the map whose type, value, recursor rules and
capabilities are the same terms up to the map and the universe image, that eta, unit and
projection-tower laws carry over, and that the Nat and reduction operations of the source are the
target's. Its success is a `StrongCone`, and `StrongCone.sound` states what that implies:

- W's conclusion for the input (above);
- the source fold accepted the installed declarations (`checkDecls … = .ok installed.env`);
- the target (artifact plus support) has a strong model, and **for every strong model of the
  target there is a strong model of the installed source whose annotations and values are the
  pull-back of the target's under the name map** (`artifact_strong_model_all`);
- every original Lean declaration of the input is installed as its exact export, or is a
  projection function whose installed replacement has a lowering receipt.

"Strong model" is the checker's `EnvModelM`: every field the certified checker's soundness uses
(typing, definitional equations, capabilities, recursor rules, projection towers, Nat operations,
`Nat.div`/`Nat.mod` laws, reduction axioms). So a Lean constant's meaning in the source model is,
by construction, the compiled constant's meaning in the target model.

### 1.3 Unit of certification

W is decided once over every candidate of a library. S is decided **per cone**: a root, its
closed dependency cone as the source, and the records that cone reaches, admitted on their own.
The S checks compare environments whose lookups are lists, so one global S over a library would
be quadratic in it; per cone the cost is bounded by the cone. A constant is **S-Certified** when
some accepted cone contains it; the conclusion then holds for every member of that cone.

## 2. Receipts and their trust

| Receipt | What it says | How it is established |
| --- | --- | --- |
| admission (`checkBytes`) | the record bytes decode, read and fold | the certified checker, proved (`IxC`) |
| W association | each Lean declaration's export is a reader entry | decided; `checkIndexed_sound` proved in the lane |
| source installation | the exported Lean declarations fold | the certified checker's fold, run per cone |
| lowering receipt (`SourceProjectionLowering`) | a lowered projection function has the original header, the declared binder domains and the recursor form of the original field | decided in the lane; the equation `f p⃗ self = lowered p⃗ self` is a theorem **checked by Lean's kernel** at certification time (`addDeclCore`, checking on) |
| name map, support, Nat/DivMod/reduce receipt names, source pins | the arguments of the S checks | **proposed by the certifier, untrusted**: names are checked by `SemanticNamesAgree` and the installed association, support by the verified fold, receipts by the receipt checks, pins by the fold (sound for any pins) |
| S association (`decideStrongCone`) | the pull-back above | decided; `StrongCone.sound`, `artifact_strong_model_all` proved in the lane |

Trusted, outside the proofs: the host `Lean.Environment` the source is read from (as for every
use of `captureCone`); that `directExport`/`exportSourceExpr` is the intended reading of a Lean
declaration (erasing binder names, binder infos and `mdata`; universes canonicalised under the
proved guard); that a theorem the certifier lists as a lowering witness was accepted by Lean's
kernel; the Lean runtime that executes the decisions. The tracked axiom audit
(`Ix/CompileCert/Audit.lean`, `lake run check-cert`) checks that every root of the lane uses only
`propext`, `Classical.choice` and `Quot.sound`, and that no decision reaches a hash-cached
equality.

**Executable only (no proof):** which constants are offered to the decisions (record selection,
the expression-size budget, the cone choice and budget), the classification of what is not
certified (class, blocking dependency, diagnostic), and every proposal. A wrong triage or proposal
can only leave a constant uncertified; Certified and S-Certified come only from an accepted
decision.

## 3. Verdicts

W: **certified**, **unsupported** (a named class, e.g. `partial`/`unsafe` definitions the
checker's reader declines, an expression over the tree budget), **blocked** (by a dependency that
is not certified) or **rejected** (a diagnostic: the compiled constant is not the Lean
declaration). S, beside it: **S-certified**, **S-unsupported** (class), **S-blocked** (by a cone
member that fails, or by W), **S-rejected** (diagnostic). A W verdict other than certified carries
over to S (`W unsupported: …`, `W: …`, `W rejected: …`).

## 4. Running it

```
lake build compile-certify
compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--explain <name>]* [--receipts-only] \
  [--strong | --strong-only] [--strong-roots <A,B,...>] [--strong-every <k>] \
  [--strong-max-cone <n>] [--strong-tasks <n>]
```

- `--file` elaborates the file as `ix compile` does (`Benchmarks/Compile/CompileInitStd.lean`,
  `Benchmarks/Compile/CompileMathlib.lean`); `--modules` imports modules.
- W writes `<prefix>.tsv` (one row per constant: name, address, verdict, cause),
  `<prefix>.classes.tsv`, `<prefix>.json`, the raw-projection measurement `<prefix>.proj.tsv` and
  the lowering receipts `<prefix>.receipts.tsv`/`.receipts.statements`.
- `--strong` then decides S: on every W-certified constant (a cover by cones, roots nothing uses
  first), on `--strong-roots`, or on a sample (`--strong-every k`: every k-th W-certified constant
  in name order plus the projection functions of non-direct structure-likes). It writes
  `<prefix>.strong.tsv` (name, W verdict, S verdict, cause), `<prefix>.strong.cones.tsv` (per cone:
  members, records, support, witnesses, time per stage, outcome), `<prefix>.strong.classes.tsv`
  and `<prefix>.strong.json`. `--strong-only` skips the global W (each cone still runs its own W
  association) for probes.
- Exit 0 iff something is certified, nothing is rejected, every raw projection on a non-direct
  structure-like has a receipt, and, with S, something is S-certified and nothing is S-rejected.

The lane's own gate is `lake run check-cert` (the audit, the strict build, the fixture checks, the
certifier on the fixture with and without `--strong`).

## 5. Known limits of the S route (2026-10-06)

- **The pin-certified Nat operations** (`Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, `Nat.shiftRight`). The certified checker accepts them only through a pin variant whose
  certificate proofs are generated over the compiled environment's names (`Benchmarks/Kernel/PinGen.lean`). The
  source installation folds Lean's declarations under their own names; the compiled names merge alias fibers
  that Lean keeps apart (for example `LT.lt` and `LE.le` share one address), so the compiled certificates do not
  translate back. Every cone containing one of these operations is S-unsupported (the operation) or S-blocked
  (by it). Closing it needs source-named certificates generated from the same certificate theorems through the
  lane's export.
- **Quotients.** The checker installs the `Quot` block only over the pinned `Eq` basis; the source installation
  installs Lean's `Eq` as an ordinary inductive, so a cone containing `Quot` is refused by the source fold.
- **Proof-field projections of mutual or nested structure-likes** (theorems in Lean 4.34.1) are refused by W.
- **Cost.** S is decided per cone; a cone of about 8,000 declarations takes about ten minutes (W of the cone and
  the source export dominate). `--strong-max-cone` bounds the cone size; larger cones are S-unsupported.
