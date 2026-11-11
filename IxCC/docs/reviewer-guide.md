# IxCC Reviewer Guide

This guide provides a top-down roadmap for auditing `IxCC` (the certified Ixon-to-x86-64 compiler), its Trusted Computing Base (TCB), its Produce-and-Recheck architecture, and its pass-by-pass soundness proofs on `jcb/ixck-ixcc-merge`.

---

## 1. Architectural Overview: Produce-and-Recheck

`IxCC` separates **untrusted certificate generation (`produce`)** from **bounded-budget certified checking (`Recheck.run` / `RcReplay.run`)**:

```
Serialized Ixon.Env (.ixe) + Unfolding Equations + Certificate Bundle
  │
  ├─► 1. Ingress & Typed Source Contract      (IxCC/Ixon/V3/Typed.lean, IxCC/Src/Semantics.lean)
  ├─► 2. Erase & Lambda Specialization        (IxCC/Lam/Erase/Term.lean, IxCC/Anf/Specialize.lean)
  ├─► 3. ANF Walk (Beta/HO/CPS Inline)        (IxCC/Anf/Walk.lean, IxCC/Anf/Shrink.lean)
  ├─► 4. Flat IR (Fir) & Control-Flow (Cfg)   (IxCC/Fir/Lower.lean, IxCC/Cfg/Lower.lean)
  ├─► 5. Ownership & Reference Counting       (IxCC/Own/Plain/Syntax.lean, IxCC/Own/Plain/Check.lean,
  │      (--rc off | --rc on | --rc auto)      IxCC/Cfg/Rc/Native.lean, IxCC/Rt/Rc/Procs.lean)
  ├─► 6. Runtime Tagging & Arithmetic (Rt)    (IxCC/Rt/Lower.lean)
  ├─► 7. Register Allocation & Framing (Xv)   (IxCC/Xv/Validate/Check.lean, IxCC/Xv/Stacking/Emit.lean)
  └─► 8. x86-64 Stream, ELF64 & Ring-0        (IxCC/X86/Eval.lean, IxCC/X86/ELF.lean, IxCC/X86/ELFRead.lean,
                                               IxCC/CompileClaim.lean, IxCC/Ring0.lean)
```

In `Recheck.front`, the checker validates the unfolding table (`Table.ofCert`; each `eqn` and `csimp` theorem may reach no axiom other than `propext`, `Classical.choice` and `Quot.sound` through the program's reference graph, `Src.Table.checkAxiomClosure_sound`, while `Tc.checkEnv` typechecks the environment), checks the certificate's relevance annotation with `Relevance.check` and `Relevance.checkCanonical` (inside `Src.Recheck.annotation`, on every program whatever its pinned identities; it re-derives each position's class from the declaration types and refuses any irrelevant tag it cannot justify; on byte-level verification paths (`CompileClaim.verifyBytes`, `Ring0Sip.verifyBytes`, and `ixcc check-cert`), `Recheck.checkCanonicalRelevance` additionally re-runs `Src.Relevance.annotate` on `(inp.env, cert.table)` and requires exact equality with `cert.relevance`), and runs `Lazify.run` to produce `a.src`. `Relevance.Proof.check_sound` states what `Relevance.check` establishes, and `Src.Lazify.run_modeEq` that `Lazify.run` changes nothing but application modes; neither is a semantic statement, and `checkCanonical` and `annotate` have no theorem. No theorem relates `a.src` to the ingested program semantically (the front end is outside the proof chain, open item S6), so every soundness theorem below is relative to SrcEval on `a.src` and says nothing on an input where it goes wrong. From `Lam.erase` through ELF emission, every middle-end and backend heuristic pass (inlining, specialization, ownership lowering, linear-scan register allocation, frame layout, and block ordering) is either proved correct for all bounded certificate steps or validated by a proved checker (`Xv.Validate.program_sound`, `FrameLayout.check_sound`, `Order.check_sound`, `ELF.check_sound`). The replay refuses, with an ordinary error, as soon as an input or a certificate step passes one of the fixed budgets in [compiler-design.md, "Middle-end budgets"](compiler-design.md#middle-end-budgets) (term depth at ingress, before the front end and in erasure, the program's term nodes counted as trees, each Lam global's nodes and depth before ANF conversion, each Anf global's nodes and depth, the whole program and the back end's work after every step, a walk's copies, depth on the native stack, firings and work, an inline or shrink step's work, a specialisation step's work and nodes), so the copying, memory, work and native stack depth of a check stay within fixed bounds whatever the certificate asks for; `tests-recheck` runs every verifier entry point on an 8 MiB Lean stack against inputs at and past each budget. Every list the certificate carries (table columns, annotation records and tags, middle-end steps, the allocation's locations, edits and facts, frame slots and cells, the block order) is capped in quantities of the program before its first reader walks it, by a loop: the table in `Table.ofCert` (`TableCert.keysOk`), the annotation in `Recheck.checkRelevanceKeys`, the shrink and inline steps in `Anf.Pipeline.Step.run`, the allocation in `Xv.Validate.sizeOk`, frames in `FrameLayout.check` (the "Certificate caps" table in [compiler-design.md, "Middle-end budgets"](compiler-design.md#middle-end-budgets)); the certificate-sized inputs also run on a 2 MiB stack.

---

## 2. Step-by-Step Audit Path

### Step 1: Top-Level Soundness & Cryptographic Claim Bridge (Start Here)

Start with the modules that state what `IxCC` proves from serialized source bytes down to x86-64 machine execution:

1. **[`IxCC/CompileClaim.lean`](../IxCC/CompileClaim.lean), [`IxCC/CompileClaim/Proof.lean`](../IxCC/CompileClaim/Proof.lean) & [`Ix/Claim.lean`](../../Ix/Claim.lean)**
   - Connects `Ix`'s Blake3-committed `CompileClaim` (tag `13`, wire header `E8 05 04 07`, naming the environment root and its role table) to machine-checked x86-64 execution across all three memory policies (`.immortal`, `.zeroRc`, `.plainRc`).
   - Key definitions and theorems:
     - `verifyProgram`, `verifyBytes`, and `checkClaim_ok_iff`: `verifyBytes` (and `checkClaim`) decodes the `.ixe` bytes, verifies that the `Ixon.Env` Merkle root matches `c.env`, that its role table's address (none for an unbound environment) matches `c.roleTable`, and that the environment typechecks (`typecheck := true` by default), requires the certificate's annotation to be `Src.Relevance.annotate`'s (Stage A), and runs `verifyProgram` on the ingested program. `verifyProgram` takes no environment: it verifies that the target root has `Nat` parameters and an observable return type, that the certified checker accepts the certificate for the claimed policy and ABI arity, and that the emitted ELF64 `.o` bytes hash to `c.elfHash`.
     - `verifyProgram_immortal_sound`, `verifyProgram_zeroRc_sound`, `verifyProgram_plainRc_sound`, and their byte-level counterparts `verifyBytes_immortal_sound`, `verifyBytes_zeroRc_sound`, and `verifyBytes_plainRc_sound`: End-to-end soundness from `Ixon.Env` / `ByteArray` inputs to linked x86-64 object execution (`X86.Linked`, `a.linked D`, `ELFRead.parse`, `ByteEval.step`) under `X86.Driver.Ok`, relative to SrcEval on the checked source `a.src`: an object result is the source's value or `a.front.GoesWrong` holds on that input, which no theorem rules out.
     - `verifyProgram_immortal_rootShape`, `verifyProgram_zeroRc_rootShape` and their `verifyBytes_*_rootShape` forms (over `Recheck.ResultShape` and `Recheck.Artifact.goesWrong_immortalRoot` in [`IxCC/Recheck/Proof/RootShape.lean`](../IxCC/Recheck/Proof/RootShape.lean)): at a claim's root, which `checkImmortalRoot` accepted (`Nat` parameters, `isImmortalViewType` readback type), `a.front.GoesWrong` holds only if SrcEval gets stuck or traps, or returns a result that is not of the shape the root's declared type describes (a `Nat`, a pinned `Bool` constructor, or a constructor of the result enumeration). Erasure registers a constructor-table row for every constructor a root's result can hold (`Lam.Erase.resultCtors`), so this needs no side condition, also for a root compiled alone (`Recheck.Front.boolRows`). On the `Nat` route the view rejects exactly the off-shape results (`Recheck.Front.view_none_iff_nat`); on the other routes it also accepts some off-shape constructors (it relabels by table tag).
     - `verifyProgram_immortal_shape`, `verifyProgram_zeroRc_shape` and their `verifyBytes_*_shape` forms (`Recheck.ShapeClaim`, same file): the three clauses at the claim's root restated with the shape view `Recheck.Front.shapeView` (the view restricted to the root's result shape), whose rejection case is exactly a result off the shape on every immortal route (`Recheck.Front.shapeView_none_iff`). The view-based statements are kept: they also describe the object where the source returns a value of another type.
     - `verifyProgram_plainRc_rootShape` and `verifyBytes_plainRc_rootShape` (over `Recheck.PlainShape` in [`IxCC/Recheck/Rc/Proof/RootTree.lean`](../IxCC/Recheck/Rc/Proof/RootTree.lean)): at a plain-RC claim's root, the plain-RC `GoesWrong` holds only if SrcEval gets stuck or traps, or returns a result that is not a constructor tree of the root's declared first-order type (`Recheck.TreeShape`; a `ResultShape` for a root returning the pinned `Nat` or `Bool`). The converse is not proved there, nor the heap readback of every such tree. Nothing proves that SrcEval returns a result of the shape (type preservation for SrcEval).
2. **[`IxCC/Compiler/Proof.lean`](../IxCC/Compiler/Proof.lean), [`IxCC/Recheck/Proof/Soundness.lean`](../IxCC/Recheck/Proof/Soundness.lean) & [`IxCC/Recheck/Proof/Sound.lean`](../IxCC/Recheck/Proof/Sound.lean)**
   - Top-level compiler composition theorems: `Compiler.compile_sound`, `Recheck.compile_sound`, `Recheck.compile_safe`, `Recheck.compileWithContracts_sound`, `Recheck.sound`, and `Recheck.sound_of_eval` (with inductive tree observation via `Rt.treeTagify` on the immortal path and `Rt.Rc.Procs.Readback.treeView` on the RC path, backed by `Rt.readback` and `toFir_liveFuel`).
3. **[`IxCC/Recheck/Rc/Proof/ObjectSound.lean`](../IxCC/Recheck/Rc/Proof/ObjectSound.lean) & [`IxCC/Recheck/Rc/Proof/Reentry.lean`](../IxCC/Recheck/Rc/Proof/Reentry.lean)**
   - `RcReplay.sound` and `RcReplay.object_refines`: End-to-end single-call soundness of the plain reference-counted native pipeline (`Own.Plain` $\to$ `Cfg.Rc.Native` $\to$ `Rt.Rc` $\to$ `X86`) from a fresh `cx_init`.
   - `recycled_session`: Lir-level multi-call heap-recycling theorem proving that across sequential source-succeeding `Fir.litArgs` calls and `cx_drop` releases (`Lir.eval`), freed heap blocks placed on the intrusive free lists are safely recycled and preserve functional equivalence up to explicit `.resource` exhaustion. Machine-level multi-call trace invariants (`runCalls_validTrace`) are formalized separately in [`IxCC/X86/DriverSession.lean`](../IxCC/X86/DriverSession.lean) and [`IxCC/X86/Proof/DriverSession.lean`](../IxCC/X86/Proof/DriverSession.lean).
4. **[`IxCC/Ring0.lean`](../IxCC/Ring0.lean) & [`IxCC/Ring0/Proof.lean`](../IxCC/Ring0/Proof.lean)**
   - Formalizes Ring-0 certified-compilation admission and model-level Software-Isolated Process (SIP) frame invariants (see explicit assumptions in the `IxCC.Ring0` module documentation for unmodeled CPL0 hardware hazards including interrupts/IST, hardware exceptions, page-table walks, MMIO, and speculation):
     - `X86.Mnemonic.all_unprivileged`, `op_rows_no_privileged_opcode` & `stream_check_cfi`: Shows that the 31 `Mnemonic` constructors in the emitter/decoder vocabulary exclude privileged mnemonics, that none of the 243 `Op` rows uses a privileged opcode (`syscall`/`sysret`/`hlt`/`cli`/`sti`/`lgdt`/`lidt`/`ltr`/`wrmsr`/`rdmsr`), and that `Stream.check` enforces `.D32` direct relative branch offsets and `.text` bounds (`ByteEval.step` requires `rip` within `.text`; `ret` pops its return address from the stack).
     - `session_runCalls_preserves_unmapped`, `text_preserved_of_canonicalOk`, and `kernelTablesPreserved_of_session_runCalls`: Conditional model-level frame preservation theorems showing that runs succeeding under `Driver.Ok` / `CanonicalOk` preserve bytes outside `D.mapped` (including disjoint `KernelPageTables` word regions).
     - `verifyRing0Sip_sound`, `verifyBytesRing0Sip_sound`, `multi_sip_frame`, and `pairwiseDisjointSips_frame`: Concrete artifact-witness admission theorems and conditional disjoint-driver frame non-interference in the byte-memory model (the frame theorems assume every run returns `.ok` and hold for any object under a canonical driver).
     - `admittedRing0Sip_call_not_goesWrong` and `admittedRing0Sip_call_frame`: what admission adds, for one call from `cx_init` on an input where the source does not go wrong: the call never faults in the model, so its byte runs leave every byte outside the writable map unchanged at every clock.

---

### Step 2: Trusted Computing Base (TCB) & Axiom Fences

Verify the axiom footprint and specification boundaries of `IxCC`:

1. **Axiom Discipline & Supply-Chain Fences**:
   - **Program-level soundness theorems** (`Recheck.sound`, `RcReplay.sound`, `verifyProgram_*_sound`, `verifyRing0Sip_sound`, `recycled_session`) depend **only** on the 3 standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
   - **Byte-level soundness theorems** that call `Recheck.ingress` (`verifyBytes_*_sound`, `verifyBytesRing0Sip_sound`, `Compiler.compile_sound`, `Recheck.compileWithContracts_sound`, `checkClaim_ok_iff`) depend on the same three axioms: every address IxCC computes is pure BLAKE3, so none reaches the Blake3 package's `native_decide` length proof ([`docs/compile-boundary.md`](compile-boundary.md)).
   - Zero `sorry` and zero `native_decide` in `IxCC/`.
   - [`IxCCTests/Fences.lean`](../IxCCTests/Fences.lean) (aggregating [`IxCCTests/Fences/Front.lean`](../IxCCTests/Fences/Front.lean), [`IxCCTests/Fences/BackHalf.lean`](../IxCCTests/Fences/BackHalf.lean), [`IxCCTests/Fences/Compile.lean`](../IxCCTests/Fences/Compile.lean), [`IxCCTests/Fences/OwnPlain.lean`](../IxCCTests/Fences/OwnPlain.lean), [`IxCCTests/Fences/RcPromotion.lean`](../IxCCTests/Fences/RcPromotion.lean), [`IxCCTests/Fences/X86.lean`](../IxCCTests/Fences/X86.lean), etc.): 5,606 exact `#guard_msgs in #print axioms` assertions, counted and digested in [`nix/ci-coverage.json`](../nix/ci-coverage.json) and checked by `.lake/build/bin/check-build-graph`.
   - [`docs/trusted-externs.json`](trusted-externs.json) and [trusted-extern-ledger.md](trusted-extern-ledger.md): Enforced by `.lake/build/bin/check-trusted-externs`.
2. **Top of the TCB (Source Semantics & Ixon Ingress)**:
   - [`IxCC/Src/Semantics.lean`](../IxCC/Src/Semantics.lean) & [`IxCC/Src/Ingress.lean`](../IxCC/Src/Ingress.lean): `Src.Ingress.ofEnv` and the big-step operational semantics `SrcEval` on `a.src` form the top of the trusted specification boundary (source adequacy against `Ix.Kernel`'s model remains open; see [compile-boundary.md](compile-boundary.md)).
   - [`IxCC/Ixon/V3/Typed.lean`](../IxCC/Ixon/V3/Typed.lean), [`IxCC/Src/Table/Check.lean`](../IxCC/Src/Table/Check.lean), and [`IxCC/Ixon/V3/Resource/Check.lean`](../IxCC/Ixon/V3/Resource/Check.lean): Decoded Ixon v4 typing (`Tc.checkEnv`), equation/csimp validation with standard-axiom closure checks, and resource-checker validation.
3. **Bottom of the TCB (x86-64 Machine Model, Decoder, ELF Validator & Silicon Validation)**:
   - [`IxCC/X86/Eval.lean`](../IxCC/X86/Eval.lean), [`IxCC/X86/ByteEval.lean`](../IxCC/X86/ByteEval.lean), [`IxCC/X86/Decode.lean`](../IxCC/X86/Decode.lean), [`IxCC/X86/Encode.lean`](../IxCC/X86/Encode.lean), [`IxCC/X86/EncodeK.lean`](../IxCC/X86/EncodeK.lean), [`IxCC/X86/Table/Op.lean`](../IxCC/X86/Table/Op.lean), and [`IxCC/X86/Table/Rows.lean`](../IxCC/X86/Table/Rows.lean): The 243-row (31-mnemonic) x86-64 ISA specification, encoder-to-decoder roundtrip theorems (`Encode.row_decode`, `instruction_decode`, `terminator_decode`, `Decode.memory_canonical`), flag/width semantics, and `@[csimp] theorem encodeK_csimp : @encodeK = @encode` (tracked in `docs/trusted-externs.json` `csimp_theorems` so compiled native execution runs the linear array-backed `Encode.encode` while kernel evaluation runs `Encode.encodeK`).
   - [`IxCC/X86/Driver.lean`](../IxCC/X86/Driver.lean), [`IxCC/X86/ELF.lean`](../IxCC/X86/ELF.lean), [`IxCC/X86/ELFRead.lean`](../IxCC/X86/ELFRead.lean), and [`IxCC/X86/ELFValidate.lean`](../IxCC/X86/ELFValidate.lean): Machine execution driver (`Driver.Ok`, `Driver.CanonicalOk`) and per-output ELF64 `.o` translation validation (`ELF.writeChecked`, `ELF.check_sound`).
   - [`IxCCTests/Scripts/CheckX86Hardware.lean`](../IxCCTests/Scripts/CheckX86Hardware.lean): Differential hardware harness (`check-x86-hardware`) verifying agreement between the formal `IxCC.X86` semantics and host x86-64 silicon across generated instruction/state vectors (plus `llvm-mc` decoding).

---

### Step 3: The Produce-and-Recheck Split (`Recheck` vs `Produce`)

Inspect how `IxCC` separates certificate generation from verified checking:

- **Zero-RC / Immortal Checker & Producer**:
  - [`IxCC/Recheck/Run.lean`](../IxCC/Recheck/Run.lean) (`Recheck.run`) and [`IxCC/Recheck.lean`](../IxCC/Recheck.lean) (`Recheck.runWithContracts`) vs. [`IxCC/Recheck/Produce.lean`](../IxCC/Recheck/Produce.lean).
- **Plain-RC Replay Checker & Automatic Policy Selector**:
  - [`IxCC/Recheck/Rc/Replay.lean`](../IxCC/Recheck/Rc/Replay.lean) (`RcReplay.run`), [`IxCC/Own/Plain/Check.lean`](../IxCC/Own/Plain/Check.lean) (`selectRcPolicy`), and [`IxCC/Recheck/Rc/Produce.lean`](../IxCC/Recheck/Rc/Produce.lean) (`RcReplay.produce`, `selectRcPolicyForSrc`).
- **CLI Entry Point**:
  - [`IxCC/Cli.lean`](../IxCC/Cli.lean) and [`IxCC/Cli/Main.lean`](../IxCC/Cli/Main.lean) (`compile` with `--rc auto|on|off`, and `check-cert`, which takes the policy from the certificate and refuses `--rc`).

---

### Step 4: Middle-End & Backend Compiler Passes

1. **Ownership & Reference Counting (`Own.Plain` $\to$ `Cfg.Rc` $\to$ `Rt.Rc`)**:
   - [`IxCC/Own/Plain/Syntax.lean`](../IxCC/Own/Plain/Syntax.lean): Ownership lowering (`lowerCode`), syntactic immediate & projection RC elision (`imm`, `isImmRhs`, `nextImm`), and terminal move-transfer (`transferActions`).
   - [`IxCC/Own/Plain/Check.lean`](../IxCC/Own/Plain/Check.lean): Static zero-RC policy selector (`zeroRcProgram`, `selectRcPolicy`, called by `Own.Plain.selectRcPolicyForSrc` in [`IxCC/Recheck/Rc/Produce.lean`](../IxCC/Recheck/Rc/Produce.lean) on `enrichFirContracts src P`) and ownership domain checks (`checkPlainMap`, `checkContractPlainMap`). When `.zeroRc` is selected, or when `RcReplay.produceAuto` (and so `--rc auto`, `CompileClaim.produce` and `makeClaim`) falls back to `.immortal` because `selectRcPolicyForSrc` returned `.plainRc` but the plain-RC certificate could not be produced or its replay refused it (for example on a program outside `programDomain P`), compilation lowers via the immortal backend (`Own.immortal`) without runtime RC operations; the fallback's claim binds the `.immortal` policy.
   - [`IxCC/Cfg/Rc/Native.lean`](../IxCC/Cfg/Rc/Native.lean), [`IxCC/Cfg/Rc/Public.lean`](../IxCC/Cfg/Rc/Public.lean), and [`IxCC/Rt/Rc/Procs.lean`](../IxCC/Rt/Rc/Procs.lean): Native CFG splicing, narrowed caller-saved clobber sets (`Layout.clobbers`: `.r8, .r9, .r10` are preserved across `inc`/`dec` and arity $\le 2$ `allocWrapper` helpers, while arity 3–5 wrappers clobber `.r8`, `.r8/.r9`, and `.r8/.r9/.r10` respectively, verified by `Stacking.run`), and synthesized `inc`/`dec`/free-list `allocWrapper` procedures.
2. **Lambda Erasure & ANF Optimization**:
   - [`IxCC/Lam/Erase/Term.lean`](../IxCC/Lam/Erase/Term.lean): Unboxed single-field structure `casesOn` erasure.
   - [`IxCC/Anf/Walk.lean`](../IxCC/Anf/Walk.lean) & [`IxCC/Anf/Proof/Walk/Prog.lean`](../IxCC/Anf/Proof/Walk/Prog.lean): Verified multi-use local `.fn`, non-recursive higher-order global, and CPS matcher $\beta$-inlining + literal folding + `caseOfCase` commutation (`caseOfCase := 512`), with bounded shrink/inline rounds (there is no common-subexpression rule).
3. **Runtime Arithmetic Lowering & Register Allocation (`Rt` $\to$ `Xv`)**:
   - [`IxCC/Rt/Lower.lean`](../IxCC/Rt/Lower.lean) & [`IxCC/Rt/Proof/OpsDiv.lean`](../IxCC/Rt/Proof/OpsDiv.lean): Tagged word representation (`2n + 1` scalars, 8-byte aligned heap pointers) and arithmetic fast paths (`divMod` by 1, 2, 4; `natMul` by 2, 3 via `lea` and squaring).
   - [`IxCC/Xv/Alloc/LinearScan.lean`](../IxCC/Xv/Alloc/LinearScan.lean) (untrusted allocator with `crossCallOrder` and non-interfering stack spill-slot reuse) and [`IxCC/Xv/Validate/Check.lean`](../IxCC/Xv/Validate/Check.lean) (verified validator via `Validate.program_sound`, keeping `LinearScan` outside the TCB).
   - [`IxCC/Xv/Stacking/Frame.lean`](../IxCC/Xv/Stacking/Frame.lean) & [`IxCC/Xv/Stacking/Emit.lean`](../IxCC/Xv/Stacking/Emit.lean): Callee-saved register framing (`FrameLayout.check`), software stack-budget guards, and x86-64 emission.

---

## 3. Component Summary (`jcb/ixck-ixcc-merge`)

The changes on `jcb/ixck-ixcc-merge` span eight functional areas:

1. **Structure Projection Resource Rules**
   - Structural projection rules (`ProjectionInfo`, `Field.binders`) in `Ix/Resource/*` and `IxCC/IxCC/Ixon/V3/Resource/*`.
2. **Single-Field Unboxing & ANF Walk Optimizations**
   - Single-field `casesOn` unboxing in `Lam.Erase`, `.box` specialization, multi-use/HO/CPS matcher $\beta$-inlining, and `caseOfCase := 512`.
3. **Arithmetic Fast Paths, Tree Observation & Clobber-Aware `LinearScan`**
   - Tagged arithmetic fast paths in `Rt.Lower`, `Rt.treeTagify` / `Rt.Rc.Procs.Readback.treeView` root tree observation, and `crossCallOrder` + spill-slot reuse in `LinearScan`.
4. **Expanded 243-Row x86-64 ISA & `DriverSession`**
   - 38 additional x86-64 instruction rows (`mul`, `not`, `neg`, `mov .w8/.w16`, `movzx .w64`, `movsx`, `movsxd`, `bswap`, `rol`, `ror`), `Decode.memory_canonical`, `Driver.CanonicalOk`, and `runCalls_validTrace`.
5. **Ownership Lowering, Zero-RC Policy Selection & Narrowed RC Clobbers**
   - `Own.Plain` contract-domain checking (`checkContractPlainMap`), static zero-RC policy selection (`zeroRcProgram`), terminal move-transfer (`transferActions`), `.prim`/`.proj` immediate RC elision (`imm`), and narrowed RC runtime clobbers.
6. **Single-Pass `RcReplay.produce`, `--rc auto|on|off`, `recycled_session` & `Compiler.Proof`**
   - Single-pass `RcReplay.produce`, automatic RC policy selection with immortal fallback, Lir-level multi-call heap-recycling session soundness (`recycled_session`), and top-level `Compiler.Proof` theorems.
7. **`CompileClaim` (Tag 13) & Byte-Level ELF64 Soundness Theorems**
   - `CompileClaim` in `Ix/Claim.lean` and program/byte-level ELF64 verification and soundness theorems in `IxCC/CompileClaim.lean` and `IxCC/CompileClaim/Proof.lean`.
8. **Ring-0 Admission & Model-Level Multi-SIP Frame Preservation**
   - Ring-0 admission (`verifyRing0Sip_sound`, `verifyBytesRing0Sip_sound`), disjoint word-region preservation (`kernelTablesPreserved_of_session_runCalls`), and model-level multi-SIP frame non-interference (`multi_sip_frame`) in `IxCC/Ring0.lean`, `IxCC/Ring0/Proof.lean`, and `IxCCTests/Ring0.lean`.

---

## 4. Verification Commands

These are the commands of IxCC's 16 required checks, as [`nix/checks.nix`](../nix/checks.nix) runs them; `nix build .#checks.x86_64-linux.ixcc-<name>` from ix's root runs one hermetically (see [ci.md](ci.md)). From `IxCC/`, in ix's development shell (`nix develop`). `--native` runs the suites' objects natively, as test executables IxCC writes (x86-64 Linux only; without it the suites run every Lean level and skip the native runs); `CC` is a C compiler, which only `x86-elf-object` (the C test harnesses and the system linker's acceptance of compiled objects) and `x86-hardware` use, and `LLVM_MC` an `llvm-mc` binary (see `x86-hardware` below). `rc-native` and `x86-hardware` are x86-64 Linux only. `ixcc compile CLOSURE.ixe --equations EQ.json --exe FILE` writes a standalone executable of the first root (`FILE N1 … Nk` prints its result); `tests-exe` and `tests-corpus --exe` test it. With `--machine` the first root is a numeric state machine (a step `Nat → Nat → Nat`) run by the generic request shell, and `FILE ARG…` runs the session whose parsing and rendering the program does in Lean (`lib/IxccExe.lean`); `tests-exe` tests it with the `phase1-machines` family.

```bash
# build, proofs: the library, every executable, and the complete proof and fence collection
# (IxCCTests imports IxCCTests.Proofs, so building it checks every exact axiom fence)
lake build IxCC IxCCTests ixcc \
  tests-ixon-v3 check-ixon-v3 check-ixon-v3-catalog census tests-aiur check-aiur \
  check-x86-encoder check-x86-bytes check-x86-streams check-x86-object x86-object-fixture \
  check-trusted-externs check-tools-tests check-build-graph check-steps check-x86-hardware \
  tests-rt-rc tests-cfg-rc tests-driver-session tests-pipeline-rc tests-rc-certificate \
  tests-pipeline corpus certified-census tests-corpus tests-exe check-backend check-regalloc tests-src src-steps \
  tests-rt check-xv-select tests-lam tests-fir check-lir tests-anf tests-own tests-own-plain \
  tests-shrink tests-relevance tests-recheck tests-recheck-readback \
  gen-src-artifacts gen-recheck-artifacts
bin=.lake/build/bin

# ixon-v3
$bin/tests-ixon-v3
$bin/check-ixon-v3 fixtures/ixon-v4/handoff/accepted.ixe fixtures/ixon-v4/handoff/profile.bin \
  fixtures/ixon-v4/handoff/accepted.claim
$bin/check-ixon-v3-catalog fixtures/ixon-v4/catalog/fat.ixc
$bin/check-ixon-v3-catalog fixtures/ixon-v4/catalog/chunked.ixc fixtures/ixon-v4/catalog/chunked.ixc/members.json

# census: each report must equal its reviewed baseline
$bin/census fixtures/ixon-v4/k1/k1.ixe --names fixtures/ixon-v4/k1/equations.json --out census.json
diff -u fixtures/ixon-v4/k1/census.json census.json
for name in fib sum-loop ackermann tak gcd; do
  $bin/census fixtures/ixon-v4/bench-k1/$name.ixe \
    --names fixtures/ixon-v4/bench-k1/$name.equations.json --out $name.census.json
  diff -u fixtures/ixon-v4/bench-k1/$name.census.json $name.census.json
done

# aiur
$bin/tests-aiur
$bin/check-aiur --root .

# x86-encoder-decoder, x86-byte-execution, x86-stream-objects, x86-elf-object
$bin/check-x86-encoder --objdump "$(command -v objdump)"
$bin/check-x86-bytes
$bin/check-x86-streams
# (--cc, --harness and --ixcc: x86-64 Linux only: the fixtures linked with the C harnesses
# and run, and objects ixcc compiles in the check linked, not run, by the system linker)
$bin/check-x86-object --fixture $bin/x86-object-fixture --readelf "$(command -v readelf)" \
  --objdump "$(command -v objdump)" --cc "$CC" --harness fixtures/x86/native_harness.c --ixcc $bin/ixcc

# trusted-extern-ledger (the integrity pins, required-check inventory, hygiene scan and
# other inventories of the trust ledger), and the auditor's own rejection paths
$bin/check-trusted-externs
$bin/check-tools-tests

# build-graph: the module manifest, import hygiene, and the proof and fence inventory
$bin/check-build-graph --root .

# rc-runtime
mkdir -p rc-logs
$bin/tests-rt-rc controls
$bin/tests-rt-rc deep
$bin/tests-cfg-rc
$bin/tests-driver-session
$bin/tests-pipeline-rc levels rc-logs/levels
$bin/tests-pipeline-rc counters rc-logs/counters

# rc-native (x86-64 Linux)
$bin/tests-rt-rc native rc-logs/runtime
$bin/tests-rc-certificate fresh rc-logs/certificate
$bin/tests-pipeline-rc native rc-logs/levels-native
$bin/tests-pipeline-rc negative rc-logs/negative

# suites (the check runs these concurrently; each must exit 0)
$bin/tests-pipeline --native
$bin/corpus check
$bin/certified-census --self-test
$bin/tests-corpus --native --exe        # (--exe: x86-64 Linux only, runs the corpus as executables)
$bin/tests-exe --run --strace "$(command -v strace)"   # (--run and --strace: x86-64 Linux only)
$bin/check-backend --native
$bin/check-regalloc
$bin/tests-src
$bin/tests-rt --native
$bin/check-xv-select
$bin/tests-lam
$bin/tests-fir
$bin/check-lir
$bin/tests-anf
$bin/tests-own --native
$bin/tests-own-plain
$bin/tests-shrink
$bin/tests-relevance
$bin/tests-recheck
$bin/tests-recheck-readback
$bin/gen-src-artifacts --check
$bin/gen-recheck-artifacts --check
$bin/corpus kernel-artifacts --check

# x86-steps
$bin/check-steps

# x86-hardware (x86-64 Linux). LLVM_MC is an llvm-mc binary: ix's development shell does not put
# one on PATH; the Nix check uses nixpkgs' llvmPackages.llvm (its bin/llvm-mc).
"$CC" -O1 -o hw_diff_harness fixtures/x86/hw_diff_harness.c
$bin/check-x86-hardware --harness ./hw_diff_harness --llvm-mc "$LLVM_MC"
```

The Nix checks run these against the tracked source tree in the store and write their outputs (`census.json`, `rc-logs/`, `hw_diff_harness`) in the build directory; run locally, they write them in `IxCC/`.
