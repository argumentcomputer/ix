import IxCCCorrect.Claim
import IxCCCorrect.Process
import IxCC.Recheck.Produce
import IxCCGrounding.Syntax
import IxCK.Kernel.Denotes

/-!
# `Correct`: the proposition a claim states (`IxCCCorrect.Tiers`)

`Correct claim envBytes exe` is the one proposition a consumer learns from an
accepted argument. Its subjects are public data only: the claim, the bytes of
the committed environment and the bytes of the shipped file. No program of
IxCC's, no certificate and no intermediate image occurs in it.

**The bytes are arguments, not hashes.** The claim carries digests
(`Claim.env`, `Claim.exeCore`); the proposition speaks about bytes, and
`Claim.Binds` and `Admits` say that those bytes have the claim's digests. A
hypothesis that BLAKE3 has no collisions would be refutable in Lean (there are
more byte strings than addresses), so any theorem under it would be vacuous; and
"some collision exists" is provable outright, so it cannot be a useful disjunct
either. The step from "some bytes with this digest are correct" to "the bytes I
hold are correct" is a computational argument about the hash, made outside Lean.

**Kernel meaning is denotation in every model.** The meaning of the constant at
`claim.target` is taken from the certified kernel's own statement
(`Ix.Kernel.Model`, `Ix.Kernel.Denotes`): the kernel admits the committed
environment (`Admits`, the tiered entry over the whole environment), and in every
model of the environment it installed, over every set theory, the target applied
to the arguments and the answer denote the same set (`SameDenotation`). This is
what the grounding library proves about IxCC's evaluator and what the kernel's
main theorem gives a model for. Two costs, both stated in the design note: the
quantifier ranges over models, so the clause says nothing unless a set theory
with the kernel's universe chain exists (the standing assumption of the
kernel's own consistency theorem, not provable in Lean); and it is a statement
of semantic validity, not of what the kernel's reduction computes.

## The three tiers

* `Tier1` (functional): on every finite trace, standard output is a prefix of the
  rendering of an answer that agrees with the kernel meaning, and a trace that
  exits with status 0 has written all of it. No hypothesis on any source
  evaluator.
* `Tier2` (safety): on every finite trace, every system call is in the envelope,
  no state is one where the processor's specification promises nothing, and no
  byte outside the file's zero-filled segments is changed.
* `Tier3` (termination and resources): the process has no infinite run and no
  silent death, stays within the bounds the claim states, and every run that ends
  ends with the answer, a refused invocation, a call the environment refused, or
  the report of a limit the claim leaves open. `Tier3Transitional` also excuses
  the 63-bit `Nat` report of today's code.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.Grounding (KEnv KKey KExpr litE)

/-! ## Kernel meaning -/

/-- The key the kernel's reader gives the constant at an address
(`Ix.Kernel.Reader.Ctx.keyAt`): its role's key where the table binds it,
otherwise the key of the address. -/
def keyOf (acc : Src.KernelFront.Accepted) (a : Ixon.Address) : Option KKey :=
  (acc.ctx.keyAt (Src.KernelFront.kaddr a)).toOption

/-- **The certified kernel admits the committed environment.** `envBytes` decodes
(every constant and blob under its address, the root the canonical Merkle root of
the constants: `Ixon.V3.decodeAnonymousEnv`), has the claim's root and role table,
and the kernel's tiered entry accepts it at the claim's limits, with result `acc`
(`Src.KernelFront.accept`, a function of the decoded environment). `acc.env` is
the logical environment the kernel installed; it has a model in every set theory
(`Ix.Kernel.Admission.checkBytesTiered_has_model`). The claim's target resolves:
the kernel's reader keys a constant at it (`keyOf`; owner-approved P4: a target the
reader cannot key, a block member whose projection record the bytes omit, is refused
here rather than making `Agrees` unsatisfiable). -/
def Admits (claim : Claim) (envBytes : ByteArray) (acc : Src.KernelFront.Accepted) : Prop :=
  ∃ env, Ixon.V3.decodeAnonymousEnv envBytes = .ok env ∧
    env.root = claim.env ∧
    env.bindingAddress = some claim.roleTable ∧
    Src.KernelFront.accept env claim.kernelLimits = .ok acc ∧
    keyOf acc claim.target ≠ none

/-- **Two kernel terms denote the same set in every model** of `kenv`, over every
set theory, at every level assignment and variable environment; and they do
denote. -/
def SameDenotation.{w} (kenv : KEnv) (e₁ e₂ : KExpr) : Prop :=
  ∀ (V : Type w) [Ix.Kernel.SetTheory V] (M : Ix.Kernel.Model V kenv)
    (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
    ∃ X, Ix.Kernel.Denotes M.cval kenv φ ρ e₁ X ∧ Ix.Kernel.Denotes M.cval kenv φ ρ e₂ X

/-- The kernel term of an answer: a `Nat` literal, or the enumeration's constructor
at the printed index, by the address the claim lists. -/
def answerTerm (abi : Abi) (key : Ixon.Address → Option KKey) (answer : Nat) : Option KExpr :=
  match abi.result with
  | .nat => some (litE answer)
  | .enum ctors => ((ctors[answer]?).bind key).map fun k => Ix.Kernel.Expr.const k []

/-- **The answer agrees with the kernel meaning of the target**: in every model of
the admitted environment, the target applied to the arguments (as literals)
denotes what the answer's term denotes. -/
def Agrees.{w} (claim : Claim) (acc : Src.KernelFront.Accepted) (xs : List Nat) (answer : Nat) :
    Prop :=
  ∃ target out, keyOf acc claim.target = some target ∧
    answerTerm claim.abi (keyOf acc) answer = some out ∧
    SameDenotation.{w} acc.env
      (Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.const target []) (xs.map fun n => (litE n : KExpr)))
      out

/-! ## The file is laid out as the claim says -/

/-- The file's zero-filled loadable segments are exactly the stack and the region
of the claim's sizes (`X86.Exe.Layout.segments`), and the sizes are ones the
writer accepts. This is what makes `Resources.stack` and `Resources.region`
statements about the file. -/
def LayoutIs (claim : Claim) (exe : ByteArray) : Prop :=
  claim.layout.check = true ∧
  ∃ view, Read.parse exe = some view ∧
    ((view.programs.filter fun ph => ph.kind == 1 && ph.fileSize == 0).map
      fun ph => (ph.address, ph.memorySize)) = claim.layout.segments

/-! ## Tier 1: functional correctness -/

/-- **Tier 1.** The kernel admits the committed environment, and for every
invocation, every loader state and every finite trace of the shipped file:

* standard output is empty, or is a prefix of the rendering of an answer to the
  arguments the invocation denotes, and that answer agrees with the kernel
  meaning of the target;
* if the trace ends with `exit 0`, standard output is the whole rendering of such
  an answer.

There is no source evaluator and no "source goes wrong" case: a file that writes
anything else to standard output on any input, from any loader state, falsifies
it. Failures are not constrained here (see `Tier3`). -/
def Tier1.{w} (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  ∃ acc, Admits claim envBytes acc ∧
    ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → ∀ σ, FileTrace exe s₀ σ →
      (stdout σ = [] ∨
        ∃ xs answer, claim.abi.parse args = some xs ∧
          stdout σ <+: claim.abi.render answer ∧ Agrees.{w} claim acc xs answer) ∧
      (exitStatus σ = some 0 →
        ∃ xs answer, claim.abi.parse args = some xs ∧
          stdout σ = claim.abi.render answer ∧ Agrees.{w} claim acc xs answer)

/-! ## Tier 2: safety -/

/-- The system calls a calling convention's executable may make. A convention that
reads standard input adds `read` here (and to `Process.Syscall`). -/
def Abi.sysAllowed (abi : Abi) : Sys → Prop :=
  match abi.convention with
  | .argvDecimal => SysAllowed

/-- **Tier 2.** For every invocation and every loader state of the shipped file,
with no hypothesis on the source:

* every system call of every finite trace is in the envelope of the claim's
  calling convention (`Abi.sysAllowed`, `SysAllowed`);
* no reachable state is one where the processor's specification promises nothing
  (`Process.Unspecified`: outside the decoded instruction set, outside the mapped
  file, or a branch on an undefined flag);
* no reachable state has changed a byte outside the file's zero-filled segments
  (`Kept`).

The second clause follows from the first (`Process.Run.other_of_unspecified`); it
is stated because it is the one a reader looks for. -/
def Tier2 (claim : Claim) (exe : ByteArray) : Prop :=
  ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ →
    (∀ σ, FileTrace exe s₀ σ → ∀ e ∈ σ, claim.abi.sysAllowed e) ∧
    (∀ σ s, FileRun exe s₀ σ s → ¬ Unspecified (execImage exe) s ∧ Kept exe s₀ s)

/-! ## Tier 3: termination and resources -/

/-- The exit status that goes with a shell message. -/
def statusOf (m : X86.Exe.Message) : Word := UInt64.ofNat m.status

/-- **How a run may end.** With exit status `c`:

* `0`, with the whole rendering of an answer that agrees with the kernel meaning;
* the usage statuses, for an invocation that denotes no arguments (or with no
  arguments at all: `Process.ArgBlock` does not distinguish `argc = 0` from an
  empty argument list);
* the write-failed or confinement-refused status, when the environment refused a
  call;
* the heap or stack report, only where the claim states no bound for it;
* a status `excused` names (none in `Tier3`).

Not among them: the `natOverflow`, `trap`, `abi` and `notValue` reports. -/
def Ending.{w} (excused : Word → Prop) (claim : Claim) (acc : Src.KernelFront.Accepted)
    (args : List (List Nat)) (σ : List Sys) : Prop :=
  ∃ c, exitStatus σ = some c ∧
    ((c = 0 ∧ ∃ xs answer, claim.abi.parse args = some xs ∧
        stdout σ = claim.abi.render answer ∧ Agrees.{w} claim acc xs answer) ∨
     ((claim.abi.parse args = none ∨ args = []) ∧
        (c = statusOf .count ∨ c = statusOf .numeral) ∧ stdout σ = []) ∨
     ((c = UInt64.ofNat X86.Exe.writeFailed ∨ c = statusOf .confine) ∧ EnvRefused σ) ∨
     (c = statusOf .heap ∧ claim.resources.heapBound = none) ∨
     (c = statusOf .stack ∧ claim.resources.stackBound = none) ∨
     excused c)

/-- **The bounds the claim states are kept**: with `stackBound = some B`, no byte of
the stack segment more than `B` below the program stack's top is written; with
`heapBound = some H`, no byte of the region past its first `H` is written. -/
def WithinBounds (claim : Claim) (s₀ s : ByteEval.State) : Prop :=
  (∀ B, claim.resources.stackBound = some B →
    Untouched X86.Exe.dataBase (claim.layout.stackTop - B) s₀ s) ∧
  (∀ H, claim.resources.heapBound = some H →
    Untouched (claim.layout.regionStart + H) (claim.layout.regionStart + claim.layout.regionArea) s₀ s)

/-- Tier 3 with a set of excused exit statuses (`Tier3` and `Tier3Transitional`). -/
def Tier3With.{w} (excused : Word → Prop) (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  ∃ acc, Admits claim envBytes acc ∧
    ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → Mapped exe args s₀ →
      Acc (Next (execImage exe)) s₀ ∧
      (∀ σ s, FileRun exe s₀ σ s → CanStep (execImage exe) s ∧ WithinBounds claim s₀ s) ∧
      (∀ σ, Ended (execImage exe) s₀ σ → Ending.{w} excused claim acc args σ)

/-- **Tier 3.** The kernel admits the committed environment, and for every
invocation and every loader state whose mappings are as the file's headers ask
(`Mapped`):

* the process has no infinite run (`Acc`), whatever the platform answers;
* it never dies silently: every reachable state has a step (`CanStep`), so every
  maximal run ends with a system call that ends the process;
* every reachable state keeps the bounds the claim states (`WithinBounds`);
* every run that ends, ends as `Ending` allows.

For a claim with both bounds (`Tier3Bounded`: roots carrying `@[no_alloc]` and
`@[bounded_stack]`) this is total correctness: on every well-formed invocation
the process prints the answer and exits 0 unless the environment refuses a
call. For a claim with a bound left open it permits the honest report of that
limit, and says nothing about when the limit is reached (`Tier3Tight`). -/
def Tier3.{w} (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  Tier3With.{w} (fun _ => False) claim envBytes exe

/-- **The restricted version**: both bounds stated, so no resource report is a
permitted ending. -/
def Tier3Bounded.{w} (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  claim.resources.stackBound.isSome = true ∧ claim.resources.heapBound.isSome = true ∧
    Tier3.{w} claim envBytes exe

/-- **The transitional version**, for code whose `Nat` is a 63-bit immediate: the
`natOverflow` report (status 67) is an excused ending, on any input. It is not a
tier of `Correct`: a claim cannot state it. It is what today's architecture can
meet once the other links of tier 3 are in place, and `Tier3` is what it becomes
when the overflow branch calls the arbitrary-precision library instead of
failing. -/
def Tier3Transitional.{w} (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  Tier3With.{w} (fun c => c = statusOf .natOverflow) claim envBytes exe

/-- **The general version, as a schema.** `need xs` is the stack and the heap, in
bytes, that the computation on `xs` needs. With it, a limit is reported only when
the need exceeds what the file reserves, so "if the stated budgets suffice, every
maximal trace ends in the answer" follows. The schema is not a tier because no
public `need` exists yet: it has to be a function of the committed environment,
the target and the claim (a cost semantics of the reference evaluator, with the
frame sizes the claim would then have to export), not of the certificate. -/
def Tier3Tight.{w} (need : List Nat → Nat × Nat) (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  Tier3.{w} claim envBytes exe ∧
  ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → Mapped exe args s₀ →
    ∀ σ, Ended (execImage exe) s₀ σ → ∀ xs, claim.abi.parse args = some xs →
      (exitStatus σ = some (statusOf .stack) → claim.resources.stack < (need xs).1) ∧
      (exitStatus σ = some (statusOf .heap) → claim.resources.region < (need xs).2)

/-! ## `Correct` -/

/-- **`Correct claim envBytes exe`**: the file is laid out as the claim says, and
each tier the claim states holds. -/
def Correct.{w} (claim : Claim) (envBytes exe : ByteArray) : Prop :=
  match claim.platform with
  | .x86_64Linux =>
    LayoutIs claim exe ∧
    (claim.tiers.functional = true → Tier1.{w} claim envBytes exe) ∧
    (claim.tiers.safety = true → Tier2 claim exe) ∧
    (claim.tiers.total = true → Tier3.{w} claim envBytes exe)

/-- **What a consumer who holds only the claim learns**: some environment and some
file with the claim's digests are correct. With the file in hand they check
`claim.Binds` themselves; that their file is the one the argument was about is
then the collision resistance of BLAKE3. -/
def Claim.Holds.{w} (claim : Claim) : Prop :=
  ∃ envBytes exe, claim.Binds exe ∧ Correct.{w} claim envBytes exe

end IxCC.Correct
