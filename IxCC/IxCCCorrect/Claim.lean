import IxCC.CompileClaim
import IxCC.X86.Exe.Cert
import IxCC.X86.Exe.Plain.Proof.Spec

/-!
# The public claim (`IxCCCorrect.Claim`)

Everything a consumer of a compiled executable can see. The certificate that the
compiler's checker replays is a private witness, so nothing about it appears here:
what a consumer learns is one proposition, `IxCC.Correct.Correct claim env exe`
(`IxCCCorrect.Tiers`), about this structure, the committed environment's bytes and
the shipped file's bytes. **A field that `Correct` does not read constrains nothing
for the consumer**; it only narrows which witnesses the checker accepts. Each field
below says which it is.

Against today's six-field `IxCC.CompileClaim` (`env`, `roleTable`, `target`,
`policy`, `abiArity`, `elfHash`):

| Today | Here | Why it moves |
| --- | --- | --- |
| `env`, `target` | unchanged | the source: a content address in a committed environment |
| `roleTable : Option Address` | `roleTable : Address` | the certified kernel admits only role-bound environments, so `none` names no claim that can be established |
| `abiArity : Nat` | `abi : Abi` | the calling convention, the argument types and the result type; the constructors of an enumeration result by address, so `#1` on standard output names a constant |
| `elfHash` (the relocatable object) | `exeCore` (the shipped file's core) | the object is an intermediate image; nothing a consumer runs has that hash |
| `policy` | unchanged | read by the checker only |
| absent | `platform`, `resources`, `kernelLimits`, `checker`, `tiers` | were free inputs of the verifier (the layout in the file's trailer, the limits a flag, the checker implicit) |

Not in the claim, by decision: the certificate, the unfolding table, the equation
sidecar and the root names. They are witness data. That is sound only if the
table is a function of the committed environment (the canonical table); until
then they are choices the proposition does not constrain.
-/

set_option autoImplicit false

namespace IxCC.Correct

/-- The instruction set, the operating system and the file format the executable is
for. It selects the process model `Correct` is stated over; there is one today. -/
inductive Platform where
  /-- x86-64 Linux, a static `ET_EXEC` ELF64 file: the processor of
  `X86.Exe.Process.Step`, the system calls of `X86.Exe.Process.Syscall`, the loader
  of `IxCC.Correct.LoadedFile`. -/
  | x86_64Linux
  deriving DecidableEq, Repr, Inhabited

/-- The type of a root's parameter. `Nat` is Lean's `Nat`: no width. -/
inductive ArgTy where
  | nat
  /-- An argument erased at run time (a proof or a type, owner-approved P3): the claim names
  its closed kernel term, the kernel meaning applies the target to it, and the shell does not
  read it from the command line. -/
  | erased (term : Ix.Kernel.Expr .anon)
  deriving DecidableEq, Repr, Inhabited

/-- The number of `Nat` parameters: the arguments an invocation passes. -/
def ArgTy.natCount : List ArgTy → Nat
  | [] => 0
  | .nat :: ps => natCount ps + 1
  | .erased _ :: ps => natCount ps

@[simp] theorem ArgTy.natCount_replicate_nat : ∀ n : Nat, natCount (List.replicate n .nat) = n
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, natCount, natCount_replicate_nat n]

/-- The type of a root's result. -/
inductive ResTy where
  /-- Lean's `Nat`. -/
  | nat
  /-- An enumeration: its constructors by address, in the order of the index the
  executable prints. The claim lists them so that an answer names a constant of
  the committed environment without reference to the compiler's tags. -/
  | enum (ctors : List Ixon.Address)
  /-- An unsigned word of `bits` bits (owner-approved P5): the answer is its number, the
  kernel term `UIntN.ofNat` (the constant at `ofNat`) applied to that number. -/
  | word (bits : Nat) (ofNat : Ixon.Address)
  deriving DecidableEq, Repr, Inhabited

/-- How arguments reach the process and how the result leaves it. A byte-array
convention (standard input to standard output) is a second constructor here and a
second arm of `Abi.parse` and `Abi.render`; `Correct` itself does not change. -/
inductive Convention where
  /-- Each argument is one element of `argv`, a decimal numeral. The result is
  written to standard output: a `Nat` as a decimal numeral and a newline, an
  enumeration as `#`, the constructor's index in decimal and a newline. Exit status
  0 is returned exactly for a result. -/
  | argvDecimal
  deriving DecidableEq, Repr, Inhabited

/-- The application binary interface of the root. A field of the claim, read by
every tier. -/
structure Abi where
  convention : Convention := .argvDecimal
  params : List ArgTy
  result : ResTy
  deriving DecidableEq, Repr, Inhabited

namespace Abi

def arity (abi : Abi) : Nat := ArgTy.natCount abi.params

/-- The shell's rendering class of the result (`X86.Exe.ResultKind`). -/
def resultKind (abi : Abi) : X86.Exe.ResultKind :=
  match abi.result with
  | .nat => .nat
  | .enum ctors => .enum ctors.length
  | .word _ _ => .nat

/-- One argument: a non-empty string of ASCII digits, read in decimal. There is no
upper bound: the argument is a Lean `Nat`. (Today's shell refuses a numeral at or
above `2 ^ 64`, `X86.Exe.Plain.parseArgBytes`; see `Tier3Transitional`.) -/
def parseArg : List Nat → Option Nat
  | [] => none
  | b :: rest => X86.Exe.Plain.parseDigitsAux 0 (b :: rest)

/-- The arguments an invocation denotes: `none` for a wrong count or an argument
that is not a numeral. -/
def parse (abi : Abi) (args : List (List Nat)) : Option (List Nat) :=
  if args.length = abi.arity then args.mapM parseArg else none

/-- The bytes an answer is written as: a `Nat` result's value, or an enumeration
result's constructor index (`X86.Exe.Plain.renderPlain`). -/
def render (abi : Abi) (answer : Nat) : List UInt8 :=
  X86.Exe.Plain.renderPlain abi.resultKind answer

end Abi

/-- The memory the executable is given and what the claim promises about its use. -/
structure Resources where
  /-- Bytes of program stack the file reserves (`X86.Exe.Layout.stack`). Read by
  `LayoutIs`: the file's zero-filled segments are exactly these. -/
  stack : Nat
  /-- Bytes of heap region the file reserves (`X86.Exe.Layout.region`). -/
  region : Nat
  /-- `some B`: on every input the program stack stays within `B` bytes of its
  top, so stack exhaustion is not a permitted outcome (a root carrying
  `@[bounded_stack]`; `B` is the checker's stack witness at the root). `none`:
  no bound is claimed and an honest stack-exhaustion report is permitted. Read by
  `Tier3`. -/
  stackBound : Option Nat
  /-- `some H`: on every input at most the first `H` bytes of the region are
  written, so heap exhaustion is not a permitted outcome (a root carrying
  `@[no_alloc]`, with `H` the runtime context's size). `none`: no bound. Read by
  `Tier3`. -/
  heapBound : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- Which parts of `Correct` the claim states. Three independent propositions, so a
claim can state safety for a program outside the grounded fragment. The numbered
tiers of the plan are `{functional}`, `{functional, safety}` and all three. -/
structure Tiers where
  /-- Tier 1: what is written as the result agrees with the kernel meaning of the
  target. -/
  functional : Bool
  /-- Tier 2: the process stays inside its memory and system-call envelope. -/
  safety : Bool
  /-- Tier 3: the process terminates, with the answer unless a limit the claim
  leaves open is reported. -/
  total : Bool
  deriving DecidableEq, Repr, Inhabited

/-- **The public claim.** -/
structure Claim where
  /-- Merkle root of the committed environment's constants. Read by `Admits`. -/
  env : Ixon.Address
  /-- Address of the environment's role table. Read by `Admits`. -/
  roleTable : Ixon.Address
  /-- Address of the compiled constant. Read by `Agrees`. -/
  target : Ixon.Address
  /-- BLAKE3 of the shipped file's core (`coreOf`). Read by `Claim.Binds`. -/
  exeCore : Ixon.Address
  /-- Read by `Correct`: it selects the process model. -/
  platform : Platform
  /-- Read by every tier. -/
  abi : Abi
  /-- The reference-counting policy the checker replays under. **Not read by
  `Correct`**: what a policy changes for a consumer is heap use, which
  `resources.heapBound` states. -/
  policy : CompilePolicy
  /-- Read by `LayoutIs` and `Tier3`. -/
  resources : Resources
  /-- The certified kernel's batch limits. Read by `Admits`: the environment is
  admitted at these limits. The kernel can decline under one setting and accept
  under another, so a checker that is a function of public data needs them. -/
  kernelLimits : Ix.Kernel.Admission.Limits
  /-- Digest of the checker (the verifying key of its arithmetization). **Not read
  by `Correct`**: it says which function's acceptance was proved, and enters only
  the route statements (`IxCCCorrect.Routes`). -/
  checker : Ixon.Address
  /-- Read by `Correct`. -/
  tiers : Tiers

/-- The stack and region sizes as the executable writer's layout. -/
def Claim.layout (c : Claim) : X86.Exe.Layout :=
  { stack := c.resources.stack, region := c.resources.region }

/-- **The bytes of a shipped file that a claim's digest covers**: the loadable core,
with the twelve section-header pointer bytes of its ELF header zeroed, of a file
whose trailer the strict parser accepts (`X86.Exe.Cert.extractTrailer`: the page
tail after the core is `int3` bytes, and nothing but the fixed section table
follows the payload). The payload itself is not covered, so the same digest names
the file whether it carries a replay certificate or a succinct proof. -/
def coreOf (file : ByteArray) : Option ByteArray :=
  match X86.Exe.Cert.extractTrailer file with
  | .ok (coreSize, _) => some (X86.Exe.Cert.zeroShdr (file.extract 0 coreSize))
  | .error _ => none

/-- The claim names this file. Decidable, and checked by the consumer on the file
they are about to run. -/
def Claim.Binds (c : Claim) (exe : ByteArray) : Prop :=
  (coreOf exe).map Ixon.Address.blake3Pure = some c.exeCore

end IxCC.Correct
