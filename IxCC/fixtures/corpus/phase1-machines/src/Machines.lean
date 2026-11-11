/-!
# IxccExe: numeric state machines for IxCC executables

Lean source compiled *with* a program, by `ix compile` and `ixcc compile`,
into an executable that `ixcc compile --exe FILE --machine` writes. It is not
part of IxCC: IxCC compiles it like the rest of the program, so its
correctness is covered by the compiler's theorem and it adds nothing to the
trusted base. A program imports this file as the module `IxccExe` or starts
with its text (the fixture family `phase1-machines` does the latter).

## The platform interface, version 0

A machine is a root `step : Nat → Nat → Nat` of a state and an event. Its
result is one number, `result state request = state * 2048 + request`: the
next state (below `2^52`, since a `Nat` word is below `2^63`) and an 11-bit
request field, the kind in its low three bits and a byte above them:

| request | asks for | the next event |
| --- | --- | --- |
| `arg` | the next byte of the argument block (the arguments after the program's name, one after another) | the byte (1 to 255); `endOfArgument` (256) at the end of an argument; `endOfArguments` (257) when none is left |
| `out b`, `err b` | the byte `b` on standard output, standard error | `written` (0), or `notWritten` (1) if the platform refused it |
| `exit c` | the end of the process with status `c` (0 to 255) | none |

The first call gets state 0 and, as its event, the number of arguments. The
executable's shell keeps the state between calls; it parses and renders
nothing.

## `Main1`: one decimal argument, a decimal result

`Main1.step` checks the argument count (a message on standard error and
status 2), reads one or more ASCII digits (else a message and 3), and at the
end of the argument hands over to the program: `Main1.ready` is true, the
program computes `f (Main1.argument s)`, and `Main1.finish` renders the
result in decimal with a newline and exits 0. A refused write exits 74.
Arguments and results must be below `limit` (`2^48`), so that the state
stays below `2^52`: a larger one gets a message and status 67. The glue a
program writes, first order:

```lean
def fibMain (s e : Nat) : Nat :=
  bif IxccExe.Main1.ready s e then IxccExe.Main1.finish (fib (IxccExe.Main1.argument s))
  else IxccExe.Main1.step s e
```

or `IxccExe.Main1.run fib s e`, which passes `fib` as a closure (it
compiles, but to a much larger object today).

## The source's shape

Today's middle end compiles every shape correctly, but turns branches into
closures (and the program onto the plain-RC route) when the tests of one
function are nested deeply after inlining. So this file names the
primitives (`Nat.beq`, `Nat.blt`, `Nat.add`…) and branches with `bif`,
looks values up in balanced trees rather than chains, and writes
`Main1.step` as one function that computes each phase's result one after
another and then picks one by the phase (large enough that it stays a call,
so the glue's branch holds only the program's call). With this shape a
machine's step compiles to straight scalar code on the zero-RC route.
-/

namespace IxccExe

/-! ## The interface -/

/-- A step's result: the next state `s` and the request field `r`. -/
def result (s r : Nat) : Nat := Nat.add (Nat.mul s 2048) r

/-- The next byte of the argument block. -/
def arg : Nat := 0
/-- The byte `b` on standard output. -/
def out (b : Nat) : Nat := Nat.add 1 (Nat.mul 8 b)
/-- The byte `b` on standard error. -/
def err (b : Nat) : Nat := Nat.add 2 (Nat.mul 8 b)
/-- The end of the process with status `c`. -/
def exit (c : Nat) : Nat := Nat.add 3 (Nat.mul 8 c)

def endOfArgument : Nat := 256
def endOfArguments : Nat := 257
def written : Nat := 0
def notWritten : Nat := 1

/-- `Main1`'s arguments and results are below this (`2^48`). -/
def limit : Nat := 281474976710656

/-! ## Decimal -/

/-- The largest power of ten at most `p`, for `1 ≤ p < 10^16`. -/
def pow10Le (p : Nat) : Nat :=
  bif Nat.blt p 100000000 then
    bif Nat.blt p 10000 then
      bif Nat.blt p 100 then (bif Nat.blt p 10 then 1 else 10)
      else (bif Nat.blt p 1000 then 100 else 1000)
    else
      bif Nat.blt p 1000000 then (bif Nat.blt p 100000 then 10000 else 100000)
      else (bif Nat.blt p 10000000 then 1000000 else 10000000)
  else
    bif Nat.blt p 1000000000000 then
      bif Nat.blt p 10000000000 then (bif Nat.blt p 1000000000 then 100000000 else 1000000000)
      else (bif Nat.blt p 100000000000 then 10000000000 else 100000000000)
    else
      bif Nat.blt p 100000000000000 then
        (bif Nat.blt p 10000000000000 then 1000000000000 else 10000000000000)
      else (bif Nat.blt p 1000000000000000 then 100000000000000 else 1000000000000000)

/-! ## Messages

Each message as little-endian 7-byte chunks: 0, "ixcc: expected 1 argument,
a decimal natural number\n" (52 bytes, status 2); 1, "ixcc: an argument is
not a decimal natural number\n" (50 bytes, status 3); 2, "ixcc: a number is
2^48 or more, past a numeric state machine's range\n" (69 bytes, status 67).
The first two are the texts of `ixcc compile --exe`'s shell. -/

def chunk0 (k : Nat) : Nat :=
  bif Nat.blt k 4 then
    (bif Nat.blt k 2 then (bif Nat.beq k 0 then 28464407795431529 else 28259048229269624)
     else (bif Nat.beq k 2 then 33046313228579104 else 27338448044975469))
  else
    (bif Nat.blt k 6 then (bif Nat.beq k 4 then 27423372147516448 else 32217290056278124)
     else (bif Nat.beq k 6 then 27704898843864161 else 684645))

def chunk1 (k : Nat) : Nat :=
  bif Nat.blt k 4 then
    (bif Nat.blt k 2 then (bif Nat.beq k 0 then 27338507888588905 else 30809859622510702)
     else (bif Nat.beq k 2 then 9134094608002661 else 28183099199483758))
  else
    (bif Nat.blt k 6 then (bif Nat.beq k 4 then 9126364957991781 else 30506441709478254)
     else (bif Nat.beq k 6 then 32199620762627616 else 10))

def chunk2 (k : Nat) : Nat :=
  bif Nat.blt k 8 then
    (bif Nat.blt k 4 then
      (bif Nat.blt k 2 then (bif Nat.beq k 0 then 27338507888588905 else 32199620762627616)
       else (bif Nat.beq k 2 then 14740268174764320 else 31363708541149240))
     else
      (bif Nat.blt k 6 then (bif Nat.beq k 4 then 32476756525737330 else 30809888311550068)
       else (bif Nat.beq k 6 then 32777680242438757 else 27973144017204321)))
  else (bif Nat.beq k 8 then 9133812297394536 else 11430643261810)

def msgChunk (id k : Nat) : Nat :=
  bif Nat.beq id 0 then chunk0 k else bif Nat.beq id 1 then chunk1 k else chunk2 k

/-- Byte `pos` of message `id`. -/
def msgByte (id pos : Nat) : Nat :=
  Nat.mod (Nat.shiftRight (msgChunk id (Nat.div pos 7)) (Nat.mul 8 (Nat.mod pos 7))) 256

def msgLength (id : Nat) : Nat := bif Nat.beq id 0 then 52 else bif Nat.beq id 1 then 50 else 69

def msgStatus (id : Nat) : Nat := bif Nat.beq id 0 then 2 else bif Nat.beq id 1 then 3 else 67

/-! ## `Main1`

The state's low two bits are its phase: 0 the start; 1 parsing, with
`acc * 2 + seen` above (the digits so far, saturated at `limit`, and whether
there was one); 2 rendering, with `10^j + rem` above (`j` digits left, `rem`
their value; 1 is the newline, 0 the exit); 3 a message, with `pos * 4 + id`
above. -/

namespace Main1

def parse (acc seen : Nat) : Nat := Nat.add (Nat.mul (Nat.add (Nat.mul acc 2) seen) 4) 1
def render (p : Nat) : Nat := Nat.add (Nat.mul p 4) 2
def message (id pos : Nat) : Nat := Nat.add (Nat.mul (Nat.add (Nat.mul pos 4) id) 4) 3

/-- Write message `id` to standard error, then exit with its status. -/
def say (id : Nat) : Nat := result (message id 1) (err (msgByte id 0))

/-- Render `r` in decimal and exit 0, starting with its first digit. -/
def finish (r : Nat) : Nat :=
  bif Nat.blt r limit then
    let q := pow10Le r
    result (render (Nat.add q (Nat.mod r q))) (out (Nat.add 48 (Nat.div r q)))
  else say 2

/-- The argument is complete and below `limit`: the program computes now. -/
def ready (s e : Nat) : Bool :=
  bif Nat.beq (Nat.mod s 4) 1 then
    (bif Nat.beq e 256 then
      (bif Nat.beq (Nat.mod (Nat.div s 4) 2) 1 then Nat.blt (Nat.div s 8) limit else false)
     else false)
  else false

/-- The parsed argument, when `ready`. -/
def argument (s : Nat) : Nat := Nat.div s 8

/-- Every step but the program's: each phase's result, then the phase's. -/
def step (s e : Nat) : Nat :=
  let p := Nat.div s 4
  let phase := Nat.mod s 4
  -- phase 0: the event is the argument count
  let a := bif Nat.beq e 1 then result (parse 0 0) arg else say 0
  -- phase 1: a byte of the argument, or its end
  let n := Nat.add (Nat.mul (Nat.div p 2) 10) (Nat.sub e 48)
  let digit := bif Nat.ble 48 e then Nat.ble e 57 else false
  let b := bif Nat.blt e 256 then
      (bif digit then result (parse (bif Nat.blt n limit then n else limit) 1) arg else say 1)
    else (bif Nat.beq e 256 then (bif Nat.beq (Nat.mod p 2) 1 then say 2 else say 1) else say 1)
  -- phase 2: the next digit, the newline, or exit 0
  let q := pow10Le (Nat.max p 1)
  let rem := Nat.sub p q
  let q' := Nat.div q 10
  let c := bif Nat.beq e 0 then
      (bif Nat.beq p 0 then result 0 (exit 0)
       else bif Nat.beq p 1 then result (render 0) (out 10)
       else result (render (Nat.add q' (Nat.mod rem (Nat.max q' 1))))
         (out (Nat.add 48 (Nat.div rem (Nat.max q' 1)))))
    else result 0 (exit 74)
  -- phase 3: the next byte of a message, or its status
  let id := Nat.mod p 4
  let pos := Nat.div p 4
  let d := bif Nat.beq e 0 then
      (bif Nat.blt pos (msgLength id) then result (message id (Nat.add pos 1)) (err (msgByte id pos))
       else result 0 (exit (msgStatus id)))
    else result 0 (exit 74)
  bif Nat.blt phase 2 then (bif Nat.beq phase 0 then a else b) else (bif Nat.beq phase 2 then c else d)

/-- The machine of `f`, with `f` passed as a closure. -/
def run (f : Nat → Nat) (s e : Nat) : Nat :=
  bif ready s e then finish (f (argument s)) else step s e

end Main1

end IxccExe

/-! # The `phase1-machines` programs

Everything above is `IxCC/lib/IxccExe.lean`, verbatim (`tests-exe` checks
it). Below: the roots of the family, each a numeric state machine, and the
oracle driver for `lean --run`. -/

namespace Machines

/-- K1's `fib` (`IxCCTests/Fixtures/K1.lean`), structural recursion. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `fib` as an executable: one decimal argument, the result in decimal. -/
def fibMain (s e : Nat) : Nat :=
  bif IxccExe.Main1.ready s e then IxccExe.Main1.finish (fib (IxccExe.Main1.argument s))
  else IxccExe.Main1.step s e

/-- The same through `Main1.run`, with `fib` passed as a closure. -/
def fibMainHO (s e : Nat) : Nat := IxccExe.Main1.run fib s e

/-- The identity: prints its argument (for the range's edges). -/
def idMain (s e : Nat) : Nat :=
  bif IxccExe.Main1.ready s e then IxccExe.Main1.finish (IxccExe.Main1.argument s)
  else IxccExe.Main1.step s e

/-- A request outside the interface, version 0 (kind 5). -/
def badRequest (_s _e : Nat) : Nat := 5

/-- The session machine. It echoes every byte of its arguments to standard
output, changed by a running hash `h` (below `2^32`), and a newline to
standard error after each argument; at the end it prints `h` in decimal and
exits with `h % 256`. Two calls per byte. Phases: 0 the start; 1 reading
(`h` above); 2 after an echo (`h`); 3 rendering (`(10^j + rem) * 256 +
status`). -/
def echo (s e : Nat) : Nat :=
  let p := Nat.div s 4
  let phase := Nat.mod s 4
  -- phase 0
  let a := IxccExe.result (Nat.add (Nat.mul 5381 4) 1) IxccExe.arg
  -- phase 1: a byte, the end of an argument, or the end of all of them
  let h := Nat.mod p 4294967296
  let h' := Nat.mod (Nat.add (Nat.mul h 33) e) 4294967296
  let q := IxccExe.pow10Le (Nat.max h 1)
  let b := bif Nat.blt e 256 then
      IxccExe.result (Nat.add (Nat.mul h' 4) 2) (IxccExe.out (Nat.xor e (Nat.mod h 64)))
    else bif Nat.beq e 256 then IxccExe.result (Nat.add (Nat.mul h' 4) 2) (IxccExe.err 10)
    else IxccExe.result (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add q (Nat.mod h q)) 256) (Nat.mod h 256)) 4) 3)
      (IxccExe.out (Nat.add 48 (Nat.div h q)))
  -- phase 2: after an echo
  let c := bif Nat.beq e 0 then IxccExe.result (Nat.add (Nat.mul h 4) 1) IxccExe.arg
    else IxccExe.result 0 (IxccExe.exit 74)
  -- phase 3: the hash in decimal, a newline, the exit
  let code := Nat.mod p 256
  let r := Nat.div p 256
  let q2 := IxccExe.pow10Le (Nat.max r 1)
  let rem := Nat.sub r q2
  let q2' := Nat.max (Nat.div q2 10) 1
  let d := bif Nat.beq e 0 then
      (bif Nat.beq r 0 then IxccExe.result 0 (IxccExe.exit code)
       else bif Nat.beq r 1 then IxccExe.result (Nat.add (Nat.mul code 4) 3) (IxccExe.out 10)
       else IxccExe.result (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add q2' (Nat.mod rem q2')) 256) code) 4) 3)
         (IxccExe.out (Nat.add 48 (Nat.div rem q2'))))
    else IxccExe.result 0 (IxccExe.exit 74)
  bif Nat.blt phase 2 then (bif Nat.beq phase 0 then a else b) else (bif Nat.beq phase 2 then c else d)

end Machines

/-! ## The oracle driver -/

/-- The platform, version 0, in plain Lean: run `step` from state 0 on the
arguments (as their UTF-8 bytes), every write succeeding, for at most `fuel`
calls. Standard output, standard error, the exit status (`none`: out of
fuel; 72: a request outside the interface) and the number of calls. -/
def simulate (step : Nat → Nat → Nat) (args : List String) (fuel : Nat) :
    List Nat × List Nat × Option Nat × Nat := Id.run do
  let mut block : List (List Nat) := args.map fun a => a.toUTF8.toList.map (·.toNat)
  let mut s := 0
  let mut e := args.length
  let mut outB : Array Nat := #[]
  let mut errB : Array Nat := #[]
  for n in List.range fuel do
    let w := step s e
    s := w / 2048
    let r := w % 2048
    match r % 8 with
    | 0 =>
      if r / 8 != 0 then return (outB.toList, errB.toList, some 72, n + 1)
      match block with
      | [] => e := 257
      | [] :: rest => e := 256; block := rest
      | (b :: bs) :: rest => e := b; block := bs :: rest
    | 1 => outB := outB.push (r / 8); e := 0
    | 2 => errB := errB.push (r / 8); e := 0
    | 3 => return (outB.toList, errB.toList, some (r / 8), n + 1)
    | _ => return (outB.toList, errB.toList, some 72, n + 1)
  return (outB.toList, errB.toList, none, fuel)

def hex (bytes : List Nat) : String :=
  String.join (bytes.map fun b =>
    let d (k : Nat) := "0123456789abcdef".toList.getD k '0'
    String.mk [d (b / 16), d (b % 16)])

def pick : String → Option (Nat → Nat → Nat)
  | "Machines.fibMain" => some Machines.fibMain
  | "Machines.fibMainHO" => some Machines.fibMainHO
  | "Machines.idMain" => some Machines.idMain
  | "Machines.badRequest" => some Machines.badRequest
  | "Machines.echo" => some Machines.echo
  | _ => none

/-- Each stdin line `ROOT S E` prints the step's value; a line
`session ROOT ARG…` prints the session's standard output and error (in hex),
its exit status and its number of calls, tab-separated. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | "session" :: root :: args =>
      match pick root with
      | some step =>
        let (o, e, code, calls) := simulate step args 100000
        IO.println s!"{hex o}\t{hex e}\t{code.getD 256}\t{calls}"
      | none => IO.println s!"unknown root {root}"
    | [root, s, e] =>
      match pick root with
      | some step => IO.println (toString (step s.toNat! e.toNat!))
      | none => IO.println s!"unknown root {root}"
    | root :: _ => IO.println s!"unknown root {root}"
