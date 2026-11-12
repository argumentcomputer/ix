/-! The `natural` fixture of `phase1-machines`: `fib` as a numeric state
machine, with the library written in the natural style (`if`, `==` and `&&`;
`if` chains for its tables; `Main1.step` a nested `if` on the phase), against
which `Machines.lean`'s library (`lib/IxccExe.lean`) works around the middle
end with named primitives, `bif`, balanced trees and one phase-selecting step.
The interface is the same: a step's result is `state * 2048 + request`, the
state's low two bits its phase (see `lib/IxccExe.lean`). Only what the two
roots reach is kept. The oracle driver (`main`) answers a line `ROOT S E` with
the step's value. -/

namespace IxccExe

/-! ## The platform interface, version 0, as numbers -/

/-- A step's result: the next state `s` (below `2^52`) and the request field. -/
def result (s r : Nat) : Nat := s * 2048 + r
/-- Requests: the next byte of the argument block; one byte to standard output
or error; exit. -/
def arg : Nat := 0
def out (b : Nat) : Nat := 1 + 8 * b
def err (b : Nat) : Nat := 2 + 8 * b
def exit (c : Nat) : Nat := 3 + 8 * c

/-- Arguments and results of `Main1` must be below this (the state has 52 bits). -/
def limit : Nat := 281474976710656

/-- The largest power of ten at most `p`, for `1 ≤ p < 10^16`. -/
def pow10Le (p : Nat) : Nat :=
  if p < 10 then 1 else if p < 100 then 10 else if p < 1000 then 100
  else if p < 10000 then 1000 else if p < 100000 then 10000
  else if p < 1000000 then 100000 else if p < 10000000 then 1000000
  else if p < 100000000 then 10000000 else if p < 1000000000 then 100000000
  else if p < 10000000000 then 1000000000 else if p < 100000000000 then 10000000000
  else if p < 1000000000000 then 100000000000 else if p < 10000000000000 then 1000000000000
  else if p < 100000000000000 then 10000000000000
  else if p < 1000000000000000 then 100000000000000
  else 1000000000000000

/-- Messages as little-endian 7-byte chunks: an `if` chain on one index. -/
def msgChunk (id k : Nat) : Nat :=
  let i := id * 16 + k
  if i == 0 then 28464407795431529 else if i == 1 then 28259048229269624
  else if i == 2 then 33046313228579104 else if i == 3 then 27338448044975469
  else if i == 4 then 27423372147516448 else if i == 5 then 32217290056278124
  else if i == 6 then 27704898843864161 else if i == 7 then 684645
  else if i == 16 then 27338507888588905 else if i == 17 then 30809859622510702
  else if i == 18 then 9134094608002661 else if i == 19 then 28183099199483758
  else if i == 20 then 9126364957991781 else if i == 21 then 30506441709478254
  else if i == 22 then 32199620762627616 else if i == 23 then 10
  else if i == 32 then 27338507888588905 else if i == 33 then 32199620762627616
  else if i == 34 then 14740268174764320 else if i == 35 then 31363708541149240
  else if i == 36 then 32476756525737330 else if i == 37 then 30809888311550068
  else if i == 38 then 32777680242438757 else if i == 39 then 27973144017204321
  else if i == 40 then 9133812297394536 else if i == 41 then 11430643261810
  else 0

def msgLength (id : Nat) : Nat := if id == 0 then 52 else if id == 1 then 50 else 69

/-- The exit status after each message: 2 a wrong count, 3 not a numeral, 67 too large. -/
def msgStatus (id : Nat) : Nat := if id == 0 then 2 else if id == 1 then 3 else 67

def msgByte (id pos : Nat) : Nat := (msgChunk id (pos / 7) >>> (8 * (pos % 7))) % 256

/-! ## `Main1`: one decimal argument, a decimal result

State `s`: `s % 4` is the phase, `s / 4` its payload: 0 start; 1 parsing
(`acc * 2 + seen`); 2 rendering (`10^j + rem`: `j` digits left); 3 a message
(`pos * 4 + id`). -/

namespace Main1

def parse (acc seen : Nat) : Nat := (acc * 2 + seen) * 4 + 1
def render (p : Nat) : Nat := p * 4 + 2
def message (id pos : Nat) : Nat := (pos * 4 + id) * 4 + 3

/-- Write message `id` to standard error, then exit with its status. -/
def say (id : Nat) : Nat := result (message id 1) (err (msgByte id 0))

/-- Render `r` and exit 0, starting with its first digit. -/
def finish (r : Nat) : Nat :=
  if r < limit then
    let q := pow10Le r
    result (render (q + r % q)) (out (48 + r / q))
  else say 2

/-- The argument is complete and in range: the program computes now. -/
def ready (s e : Nat) : Bool :=
  s % 4 == 1 && e == 256 && (s / 4) % 2 == 1 && s / 8 < limit

/-- The parsed argument. -/
def argument (s : Nat) : Nat := s / 8

/-- Phase 3: the next byte of a message, or its status. -/
def onMessage (p e : Nat) : Nat :=
  let id := p % 4
  let pos := p / 4
  if e == 0 then
    if pos < msgLength id then result (message id (pos + 1)) (err (msgByte id pos))
    else result 0 (exit (msgStatus id))
  else result 0 (exit 74)

/-- Every other step. -/
def step (s e : Nat) : Nat :=
  let phase := s % 4
  let p := s / 4
  if phase == 0 then
    if e == 1 then result (parse 0 0) arg else say 0
  else if phase == 1 then
    if e < 256 then
      if 48 ≤ e && e ≤ 57 then
        let n := (p / 2) * 10 + (e - 48)
        result (parse (if n < limit then n else limit) 1) arg
      else say 1
    else if e == 256 && p % 2 == 1 then say 2
    else say 1
  else if phase == 2 then
    if e == 0 then
      if p == 0 then result 0 (exit 0)
      else if p == 1 then result (render 0) (out 10)
      else
        let q := pow10Le p
        let rem := p - q
        let q' := q / 10
        result (render (q' + rem % q')) (out (48 + rem / q'))
    else result 0 (exit 74)
  else
    let id := p % 4
    let pos := p / 4
    if e == 0 then
      if pos < msgLength id then result (message id (pos + 1)) (err (msgByte id pos))
      else result 0 (exit (msgStatus id))
    else result 0 (exit 74)

end Main1
end IxccExe

/-! ## The program -/

namespace Natural

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `fib` as a machine: the user's glue, first order. -/
def fibMain (s e : Nat) : Nat :=
  if IxccExe.Main1.ready s e then IxccExe.Main1.finish (fib (IxccExe.Main1.argument s))
  else IxccExe.Main1.step s e

/-- The message phase's step alone (state payload `pos * 4 + id`). -/
def onMessage (p e : Nat) : Nat := IxccExe.Main1.onMessage p e

end Natural

/-- The oracle: a line `ROOT S E` answered with the step's value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      IO.println <| match root, args.map String.toNat! with
        | "Natural.fibMain", [s, e] => toString (Natural.fibMain s e)
        | "Natural.onMessage", [p, e] => toString (Natural.onMessage p e)
        | _, _ => s!"unknown root {root}"
