/-
  Equations for fixed-width words (`ix compile --equations`).

  A consumer that evaluates `UInt8`, `UInt16`, `UInt32` and `UInt64` operations as primitives
  (IxCC, `IxCC/docs/data-and-roots-design.md`, DR2) gives each a meaning by a stored theorem: the
  operation applied to `UIntN.ofNat x` (and `UIntN.ofNat y`) equals `UIntN.ofNat` of a formula over
  `Nat`'s operations, and, per width, `UIntN.ofNat x` is the constructor tower of `x` below the size
  (the *bridge*). Being theorems the kernel checks, they hold in every model of the environment;
  the consumer compares each statement with the one it expects, syntactically, so the statements
  below are fixed in that form: `Nat.add`, `Nat.mod`, … applied (no notation), sizes as raw
  literals (`nat_lit`), and the bound as `Nat.le (Nat.succ x) size`.

  `close` adds, for every word operation the closure reaches, its theorem, and for every width
  reached the `ofNat` equation and the bridge, by elaborating their statements in the environment
  being compiled (Lean's `Init` is all they need), so that they join the closure as seeds. The
  decisions (`decEq`, `decLt`, `decLe`) have no theorem: their reference bodies reduce to `Nat`'s
  own and compile as they are.
-/
module
public import Lean.Elab.Frontend

public section

namespace Ix.Compile.WordEquations

open Lean Elab

/-- A width: the type's name and its number of bits. -/
structure Width where
  name : String
  bits : Nat
  deriving Inhabited, BEq

def widths : List Width := [⟨"UInt8", 8⟩, ⟨"UInt16", 16⟩, ⟨"UInt32", 32⟩, ⟨"UInt64", 64⟩]

def Width.size (w : Width) : Nat := 2 ^ w.bits

/-- The namespace of the theorems, which are named `UInt64_add`, … (not `UInt64.add`, which
would shadow the operations inside the statements). -/
def theoremNamespace : String := "IxWordEquations"

/-- One equation: the operation's constant (`UInt64.add`), the theorem's name and its text. -/
structure Equation where
  operation : Lean.Name
  theoremName : Lean.Name
  text : String
  deriving Inhabited

/-- The equations of width `w`: one per primitive operation (`ofNat`'s states that it reduces
its argument), then the bridge. Every statement is `eqnType`'s form in IxCC's
`IxCC/Src/Word/Eqns.lean`. -/
def equations (w : Width) : List Equation :=
  let t := w.name
  let m := s!"(nat_lit {w.size})"
  let xm := s!"(Nat.mod x {m})"
  let ym := s!"(Nat.mod y {m})"
  let red := fun (e : String) => s!"(Nat.mod {e} {m})"
  let amount := s!"(Nat.mod {ym} (nat_lit {w.bits}))"
  let proof := s!"{t}.toNat_inj.mp (Nat.mod_eq_of_lt ({t}.toNat_lt _)).symm"
  let thm := fun (op : String) => (theoremNamespace ++ "." ++ t ++ "_" ++ op).toName
  let binary := fun (op rhs : String) =>
    { operation := s!"{t}.{op}".toName, theoremName := thm op
      text := s!"theorem {thm op} (x y : Nat) : {t}.{op} ({t}.ofNat x) ({t}.ofNat y) = \
        {t}.ofNat {rhs} :=\n  {proof}\n" : Equation }
  let unary := fun (op rhs : String) =>
    { operation := s!"{t}.{op}".toName, theoremName := thm op
      text := s!"theorem {thm op} (x : Nat) : {t}.{op} ({t}.ofNat x) = {t}.ofNat {rhs} :=\n  \
        {proof}\n" : Equation }
  let converts := (widths.filter (· != w)).map fun w' =>
    let rhs := if w.bits ≤ w'.bits then xm else s!"(Nat.mod {xm} (nat_lit {w'.size}))"
    let op := s!"to{w'.name}"
    { operation := s!"{t}.{op}".toName, theoremName := thm op
      text := s!"theorem {thm op} (x : Nat) : {t}.{op} ({t}.ofNat x) = {w'.name}.ofNat {rhs} :=\n  \
        {w'.name}.toNat_inj.mp (Nat.mod_eq_of_lt ({w'.name}.toNat_lt _)).symm\n" : Equation }
  [ binary "add" (red s!"(Nat.add {xm} {ym})"),
    binary "sub" (red s!"(Nat.add (Nat.sub {m} {ym}) {xm})"),
    binary "mul" (red s!"(Nat.mul {xm} {ym})"),
    binary "div" s!"(Nat.div {xm} {ym})",
    binary "mod" s!"(Nat.mod {xm} {ym})",
    binary "land" s!"(Nat.land {xm} {ym})",
    binary "lor" s!"(Nat.lor {xm} {ym})",
    binary "xor" s!"(Nat.xor {xm} {ym})",
    binary "shiftLeft" (red s!"(Nat.shiftLeft {xm} {amount})"),
    binary "shiftRight" s!"(Nat.shiftRight {xm} {amount})",
    unary "complement" s!"(Nat.xor (nat_lit {w.size - 1}) {xm})",
    unary "neg" (red s!"(Nat.sub {m} {xm})"),
    { operation := s!"{t}.toNat".toName, theoremName := thm "toNat"
      text := s!"theorem {thm "toNat"} (x : Nat) : {t}.toNat ({t}.ofNat x) = {xm} := rfl\n" },
    { operation := s!"{t}.ofNat".toName, theoremName := thm "ofNat"
      text := s!"theorem {thm "ofNat"} (x : Nat) : {t}.ofNat x = {t}.ofNat {xm} :=\n  {proof}\n" },
    { operation := s!"{t}.ofNat".toName, theoremName := thm "bridge"
      text := s!"theorem {thm "bridge"} (x : Nat) (h : Nat.le (Nat.succ x) {m}) : {t}.ofNat x = \
        {t}.ofBitVec (@BitVec.ofFin (nat_lit {w.bits}) (@Fin.mk {m} x h)) :=\n  \
        {t}.toNat_inj.mp (Nat.mod_eq_of_lt h)\n" } ] ++ converts

/-- Every equation of every width. -/
def all : List Equation := widths.flatMap equations

/-- The equations to add for a closure: those of the operations it holds whose theorem is not
yet in the environment, with the `ofNat` equation and the bridge of every width one of whose
operations it holds. -/
def needed (env : Lean.Environment) (closed : List Lean.Name) : List Equation :=
  let present : Lean.NameSet := closed.foldl (·.insert ·) {}
  widths.flatMap fun w =>
    let eqs := equations w
    let reached := eqs.filter (present.contains ·.operation)
    if reached.isEmpty then []
    else
      let ofNat := eqs.filter (·.operation == s!"{w.name}.ofNat".toName)
      (reached ++ ofNat).foldl (fun acc e =>
        if acc.any (·.theoremName == e.theoremName) || env.contains e.theoremName then acc
        else acc ++ [e]) []

/-- Elaborate `eqs` in `env` (every statement checked by Lean's kernel as any theorem is). -/
def add (env : Lean.Environment) (eqs : List Equation) : IO Lean.Environment := do
  if eqs.isEmpty then return env
  let text := String.join (eqs.map (·.text))
  let inputCtx := Parser.mkInputContext text "<ix-word-equations>"
  let s ← IO.processCommands inputCtx {} (Command.mkState env {} {})
  let msgs := s.commandState.messages
  if msgs.hasErrors then
    throw <| IO.userError <| "word equations:\n" ++ "\n".intercalate
      (← msgs.toList.mapM (·.toString))
  return s.commandState.env

end Ix.Compile.WordEquations

end
