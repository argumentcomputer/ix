/-
  Equations for fixed-width words (`ix compile --equations`).

  A consumer that evaluates `UInt8`, `UInt16`, `UInt32` and `UInt64` operations as primitives
  (IxCC, `IxCC/docs/data-and-roots-design.md`, DR2) gives each a meaning by a stored theorem: the
  operation applied to `UIntN.ofNat x` (and `UIntN.ofNat y`) equals `UIntN.ofNat` of a formula over
  `Nat`'s operations; `ofNat`'s own theorem, the *bridge*, says `UIntN.ofNat x` is the constructor
  tower of `x % size`, given a proof that `x % size` is below the size. Being theorems the kernel
  checks, they hold in every model of the environment; the consumer compares each statement with
  the one it expects, syntactically, so the statements below are fixed in that form: `Nat.add`,
  `Nat.mod`, … applied (no notation), sizes as raw literals (`nat_lit`), and the bridge's bound as
  `Nat.le (Nat.succ (Nat.mod x size)) size`.

  `close` adds the theorem of every word operation the closure reaches outside theorems
  (`reachedOutsideTheorems`, from the compile's roots), with the bridges its statement mentions
  (`neededFor`), by elaborating the statements in the environment being compiled (Lean's `Init` is
  all they need), so that they join the closure as seeds. The decisions
  (`decEq`, `decLt`, `decLe`) have no theorem: their reference bodies reduce to `Nat`'s own and
  compile as they are.
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

/-- The equations of width `w`, one per primitive operation (`ofNat`'s is the bridge). Every
statement is in the form IxCC's table check expects (`IxCC/Src/Table/Word.lean`). -/
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
      text := s!"theorem {thm "ofNat"} (x : Nat) (h : Nat.le (Nat.succ {xm}) {m}) : \
        {t}.ofNat x = {t}.ofBitVec (@BitVec.ofFin (nat_lit {w.bits}) (@Fin.mk {m} {xm} h)) :=\n  \
        rfl\n" } ] ++ converts

/-- Every equation of every width. -/
def all : List Equation := widths.flatMap equations

/-- The operations that have an equation. -/
def operations : Lean.NameSet := all.foldl (fun s e => s.insert e.operation) {}

/-- **The word operations reached outside theorems**: a dependency walk from `roots` over the
values of definitions and opaques and the rules of recursors, the terms that can run, that enters
no theorem (a theorem's statement and proof never run, and Lean puts the proofs nested in a
definition, an `omega` termination proof among them, in auxiliary theorems), no declaration's type
(a type never runs; through `autoParam`'s, every `for` loop would reach `String` and `Char`) and no
word operation (a consumer that takes the operation as a primitive does not run its body). It is a
dependency walk, not a consumer's relevance analysis: it can hold an operation that occurs only in
a binder's type or an irrelevant argument of a value (an equation too many, harmless), and it misses
one that runs only through a theorem (the target of a `csimp` redirect), for which IxCC's hint
names the operation. -/
partial def reachedOutsideTheorems (env : Lean.Environment) (roots : List Lean.Name) :
    Lean.NameSet :=
  go roots {} {}
where
  go : List Lean.Name → Lean.NameSet → Lean.NameSet → Lean.NameSet
    | [], _, found => found
    | n :: rest, seen, found =>
      if seen.contains n then go rest seen found
      else if operations.contains n then go rest (seen.insert n) (found.insert n)
      else
        let refs : Array Lean.Name := match env.find? n with
          | some (.defnInfo v) => v.value.getUsedConstants
          | some (.opaqueInfo v) => v.value.getUsedConstants
          | some (.recInfo v) => v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants) #[]
          | _ => #[]
        go (refs.toList ++ rest) (seen.insert n) found

/-- The equations to add for the word operations `ops` (`reachedOutsideTheorems`): each
operation's, and the bridges its statement mentions (its width's `ofNat`, and a conversion's
target width's), unless already in the environment; in the order of `all`. -/
def neededFor (env : Lean.Environment) (ops : Lean.NameSet) : List Equation :=
  let ofNat := fun (w : Width) => s!"{w.name}.ofNat".toName
  let bridges : Lean.NameSet := widths.foldl (init := {}) fun s w =>
    (equations w).foldl (init := s) fun s e =>
      if !ops.contains e.operation then s
      else
        let s := s.insert (ofNat w)
        match widths.find? fun w' => e.operation == s!"{w.name}.to{w'.name}".toName with
        | some w' => s.insert (ofNat w')
        | none => s
  all.filter fun e =>
    (ops.contains e.operation || bridges.contains e.operation) && !env.contains e.theoremName

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

/-- Equations for the five 64-bit hardware limb primitives (`IxCC.BigNat.LimbOps`), matching
`IxCC.Src.Table.limbEqnType`. -/
def limbEquations : List Equation :=
  let m := s!"(nat_lit {2 ^ 64})"
  let xm := s!"(Nat.mod x {m})"
  let ym := s!"(Nat.mod y {m})"
  let him := s!"(Nat.mod hi {m})"
  let lom := s!"(Nat.mod lo {m})"
  let dm := s!"(Nat.mod d {m})"
  let thm := fun (op : String) => (theoremNamespace ++ ".BigNat_" ++ op).toName
  [ { operation := `IxCC.BigNat.clz64, theoremName := thm "clz64"
      text := s!"theorem {thm "clz64"} (x : Nat) : IxCC.BigNat.clz64 (UInt64.ofNat x) = \
        UInt64.ofNat (cond (Nat.beq {xm} (nat_lit 0)) (nat_lit 64) \
          (Nat.sub (nat_lit 63) (Nat.log2 {xm}))) := by\n  \
        unfold IxCC.BigNat.clz64\n  \
        by_cases h : x % {2 ^ 64} = 0\n  \
        · have h1 : UInt64.ofNat x = 0 := UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofNat']; exact h)\n    \
          have h2 : Nat.beq {xm} (nat_lit 0) = true := Nat.beq_eq.mpr h\n    \
          rw [h2]; simp [h1]\n  \
        · have h1 : UInt64.ofNat x ≠ 0 := fun e => h (by simpa [UInt64.toNat_ofNat'] using congrArg UInt64.toNat e)\n    \
          have h2 : Nat.beq {xm} (nat_lit 0) = false := by\n      \
            cases hb : Nat.beq {xm} (nat_lit 0)\n      \
            · rfl\n      \
            · exact absurd (Nat.beq_eq.mp hb) h\n    \
          rw [h2]; simp [h1, UInt64.toNat_ofNat']; rfl\n" },
    { operation := `IxCC.BigNat.mulWide64, theoremName := thm "mulWide64"
      text := s!"theorem {thm "mulWide64"} (x y : Nat) : \
        IxCC.BigNat.mulWide64 (UInt64.ofNat x) (UInt64.ofNat y) = \
        Prod.mk (UInt64.ofNat (Nat.mod (Nat.mul {xm} {ym}) {m})) \
          (UInt64.ofNat (Nat.div (Nat.mul {xm} {ym}) {m})) :=\n  rfl\n" },
    { operation := `IxCC.BigNat.divWide64, theoremName := thm "divWide64"
      text := s!"theorem {thm "divWide64"} (hi lo d : Nat) \
        (h : Nat.le (Nat.succ {him}) {dm}) : \
        IxCC.BigNat.divWide64 (UInt64.ofNat hi) (UInt64.ofNat lo) (UInt64.ofNat d) h = \
        Prod.mk (UInt64.ofNat (Nat.div (Nat.add (Nat.mul {him} {m}) {lom}) {dm})) \
          (UInt64.ofNat (Nat.mod (Nat.add (Nat.mul {him} {m}) {lom}) {dm})) :=\n  rfl\n" },
    { operation := `IxCC.BigNat.addCarry64, theoremName := thm "addCarry64"
      text := s!"theorem {thm "addCarry64"} (x y : Nat) (c : Bool) : \
        IxCC.BigNat.addCarry64 (UInt64.ofNat x) (UInt64.ofNat y) c = \
        Prod.mk (UInt64.ofNat (Nat.add (Nat.add {xm} {ym}) (Bool.toNat c))) \
          (Nat.ble {m} (Nat.add (Nat.add {xm} {ym}) (Bool.toNat c))) := by\n  \
        unfold IxCC.BigNat.addCarry64\n  \
        apply Prod.ext\n  \
        · rfl\n  \
        · simp only [UInt64.toNat_ofNat']\n    \
          by_cases h : {2 ^ 64} ≤ x % {2 ^ 64} + y % {2 ^ 64} + c.toNat\n    \
          · have hb : Nat.ble {m} (Nat.add (Nat.add {xm} {ym}) (Bool.toNat c)) = true := Nat.ble_eq.mpr h\n      \
            rw [hb]; simp [h]\n    \
          · have hb : Nat.ble {m} (Nat.add (Nat.add {xm} {ym}) (Bool.toNat c)) = false := by\n        \
              cases hq : Nat.ble {m} (Nat.add (Nat.add {xm} {ym}) (Bool.toNat c))\n        \
              · rfl\n        \
              · exact absurd (Nat.ble_eq.mp hq) h\n      \
            rw [hb]; simp [h]\n" },
    { operation := `IxCC.BigNat.subBorrow64, theoremName := thm "subBorrow64"
      text := s!"theorem {thm "subBorrow64"} (x y : Nat) (b : Bool) : \
        IxCC.BigNat.subBorrow64 (UInt64.ofNat x) (UInt64.ofNat y) b = \
        Prod.mk (UInt64.ofNat (cond (Nat.ble (Nat.succ {xm}) (Nat.add {ym} (Bool.toNat b))) \
          (Nat.sub (Nat.add {m} {xm}) (Nat.add {ym} (Bool.toNat b))) \
          (Nat.sub {xm} (Nat.add {ym} (Bool.toNat b))))) \
          (Nat.ble (Nat.succ {xm}) (Nat.add {ym} (Bool.toNat b))) := by\n  \
        unfold IxCC.BigNat.subBorrow64\n  \
        by_cases h : x % {2 ^ 64} < y % {2 ^ 64} + b.toNat\n  \
        · have hb : Nat.ble (Nat.succ {xm}) (Nat.add {ym} (Bool.toNat b)) = true := Nat.ble_eq.mpr h\n    \
          rw [hb]; simp [UInt64.toNat_ofNat', h]; rfl\n  \
        · have hb : Nat.ble (Nat.succ {xm}) (Nat.add {ym} (Bool.toNat b)) = false := by\n      \
            cases hq : Nat.ble (Nat.succ {xm}) (Nat.add {ym} (Bool.toNat b))\n      \
            · rfl\n      \
            · exact absurd (Nat.ble_eq.mp hq) h\n    \
          rw [hb]; simp [UInt64.toNat_ofNat', h]; rfl\n" } ]

/-- The five 64-bit limb primitive operations that have equations. -/
def limbOperations : Lean.NameSet :=
  limbEquations.foldl (fun s e => s.insert e.operation) {}

/-- The limb equations to add for operations present in `ops` (and not already in `env`). -/
def neededLimbFor (env : Lean.Environment) (ops : Lean.NameSet) : List Equation :=
  limbEquations.filter fun e => ops.contains e.operation && !env.contains e.theoremName

end Ix.Compile.WordEquations

end
