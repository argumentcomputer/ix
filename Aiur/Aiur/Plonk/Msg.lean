import Aiur.Plonk.Air

/-!
# Lookup messages, `q` and running-sum gates, and the pool

For lookup `k` of a lowered row, the lowering emits a `q` gate
`q·d − m = 0` (`d` the fingerprint wire, `m` the multiplicity), a running-sum
gate `s' = s + q` and, for a request, a booleanity gate `m² − m = 0`. The
fingerprint chain under `d` reaches cell wires, row-local wires and global
pool wires (`γ`, `β`, the powers `γ^e` and the shared bases).

`msgCircuit a r k` states what these gates must mean, over the row's main
columns `0 … W − 1` and the pseudo-columns

* `W` = `γ`, `W + 1` = `β`, `W + 2` = `q`, `W + 3` = `s`, `W + 4` = `s'`
  (and `W + 5` for the unused `sumIn` reference of a later message),

as the constraints `q·fp(γ, β, args) − m`, `s + q − s'` and, when a
booleanity gate is present, `m² − m`; fixed columns are substituted and every
constraint is normalised. `checkMessage` checks them with
`Tiling.Template.check` on the cone of the three gates, in which pool wires
and row-local wires are sum slots: the pool gates are checked inside every
cone that reaches them. A lookup without gates must have a multiplicity that
normalises to zero.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Poly Template SlotDef Row Term)
open Aiur.Tiling.WideStage (Air)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (LGate Ref)

section Fp

variable {F : Type} [Field F]

def powExpr (g : ArithExpr F) : Nat → ArithExpr F
  | 0 => .const 1
  | e + 1 => .mul (powExpr g e) g

theorem powExpr_denote (x : Nat → F) (g : ArithExpr F) (e : Nat) :
    (powExpr g e).denote x = g.denote x ^ e := by
  induction e with
  | zero => simp [powExpr, ArithExpr.denote]
  | succ e ih => simp [powExpr, ArithExpr.denote, ih, pow_succ]

def fpTerms (γ : ArithExpr F) (n : Nat) : List (ArithExpr F × Nat) → ArithExpr F
  | [] => .const 0
  | (x, i) :: rest => .add (.mul x (powExpr γ (expOf n i))) (fpTerms γ n rest)

/-- `fp γ β args` as an expression. -/
def fpExpr (γ β : ArithExpr F) (args : List (ArithExpr F)) : ArithExpr F :=
  .add (.add β (.mul (.const (args.length : F)) (powExpr γ args.length))) (fpTerms γ args.length args.zipIdx)

theorem fpTerms_denote (x : Nat → F) (γ : ArithExpr F) (n : Nat) (l : List (ArithExpr F × Nat)) :
    (fpTerms γ n l).denote x = (l.map fun (e, i) => e.denote x * γ.denote x ^ expOf n i).sum := by
  induction l with
  | nil => simp [fpTerms, ArithExpr.denote]
  | cons h t ih => obtain ⟨e, i⟩ := h; simp [fpTerms, ArithExpr.denote, ih, powExpr_denote]

theorem fpExpr_denote (x : Nat → F) (γ β : ArithExpr F) (args : List (ArithExpr F)) :
    (fpExpr γ β args).denote x = fp (γ.denote x) (β.denote x) (args.map (·.denote x)) := by
  simp only [fpExpr, fp, ArithExpr.denote, fpTerms_denote, powExpr_denote, List.length_map]
  congr 1
  rw [List.zipIdx_map, List.map_map]
  rfl

end Fp

namespace AirIn

section Generic

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
/-- The pseudo-columns of a message circuit. -/
def gammaCol (a : Air F) : Nat := a.circuit.width
omit [Field F] [DecidableEq F] in
def betaCol (a : Air F) : Nat := a.circuit.width + 1
omit [Field F] [DecidableEq F] in
def qCol (a : Air F) : Nat := a.circuit.width + 2
omit [Field F] [DecidableEq F] in
def sInCol (a : Air F) : Nat := a.circuit.width + 3
omit [Field F] [DecidableEq F] in
def sOutCol (a : Air F) : Nat := a.circuit.width + 4
omit [Field F] [DecidableEq F] in
def spareCol (a : Air F) : Nat := a.circuit.width + 5

omit [DecidableEq F] in
def lookupAt (a : Air F) (k : Nat) : Tiling.Lookup F :=
  a.circuit.lookups.getD k ⟨.const 0, []⟩

omit [DecidableEq F] in
def multExpr (a : Air F) (r k : Nat) : ArithExpr F := fixRow a r (lookupAt a k).multiplicity

omit [DecidableEq F] in
def argExprs (a : Air F) (r k : Nat) : List (ArithExpr F) := (lookupAt a k).args.map (fixRow a r)

def qConstraint (a : Air F) (r k : Nat) : ArithExpr F :=
  normExpr (.sub (.mul (.var (qCol a)) (fpExpr (.var (gammaCol a)) (.var (betaCol a)) (argExprs a r k)))
    (multExpr a r k))

def sumConstraint (a : Air F) : ArithExpr F :=
  normExpr (.sub (.add (.var (sInCol a)) (.var (qCol a))) (.var (sOutCol a)))

def countConstraint (a : Air F) (r k : Nat) : ArithExpr F :=
  normExpr (.sub (.mul (multExpr a r k) (multExpr a r k)) (multExpr a r k))

/-- The meaning of lookup `k`'s gates at row `r`: constraint 0 is the `q`
relation, 1 the running sum, 2 (when `count`) booleanity. -/
def msgCircuit (a : Air F) (r k : Nat) (count : Bool) : Tiling.Circuit F where
  width := a.circuit.width + 6
  constraints := [qConstraint a r k, sumConstraint a] ++ (if count then [countConstraint a r k] else [])
  lookups := []

end Generic

end AirIn

namespace Lower

/-- The template of a gate cone: `roots` assert constraints `0, 1, …` in
order, `defs` define their output wire, references with `col r = some c` are
wide column `c`. -/
def toTemplateG {F : Type} [Ring F] [BEq F] (defs roots : Array (LGate F)) (col : Ref → Option Nat) :
    Except String (Template F) := do
  let mut slotOf : Std.HashMap Ref Nat := {}
  let mut slots : Array (SlotDef F) := #[]
  let mut seenCols : Std.HashMap Nat Unit := {}
  for g in defs ++ roots do
    for r in [g.a, g.b, g.c] do
      if let some c := col r then
        unless slotOf.contains r do
          if seenCols.contains c then throw s!"two references share column {c}"
          seenCols := seenCols.insert c ()
          slotOf := slotOf.insert r slots.size
          slots := slots.push (.column c)
  let mut rows : Array (Row F) := #[]
  for g in defs do
    let get (r : Ref) : Except String Nat :=
      match slotOf[r]? with
      | some s => pure s
      | none => throw s!"gate reads an undefined wire {r}"
    let sa ← get g.a
    let sb ← get g.b
    unless g.O == -1 && !slotOf.contains g.c do
      throw "a defining gate must define a fresh wire"
    let s := slots.size
    slotOf := slotOf.insert g.c s
    let terms : List (Term F) :=
      (if g.L == 0 then [] else [.linear g.L sa]) ++ (if g.R == 0 then [] else [.linear g.R sb]) ++
        (if g.M == 0 then [] else [.product g.M sa sb])
    slots := slots.push (.sum terms g.C)
    rows := rows.push (.gate [⟨g.M, g.L, g.R, -1, 0, g.C, some sa, some sb, some s, none, 0⟩] false [.defines s])
  for h : j in [0:roots.size] do
    let g := roots[j]
    let get (r : Ref) : Except String Nat :=
      match slotOf[r]? with
      | some s => pure s
      | none => throw s!"gate reads an undefined wire {r}"
    let sa ← get g.a
    let sb ← get g.b
    let sc ← get g.c
    rows := rows.push (.gate [⟨g.M, g.L, g.R, g.O, 0, g.C, some sa, some sb, some sc, none, 0⟩] false [.root j])
  return { width := 4, slots := slots.toList, rows := rows.toList }

/-- The defining gates `roots` reach through `defOf`, pool wires first, each
group in creation order (a defining gate reads only wires created before its
output). -/
def coneOf {F : Type} (defOf : Ref → Option (LGate F)) (roots : Array (LGate F)) : Array (LGate F) := Id.run do
  let mut need : Std.HashMap Ref (LGate F) := {}
  let mut stack : List Ref := roots.toList.flatMap fun g => [g.a, g.b, g.c]
  while !stack.isEmpty do
    let r := stack.head!
    stack := stack.tail!
    if need.contains r then continue
    if let some g := defOf r then
      need := need.insert r g
      stack := g.a :: g.b :: stack
  let refs := need.toArray.map (·.1)
  let group (r : Ref) : Nat := if r % 4 == 2 then 0 else 1
  let sorted := refs.qsort fun x y => group x < group y || (group x == group y && x < y)
  return sorted.filterMap (need[·]?)

end Lower

namespace AirIn

/-- A row's lowering with a given pool. -/
def lowerRowState {p : Nat} [Fact (Nat.Prime p)] (a : Air (ZMod p)) (r : Nat) (P : Lower.Pool (ZMod p)) :
    Lower.St (ZMod p) :=
  let t := table a r
  ((Lower.lowerRow t (Lower.sharedNodes t) 0).run { pool := P }).2

section MsgChecks

variable {F : Type} [Field F] [DecidableEq F]

/-- The message template of lookup `k` from its gates `gs` (count gates,
then the `q` and running-sum gates in emission order), or `none` when the
lowering emitted none. -/
def msgTemplate (a : Air F) (defOf : Ref → Option (LGate F)) (gs : Array (LGate F)) :
    Except String (Option (Template F × Bool)) := do
  if gs.isEmpty then return none
  let counts := gs.filter (·.tag == .count)
  let logups := gs.filter (·.tag == .logup)
  unless logups.size == 2 && counts.size ≤ 1 do throw "malformed message gates"
  let qg := logups.getD 0 Lower.LGate.empty
  let sg := logups.getD 1 Lower.LGate.empty
  let col (x : Ref) : Option Nat :=
    if x % 4 == 0 then some (x / 8)
    else if x == Lower.gammaRef then some (gammaCol a)
    else if x == Lower.betaRef then some (betaCol a)
    else if x == qg.a then some (qCol a)
    else if x == sg.a then some (sInCol a)
    else if x == sg.c then some (sOutCol a)
    else if x == Lower.sumIn then some (spareCol a)
    else none
  let roots := #[qg, sg] ++ counts
  let T ← Lower.toTemplateG (Lower.coneOf defOf roots) roots col
  return some (T, !counts.isEmpty)

/-- Lookup `k` of row `r` is checked: either it has no gates and its
multiplicity normalises to zero, or its message template passes
`Template.check` against `msgCircuit` and covers its variables. -/
def msgOk (a : Air F) (r k : Nat) (defOf : Ref → Option (LGate F)) (gs : Array (LGate F)) : Bool :=
  match msgTemplate a defOf gs with
  | .ok none => (Poly.norm (Poly.ofExpr (multExpr a r k))).isEmpty
  | .ok (some (T, count)) =>
      T.check (msgCircuit a r k count) && coversVars T (a.circuit.width + 6) (msgCircuit a r k count)
  | .error _ => false

theorem msgOk_spec {a : Air F} {r k : Nat} {defOf : Ref → Option (LGate F)} {gs : Array (LGate F)}
    (h : msgOk a r k defOf gs = true) :
    (msgTemplate a defOf gs = .ok none ∧ (Poly.norm (Poly.ofExpr (multExpr a r k))).isEmpty = true) ∨
      ∃ T count, msgTemplate a defOf gs = .ok (some (T, count)) ∧ T.check (msgCircuit a r k count) = true ∧
        coversVars T (a.circuit.width + 6) (msgCircuit a r k count) = true := by
  unfold msgOk at h
  split at h
  · rename_i hT; exact .inl ⟨hT, h⟩
  · rename_i T count hT; simp only [Bool.and_eq_true] at h; exact .inr ⟨T, count, hT, h.1, h.2⟩
  · exact absurd h (by simp)

omit [Field F] [DecidableEq F] in
/-- The defining gates of a row's local wires, and each lookup's gates. -/
def rowIndex (s : Lower.St F) : Std.HashMap Ref (LGate F) × Std.HashMap Nat (Array (LGate F)) := Id.run do
  let mut localDef : Std.HashMap Ref (LGate F) := {}
  let mut byMsg : Std.HashMap Nat (Array (LGate F)) := {}
  for g in s.gates do
    match g.msg with
    | some k => byMsg := byMsg.insert k ((byMsg.getD k #[]).push g)
    | none => if g.root.isNone then localDef := localDef.insert g.c g
  return (localDef, byMsg)

/-- Check every lookup of row `r`; `poolDef` gives the defining gate of
every pool wire created so far. -/
def checkMessages (name : String) (a : Air F) (r : Nat) (s : Lower.St F)
    (poolDef : Ref → Option (LGate F)) : Except String Unit := do
  let (localDef, byMsg) := rowIndex s
  let defOf (x : Ref) : Option (LGate F) := if x % 4 == 2 then poolDef x else localDef[x]?
  for k in [0:a.circuit.lookups.length] do
    unless msgOk a r k defOf (byMsg.getD k #[]) do
      throw s!"{name}: lookup {k} is not implied by its gates"

end MsgChecks

end AirIn

end Aiur.Plonk
