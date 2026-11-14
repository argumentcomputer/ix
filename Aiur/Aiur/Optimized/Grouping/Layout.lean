import Aiur.Optimized.Grouping
import Aiur.Optimized.PolynomialIdentity

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

structure Lookup (F : Type) where
  enable : Polynomial F
  args : List (Polynomial F)

structure Member (F : Type) where
  name : String
  columns : Array Nat
  selector : Nat
  /-- Private message arguments of degree two, populated after the source row. -/
  writes : List (Nat × Polynomial F) := []
  origin : Chip F
  privateCols : List Nat

def Member.source (m : Member F) : Chip F := Activation.compile m.origin
def Member.sourceSelector (m : Member F) : Nat := m.origin.numVars

structure Layout (F : Type) where
  name : String
  width : Nat
  members : List (Member F)
  receive : List (Polynomial F)
  sends : List (Lookup F)

def rename (columns : Array Nat) (p : Polynomial F) : Polynomial F :=
  p.subst (fun v => .var (columns[v]?.getD 0))

omit [DecidableEq F] in
@[simp] theorem rename_denote (columns : Array Nat) (p : Polynomial F) (a : Nat → F) :
    (rename columns p).denote a = p.denote (fun v => a (columns[v]?.getD 0)) := by
  simp [rename, Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote]

def plus (a b : Polynomial F) : Polynomial F := Polynomial.simplify (.add a b)
def sum (ps : List (Polynomial F)) : Polynomial F := ps.foldl plus (.const 0)

def Member.constraints (m : Member F) : List (Polynomial F) :=
  (member m.source m.sourceSelector m.privateCols).constraints.map (rename m.columns) ++
    m.writes.flatMap fun (column, value) =>
      [.mul (.var m.selector) (.sub (.var column) value), privateZero m.selector column]

def exclusions : List (Polynomial F) → List (Polynomial F)
  | [] => []
  | s :: ss => .mul s (sum ss) :: exclusions ss

def Layout.activation (g : Layout F) : Polynomial F :=
  sum (g.members.map fun m => .var m.selector)

def Layout.rawConstraints (g : Layout F) : List (Polynomial F) :=
  g.members.flatMap Member.constraints ++ exclusions (g.members.map fun m => .var m.selector)

def Layout.constraints (g : Layout F) : List (Polynomial F) :=
  (g.rawConstraints.map Polynomial.simplify).filter (· != .const 0)

/-- Projection from the actual emitted constraints, not a parallel circuit
model. Renaming shares data columns, but the selected member satisfies exactly
the original constraint list. Memory membership is recovered from its selected
lookup messages, just as for an ungrouped physical chip. -/
theorem Layout.member_constraints (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a) :
    Satisfies (member m.source m.sourceSelector m.privateCols).constraints
      (fun v => a (m.columns[v]?.getD 0)) := by
  intro p hp
  have included : rename m.columns p ∈ g.members.flatMap Member.constraints := by
    apply List.mem_flatMap.mpr
    refine ⟨m, present, List.mem_append_left _ ?_⟩
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  by_cases zero : (rename m.columns p).simplify = .const 0
  · have h := congrArg (fun p : Polynomial F => p.denote a) zero
    simpa only [Polynomial.denote_simplify, rename_denote, Scalar.Circuit.ArithExpr.denote] using h
  · have h := valid ((rename m.columns p).simplify) (by
      unfold Layout.constraints Layout.rawConstraints
      apply List.mem_filter.mpr
      constructor
      · exact List.mem_map.mpr ⟨_, List.mem_append_left _ included, rfl⟩
      · change (!((rename m.columns p).simplify == .const 0)) = true
        cases h : ((rename m.columns p).simplify == .const 0) with
        | false => rfl
        | true => exact (zero ((Polynomial.beq_eq _ _).mp h)).elim)
    simpa only [Polynomial.denote_simplify, rename_denote] using h

theorem Layout.selected_member_sound (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a)
    (active : a (m.columns[m.sourceSelector]?.getD 0) = 1)
    (memory : ∀ lookup ∈ m.source.memory,
      lookup.Valid rom (fun v => a (m.columns[v]?.getD 0))) :
    m.source.ValidAssignment rom (fun v => a (m.columns[v]?.getD 0)) := by
  exact (member_active m.source m.sourceSelector m.privateCols
    (fun v => a (m.columns[v]?.getD 0)) active).mp ⟨g.member_constraints m present a valid, memory⟩
def plusArgs (xs ys : List (Polynomial F)) : List (Polynomial F) :=
  (List.range (max xs.length ys.length)).map fun i =>
    plus (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))

def messages (id : String → Except String Nat) (source : Chip F) :
    Except String (List (Polynomial F) × List (Lookup F)) := do
  let call ← id source.name
  let receive := [.const 1, .const call] ++
    (source.inputs.flatMap WireValue.words).map .var ++ source.output.words
  let sends ← source.sends.mapM fun s => do
    let callee ← id s.channel
    return Lookup.mk s.enable ([.const 1, .const callee] ++
      s.args.flatMap WireValue.words ++ s.result.words.map .var)
  let memory := source.memory.map fun m =>
    Lookup.mk m.enable ([.const 2, .const m.value.words.length, m.address] ++ m.value.words)
  return (receive, sends ++ memory)


end Aiur.Optimized.Grouping
