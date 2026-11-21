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
  /-- Per-member slot assignment mapping each logical lookup index
  `0 .. origin.sends.length + origin.memory.length - 1` to its physical slot
  index in `Layout.sends`. Empty defaults to the identity map `i ↦ i`. -/
  slotMap : Array Nat := #[]

def slotOf (slotMap : Array Nat) (i : Nat) : Nat := slotMap[i]?.getD i
def bucketOf (slotMap : Array Nat) (n s : Nat) : List Nat :=
  (List.range n).filter fun i => slotOf slotMap i == s

def Member.source (m : Member F) : Chip F := Activation.compile m.origin
def Member.sourceSelector (m : Member F) : Nat := m.origin.numVars
def Member.slotIndex (m : Member F) (i : Nat) : Nat := slotOf m.slotMap i
def Member.numLookups (m : Member F) : Nat := m.origin.sends.length + m.origin.memory.length
def Member.bucket (m : Member F) (s : Nat) : List Nat :=
  bucketOf m.slotMap m.numLookups s

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

theorem Layout.selected_origin_constraints (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a)
    (active : a (m.columns[m.sourceSelector]?.getD 0) = 1) :
    Satisfies m.origin.constraints (fun v => a (m.columns[v]?.getD 0)) := by
  intro p hp
  let b := fun v : Nat => a (m.columns[v]?.getD 0)
  have on : b m.sourceSelector = 1 := active
  have on' : b m.origin.numVars = 1 := on
  have mc := g.member_constraints m present a valid
  have hmem : gate m.sourceSelector m.privateCols (Activation.polynomial m.origin.numVars p) ∈
      (member m.source m.sourceSelector m.privateCols).constraints := by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩)), rfl⟩
  have hz := mc _ hmem
  simpa only [b, gate_active _ _ _ _ on,
    Activation.polynomial_active m.origin.numVars p b on'] using hz

def plusArgs (xs ys : List (Polynomial F)) : List (Polynomial F) :=
  (List.range (max xs.length ys.length)).map fun i =>
    plus (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))

def encodeSend (id : String → Except String Nat) (s : Send F) : Except String (Lookup F) := do
  let callee ← id s.channel
  return Lookup.mk s.enable ([.const 1, .const callee] ++
    s.args.flatMap WireValue.words ++ s.result.words.map .var)

def messages (id : String → Except String Nat) (source : Chip F) :
    Except String (List (Polynomial F) × List (Lookup F)) := do
  let call ← id source.name
  let receive := [.const 1, .const call] ++
    (source.inputs.flatMap WireValue.words).map .var ++ source.output.words
  let sends ← source.sends.mapM (encodeSend id)
  let memory := source.memory.map fun m =>
    Lookup.mk m.enable ([.const 2, .const m.value.words.length, m.address] ++ m.value.words)
  return (receive, sends ++ memory)

private theorem mapM_except_length {α β ε : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
  | x :: xs, ys, h => by
      rw [List.mapM_cons] at h
      cases hx : f x with
      | error _ => simp [hx, bind, Except.bind] at h
      | ok y =>
          simp only [hx, bind, Except.bind] at h
          cases hxs : xs.mapM f with
          | error _ => simp [hxs] at h
          | ok ys' =>
              simp only [hxs, pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp [mapM_except_length f hxs]

theorem messages_required_length {id : String → Except String Nat} {source : Chip F}
    {provided : List (Polynomial F)} {required : List (Lookup F)}
    (h : messages id source = .ok (provided, required)) :
    required.length = source.sends.length + source.memory.length := by
  unfold messages at h
  cases hid : id source.name with
  | error _ => simp [hid, bind, Except.bind] at h
  | ok call =>
      simp only [hid, bind, Except.bind] at h
      cases hsends : source.sends.mapM (encodeSend id) with
      | error _ => simp [hsends] at h
      | ok sends =>
          simp only [hsends, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          simp [mapM_except_length _ hsends]

end Aiur.Optimized.Grouping
