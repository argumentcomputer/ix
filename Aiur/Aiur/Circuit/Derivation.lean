import Aiur.Circuit.Basic

namespace Aiur.Circuit

variable {F : Type} {rom : WireROM F}

mutual
  /--
  A closed, finite derivation of a message. Local validity is a side condition;
  all enabled calls must be discharged by child derivations. There is no assumption rule.
  -/
  inductive Derivation [Field F] [DecidableEq F] (system : System F) (rom : WireROM F) : Message F → Type where
    | node (chip : Chip F) (row : Row F)
        (lookup : system.findChip? row.chip = some chip)
        (valid : chip.ValidRow rom row)
        (children : Derivations system rom (chip.premises row)) :
        Derivation system rom (chip.receive row)
    | table (member : system.MapClaim message) : Derivation system rom message

  /-- A finite list of proofs indexed by its list of premise occurrences. -/
  inductive Derivations [Field F] [DecidableEq F] (system : System F) (rom : WireROM F) : List (Message F) → Type where
    | nil : Derivations system rom []
    | cons (head : Derivation system rom message) (tail : Derivations system rom messages) :
        Derivations system rom (message :: messages)
end

/-- Derivability asserts the existence of a closed derivation tree. -/
def Derives [Field F] [DecidableEq F] (system : System F) (rom : WireROM F) (message : Message F) : Prop :=
  Nonempty (Derivation system rom message)

/-- The circuit relation for one function's arguments and claimed result. -/
def CircuitEvaluates [Field F] [DecidableEq F] (system : System F) (rom : WireROM F)
    (function : String) (args : List (WireValue F)) (result : WireValue F) : Prop :=
  Derives system rom ⟨function, args, result⟩

/-- Assemble a forest from proofs of every premise, retaining repeated occurrences. -/
theorem derivations_nonempty_iff [Field F] [DecidableEq F] {system : System F}
    {messages : List (Message F)} :
    Nonempty (Derivations system rom messages) ↔ ∀ message ∈ messages, Derives system rom message := by
  induction messages with
  | nil =>
      constructor
      · intros; contradiction
      · intro _; exact ⟨.nil⟩
  | cons message messages ih =>
      constructor
      · rintro ⟨children⟩
        cases children with
        | cons head tail =>
            intro next member
            rcases List.mem_cons.mp member with same | member
            · subst next; exact ⟨head⟩
            · exact ih.mp ⟨tail⟩ next member
      · intro premises
        obtain ⟨head⟩ := premises message (by simp)
        obtain ⟨tail⟩ := ih.mpr (fun next member => premises next (by simp [member]))
        exact ⟨.cons head tail⟩

mutual
  /-- Flatten a tree to rows, retaining separate occurrences of identical calls. -/
  def Derivation.rows [Field F] [DecidableEq F] {system : System F} {message : Message F} :
      Derivation system rom message → List (Row F)
    | .node _ row _ _ children => row :: children.rows
    | .table _ => []

  def Derivations.rows [Field F] [DecidableEq F] {system : System F} {messages : List (Message F)} :
      Derivations system rom messages → List (Row F)
    | .nil => []
    | .cons head tail => head.rows ++ tail.rows
end

theorem Derivation.rows_ne_nil [Field F] [DecidableEq F] {system : System F}
    {message : Message F} (derivation : Derivation system rom message)
    (dynamic : ¬ system.MapClaim message) : derivation.rows ≠ [] := by
  cases derivation with
  | node => simp [Derivation.rows]
  | table member => exact (dynamic member).elim

/-- If every valid rule requires a call, no finite closed derivation can start. -/
theorem not_derives_of_no_leaves [Field F] [DecidableEq F] {system : System F}
    (noTables : system.mapClaims = [])
    (requiresCall : ∀ chip row, system.findChip? row.chip = some chip →
      chip.ValidRow rom row → chip.premises row ≠ []) (message : Message F) :
    ¬ Derives system rom message := by
  rintro ⟨derivation⟩
  induction derivation using Derivation.rec
    (motive_2 := fun messages _ => messages ≠ [] → False) with
  | node chip row lookup valid _ childrenIH =>
      exact childrenIH (requiresCall chip row lookup valid)
  | table member => simp [System.MapClaim, noTables] at member
  | nil => exact absurd rfl ‹([] : List (Message F)) ≠ []›
  | cons _ _ headIH _ => exact headIH

end Aiur.Circuit
