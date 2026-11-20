/-!
# DPLL for CNF

A satisfiability decision procedure for formulas in conjunctive normal form over atoms `0, 1, …`:
unit propagation and splitting, as one rule. `dpll` looks at a shortest clause: if it is empty
the formula is unsatisfiable, if it is a unit `[l]` it assigns `l` (unit propagation), and
otherwise it splits on the clause's first literal. Assigning a literal (`assign`) removes every
occurrence of its atom, so the total clause length (`size`) drops at each call and `size F + 1`
fuel always suffices (`dpll_iff`).

`solve_iff` proves `solve F = true ↔ ∃ σ, cnfEval σ F = true`. The procedure is structurally
recursive on its fuel, so a label it computes is a closed term the kernel can evaluate.
-/

namespace IxAICore
namespace Dpll

/-- A literal: an atom and its polarity (`true` for the atom, `false` for its negation). -/
abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev CNF := List Clause

def litEval (σ : Nat → Bool) (l : Lit) : Bool := σ l.1 == l.2
def clauseEval (σ : Nat → Bool) (c : Clause) : Bool := c.any (litEval σ)
def cnfEval (σ : Nat → Bool) (F : CNF) : Bool := F.all (clauseEval σ)

/-- `F` with literal `l` made true: clauses containing `l` are dropped, and the other clauses lose
every literal over `l`'s atom (each of which is then false). -/
def assign (l : Lit) : CNF → CNF
  | [] => []
  | c :: F => if c.contains l then assign l F else c.filter (fun m => m.1 != l.1) :: assign l F

/-- Total number of literal occurrences. -/
def size : CNF → Nat
  | [] => 0
  | c :: F => c.length + size F

/-- The first clause of least length. -/
def shortest : CNF → Option Clause
  | [] => none
  | c :: F =>
    match shortest F with
    | none => some c
    | some d => if d.length < c.length then some d else some c

def dpll : Nat → CNF → Bool
  | 0, _ => false
  | fuel + 1, F =>
    match shortest F with
    | none => true
    | some [] => false
    | some (l :: rest) =>
      if rest.isEmpty then dpll fuel (assign l F)
      else dpll fuel (assign l F) || dpll fuel (assign (l.1, !l.2) F)

def solve (F : CNF) : Bool := dpll (size F + 1) F

/-! ## Correctness -/

theorem clauseEval_of_mem {σ : Nat → Bool} {c : Clause} {m : Lit} (hm : m ∈ c)
    (h : litEval σ m = true) : clauseEval σ c = true := by
  simp only [clauseEval, List.any_eq_true]
  exact ⟨m, hm, h⟩

/-- Dropping literals that are false leaves a clause's value unchanged. -/
theorem clauseEval_filter {σ : Nat → Bool} (p : Lit → Bool) (c : Clause)
    (h : ∀ m ∈ c, p m = false → litEval σ m = false) : clauseEval σ (c.filter p) = clauseEval σ c := by
  induction c with
  | nil => rfl
  | cons m c ih =>
    have ih := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hp : p m = true
    · simp only [List.filter_cons, hp, ite_true, clauseEval, List.any_cons] at ih ⊢
      rw [ih]
    · have hf : p m = false := by simpa using hp
      simp only [List.filter_cons, hf, clauseEval, List.any_cons, h m (List.mem_cons_self) hf,
        Bool.false_or] at ih ⊢
      exact ih

theorem cnfEval_cons (σ : Nat → Bool) (c : Clause) (F : CNF) :
    cnfEval σ (c :: F) = (clauseEval σ c && cnfEval σ F) := by
  simp [cnfEval]

theorem assign_eval {σ : Nat → Bool} {l : Lit} (hl : litEval σ l = true) :
    ∀ F : CNF, cnfEval σ (assign l F) = cnfEval σ F
  | [] => rfl
  | c :: F => by
    have ih := assign_eval hl F
    by_cases hc : c.contains l = true
    · simp only [assign, hc, ite_true, ih, cnfEval_cons]
      rw [clauseEval_of_mem (List.contains_iff_mem.mp hc) hl, Bool.true_and]
    · simp only [assign, hc, cnfEval_cons, ih, Bool.false_eq_true, ite_false]
      congr 1
      apply clauseEval_filter
      intro m hm hp
      have hcl : m ≠ l := fun e => hc (List.contains_iff_mem.mpr (e ▸ hm))
      have h1 : m.1 = l.1 := by simpa using hp
      have h2 : m.2 ≠ l.2 := fun e => hcl (Prod.ext h1 e)
      simp only [litEval] at hl ⊢
      have : σ l.1 = l.2 := by simpa using hl
      rw [h1, this]
      cases hm2 : m.2 <;> cases hl2 : l.2 <;> simp_all

/-- No literal of `assign l F` is over `l`'s atom. -/
theorem atom_ne_of_mem_assign {l : Lit} :
    ∀ {F : CNF} {c : Clause} {m : Lit}, c ∈ assign l F → m ∈ c → m.1 ≠ l.1
  | [], _, _, hc, _ => by simp [assign] at hc
  | d :: F, c, m, hc, hm => by
    unfold assign at hc
    split at hc
    · exact atom_ne_of_mem_assign hc hm
    · rcases List.mem_cons.mp hc with rfl | hc
      · have := (List.mem_filter.mp hm).2
        simpa using this
      · exact atom_ne_of_mem_assign hc hm

theorem clauseEval_congr {σ τ : Nat → Bool} :
    ∀ {c : Clause}, (∀ m ∈ c, σ m.1 = τ m.1) → clauseEval σ c = clauseEval τ c
  | [], _ => rfl
  | m :: c, h => by
    have ih : clauseEval σ c = clauseEval τ c :=
      clauseEval_congr fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [clauseEval, List.any_cons] at ih ⊢
    rw [ih]
    simp [litEval, h m List.mem_cons_self]

/-- The value of `F` depends only on the atoms occurring in it. -/
theorem cnfEval_congr {σ τ : Nat → Bool} :
    ∀ {F : CNF}, (∀ c ∈ F, ∀ m ∈ c, σ m.1 = τ m.1) → cnfEval σ F = cnfEval τ F
  | [], _ => rfl
  | c :: F, h => by
    rw [cnfEval_cons, cnfEval_cons, cnfEval_congr fun d hd => h d (List.mem_cons_of_mem _ hd),
      clauseEval_congr (h c List.mem_cons_self)]

def Sat (F : CNF) : Prop := ∃ σ : Nat → Bool, cnfEval σ F = true

/-- The assignment `σ` with atom `l.1` set so that `l` is true. -/
def setLit (σ : Nat → Bool) (l : Lit) : Nat → Bool := fun i => if i = l.1 then l.2 else σ i

theorem sat_of_sat_assign {l : Lit} {F : CNF} (h : Sat (assign l F)) : Sat F := by
  obtain ⟨σ, hσ⟩ := h
  have hl : litEval (setLit σ l) l = true := by simp [litEval, setLit]
  refine ⟨setLit σ l, ?_⟩
  rw [← assign_eval hl, cnfEval_congr (τ := σ), hσ]
  intro c hc m hm
  simp [setLit, atom_ne_of_mem_assign hc hm]

theorem sat_assign_of_mem {l : Lit} {F : CNF} (hu : [l] ∈ F) (h : Sat F) : Sat (assign l F) := by
  obtain ⟨σ, hσ⟩ := h
  have hc : clauseEval σ [l] = true := by
    simp only [cnfEval, List.all_eq_true] at hσ
    exact hσ _ hu
  have hl : litEval σ l = true := by simpa [clauseEval] using hc
  exact ⟨σ, (assign_eval hl F).trans hσ⟩

theorem sat_split (l : Lit) {F : CNF} (h : Sat F) : Sat (assign l F) ∨ Sat (assign (l.1, !l.2) F) := by
  obtain ⟨σ, hσ⟩ := h
  by_cases hl : σ l.1 = l.2
  · exact .inl ⟨σ, (assign_eval (by simp [litEval, hl]) F).trans hσ⟩
  · refine .inr ⟨σ, (assign_eval ?_ F).trans hσ⟩
    simp only [litEval, beq_iff_eq]
    cases h2 : l.2 <;> simp_all

theorem not_sat_of_nil_mem {F : CNF} (h : [] ∈ F) : ¬ Sat F := by
  rintro ⟨σ, hσ⟩
  simp only [cnfEval, List.all_eq_true] at hσ
  simpa [clauseEval] using hσ _ h

theorem mem_of_shortest : ∀ {F : CNF} {c : Clause}, shortest F = some c → c ∈ F
  | [], _, h => by simp [shortest] at h
  | d :: F, c, h => by
    unfold shortest at h
    split at h
    · cases h; exact List.mem_cons_self
    · rename_i e hd
      split at h
      · cases h; exact List.mem_cons_of_mem _ (mem_of_shortest hd)
      · cases h; exact List.mem_cons_self

theorem shortest_eq_none : ∀ {F : CNF}, shortest F = none → F = []
  | [], _ => rfl
  | _ :: F, h => by
    unfold shortest at h
    split at h
    · cases h
    · split at h <;> cases h

theorem size_assign_le (l : Lit) : ∀ F : CNF, size (assign l F) ≤ size F
  | [] => Nat.le_refl _
  | c :: F => by
    have ih := size_assign_le l F
    unfold assign
    split
    · simp only [size]; omega
    · simp only [size]
      have := List.length_filter_le (fun m : Lit => m.1 != l.1) c
      omega

/-- Assigning an atom that occurs in `F` shrinks it. -/
theorem size_assign_lt (l : Lit) :
    ∀ {F : CNF} {c : Clause} {m : Lit}, c ∈ F → m ∈ c → m.1 = l.1 → size (assign l F) < size F
  | [], _, _, hc, _, _ => by simp at hc
  | d :: F, c, m, hc, hm, he => by
    rcases List.mem_cons.mp hc with rfl | hc
    · have hle := size_assign_le l F
      have hpos : 0 < c.length := List.length_pos_of_mem hm
      unfold assign
      split
      · simp only [size]; omega
      · simp only [size]
        have : (c.filter fun m : Lit => m.1 != l.1).length < c.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨m, hm, by simp [he]⟩
        omega
    · have ih := size_assign_lt l hc hm he
      unfold assign
      split
      · simp only [size]; omega
      · simp only [size]
        have := List.length_filter_le (fun m : Lit => m.1 != l.1) d
        omega

theorem dpll_iff : ∀ (fuel : Nat) (F : CNF), size F < fuel → (dpll fuel F = true ↔ Sat F)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, F, hf => by
    unfold dpll
    split
    · rename_i h
      have hF := shortest_eq_none h
      subst hF
      have hs : Sat [] := ⟨fun _ => false, rfl⟩
      exact iff_of_true rfl hs
    · rename_i h
      exact ⟨fun e => (by cases e), fun hs => absurd hs (not_sat_of_nil_mem (mem_of_shortest h))⟩
    · rename_i l rest h
      have hc := mem_of_shortest h
      have h1 : size (assign l F) < fuel :=
        Nat.lt_of_lt_of_le (size_assign_lt l hc List.mem_cons_self rfl) (Nat.le_of_lt_succ hf)
      have h2 : size (assign (l.1, !l.2) F) < fuel :=
        Nat.lt_of_lt_of_le (size_assign_lt (l.1, !l.2) hc List.mem_cons_self rfl) (Nat.le_of_lt_succ hf)
      split
      · rename_i hr
        have : rest = [] := List.isEmpty_iff.mp hr
        subst this
        rw [dpll_iff fuel _ h1]
        exact ⟨sat_of_sat_assign, sat_assign_of_mem hc⟩
      · rw [Bool.or_eq_true, dpll_iff fuel _ h1, dpll_iff fuel _ h2]
        exact ⟨fun h => h.elim sat_of_sat_assign sat_of_sat_assign, sat_split l⟩

theorem solve_iff (F : CNF) : solve F = true ↔ ∃ σ : Nat → Bool, cnfEval σ F = true :=
  dpll_iff _ F (Nat.lt_succ_self _)

/-! ## Atoms past a bound

Assignments elsewhere are lists of length `n`, which read every atom `≥ n` as false. `restrict n F`
fixes those atoms to false, so its satisfiability over all assignments is that of `F` over lists. -/

def restrict (n : Nat) : CNF → CNF
  | [] => []
  | c :: F =>
    if c.any (fun m => decide (n ≤ m.1) && !m.2) then restrict n F
    else c.filter (fun m => decide (m.1 < n)) :: restrict n F

theorem restrict_eval {σ : Nat → Bool} {n : Nat} (hσ : ∀ i, n ≤ i → σ i = false) :
    ∀ F : CNF, cnfEval σ (restrict n F) = cnfEval σ F
  | [] => rfl
  | c :: F => by
    have ih := restrict_eval hσ F
    unfold restrict
    split
    · rename_i h
      obtain ⟨m, hm, hp⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
      rw [ih, cnfEval_cons, clauseEval_of_mem hm (by simp [litEval, hσ _ hp.1, hp.2]), Bool.true_and]
    · rename_i h
      rw [cnfEval_cons, cnfEval_cons, ih]
      congr 1
      apply clauseEval_filter
      intro m hm hp
      have hn : n ≤ m.1 := by simpa using hp
      have h2 : m.2 = true := by
        cases e : m.2
        · exact absurd (List.any_eq_true.mpr ⟨m, hm, by simp [hn, e]⟩) h
        · rfl
      simp [litEval, hσ _ hn, h2]

theorem atom_lt_of_mem_restrict {n : Nat} :
    ∀ {F : CNF} {c : Clause} {m : Lit}, c ∈ restrict n F → m ∈ c → m.1 < n
  | [], _, _, hc, _ => by simp [restrict] at hc
  | d :: F, c, m, hc, hm => by
    unfold restrict at hc
    split at hc
    · exact atom_lt_of_mem_restrict hc hm
    · rcases List.mem_cons.mp hc with rfl | hc
      · simpa using (List.mem_filter.mp hm).2
      · exact atom_lt_of_mem_restrict hc hm

/-- The assignment read from a list, as `PForm.eval` reads it. -/
def ofList (l : List Bool) : Nat → Bool := fun i => l.getD i false

/-- Satisfiability over assignments of `n` atoms. -/
def satN (n : Nat) (F : CNF) : Bool := solve (restrict n F)

theorem sat_restrict_iff (n : Nat) (F : CNF) :
    Sat (restrict n F) ↔ ∃ l : List Bool, l.length = n ∧ cnfEval (ofList l) F = true := by
  have hlist : ∀ l : List Bool, l.length = n → ∀ i, n ≤ i → ofList l i = false := by
    intro l hl i hi
    simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_eq_none (hl ▸ hi)]
  constructor
  · rintro ⟨σ, hσ⟩
    let l := (List.range n).map σ
    have hl : l.length = n := by simp [l]
    refine ⟨l, hl, ?_⟩
    rw [← restrict_eval (hlist l hl), cnfEval_congr (τ := σ), hσ]
    intro c hc m hm
    have := atom_lt_of_mem_restrict hc hm
    simp [ofList, l, List.getD_eq_getElem?_getD, this]
  · rintro ⟨l, hl, he⟩
    exact ⟨ofList l, (restrict_eval (hlist l hl) F).trans he⟩

theorem satN_iff (n : Nat) (F : CNF) :
    satN n F = true ↔ ∃ l : List Bool, l.length = n ∧ cnfEval (ofList l) F = true := by
  rw [satN, solve_iff]
  exact sat_restrict_iff n F

example : solve [[(0, true), (1, true)], [(0, false)], [(1, false)]] = false := by decide
example : solve [[(0, true), (1, true)], [(0, false), (1, true)], [(1, false), (2, true)]] = true := by decide

/-! ## Refutation within a budget

`lookahead` is a one-sided certificate of unsatisfiability: it never searches for a model, and
when it returns `true` the formula has none (`lookahead_sound`). At each node it runs unit
propagation and failed-literal probing to a fixpoint (`closure`): a literal whose propagation
reaches an empty clause is false in every model, so its complement is asserted (a learned unit),
and the formula is refuted when propagation itself reaches an empty clause. If that does not
refute the node, it splits on a literal and must refute both branches, within a depth and a total
node budget. Every rule only maps a satisfiable formula to a satisfiable one (`SatO`), so the
literal order and the branching choice, passed as functions, are heuristics that soundness does
not depend on. -/

/-- A formula that is satisfiable; `none` stands for a formula already refuted. -/
def SatO : Option CNF → Prop
  | none => False
  | some F => Sat F

/-- Unit propagation for at most `fuel` steps: `none` on reaching an empty clause, otherwise the
formula with the propagated literals assigned. -/
def propagate : Nat → CNF → Option CNF
  | 0, F => some F
  | fuel + 1, F =>
    match shortest F with
    | some [] => none
    | some [l] => propagate fuel (assign l F)
    | _ => some F

theorem propagate_sat : ∀ (fuel : Nat) {F : CNF}, Sat F → SatO (propagate fuel F)
  | 0, _, h => h
  | fuel + 1, F, h => by
    unfold propagate
    split
    · rename_i hs
      exact not_sat_of_nil_mem (mem_of_shortest hs) h
    · rename_i l hs
      exact propagate_sat fuel (sat_assign_of_mem (mem_of_shortest hs) h)
    · exact h

theorem not_sat_of_propagate {fuel : Nat} {F : CNF} (h : propagate fuel F = none) : ¬ Sat F :=
  fun hs => by
    have := propagate_sat fuel hs
    rw [h] at this
    exact this

/-- One failed-literal pass over `ls`: when propagating `l` reaches an empty clause, `l` is false in
every model, so its complement is assigned and propagated before the next literal. -/
def probe (fuel : Nat) : List Lit → Option CNF → Option CNF
  | _, none => none
  | [], some F => some F
  | l :: ls, some F =>
    match propagate fuel (assign l F) with
    | none => probe fuel ls (propagate fuel (assign (l.1, !l.2) F))
    | some _ => probe fuel ls (some F)

theorem probe_sat (fuel : Nat) : ∀ (ls : List Lit) {x : Option CNF}, SatO x → SatO (probe fuel ls x)
  | _, none, h => h.elim
  | [], some _, h => h
  | l :: ls, some F, h => by
    simp only [probe]
    split
    · rename_i hn
      exact probe_sat fuel ls
        (propagate_sat fuel ((sat_split l h).resolve_left (not_sat_of_propagate hn)))
    · exact probe_sat fuel ls h

/-- Propagation and failed-literal passes until a pass changes nothing, at most `rounds` passes. -/
def closure (fuel : Nat) (ls : List Lit) : Nat → CNF → Option CNF
  | 0, F => some F
  | rounds + 1, F =>
    match probe fuel ls (propagate fuel F) with
    | none => none
    | some G => if size G == size F then some G else closure fuel ls rounds G

theorem closure_sat (fuel : Nat) (ls : List Lit) : ∀ (rounds : Nat) {F : CNF}, Sat F →
    SatO (closure fuel ls rounds F)
  | 0, _, h => h
  | rounds + 1, F, h => by
    have hp := probe_sat fuel ls (propagate_sat fuel h)
    simp only [closure]
    split
    · rename_i e
      rw [e] at hp
      exact hp
    · rename_i G e
      rw [e] at hp
      split
      · exact hp
      · exact closure_sat fuel ls rounds hp

/-- Refutation by closure and splitting, at most `depth` levels deep and `budget` nodes in all:
`true` when every leaf was refuted, with the budget left. `lits F` lists the literals to probe at a
node and `pick F` the literal to split on. -/
def lookahead (fuel rounds : Nat) (lits : CNF → List Lit) (pick : CNF → Option Lit) :
    Nat → CNF → Nat → Bool × Nat
  | 0, _, b => (false, b)
  | _ + 1, _, 0 => (false, 0)
  | depth + 1, F, b + 1 =>
    match closure fuel (lits F) rounds F with
    | none => (true, b)
    | some G =>
      match pick G with
      | none => (false, b)
      | some l =>
        let r := lookahead fuel rounds lits pick depth (assign l G) b
        if r.1 then lookahead fuel rounds lits pick depth (assign (l.1, !l.2) G) r.2 else (false, r.2)

theorem lookahead_sound (fuel rounds : Nat) (lits : CNF → List Lit) (pick : CNF → Option Lit) :
    ∀ (depth : Nat) (F : CNF) (b : Nat),
      (lookahead fuel rounds lits pick depth F b).1 = true → ¬ Sat F
  | 0, _, _, h => by simp [lookahead] at h
  | _ + 1, _, 0, h => by simp [lookahead] at h
  | depth + 1, F, b + 1, h => by
    intro hs
    have hc := closure_sat fuel (lits F) rounds hs
    simp only [lookahead] at h
    split at h
    · rename_i e
      rw [e] at hc
      exact hc
    · rename_i G e
      rw [e] at hc
      split at h
      · simp at h
      · rename_i l _
        split at h
        · rename_i h1
          exact (sat_split l hc).elim (lookahead_sound fuel rounds lits pick depth _ _ h1)
            (lookahead_sound fuel rounds lits pick depth _ _ h)
        · simp at h

example : (lookahead 3 2 (fun _ => [(0, true), (0, false), (1, true), (1, false)]) (fun _ => none) 1
    [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)], [(0, false), (1, false)]]
    1).1 = true := by decide

end Dpll
end IxAICore
