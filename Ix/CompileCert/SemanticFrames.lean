import Ix.SemanticContract
import Ix.CompileCert.Loop
import Init.Internal.Order.While
import Std.Data.HashSet.Lemmas

/-! Semantic payload decoding and binder placement in the actual inspector.
This does not establish scope, resource typing or value preservation. -/
namespace Ix.CompileCert.SemanticFrames
open Ix (Expr)
open Ix.SemanticContract

def fits : Kind → Expr → Bool
  | .lam, .lam .. | .all, .forallE .. | .letE, .letE .. => true
  | _, _ => false

def Root : Expr → Prop
  | .mdata data inner _ => hasMetadata data = true →
      ∃ c, read data = .ok c ∧ fits c.kind inner = true
  | _ => True

def children : Expr → Array Expr
  | .app f a _ => (#[].push f).push a
  | .lam _ t b _ _ | .forallE _ t b _ _ => (#[].push t).push b
  | .letE _ t v b _ _ => ((#[].push t).push v).push b
  | .proj _ _ x _ | .mdata _ x _ => #[x]
  | _ => #[]

def Frames : Expr → Prop
  | .app f a _ => Frames f ∧ Frames a
  | .lam _ t b _ _ | .forallE _ t b _ _ => Frames t ∧ Frames b
  | .letE _ t v b _ _ => Frames t ∧ Frames v ∧ Frames b
  | .proj _ _ x _ => Frames x
  | e@(.mdata _ x _) => Root e ∧ Frames x
  | _ => True

def Shell (e out : Expr) : Prop := match e, out with
  | .forallE n _ _ bi _, .forallE n' _ _ bi' _ => n = n' ∧ bi = bi'
  | .letE n _ _ _ nd _, .letE n' _ _ _ nd' _ => n = n' ∧ nd = nd'
  | .mdata data _ _, .mdata data' _ _ => data = data'
  | .forallE .., _ | .letE .., _ | .mdata .., _ => False
  | _, _ => True

theorem frames_iff (e : Expr) : Frames e ↔ Root e ∧ ∀ x ∈ children e, Frames x := by
  cases e <;> simp [Frames, Root, children]

noncomputable def weight (stack : Array Expr) : Nat := (stack.toList.map sizeOf).sum

theorem children_weight (e : Expr) : weight (children e) < sizeOf e := by
  cases e <;> simp [children, weight] <;> omega

abbrev Seen := Std.HashSet Ix.Compile.ExactKey.ExprKey
abbrev State := Seen × Array Expr × Bool

-- This is the inspector's actual elaborated loop body; inspect_eq below
-- checks the connection by definitional equality, not a callback premise.
def step (_ : Unit) (state : State) : Except String (ForInStep State) := do
  let mut seen := state.1
  let mut stack := state.2.1
  let mut annotated := state.2.2
  if !stack.isEmpty then
    let e := stack.back!
    stack := stack.pop
    if seen.contains ⟨e⟩ then return .yield (seen, stack, annotated)
    seen := seen.insert ⟨e⟩
    match e with
    | .app fn arg _ => stack := stack.push fn |>.push arg
    | .lam _ type body _ _ | .forallE _ type body _ _ =>
      stack := stack.push type |>.push body
    | .letE _ type value body _ _ => stack := stack.push type |>.push value |>.push body
    | .proj _ _ value _ => stack := stack.push value
    | .mdata data inner _ =>
      if hasMetadata data then
        let contract ← read data
        unless fits contract.kind inner do
          throw "semantic contract is not attached to its original binder"
        annotated := true
      stack := stack.push inner
    | _ => pure ()
    return .yield (seen, stack, annotated)
  else return .done (seen, stack, annotated)

def scan (state : State) : Except String State := Lean.Loop.forIn {} state step

theorem inspect_eq (e : Expr) : inspect e = (do
    let state ← scan ({}, #[e], false)
    pure state.2.2) := rfl

theorem scan_eq (state : State) : scan state = (do
    match ← step () state with
    | .done out => pure out
    | .yield next => scan next) := by
  unfold scan
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases step () state with
  | error _ => rfl
  | ok result => cases result <;> rfl

def marked : Expr → Bool
  | .mdata data _ _ => hasMetadata data | _ => false

def next (seen : Seen) (rest : Array Expr) (flag : Bool) (e : Expr) : State :=
  (seen.insert ⟨e⟩, rest ++ children e, flag || marked e)

theorem step_empty (seen : Seen) (flag : Bool) :
    step () (seen, #[], flag) = .ok (.done (seen, #[], flag)) := rfl

theorem step_seen (seen : Seen) (rest : Array Expr) (flag : Bool) (e : Expr)
    (hit : seen.contains ⟨e⟩ = true) :
    step () (seen, rest.push e, flag) = .ok (.yield (seen, rest, flag)) := by
  simp [step, hit, pure, Except.pure]

theorem step_fresh (seen : Seen) (rest : Array Expr) (flag : Bool) (e : Expr)
    (miss : seen.contains ⟨e⟩ = false) (result : ForInStep State) :
    step () (seen, rest.push e, flag) = .ok result ↔
      Root e ∧ result = .yield (next seen rest flag e) := by
  cases e
  case mdata data inner hash =>
    cases present : hasMetadata data
    · simp [step, miss, Root, next, children, marked, present, pure, Except.pure]
      exact eq_comm
    · cases decoded : read data with
      | error error => simp [step, miss, Root, next, children, marked, present, decoded, bind, Except.bind]
      | ok c =>
        cases compatible : fits c.kind inner <;>
          simp [step, miss, Root, next, children, marked, present, decoded, compatible,
            bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
        exact eq_comm
  all_goals simp [step, miss, Root, next, children, marked, pure, Except.pure]
  all_goals exact eq_comm

theorem weight_push (rest : Array Expr) (e : Expr) :
    weight (rest.push e) = weight rest + sizeOf e := by simp [weight]

theorem weight_append (a b : Array Expr) :
    weight (a ++ b) = weight a + weight b := by simp [weight, List.sum_append]

theorem child_small {e x : Expr} (member : x ∈ children e) : sizeOf x < sizeOf e := by
  cases e <;> simp [children] at member
  all_goals first
    | (subst x; simp +arith)
    | (rcases member with rfl | rfl; all_goals simp +arith)
    | (rcases member with rfl | rfl | rfl; all_goals simp +arith)

def Covered (root : Expr) (state : State) : Prop :=
  (⟨root⟩ ∈ state.1 ∨ root ∈ state.2.1) ∧
    ∀ e, ⟨e⟩ ∈ state.1 → Root e ∧
      ∀ x ∈ children e, ⟨x⟩ ∈ state.1 ∨ x ∈ state.2.1

theorem covered_frames {root : Expr} {state : State} (covered : Covered root state)
    (ready : ∀ e ∈ state.2.1, Frames e) : Frames root := by
  have checked : ∀ e, (⟨e⟩ : Ix.Compile.ExactKey.ExprKey) ∈ state.1 → Frames e := by
    intro e
    induction e using (measure (fun e : Expr => sizeOf e)).wf.induction with
    | h e ih =>
      intro member
      rw [frames_iff]
      refine ⟨(covered.2 e member).1, ?_⟩
      intro x child
      rcases (covered.2 e member).2 x child with old | pending
      · exact ih x (child_small child) old
      · exact ready x pending
  exact covered.1.elim (checked root) (ready root)

theorem covered_seen {root e : Expr} {seen : Seen} {rest : Array Expr} {flag : Bool}
    (hit : (⟨e⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen)
    (covered : Covered root (seen, rest.push e, flag)) : Covered root (seen, rest, flag) := by
  have shrink : ∀ x, (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen ∨ x ∈ rest.push e →
      (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen ∨ x ∈ rest := by
    intro x h
    rcases h with old | pending
    · exact .inl old
    · rcases Array.mem_push.mp pending with old | rfl
      · exact .inr old
      · exact .inl hit
  exact ⟨shrink root covered.1, fun x hx =>
    ⟨(covered.2 x hx).1, fun y hy => shrink y ((covered.2 x hx).2 y hy)⟩⟩

theorem covered_next {root e : Expr} {seen : Seen} {rest : Array Expr} {flag : Bool}
    (validHead : Root e) (covered : Covered root (seen, rest.push e, flag)) :
    Covered root (next seen rest flag e) := by
  have keep : ∀ x, (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen →
      (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen.insert ⟨e⟩ := by
    intro x hx; exact Std.HashSet.mem_insert.mpr (.inr hx)
  have grow : ∀ x, (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen ∨ x ∈ rest.push e →
      (⟨x⟩ : Ix.Compile.ExactKey.ExprKey) ∈ seen.insert ⟨e⟩ ∨ x ∈ rest ++ children e := by
    intro x h
    rcases h with old | pending
    · exact .inl (keep x old)
    · rcases Array.mem_push.mp pending with old | rfl
      · exact .inr (Array.mem_append.mpr (.inl old))
      · exact .inl (by simp)
  refine ⟨grow root covered.1, ?_⟩
  intro x hx
  simp only [next, Std.HashSet.mem_insert, beq_iff_eq, Ix.Compile.ExactKey.ExprKey.mk.injEq] at hx
  rcases hx with rfl | old
  · exact ⟨validHead, fun y hy => .inr (Array.mem_append.mpr (.inr hy))⟩
  · exact ⟨(covered.2 x old).1, fun y hy => grow y ((covered.2 x old).2 y hy)⟩

theorem initial (e : Expr) : Covered e ({}, #[e], false) := by simp [Covered]

theorem next_decreases (seen : Seen) (rest : Array Expr) (flag : Bool) (e : Expr) :
    weight (next seen rest flag e).2.1 < weight (rest.push e) := by
  simpa only [next, weight_append, weight_push] using Nat.add_lt_add_left (children_weight e) (weight rest)

theorem scan_empty (seen : Seen) (flag : Bool) : scan (seen, #[], flag) = .ok (seen, #[], flag) := by
  rw [scan_eq, step_empty]; rfl

private theorem scan_facts (state : State) :
    (∀ root, Covered root state → ∀ out, scan state = .ok out →
      Covered root out ∧ out.2.1 = #[]) ∧
    ((∀ e ∈ state.2.1, Frames e) → ∃ out, scan state = .ok out) := by
  induction state using (measure (fun s : State => weight s.2.1)).wf.induction with
  | h state ih =>
    rcases state with ⟨seen, stack, flag⟩
    by_cases empty : stack = #[]
    · subst stack
      constructor
      · intro root covered out run
        rw [scan_empty] at run
        cases Except.ok.inj run
        exact ⟨covered, rfl⟩
      · intro _; exact ⟨_, scan_empty seen flag⟩
    · obtain ⟨rest, e, rfl⟩ := Array.exists_push_of_ne_empty empty
      cases hit : seen.contains ⟨e⟩ with
      | false =>
        have smaller := ih (next seen rest flag e) (next_decreases seen rest flag e)
        constructor
        · intro root covered out run
          rw [scan_eq] at run
          obtain ⟨result, first, last⟩ := Loop.except_bind_ok.mp run
          obtain ⟨validHead, rfl⟩ := (step_fresh seen rest flag e hit result).mp first
          exact smaller.1 root (covered_next validHead covered) out last
        · intro ready
          have head := (frames_iff e).mp (ready e (by simp))
          have pending : ∀ x ∈ (next seen rest flag e).2.1, Frames x := by
            intro x member
            rcases Array.mem_append.mp member with old | child
            · exact ready x (Array.mem_push.mpr (.inl old))
            · exact head.2 x child
          obtain ⟨out, run⟩ := smaller.2 pending
          refine ⟨out, ?_⟩
          rw [scan_eq, (step_fresh seen rest flag e hit _).mpr ⟨head.1, rfl⟩]
          exact run
      | true =>
        have decrease : weight rest < weight (rest.push e) := by
          rw [weight_push]; have := children_weight e; omega
        have smaller := ih (seen, rest, flag) decrease
        constructor
        · intro root covered out run
          rw [scan_eq, step_seen seen rest flag e hit] at run
          exact smaller.1 root (covered_seen (Std.HashSet.mem_iff_contains.mpr hit) covered) out run
        · intro ready
          obtain ⟨out, run⟩ := smaller.2 (fun x hx => ready x (Array.mem_push.mpr (.inl hx)))
          refine ⟨out, ?_⟩
          rw [scan_eq, step_seen seen rest flag e hit]
          exact run

/-- The actual guard accepts exactly structurally valid frames. This does
not characterize the annotation bit or assert resource/value semantics. -/
theorem inspect_frames_iff (e : Expr) : (∃ b, inspect e = .ok b) ↔ Frames e := by
  constructor
  · rintro ⟨b, run⟩
    rw [inspect_eq] at run
    obtain ⟨state, scanned, _⟩ := Loop.except_bind_ok.mp run
    obtain ⟨covered, empty⟩ := (scan_facts ({}, #[e], false)).1 e (initial e) state scanned
    exact covered_frames covered (by rw [empty]; simp)
  · intro valid
    obtain ⟨state, scanned⟩ := (scan_facts ({}, #[e], false)).2 (by simpa using valid)
    refine ⟨state.2.2, ?_⟩
    rw [inspect_eq, scanned]; rfl

end Ix.CompileCert.SemanticFrames
