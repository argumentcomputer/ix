import Aiur.Generic.AST

/-! Late compilation of native pointer and or-patterns to ordinary core loads
and pattern tests. Failed attempts introduce only fresh names; user bindings
are installed after all tests succeed. The scrutinee is evaluated once. -/

namespace Aiur.Generic

def Pattern.toCore? (env : List (String × Ty)) : Pattern α → Option (Aiur.Pattern α)
  | .literal x => some (.literal x)
  | .wildcard => some .wildcard
  | .bind n => some (.bind n)
  | .global _ _ => none
  | .load _ | .orElse _ _ _ => none
  | .tuple ps | .array ps => return .tuple (← ps.mapM (Pattern.toCore? env))
  | .record head ps => do
      let .enum n := (head.type.subst env).toCore | none
      return .construct n structConstructor (head.order (← ps.mapM (Pattern.toCore? env)) .wildcard)
  | .repeat p n => return .tuple (List.replicate n (← p.toCore? env))
  | .construct t c ps | .constructAs _ t c ps => do
      let .enum n := (t.subst env).toCore | none
      return .construct n c (← ps.mapM (Pattern.toCore? env))
termination_by p => sizeOf p

namespace PatternLowering

def patternNames : Aiur.Pattern α → List String
  | .literal _ | .wildcard => []
  | .bind n => [n]
  | .tuple ps | .construct _ _ ps => ps.flatMap patternNames
termination_by p => sizeOf p

def exprNames : Aiur.Expr α → List String
  | .literal _ => []
  | .var n => [n]
  | .tuple xs | .construct _ _ xs | .call _ xs => xs.flatMap exprNames
  | .project x _ | .store x | .load x | .hint _ x channel | .neg x => exprNames x
  | .letValue p x b => patternNames p ++ exprNames x ++ exprNames b
  | .binary _ x y | .assertEq _ x y | .ptrEq x y => exprNames x ++ exprNames y
  | .matchValue x arms => exprNames x ++ arms.flatMap (fun arm => patternNames arm.1 ++ exprNames arm.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Longer than every existing variable name, including names in already
lowered subexpressions. This also protects programmatically constructed ASTs. -/
def freshPrefix (names : List String) : String :=
  "$pattern" ++ String.ofList (List.replicate (names.foldl (fun n s => max n s.length) 0 + 1) '_') ++ ":"

def fresh (stem : String) : StateM Nat String := do
  let n ← get
  set (n + 1)
  return stem ++ toString n

inductive Step (α : Type) where
  | test (pattern : Aiur.Pattern α) (input : String)
  | load (name input : String)
  | choice (outputs : List (String × String))
      (left : List (Step α)) (leftBindings : List (String × String))
      (right : List (Step α)) (rightBindings : List (String × String)) (rightOrder : List Nat)
  deriving Repr

structure Plan (α : Type) where
  steps : List (Step α) := []
  bindings : List (String × String) := []
  deriving Repr

/-- The tree records the nesting of a pattern before its read/test steps are
flattened. Names belong only to the compiler; `erase` recovers the pattern's
matching condition and user bindings. -/
inductive PlanTree (α : Type) where
  | literal (value : α)
  | wildcard
  | bind (name : String)
  | load (name : String) (child : PlanTree α)
  | choice (stem : String) (left right : PlanTree α) (bindings : OrBindings)
  | tuple (children : List (String × PlanTree α))
  | construct (name ctor : String) (children : List (String × PlanTree α))
  deriving Repr

def PlanTree.erase : PlanTree α → Pattern α
  | .literal x => .literal x
  | .wildcard => .wildcard
  | .bind n => .bind n
  | .load _ child => .load child.erase
  | .choice _ left right names => .orElse left.erase right.erase names
  | .tuple children => .tuple (children.map fun part => part.2.erase)
  | .construct n c children => .construct (.named n []) c (children.map fun part => part.2.erase)
termination_by tree => sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals try cases ‹String × PlanTree α›
  all_goals simp_all only [Prod.mk.sizeOf_spec] <;> omega

def choiceBindings (stem : String) (names : List String) : List (String × String) :=
  names.map fun name => (name, stem ++ ":or:" ++ name)

/-- Copy an alternative's bindings into the shared result slots by recorded position. -/
def choiceLinks (outputs bindings : List (String × String)) (positions : List Nat) :
    Option (List (String × String)) := reorderBindings (outputs.map Prod.snd) positions bindings

def PlanTree.temps : PlanTree F → List String
  | .literal _ | .wildcard | .bind _ => []
  | .load name child => name :: child.temps
  | .choice stem left right names => left.temps ++ right.temps ++
      (choiceBindings stem names.names).map Prod.snd
  | .tuple parts | .construct _ _ parts =>
      parts.map Prod.fst ++ parts.flatMap (fun part => part.2.temps)
termination_by tree => sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals try cases ‹String × PlanTree F›
  all_goals simp_all only [Prod.mk.sizeOf_spec] <;> omega


def PlanTree.toPlan : PlanTree α → String → Plan α
  | .literal x, input => ⟨[.test (.literal x) input], []⟩
  | .wildcard, _ => {}
  | .bind n, input => ⟨[], [(n, input)]⟩
  | .choice stem left right names, input =>
      let l := left.toPlan input
      let r := right.toPlan input
      let outputs := choiceBindings stem names.names
      ⟨[.choice outputs l.steps l.bindings r.steps r.bindings names.rightOrder], outputs⟩
  | .load n child, input =>
      let next := child.toPlan n
      { next with steps := .load n input :: next.steps }
  | .tuple children, input =>
      let parts := children.map fun part => (part.1, part.2.toPlan part.1)
      { steps := .test (.tuple (parts.map (fun part => .bind part.1))) input :: parts.flatMap (·.2.steps)
        bindings := parts.flatMap (·.2.bindings) }
  | .construct n c children, input =>
      let parts := children.map fun part => (part.1, part.2.toPlan part.1)
      { steps := .test (.construct n c (parts.map (fun part => .bind part.1))) input :: parts.flatMap (·.2.steps)
        bindings := parts.flatMap (·.2.bindings) }
termination_by tree _ => sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals try cases ‹String × PlanTree α›
  all_goals simp_all only [Prod.mk.sizeOf_spec] <;> omega

/-- Decompose from left to right. Constructor shape tests will precede payload
reads when the tree is flattened. Arrays retain the same ordered tuple shape. -/
def planTree (env : List (String × Ty)) (stem : String) : Pattern α → StateM Nat (PlanTree α)
  | .literal x => return .literal x
  | .global n _ => return .construct ("$const:" ++ n) "$unexpanded" []
  | .wildcard => return .wildcard
  | .bind n => return .bind n
  | .orElse left right names => do
      let left ← planTree env stem left
      let right ← planTree env stem right
      let name ← fresh stem
      return .choice name left right names
  | .load p => do
      let name ← fresh stem
      return .load name (← planTree env stem p)
  | .tuple ps | .array ps => do
      let parts ← ps.mapM fun p => do
        let name ← fresh stem
        return (name, ← planTree env stem p)
      return .tuple parts
  | .repeat p n => do
      let parts ← (List.range n).mapM fun _ => do
        let name ← fresh stem
        return (name, ← planTree env stem p)
      return .tuple parts
  | .record head ps => do
      let parts ← (head.order (ps.attach.map some) none).mapM fun child => do
        let name ← fresh stem
        let tree ← match child with
          | some p => planTree env stem p.val
          | none => pure .wildcard
        return (name, tree)
      let n := match (head.type.subst env).toCore with | .enum n => n | _ => "$invalid"
      return .construct n structConstructor parts
  | .construct t c ps | .constructAs _ t c ps => do
      let parts ← ps.mapM fun p => do
        let name ← fresh stem
        return (name, ← planTree env stem p)
      let n := match (t.subst env).toCore with | .enum n => n | _ => "$invalid"
      return .construct n c parts
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals try have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals try have := List.sizeOf_lt_of_mem p.property
  all_goals omega

def plan (env : List (String × Ty)) (stem : String) (pat : Pattern α) (input : String) :
    StateM Nat (Plan α) := do return (← planTree env stem pat).toPlan input

def bindUsers (bindings : List (String × String)) (body : Aiur.Expr α) : Aiur.Expr α :=
  .letValue (.tuple (bindings.map fun binding => .bind binding.1))
    (.tuple (bindings.map fun binding => .var binding.2)) body

/-- Installing selected bindings cannot evaluate the continuation when an
unchecked alternative is missing a required binder. -/
def choiceBody (outputs bindings : List (String × String)) (positions : List Nat) (body : Aiur.Expr α) : Aiur.Expr α :=
  match choiceLinks outputs bindings positions with
  | some links => bindUsers links body
  | none => .matchValue (.tuple []) []

def matchSteps (steps : List (Step α)) (body : Aiur.Expr α)
    (failure : Option (Aiur.Expr α)) : Aiur.Expr α :=
  match steps with
  | [] => body
  | .test p input :: steps =>
      .matchValue (.var input) ((p, matchSteps steps body failure) ::
        failure.toList.map (fun e => (.wildcard, e)))
  | .load name input :: steps =>
      .letValue (.bind name) (.load (.var input)) (matchSteps steps body failure)
  | .choice outputs left lbs right rbs order :: steps =>
      let rest := matchSteps steps body failure
      matchSteps left (choiceBody outputs lbs (List.range outputs.length) rest)
        (some (matchSteps right (choiceBody outputs rbs order rest) failure))
termination_by sizeOf steps

def letSteps (steps : List (Step α)) (body : Aiur.Expr α) : Aiur.Expr α :=
  match steps with
  | [] => body
  | .test p input :: steps => .letValue p (.var input) (letSteps steps body)
  | .load name input :: steps => .letValue (.bind name) (.load (.var input)) (letSteps steps body)
  | .choice outputs left lbs right rbs order :: steps =>
      let rest := letSteps steps body
      matchSteps left (choiceBody outputs lbs (List.range outputs.length) rest)
        (some (matchSteps right (choiceBody outputs rbs order rest) none))

/-- Top-level `&p` is exactly `let p = *value`; ordinary patterns retain their
existing core representation. Only mixed nested patterns need fresh names. -/
def lowerLet (env : List (String × Ty)) : Pattern α → Aiur.Expr α → Aiur.Expr α → Aiur.Expr α
  | .load p, value, body => lowerLet env p (.load value) body
  | p, value, body =>
      match p.toCore? env with
      | some core => .letValue core value body
      | none =>
          let stem := freshPrefix (p.bindingNames ++ exprNames value ++ exprNames body)
          let root := stem ++ "0"
          let result := ((plan env stem p root).run 1).1
          .letValue (.bind root) value (letSteps result.steps (bindUsers result.bindings body))
termination_by p _ _ => sizeOf p

/-- A vacuous final test keeps the next arm syntactically visible even when
this arm's pattern cannot fail. It adds no semantic requirement. -/
def Plan.retainedSteps (p : Plan α) (root : String) : List (Step α) :=
  if p.steps.any (fun step => match step with
    | .test _ _ => true | .load _ _ | .choice _ _ _ _ _ _ => false) then p.steps
  else p.steps ++ [.test .wildcard root]

def matchArms (env : List (String × Ty)) (stem root : String) :
    List (Pattern α × Aiur.Expr α) → StateM Nat (Option (Aiur.Expr α))
  | [] => return none
  | (pat, body) :: arms => do
      let current ← plan env stem pat root
      let next ← matchArms env stem root arms
      -- Keep even unreachable alternatives syntactically visible to the
      -- specialization dependency check. The core compiler discards them.
      let steps := current.retainedSteps root
      return some (matchSteps steps (bindUsers current.bindings body) next)

def lowerMatch (env : List (String × Ty)) (value : Aiur.Expr α)
    (arms : List (Pattern α × Aiur.Expr α)) : Aiur.Expr α :=
  match arms.mapM (fun arm => return (← arm.1.toCore? env, arm.2)) with
  | some core => .matchValue value core
  | none =>
      let names := exprNames value ++ arms.flatMap (fun arm => arm.1.bindingNames ++ exprNames arm.2)
      let stem := freshPrefix names
      let root := stem ++ "0"
      let body := ((matchArms env stem root arms).run 1).1
      .letValue (.bind root) value (body.getD (.matchValue (.var root) []))

theorem bindUsers_ptrEqFree (bindings : List (String × String)) {body : Aiur.Expr α}
    (hb : body.ptrEqFree = true) : (bindUsers bindings body).ptrEqFree = true := by
  simp [bindUsers, Aiur.Expr.ptrEqFree, hb]

theorem choiceBody_ptrEqFree (outputs bindings : List (String × String)) (positions : List Nat)
    {body : Aiur.Expr α} (hb : body.ptrEqFree = true) :
    (choiceBody outputs bindings positions body).ptrEqFree = true := by
  unfold choiceBody
  cases choiceLinks outputs bindings positions with
  | none => simp [Aiur.Expr.ptrEqFree]
  | some links => exact bindUsers_ptrEqFree links hb

theorem matchSteps_ptrEqFree (steps : List (Step α)) {body : Aiur.Expr α}
    {failure : Option (Aiur.Expr α)} (hb : body.ptrEqFree = true)
    (hf : ∀ f, failure = some f → f.ptrEqFree = true) :
    (matchSteps steps body failure).ptrEqFree = true := by
  match steps with
  | [] => simpa [matchSteps] using hb
  | .test p input :: rest =>
      have hrest := matchSteps_ptrEqFree rest hb hf
      cases failure with
      | none => simp [matchSteps, Aiur.Expr.ptrEqFree, hrest]
      | some f => simp [matchSteps, Aiur.Expr.ptrEqFree, hrest, hf f rfl]
  | .load name input :: rest =>
      simp [matchSteps, Aiur.Expr.ptrEqFree, matchSteps_ptrEqFree rest hb hf]
  | .choice outputs left lbs right rbs order :: rest =>
      simp only [matchSteps]
      have hrest := matchSteps_ptrEqFree rest hb hf
      apply matchSteps_ptrEqFree left (choiceBody_ptrEqFree _ _ _ hrest)
      intro f heq
      cases heq
      exact matchSteps_ptrEqFree right (choiceBody_ptrEqFree _ _ _ hrest) hf
termination_by sizeOf steps

theorem letSteps_ptrEqFree (steps : List (Step α)) {body : Aiur.Expr α}
    (hb : body.ptrEqFree = true) : (letSteps steps body).ptrEqFree = true := by
  induction steps with
  | nil => exact hb
  | cons step rest ih =>
      cases step with
      | test p input => simp [letSteps, Aiur.Expr.ptrEqFree, ih]
      | load name input => simp [letSteps, Aiur.Expr.ptrEqFree, ih]
      | choice outputs left lbs right rbs order =>
          simp only [letSteps]
          apply matchSteps_ptrEqFree left (choiceBody_ptrEqFree _ _ _ ih)
          intro f heq
          cases heq
          exact matchSteps_ptrEqFree right (choiceBody_ptrEqFree _ _ _ ih) (by intro _ h; cases h)

theorem lowerLet_ptrEqFree (env : List (String × Ty)) (pat : Pattern α)
    {value body : Aiur.Expr α} (hv : value.ptrEqFree = true) (hb : body.ptrEqFree = true) :
    (lowerLet env pat value body).ptrEqFree = true := by
  match pat with
  | .load p =>
      simp only [lowerLet]
      exact lowerLet_ptrEqFree env p (by simpa [Aiur.Expr.ptrEqFree] using hv) hb
  | p =>
      unfold lowerLet
      split
      · exact lowerLet_ptrEqFree env _ (by simpa [Aiur.Expr.ptrEqFree] using hv) hb
      · split
        · simp [Aiur.Expr.ptrEqFree, hv, hb]
        · simp [Aiur.Expr.ptrEqFree, hv, letSteps_ptrEqFree _ (bindUsers_ptrEqFree _ hb)]
termination_by sizeOf pat

private theorem mapM_arms_ptrEqFree {arms : List (Pattern α × Aiur.Expr α)}
    {core : List (Aiur.Pattern α × Aiur.Expr α)}
    (hm : arms.mapM (fun arm => do return (← arm.1.toCore? env, arm.2)) = some core)
    (ha : ∀ arm ∈ arms, arm.2.ptrEqFree = true) :
    ∀ arm ∈ core, arm.2.ptrEqFree = true := by
  induction arms generalizing core with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at hm
      subst hm
      simp
  | cons arm rest ih =>
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hm
      obtain ⟨hd, ⟨cp, _, rfl⟩, tl, htl, rfl⟩ := hm
      intro a ha'
      rcases List.mem_cons.mp ha' with rfl | hmem
      · exact ha arm (by simp)
      · exact ih htl (fun x hx => ha x (by simp [hx])) a hmem

private theorem matchArms_ptrEqFree (env : List (String × Ty)) (stem root : String)
    (arms : List (Pattern α × Aiur.Expr α)) (st : Nat)
    (ha : ∀ arm ∈ arms, arm.2.ptrEqFree = true) :
    ∀ e, ((matchArms env stem root arms).run st).1 = some e → e.ptrEqFree = true := by
  induction arms generalizing st with
  | nil => intro e he; cases he
  | cons arm rest ih =>
      rcases arm with ⟨pat, body⟩
      intro e he
      simp only [matchArms, bind, StateT.bind, pure, StateT.pure, StateT.run] at he
      cases he
      apply matchSteps_ptrEqFree _ (bindUsers_ptrEqFree _ (ha (pat, body) (by simp)))
      intro f hf
      exact ih _ (fun a hm => ha a (by simp [hm])) f hf

theorem lowerMatch_ptrEqFree (env : List (String × Ty)) {value : Aiur.Expr α}
    {arms : List (Pattern α × Aiur.Expr α)} (hv : value.ptrEqFree = true)
    (ha : ∀ arm ∈ arms, arm.2.ptrEqFree = true) :
    (lowerMatch env value arms).ptrEqFree = true := by
  unfold lowerMatch
  split
  · rename_i core hm
    simp only [Aiur.Expr.ptrEqFree, hv, Bool.true_and, List.all_map, List.all_eq_true,
      Function.comp_def, id_eq]
    exact mapM_arms_ptrEqFree hm ha
  · simp only [Aiur.Expr.ptrEqFree, hv, Bool.true_and]
    cases hb : ((matchArms env _ _ arms).run 1).1 with
    | none => simp [Aiur.Expr.ptrEqFree]
    | some e => exact matchArms_ptrEqFree env _ _ arms 1 ha e hb

end PatternLowering
end Aiur.Generic
