import Ix.Kernel.DefinitionDependencies
import Ix.Kernel.Verify.Check.ValidatorSoundness

/-!
Completeness of the production address-memoized reference collector.
An address is marked before its children are visited, so the invariant keeps
the local references and the pending child frontier separate. Finite syntax
collision freedom justifies each memo hit. No trusted parser or alternate
reference validator is used.
-/

namespace Ix.Kernel.DefinitionReferences

def Children : KExpr .anon → List (KExpr .anon)
  | .app fn arg _ => [fn, arg]
  | .lam _ _ domain body _ | .all _ _ domain body _ => [domain, body]
  | .letE _ domain value body _ _ => [domain, value, body]
  | .prj _ _ major _ => [major]
  | _ => []

def Heads : KExpr .anon → Array (KId .anon)
  | .const id .. | .prj id .. => #[id]
  | _ => #[]

/-- Literal constant and projection-head references anywhere in the syntax. -/
inductive Reference (id : KId .anon) : KExpr .anon → Prop where
  | head {expr : KExpr .anon} (member : id ∈ Heads expr) : Reference id expr
  | child {expr child : KExpr .anon}
      (member : child ∈ Children expr) (nested : Reference id child) : Reference id expr

def DomainClosed (domain : KExpr .anon → Prop) : Prop :=
  ∀ expr, domain expr → ∀ child ∈ Children expr, domain child

def StackInDomain (domain : KExpr .anon → Prop) (stack : List (KExpr .anon)) : Prop :=
  ∀ expr ∈ stack, domain expr

def SeenLocal (domain : KExpr .anon → Prop) (seen : Std.HashSet Address)
    (refs : Array (KId .anon)) : Prop :=
  ∀ expr, domain expr → seen.contains expr.addr = true → ∀ id ∈ Heads expr, id ∈ refs

def SeenFrontier (domain : KExpr .anon → Prop) (seen : Std.HashSet Address)
    (stack : List (KExpr .anon)) : Prop :=
  ∀ expr, domain expr → seen.contains expr.addr = true → ∀ child ∈ Children expr,
    seen.contains child.addr = true ∨ child ∈ stack

private theorem go_step (expr : KExpr .anon) (stack : List (KExpr .anon))
    (seen : Std.HashSet Address) (refs : Array (KId .anon)) :
    definitionRefs.go (expr :: stack) seen refs =
      if seen.contains expr.addr then definitionRefs.go stack seen refs
      else definitionRefs.go (Children expr ++ stack) (seen.insert expr.addr) (refs ++ Heads expr) := by
  rw [definitionRefs.go]
  split
  · rfl
  · cases expr <;> simp [Children, Heads]

theorem Children.reachable {expr child : KExpr .anon} (member : child ∈ Children expr) :
    expr.ValidationReach child := by
  cases expr <;> simp only [Children, List.mem_cons, List.not_mem_nil,
    or_false] at member
  all_goals first
    | contradiction
    | rcases member with rfl | rfl | rfl
      · exact .letType (.refl _)
      · exact .letValue (.refl _)
      · exact .letBody (.refl _)
    | rcases member with rfl | rfl
      all_goals first
        | exact .appFn (.refl _)
        | exact .appArg (.refl _)
        | exact .lamType (.refl _)
        | exact .lamBody (.refl _)
        | exact .allType (.refl _)
        | exact .allBody (.refl _)
    | cases member; exact .projectionValue (.refl _)

theorem SeenFrontier.drop {domain : KExpr .anon → Prop} {expr : KExpr .anon}
    {seen : Std.HashSet Address} {stack : List (KExpr .anon)}
    (frontier : SeenFrontier domain seen (expr :: stack))
    (present : seen.contains expr.addr = true) : SeenFrontier domain seen stack := by
  intro parent parentDomain parentSeen child childMember
  rcases frontier parent parentDomain parentSeen child childMember with h | h
  · exact .inl h
  · rcases List.mem_cons.mp h with rfl | h
    · exact .inl present
    · exact .inr h

theorem SeenLocal.expand {domain : KExpr .anon → Prop} {expr : KExpr .anon}
    {seen : Std.HashSet Address} {refs : Array (KId .anon)}
    (faithful : ∀ left right, domain left → domain right → left.addr = right.addr → left = right)
    (locals : SeenLocal domain seen refs) (exprDomain : domain expr) :
    SeenLocal domain (seen.insert expr.addr) (refs ++ Heads expr) := by
  intro candidate candidateDomain candidateSeen id idMember
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at candidateSeen
  apply Array.mem_append.mpr
  rcases candidateSeen with h | h
  · have equality := faithful expr candidate exprDomain candidateDomain (eq_of_beq h)
    subst candidate
    exact .inr idMember
  · exact .inl (locals candidate candidateDomain h id idMember)

theorem SeenFrontier.expand {domain : KExpr .anon → Prop} {expr : KExpr .anon}
    {seen : Std.HashSet Address} {stack : List (KExpr .anon)}
    (faithful : ∀ left right, domain left → domain right → left.addr = right.addr → left = right)
    (frontier : SeenFrontier domain seen (expr :: stack)) (exprDomain : domain expr) :
    SeenFrontier domain (seen.insert expr.addr) (Children expr ++ stack) := by
  intro candidate candidateDomain candidateSeen child childMember
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at candidateSeen
  rcases candidateSeen with h | h
  · have equality := faithful expr candidate exprDomain candidateDomain (eq_of_beq h)
    subst candidate
    exact .inr (List.mem_append_left _ childMember)
  · rcases frontier candidate candidateDomain h child childMember with childSeen | childPending
    · exact .inl (AddressSetLE.insert seen expr.addr _ childSeen)
    · rcases List.mem_cons.mp childPending with equality | childPending
      · subst child
        exact .inl (AddressSetLE.insert_self seen expr.addr)
      · exact .inr (List.mem_append_right _ childPending)

structure Post (domain : KExpr .anon → Prop) (stack : List (KExpr .anon))
    (seen : Std.HashSet Address) (refs result : Array (KId .anon)) where
  finalSeen : Std.HashSet Address
  locals : SeenLocal domain finalSeen result
  frontier : SeenFrontier domain finalSeen []
  seenMonotone : AddressSetLE seen finalSeen
  refsMonotone : ∀ id ∈ refs, id ∈ result
  covered : ∀ expr ∈ stack, finalSeen.contains expr.addr = true

theorem go_complete {domain : KExpr .anon → Prop}
    (closed : DomainClosed domain)
    (faithful : ∀ left right, domain left → domain right → left.addr = right.addr → left = right) :
    ∀ (stack : List (KExpr .anon)) (seen : Std.HashSet Address) (refs : Array (KId .anon)),
      StackInDomain domain stack → SeenLocal domain seen refs → SeenFrontier domain seen stack →
      Nonempty (Post domain stack seen refs (definitionRefs.go stack seen refs))
  | [], seen, refs, _, locals, frontier => by
      rw [definitionRefs.go]
      exact ⟨⟨seen, locals, frontier, .refl seen, fun _ h => h, by simp⟩⟩
  | expr :: stack, seen, refs, inDomain, locals, frontier => by
      have exprDomain := inDomain expr (.head _)
      rw [go_step]
      split
      · rename_i present
        obtain ⟨post⟩ := go_complete closed faithful stack seen refs
          (fun child member => inDomain child (.tail _ member)) locals (frontier.drop present)
        refine ⟨⟨post.finalSeen, post.locals, post.frontier, post.seenMonotone,
          post.refsMonotone, ?_⟩⟩
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact post.seenMonotone _ present
        · exact post.covered child member
      · obtain ⟨post⟩ := go_complete closed faithful (Children expr ++ stack)
          (seen.insert expr.addr) (refs ++ Heads expr)
          (by
            intro child member
            rcases List.mem_append.mp member with member | member
            · exact closed expr exprDomain child member
            · exact inDomain child (.tail _ member))
          (locals.expand faithful exprDomain) (frontier.expand faithful exprDomain)
        refine ⟨⟨post.finalSeen, post.locals, post.frontier,
          (AddressSetLE.insert seen expr.addr).trans post.seenMonotone, ?_, ?_⟩⟩
        · intro id member
          exact post.refsMonotone id (Array.mem_append.mpr (.inl member))
        · intro child member
          rcases List.mem_cons.mp member with equality | member
          · subst child
            exact post.seenMonotone _ (AddressSetLE.insert_self seen expr.addr)
          · exact post.covered child (List.mem_append_right _ member)
termination_by stack _ _ _ _ _ => exprWorkSize stack
decreasing_by
  all_goals simp_wf
  all_goals first
    | simp [exprWorkSize, KExpr.treeSize_pos]; omega
    | cases expr <;> simp [Children, exprWorkSize, KExpr.treeSize] <;> omega

theorem Reference.collected {domain : KExpr .anon → Prop}
    {seen : Std.HashSet Address} {refs : Array (KId .anon)}
    (closed : DomainClosed domain) (locals : SeenLocal domain seen refs)
    (frontier : SeenFrontier domain seen []) {expr : KExpr .anon} {id : KId .anon}
    (reference : Reference id expr) (exprDomain : domain expr)
    (present : seen.contains expr.addr = true) : id ∈ refs := by
  induction reference with
  | head member => exact locals _ exprDomain present id member
  | @child parent child member nested ih =>
      have childDomain := closed parent exprDomain child member
      have childSeen : seen.contains child.addr = true := by
        rcases frontier parent exprDomain present child member with h | h
        · exact h
        · contradiction
      exact ih childDomain childSeen

/-- Every literal reference beneath an input root occurs in the production
collector's result. Collision freedom is restricted to the supplied finite
run support; it is not a global hash-injectivity premise. -/
theorem definitionRefs_complete {roots : List (KExpr .anon)} {support : RunSupport}
    (coverage : ∀ root ∈ roots, root.ValidationCoverage support)
    (collision : support.CollisionFree) {root : KExpr .anon} (member : root ∈ roots)
    {id : KId .anon} (reference : Reference id root) : id ∈ definitionRefs roots := by
  let domain := fun candidate => ∃ root ∈ roots, root.ValidationReach candidate
  have closed : DomainClosed domain := by
    rintro parent ⟨root, member, reachable⟩ child childMember
    exact ⟨root, member, reachable.trans (Children.reachable childMember)⟩
  have faithful : ∀ left right, domain left → domain right → left.addr = right.addr → left = right := by
    rintro left right ⟨leftRoot, leftMember, leftReach⟩ ⟨rightRoot, rightMember, rightReach⟩ equality
    have erased := collision.expr ((coverage leftRoot leftMember).expr leftReach)
      ((coverage rightRoot rightMember).expr rightReach) equality
    simpa only [KExpr.eraseMeta_anon] using erased
  obtain ⟨post⟩ := go_complete closed faithful roots {} #[]
    (fun root member => ⟨root, member, .refl root⟩)
    (by intro expr _ present; simp at present)
    (by intro expr _ present; simp at present)
  exact reference.collected closed post.locals post.frontier
    ⟨root, member, .refl root⟩ (post.covered root member)

end Ix.Kernel.DefinitionReferences
