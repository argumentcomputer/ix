import Ix.Tc.Verify.Check.ValidationReach

/-!
# Soundness of the address-memoized scoping validators

The validator inserts a node into its seen set before visiting the node's
children.  Consequently, “every seen node is already fully scoped” is not a
valid loop invariant.  The invariant used here separates:

* the local guard already checked for every seen node; and
* a frontier condition saying that each direct child is either seen or still
  present on the worklist.

When the worklist becomes empty, the frontier is transitively closed and the
local guards imply full structural scoping.  Address equality is converted
to syntax equality only through finite-run collision freedom.
-/

namespace Ix.Tc

open Std (HashSet)

/-- Inclusion expressed using the exact Boolean membership operation used by
the production hash sets. -/
def AddressSetLE {α : Type} [BEq α] [Hashable α]
    (before after : HashSet α) : Prop :=
  ∀ key, before.contains key = true → after.contains key = true

namespace AddressSetLE

variable {α : Type} [BEq α] [Hashable α] [EquivBEq α]
  [LawfulHashable α] [ReflBEq α]

omit [EquivBEq α] [LawfulHashable α] [ReflBEq α] in
theorem refl (set : HashSet α) : AddressSetLE set set :=
  fun _ h => h

omit [EquivBEq α] [LawfulHashable α] [ReflBEq α] in
theorem trans {a b c : HashSet α}
    (hab : AddressSetLE a b) (hbc : AddressSetLE b c) :
    AddressSetLE a c :=
  fun key h => hbc key (hab key h)

omit [ReflBEq α] in
theorem insert (set : HashSet α) (key : α) :
    AddressSetLE set (set.insert key) := by
  intro candidate hcandidate
  rw [Std.HashSet.contains_insert, Bool.or_eq_true]
  exact .inr hcandidate

theorem insert_self (set : HashSet α) (key : α) :
    (set.insert key).contains key = true := by
  rw [Std.HashSet.contains_insert, Bool.or_eq_true]
  exact .inl (beq_self_eq_true key)

end AddressSetLE

/-! ## Universe-worklist invariant -/

def UnivStackInDomain (domain : KUniv .anon → Prop)
    (stack : List (KUniv .anon)) : Prop :=
  ∀ ⦃level⦄, level ∈ stack → domain level

def UnivSeenLocal (domain : KUniv .anon → Prop) (bound : Nat)
    (seen : HashSet Address) : Prop :=
  ∀ ⦃level⦄, domain level → seen.contains level.addr = true →
    level.ValidationLocal bound

def UnivSeenFrontier (domain : KUniv .anon → Prop)
    (stack : List (KUniv .anon)) (seen : HashSet Address) : Prop :=
  ∀ ⦃parent⦄, domain parent → seen.contains parent.addr = true →
    ∀ ⦃child⦄, child ∈ parent.validationChildren →
      seen.contains child.addr = true ∨ child ∈ stack

def UnivStackCovered (stack : List (KUniv .anon))
    (seen : HashSet Address) : Prop :=
  ∀ ⦃level⦄, level ∈ stack → seen.contains level.addr = true

/-- Ghost result of a successful universe worklist run. -/
structure UnivValidationPost (domain : KUniv .anon → Prop) (bound : Nat)
    (initialStack : List (KUniv .anon)) (initialSeen finalSeen :
      HashSet Address) : Prop where
  locals : UnivSeenLocal domain bound finalSeen
  frontier : UnivSeenFrontier domain [] finalSeen
  monotone : AddressSetLE initialSeen finalSeen
  covered : UnivStackCovered initialStack finalSeen

namespace UnivValidationPost

/-- Reattach a memo-hit head to the recursive tail result. -/
theorem ofHit
    {domain : KUniv .anon → Prop} {bound : Nat}
    {level : KUniv .anon} {stack : List (KUniv .anon)}
    {seen finalSeen : HashSet Address}
    (hhit : seen.contains level.addr = true)
    (hpost : UnivValidationPost domain bound stack seen finalSeen) :
    UnivValidationPost domain bound (level :: stack) seen finalSeen where
  locals := hpost.locals
  frontier := hpost.frontier
  monotone := hpost.monotone
  covered := by
    intro candidate hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hpost.monotone _ hhit
    · exact hpost.covered hmem

/-- Reattach a freshly inserted head to a recursive result over its expanded
children and the old tail. -/
theorem ofExpanded
    {domain : KUniv .anon → Prop} {bound : Nat}
    {level : KUniv .anon} {stack expanded : List (KUniv .anon)}
    {seen finalSeen : HashSet Address}
    (hexpanded : expanded = level.validationChildren ++ stack)
    (hpost : UnivValidationPost domain bound expanded
      (seen.insert level.addr) finalSeen) :
    UnivValidationPost domain bound (level :: stack) seen finalSeen where
  locals := hpost.locals
  frontier := hpost.frontier
  monotone := (AddressSetLE.insert seen level.addr).trans hpost.monotone
  covered := by
    intro candidate hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hpost.monotone _
        (AddressSetLE.insert_self seen candidate.addr)
    · apply hpost.covered
      rw [hexpanded]
      exact List.mem_append.mpr (.inr hmem)

end UnivValidationPost

namespace UnivSeenLocal

/-- Insert a locally valid node.  Collision freedom is what makes the local
fact valid for every supported syntax node that shares the new address. -/
theorem insert
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    (hcollision : support.CollisionFree)
    {bound : Nat} {seen : HashSet Address} {level : KUniv .anon}
    (hbefore : UnivSeenLocal domain bound seen)
    (hlevel : domain level) (hlocal : level.ValidationLocal bound) :
    UnivSeenLocal domain bound (seen.insert level.addr) := by
  intro candidate hcandidate hmem
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hmem
  rcases hmem with hsame | hold
  · have herase := hcollision.univ.addrFaithful
      (hdomain.covered hlevel) (hdomain.covered hcandidate) hsame
    have heq : level = candidate := by
      simpa only [KUniv.eraseMeta_anon] using herase
    subst candidate
    exact hlocal
  · exact hbefore hcandidate hold

end UnivSeenLocal

namespace UnivSeenFrontier

/-- Adding pending work can only weaken the frontier obligation. -/
theorem weakenStack
    {domain : KUniv .anon → Prop} {small large : List (KUniv .anon)}
    {seen : HashSet Address}
    (hfrontier : UnivSeenFrontier domain small seen)
    (hsub : ∀ ⦃level⦄, level ∈ small → level ∈ large) :
    UnivSeenFrontier domain large seen := by
  intro parent hparent hseen child hchild
  rcases hfrontier hparent hseen hchild with hcovered | hpending
  · exact .inl hcovered
  · exact .inr (hsub hpending)

/-- Dropping a memo hit from the stack preserves the frontier: a reference
to the dropped node is discharged by its existing seen membership. -/
theorem dropHit
    {domain : KUniv .anon → Prop} {level : KUniv .anon}
    {stack : List (KUniv .anon)} {seen : HashSet Address}
    (hfrontier : UnivSeenFrontier domain (level :: stack) seen)
    (hhit : seen.contains level.addr = true) :
    UnivSeenFrontier domain stack seen := by
  intro parent hparent hseen child hchild
  rcases hfrontier hparent hseen hchild with hcovered | hpending
  · exact .inl hcovered
  · rcases List.mem_cons.mp hpending with rfl | hpending
    · exact .inl hhit
    · exact .inr hpending

/-- Inserting a fresh node and replacing it by its direct children preserves
the frontier. -/
theorem insertAndExpand
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    (hcollision : support.CollisionFree)
    {level : KUniv .anon} {stack : List (KUniv .anon)}
    {seen : HashSet Address}
    (hfrontier : UnivSeenFrontier domain (level :: stack) seen)
    (hlevel : domain level) :
    UnivSeenFrontier domain
      (level.validationChildren ++ stack) (seen.insert level.addr) := by
  intro parent hparent hseen child hchild
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hseen
  rcases hseen with hsame | hold
  · have herase := hcollision.univ.addrFaithful
      (hdomain.covered hlevel) (hdomain.covered hparent) hsame
    have heq : level = parent := by
      simpa only [KUniv.eraseMeta_anon] using herase
    subst parent
    exact .inr (List.mem_append.mpr (.inl hchild))
  · rcases hfrontier hparent hold hchild with hcovered | hpending
    · exact .inl (AddressSetLE.insert seen level.addr child.addr hcovered)
    · rcases List.mem_cons.mp hpending with heq | hpending
      · subst child
        exact .inl (AddressSetLE.insert_self seen level.addr)
      · exact .inr (List.mem_append.mpr (.inr hpending))

/-- At an empty frontier, local validity recursively implies full scoping. -/
theorem fullyScoped
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    {bound : Nat} {seen : HashSet Address} {root : KUniv .anon}
    (hlocal : UnivSeenLocal domain bound seen)
    (hfrontier : UnivSeenFrontier domain [] seen)
    (hroot : domain root) (hseen : seen.contains root.addr = true) :
    root.Scoped bound := by
  cases root with
  | zero => trivial
  | succ child addr =>
      have hchildDomain : domain child :=
        hdomain.child hroot (by simp [KUniv.validationChildren])
      have hchildSeen : seen.contains child.addr = true := by
        rcases hfrontier hroot hseen
            (by simp [KUniv.validationChildren] :
              child ∈ (KUniv.succ child addr).validationChildren) with
          h | h
        · exact h
        · simp at h
      exact fullyScoped (root := child) hdomain hlocal hfrontier
        hchildDomain hchildSeen
  | max left right addr =>
      have hleftDomain : domain left :=
        hdomain.child hroot (by simp [KUniv.validationChildren])
      have hrightDomain : domain right :=
        hdomain.child hroot (by simp [KUniv.validationChildren])
      have hleftSeen : seen.contains left.addr = true := by
        rcases hfrontier hroot hseen
            (by simp [KUniv.validationChildren] :
              left ∈ (KUniv.max left right addr).validationChildren) with
          h | h
        · exact h
        · simp at h
      have hrightSeen : seen.contains right.addr = true := by
        rcases hfrontier hroot hseen
            (by simp [KUniv.validationChildren] :
              right ∈ (KUniv.max left right addr).validationChildren) with
          h | h
        · exact h
        · simp at h
      exact ⟨fullyScoped (root := left) hdomain hlocal hfrontier
          hleftDomain hleftSeen,
        fullyScoped (root := right) hdomain hlocal hfrontier
          hrightDomain hrightSeen⟩
  | imax left right addr =>
      have hleftDomain : domain left :=
        hdomain.child hroot (by simp [KUniv.validationChildren])
      have hrightDomain : domain right :=
        hdomain.child hroot (by simp [KUniv.validationChildren])
      have hleftSeen : seen.contains left.addr = true := by
        rcases hfrontier hroot hseen
            (by simp [KUniv.validationChildren] :
              left ∈ (KUniv.imax left right addr).validationChildren) with
          h | h
        · exact h
        · simp at h
      have hrightSeen : seen.contains right.addr = true := by
        rcases hfrontier hroot hseen
            (by simp [KUniv.validationChildren] :
              right ∈ (KUniv.imax left right addr).validationChildren) with
          h | h
        · exact h
        · simp at h
      exact ⟨fullyScoped (root := left) hdomain hlocal hfrontier
          hleftDomain hleftSeen,
        fullyScoped (root := right) hdomain hlocal hfrontier
          hrightDomain hrightSeen⟩
  | param idx name addr => exact hlocal hroot hseen
termination_by root.size
decreasing_by
  all_goals simp_all [KUniv.size] <;> omega

end UnivSeenFrontier

/-! ## Production universe validator -/

namespace RecM

/-- Successful execution of the exact memoized universe worklist establishes
the local/frontier certificate.  The theorem is generic over a child-closed
finite domain so one expression validation can share its universe seen set
across every sort and constant argument it encounters. -/
theorem validateUnivParamsSeen_go_sound :
    ∀ {support : RunSupport} {domain : KUniv .anon → Prop},
      KUniv.ValidationDomain support domain →
      support.CollisionFree →
      ∀ (bound : Nat) (stack : List (KUniv .anon))
        (seen : HashSet Address),
      UnivStackInDomain domain stack →
      UnivSeenLocal domain bound seen →
      UnivSeenFrontier domain stack seen →
      ∀ (methods : Methods .anon) (state : TcState .anon)
        (finalSeen : HashSet Address) (after : TcState .anon),
      (RecM.validateUnivParamsSeen.go bound stack seen).run methods state =
        .ok finalSeen after →
      UnivValidationPost domain bound stack seen finalSeen
  | support, domain, hdomain, hcollision, bound, [], seen,
      hstack, hlocal, hfrontier, methods, state, finalSeen, after, hrun => by
      rw [RecM.validateUnivParamsSeen.go] at hrun
      cases hrun
      exact ⟨hlocal, hfrontier, AddressSetLE.refl seen,
        fun _ h => by simp at h⟩
  | support, domain, hdomain, hcollision, bound, level :: stack, seen,
      hstack, hlocal, hfrontier, methods, state, finalSeen, after, hrun => by
      rw [RecM.validateUnivParamsSeen.go] at hrun
      split at hrun
      · rename_i hhit
        simp only [bind_pure] at hrun
        have htailDomain : UnivStackInDomain domain stack := by
          intro candidate hmem
          exact hstack (List.mem_cons.mpr (.inr hmem))
        have htailFrontier := hfrontier.dropHit hhit
        exact UnivValidationPost.ofHit hhit <|
          validateUnivParamsSeen_go_sound hdomain hcollision bound stack seen
            htailDomain hlocal htailFrontier methods state finalSeen after hrun
      · rename_i hmiss
        have hlevelDomain : domain level :=
          hstack (List.mem_cons.mpr (.inl rfl))
        have hchildrenDomain :
            UnivStackInDomain domain
              (level.validationChildren ++ stack) := by
          intro candidate hmem
          rcases List.mem_append.mp hmem with hchild | htail
          · exact hdomain.child hlevelDomain hchild
          · exact hstack (List.mem_cons.mpr (.inr htail))
        have hexpandedFrontier :=
          hfrontier.insertAndExpand hdomain hcollision hlevelDomain
        cases level with
        | zero addr =>
            simp only [pure_bind] at hrun
            have hlocal' := hlocal.insert hdomain hcollision hlevelDomain
              (by trivial)
            exact UnivValidationPost.ofExpanded rfl <|
              validateUnivParamsSeen_go_sound hdomain hcollision bound stack
                (seen.insert addr) (by simpa [KUniv.validationChildren] using
                  hchildrenDomain) hlocal'
                (by simpa [KUniv.validationChildren] using hexpandedFrontier)
                methods state finalSeen after hrun
        | succ child addr =>
            simp only [pure_bind] at hrun
            have hlocal' := hlocal.insert hdomain hcollision hlevelDomain
              (by trivial)
            exact UnivValidationPost.ofExpanded rfl <|
              validateUnivParamsSeen_go_sound hdomain hcollision bound
                (child :: stack) (seen.insert addr)
                (by simpa [KUniv.validationChildren] using hchildrenDomain)
                hlocal'
                (by simpa [KUniv.validationChildren] using hexpandedFrontier)
                methods state finalSeen after hrun
        | max left right addr =>
            simp only [pure_bind] at hrun
            have hlocal' := hlocal.insert hdomain hcollision hlevelDomain
              (by trivial)
            exact UnivValidationPost.ofExpanded rfl <|
              validateUnivParamsSeen_go_sound hdomain hcollision bound
                (right :: left :: stack) (seen.insert addr)
                (by simpa [KUniv.validationChildren] using hchildrenDomain)
                hlocal'
                (by simpa [KUniv.validationChildren] using hexpandedFrontier)
                methods state finalSeen after hrun
        | imax left right addr =>
            simp only [pure_bind] at hrun
            have hlocal' := hlocal.insert hdomain hcollision hlevelDomain
              (by trivial)
            exact UnivValidationPost.ofExpanded rfl <|
              validateUnivParamsSeen_go_sound hdomain hcollision bound
                (right :: left :: stack) (seen.insert addr)
                (by simpa [KUniv.validationChildren] using hchildrenDomain)
                hlocal'
                (by simpa [KUniv.validationChildren] using hexpandedFrontier)
                methods state finalSeen after hrun
        | param idx name addr =>
            simp only [pure_bind] at hrun
            split at hrun
            · contradiction
            · rename_i hinRange
              have hidx : idx.toNat < bound := by omega
              have hlocal' := hlocal.insert hdomain hcollision hlevelDomain
                hidx
              exact UnivValidationPost.ofExpanded rfl <|
                validateUnivParamsSeen_go_sound hdomain hcollision bound stack
                  (seen.insert addr)
                  (by simpa [KUniv.validationChildren] using hchildrenDomain)
                  hlocal'
                  (by simpa [KUniv.validationChildren] using hexpandedFrontier)
                  methods state finalSeen after hrun
termination_by _ _ _ _ _ stack _ _ _ _ _ _ _ _ _ =>
  RecM.univWorkSize stack
decreasing_by
  all_goals simp_all [RecM.univWorkSize, KUniv.validationChildren, KUniv.size]
  all_goals try omega
  all_goals exact KUniv.size_pos _

/-- Public universe-validator soundness from an already closed memo set.
The returned memo set remains locally valid and closed, and the requested
root is fully scoped. -/
theorem validateUnivParamsSeen_sound
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    (hcollision : support.CollisionFree)
    {bound : Nat} {root : KUniv .anon} {seen finalSeen : HashSet Address}
    {methods : Methods .anon} {state after : TcState .anon}
    (hroot : domain root)
    (hlocal : UnivSeenLocal domain bound seen)
    (hfrontier : UnivSeenFrontier domain [] seen)
    (hrun : (validateUnivParamsSeen root bound seen).run methods state =
      .ok finalSeen after) :
    UnivValidationPost domain bound [root] seen finalSeen ∧
      root.Scoped bound := by
  rw [RecM.validateUnivParamsSeen_equation] at hrun
  have hpost := validateUnivParamsSeen_go_sound hdomain hcollision bound
    [root] seen (by simpa [UnivStackInDomain]) hlocal
    (hfrontier.weakenStack (by simp)) methods state finalSeen after hrun
  exact ⟨hpost,
    hpost.frontier.fullyScoped hdomain hpost.locals hroot
      (hpost.covered (by simp))⟩

end RecM

/-! ## Expression-worklist invariant -/

def ExprStackInReach (root : KExpr .anon)
    (stack : List (KExpr .anon × UInt64)) : Prop :=
  ∀ ⦃item⦄, item ∈ stack → root.ValidationReach item.1

def ExprSeenLocal (root : KExpr .anon)
    (seen : HashSet (Address × UInt64)) : Prop :=
  ∀ ⦃expr : KExpr .anon⦄ ⦃depth : UInt64⦄,
    root.ValidationReach expr →
    seen.contains (expr.addr, depth) = true →
    expr.ValidationLocal depth

def ExprSeenFrontier (root : KExpr .anon)
    (stack : List (KExpr .anon × UInt64))
    (seen : HashSet (Address × UInt64)) : Prop :=
  ∀ ⦃expr : KExpr .anon⦄ ⦃depth : UInt64⦄,
    root.ValidationReach expr →
    seen.contains (expr.addr, depth) = true →
    ∀ ⦃child : KExpr .anon × UInt64⦄,
      child ∈ expr.validationChildrenAt depth →
      seen.contains (child.1.addr, child.2) = true ∨ child ∈ stack

/-- Every universe root attached to a seen expression node has completed its
universe validation. -/
def ExprSeenUnivs (root : KExpr .anon)
    (seenExprs : HashSet (Address × UInt64))
    (seenUnivs : HashSet Address) : Prop :=
  ∀ ⦃expr : KExpr .anon⦄ ⦃depth : UInt64⦄,
    root.ValidationReach expr →
    seenExprs.contains (expr.addr, depth) = true →
    ∀ ⦃level : KUniv .anon⦄, level ∈ expr.validationUnivRoots →
      seenUnivs.contains level.addr = true

def ExprStackCovered (stack : List (KExpr .anon × UInt64))
    (seen : HashSet (Address × UInt64)) : Prop :=
  ∀ ⦃item⦄, item ∈ stack →
    seen.contains (item.1.addr, item.2) = true

/-- Ghost result of a successful expression worklist run.  The production
validator returns only `Unit`; the two final memo sets are existential ghost
state retained by the soundness proof. -/
structure ExprValidationPost (root : KExpr .anon) (bound : Nat)
    (initialStack : List (KExpr .anon × UInt64))
    (initialExprs finalExprs : HashSet (Address × UInt64))
    (initialUnivs finalUnivs : HashSet Address) : Prop where
  exprLocals : ExprSeenLocal root finalExprs
  exprFrontier : ExprSeenFrontier root [] finalExprs
  exprUnivs : ExprSeenUnivs root finalExprs finalUnivs
  univLocals : UnivSeenLocal (KExpr.ValidationUnivReach root)
    bound finalUnivs
  univFrontier : UnivSeenFrontier (KExpr.ValidationUnivReach root)
    [] finalUnivs
  exprMonotone : AddressSetLE initialExprs finalExprs
  univMonotone : AddressSetLE initialUnivs finalUnivs
  covered : ExprStackCovered initialStack finalExprs


namespace ExprSeenLocal

theorem insert
    {support : RunSupport} {root expr : KExpr .anon} {depth : UInt64}
    (hcoverage : root.ValidationCoverage support)
    (hcollision : support.CollisionFree)
    {seen : HashSet (Address × UInt64)}
    (hbefore : ExprSeenLocal root seen)
    (hexpr : root.ValidationReach expr)
    (hlocal : expr.ValidationLocal depth) :
    ExprSeenLocal root (seen.insert (expr.addr, depth)) := by
  intro candidate candidateDepth hcandidate hmem
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hmem
  rcases hmem with hsame | hold
  · have hkey : (expr.addr, depth) = (candidate.addr, candidateDepth) :=
      eq_of_beq hsame
    have haddr : expr.addr = candidate.addr := congrArg Prod.fst hkey
    have hdepth : depth = candidateDepth := congrArg Prod.snd hkey
    have herase := hcollision.expr
      (hcoverage.expr hexpr) (hcoverage.expr hcandidate) haddr
    have heq : expr = candidate := by
      simpa only [KExpr.eraseMeta_anon] using herase
    subst candidate
    subst candidateDepth
    exact hlocal
  · exact hbefore hcandidate hold

end ExprSeenLocal

namespace ExprSeenFrontier

theorem weakenStack
    {root : KExpr .anon} {small large : List (KExpr .anon × UInt64)}
    {seen : HashSet (Address × UInt64)}
    (hfrontier : ExprSeenFrontier root small seen)
    (hsub : ∀ ⦃item⦄, item ∈ small → item ∈ large) :
    ExprSeenFrontier root large seen := by
  intro expr depth hexpr hseen child hchild
  rcases hfrontier hexpr hseen hchild with hcovered | hpending
  · exact .inl hcovered
  · exact .inr (hsub hpending)

theorem dropHit
    {root expr : KExpr .anon} {depth : UInt64}
    {stack : List (KExpr .anon × UInt64)}
    {seen : HashSet (Address × UInt64)}
    (hfrontier : ExprSeenFrontier root ((expr, depth) :: stack) seen)
    (hhit : seen.contains (expr.addr, depth) = true) :
    ExprSeenFrontier root stack seen := by
  intro parent parentDepth hparent hseen child hchild
  rcases hfrontier hparent hseen hchild with hcovered | hpending
  · exact .inl hcovered
  · rcases List.mem_cons.mp hpending with heq | hpending
    · cases heq
      exact .inl hhit
    · exact .inr hpending

theorem insertAndExpand
    {support : RunSupport} {root expr : KExpr .anon} {depth : UInt64}
    (hcoverage : root.ValidationCoverage support)
    (hcollision : support.CollisionFree)
    {stack : List (KExpr .anon × UInt64)}
    {seen : HashSet (Address × UInt64)}
    (hfrontier : ExprSeenFrontier root ((expr, depth) :: stack) seen)
    (hexpr : root.ValidationReach expr) :
    ExprSeenFrontier root
      (expr.validationChildrenAt depth ++ stack)
      (seen.insert (expr.addr, depth)) := by
  intro parent parentDepth hparent hseen child hchild
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hseen
  rcases hseen with hsame | hold
  · have hkey : (expr.addr, depth) = (parent.addr, parentDepth) :=
      eq_of_beq hsame
    have haddr : expr.addr = parent.addr := congrArg Prod.fst hkey
    have hdepth : depth = parentDepth := congrArg Prod.snd hkey
    have herase := hcollision.expr
      (hcoverage.expr hexpr) (hcoverage.expr hparent) haddr
    have heq : expr = parent := by
      simpa only [KExpr.eraseMeta_anon] using herase
    subst parent
    subst parentDepth
    exact .inr (List.mem_append.mpr (.inl hchild))
  · rcases hfrontier hparent hold hchild with hcovered | hpending
    · exact .inl
        (AddressSetLE.insert seen (expr.addr, depth)
          (child.1.addr, child.2) hcovered)
    · rcases List.mem_cons.mp hpending with heq | hpending
      · cases heq
        exact .inl (AddressSetLE.insert_self seen (expr.addr, depth))
      · exact .inr (List.mem_append.mpr (.inr hpending))

/-- At empty expression and universe frontiers, the local certificates imply
the full recursive `KExpr.Scoped` predicate. -/
theorem fullyScoped
    {support : RunSupport} {root : KExpr .anon}
    (hcoverage : root.ValidationCoverage support)
    {bound : Nat}
    {seenExprs : HashSet (Address × UInt64)}
    {seenUnivs : HashSet Address}
    (hexprLocal : ExprSeenLocal root seenExprs)
    (hexprFrontier : ExprSeenFrontier root [] seenExprs)
    (hexprUnivs : ExprSeenUnivs root seenExprs seenUnivs)
    (hunivLocal : UnivSeenLocal (KExpr.ValidationUnivReach root)
      bound seenUnivs)
    (hunivFrontier : UnivSeenFrontier (KExpr.ValidationUnivReach root)
      [] seenUnivs)
    {expr : KExpr .anon} {depth : UInt64}
    (hexpr : root.ValidationReach expr)
    (hseen : seenExprs.contains (expr.addr, depth) = true) :
    expr.Scoped depth bound := by
  have childSeen : ∀ ⦃child : KExpr .anon × UInt64⦄,
      child ∈ expr.validationChildrenAt depth →
      seenExprs.contains (child.1.addr, child.2) = true := by
    intro child hchild
    rcases hexprFrontier hexpr hseen hchild with h | h
    · exact h
    · simp at h
  have childReach : ∀ ⦃child : KExpr .anon × UInt64⦄,
      child ∈ expr.validationChildrenAt depth →
      root.ValidationReach child.1 := by
    intro child hchild
    exact hexpr.trans (.childAt hchild)
  have univScoped : ∀ ⦃level : KUniv .anon⦄,
      level ∈ expr.validationUnivRoots → level.Scoped bound := by
    intro level hlevel
    have hlevelDomain := hexpr.univRoot hlevel
    exact hunivFrontier.fullyScoped hcoverage.univDomain hunivLocal
      hlevelDomain (hexprUnivs hexpr hseen hlevel)
  cases expr with
  | var => exact hexprLocal hexpr hseen
  | fvar => trivial
  | sort level info =>
      exact univScoped (by simp [KExpr.validationUnivRoots])
  | const id levels info =>
      intro level hlevel
      exact univScoped (by simpa [KExpr.validationUnivRoots] using hlevel)
  | app fn arg info =>
      have hargMem : (arg, depth) ∈
          (KExpr.app fn arg info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      have hfnMem : (fn, depth) ∈
          (KExpr.app fn arg info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      exact ⟨fullyScoped (expr := fn) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hfnMem) (childSeen hfnMem),
        fullyScoped (expr := arg) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hargMem) (childSeen hargMem)⟩
  | lam name bi type body info =>
      have hbodyMem : (body, depth + 1) ∈
          (KExpr.lam name bi type body info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      have htypeMem : (type, depth) ∈
          (KExpr.lam name bi type body info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      exact ⟨fullyScoped (expr := type) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach htypeMem) (childSeen htypeMem),
        fullyScoped (expr := body) (depth := depth + 1) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hbodyMem)
          (childSeen hbodyMem)⟩
  | all name bi type body info =>
      have hbodyMem : (body, depth + 1) ∈
          (KExpr.all name bi type body info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      have htypeMem : (type, depth) ∈
          (KExpr.all name bi type body info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      exact ⟨fullyScoped (expr := type) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach htypeMem) (childSeen htypeMem),
        fullyScoped (expr := body) (depth := depth + 1) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hbodyMem)
          (childSeen hbodyMem)⟩
  | letE name type value body nonDep info =>
      have hbodyMem : (body, depth + 1) ∈
          (KExpr.letE name type value body nonDep info).validationChildrenAt
            depth := by
        simp [KExpr.validationChildrenAt]
      have hvalueMem : (value, depth) ∈
          (KExpr.letE name type value body nonDep info).validationChildrenAt
            depth := by
        simp [KExpr.validationChildrenAt]
      have htypeMem : (type, depth) ∈
          (KExpr.letE name type value body nonDep info).validationChildrenAt
            depth := by
        simp [KExpr.validationChildrenAt]
      exact ⟨fullyScoped (expr := type) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach htypeMem) (childSeen htypeMem),
        fullyScoped (expr := value) (depth := depth) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hvalueMem)
          (childSeen hvalueMem),
        fullyScoped (expr := body) (depth := depth + 1) hcoverage
          hexprLocal hexprFrontier hexprUnivs
          hunivLocal hunivFrontier (childReach hbodyMem)
          (childSeen hbodyMem)⟩
  | prj id field value info =>
      have hvalueMem : (value, depth) ∈
          (KExpr.prj id field value info).validationChildrenAt depth := by
        simp [KExpr.validationChildrenAt]
      exact fullyScoped (expr := value) (depth := depth) hcoverage
        hexprLocal hexprFrontier hexprUnivs
        hunivLocal hunivFrontier (childReach hvalueMem) (childSeen hvalueMem)
  | nat | str => trivial
termination_by expr.treeSize
decreasing_by
  all_goals simp_all [KExpr.treeSize]
  all_goals try omega

end ExprSeenFrontier

namespace ExprSeenUnivs

theorem insert
    {support : RunSupport} {root expr : KExpr .anon} {depth : UInt64}
    (hcoverage : root.ValidationCoverage support)
    (hcollision : support.CollisionFree)
    {seenExprs : HashSet (Address × UInt64)}
    {beforeUnivs afterUnivs : HashSet Address}
    (hbefore : ExprSeenUnivs root seenExprs beforeUnivs)
    (hmono : AddressSetLE beforeUnivs afterUnivs)
    (hexpr : root.ValidationReach expr)
    (hroots : ∀ ⦃level⦄, level ∈ expr.validationUnivRoots →
      afterUnivs.contains level.addr = true) :
    ExprSeenUnivs root (seenExprs.insert (expr.addr, depth)) afterUnivs := by
  intro candidate candidateDepth hcandidate hmem level hlevel
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hmem
  rcases hmem with hsame | hold
  · have hkey : (expr.addr, depth) = (candidate.addr, candidateDepth) :=
      eq_of_beq hsame
    have haddr : expr.addr = candidate.addr := congrArg Prod.fst hkey
    have herase := hcollision.expr
      (hcoverage.expr hexpr) (hcoverage.expr hcandidate) haddr
    have heq : expr = candidate := by
      simpa only [KExpr.eraseMeta_anon] using herase
    subst candidate
    exact hroots hlevel
  · exact hmono _ (hbefore hcandidate hold hlevel)

end ExprSeenUnivs

namespace ExprValidationPost

/-- Reattach a memo-hit head to the recursive tail result. -/
theorem ofHit
    {root expr : KExpr .anon} {bound : Nat} {depth : UInt64}
    {stack : List (KExpr .anon × UInt64)}
    {seenExprs finalExprs : HashSet (Address × UInt64)}
    {seenUnivs finalUnivs : HashSet Address}
    (hhit : seenExprs.contains (expr.addr, depth) = true)
    (hpost : ExprValidationPost root bound stack seenExprs finalExprs
      seenUnivs finalUnivs) :
    ExprValidationPost root bound ((expr, depth) :: stack)
      seenExprs finalExprs seenUnivs finalUnivs where
  exprLocals := hpost.exprLocals
  exprFrontier := hpost.exprFrontier
  exprUnivs := hpost.exprUnivs
  univLocals := hpost.univLocals
  univFrontier := hpost.univFrontier
  exprMonotone := hpost.exprMonotone
  univMonotone := hpost.univMonotone
  covered := by
    intro item hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hpost.exprMonotone _ hhit
    · exact hpost.covered hmem

/-- Reattach a freshly inserted head after the recursive run over its exact
expanded worklist.  Universe validation may have advanced independently
before expression recursion resumes. -/
theorem ofExpanded
    {root expr : KExpr .anon} {bound : Nat} {depth : UInt64}
    {stack expanded : List (KExpr .anon × UInt64)}
    {seenExprs finalExprs : HashSet (Address × UInt64)}
    {beforeUnivs afterUnivs finalUnivs : HashSet Address}
    (hexpanded : expanded = expr.validationChildrenAt depth ++ stack)
    (hunivMono : AddressSetLE beforeUnivs afterUnivs)
    (hpost : ExprValidationPost root bound expanded
      (seenExprs.insert (expr.addr, depth)) finalExprs
      afterUnivs finalUnivs) :
    ExprValidationPost root bound ((expr, depth) :: stack)
      seenExprs finalExprs beforeUnivs finalUnivs where
  exprLocals := hpost.exprLocals
  exprFrontier := hpost.exprFrontier
  exprUnivs := hpost.exprUnivs
  univLocals := hpost.univLocals
  univFrontier := hpost.univFrontier
  exprMonotone :=
    (AddressSetLE.insert seenExprs (expr.addr, depth)).trans
      hpost.exprMonotone
  univMonotone := hunivMono.trans hpost.univMonotone
  covered := by
    intro item hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hpost.exprMonotone _
        (AddressSetLE.insert_self seenExprs (expr.addr, depth))
    · apply hpost.covered
      rw [hexpanded]
      exact List.mem_append.mpr (.inr hmem)

end ExprValidationPost

/-! ## Sequential universe-root validation -/

/-- Ghost result of validating several direct universe roots while sharing
the production memo set. -/
structure UnivRootsPost (domain : KUniv .anon → Prop) (bound : Nat)
    (roots : List (KUniv .anon))
    (initialSeen finalSeen : HashSet Address) : Prop where
  locals : UnivSeenLocal domain bound finalSeen
  frontier : UnivSeenFrontier domain [] finalSeen
  monotone : AddressSetLE initialSeen finalSeen
  covered : ∀ ⦃level⦄, level ∈ roots →
    finalSeen.contains level.addr = true

namespace RecM

/-- Expose one `TcM` bind at a concrete starting state. -/
private theorem runTcBind {α β : Type}
    (x : TcM .anon α) (k : α → TcM .anon β)
    (state : TcState .anon) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- Soundness of the exact list-normalized `for` loop used by constant
universe arguments.  Every iteration receives the preceding iteration's
memo set and preserves the closed universe frontier. -/
theorem validateUnivRootsList_sound
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    (hcollision : support.CollisionFree) (bound : Nat) :
    ∀ (roots : List (KUniv .anon)) (seen : HashSet Address)
      (methods : Methods .anon) (state : TcState .anon)
      (finalSeen : HashSet Address) (after : TcState .anon),
      (∀ ⦃level⦄, level ∈ roots → domain level) →
      UnivSeenLocal domain bound seen →
      UnivSeenFrontier domain [] seen →
      ((forIn (m := RecM .anon) roots seen (fun level current => do
          let next ← validateUnivParamsSeen level bound current
          pure (.yield next))).run methods state = .ok finalSeen after) →
      UnivRootsPost domain bound roots seen finalSeen
  | [], seen, methods, state, finalSeen, after,
      hroots, hlocal, hfrontier, hrun => by
      rw [List.forIn_nil] at hrun
      cases hrun
      exact ⟨hlocal, hfrontier, AddressSetLE.refl seen,
        fun _ h => by simp at h⟩
  | level :: roots, seen, methods, state, finalSeen, after,
      hroots, hlocal, hfrontier, hrun => by
      rw [List.forIn_cons, ReaderT.run_bind] at hrun
      rw [ReaderT.run_bind] at hrun
      rw [bind_assoc] at hrun
      rw [runTcBind] at hrun
      cases hhead :
          (validateUnivParamsSeen level bound seen).run methods state with
      | error err failed =>
          rw [hhead] at hrun
          contradiction
      | ok nextSeen nextState =>
          rw [hhead] at hrun
          have hlevel : domain level := hroots (by simp)
          have hvalidated := validateUnivParamsSeen_sound hdomain hcollision
            hlevel hlocal hfrontier hhead
          have htailRoots : ∀ ⦃candidate⦄, candidate ∈ roots →
              domain candidate := by
            intro candidate hmem
            exact hroots (List.mem_cons.mpr (.inr hmem))
          have htail := validateUnivRootsList_sound hdomain hcollision bound
            roots nextSeen methods nextState finalSeen after htailRoots
            hvalidated.1.locals hvalidated.1.frontier hrun
          exact ⟨htail.locals, htail.frontier,
            hvalidated.1.monotone.trans htail.monotone, by
              intro candidate hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact htail.monotone _
                  (hvalidated.1.covered (by simp))
              · exact htail.covered hmem⟩

/-- Array-level bridge in the exact shape exposed by the production
constant branch. -/
theorem validateUnivRootsArray_sound
    {support : RunSupport} {domain : KUniv .anon → Prop}
    (hdomain : KUniv.ValidationDomain support domain)
    (hcollision : support.CollisionFree) (bound : Nat)
    (roots : Array (KUniv .anon)) (seen : HashSet Address)
    (methods : Methods .anon) (state : TcState .anon)
    (finalSeen : HashSet Address) (after : TcState .anon)
    (hroots : ∀ ⦃level⦄, level ∈ roots → domain level)
    (hlocal : UnivSeenLocal domain bound seen)
    (hfrontier : UnivSeenFrontier domain [] seen)
    (hrun : ((forIn (m := RecM .anon) roots seen
        (fun level current => do
          let next ← validateUnivParamsSeen level bound current
          pure (.yield next))).run methods state = .ok finalSeen after)) :
    UnivRootsPost domain bound roots.toList seen finalSeen := by
  rw [← Array.forIn_toList] at hrun
  exact validateUnivRootsList_sound hdomain hcollision bound roots.toList seen
    methods state finalSeen after (by simpa using hroots) hlocal hfrontier hrun

/-! ## Production expression validator -/

/-- Successful execution of the exact address-memoized expression worklist
produces ghost final memo sets satisfying the local/frontier certificate.
Lookup effects are intentionally unconstrained: they can affect checker
state, but not the finite syntax footprint being validated. -/
theorem validateExprWellScoped_go_sound :
    ∀ {support : RunSupport} {root : KExpr .anon},
      root.ValidationCoverage support →
      support.CollisionFree →
      ∀ (bound : Nat) (stack : List (KExpr .anon × UInt64))
        (seenExprs : HashSet (Address × UInt64))
        (seenUnivs : HashSet Address),
      ExprStackInReach root stack →
      ExprSeenLocal root seenExprs →
      ExprSeenFrontier root stack seenExprs →
      ExprSeenUnivs root seenExprs seenUnivs →
      UnivSeenLocal (KExpr.ValidationUnivReach root) bound seenUnivs →
      UnivSeenFrontier (KExpr.ValidationUnivReach root) [] seenUnivs →
      ∀ (methods : Methods .anon) (state after : TcState .anon),
      (RecM.validateExprWellScoped.go bound stack seenExprs seenUnivs).run
          methods state = .ok () after →
      ∃ finalExprs finalUnivs,
        ExprValidationPost root bound stack seenExprs finalExprs
          seenUnivs finalUnivs
  | support, root, hcoverage, hcollision, bound, [], seenExprs,
      seenUnivs, hstack, hlocal, hfrontier, hunivs, hulocal,
      hufrontier, methods, state, after, hrun => by
      rw [RecM.validateExprWellScoped.go] at hrun
      cases hrun
      exact ⟨seenExprs, seenUnivs, hlocal, hfrontier, hunivs,
        hulocal, hufrontier, AddressSetLE.refl seenExprs,
        AddressSetLE.refl seenUnivs, fun _ h => by simp at h⟩
  | support, root, hcoverage, hcollision, bound, (expr, depth) :: stack,
      seenExprs, seenUnivs, hstack, hlocal, hfrontier, hunivs,
      hulocal, hufrontier, methods, state, after, hrun => by
      rw [RecM.validateExprWellScoped.go] at hrun
      split at hrun
      · rename_i hhit
        simp only [bind_pure] at hrun
        have htailReach : ExprStackInReach root stack := by
          intro item hmem
          exact hstack (List.mem_cons.mpr (.inr hmem))
        have htailFrontier := hfrontier.dropHit hhit
        obtain ⟨finalExprs, finalUnivs, hpost⟩ :=
          validateExprWellScoped_go_sound hcoverage hcollision bound stack
            seenExprs seenUnivs htailReach hlocal htailFrontier hunivs
            hulocal hufrontier methods state after hrun
        exact ⟨finalExprs, finalUnivs,
          ExprValidationPost.ofHit hhit hpost⟩
      · rename_i hmiss
        have hexpr : root.ValidationReach expr :=
          hstack (List.mem_cons.mpr (.inl rfl))
        have htailReach : ExprStackInReach root stack := by
          intro item hmem
          exact hstack (List.mem_cons.mpr (.inr hmem))
        have hchildrenReach : ExprStackInReach root
            (expr.validationChildrenAt depth ++ stack) := by
          intro item hmem
          rcases List.mem_append.mp hmem with hchild | htail
          · exact hexpr.trans (.childAt hchild)
          · exact htailReach htail
        have hfrontier' :=
          hfrontier.insertAndExpand hcoverage hcollision hexpr
        have finishFresh
            {afterUnivs : HashSet Address} {nextState : TcState .anon}
            (hlocalNow : expr.ValidationLocal depth)
            (hunivMono : AddressSetLE seenUnivs afterUnivs)
            (hrootsCovered : ∀ ⦃level⦄,
              level ∈ expr.validationUnivRoots →
                afterUnivs.contains level.addr = true)
            (hulocalAfter : UnivSeenLocal
              (KExpr.ValidationUnivReach root) bound afterUnivs)
            (hufrontierAfter : UnivSeenFrontier
              (KExpr.ValidationUnivReach root) [] afterUnivs)
            (hdecrease : RecM.scopedExprWorkSize
                (expr.validationChildrenAt depth ++ stack) <
              RecM.scopedExprWorkSize ((expr, depth) :: stack))
            (hrun' :
              (RecM.validateExprWellScoped.go bound
                  (expr.validationChildrenAt depth ++ stack)
                  (seenExprs.insert (expr.addr, depth)) afterUnivs).run
                methods nextState = .ok () after) :
            ∃ finalExprs finalUnivs,
              ExprValidationPost root bound ((expr, depth) :: stack)
                seenExprs finalExprs seenUnivs finalUnivs := by
          have hlocal' := hlocal.insert (depth := depth)
            hcoverage hcollision hexpr hlocalNow
          have hunivs' := hunivs.insert (depth := depth)
            hcoverage hcollision hunivMono hexpr hrootsCovered
          obtain ⟨finalExprs, finalUnivs, hpost⟩ :=
            validateExprWellScoped_go_sound hcoverage hcollision bound
              (expr.validationChildrenAt depth ++ stack)
              (seenExprs.insert (expr.addr, depth)) afterUnivs
              hchildrenReach hlocal' hfrontier' hunivs'
              hulocalAfter hufrontierAfter methods nextState after hrun'
          exact ⟨finalExprs, finalUnivs,
            ExprValidationPost.ofExpanded rfl hunivMono hpost⟩
        cases expr with
        | var idx name info =>
            simp only [pure_bind] at hrun
            split at hrun
            · contradiction
            · rename_i hinRange
              apply finishFresh (afterUnivs := seenUnivs)
                (nextState := state) (by
                  simp only [KExpr.ValidationLocal]
                  exact UInt64.not_le.mp hinRange)
                (AddressSetLE.refl seenUnivs)
                (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
              · simp [RecM.scopedExprWorkSize,
                  KExpr.validationChildrenAt, KExpr.treeSize]
              · simpa [KExpr.validationChildrenAt] using hrun
        | fvar id name info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
            · simpa [KExpr.validationChildrenAt] using hrun
        | sort level info =>
            simp only [pure_bind] at hrun
            rw [ReaderT.run_bind, runTcBind] at hrun
            cases hvalidate :
                (validateUnivParamsSeen level bound seenUnivs).run
                  methods state with
            | error err failed =>
                rw [hvalidate] at hrun
                contradiction
            | ok nextUnivs nextState =>
                rw [hvalidate] at hrun
                have hlevel : KExpr.ValidationUnivReach root level :=
                  hexpr.univRoot (by simp [KExpr.validationUnivRoots])
                have hvalidated := validateUnivParamsSeen_sound
                  hcoverage.univDomain hcollision hlevel hulocal hufrontier
                  hvalidate
                apply finishFresh (afterUnivs := nextUnivs)
                  (nextState := nextState) (by trivial)
                  hvalidated.1.monotone
                  (by
                    intro candidate hmem
                    simpa [KExpr.validationUnivRoots] using
                      hvalidated.1.covered hmem)
                  hvalidated.1.locals hvalidated.1.frontier
                · simp [RecM.scopedExprWorkSize,
                    KExpr.validationChildrenAt, KExpr.treeSize]
                · simpa [KExpr.validationChildrenAt] using hrun
        | const id levels info =>
            simp only [pure_bind] at hrun
            rw [ReaderT.run_bind, ReaderT.run_monadLift, runTcBind] at hrun
            cases hget :
                (monadLift (TcM.getConst id) : TcM .anon (KConst .anon))
                  state with
            | error err failed =>
                simp only [hget] at hrun
                contradiction
            | ok declaration lookupState =>
                simp only [hget] at hrun
                split at hrun
                · contradiction
                · rw [ReaderT.run_bind, runTcBind] at hrun
                  cases hloop :
                      ((forIn (m := RecM .anon) levels seenUnivs
                        (fun level current => do
                          let next ← validateUnivParamsSeen level bound current
                          pure (.yield next))).run methods lookupState) with
                  | error err failed =>
                      rw [hloop] at hrun
                      contradiction
                  | ok nextUnivs nextState =>
                      rw [hloop] at hrun
                      have hlevels : ∀ ⦃level⦄, level ∈ levels →
                          KExpr.ValidationUnivReach root level := by
                        intro level hmem
                        exact hexpr.univRoot (by
                          simpa [KExpr.validationUnivRoots] using hmem)
                      have hvalidated := validateUnivRootsArray_sound
                        hcoverage.univDomain hcollision bound levels seenUnivs
                        methods lookupState nextUnivs nextState hlevels
                        hulocal hufrontier hloop
                      apply finishFresh (afterUnivs := nextUnivs)
                        (nextState := nextState) (by trivial)
                        hvalidated.monotone
                        (by
                          intro candidate hmem
                          exact hvalidated.covered (by
                            simpa [KExpr.validationUnivRoots] using hmem))
                        hvalidated.locals hvalidated.frontier
                      · simp [RecM.scopedExprWorkSize,
                          KExpr.validationChildrenAt, KExpr.treeSize]
                      · simpa [KExpr.validationChildrenAt] using hrun
        | app fn arg info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
              omega
            · simpa [KExpr.validationChildrenAt] using hrun
        | lam name bi type body info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
              omega
            · simpa [KExpr.validationChildrenAt] using hrun
        | all name bi type body info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
              omega
            · simpa [KExpr.validationChildrenAt] using hrun
        | letE name type value body nonDep info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
              omega
            · simpa [KExpr.validationChildrenAt] using hrun
        | prj id field value info =>
            simp only [pure_bind] at hrun
            rw [ReaderT.run_bind, ReaderT.run_monadLift, runTcBind] at hrun
            cases hhas :
                (monadLift (TcM.hasConst id) : TcM .anon Bool) state with
            | error err failed =>
                simp only [hhas] at hrun
                contradiction
            | ok found nextState =>
                simp only [hhas] at hrun
                split at hrun
                · contradiction
                · apply finishFresh (afterUnivs := seenUnivs)
                    (nextState := nextState) (by trivial)
                    (AddressSetLE.refl seenUnivs)
                    (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
                  · simp [RecM.scopedExprWorkSize,
                      KExpr.validationChildrenAt, KExpr.treeSize]
                  · simpa [KExpr.validationChildrenAt] using hrun
        | nat value blob info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
            · simpa [KExpr.validationChildrenAt] using hrun
        | str value blob info =>
            simp only [pure_bind] at hrun
            apply finishFresh (afterUnivs := seenUnivs)
              (nextState := state) (by trivial)
              (AddressSetLE.refl seenUnivs)
              (by simp [KExpr.validationUnivRoots]) hulocal hufrontier
            · simp [RecM.scopedExprWorkSize,
                KExpr.validationChildrenAt, KExpr.treeSize]
            · simpa [KExpr.validationChildrenAt] using hrun
termination_by _ _ _ _ _ stack _ _ _ _ _ _ _ _ _ _ _ _ =>
  RecM.scopedExprWorkSize stack
decreasing_by
  all_goals simp_all [RecM.scopedExprWorkSize, KExpr.validationChildrenAt]

/-- Public expression-validator soundness.  Starting from the production
empty memo sets, successful validation proves the requested root is fully
scoped at its exact binder depth and universe bound. -/
theorem validateExprWellScoped_sound
    {support : RunSupport} {root : KExpr .anon}
    (hcoverage : root.ValidationCoverage support)
    (hcollision : support.CollisionFree)
    {depth : UInt64} {bound : Nat}
    {methods : Methods .anon} {state after : TcState .anon}
    (hrun : (validateExprWellScoped root depth bound).run methods state =
      .ok () after) :
    ∃ finalExprs finalUnivs,
      ExprValidationPost root bound [(root, depth)]
          ({} : HashSet (Address × UInt64)) finalExprs
          ({} : HashSet Address) finalUnivs ∧
        root.Scoped depth bound := by
  rw [RecM.validateExprWellScoped_equation] at hrun
  obtain ⟨finalExprs, finalUnivs, hpost⟩ :=
    validateExprWellScoped_go_sound hcoverage hcollision bound
      [(root, depth)] ({} : HashSet (Address × UInt64))
      ({} : HashSet Address)
      (by
        intro item hmem
        rcases List.mem_singleton.mp hmem with rfl
        exact .refl root)
      (by
        intro expr exprDepth hexpr hmem
        simp at hmem)
      (by
        intro expr exprDepth hexpr hmem
        simp at hmem)
      (by
        intro expr exprDepth hexpr hmem
        simp at hmem)
      (by
        intro level hlevel hmem
        simp at hmem)
      (by
        intro level hlevel hmem
        simp at hmem)
      methods state after hrun
  have hseen : finalExprs.contains (root.addr, depth) = true :=
    hpost.covered (item := (root, depth)) (by simp)
  have hscoped := hpost.exprFrontier.fullyScoped hcoverage
    hpost.exprLocals hpost.exprUnivs hpost.univLocals hpost.univFrontier
    (.refl root) hseen
  exact ⟨finalExprs, finalUnivs, hpost, hscoped⟩

end RecM

end Ix.Tc
