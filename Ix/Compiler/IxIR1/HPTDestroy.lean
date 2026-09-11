import Ix.Compiler.IxIR1.HPTFetchForward

/-!
# Checked shape-specialized destruction

This consumer specializes destruction only where the current HPT domain gives
enough ownership-neutral evidence:

* a proven scalar `drop` or `dropU` becomes `pure erased`;
* a `dropU` of one exact constructor whose complete field vector is scalar
  becomes a shallow `free`.

The second rewrite is the first useful known-shape destructor.  It preserves
the root free while removing the generic node dispatch and recursive field
walk.  Heap-valued, widened, identity-only, multi-shape, and shared-root facts
remain on the generic path.  The fuel-boundary guard below records why deeper
destruction needs a fuel-neutral primitive rather than an expansion in the
current `Code` language.
-/

namespace Ix.Compiler.IxIR1.HPT.Destroy

open Ix.Compiler.IxIR1.Sim

/-- A recursive field fact which can describe only scalar run-time values.
Bottom is admitted: it cannot justify a concrete successful path. -/
def fieldScalarOnly (fact : FieldFact) : Bool :=
  !fact.unknownHeap && fact.shapes.isEmpty

/-- The exact constructor payload retained by an accepted leaf decision. -/
structure LeafShape where
  identity : CtorId
  fields : List FieldFact
  deriving BEq, Repr

/-- Recognize one exact, non-scalar constructor shape with a complete
scalar-only field vector. -/
def exactLeaf? (fact : Fact) : Option LeafShape :=
  if fact.mayScalar || fact.unknownHeap then
    none
  else
    match fact.shapes with
    | [.ctor identity (some fields)] =>
        if fields.all fieldScalarOnly then some ⟨identity, fields⟩ else none
    | _ => none

inductive Kind where
  | sharedScalar
  | uniqueScalar
  | uniqueLeaf
  deriving BEq, Repr

/-- One accepted replacement operation.  Every replacement keeps the single
let binder and returns `erased`, exactly like the source destructor. -/
structure Specialization where
  operation : Op
  kind : Kind

def specialize? (facts : List Fact) : Op → Option Specialization
  | .drop target =>
      match resolveAtomFact facts target with
      | .error _ => none
      | .ok fact =>
          if FetchForward.scalarOnly fact then
            some ⟨.pure .erased, .sharedScalar⟩
          else
            none
  | .dropU target =>
      match resolveAtomFact facts target with
      | .error _ => none
      | .ok fact =>
          if FetchForward.scalarOnly fact then
            some ⟨.pure .erased, .uniqueScalar⟩
          else if (exactLeaf? fact).isSome then
            some ⟨.free target, .uniqueLeaf⟩
          else
            none
  | _ => none

/-! The executable boundary is deliberately pinned independently of the
recursive traversal.  Exact scalar leaves are admitted; any evidence that
could hide a heap child, another root shape, or an unresolved variable stays
on the generic destructor. -/

private def guardIdentity : CtorId :=
  { block := Ixon.Address.replicate 0xd1, indIdx := 0, cidx := 0 }

private def guardChildIdentity : CtorId :=
  { block := Ixon.Address.replicate 0xd2, indIdx := 0, cidx := 1 }

private def guardLeafFact : Fact :=
  .heap (.ctor guardIdentity (some [FieldFact.scalar]))

private def guardHeapFieldFact : Fact :=
  .heap (.ctor guardIdentity
    (some [.heap (.ctor guardChildIdentity (some []))]))

private def guardIdentityOnlyFact : Fact :=
  .heap (.ctor guardIdentity none)

private def guardMultiShapeFact : Fact :=
  { mayScalar := false
    unknownHeap := false
    shapes :=
      [.ctor guardIdentity (some [FieldFact.scalar]),
       .ctor guardChildIdentity (some [])] }

private def isPureErased (kind : Kind) : Option Specialization → Bool
  | some ⟨.pure .erased, actualKind⟩ => actualKind == kind
  | none => false
  | _ => false

private def isFreeVar (index : Nat) (kind : Kind) :
    Option Specialization → Bool
  | some ⟨.free (.var actualIndex), actualKind⟩ =>
      actualIndex == index && actualKind == kind
  | none => false
  | _ => false

private def decisionBoundary : Bool :=
  isPureErased .sharedScalar
      (specialize? [Fact.scalar] (.drop (.var 0))) &&
    isPureErased .uniqueScalar
      (specialize? [Fact.scalar] (.dropU (.var 0))) &&
    isFreeVar 0 .uniqueLeaf
      (specialize? [guardLeafFact] (.dropU (.var 0))) &&
    (specialize? [guardLeafFact] (.drop (.var 0))).isNone &&
    (specialize? [guardHeapFieldFact] (.dropU (.var 0))).isNone &&
    (specialize? [guardIdentityOnlyFact] (.dropU (.var 0))).isNone &&
    (specialize? [guardMultiShapeFact] (.dropU (.var 0))).isNone &&
    (specialize? [Fact.top] (.dropU (.var 0))).isNone &&
    (specialize? [] (.dropU (.var 0))).isNone &&
    (specialize? [guardLeafFact] (.free (.var 0))).isNone

#guard decisionBoundary

/-! ## Why recursive expansion is not an IxIR₁ `Code` rewrite

The evaluator exposes `Code` nesting through fuel.  Expanding one `dropU`
inline consumes extra continuation fuel; putting the same expansion behind a
call preserves continuation fuel but adds call/invoke fuel at the destructor's
minimum successful boundary.  The two executable witnesses below pin both
failures on the smallest recursive unique tree (a unary root over a nullary
child).  This is an IR constraint, independent of HPT precision or
owner-sensitive declaration rewriting.
-/

private def fuelChildIdentity : CtorId :=
  { block := Ixon.Address.replicate 0xd3, indIdx := 0, cidx := 0 }

private def fuelRootIdentity : CtorId :=
  { block := Ixon.Address.replicate 0xd4, indIdx := 0, cidx := 0 }

private def fuelHelperAddress : Ixon.Address :=
  Ixon.Address.replicate 0xd5

/-- Fetch the unary child, shallow-free the root, then shallow-free the
nullary child.  Semantically this is the obvious exact recursive destructor. -/
private def fuelHelperBody : Code :=
  .letOp (.fetch (.var 0) 0)
    (.letOp (.free (.var 1))
      (.letOp (.free (.var 1))
        (.ret .erased)))

private def fuelHelper : FnDef :=
  { arity := 1, result := .shared, papSafe := false, body := fuelHelperBody }

private def fuelCtx : Ctx :=
  { decls := Env.ofList [(fuelHelperAddress, .fn fuelHelper)] }

private def fuelInput : Store × RVal :=
  let (withChild, child) := ({} : Store).allocNode .unique
    (.ctorN fuelChildIdentity #[])
  let (withRoot, root) := withChild.allocNode .unique
    (.ctorN fuelRootIdentity #[.loc child])
  (withRoot, .loc root)

private def pureContinuation : Nat → Code
  | 0 => .ret .erased
  | fuel + 1 => .letOp (.pure .erased) (pureContinuation fuel)

private def genericRecursiveDrop (rest : Code) : Code :=
  .letOp (.dropU (.var 0)) rest

private def inlineRecursiveDrop (rest : Code) : Code :=
  .letOp (.fetch (.var 0) 0)
    (.letOp (.free (.var 1))
      (.letOp (.free (.var 1)) rest))

private def helperRecursiveDrop (rest : Code) : Code :=
  .letOp (.call fuelHelperAddress #[.var 0]) rest

private def fuelCurrent : FnDef :=
  { arity := 1, result := .shared, papSafe := false, body := .ret .erased }

private def recursiveExpansionFuelBoundary : Bool :=
  let (store, root) := fuelInput
  let short := .ret .erased
  let long := pureContinuation 5
  match
      runCode fuelCtx 6 fuelCurrent store [root]
        (genericRecursiveDrop short),
      runCode fuelCtx 6 fuelCurrent store [root]
        (helperRecursiveDrop short),
      runCode fuelCtx 7 fuelCurrent store [root]
        (genericRecursiveDrop long),
      runCode fuelCtx 7 fuelCurrent store [root]
        (inlineRecursiveDrop long) with
  | .ok (shortStore, .erased), .error .fuel,
      .ok (longStore, .erased), .error .fuel =>
      shortStore.live == 0 && longStore.live == 0
  | _, _, _, _ => false

#guard recursiveExpansionFuelBoundary

/-- Proof-facing view of an accepted executable decision. -/
inductive Spec (facts : List Fact) : Op → Specialization → Prop where
  | sharedScalar {target fact}
      (hfact : resolveAtomFact facts target = .ok fact)
      (hscalar : FetchForward.scalarOnly fact = true) :
      Spec facts (.drop target) ⟨.pure .erased, .sharedScalar⟩
  | uniqueScalar {target fact}
      (hfact : resolveAtomFact facts target = .ok fact)
      (hscalar : FetchForward.scalarOnly fact = true) :
      Spec facts (.dropU target) ⟨.pure .erased, .uniqueScalar⟩
  | uniqueLeaf {target fact leaf}
      (hfact : resolveAtomFact facts target = .ok fact)
      (hleaf : exactLeaf? fact = some leaf) :
      Spec facts (.dropU target) ⟨.free target, .uniqueLeaf⟩

theorem spec_of_specialize?_eq_some
    {facts : List Fact} {operation : Op} {specialization : Specialization}
    (hspecialize : specialize? facts operation = some specialization) :
    Spec facts operation specialization := by
  cases operation with
  | pure atom => simp [specialize?] at hspecialize
  | alloc world identity fields => simp [specialize?] at hspecialize
  | reuse location identity fields => simp [specialize?] at hspecialize
  | free target => simp [specialize?] at hspecialize
  | dup target => simp [specialize?] at hspecialize
  | drop target =>
      simp only [specialize?] at hspecialize
      cases hfact : resolveAtomFact facts target with
      | error error => simp [hfact] at hspecialize
      | ok fact =>
          rw [hfact] at hspecialize
          by_cases hscalar : FetchForward.scalarOnly fact = true
          · simp only [hscalar, if_true, Option.some.injEq] at hspecialize
            rw [← hspecialize]
            exact .sharedScalar hfact hscalar
          · simp [hscalar] at hspecialize
  | dropU target =>
      simp only [specialize?] at hspecialize
      cases hfact : resolveAtomFact facts target with
      | error error => simp [hfact] at hspecialize
      | ok fact =>
          rw [hfact] at hspecialize
          by_cases hscalar : FetchForward.scalarOnly fact = true
          · simp only [hscalar, if_true, Option.some.injEq] at hspecialize
            rw [← hspecialize]
            exact .uniqueScalar hfact hscalar
          · simp only [hscalar] at hspecialize
            by_cases hleafSome : (exactLeaf? fact).isSome = true
            · simp only [hleafSome, if_true] at hspecialize
              cases hleaf : exactLeaf? fact with
              | none => simp [hleaf] at hleafSome
              | some leaf =>
                  simp at hspecialize
                  rw [← hspecialize]
                  exact .uniqueLeaf hfact hleaf
            · simp [hleafSome] at hspecialize
  | fetch target field => simp [specialize?] at hspecialize
  | call function arguments => simp [specialize?] at hspecialize
  | callSelf arguments => simp [specialize?] at hspecialize
  | papp function arguments => simp [specialize?] at hspecialize
  | apply function arguments => simp [specialize?] at hspecialize
  | extern name arguments => simp [specialize?] at hspecialize

structure Changes where
  elidedScalarDrops : Nat := 0
  specializedUniqueDrops : Nat := 0
  deriving BEq, Repr, Inhabited

def Changes.add (left right : Changes) : Changes :=
  { elidedScalarDrops :=
      left.elidedScalarDrops + right.elidedScalarDrops
    specializedUniqueDrops :=
      left.specializedUniqueDrops + right.specializedUniqueDrops }

def Changes.ofKind : Kind → Changes
  | .sharedScalar | .uniqueScalar => { elidedScalarDrops := 1 }
  | .uniqueLeaf => { specializedUniqueDrops := 1 }

structure Outcome where
  code : Code
  changes : Changes := {}

structure AlternativeOutcome where
  alternative : Alt
  changes : Changes := {}

mutual

/-- Mirror HPT transfer through the whole owner-sensitive code tree, replacing
only one-binder destructor operations. -/
def runWithFacts (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef) (facts : List Fact) :
    Code → Outcome
  | input@(.ret _) => ⟨input, {}⟩
  | input@(.letOp operation rest) =>
      match analyzeOp declarations summaries owner current facts operation with
      | .error _ => ⟨input, {}⟩
      | .ok bound =>
          let nested := runWithFacts declarations summaries owner current
            (bound :: facts.map Fact.forgetHeap) rest
          match specialize? facts operation with
          | none => ⟨.letOp operation nested.code, nested.changes⟩
          | some specialization =>
              ⟨.letOp specialization.operation nested.code,
                nested.changes.add (.ofKind specialization.kind)⟩
  | input@(.case scrutinee peelNat alternatives) =>
      match resolveAtomFact facts scrutinee with
      | .error _ => ⟨input, {}⟩
      | .ok fact =>
          let nested := alternatives.map
            (runAlternativeWithFacts declarations summaries owner current
              fact peelNat facts)
          ⟨.case scrutinee peelNat
              (nested.map fun result => result.alternative),
            nested.foldl
              (fun total result => total.add result.changes) {}⟩

def runAlternativeWithFacts (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Ixon.Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact) :
    Alt → AlternativeOutcome
  | .mk cidx fields body =>
      let nested := runWithFacts declarations summaries owner current
        (scrutineeFact.caseFields peelNat cidx fields ++ facts) body
      ⟨.mk cidx fields nested.code, nested.changes⟩

end

def runFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef) : Outcome :=
  runWithFacts declarations summaries owner current
    (List.replicate current.arity Fact.top) current.body

def rewriteFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef) : FnDef :=
  { current with body := (runFunction declarations summaries owner current).code }

/-! ## Semantic support for accepted decisions -/

theorem isScalar_of_fieldScalarOnly_holds
    {declarations : DeclEnv} {store : Store} {fact : FieldFact}
    {value : RVal}
    (honly : fieldScalarOnly fact = true)
    (hholds : fact.Holds declarations store value) :
    value.isScalar = true := by
  unfold fieldScalarOnly at honly
  simp only [Bool.and_eq_true] at honly
  cases hholds with
  | lit hscalar => rfl
  | erased hscalar => rfl
  | unknown hunknown =>
      have hfalse : fact.unknownHeap = false := by simpa using honly.1
      rw [hfalse] at hunknown
      contradiction
  | heap hmember hshape =>
      have hempty : fact.shapes = [] := List.isEmpty_iff.mp honly.2
      rw [hempty] at hmember
      contradiction

theorem FieldFactsHold.all_isScalar
    {declarations : DeclEnv} {store : Store} {facts : List FieldFact}
    {values : List RVal}
    (honly : facts.all fieldScalarOnly = true)
    (hholds : FieldFactsHold declarations store facts values) :
    values.all RVal.isScalar = true := by
  cases hholds with
  | nil => rfl
  | @cons fact value facts values hhead htail =>
      simp only [List.all_cons, Bool.and_eq_true] at honly ⊢
      exact ⟨isScalar_of_fieldScalarOnly_holds honly.1 hhead,
        FieldFactsHold.all_isScalar honly.2 htail⟩
termination_by sizeOf facts
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

/-- An accepted exact-leaf decision determines the concrete constructor and
proves that every stored field is a scalar. -/
theorem exactLeaf?_holds
    {declarations : DeclEnv} {store : Store} {fact : Fact}
    {value : RVal} {leaf : LeafShape}
    (hleaf : exactLeaf? fact = some leaf)
    (hholds : fact.Holds declarations store value) :
    ∃ location box fields,
      value = .loc location ∧
      store.get? location = some box ∧
      box.node = .ctorN leaf.identity fields ∧
      fields.toList.all RVal.isScalar = true := by
  cases fact with
  | mk mayScalar unknownHeap shapes =>
      unfold exactLeaf? at hleaf
      cases hmay : mayScalar with
      | true => simp [hmay] at hleaf
      | false =>
          cases hunknown : unknownHeap with
          | true => simp [hmay, hunknown] at hleaf
          | false =>
              simp only [hmay, hunknown, Bool.false_or] at hleaf
              cases shapes with
              | nil => simp at hleaf
              | cons shape tail =>
                  cases tail with
                  | cons next tail => simp at hleaf
                  | nil =>
                      cases shape with
                      | pap function supplied => simp at hleaf
                      | ctor identity fieldFacts =>
                          cases fieldFacts with
                          | none => simp at hleaf
                          | some facts =>
                              by_cases honly :
                                  facts.all fieldScalarOnly = true
                              · simp only [honly, if_true] at hleaf
                                simp at hleaf
                                rw [← hleaf]
                                cases value with
                                | lit literal =>
                                    change mayScalar = true at hholds
                                    rw [hmay] at hholds
                                    contradiction
                                | erased =>
                                    change mayScalar = true at hholds
                                    rw [hmay] at hholds
                                    contradiction
                                | loc location =>
                                    simp only [Fact.Holds, hunknown,
                                      Bool.false_eq_true, false_or] at hholds
                                    rcases hholds with
                                      ⟨heldShape, hmember, hshape⟩
                                    have hshapeEq : heldShape =
                                        .ctor identity (some facts) := by
                                      simpa using hmember
                                    subst heldShape
                                    rcases hshape with
                                      ⟨box, fields, hget, hnode, hfields⟩
                                    exact ⟨location, box, fields, rfl, hget,
                                      hnode,
                                      FieldFactsHold.all_isScalar honly
                                        hfields⟩
                              · simp [honly] at hleaf

private theorem dropUVal_eq_store_of_isScalar_success
    {ctx : Ctx} {fuel : Nat} {store result : Store} {value : RVal}
    (hscalar : value.isScalar = true)
    (hrun : dropUVal ctx fuel store value = .ok result) :
    result = store := by
  cases fuel with
  | zero => simp [dropUVal] at hrun
  | succ fuel =>
      cases value with
      | lit literal =>
          simp only [dropUVal] at hrun
          exact (Except.ok.inj hrun).symm
      | erased =>
          simp only [dropUVal] at hrun
          exact (Except.ok.inj hrun).symm
      | loc location => simp [RVal.isScalar] at hscalar

private theorem dropManyU_eq_store_of_all_isScalar_success
    {ctx : Ctx} {fuel : Nat} {store result : Store} {values : List RVal}
    (hscalar : values.all RVal.isScalar = true)
    (hrun : dropManyU ctx fuel store values = .ok result) :
    result = store := by
  induction fuel generalizing store result values with
  | zero => simp [dropManyU] at hrun
  | succ fuel ih =>
      cases values with
      | nil =>
          simp only [dropManyU] at hrun
          exact (Except.ok.inj hrun).symm
      | cons value values =>
          simp only [List.all_cons, Bool.and_eq_true] at hscalar
          rw [dropManyU.eq_def] at hrun
          dsimp only at hrun
          cases hfirst : dropUVal ctx fuel store value with
          | error error => simp [hfirst, bind, Except.bind] at hrun
          | ok middle =>
              simp only [hfirst, bind, Except.bind] at hrun
              have hmiddle :=
                dropUVal_eq_store_of_isScalar_success hscalar.1 hfirst
              subst middle
              exact ih hscalar.2 hrun

private theorem dropUVal_eq_kill_of_ctor_all_isScalar_success
    {ctx : Ctx} {fuel : Nat} {store result : Store} {value : RVal}
    {location : Nat} {box : NodeBox} {identity : CtorId}
    {fields : Array RVal}
    (hvalue : value = .loc location)
    (hget : store.get? location = some box)
    (hnode : box.node = .ctorN identity fields)
    (hscalar : fields.toList.all RVal.isScalar = true)
    (hrun : dropUVal ctx fuel store value = .ok result) :
    box.world = .unique ∧ result = store.kill location := by
  subst value
  cases fuel with
  | zero => simp [dropUVal] at hrun
  | succ fuel =>
      rw [dropUVal.eq_def] at hrun
      dsimp only at hrun
      rw [hget] at hrun
      cases hworld : box.world with
      | shared => simp [hworld] at hrun
      | unique =>
          refine ⟨rfl, ?_⟩
          simp only at hrun
          rw [hworld, hnode] at hrun
          exact dropManyU_eq_store_of_all_isScalar_success hscalar hrun

/-- Every accepted local specialization preserves a successful operation
result exactly.  The implication is intentionally one-way: a shallow free
can need less fuel than the generic deep-drop interpreter. -/
theorem runOp_specialize?_success
    {declarations : DeclEnv} {facts : List Fact} {operation : Op}
    {specialization : Specialization} {ctx : Ctx} {fuel : Nat}
    {current : FnDef} {store : Store} {environment : List RVal}
    {output : Store × RVal}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hspecialize : specialize? facts operation = some specialization)
    (hrun : runOp ctx fuel current store environment operation = .ok output) :
    runOp ctx fuel current store environment specialization.operation =
      .ok output := by
  have hspec := spec_of_specialize?_eq_some hspecialize
  cases hspec with
  | @sharedScalar target fact hfact hscalar =>
      cases fuel with
      | zero => simp [runOp] at hrun
      | succ fuel =>
          rw [runOp.eq_def] at hrun ⊢
          dsimp only at hrun ⊢
          cases hresolve : resolveAtom environment target with
          | error error => simp [hresolve, bind, Except.bind] at hrun
          | ok value =>
              have hholds := resolveAtom_sound henvironment hfact hresolve
              have hvalue :=
                FetchForward.scalar_of_scalarOnly_holds hscalar hholds
              rw [hresolve] at hrun
              simp only [bind, Except.bind] at hrun
              cases value with
              | lit literal =>
                  dsimp only at hrun
                  change Except.ok (store, .erased) = .ok output
                  exact hrun
              | erased =>
                  dsimp only at hrun
                  change Except.ok (store, .erased) = .ok output
                  exact hrun
              | loc location => simp [RVal.isScalar] at hvalue
  | @uniqueScalar target fact hfact hscalar =>
      cases fuel with
      | zero => simp [runOp] at hrun
      | succ fuel =>
          rw [runOp.eq_def] at hrun ⊢
          dsimp only at hrun ⊢
          cases hresolve : resolveAtom environment target with
          | error error => simp [hresolve, bind, Except.bind] at hrun
          | ok value =>
              have hholds := resolveAtom_sound henvironment hfact hresolve
              have hvalue :=
                FetchForward.scalar_of_scalarOnly_holds hscalar hholds
              rw [hresolve] at hrun
              simp only [bind, Except.bind] at hrun
              cases value with
              | lit literal =>
                  dsimp only at hrun
                  change Except.ok (store, .erased) = .ok output
                  exact hrun
              | erased =>
                  dsimp only at hrun
                  change Except.ok (store, .erased) = .ok output
                  exact hrun
              | loc location => simp [RVal.isScalar] at hvalue
  | @uniqueLeaf target fact leaf hfact hleaf =>
      cases fuel with
      | zero => simp [runOp] at hrun
      | succ fuel =>
          rw [runOp.eq_def] at hrun ⊢
          dsimp only at hrun ⊢
          cases hresolve : resolveAtom environment target with
          | error error => simp [hresolve, bind, Except.bind] at hrun
          | ok value =>
              have hholds := resolveAtom_sound henvironment hfact hresolve
              obtain ⟨location, box, fields, hvalue, hget, hnode, hscalar⟩ :=
                exactLeaf?_holds hleaf hholds
              subst value
              simp only [hresolve] at hrun ⊢
              simp only [bind, Except.bind] at hrun ⊢
              cases hdrop : dropUVal ctx fuel store (.loc location) with
              | error error => simp [hdrop] at hrun
              | ok dropped =>
                  rw [hdrop] at hrun
                  obtain ⟨hworld, hkilled⟩ :=
                    dropUVal_eq_kill_of_ctor_all_isScalar_success rfl hget
                      hnode hscalar hdrop
                  subst dropped
                  rw [hget]
                  simp only
                  rw [hworld]
                  simpa using hrun

/-! ## Successful recursive traversal -/

@[simp] private theorem runAlternativeWithFacts_cidx
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternative : Alt) :
    (runAlternativeWithFacts declarations summaries owner current
      scrutineeFact peelNat facts alternative).alternative.cidx =
        alternative.cidx := by
  cases alternative
  simp [runAlternativeWithFacts, Alt.cidx]

private theorem runAlternativeWithFacts_predicate
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (index : Nat) :
    ((fun alternative : Alt => alternative.cidx == index) ∘
        (fun result : AlternativeOutcome => result.alternative) ∘
        runAlternativeWithFacts declarations summaries owner current
          scrutineeFact peelNat facts) =
      (fun alternative => alternative.cidx == index) := by
  funext alternative
  cases alternative
  simp [Function.comp_def, runAlternativeWithFacts, Alt.cidx]

private theorem find?_runAlternativeWithFacts
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ixon.Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternatives : Array Alt) (index : Nat) :
    ((alternatives.map
        (runAlternativeWithFacts declarations summaries owner current
          scrutineeFact peelNat facts)).map
        (fun result => result.alternative)).find?
          (fun alternative => alternative.cidx == index) =
      (alternatives.find? (fun alternative => alternative.cidx == index)).map
        (fun alternative =>
          (runAlternativeWithFacts declarations summaries owner current
            scrutineeFact peelNat facts alternative).alternative) := by
  rw [Array.map_map, Array.find?_map,
    runAlternativeWithFacts_predicate declarations summaries owner current
      scrutineeFact peelNat facts index]
  simp [Function.comp_def]

private theorem Array.foldl_cons_eq_reverse_append
    (fields : Array RVal) (environment : List RVal) :
    fields.foldl (fun current field => field :: current) environment =
      fields.toList.reverse ++ environment := by
  rw [← Array.foldl_toList]
  induction fields.toList generalizing environment with
  | nil => rfl
  | cons field fields ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Case traversal preserves a successful selected branch once its HPT
binders have been justified against the concrete scrutinee. -/
private theorem runCode_caseWithFactsBodies_success
    {declarations : DeclEnv} {summaries : SummaryEnv}
    {owner : Ixon.Address} {current : FnDef}
    {ctx : Ctx} {store : Store} {facts : List Fact}
    {environment : List RVal} {scrutinee : Atom} {peelNat : Bool}
    {alternatives : Array Alt} {scrutineeFact : Fact} {fuel : Nat}
    {output : Store × RVal}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (habstract : resolveAtomFact facts scrutinee = .ok scrutineeFact)
    (ih : ∀ {store : Store} {facts : List Fact}
      {environment : List RVal} {input : Code} {output : Store × RVal},
      EnvironmentHolds declarations store facts environment →
      runCode ctx fuel current store environment input = .ok output →
      runCode ctx fuel current store environment
          (runWithFacts declarations summaries owner current facts input).code =
        .ok output)
    (hrun : runCode ctx (fuel + 1) current store environment
      (.case scrutinee peelNat alternatives) = .ok output) :
    runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat
          ((alternatives.map
            (runAlternativeWithFacts declarations summaries owner current
              scrutineeFact peelNat facts)).map
                (fun result => result.alternative))) =
      .ok output := by
  obtain ⟨scrutineeValue, hresolve⟩ :=
    resolveAtom_complete henvironment habstract
  have hscrutineeHolds :=
    resolveAtom_sound henvironment habstract hresolve
  simp only [runCode] at hrun ⊢
  rw [hresolve] at hrun ⊢
  simp only [bind, Except.bind] at hrun ⊢
  cases scrutineeValue with
  | erased => contradiction
  | lit literal =>
      cases literal with
      | str value => contradiction
      | nat value =>
          simp only at hrun ⊢
          cases peelNat with
          | false => contradiction
          | true =>
              simp only at hrun ⊢
              cases value with
              | zero =>
                  simp only at hrun ⊢
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 0) with
                  | none => simp [hfind] at hrun
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero =>
                              have hzero :
                                  scrutineeFact.caseFields true cidx 0 = [] := by
                                unfold Fact.caseFields
                                split <;> rfl
                              have hbody :
                                  runCode ctx fuel current store environment
                                    body = .ok output := by
                                simpa [hfind] using hrun
                              simpa [runAlternativeWithFacts, hzero]
                                using (ih henvironment hbody)
                          | succ fields => simp [hfind] at hrun
              | succ value =>
                  simp only at hrun ⊢
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 1) with
                  | none => simp [hfind] at hrun
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero => simp [hfind] at hrun
                          | succ fields =>
                              cases fields with
                              | zero =>
                                  have hcidx : cidx = 1 := by
                                    have hmatch := Array.find?_some
                                      (p := fun alternative : Alt =>
                                        alternative.cidx == 1)
                                      (a := .mk cidx 1 body)
                                      (xs := alternatives) hfind
                                    exact beq_iff_eq.mp hmatch
                                  have hbinders :
                                      EnvironmentHolds declarations store
                                        (scrutineeFact.caseFields true cidx 1)
                                        [.lit (.nat value)] := by
                                    simpa [hcidx] using
                                      (Fact.caseFields_natSucc_holds
                                        hscrutineeHolds)
                                  have hbody :
                                      runCode ctx fuel current store
                                        (.lit (.nat value) :: environment)
                                        body = .ok output := by
                                    simpa [hfind] using hrun
                                  simpa [runAlternativeWithFacts] using
                                    (ih (hbinders.append henvironment) hbody)
                              | succ fields => simp [hfind] at hrun
  | loc location =>
      simp only at hrun ⊢
      cases hget : store.get? location with
      | none => simp [hget] at hrun
      | some box =>
          simp only at hrun ⊢
          cases hnode : box.node with
          | papN function arity arguments => simp [hget, hnode] at hrun
          | ctorN identity fields =>
              simp only at hrun ⊢
              rw [find?_runAlternativeWithFacts]
              cases hfind : alternatives.find?
                  (fun alternative => alternative.cidx == identity.cidx) with
              | none => simp [hget, hnode, hfind] at hrun
              | some alternative =>
                  cases alternative with
                  | mk cidx fieldCount body =>
                      by_cases hfields : fields.size = fieldCount
                      · have hcidx : identity.cidx = cidx := by
                          have hmatch := Array.find?_some
                            (p := fun alternative : Alt =>
                              alternative.cidx == identity.cidx)
                            (a := .mk cidx fieldCount body)
                            (xs := alternatives) hfind
                          exact (beq_iff_eq.mp hmatch).symm
                        have hbinders := Fact.caseFields_ctor_holds
                          peelNat cidx fieldCount hscrutineeHolds hget hnode
                          hcidx hfields
                        have hbody :
                            runCode ctx fuel current store
                              (fields.foldl
                                (fun current field => field :: current)
                                environment) body = .ok output := by
                          simpa [hget, hnode, hfind, hfields] using hrun
                        rw [Array.foldl_cons_eq_reverse_append]
                        simpa [hfields, runAlternativeWithFacts] using
                            (ih (hbinders.append henvironment) (by
                              rw [← Array.foldl_cons_eq_reverse_append]
                              exact hbody))
                      · simp [hget, hnode, hfind, hfields] at hrun

/-- Successful evaluator refinement for the complete owner-sensitive
destruction traversal. -/
theorem runCode_runWithFacts_success_ownerCompatible
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ixon.Address} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {input : Code} {fuel : Nat} {output : Store × RVal}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hrun : runCode ctx fuel current store environment input = .ok output) :
    runCode ctx fuel current store environment
        (runWithFacts declarations summaries owner current facts input).code =
      .ok output := by
  induction fuel generalizing store facts environment input output with
  | zero => simp [runCode] at hrun
  | succ fuel ih =>
      cases input with
      | ret atom => simpa [runWithFacts] using hrun
      | letOp operation rest =>
          cases habstract : analyzeOp declarations summaries owner current
              facts operation with
          | error error =>
              simpa [runWithFacts, habstract] using hrun
          | ok bound =>
              let nested := runWithFacts declarations summaries owner current
                (bound :: facts.map Fact.forgetHeap) rest
              simp only [runCode] at hrun
              cases hoperation : runOp ctx fuel current store environment
                  operation with
              | error error => simp [hoperation, bind, Except.bind] at hrun
              | ok operationOutput =>
                  rcases operationOutput with ⟨outputStore, outputValue⟩
                  rw [hoperation] at hrun
                  simp only [bind, Except.bind] at hrun
                  have hbound := analyzeOp_sound_ownerCompatible hpost hctx
                    howner henvironment habstract hoperation
                  have hold := EnvironmentHolds.forgetHeap
                    (after := outputStore) henvironment
                  have hnested :
                      runCode ctx fuel current outputStore
                          (outputValue :: environment) nested.code =
                        .ok output := by
                    simpa [nested] using
                      (ih (store := outputStore)
                        (facts := bound :: facts.map Fact.forgetHeap)
                        (environment := outputValue :: environment)
                        (input := rest) (.cons hbound hold) hrun)
                  cases hspecialize : specialize? facts operation with
                  | none =>
                      simp only [runWithFacts, habstract, hspecialize, runCode]
                      rw [hoperation]
                      simp only [bind, Except.bind]
                      exact hnested
                  | some specialization =>
                      have hspecialized := runOp_specialize?_success
                        henvironment hspecialize hoperation
                      simp only [runWithFacts, habstract, hspecialize, runCode]
                      rw [hspecialized]
                      simp only [bind, Except.bind]
                      exact hnested
      | case scrutinee peelNat alternatives =>
          cases habstract : resolveAtomFact facts scrutinee with
          | error error => simpa [runWithFacts, habstract] using hrun
          | ok scrutineeFact =>
              simpa [runWithFacts, habstract] using
                (runCode_caseWithFactsBodies_success henvironment habstract
                  (fun henv hsuccess => ih henv hsuccess) hrun)

/-- Stored-function specialization of successful destruction refinement. -/
theorem runCode_runWithFacts_success
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ixon.Address} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {input : Code} {fuel : Nat} {output : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hrun : runCode ctx fuel current store environment input = .ok output) :
    runCode ctx fuel current store environment
        (runWithFacts declarations summaries owner current facts input).code =
      .ok output :=
  runCode_runWithFacts_success_ownerCompatible hpost hctx (.inl hcurrent)
    henvironment hrun

end Ix.Compiler.IxIR1.HPT.Destroy
