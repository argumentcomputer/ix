import Ix.Compiler.IxIR1.HPTPAPFuse

/-!
# Checked scalar fetch forwarding

This consumer recognizes an immediately projected constructor field:

```text
let node := alloc/reuse constructor fields
let field := fetch node i
rest
```

When the selected source atom is HPT-proven scalar, the projection is replaced
by `pure` of that atom lifted across the node binder.  Both binders and the
constructor operation remain in place, so the rewrite preserves evaluator
fuel, stores, allocation identities, and every continuation index exactly.

The scalar restriction is the ownership boundary.  Reusing a heap-valued
source atom after it was installed in a node could duplicate or revive an
owner in the validated syntax; scalars carry no heap ownership.
-/

namespace Ix.Compiler.IxIR1.HPT.FetchForward

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Sim

/-- Lift an atom across the constructor result binder retained by the rewrite. -/
def liftAtom : Atom → Atom
  | .var index => .var (index + 1)
  | .lit literal => .lit literal
  | .erased => .erased

theorem resolveAtom_liftAtom_of_eq_ok {head : RVal}
    {environment : List RVal} {atom : Atom} {value : RVal}
    (hresolve : resolveAtom environment atom = .ok value) :
    resolveAtom (head :: environment) (liftAtom atom) = .ok value := by
  cases atom with
  | lit literal => simpa [liftAtom, resolveAtom] using hresolve
  | erased => simpa [liftAtom, resolveAtom] using hresolve
  | var index =>
      simp only [resolveAtom] at hresolve ⊢
      cases hget : environment[index]? with
      | none => simp [hget] at hresolve
      | some found => simpa [liftAtom, hget] using hresolve

/-- A fact which admits no heap value.  Bottom is accepted because its
concrete interpretation cannot authorize a successful non-scalar execution. -/
def scalarOnly (fact : Fact) : Bool :=
  !fact.unknownHeap && fact.shapes.isEmpty

private def selectedScalarAtom? (facts : List Fact) (arguments : Array Atom)
    (field : Nat) : Option Atom :=
  match arguments[field]? with
  | none => none
  | some atom =>
      match resolveAtomFact facts atom with
      | .error _ => none
      | .ok fact => if scalarOnly fact then some atom else none

inductive Kind where
  | allocation
  | reuse
  deriving BEq, Repr

/-- One accepted forwarding decision and its source-side operand. -/
structure Forwarding where
  code : Code
  source : Atom
  kind : Kind

/-- Try to replace the head fetch of an already recursively rewritten
continuation.  Only the constructor-producing operation immediately outside
that continuation is considered. -/
def forwardHead? (facts : List Fact) (operation : Op)
    (continuation : Code) : Option Forwarding :=
  match continuation with
  | .letOp (.fetch (.var 0) field) rest =>
      match operation with
      | .alloc world identity arguments => do
          let atom ← selectedScalarAtom? facts arguments field
          return ⟨.letOp (.alloc world identity arguments)
              (.letOp (.pure (liftAtom atom)) rest), atom, .allocation⟩
      | .reuse target identity arguments => do
          let atom ← selectedScalarAtom? facts arguments field
          return ⟨.letOp (.reuse target identity arguments)
              (.letOp (.pure (liftAtom atom)) rest), atom, .reuse⟩
      | _ => none
  | _ => none

/-- Proof-facing view of an accepted executable decision. -/
inductive ForwardSpec (facts : List Fact) : Op → Code → Forwarding → Prop where
  | allocation {world identity arguments field rest atom fact}
      (hfield : arguments[field]? = some atom)
      (hfact : resolveAtomFact facts atom = .ok fact)
      (hscalar : scalarOnly fact = true) :
      ForwardSpec facts (.alloc world identity arguments)
        (.letOp (.fetch (.var 0) field) rest)
        ⟨.letOp (.alloc world identity arguments)
            (.letOp (.pure (liftAtom atom)) rest), atom, .allocation⟩
  | reuse {target identity arguments field rest atom fact}
      (hfield : arguments[field]? = some atom)
      (hfact : resolveAtomFact facts atom = .ok fact)
      (hscalar : scalarOnly fact = true) :
      ForwardSpec facts (.reuse target identity arguments)
        (.letOp (.fetch (.var 0) field) rest)
        ⟨.letOp (.reuse target identity arguments)
            (.letOp (.pure (liftAtom atom)) rest), atom, .reuse⟩

theorem forwardSpec_of_forwardHead?_eq_some
    {facts : List Fact} {operation : Op} {continuation : Code}
    {forwarding : Forwarding}
    (hforward : forwardHead? facts operation continuation = some forwarding) :
    ForwardSpec facts operation continuation forwarding := by
  cases continuation with
  | ret atom => simp [forwardHead?] at hforward
  | case scrutinee peelNat alternatives => simp [forwardHead?] at hforward
  | letOp next rest =>
      cases next with
      | fetch target field =>
          cases target with
          | var index =>
              cases index with
              | zero =>
                  cases operation with
                  | alloc world identity arguments =>
                    simp only [forwardHead?, selectedScalarAtom?] at hforward
                    split at hforward
                    · simp at hforward
                    · rename_i atom hfield
                      split at hforward
                      · simp at hforward
                      · rename_i fact hfact
                        split at hforward
                        · rename_i hscalar
                          injection hforward with hforwarding
                          subst forwarding
                          exact .allocation hfield hfact hscalar
                        · simp at hforward
                  | reuse target identity arguments =>
                    simp only [forwardHead?, selectedScalarAtom?] at hforward
                    split at hforward
                    · simp at hforward
                    · rename_i atom hfield
                      split at hforward
                      · simp at hforward
                      · rename_i fact hfact
                        split at hforward
                        · rename_i hscalar
                          injection hforward with hforwarding
                          subst forwarding
                          exact .reuse hfield hfact hscalar
                        · simp at hforward
                  | pure atom => simp [forwardHead?] at hforward
                  | free target => simp [forwardHead?] at hforward
                  | dup target => simp [forwardHead?] at hforward
                  | drop target => simp [forwardHead?] at hforward
                  | dropU target => simp [forwardHead?] at hforward
                  | fetch target field => simp [forwardHead?] at hforward
                  | call function arguments => simp [forwardHead?] at hforward
                  | callSelf arguments => simp [forwardHead?] at hforward
                  | papp function arguments => simp [forwardHead?] at hforward
                  | apply function arguments => simp [forwardHead?] at hforward
                  | extern function arguments => simp [forwardHead?] at hforward
              | succ index => simp [forwardHead?] at hforward
          | lit literal => simp [forwardHead?] at hforward
          | erased => simp [forwardHead?] at hforward
      | pure atom => simp [forwardHead?] at hforward
      | alloc world identity arguments => simp [forwardHead?] at hforward
      | reuse target identity arguments => simp [forwardHead?] at hforward
      | free target => simp [forwardHead?] at hforward
      | dup target => simp [forwardHead?] at hforward
      | drop target => simp [forwardHead?] at hforward
      | dropU target => simp [forwardHead?] at hforward
      | call function arguments => simp [forwardHead?] at hforward
      | callSelf arguments => simp [forwardHead?] at hforward
      | papp function arguments => simp [forwardHead?] at hforward
      | apply function arguments => simp [forwardHead?] at hforward
      | extern function arguments => simp [forwardHead?] at hforward

structure Changes where
  forwardedFetches : Nat := 0
  afterAllocations : Nat := 0
  afterReuses : Nat := 0
  deriving BEq, Repr, Inhabited

def Changes.add (left right : Changes) : Changes :=
  { forwardedFetches := left.forwardedFetches + right.forwardedFetches
    afterAllocations := left.afterAllocations + right.afterAllocations
    afterReuses := left.afterReuses + right.afterReuses }

def Changes.ofKind : Kind → Changes
  | .allocation => { forwardedFetches := 1, afterAllocations := 1 }
  | .reuse => { forwardedFetches := 1, afterReuses := 1 }

structure Outcome where
  code : Code
  changes : Changes := {}

structure AlternativeOutcome where
  alternative : Alt
  changes : Changes := {}

mutual

/-- Mirror HPT transfer, recursively rewrite each continuation, and then
forward a scalar fetch at the current let boundary when possible. -/
def runWithFacts (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) (facts : List Fact) : Code → Outcome
  | input@(.ret _) => ⟨input, {}⟩
  | input@(.letOp operation rest) =>
      match analyzeOp declarations summaries owner current facts operation with
      | .error _ => ⟨input, {}⟩
      | .ok bound =>
          let nested := runWithFacts declarations summaries owner current
            (bound :: facts.map Fact.forgetHeap) rest
          match forwardHead? facts operation nested.code with
          | some forwarding =>
              ⟨forwarding.code,
                nested.changes.add (.ofKind forwarding.kind)⟩
          | none => ⟨.letOp operation nested.code, nested.changes⟩
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
    (summaries : SummaryEnv) (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact) :
    Alt → AlternativeOutcome
  | .mk cidx fields body =>
      let nested := runWithFacts declarations summaries owner current
        (scrutineeFact.caseFields peelNat cidx fields ++ facts) body
      ⟨.mk cidx fields nested.code, nested.changes⟩

end

def runFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) : Outcome :=
  runWithFacts declarations summaries owner current
    (List.replicate current.arity Fact.top) current.body

def rewriteFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) : FnDef :=
  { current with body := (runFunction declarations summaries owner current).code }

/-! ## Semantic support for one forwarded field -/

theorem scalar_of_scalarOnly_holds
    {declarations : DeclEnv} {store : Store} {fact : Fact} {value : RVal}
    (honly : scalarOnly fact = true)
    (hholds : fact.Holds declarations store value) :
    value.isScalar = true := by
  unfold scalarOnly at honly
  simp only [Bool.and_eq_true] at honly
  cases value with
  | lit literal => rfl
  | erased => rfl
  | loc location =>
      simp only [Fact.Holds] at hholds
      rcases hholds with hunknown | ⟨shape, hmember, _⟩
      · have hfalse : fact.unknownHeap = false := by
          simpa using honly.1
        rw [hfalse] at hunknown
        contradiction
      · have hempty : fact.shapes = [] := List.isEmpty_iff.mp honly.2
        rw [hempty] at hmember
        contradiction

private def resolveStep (environment : List RVal)
    (values : List RVal) (atom : Atom) : Except Err (List RVal) := do
  pure (values ++ [← resolveAtom environment atom])

private inductive AtomsResolve (environment : List RVal) :
    List Atom → List RVal → Prop where
  | nil : AtomsResolve environment [] []
  | cons (hhead : resolveAtom environment atom = .ok value)
      (htail : AtomsResolve environment atoms values) :
      AtomsResolve environment (atom :: atoms) (value :: values)

namespace AtomsResolve

private theorem foldlM {environment : List RVal} :
    ∀ {atoms values}, AtomsResolve environment atoms values →
      ∀ accumulator,
        atoms.foldlM (resolveStep environment) accumulator =
          .ok (accumulator ++ values)
  | [], [], .nil, accumulator => by
      simp only [List.foldlM_nil, pure, Except.pure, List.append_nil]
  | atom :: atoms, value :: values, .cons hhead htail, accumulator => by
      have hstep : resolveStep environment accumulator atom =
          .ok (accumulator ++ [value]) := by
        simp [resolveStep, hhead, bind, Except.bind, pure, Except.pure]
      rw [List.foldlM_cons, hstep]
      simp only [bind, Except.bind]
      rw [htail.foldlM (accumulator ++ [value])]
      simp [List.append_assoc]

private theorem ofFoldlM {environment : List RVal} :
    ∀ atoms accumulator output,
      atoms.foldlM (resolveStep environment) accumulator = .ok output →
      ∃ values, AtomsResolve environment atoms values ∧
        output = accumulator ++ values := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output hrun
      simp only [List.foldlM_nil, pure, Except.pure] at hrun
      injection hrun with houtput
      subst output
      exact ⟨[], .nil, by simp⟩
  | cons atom atoms ih =>
      intro accumulator output hrun
      simp only [List.foldlM_cons] at hrun
      cases hhead : resolveAtom environment atom with
      | error error =>
          have hstep : resolveStep environment accumulator atom =
              .error error := by
            simp [resolveStep, hhead, bind, Except.bind]
          rw [hstep] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok value =>
          have hstep : resolveStep environment accumulator atom =
              .ok (accumulator ++ [value]) := by
            simp [resolveStep, hhead, bind, Except.bind, pure, Except.pure]
          rw [hstep] at hrun
          simp only [bind, Except.bind] at hrun
          obtain ⟨values, hvalues, houtput⟩ :=
            ih (accumulator ++ [value]) output hrun
          refine ⟨value :: values, .cons hhead hvalues, ?_⟩
          rw [houtput]
          simp [List.append_assoc]

private theorem getElem? {environment : List RVal} :
    ∀ {atoms values}, AtomsResolve environment atoms values →
      ∀ {field : Nat} {atom : Atom}, atoms[field]? = some atom →
        ∃ value, values[field]? = some value ∧
          resolveAtom environment atom = .ok value := by
  intro atoms values hresolve
  induction hresolve with
  | nil => intro field atom hfield; simp at hfield
  | @cons atom value atoms values hhead htail ih =>
      intro field selected hfield
      cases field with
      | zero =>
          simp only [List.getElem?_cons_zero] at hfield
          injection hfield with hselected
          subst selected
          exact ⟨value, rfl, hhead⟩
      | succ field =>
          simp only [List.getElem?_cons_succ] at hfield
          obtain ⟨selectedValue, hvalue, hatom⟩ := ih hfield
          exact ⟨selectedValue, by simpa using hvalue, hatom⟩

end AtomsResolve

private theorem atomsResolve_of_resolveAtoms {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (hrun : resolveAtoms environment atoms = .ok values) :
    AtomsResolve environment atoms.toList values := by
  unfold resolveAtoms at hrun
  rw [← Array.foldlM_toList] at hrun
  change atoms.toList.foldlM (resolveStep environment) [] = .ok values at hrun
  obtain ⟨found, hfound, hvalues⟩ :=
    AtomsResolve.ofFoldlM atoms.toList [] values hrun
  simp only [List.nil_append] at hvalues
  subst found
  exact hfound

private theorem selectedAtom_resolves
    {environment : List RVal} {arguments : Array Atom} {values : List RVal}
    {field : Nat} {atom : Atom}
    (harguments : resolveAtoms environment arguments = .ok values)
    (hfield : arguments[field]? = some atom) :
    ∃ value, resolveAtom environment atom = .ok value ∧
      values.toArray[field]? = some value := by
  have hfieldList : arguments.toList[field]? = some atom := by
    simpa using hfield
  obtain ⟨value, hvalue, hresolve⟩ :=
    AtomsResolve.getElem? (atomsResolve_of_resolveAtoms harguments) hfieldList
  exact ⟨value, hresolve, by simpa using hvalue⟩

/-- Once a constructor-producing operation has installed the selected field,
the retained-binder `pure` resolves to exactly the value that `fetch` returns. -/
private theorem runOp_pure_eq_fetch_ctor
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {store : Store}
    {environment : List RVal} {location : Nat} {world : Ixon.Owned}
    {rc : Nat} {identity : CtorId} {arguments : Array Atom}
    {values : List RVal} {field : Nat} {atom : Atom}
    (hget : store.get? location =
      some ⟨world, rc, .ctorN identity values.toArray⟩)
    (harguments : resolveAtoms environment arguments = .ok values)
    (hfield : arguments[field]? = some atom) :
    runOp ctx fuel current store (.loc location :: environment)
        (.pure (liftAtom atom)) =
      runOp ctx fuel current store (.loc location :: environment)
        (.fetch (.var 0) field) := by
  cases fuel with
  | zero => rw [runOp.eq_def, runOp.eq_def]
  | succ fuel =>
      obtain ⟨value, hresolve, hvalue⟩ :=
        selectedAtom_resolves harguments hfield
      simp only [runOp]
      rw [resolveAtom_liftAtom_of_eq_ok hresolve]
      simp only [bind, Except.bind, resolveAtom, List.getElem?_cons_zero]
      rw [hget]
      simp only
      rw [hvalue]

/-- Every accepted local decision preserves the complete evaluator result,
including errors, fuel behavior, stores, and instruction counters. -/
theorem runCode_forwardHead?_eq
    {facts : List Fact} {operation : Op} {continuation : Code}
    {forwarding : Forwarding} {ctx : Ctx} {fuel : Nat}
    {current : FnDef} {store : Store} {environment : List RVal}
    (hforward : forwardHead? facts operation continuation = some forwarding) :
    runCode ctx fuel current store environment forwarding.code =
      runCode ctx fuel current store environment
        (.letOp operation continuation) := by
  have hspec := forwardSpec_of_forwardHead?_eq_some hforward
  cases hspec with
  | @allocation world identity arguments field rest atom fact hfield hfact
      hscalar =>
      cases fuel with
      | zero => rw [runCode.eq_def, runCode.eq_def]
      | succ outerFuel =>
          cases outerFuel with
          | zero => simp [runCode, runOp]
          | succ operationFuel =>
              cases harguments : resolveAtoms environment arguments with
              | error error =>
                  simp [runCode, runOp, harguments, bind, Except.bind]
              | ok values =>
                  let allocated :=
                    store.allocNode world (.ctorN identity values.toArray)
                  have hoperation :
                      runOp ctx (operationFuel + 1) current store environment
                          (.alloc world identity arguments) =
                        .ok (allocated.1, .loc allocated.2) := by
                    simp [runOp, harguments, allocated, bind, Except.bind]
                  have hget : allocated.1.get? allocated.2 =
                      some ⟨world, 1, .ctorN identity values.toArray⟩ := by
                    simp [allocated, Sim.HeapIso.get?_allocNode_new]
                  simp only [runCode]
                  rw [hoperation]
                  simp only [bind, Except.bind]
                  rw [runOp_pure_eq_fetch_ctor hget harguments hfield]
  | @reuse target identity arguments field rest atom fact hfield hfact
      hscalar =>
      cases fuel with
      | zero => rw [runCode.eq_def, runCode.eq_def]
      | succ outerFuel =>
          cases outerFuel with
          | zero => simp [runCode, runOp]
          | succ operationFuel =>
              cases harguments : resolveAtoms environment arguments with
              | error error =>
                  simp [runCode, runOp, harguments, bind, Except.bind]
              | ok values =>
                  cases htarget : resolveAtom environment target with
                  | error error =>
                      simp [runCode, runOp, harguments, htarget, bind,
                        Except.bind]
                  | ok targetValue =>
                      cases targetValue with
                      | lit literal =>
                          simp [runCode, runOp, harguments, htarget, bind,
                            Except.bind]
                      | erased =>
                          simp [runCode, runOp, harguments, htarget, bind,
                            Except.bind]
                      | loc location =>
                          cases hbox : store.get? location with
                          | none =>
                              simp [runCode, runOp, harguments, htarget, hbox,
                                bind, Except.bind]
                          | some box =>
                              cases hworld : box.world with
                              | shared =>
                                  simp [runCode, runOp, harguments, htarget,
                                    hbox, hworld, bind, Except.bind]
                              | unique =>
                                  let replacement : NodeBox :=
                                    ⟨.unique, 1,
                                      .ctorN identity values.toArray⟩
                                  let updated := store.setBox location replacement
                                  let next : Store :=
                                    { updated with reuses := updated.reuses + 1 }
                                  have hoperation :
                                      runOp ctx (operationFuel + 1) current
                                          store environment
                                          (.reuse target identity arguments) =
                                        .ok (next, .loc location) := by
                                    simp [runOp, harguments, htarget, hbox,
                                      hworld, replacement, updated, next, bind,
                                      Except.bind]
                                  have hset :
                                      (store.setBox location replacement).get?
                                          location = some replacement :=
                                    Sim.get?_setBox_same hbox
                                  have hget : next.get? location =
                                      some ⟨.unique, 1,
                                        .ctorN identity values.toArray⟩ := by
                                    simpa [next, updated, replacement,
                                      Store.get?] using hset
                                  simp only [runCode]
                                  rw [hoperation]
                                  simp only [bind, Except.bind]
                                  rw [runOp_pure_eq_fetch_ctor hget harguments
                                    hfield]

/-- The executable side condition proves that the reused source operand is a
runtime scalar whenever the checked HPT environment and concrete resolution
agree.  This is the ownership justification beyond evaluator equality. -/
theorem source_isScalar_of_forwardHead?_eq_some
    {declarations : DeclEnv} {store : Store} {facts : List Fact}
    {environment : List RVal} {operation : Op} {continuation : Code}
    {forwarding : Forwarding} {value : RVal}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hforward : forwardHead? facts operation continuation = some forwarding)
    (hresolve : resolveAtom environment forwarding.source = .ok value) :
    value.isScalar = true := by
  have hspec := forwardSpec_of_forwardHead?_eq_some hforward
  cases hspec with
  | allocation hfield hfact hscalar =>
      exact scalar_of_scalarOnly_holds hscalar
        (resolveAtom_sound henvironment hfact hresolve)
  | reuse hfield hfact hscalar =>
      exact scalar_of_scalarOnly_holds hscalar
        (resolveAtom_sound henvironment hfact hresolve)

/-! ## Exact recursive traversal -/

@[simp] private theorem runAlternativeWithFacts_cidx
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternative : Alt) :
    (runAlternativeWithFacts declarations summaries owner current
      scrutineeFact peelNat facts alternative).alternative.cidx =
        alternative.cidx := by
  cases alternative
  simp [runAlternativeWithFacts, Alt.cidx]

private theorem runAlternativeWithFacts_predicate
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef)
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
    (owner : Address) (current : FnDef)
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

/-- The branch-body half of fetch forwarding.  HPT case binders are installed
only after the concrete evaluator selects a matching alternative and arity. -/
private theorem runCode_caseWithFactsBodies_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    {owner : Address} {current : FnDef}
    {ctx : Ctx} {store : Store} {facts : List Fact}
    {environment : List RVal} {scrutinee : Atom} {peelNat : Bool}
    {alternatives : Array Alt} {scrutineeFact : Fact} {fuel : Nat}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (habstract : resolveAtomFact facts scrutinee = .ok scrutineeFact)
    (ih : ∀ {store : Store} {facts : List Fact}
      {environment : List RVal} {input : Code},
      EnvironmentHolds declarations store facts environment →
      runCode ctx fuel current store environment
          (runWithFacts declarations summaries owner current facts input).code =
        runCode ctx fuel current store environment input) :
    runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat
          ((alternatives.map
            (runAlternativeWithFacts declarations summaries owner current
              scrutineeFact peelNat facts)).map
                (fun result => result.alternative))) =
      runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  obtain ⟨scrutineeValue, hresolve⟩ :=
    resolveAtom_complete henvironment habstract
  have hscrutineeHolds :=
    resolveAtom_sound henvironment habstract hresolve
  simp only [runCode]
  rw [hresolve]
  simp only [bind, Except.bind]
  cases scrutineeValue with
  | erased => rfl
  | lit literal =>
      cases literal with
      | str value => rfl
      | nat value =>
          simp only
          cases peelNat with
          | false => rfl
          | true =>
              simp only
              cases value with
              | zero =>
                  simp only
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 0) with
                  | none => simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero =>
                              have hzero :
                                  scrutineeFact.caseFields true cidx 0 = [] := by
                                unfold Fact.caseFields
                                split <;> rfl
                              simpa [runAlternativeWithFacts, hzero] using
                                (ih (input := body) henvironment)
                          | succ fields => simp [runAlternativeWithFacts]
              | succ value =>
                  simp only
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 1) with
                  | none => simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero => simp [runAlternativeWithFacts]
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
                                  simpa [runAlternativeWithFacts] using
                                    (ih (input := body)
                                      (hbinders.append henvironment))
                              | succ fields =>
                                  simp [runAlternativeWithFacts]
  | loc location =>
      simp only
      cases hget : store.get? location with
      | none => simp
      | some box =>
          simp only
          cases hnode : box.node with
          | papN function arity arguments => simp
          | ctorN identity fields =>
              simp only
              rw [find?_runAlternativeWithFacts]
              cases hfind : alternatives.find?
                  (fun alternative => alternative.cidx == identity.cidx) with
              | none => simp
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
                        rw [Array.foldl_cons_eq_reverse_append]
                        simpa [hfields, runAlternativeWithFacts] using
                          (ih (input := body)
                            (hbinders.append henvironment))
                      · simp [hfields, runAlternativeWithFacts]

/-- Exact evaluator equality for the owner-sensitive forwarding traversal.
The owner may name the current stored function or be absent from the summary,
which is the fail-closed top-level-main convention. -/
theorem runCode_runWithFacts_eq_ownerCompatible
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    (henvironment : EnvironmentHolds declarations store facts environment) :
    runCode ctx fuel current store environment
        (runWithFacts declarations summaries owner current facts input).code =
      runCode ctx fuel current store environment input := by
  induction fuel generalizing store facts environment input with
  | zero => simp [runCode]
  | succ fuel ih =>
      cases input with
      | ret atom => simp [runWithFacts, runCode]
      | letOp operation rest =>
          cases habstract : analyzeOp declarations summaries owner current
              facts operation with
          | error error => simp [runWithFacts, habstract]
          | ok bound =>
              let nested := runWithFacts declarations summaries owner current
                (bound :: facts.map Fact.forgetHeap) rest
              have hordinary :
                  runCode ctx (fuel + 1) current store environment
                      (.letOp operation nested.code) =
                    runCode ctx (fuel + 1) current store environment
                      (.letOp operation rest) := by
                simp only [runCode]
                cases hoperation : runOp ctx fuel current store environment
                    operation with
                | error error => simp [bind, Except.bind]
                | ok output =>
                    rcases output with ⟨outputStore, outputValue⟩
                    simp only [bind, Except.bind]
                    have hbound := analyzeOp_sound_ownerCompatible hpost hctx
                      howner henvironment habstract hoperation
                    have hold := EnvironmentHolds.forgetHeap
                      (after := outputStore) henvironment
                    simpa [nested] using
                      (ih (store := outputStore)
                        (facts := bound :: facts.map Fact.forgetHeap)
                        (environment := outputValue :: environment)
                        (input := rest) (.cons hbound hold))
              cases hforward : forwardHead? facts operation nested.code with
              | none =>
                  simpa [runWithFacts, habstract, nested, hforward] using
                    hordinary
              | some forwarding =>
                  calc
                    runCode ctx (fuel + 1) current store environment
                        (runWithFacts declarations summaries owner current facts
                          (.letOp operation rest)).code =
                      runCode ctx (fuel + 1) current store environment
                        forwarding.code := by
                          simp [runWithFacts, habstract, nested, hforward]
                    _ = runCode ctx (fuel + 1) current store environment
                          (.letOp operation nested.code) :=
                      runCode_forwardHead?_eq hforward
                    _ = runCode ctx (fuel + 1) current store environment
                          (.letOp operation rest) := hordinary
      | case scrutinee peelNat alternatives =>
          cases habstract : resolveAtomFact facts scrutinee with
          | error error => simp [runWithFacts, habstract]
          | ok scrutineeFact =>
              simpa [runWithFacts, habstract] using
                (runCode_caseWithFactsBodies_eq henvironment habstract
                  (fun henv => ih henv))

/-- Stored-function specialization of exact recursive fetch forwarding. -/
theorem runCode_runWithFacts_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (henvironment : EnvironmentHolds declarations store facts environment) :
    runCode ctx fuel current store environment
        (runWithFacts declarations summaries owner current facts input).code =
      runCode ctx fuel current store environment input :=
  runCode_runWithFacts_eq_ownerCompatible hpost hctx (.inl hcurrent)
    henvironment

end Ix.Compiler.IxIR1.HPT.FetchForward
