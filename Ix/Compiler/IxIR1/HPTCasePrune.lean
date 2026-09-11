import Ix.Compiler.IxIR1.HPTSound

/-!
# Checked HPT consumer: fact-driven case simplification

This is the first transformation that consumes accepted HPT facts.  Its
compatibility entry point `run` has the deliberately small rewrite window

```text
let x := call f(args); case x of alternatives
```

When `f` has a finite heap-only result fact, alternatives whose constructor
index is absent from that fact are removed.  If the accepted fact describes
exactly one unary constructor and filtering leaves exactly its unary branch,
the case is replaced by one checked `fetch`; this preserves both the branch
environment and exact evaluator fuel.  Scalar, unknown-heap, identity-only,
and non-unary rows retain the conservative pruning behavior.  The semantic
theorem below treats the summary as untrusted until it is backed by the same
local post-fixpoint used by the HPT checker.

`runWithFacts` instead mirrors HPT transfer through a complete function body.
It propagates primitive results, forgets older heap identities at the same
mutation boundary as the analyzer, refines case binders, and simplifies every
case from the fact available at that program point.  The function owner is
explicit because `callSelf` transfer is owner-sensitive.

`runRecursive` remains the fixed-environment traversal for supplied fragments
such as a top-level main, which has no declaration owner.  Stored declarations
use `runFunction` and `rewriteDeclarationAt`; changed bodies still require the
separate content-address rebuild stage.
-/

namespace Ix.Compiler.IxIR1.HPT.CasePrune

/-- Only a finite, heap-only row can exclude a case alternative. -/
def preciseHeapOnly (fact : Fact) : Bool :=
  !fact.mayScalar && !fact.unknownHeap

/-- Whether a finite result row contains a constructor with this runtime case
index.  Case dispatch observes `cidx`, not the constructor's block identity. -/
def hasCtorIndex (fact : Fact) (index : Nat) : Bool :=
  fact.shapes.any fun
    | .ctor identity _ => identity.cidx == index
    | .pap _ _ => false

def pruneAlternatives (fact : Fact) (alternatives : Array Alt) : Array Alt :=
  alternatives.filter fun alternative => hasCtorIndex fact alternative.cidx

/-- The detailed singleton constructor fact required for exact unary case
collapse.  Identity-only constructor facts deliberately return `none`: they
do not certify that field zero exists or that the branch arity is one. -/
def exactUnaryConstructor? (fact : Fact) : Option CtorId :=
  match fact.shapes with
  | [.ctor identity (some [_])] => some identity
  | _ => none

/-- Select the sole unary branch body when its dispatch index agrees with the
sole detailed unary constructor fact. -/
def exactUnaryBody? (fact : Fact) (alternatives : Array Alt) : Option Code :=
  match exactUnaryConstructor? fact, alternatives.toList with
  | some identity, [.mk cidx 1 body] =>
      if cidx == identity.cidx then some body else none
  | _, _ => none

private theorem exactUnaryConstructor?_eq_some
    {fact : Fact} {identity : CtorId}
    (h : exactUnaryConstructor? fact = some identity) :
    ∃ fieldFact,
      fact.shapes = [.ctor identity (some [fieldFact])] := by
  unfold exactUnaryConstructor? at h
  split at h <;> simp_all

private theorem exactUnaryBody?_eq_some
    {fact : Fact} {alternatives : Array Alt} {body : Code}
    (h : exactUnaryBody? fact alternatives = some body) :
    ∃ identity fieldFact,
      fact.shapes = [.ctor identity (some [fieldFact])] ∧
        alternatives = #[.mk identity.cidx 1 body] := by
  unfold exactUnaryBody? at h
  split at h <;> simp_all
  obtain ⟨fieldFact, hshapes⟩ :=
    exactUnaryConstructor?_eq_some (by assumption)
  refine ⟨_, ⟨fieldFact, hshapes⟩, Array.toList_inj.mp ?_⟩
  simpa using (by assumption)

/-- Observable output of the one-redex consumer. -/
structure Outcome where
  code : Code
  removedAlternatives : Nat
  collapsedCases : Nat
  materializedFetches : Nat

/-- Pass-attributed counters without the rewritten syntax payload. -/
structure Changes where
  removedAlternatives : Nat := 0
  collapsedCases : Nat := 0
  materializedFetches : Nat := 0

def Changes.add (left right : Changes) : Changes :=
  { removedAlternatives :=
      left.removedAlternatives + right.removedAlternatives
    collapsedCases := left.collapsedCases + right.collapsedCases
    materializedFetches :=
      left.materializedFetches + right.materializedFetches }

def Outcome.changes (outcome : Outcome) : Changes :=
  { removedAlternatives := outcome.removedAlternatives
    collapsedCases := outcome.collapsedCases
    materializedFetches := outcome.materializedFetches }

/-- Simplify one root `call`→`case` redex.  Every other shape is returned
byte-for-byte at the inductive syntax level. -/
def run (declarations : DeclEnv) (summaries : SummaryEnv)
    (input : Code) : Outcome :=
  match input with
  | .letOp (.call function arguments)
      (.case (.var 0) peelNat alternatives) =>
      match declarations function, summaries function with
      | some (.fn _), some fact =>
          if preciseHeapOnly fact then
            let kept := pruneAlternatives fact alternatives
            match exactUnaryBody? fact kept with
            | some body =>
                ⟨.letOp (.call function arguments)
                    (.letOp (.fetch (.var 0) 0) body),
                  alternatives.size - kept.size, 1, 1⟩
            | none =>
                ⟨.letOp (.call function arguments)
                    (.case (.var 0) peelNat kept),
                  alternatives.size - kept.size, 0, 0⟩
          else
            ⟨input, 0, 0, 0⟩
      | _, _ => ⟨input, 0, 0, 0⟩
  | _ => ⟨input, 0, 0, 0⟩

/-- Internal result for recursively rewriting an alternative body while
retaining its dispatch metadata. -/
structure AlternativeOutcome where
  alternative : Alt
  removedAlternatives : Nat
  collapsedCases : Nat
  materializedFetches : Nat

mutual

/-- Recursively apply the one-redex consumer throughout one supplied code
fragment.  This still does not rewrite declaration bodies or the evaluator's
current-function frame. -/
def runRecursive (declarations : DeclEnv) (summaries : SummaryEnv) :
    Code → Outcome
  | .ret atom => ⟨.ret atom, 0, 0, 0⟩
  | .letOp operation rest =>
      let nested := runRecursive declarations summaries rest
      let root := run declarations summaries (.letOp operation nested.code)
      ⟨root.code,
        nested.removedAlternatives + root.removedAlternatives,
        nested.collapsedCases + root.collapsedCases,
        nested.materializedFetches + root.materializedFetches⟩
  | .case scrutinee peelNat alternatives =>
      let nested := alternatives.map
        (runAlternativeRecursive declarations summaries)
      ⟨.case scrutinee peelNat (nested.map (fun result => result.alternative)),
        nested.foldl
          (fun total result => total + result.removedAlternatives) 0,
        nested.foldl
          (fun total result => total + result.collapsedCases) 0,
        nested.foldl
          (fun total result => total + result.materializedFetches) 0⟩

def runAlternativeRecursive (declarations : DeclEnv)
    (summaries : SummaryEnv) : Alt → AlternativeOutcome
  | .mk cidx fields body =>
      let nested := runRecursive declarations summaries body
      ⟨.mk cidx fields nested.code, nested.removedAlternatives,
        nested.collapsedCases, nested.materializedFetches⟩

end

/-! ## Owner-sensitive whole-code fact propagation -/

/-- Simplify one case whose scrutinee fact has already been established by
the ambient HPT environment.  Unlike `run`, this root does not require a
syntactically adjacent call and may fetch from any resolved scrutinee atom. -/
def runKnownCase (fact : Fact) (scrutinee : Atom) (peelNat : Bool)
    (alternatives : Array Alt) : Outcome :=
  let input := Code.case scrutinee peelNat alternatives
  if preciseHeapOnly fact then
    let kept := pruneAlternatives fact alternatives
    match exactUnaryBody? fact kept with
    | some body =>
        ⟨.letOp (.fetch scrutinee 0) body,
          alternatives.size - kept.size, 1, 1⟩
    | none =>
        ⟨.case scrutinee peelNat kept,
          alternatives.size - kept.size, 0, 0⟩
  else
    ⟨input, 0, 0, 0⟩

mutual

/-- Mirror `analyzeCode` while simplifying every case from the fact available
at that exact program point.  Transfer failures are fail-soft: the affected
subtree is returned byte-for-byte with zero attributed changes. -/
def runWithFacts (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef)
    (facts : List Fact) : Code → Outcome
  | .ret atom => ⟨.ret atom, 0, 0, 0⟩
  | input@(.letOp operation rest) =>
      match analyzeOp declarations summaries owner current facts operation with
      | .error _ => ⟨input, 0, 0, 0⟩
      | .ok bound =>
          let nested := runWithFacts declarations summaries owner current
            (bound :: facts.map Fact.forgetHeap) rest
          ⟨.letOp operation nested.code,
            nested.removedAlternatives, nested.collapsedCases,
            nested.materializedFetches⟩
  | input@(.case scrutinee peelNat alternatives) =>
      match resolveAtomFact facts scrutinee with
      | .error _ => ⟨input, 0, 0, 0⟩
      | .ok fact =>
          let nested := alternatives.map
            (runAlternativeWithFacts declarations summaries owner current
              fact peelNat facts)
          let rewritten := nested.map (fun result => result.alternative)
          let root := runKnownCase fact scrutinee peelNat rewritten
          ⟨root.code,
            nested.foldl
                (fun total result => total + result.removedAlternatives) 0 +
              root.removedAlternatives,
            nested.foldl
                (fun total result => total + result.collapsedCases) 0 +
              root.collapsedCases,
            nested.foldl
                (fun total result => total + result.materializedFetches) 0 +
              root.materializedFetches⟩

/-- Rewrite one alternative under the exact HPT binder environment used by
`analyzeAlternatives`. -/
def runAlternativeWithFacts (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Ix.Compiler.Ixon.Address)
    (current : FnDef) (scrutineeFact : Fact) (peelNat : Bool)
    (facts : List Fact) : Alt → AlternativeOutcome
  | .mk cidx fields body =>
      let nested := runWithFacts declarations summaries owner current
        (scrutineeFact.caseFields peelNat cidx fields ++ facts) body
      ⟨.mk cidx fields nested.code, nested.removedAlternatives,
        nested.collapsedCases, nested.materializedFetches⟩

end

/-- Analyze and simplify a complete function from HPT's universal parameter
environment. -/
def runFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef) : Outcome :=
  runWithFacts declarations summaries owner current
    (List.replicate current.arity Fact.top) current.body

/-- Owner-sensitive function rewrite used for stored declarations. -/
def rewriteCurrentAt (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef) : FnDef :=
  { current with body :=
      (runFunction declarations summaries owner current).code }

/-- Owner-sensitive declaration rewrite.  The address is semantically
relevant to `callSelf` transfer. -/
def rewriteDeclarationAt (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) : Decl → Decl
  | .fn function => .fn (rewriteCurrentAt declarations summaries owner function)
  | .extern arity => .extern arity

/-- Rewrite a current-function body while retaining the dynamic arity and
result-world contract used by `callSelf`. -/
def rewriteCurrent (declarations : DeclEnv) (summaries : SummaryEnv)
    (current : FnDef) : FnDef :=
  { current with body :=
      (runRecursive declarations summaries current.body).code }

/-- Rewrite one declaration body without changing its calling convention.
Extern declarations are retained exactly. -/
def rewriteDeclaration (declarations : DeclEnv) (summaries : SummaryEnv) :
    Decl → Decl
  | .fn function => .fn (rewriteCurrent declarations summaries function)
  | .extern arity => .extern arity

/-- Logical declaration environment obtained by rewriting every function
body under its existing key.  This is an intermediate semantic object: a
stored artifact must subsequently readdress the changed declarations. -/
def rewriteDeclEnv (declarations : DeclEnv) (summaries : SummaryEnv) :
    DeclEnv :=
  fun address => (declarations address).map
    (rewriteDeclarationAt declarations summaries address)

/-- Retain a context's oracle while replacing its declaration environment by
the logical body-rewritten environment. -/
def rewriteCtx (declarations : DeclEnv) (summaries : SummaryEnv)
    (ctx : Ctx) : Ctx :=
  { ctx with decls := rewriteDeclEnv declarations summaries }

/-- List form consumed by the content-address rebuild stage. -/
def rewriteEntries (declarations : DeclEnv) (summaries : SummaryEnv)
    (entries : List (Ix.Compiler.Ixon.Address × Decl)) :
    List (Ix.Compiler.Ixon.Address × Decl) :=
  entries.map fun entry =>
    (entry.1,
      rewriteDeclarationAt declarations summaries entry.1 entry.2)

@[simp] theorem declArity_rewriteDeclaration
    (declarations : DeclEnv) (summaries : SummaryEnv) (declaration : Decl) :
    declArity (rewriteDeclaration declarations summaries declaration) =
      declArity declaration := by
  cases declaration <;> rfl

@[simp] theorem declArity_rewriteDeclarationAt
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (declaration : Decl) :
    declArity
        (rewriteDeclarationAt declarations summaries owner declaration) =
      declArity declaration := by
  cases declaration <;> rfl

/-! ## Semantic support -/

/-- A finite fact covering a live constructor necessarily retains its runtime
case index.  Detailed field payloads do not affect dispatch. -/
theorem hasCtorIndex_of_holds_ctor
    {declarations : DeclEnv} {store : Store} {fact : Fact}
    {location : Nat} {box : NodeBox} {identity : CtorId}
    {fields : Array RVal}
    (hfinite : fact.unknownHeap = false)
    (hholds : fact.Holds declarations store (.loc location))
    (hget : store.get? location = some box)
    (hnode : box.node = .ctorN identity fields) :
    hasCtorIndex fact identity.cidx = true := by
  simp only [Fact.Holds] at hholds
  rcases hholds with hunknown | ⟨shape, hmember, hshape⟩
  · rw [hfinite] at hunknown
    contradiction
  · apply List.any_eq_true.mpr
    refine ⟨shape, hmember, ?_⟩
    cases shape with
    | ctor shapeIdentity fieldFacts =>
        simp only [HeapShape.Holds] at hshape
        rcases hshape with
          ⟨shapeBox, shapeFields, hshapeGet, hshapeNode, _⟩
        rw [hget] at hshapeGet
        injection hshapeGet with hbox
        subst shapeBox
        rw [hnode] at hshapeNode
        injection hshapeNode with hidentity
        subst shapeIdentity
        simp
    | pap function supplied =>
        simp only [HeapShape.Holds] at hshape
        rcases hshape with
          ⟨shapeBox, arguments, declaration, hshapeGet, _, hshapeNode, _, _⟩
        rw [hget] at hshapeGet
        injection hshapeGet with hbox
        subst shapeBox
        rw [hnode] at hshapeNode
        contradiction

/-- Filtering by the finite fact preserves the evaluator's first-match lookup
for every constructor index admitted by that fact. -/
theorem find?_pruneAlternatives {fact : Fact} {alternatives : Array Alt}
    {index : Nat} (hindex : hasCtorIndex fact index = true) :
    (pruneAlternatives fact alternatives).find?
        (fun alternative => alternative.cidx == index) =
      alternatives.find? (fun alternative => alternative.cidx == index) := by
  simp only [pruneAlternatives, Array.find?_filter]
  apply congrArg (fun predicate => alternatives.find? predicate)
  funext alternative
  by_cases hsame : alternative.cidx = index
  · subst index
    simp [hindex]
  · simp [hsame]

private theorem mayScalar_eq_false_of_preciseHeapOnly {fact : Fact}
    (hprecise : preciseHeapOnly fact = true) : fact.mayScalar = false := by
  simp [preciseHeapOnly] at hprecise
  exact hprecise.1

private theorem unknownHeap_eq_false_of_preciseHeapOnly {fact : Fact}
    (hprecise : preciseHeapOnly fact = true) : fact.unknownHeap = false := by
  simp [preciseHeapOnly] at hprecise
  exact hprecise.2

/-- A detailed singleton unary result fact exposes one concrete constructor
field.  This is the semantic fact that makes the replacement `fetch` total. -/
private theorem exists_of_exactUnary_holds
    {declarations : DeclEnv} {store : Store} {value : RVal}
    {identity : CtorId} {fieldFact : FieldFact}
    (hholds : (⟨false, false,
      [.ctor identity (some [fieldFact])]⟩ : Fact).Holds
        declarations store value) :
    ∃ location box field,
      value = .loc location ∧
        store.get? location = some box ∧
        box.node = .ctorN identity #[field] := by
  cases value with
  | lit literal =>
      change false = true at hholds
      contradiction
  | erased =>
      change false = true at hholds
      contradiction
  | loc location =>
      simp only [Fact.Holds] at hholds
      rcases hholds with hunknown | ⟨shape, hmember, hshape⟩
      · contradiction
      · simp only [List.mem_singleton] at hmember
        subst shape
        simp only [HeapShape.Holds] at hshape
        rcases hshape with ⟨box, fields, hget, hnode, hfields⟩
        have hlength : fields.toList.length = 1 := by
          simpa using (FieldFactsHold.length_eq hfields).symm
        cases hlist : fields.toList with
        | nil => simp [hlist] at hlength
        | cons field tail =>
            cases tail with
            | nil =>
                have harray : fields = #[field] := by
                  apply Array.toList_inj.mp
                  simpa using hlist
                refine ⟨location, box, field, rfl, hget, ?_⟩
                simpa [harray] using hnode
            | cons next tail => simp [hlist] at hlength

/-- For a certified unary constructor, one checked fetch installs exactly the
environment that the matching case branch would have received, at the same
code fuel. -/
private theorem runCode_fetch_eq_exactUnaryCase_of_holds
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {value : RVal}
    {identity : CtorId} {fieldFact : FieldFact} {body : Code}
    {peelNat : Bool} {fuel : Nat}
    (hholds : (⟨false, false,
      [.ctor identity (some [fieldFact])]⟩ : Fact).Holds
        declarations store value) :
    runCode ctx fuel current store (value :: environment)
        (.letOp (.fetch (.var 0) 0) body) =
      runCode ctx fuel current store (value :: environment)
        (.case (.var 0) peelNat #[.mk identity.cidx 1 body]) := by
  obtain ⟨location, box, field, hvalue, hget, hnode⟩ :=
    exists_of_exactUnary_holds hholds
  subst value
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [runCode, runOp, resolveAtom, Alt.cidx, bind, Except.bind,
            hget, hnode]
      | succ fuel =>
          simp [runCode, runOp, resolveAtom, Alt.cidx, bind, Except.bind,
            hget, hnode]

/-- Successful executable collapse selection supplies exactly the fact and
branch shape required by the concrete unary-fetch theorem. -/
private theorem runCode_fetch_eq_of_exactUnaryBody
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {value : RVal}
    {fact : Fact} {alternatives : Array Alt} {body : Code}
    {peelNat : Bool} {fuel : Nat}
    (hprecise : preciseHeapOnly fact = true)
    (hbody : exactUnaryBody? fact alternatives = some body)
    (hholds : fact.Holds declarations store value) :
    runCode ctx fuel current store (value :: environment)
        (.letOp (.fetch (.var 0) 0) body) =
      runCode ctx fuel current store (value :: environment)
        (.case (.var 0) peelNat alternatives) := by
  obtain ⟨identity, fieldFact, hshapes, halternatives⟩ :=
    exactUnaryBody?_eq_some hbody
  have hscalar := mayScalar_eq_false_of_preciseHeapOnly hprecise
  have hunknown := unknownHeap_eq_false_of_preciseHeapOnly hprecise
  cases fact with
  | mk mayScalar unknownHeap shapes =>
      change mayScalar = false at hscalar
      change unknownHeap = false at hunknown
      change shapes = [.ctor identity (some [fieldFact])] at hshapes
      subst mayScalar
      subst unknownHeap
      subst shapes
      subst alternatives
      exact runCode_fetch_eq_exactUnaryCase_of_holds hholds

/-- Once a concrete call result satisfies a finite heap-only row, pruning does
not change evaluation of the immediately following case. -/
private theorem runCode_case_pruned_eq_of_holds
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {value : RVal}
    {fact : Fact} {peelNat : Bool} {alternatives : Array Alt} {fuel : Nat}
    (hprecise : preciseHeapOnly fact = true)
    (hholds : fact.Holds declarations store value) :
    runCode ctx fuel current store (value :: environment)
        (.case (.var 0) peelNat (pruneAlternatives fact alternatives)) =
      runCode ctx fuel current store (value :: environment)
        (.case (.var 0) peelNat alternatives) := by
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      cases value with
      | lit literal =>
          change fact.mayScalar = true at hholds
          rw [mayScalar_eq_false_of_preciseHeapOnly hprecise] at hholds
          contradiction
      | erased =>
          change fact.mayScalar = true at hholds
          rw [mayScalar_eq_false_of_preciseHeapOnly hprecise] at hholds
          contradiction
      | loc location =>
          cases hget : store.get? location with
          | none =>
              simp [runCode, resolveAtom, bind, Except.bind, hget]
          | some box =>
              cases hnode : box.node with
              | papN function arity arguments =>
                  simp [runCode, resolveAtom, bind, Except.bind, hget, hnode]
              | ctorN identity fields =>
                  have hfind := find?_pruneAlternatives
                    (fact := fact) (alternatives := alternatives)
                    (hasCtorIndex_of_holds_ctor
                      (unknownHeap_eq_false_of_preciseHeapOnly hprecise)
                      hholds hget hnode)
                  simp [runCode, resolveAtom, bind, Except.bind, hget, hnode,
                    hfind]

/-- A successful concrete `.call` operation is covered by the row selected by
the same declaration and summary environments. -/
private theorem holds_of_runOp_call
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current currentFunction : FnDef}
    {store outputStore : Store}
    {environment : List RVal} {function : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {fact : Fact} {outputValue : RVal} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hdeclaration : declarations function = some (.fn currentFunction))
    (hsummary : summaries function = some fact)
    (hcall : runOp ctx fuel current store environment
      (.call function arguments) = .ok (outputStore, outputValue)) :
    fact.Holds declarations outputStore outputValue := by
  cases fuel with
  | zero => simp [runOp] at hcall
  | succ fuel =>
      simp only [runOp] at hcall
      cases harguments : resolveAtoms environment arguments with
      | error error =>
          rw [harguments] at hcall
          simp only [bind, Except.bind] at hcall
          contradiction
      | ok values =>
          have hinvoke : invoke ctx fuel function values store =
              .ok (outputStore, outputValue) := by
            rw [harguments] at hcall
            simpa only [bind, Except.bind] using hcall
          exact invoke_sound hpost hctx
            (by simp [callableResult, hdeclaration, hsummary]) hinvoke

/-- Exact evaluator equality for the single rewritten redex.  The call itself
is untouched; on success, HPT soundness ensures the concrete constructor's
first matching branch survived the filter. -/
private theorem runCode_prunedRedex_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current currentFunction : FnDef} {store : Store}
    {environment : List RVal} {function : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {fact : Fact} {peelNat : Bool}
    {alternatives : Array Alt} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hdeclaration : declarations function = some (.fn currentFunction))
    (hsummary : summaries function = some fact)
    (hprecise : preciseHeapOnly fact = true) :
    runCode ctx fuel current store environment
        (.letOp (.call function arguments)
          (.case (.var 0) peelNat (pruneAlternatives fact alternatives))) =
      runCode ctx fuel current store environment
        (.letOp (.call function arguments)
          (.case (.var 0) peelNat alternatives)) := by
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      simp only [runCode]
      cases hcall : runOp ctx fuel current store environment
          (.call function arguments) with
      | error error =>
          simp [bind, Except.bind]
      | ok output =>
          rcases output with ⟨outputStore, outputValue⟩
          simp only [bind, Except.bind]
          exact runCode_case_pruned_eq_of_holds hprecise
            (holds_of_runOp_call hpost hctx hdeclaration hsummary hcall)

/-- Exact evaluator equality between a selected unary-fetch collapse and its
already-pruned singleton case. -/
private theorem runCode_collapsedRedex_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current currentFunction : FnDef} {store : Store}
    {environment : List RVal} {function : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {fact : Fact} {peelNat : Bool}
    {alternatives : Array Alt} {body : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hdeclaration : declarations function = some (.fn currentFunction))
    (hsummary : summaries function = some fact)
    (hprecise : preciseHeapOnly fact = true)
    (hcollapse : exactUnaryBody? fact alternatives = some body) :
    runCode ctx fuel current store environment
        (.letOp (.call function arguments)
          (.letOp (.fetch (.var 0) 0) body)) =
      runCode ctx fuel current store environment
        (.letOp (.call function arguments)
          (.case (.var 0) peelNat alternatives)) := by
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      simp only [runCode]
      cases hcall : runOp ctx fuel current store environment
          (.call function arguments) with
      | error error =>
          simp [bind, Except.bind]
      | ok output =>
          rcases output with ⟨outputStore, outputValue⟩
          simp only [bind, Except.bind]
          exact runCode_fetch_eq_of_exactUnaryBody hprecise hcollapse
            (holds_of_runOp_call hpost hctx hdeclaration hsummary hcall)

/-- The executable consumer preserves the exact evaluator result for every
fuel, store, environment, and current function whenever its summary
environment is a local post-fixpoint for the runtime declaration environment.
This includes every error result, not only successful executions. -/
theorem runCode_run_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runCode ctx fuel current store environment
        (run declarations summaries input).code =
      runCode ctx fuel current store environment input := by
  cases input with
  | ret atom => rfl
  | case scrutinee peelNat alternatives => rfl
  | letOp operation rest =>
      cases operation <;> try rfl
      case call function arguments =>
        cases rest with
        | ret atom => rfl
        | letOp operation rest => rfl
        | case scrutinee peelNat alternatives =>
            cases scrutinee with
            | lit literal => rfl
            | erased => rfl
            | var index =>
                cases index with
                | succ index => rfl
                | zero =>
                    cases hdeclaration : declarations function with
                    | none => simp [run, hdeclaration]
                    | some declaration =>
                        cases declaration with
                        | extern arity => simp [run, hdeclaration]
                        | fn currentFunction =>
                            cases hsummary : summaries function with
                            | none => simp [run, hdeclaration, hsummary]
                            | some fact =>
                                cases hprecise : preciseHeapOnly fact with
                                | false =>
                                    simp [run, hdeclaration, hsummary, hprecise]
                                | true =>
                                    cases hcollapse : exactUnaryBody? fact
                                        (pruneAlternatives fact alternatives) with
                                    | none =>
                                        simpa [run, hdeclaration, hsummary,
                                          hprecise, hcollapse] using
                                          runCode_prunedRedex_eq hpost hctx
                                            hdeclaration hsummary hprecise
                                    | some body =>
                                        calc
                                          runCode ctx fuel current store
                                              environment
                                              (run declarations summaries
                                                (.letOp
                                                  (.call function arguments)
                                                  (.case (.var 0) peelNat
                                                    alternatives))).code =
                                            runCode ctx fuel current store
                                              environment
                                              (.letOp
                                                (.call function arguments)
                                                (.letOp
                                                  (.fetch (.var 0) 0) body)) := by
                                                    simp [run, hdeclaration,
                                                      hsummary, hprecise,
                                                      hcollapse]
                                          _ = runCode ctx fuel current store
                                                environment
                                                (.letOp
                                                  (.call function arguments)
                                                  (.case (.var 0) peelNat
                                                    (pruneAlternatives fact
                                                      alternatives))) :=
                                            runCode_collapsedRedex_eq hpost hctx
                                              hdeclaration hsummary hprecise
                                              hcollapse
                                          _ = runCode ctx fuel current store
                                                environment
                                                (.letOp
                                                  (.call function arguments)
                                                  (.case (.var 0) peelNat
                                                    alternatives)) :=
                                          runCode_prunedRedex_eq hpost hctx
                                              hdeclaration hsummary hprecise

/-! ## Semantic support for propagated cases -/

/-- A checked fetch from an arbitrary resolved atom installs exactly the
environment of its matching detailed-unary case branch. -/
private theorem runCode_fetchAtom_eq_exactUnaryCase_of_holds
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {scrutinee : Atom}
    {value : RVal} {identity : CtorId} {fieldFact : FieldFact}
    {body : Code} {peelNat : Bool} {fuel : Nat}
    (hresolve : resolveAtom environment scrutinee = .ok value)
    (hholds : (⟨false, false,
      [.ctor identity (some [fieldFact])]⟩ : Fact).Holds
        declarations store value) :
    runCode ctx fuel current store environment
        (.letOp (.fetch scrutinee 0) body) =
      runCode ctx fuel current store environment
        (.case scrutinee peelNat #[.mk identity.cidx 1 body]) := by
  obtain ⟨location, box, field, hvalue, hget, hnode⟩ :=
    exists_of_exactUnary_holds hholds
  subst value
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [runCode, runOp, hresolve, Alt.cidx, bind, Except.bind,
            hget, hnode]
      | succ fuel =>
          simp [runCode, runOp, hresolve, Alt.cidx, bind, Except.bind,
            hget, hnode]

private theorem runCode_fetchAtom_eq_of_exactUnaryBody
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {scrutinee : Atom}
    {value : RVal} {fact : Fact} {alternatives : Array Alt} {body : Code}
    {peelNat : Bool} {fuel : Nat}
    (hresolve : resolveAtom environment scrutinee = .ok value)
    (hprecise : preciseHeapOnly fact = true)
    (hbody : exactUnaryBody? fact alternatives = some body)
    (hholds : fact.Holds declarations store value) :
    runCode ctx fuel current store environment
        (.letOp (.fetch scrutinee 0) body) =
      runCode ctx fuel current store environment
        (.case scrutinee peelNat alternatives) := by
  obtain ⟨identity, fieldFact, hshapes, halternatives⟩ :=
    exactUnaryBody?_eq_some hbody
  have hscalar := mayScalar_eq_false_of_preciseHeapOnly hprecise
  have hunknown := unknownHeap_eq_false_of_preciseHeapOnly hprecise
  cases fact with
  | mk mayScalar unknownHeap shapes =>
      change mayScalar = false at hscalar
      change unknownHeap = false at hunknown
      change shapes = [.ctor identity (some [fieldFact])] at hshapes
      subst mayScalar
      subst unknownHeap
      subst shapes
      subst alternatives
      exact runCode_fetchAtom_eq_exactUnaryCase_of_holds hresolve hholds

/-- Pruning from a fact resolved at an arbitrary program point preserves the
case evaluator, including its first-match behavior and all errors. -/
private theorem runCode_caseAtom_pruned_eq_of_holds
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {environment : List RVal} {scrutinee : Atom}
    {value : RVal} {fact : Fact} {peelNat : Bool}
    {alternatives : Array Alt} {fuel : Nat}
    (hresolve : resolveAtom environment scrutinee = .ok value)
    (hprecise : preciseHeapOnly fact = true)
    (hholds : fact.Holds declarations store value) :
    runCode ctx fuel current store environment
        (.case scrutinee peelNat (pruneAlternatives fact alternatives)) =
      runCode ctx fuel current store environment
        (.case scrutinee peelNat alternatives) := by
  cases fuel with
  | zero => simp [runCode]
  | succ fuel =>
      simp only [runCode]
      rw [hresolve]
      simp only [bind, Except.bind]
      cases value with
      | lit literal =>
          change fact.mayScalar = true at hholds
          rw [mayScalar_eq_false_of_preciseHeapOnly hprecise] at hholds
          contradiction
      | erased =>
          change fact.mayScalar = true at hholds
          rw [mayScalar_eq_false_of_preciseHeapOnly hprecise] at hholds
      | loc location =>
          cases hget : store.get? location with
          | none => simp [hget]
          | some box =>
              cases hnode : box.node with
              | papN function arity arguments => simp [hget, hnode]
              | ctorN identity fields =>
                  have hfind := find?_pruneAlternatives
                    (fact := fact) (alternatives := alternatives)
                    (hasCtorIndex_of_holds_ctor
                      (unknownHeap_eq_false_of_preciseHeapOnly hprecise)
                      hholds hget hnode)
                  simp [hget, hnode, hfind]

/-- The environment-driven case root is exact whenever its abstract
scrutinee resolution is backed by the concrete HPT environment. -/
private theorem runCode_runKnownCase_eq
    {declarations : DeclEnv} {ctx : Ctx} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {fact : Fact} {scrutinee : Atom} {peelNat : Bool}
    {alternatives : Array Alt} {fuel : Nat}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (habstract : resolveAtomFact facts scrutinee = .ok fact) :
    runCode ctx fuel current store environment
        (runKnownCase fact scrutinee peelNat alternatives).code =
      runCode ctx fuel current store environment
        (.case scrutinee peelNat alternatives) := by
  obtain ⟨value, hresolve⟩ := resolveAtom_complete henvironment habstract
  have hholds := resolveAtom_sound henvironment habstract hresolve
  cases hprecise : preciseHeapOnly fact with
  | false => simp [runKnownCase, hprecise]
  | true =>
      cases hcollapse : exactUnaryBody? fact
          (pruneAlternatives fact alternatives) with
      | none =>
          simpa [runKnownCase, hprecise, hcollapse] using
            (runCode_caseAtom_pruned_eq_of_holds hresolve hprecise hholds)
      | some body =>
          calc
            runCode ctx fuel current store environment
                (runKnownCase fact scrutinee peelNat alternatives).code =
              runCode ctx fuel current store environment
                (.letOp (.fetch scrutinee 0) body) := by
                  simp [runKnownCase, hprecise, hcollapse]
            _ = runCode ctx fuel current store environment
                  (.case scrutinee peelNat
                    (pruneAlternatives fact alternatives)) :=
              runCode_fetchAtom_eq_of_exactUnaryBody hresolve hprecise
                hcollapse hholds
            _ = runCode ctx fuel current store environment
                  (.case scrutinee peelNat alternatives) :=
              runCode_caseAtom_pruned_eq_of_holds hresolve hprecise hholds

@[simp] private theorem runAlternativeWithFacts_cidx
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternative : Alt) :
    (runAlternativeWithFacts declarations summaries owner current
      scrutineeFact peelNat facts alternative).alternative.cidx =
        alternative.cidx := by
  cases alternative
  simp [runAlternativeWithFacts, Alt.cidx]

private theorem runAlternativeWithFacts_predicate
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef)
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
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef)
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

private theorem Array.foldl_cons_eq_reverse_append'
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

/-- The alternative-body half of propagated case rewriting.  HPT's branch
facts are installed only after the concrete evaluator has selected a matching
alternative with the expected field count. -/
private theorem runCode_caseWithFactsBodies_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    {owner : Ix.Compiler.Ixon.Address} {current : FnDef}
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
                        rw [Array.foldl_cons_eq_reverse_append']
                        simpa [hfields, runAlternativeWithFacts] using
                          (ih (input := body)
                            (hbinders.append henvironment))
                      · simp [hfields, runAlternativeWithFacts]

/-- Exact evaluator equality for the owner-sensitive HPT traversal.  This is
the reusable semantic boundary for subsequent fact-driven local consumers. -/
theorem runCode_runWithFacts_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ix.Compiler.Ixon.Address} {current : FnDef}
    {store : Store} {facts : List Fact} {environment : List RVal}
    {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
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
              simp only [runWithFacts, habstract, runCode]
              cases hoperation : runOp ctx fuel current store environment
                  operation with
              | error error => simp [bind, Except.bind]
              | ok output =>
                  rcases output with ⟨outputStore, outputValue⟩
                  simp only [bind, Except.bind]
                  have hbound := analyzeOp_sound hpost hctx hcurrent
                    henvironment habstract hoperation
                  have hold := EnvironmentHolds.forgetHeap
                    (after := outputStore) henvironment
                  exact ih (store := outputStore)
                    (facts := bound :: facts.map Fact.forgetHeap)
                    (environment := outputValue :: environment)
                    (input := rest) (.cons hbound hold)
      | case scrutinee peelNat alternatives =>
          cases habstract : resolveAtomFact facts scrutinee with
          | error error => simp [runWithFacts, habstract]
          | ok scrutineeFact =>
              simp only [runWithFacts, habstract]
              calc
                runCode ctx (fuel + 1) current store environment
                    (runKnownCase scrutineeFact scrutinee peelNat
                      ((alternatives.map
                        (runAlternativeWithFacts declarations summaries owner
                          current scrutineeFact peelNat facts)).map
                            (fun result => result.alternative))).code =
                  runCode ctx (fuel + 1) current store environment
                    (.case scrutinee peelNat
                      ((alternatives.map
                        (runAlternativeWithFacts declarations summaries owner
                          current scrutineeFact peelNat facts)).map
                            (fun result => result.alternative))) :=
                  runCode_runKnownCase_eq henvironment habstract
                _ = runCode ctx (fuel + 1) current store environment
                      (.case scrutinee peelNat alternatives) :=
                  runCode_caseWithFactsBodies_eq henvironment habstract
                    (fun henv => ih henv)

/-- Changing one owner-sensitive current body preserves a case step whenever
the two current frames agree at the smaller fuel. -/
private theorem runCode_case_rewriteCurrentAt_eq
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Ix.Compiler.Ixon.Address) (current : FnDef)
    {ctx : Ctx} {fuel : Nat}
    (ih : ∀ {store : Store} {environment : List RVal} {input : Code},
      runCode ctx fuel
          (rewriteCurrentAt declarations summaries owner current)
          store environment input =
        runCode ctx fuel current store environment input)
    (store : Store) (environment : List RVal)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt) :
    runCode ctx (fuel + 1)
        (rewriteCurrentAt declarations summaries owner current)
        store environment (.case scrutinee peelNat alternatives) =
      runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  simp only [runCode]
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error => simp [bind, Except.bind]
  | ok value =>
      simp only [bind, Except.bind]
      cases value with
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
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => exact ih
                              | succ fields => simp
                  | succ value =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp
                              | succ fields =>
                                  cases fields with
                                  | zero => exact ih
                                  | succ fields => simp
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
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == identity.cidx) with
                  | none => simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hfields : fields.size = fieldCount
                          · simpa [hfields] using
                              ih (store := store)
                                (environment := fields.foldl
                                  (fun result field => field :: result)
                                  environment)
                                (input := body)
                          · simp [hfields]

/-- At one positive operation fuel, changing the owner-sensitive current body
is invisible.  `callSelf` uses both the smaller-fuel frame hypothesis and the
proved HPT traversal equality for the rewritten recursive body. -/
private theorem runOp_rewriteCurrentAt_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ix.Compiler.Ixon.Address} {current : FnDef}
    {fuel : Nat}
    (ih : ∀ {store : Store} {environment : List RVal} {input : Code},
      runCode ctx fuel
          (rewriteCurrentAt declarations summaries owner current)
          store environment input =
        runCode ctx fuel current store environment input)
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (store : Store) (environment : List RVal) (operation : Op) :
    runOp ctx (fuel + 1)
        (rewriteCurrentAt declarations summaries owner current)
        store environment operation =
      runOp ctx (fuel + 1) current store environment operation := by
  cases operation <;> try simp [runOp, rewriteCurrentAt]
  case callSelf arguments =>
    cases harguments : resolveAtoms environment arguments with
    | error error => simp [bind, Except.bind]
    | ok values =>
        by_cases harity : values.length = current.arity
        · have henvironment : EnvironmentHolds declarations store
              (List.replicate current.arity Fact.top) values.reverse := by
            simpa [harity] using
              (EnvironmentHolds.top_replicate declarations store
                values.reverse)
          have hbody :
              runCode ctx fuel
                  (rewriteCurrentAt declarations summaries owner current)
                  store values.reverse
                  (rewriteCurrentAt declarations summaries owner current).body =
                runCode ctx fuel current store values.reverse current.body := by
            calc
              runCode ctx fuel
                  (rewriteCurrentAt declarations summaries owner current)
                  store values.reverse
                  (rewriteCurrentAt declarations summaries owner current).body =
                runCode ctx fuel current store values.reverse
                  (rewriteCurrentAt declarations summaries owner current).body :=
                ih
              _ = runCode ctx fuel current store values.reverse current.body := by
                simpa [rewriteCurrentAt, runFunction] using
                  (runCode_runWithFacts_eq hpost hctx hcurrent henvironment)
          simp only [rewriteCurrentAt] at hbody
          simp [harity, bind, Except.bind]
          rw [hbody]
        · simp [harity, bind, Except.bind]

/-- Rewriting a stored function from its owner-aware HPT environment is
observationally irrelevant to arbitrary code executed under that current
frame. -/
theorem runCode_rewriteCurrentAt_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ix.Compiler.Ixon.Address} {current : FnDef}
    {store : Store} {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current)) :
    runCode ctx fuel (rewriteCurrentAt declarations summaries owner current)
        store environment input =
      runCode ctx fuel current store environment input := by
  induction fuel using Nat.strongRecOn generalizing store environment input with
  | ind fuel ih =>
      cases fuel with
      | zero => simp [runCode]
      | succ fuel =>
          have hsmaller : ∀ {store : Store} {environment : List RVal}
              {input : Code},
              runCode ctx fuel
                  (rewriteCurrentAt declarations summaries owner current)
                  store environment input =
                runCode ctx fuel current store environment input :=
            ih fuel (Nat.lt_succ_self fuel)
          cases input with
          | ret atom => simp [runCode]
          | case scrutinee peelNat alternatives =>
              exact runCode_case_rewriteCurrentAt_eq declarations summaries
                owner current hsmaller store environment scrutinee peelNat
                alternatives
          | letOp operation rest =>
              cases fuel with
              | zero => simp [runCode, runOp]
              | succ smaller =>
                  simp only [runCode]
                  rw [runOp_rewriteCurrentAt_eq hpost
                    (ih smaller (by omega)) hctx hcurrent]
                  cases hoperation : runOp ctx (smaller + 1) current store
                      environment operation with
                  | error error => simp [bind, Except.bind]
                  | ok output =>
                      rcases output with ⟨outputStore, outputValue⟩
                      simp only [bind, Except.bind]
                      exact ih (smaller + 1) (by omega)
                        (store := outputStore)
                        (environment := outputValue :: environment)
                        (input := rest)

/-- Combined body-and-current equality used when invocation enters a rewritten
stored function. -/
theorem runCode_rewriteCurrentAt_body_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Ix.Compiler.Ixon.Address} {current : FnDef}
    {store : Store} {environment : List RVal} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (henvironment : EnvironmentHolds declarations store
      (List.replicate current.arity Fact.top) environment) :
    runCode ctx fuel (rewriteCurrentAt declarations summaries owner current)
        store environment
        (rewriteCurrentAt declarations summaries owner current).body =
      runCode ctx fuel current store environment current.body := by
  calc
    runCode ctx fuel (rewriteCurrentAt declarations summaries owner current)
        store environment
        (rewriteCurrentAt declarations summaries owner current).body =
      runCode ctx fuel current store environment
        (rewriteCurrentAt declarations summaries owner current).body :=
      runCode_rewriteCurrentAt_eq hpost hctx hcurrent
    _ = runCode ctx fuel current store environment current.body := by
      simpa [rewriteCurrentAt, runFunction] using
        (runCode_runWithFacts_eq hpost hctx hcurrent henvironment)

@[simp] private theorem runAlternativeRecursive_cidx
    (declarations : DeclEnv) (summaries : SummaryEnv) (alternative : Alt) :
    (runAlternativeRecursive declarations summaries
      alternative).alternative.cidx = alternative.cidx := by
  cases alternative
  simp [runAlternativeRecursive, Alt.cidx]

/-- Recursive body rewriting leaves the case-dispatch predicate unchanged. -/
private theorem runAlternativeRecursive_predicate
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (index : Nat) :
    ((fun alternative : Alt => alternative.cidx == index) ∘
        (fun result : AlternativeOutcome => result.alternative) ∘
        runAlternativeRecursive declarations summaries) =
      (fun alternative => alternative.cidx == index) := by
  funext alternative
  cases alternative
  simp [Function.comp_def, runAlternativeRecursive, Alt.cidx]

/-- Recursive body rewriting preserves first-match dispatch and returns the
rewritten version of the originally selected alternative. -/
private theorem find?_runAlternativeRecursive
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (alternatives : Array Alt) (index : Nat) :
    ((alternatives.map (runAlternativeRecursive declarations summaries)).map
        (fun result => result.alternative)).find?
          (fun alternative => alternative.cidx == index) =
      (alternatives.find? (fun alternative => alternative.cidx == index)).map
        (fun alternative =>
          (runAlternativeRecursive declarations summaries
            alternative).alternative) := by
  rw [Array.map_map, Array.find?_map,
    runAlternativeRecursive_predicate declarations summaries index]
  simp [Function.comp_def]

/-- If every recursively rewritten body is equivalent at the smaller fuel,
then a case whose alternative bodies were all rewritten is equivalent at the
successor fuel. -/
private theorem runCode_recursiveCase_eq
    (declarations : DeclEnv) (summaries : SummaryEnv)
    {ctx : Ctx} {fuel : Nat}
    (ih : ∀ {current : FnDef} {store : Store} {environment : List RVal}
      {input : Code},
      runCode ctx fuel current store environment
          (runRecursive declarations summaries input).code =
        runCode ctx fuel current store environment input)
    (current : FnDef) (store : Store) (environment : List RVal)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt) :
    runCode ctx (fuel + 1) current store environment
        (runRecursive declarations summaries
          (.case scrutinee peelNat alternatives)).code =
      runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  simp only [runRecursive, runCode]
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error =>
      simp [bind, Except.bind]
  | ok value =>
      simp only [bind, Except.bind]
      cases value with
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
                      rw [find?_runAlternativeRecursive]
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none =>
                          simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  simpa [runAlternativeRecursive] using
                                    ih (current := current) (store := store)
                                      (environment := environment) (input := body)
                              | succ fields =>
                                  simp [runAlternativeRecursive]
                  | succ value =>
                      simp only
                      rw [find?_runAlternativeRecursive]
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none =>
                          simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  simp [runAlternativeRecursive]
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      simpa [runAlternativeRecursive] using
                                        ih (current := current) (store := store)
                                          (environment :=
                                            .lit (.nat value) :: environment)
                                          (input := body)
                                  | succ fields =>
                                      simp [runAlternativeRecursive]
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
                  rw [find?_runAlternativeRecursive]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == identity.cidx) with
                  | none =>
                      simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hfields : fields.size = fieldCount
                          · simpa [hfields, runAlternativeRecursive] using
                              ih (current := current) (store := store)
                                (environment := fields.foldl
                                  (fun result field => field :: result)
                                  environment)
                                (input := body)
                          · simp [hfields, runAlternativeRecursive]

/-- Recursive traversal preserves the exact evaluator result for every code
fragment under the same local post-fixpoint premise as the one-root pass. -/
theorem runCode_runRecursive_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runCode ctx fuel current store environment
        (runRecursive declarations summaries input).code =
      runCode ctx fuel current store environment input := by
  induction fuel generalizing current store environment input with
  | zero => simp [runCode]
  | succ fuel ih =>
      cases input with
      | ret atom => simp [runRecursive]
      | case scrutinee peelNat alternatives =>
          exact runCode_recursiveCase_eq declarations summaries ih current
            store environment scrutinee peelNat alternatives
      | letOp operation rest =>
          let nested := runRecursive declarations summaries rest
          calc
            runCode ctx (fuel + 1) current store environment
                (runRecursive declarations summaries
                  (.letOp operation rest)).code =
              runCode ctx (fuel + 1) current store environment
                (.letOp operation nested.code) := by
                  simpa only [runRecursive, nested] using
                    runCode_run_eq hpost (fuel := fuel + 1) hctx
                      (input := .letOp operation nested.code)
            _ = runCode ctx (fuel + 1) current store environment
                (.letOp operation rest) := by
                  simp only [runCode]
                  cases hoperation : runOp ctx fuel current store environment
                      operation with
                  | error error => simp [bind, Except.bind]
                  | ok output =>
                      rcases output with ⟨outputStore, outputValue⟩
                      simp only [bind, Except.bind]
                      exact ih (current := current) (store := outputStore)
                        (environment := outputValue :: environment)
                        (input := rest)

/-- Changing only the current body preserves a case step whenever evaluation
under the two current frames agrees at the smaller fuel. -/
private theorem runCode_case_rewriteCurrent_eq
    (declarations : DeclEnv) (summaries : SummaryEnv)
    {ctx : Ctx} {fuel : Nat}
    (ih : ∀ {current : FnDef} {store : Store} {environment : List RVal}
      {input : Code},
      runCode ctx fuel (rewriteCurrent declarations summaries current)
          store environment input =
        runCode ctx fuel current store environment input)
    (current : FnDef) (store : Store) (environment : List RVal)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt) :
    runCode ctx (fuel + 1) (rewriteCurrent declarations summaries current)
        store environment (.case scrutinee peelNat alternatives) =
      runCode ctx (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  simp only [runCode]
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error => simp [bind, Except.bind]
  | ok value =>
      simp only [bind, Except.bind]
      cases value with
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
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  exact ih (current := current) (store := store)
                                    (environment := environment) (input := body)
                              | succ fields => simp
                  | succ value =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      exact ih (current := current)
                                        (store := store)
                                        (environment :=
                                          .lit (.nat value) :: environment)
                                        (input := body)
                                  | succ fields => simp
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
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == identity.cidx) with
                  | none => simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hfields : fields.size = fieldCount
                          · simpa [hfields] using
                              ih (current := current) (store := store)
                                (environment := fields.foldl
                                  (fun result field => field :: result)
                                  environment)
                                (input := body)
                          · simp [hfields]

/-- At one positive operation fuel, rewriting the current body is invisible.
The only non-definitional case is `callSelf`, whose recursive body execution
is discharged by the smaller-fuel current-frame hypothesis. -/
private theorem runOp_rewriteCurrent_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {fuel : Nat}
    (ih : ∀ {current : FnDef} {store : Store} {environment : List RVal}
      {input : Code},
      runCode ctx fuel (rewriteCurrent declarations summaries current)
          store environment input =
        runCode ctx fuel current store environment input)
    (hctx : ctx.decls = declarations)
    (current : FnDef) (store : Store) (environment : List RVal)
    (operation : Op) :
    runOp ctx (fuel + 1) (rewriteCurrent declarations summaries current)
        store environment operation =
      runOp ctx (fuel + 1) current store environment operation := by
  cases operation <;> try simp [runOp]
  case callSelf arguments =>
    cases harguments : resolveAtoms environment arguments with
    | error error =>
        simp [bind, Except.bind]
    | ok values =>
        by_cases harity : values.length = current.arity
        · have hbody :
              runCode ctx fuel
                  (rewriteCurrent declarations summaries current) store
                  values.reverse
                  (rewriteCurrent declarations summaries current).body =
                runCode ctx fuel current store values.reverse current.body := by
            calc
              runCode ctx fuel
                  (rewriteCurrent declarations summaries current) store
                  values.reverse
                  (rewriteCurrent declarations summaries current).body =
                runCode ctx fuel
                  (rewriteCurrent declarations summaries current) store
                  values.reverse current.body := by
                    simpa only [rewriteCurrent] using
                      runCode_runRecursive_eq hpost (fuel := fuel) hctx
                        (current := rewriteCurrent declarations summaries current)
                        (store := store) (environment := values.reverse)
                        (input := current.body)
              _ = runCode ctx fuel current store values.reverse current.body :=
                ih (current := current) (store := store)
                  (environment := values.reverse) (input := current.body)
          simp only [rewriteCurrent] at hbody
          simp [rewriteCurrent, harity, bind, Except.bind]
          rw [hbody]
        · simp [rewriteCurrent, harity, bind, Except.bind]

/-- Rewriting a current-function body is observationally irrelevant when the
same current frame is used by `callSelf`.  Strong induction supplies the
strictly smaller recursive self-call. -/
theorem runCode_rewriteCurrent_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runCode ctx fuel (rewriteCurrent declarations summaries current)
        store environment input =
      runCode ctx fuel current store environment input := by
  induction fuel using Nat.strongRecOn generalizing current store
      environment input with
  | ind fuel ih =>
      cases fuel with
      | zero => simp [runCode]
      | succ fuel =>
          have hsmaller : ∀ {current : FnDef} {store : Store}
              {environment : List RVal} {input : Code},
              runCode ctx fuel
                  (rewriteCurrent declarations summaries current)
                  store environment input =
                runCode ctx fuel current store environment input :=
            ih fuel (Nat.lt_succ_self fuel)
          cases input with
          | ret atom => simp [runCode]
          | case scrutinee peelNat alternatives =>
              exact runCode_case_rewriteCurrent_eq declarations summaries
                hsmaller current store environment scrutinee peelNat
                alternatives
          | letOp operation rest =>
              cases fuel with
              | zero => simp [runCode, runOp]
              | succ smaller =>
                  simp only [runCode]
                  rw [runOp_rewriteCurrent_eq hpost
                    (ih smaller (by omega)) hctx]
                  cases hoperation : runOp ctx (smaller + 1) current store
                      environment operation with
                  | error error => simp [bind, Except.bind]
                  | ok output =>
                      rcases output with ⟨outputStore, outputValue⟩
                      simp only [bind, Except.bind]
                      exact ih (smaller + 1) (by omega)
                        (current := current) (store := outputStore)
                        (environment := outputValue :: environment)
                        (input := rest)

/-- Recursive pruning can update both a supplied fragment and the current
frame that `callSelf` re-enters. -/
theorem runCode_runRecursive_rewriteCurrent_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runCode ctx fuel (rewriteCurrent declarations summaries current)
        store environment (runRecursive declarations summaries input).code =
      runCode ctx fuel current store environment input := by
  calc
    runCode ctx fuel (rewriteCurrent declarations summaries current)
        store environment (runRecursive declarations summaries input).code =
      runCode ctx fuel (rewriteCurrent declarations summaries current)
        store environment input := runCode_runRecursive_eq hpost hctx
    _ = runCode ctx fuel current store environment input :=
      runCode_rewriteCurrent_eq hpost hctx

/-- Recursive pruning of a top-level main is exact even when `callSelf`
re-enters that main. -/
theorem runMain_runRecursive_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runMain ctx (runRecursive declarations summaries input).code fuel =
      runMain ctx input fuel := by
  simpa [runMain, rewriteCurrent] using
    (runCode_runRecursive_rewriteCurrent_eq hpost
      (current := ⟨0, .shared, false, input⟩) (store := {}) (environment := [])
      (input := input) (fuel := fuel) hctx)

/-- Whole-program certificate specialization of `runCode_run_eq`. -/
theorem runCode_run_eq_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    (hcertificate : certificate.postFixpoint program = true)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runCode ctx fuel current store environment
        (run (programDeclEnv program) certificate.summaryEnv input).code =
      runCode ctx fuel current store environment input := by
  exact runCode_run_eq
    (localPostFixpoint_of_postFixpoint hcertificate) hctx

/-- A successful configurable HPT check is sufficient authority for the
consumer.  The returned materialized summary identities are not trusted as a
substitute for the checked candidate's post-fixpoint evidence. -/
theorem runCode_run_eq_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hcheck : HPT.runWith limits program certificate = .ok result)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runCode ctx fuel current store environment
        (run (programDeclEnv program) certificate.summaryEnv input).code =
      runCode ctx fuel current store environment input := by
  exact runCode_run_eq_of_postFixpoint
    (postFixpoint_of_runWith_eq_ok hcheck) hctx

/-- Whole-program certificate specialization of `runCode_runRecursive_eq`. -/
theorem runCode_runRecursive_eq_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    (hcertificate : certificate.postFixpoint program = true)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runCode ctx fuel current store environment
        (runRecursive (programDeclEnv program) certificate.summaryEnv input).code =
      runCode ctx fuel current store environment input := by
  exact runCode_runRecursive_eq
    (localPostFixpoint_of_postFixpoint hcertificate) hctx

/-- A successful configurable HPT check is sufficient authority for recursive
pruning throughout the supplied code fragment. -/
theorem runCode_runRecursive_eq_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hcheck : HPT.runWith limits program certificate = .ok result)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runCode ctx fuel current store environment
        (runRecursive (programDeclEnv program) certificate.summaryEnv input).code =
      runCode ctx fuel current store environment input := by
  exact runCode_runRecursive_eq_of_postFixpoint
    (postFixpoint_of_runWith_eq_ok hcheck) hctx

/-- Whole-program certificate specialization of the self-call-aware main
theorem.  The declaration environment remains the checked addressed graph. -/
theorem runMain_runRecursive_eq_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    (hcertificate : certificate.postFixpoint program = true)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runMain ctx
        (runRecursive (programDeclEnv program) certificate.summaryEnv
          input).code fuel =
      runMain ctx input fuel := by
  exact runMain_runRecursive_eq
    (localPostFixpoint_of_postFixpoint hcertificate) hctx

/-- Successful configurable checking authorizes recursive main pruning,
including every dynamic re-entry through `callSelf`. -/
theorem runMain_runRecursive_eq_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hcheck : HPT.runWith limits program certificate = .ok result)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runMain ctx
        (runRecursive (programDeclEnv program) certificate.summaryEnv
          input).code fuel =
      runMain ctx input fuel := by
  exact runMain_runRecursive_eq_of_postFixpoint
    (postFixpoint_of_runWith_eq_ok hcheck) hctx

end Ix.Compiler.IxIR1.HPT.CasePrune
