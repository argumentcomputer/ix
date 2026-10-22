import Aiur.Modules.Check
import Aiur.Generic.Runtime

namespace Aiur.Modules

/-- Declarative global-name resolution. Local binders are handled separately by
the capture-avoiding structural rebinding in `reexpr`. -/
inductive NameDenotes (p : Program α) (owner : Ref) (bindings : Bindings) : String → Ref → String → Prop where
  | local (spelling : splitPath path = [member]) :
      NameDenotes p owner bindings path owner (rename owner.symbol member)
  | qualified (spelling : splitPath path = [ref.symbol, member])
      (resolved : Denotes p bindings ref target) :
      NameDenotes p owner bindings path target (rename target.symbol member)

structure ResolvedName (p : Program α) (owner : Ref) (bindings : Bindings)
    (instances : List Ref) (path : String) where
  target : Ref
  name : String
  denotes : NameDenotes p owner bindings path target name
  closed : instances.contains target = true

def resolveName (p : Program α) (owner : Ref) (bindings : Bindings) (instances : List Ref)
    (path : String) : Except String (ResolvedName p owner bindings instances path) := do
  match spelling : splitPath path with
  | [member] =>
      if closed : instances.contains owner = true then
        return ⟨owner, rename owner.symbol member, .local spelling, closed⟩
      else throw "local module is absent from the declaration environment"
  | [head, member] =>
      let ref ← parseRef 128 head
      if canonical : ref.symbol = head then
        let target ← resolve p bindings 128 ref
        if closed : instances.contains target.value = true then
          return ⟨target.value, rename target.value.symbol member,
            .qualified (by simpa [canonical] using spelling) target.valid, closed⟩
        else throw s!"unlinked dependency '{target.value.symbol}'"
      else throw "module paths must use canonical identifier syntax"
  | _ => throw s!"expected a module-qualified member, got '{path}'"

/-- A certified substitution for global identifiers, independent of the module
collector's cache and traversal order. -/
structure Relocation (p : Program α) (owner : Ref) (bindings : Bindings) (instances : List Ref) where
  lookup : Access → String → Except String String
  valid : ∀ access path name, lookup access path = .ok name →
    ∃ target, NameDenotes p owner bindings path target name ∧ instances.contains target = true

def relocation (p : Program α) (owner : Ref) (bindings : Bindings) (instances : List Ref) :
    Relocation p owner bindings instances where
  lookup := fun _ path => (resolveName p owner bindings instances path).map (·.name)
  valid := by
    intro access path name success
    cases h : resolveName p owner bindings instances path with
    | error e => simp [h, Except.map] at success
    | ok result =>
        simp only [h, Except.map, Except.ok.injEq] at success
        subst name
        exact ⟨result.target, result.denotes, result.closed⟩

/-- One environment fragment is exactly an original module body under a
certified name substitution. This specification mentions neither `collect`
nor `checkTemplates`, and contains no interface placeholder bodies. -/
structure Fragment (p : Program α) (instances : List Ref) where
  key : Ref
  decl : Module α
  definitions : Definitions α
  found : p.findModule? key.name = some decl
  body : decl.body = .definitions definitions
  arity : decl.parameters.length = key.args.length
  names : Relocation p key ((decl.parameters.map Prod.fst).zip key.args) instances
  program : Generic.Program α
  relocated : rewrite key.symbol names.lookup definitions.program = .ok program

def linkFragment (p : Program α) (instances : List Ref) (key : Ref) :
    Except String { fragment : Fragment p instances // fragment.key = key } := do
  match found : p.findModule? key.name with
  | none => throw s!"unknown module '{key.name}'"
  | some decl =>
      match body : decl.body with
      | .alias _ => throw "aliases must resolve to definitions before linking"
      | .definitions definitions =>
          if arity : decl.parameters.length = key.args.length then
            let names := relocation p key ((decl.parameters.map Prod.fst).zip key.args) instances
            match h : rewrite key.symbol names.lookup definitions.program with
            | .error e => throw e
            | .ok program => return ⟨⟨key,decl,definitions,found,body,arity,names,program,h⟩,rfl⟩
          else throw "unbound module parameters during linking"

structure Fragments (p : Program α) (instances keys : List Ref) where
  values : List (Fragment p instances)
  covers : values.map (·.key) = keys

def linkFragments (p : Program α) (instances : List Ref) :
    (keys : List Ref) → Except String (Fragments p instances keys)
  | [] => return ⟨[],rfl⟩
  | key :: keys => do
      let head ← linkFragment p instances key
      let tail ← linkFragments p instances keys
      return ⟨head.val :: tail.values, by simp [head.property, tail.covers]⟩

def combine {p : Program α} {instances : List Ref} (fragments : List (Fragment p instances)) : Generic.Program α :=
  fragments.foldl (fun program fragment => append program fragment.program) {functions := []}

/-- Static semantics of a linked declaration environment. Every definition
comes from a source module, rebinding is valid, and all module dependencies are
present. Extra unreachable instances are harmless and may remain. -/
structure Assembly (p : Program α) where
  instances : List Ref
  fragments : Fragments p instances instances
  program : Generic.Program α
  assembled : combine fragments.values = program

def assemble (p : Program α) (world : World α) : Except String (Assembly p) := do
  let instances := (world.items.filter (·.target.isNone)).map (·.key)
  let fragments ← linkFragments p instances instances
  return ⟨instances,fragments,combine fragments.values,rfl⟩

/-- Expose the useful source-to-environment fact without referring to a
particular elaboration implementation. -/
theorem Assembly.fragment_origin (a : Assembly p) (f : Fragment p a.instances)
    (_present : f ∈ a.fragments.values) :
    p.findModule? f.key.name = some f.decl ∧
    f.decl.body = .definitions f.definitions ∧
    rewrite f.key.symbol f.names.lookup f.definitions.program = .ok f.program :=
  ⟨f.found,f.body,f.relocated⟩

theorem combine_functions {p : Program α} {instances : List Ref}
    (fragments : List (Fragment p instances)) :
    (combine fragments).functions = fragments.flatMap (·.program.functions) := by
  have aux : ∀ initial : Generic.Program α,
      (fragments.foldl (fun program fragment => append program fragment.program) initial).functions =
        initial.functions ++ fragments.flatMap (·.program.functions) := by
    induction fragments with
    | nil => intro initial; simp
    | cons head tail ih =>
        intro initial
        rw [List.foldl_cons, ih]
        simp [append, List.append_assoc]
  simpa [combine] using aux {functions := []}

/-- Linking cannot invent a function: each member of the resulting environment
belongs to a certified rebinding of an original module body. -/
theorem Assembly.function_origin (a : Assembly p) (present : f ∈ a.program.functions) :
    ∃ fragment ∈ a.fragments.values,
      f ∈ fragment.program.functions ∧
      p.findModule? fragment.key.name = some fragment.decl ∧
      fragment.decl.body = .definitions fragment.definitions := by
  rw [← a.assembled, combine_functions] at present
  obtain ⟨fragment, member, present⟩ := List.mem_flatMap.mp present
  exact ⟨fragment,member,present,fragment.found,fragment.body⟩

structure Selection (p : Program α) (instances : List Ref) where
  external : String
  resolved : ResolvedName p (.mk "" []) [] instances external

/-- The semantic context is an independently specified assembly plus the
existing checked native source. Module syntax adds no expression-evaluation rules. -/
structure Environment (p : Program F) [DecidableEq F] where
  assembly : Assembly p
  source : Generic.Source F
  checked : Generic.prepare assembly.program = .ok source

structure Prepared (p : Program F) [DecidableEq F] where
  environment : Environment p
  selections : List (Selection p environment.assembly.instances)

def prepare [DecidableEq F] (p : Program F) (entries : List String) : Except String (Prepared p) := do
  checkTemplates p
  let (world,_) ← collect p entries
  checkWorld p world
  entries.forM (checkEntryInputs p world)
  let assembly ← assemble p world
  match checked : Generic.prepare assembly.program with
  | .error e => throw e
  | .ok source =>
      let selections ← entries.mapM fun external => do
        let resolved ← resolveName p (.mk "" []) [] assembly.instances external
        source.checkEntry resolved.name
        return {external,resolved : Selection p assembly.instances}
      return ⟨⟨assembly,source,checked⟩, selections⟩

def Prepared.entries [DecidableEq F] (p : Prepared (program : Program F)) : List String :=
  p.selections.map (·.resolved.name)

def Prepared.find? [DecidableEq F] (p : Prepared (program : Program F)) (name : String) :=
  p.selections.find? (·.external == name)

def Prepared.run [Field F] [DecidableEq F] (p : Prepared (program : Program F)) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : p.environment.source.HintProvider := Generic.SourceSemantics.unavailable) :
    Except String (SourceValue F × Heap F) := do
  let some entry := p.find? name | throw s!"unselected entrypoint '{name}'"
  p.environment.source.run entry.resolved.name args fuel hints

def Prepared.EvalCall [Field F] [DecidableEq F] (p : Prepared (program : Program F))
    (name : String) (args : List (SourceValue F)) (value : SourceValue F) : Prop :=
  ∃ entry, p.find? name = some entry ∧ p.environment.source.EvalCall entry.resolved.name args value

theorem Prepared.run_spec [Field F] [DecidableEq F] {p : Prepared (program : Program F)}
    {hints : p.environment.source.HintProvider}
    (executed : p.run name args fuel hints = .ok (value, heap)) : p.EvalCall name args value := by
  cases selected : p.find? name with
  | none => simp [Prepared.run,selected] at executed
  | some entry =>
      simp only [Prepared.run,selected] at executed
      obtain ⟨checked,evaluated⟩ := Generic.Source.run_spec executed
      exact ⟨entry,selected,checked,heap,evaluated⟩

end Aiur.Modules
