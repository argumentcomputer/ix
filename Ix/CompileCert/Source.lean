import Lean.Environment

/-! # Finite source snapshots for compiler certification

The host supplies this snapshot. Certification binds to these complete
`ConstantInfo` values; it does not certify which external modules the host
loaded. Dependency extraction is independent of compiler closure discovery.
Proof and opaque bodies are included in checking dependencies even though
their values are not computational unfolding equations.
-/

namespace Ix.CompileCert

/-- A finite, immutable source inventory. Duplicate names are invalid, even
when their values happen to agree. No reverse target-address lookup occurs. -/
structure Source where
  declarations : List Lean.ConstantInfo

def Source.names (s : Source) : List Lean.Name :=
  s.declarations.map Lean.ConstantInfo.name

def Source.find (s : Source) (n : Lean.Name) : Option Lean.ConstantInfo :=
  s.declarations.find? (fun c => c.name == n)

/-- Syntactic references, including projection structure names. Metadata
payloads are deliberately not interpreted here: translation separately
erases metadata (`exportExpr`'s erasure contract), so its references count. -/
def exprRefs : Lean.Expr → List Lean.Name
  | .const n _ => [n]
  | .app f a => exprRefs f ++ exprRefs a
  | .lam _ t b _ | .forallE _ t b _ => exprRefs t ++ exprRefs b
  | .letE _ t v b _ => exprRefs t ++ exprRefs v ++ exprRefs b
  | .mdata _ b => exprRefs b
  | .proj n _ b => n :: exprRefs b
  | .lit (.natVal _) => [`Nat, `Nat.zero, `Nat.succ]
  | .lit (.strVal _) => [`String, `String.ofList, `List, `List.nil, `List.cons, `Char, `Char.ofNat]
  | _ => []

/-- Full checking and declaration-unit support. Recursor rules and source
mutual membership are obligations, not facts inferred from target aliases. -/
def declarationRefs (c : Lean.ConstantInfo) : List Lean.Name :=
  exprRefs c.type ++ match c with
  | .defnInfo v => v.all ++ exprRefs v.value
  | .thmInfo v => v.all ++ exprRefs v.value
  | .opaqueInfo v => v.all ++ exprRefs v.value
  | .inductInfo v => v.all ++ v.ctors ++ v.all.map (·.str "rec") ++
      (List.range v.numNested).filterMap (fun i => v.all.head?.map (·.str s!"rec_{i + 1}"))
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all ++ v.all.map (·.str "rec") ++
      (List.range (v.numMotives - v.all.length)).filterMap
        (fun i => v.all.head?.map (·.str s!"rec_{i + 1}")) ++
      v.rules.flatMap (fun r => r.ctor :: exprRefs r.rhs)
  | _ => []

/-- Closed finite source inventory. Cycles are allowed: this is a finite
closure predicate, not a scheduler DAG or a termination argument. -/
def CompleteSource (s : Source) (roots : List Lean.Name) : Prop :=
  s.names.Nodup ∧ (∀ n ∈ roots, n ∈ s.names) ∧
    ∀ c ∈ s.declarations, ∀ n ∈ declarationRefs c, n ∈ s.names

instance (s : Source) (roots : List Lean.Name) : Decidable (CompleteSource s roots) :=
  inferInstanceAs (Decidable (s.names.Nodup ∧
    (∀ n ∈ roots, n ∈ s.names) ∧
    ∀ c ∈ s.declarations, ∀ n ∈ declarationRefs c, n ∈ s.names))

def checkCompleteSource (s : Source) (roots : List Lean.Name) : Bool :=
  decide (CompleteSource s roots)

theorem checkCompleteSource_sound {s : Source} {roots : List Lean.Name}
    (h : checkCompleteSource s roots = true) : CompleteSource s roots :=
  of_decide_eq_true h

/-- Keep exact source values, in supplied source order. This does not copy
declarations out of a target environment or reconstruct them from names. -/
def Source.restrict (ambient : Source) (names : List Lean.Name) : Source :=
  ⟨ambient.declarations.filter (fun ci => names.contains ci.name)⟩

/-- One monotone closure step. An unrelated unsupported ambient declaration
is never inspected for dependencies. Missing names remain in the set and
are subsequently diagnosed by the closed-source check. -/
def sourceClosureStep (ambient : Source) (names : List Lean.Name) : List Lean.Name :=
  (names ++ (ambient.restrict names).declarations.flatMap declarationRefs).eraseDups

/-- Finite executable construction; success is checked independently below.
The explicit round budget bounds execution, not the eventual L4 domain. -/
def sourceClosure (ambient : Source) : Nat → List Lean.Name → List Lean.Name
  | 0, names => names
  | fuel + 1, names =>
    let next := sourceClosureStep ambient names
    if next == names then names else sourceClosure ambient fuel next

structure SelectedSource (ambient : Source) (roots : List Lean.Name) where
  names : List Lean.Name
  source : Source
  exact : source = ambient.restrict names
  complete : CompleteSource source roots

/-- Construct a root-selected closed cone, retaining the exact ambient
source declarations. Source cycles are permitted. An inadequate explicit
budget declines rather than claiming completeness. -/
def selectSource (ambient : Source) (roots : List Lean.Name)
    (rounds : Nat := ambient.declarations.length + 1) :
    Except String (SelectedSource ambient roots) :=
  let names := sourceClosure ambient rounds roots.eraseDups
  let selected := ambient.restrict names
  if h : CompleteSource selected roots then .ok ⟨names, selected, rfl, h⟩
  else .error "source cone is incomplete, has duplicate keys, or exhausted closure rounds"

/-- Successful selection contains original declarations, never synthesized
or guessed substitutes. This conclusion is independent of source typing. -/
theorem SelectedSource.original {ambient : Source} {roots : List Lean.Name}
    (selected : SelectedSource ambient roots) {ci : Lean.ConstantInfo}
    (h : ci ∈ selected.source.declarations) : ci ∈ ambient.declarations := by
  rw [selected.exact] at h
  exact (List.mem_filter.mp h).1

/-- Exact source capture from a supplied lookup operation. Equality here is
the dependent match's proof, never a cached hash or a BEq comparison between
two `ConstantInfo` values. With `find := env.find?` this binds to that supplied
Lean environment; it does not attest which external module files were loaded. -/
structure CapturedSource (find : Lean.Name → Option Lean.ConstantInfo) where
  source : Source
  faithful : ∀ ci ∈ source.declarations, find ci.name = some ci

def captureNames (find : Lean.Name → Option Lean.ConstantInfo) :
    List Lean.Name → Except String (CapturedSource find)
  | [] => .ok ⟨⟨[]⟩, by simp⟩
  | name :: names =>
    match hf : find name with
    | none => .error s!"source declaration is missing: {name}"
    | some ci =>
      if hn : ci.name = name then do
        let tail ← captureNames find names
        return ⟨⟨ci :: tail.source.declarations⟩, by
          intro c hc
          rcases List.mem_cons.mp hc with he | ht
          · subst c
            simpa only [hn] using hf
          · exact tail.faithful c ht⟩
      else .error s!"source lookup returned a declaration with a different name: {name}"

structure ClosedCapture (find : Lean.Name → Option Lean.ConstantInfo) (roots : List Lean.Name)
    extends CapturedSource find where
  complete : CompleteSource source roots

/-- Independent forward discovery from actual source lookups. It never
enumerates unrelated ambient declarations. The returned proof states both
closure and exact lookup provenance of every retained complete declaration. -/
def captureCone (find : Lean.Name → Option Lean.ConstantInfo) (roots : List Lean.Name)
    (rounds : Nat) : Except String (ClosedCapture find roots) :=
  loop rounds roots
where
  loop : Nat → List Lean.Name → Except String (ClosedCapture find roots)
    | fuel, names => do
      let captured ← captureNames find names.eraseDups
      if h : CompleteSource captured.source roots then return ⟨captured, h⟩
      match fuel with
      | 0 => throw "source closure discovery exhausted its explicit round budget"
      | fuel + 1 =>
        loop fuel (names ++ captured.source.declarations.flatMap declarationRefs)

/-- Original structure-like projection metadata. Mutual/nested membership
is retained in `owner`; this predicate does not require non-recursion or
non-nesting, and it never consults a target declaration. -/
def SourceProjectionShape (owner : Lean.InductiveVal) (ctor : Lean.ConstructorVal)
    (field : Nat) : Prop :=
  owner.ctors = [ctor.name] ∧ owner.numIndices = 0 ∧ ctor.induct = owner.name ∧
    ctor.cidx = 0 ∧ ctor.numParams = owner.numParams ∧ field < ctor.numFields

instance (owner : Lean.InductiveVal) (ctor : Lean.ConstructorVal) (field : Nat) :
    Decidable (SourceProjectionShape owner ctor field) :=
  inferInstanceAs (Decidable (owner.ctors = [ctor.name] ∧ owner.numIndices = 0 ∧
    ctor.induct = owner.name ∧ ctor.cidx = 0 ∧ ctor.numParams = owner.numParams ∧ field < ctor.numFields))

structure SourceProjectionSite (source : Source) where
  ownerName : Lean.Name
  ctorName : Lean.Name
  owner : Lean.InductiveVal
  ctor : Lean.ConstructorVal
  field : Nat
  owner_original : source.find ownerName = some (.inductInfo owner)
  ctor_original : source.find ctorName = some (.ctorInfo ctor)
  shape : SourceProjectionShape owner ctor field

def sourceProjectionSite (source : Source) (ownerName : Lean.Name) (field : Nat) :
    Except String (SourceProjectionSite source) :=
  match ho : source.find ownerName with
  | some (.inductInfo owner) =>
    match owner.ctors with
    | [ctorName] =>
      match hc : source.find ctorName with
      | some (.ctorInfo ctor) =>
        if shape : SourceProjectionShape owner ctor field then
          .ok ⟨ownerName, ctorName, owner, ctor, field, ho, hc, shape⟩
        else .error "source projection constructor ownership, arity or field position is invalid"
      | _ => .error "source projection constructor is missing"
    | _ => .error "source projection owner does not have exactly one constructor"
  | _ => .error "source projection owner is not an original inductive"

/-- The constructor computation specified by the original source metadata:
parameters precede fields, and a projection selects field `i`, not argument
`i` of the full constructor spine. An incomplete/overapplied spine declines.
This is the source computation interface; it is not the target checker's
`.proj` capability test or a theorem about arbitrary raw `Denotes`. -/
def sourceProjectionField {source : Source} (site : SourceProjectionSite source)
    (arguments : List Lean.Expr) : Option Lean.Expr :=
  if arguments.length = site.owner.numParams + site.ctor.numFields then
    arguments[site.owner.numParams + site.field]?
  else none

theorem sourceProjectionField_constructor {source : Source} (site : SourceProjectionSite source)
    (params fields : List Lean.Expr) (parameterCount : params.length = site.owner.numParams)
    (fieldCount : fields.length = site.ctor.numFields) :
    sourceProjectionField site (params ++ fields) = fields[site.field]? := by
  simp only [sourceProjectionField, List.length_append, parameterCount, fieldCount, ↓reduceIte]
  rw [List.getElem?_append_right (by omega)]
  simp [parameterCount]

def sourceApps : Lean.Expr → List Lean.Expr → Lean.Expr
  | head, [] => head
  | head, arg :: args => sourceApps (.app head arg) args

def sourceAppSpine : Lean.Expr → Lean.Expr × List Lean.Expr
  | .app f a =>
    let (head, args) := sourceAppSpine f
    (head, args ++ [a])
  | e => (e, [])

theorem sourceAppSpine_apps (head : Lean.Expr) (args : List Lean.Expr) :
    sourceAppSpine (sourceApps head args) =
      ((sourceAppSpine head).1, (sourceAppSpine head).2 ++ args) := by
  induction args generalizing head with
  | nil => simp [sourceApps]
  | cons arg args ih => simp [sourceApps, ih, sourceAppSpine, List.append_assoc]

/-- The source projection computation is checked against original owner
and constructor records. Structural expression traversal ignores cached
hashes and does not ask either compiler or target checker to reduce it. -/
def sourceProjectionCompute (source : Source) (expression : Lean.Expr) : Except String Lean.Expr := do
  let .proj owner field operand := expression | throw "not a source projection"
  let site ← sourceProjectionSite source owner field
  let (.const ctor _, arguments) := sourceAppSpine operand
    | throw "source projection operand is not a constructor application"
  unless ctor == site.ctorName do throw "source projection uses a different constructor"
  let some value := sourceProjectionField site arguments
    | throw "source projection constructor spine has the wrong arity"
  return value

theorem sourceProjectionCompute_constructor {source : Source} {owner : Lean.Name} {field : Nat}
    {site : SourceProjectionSite source}
    (metadata : sourceProjectionSite source owner field = .ok site)
    (levels : List Lean.Level) (params fields : List Lean.Expr)
    (parameterCount : params.length = site.owner.numParams)
    (fieldCount : fields.length = site.ctor.numFields) {value : Lean.Expr}
    (selected : fields[site.field]? = some value) :
    sourceProjectionCompute source
      (.proj owner field (sourceApps (.const site.ctorName levels) (params ++ fields))) = .ok value := by
  have computed := sourceProjectionField_constructor site params fields parameterCount fieldCount
  simp [sourceProjectionCompute, metadata, sourceAppSpine_apps, sourceAppSpine,
    bind, Except.bind, pure, Except.pure, computed, selected]

/-- Exact raw source syntax eligible for a projection-function proposal.
The caller checks the number of leading binders against the original owner.
Metadata, lets, applications and non-major operands are not erased here. -/
def sourceProjectionBody : Lean.Expr → Option (Lean.Name × Nat × Nat)
  | .lam _ _ body _ => do
    let (owner, field, binders) ← sourceProjectionBody body
    return (owner, field, binders + 1)
  | .proj owner field (.bvar 0) => some (owner, field, 0)
  | _ => none

end Ix.CompileCert
