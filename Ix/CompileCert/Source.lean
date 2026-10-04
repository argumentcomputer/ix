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
declines metadata until an explicit erasure/semantic contract is checked. -/
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

end Ix.CompileCert
