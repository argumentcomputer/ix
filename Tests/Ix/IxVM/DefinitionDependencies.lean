import Tests.Ix.IxVM.Exploits

/-!
  Definition dependency tests for IxVM (`Tests.Ix.IxVM.DefinitionDependencies`).
-/

namespace Tests.Ix.IxVM.DefinitionDependencies

open LSpec Exploits

/-- `∀ P : Prop, P` has no closed inhabitant; no axiom is needed for this exploit. -/
private def everyProp : Ixon.Expr := .leanAll (.sort 0) (.var 0)

private def identityType : Ixon.Expr :=
  .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))

private def identityValue : Ixon.Expr :=
  .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))

private def definition (kind : Ix.DefKind) (ty value : Ixon.Expr) : Ixon.Definition :=
  ⟨kind, .safe, 0, ty, value⟩

private def block (definitions : Array Ixon.Definition)
    (sharing : Array Ixon.Expr := #[]) : Ixon.Env × Address := Id.run do
  let (source, address) := storeAt {}
    ⟨.muts (definitions.map .defn), sharing, #[], #[.zero]⟩
  let mut source := source
  let mut first := address
  for i in [:definitions.size] do
    let (updated, projection) := storeAt source
      ⟨.dPrj ⟨i.toUInt64, address⟩, #[], #[], #[]⟩
    source := { updated with anonHints := updated.anonHints.insert projection (.regular 0) }
    if i == 0 then first := projection
  return (source, first)

private def asCase (name intent : String) (fixture : Ixon.Env × Address)
    (accept : Bool := false) : ExploitCase :=
  { name, intent, env := fixture.1
    claim := .check (Ix.ClaimContext.ofDefaultTable.toOption.getD default) fixture.2 none
    expectAccept := accept }

/-- Hand-authored, hash-bound Ixon environments for the Rust soundness fix.
IxVM already rejects circular safe definitions by denying relative peer slots.
Only the rejection cases are shared with IxVM: accepting valid forward peer
references would require a separate completeness change to that kernel. -/
def cases : Array ExploitCase := Id.run do
  let mut result := #[]
  for (label, kind) in [("definition", Ix.DefKind.defn), ("theorem", .thm), ("opaque", .opaq)] do
    result := result.push (asCase s!"axiom-free-self-{label}"
      "prove every proposition by citing the declaration itself"
      (storeAt {} ⟨.defn (definition kind everyProp (.recur 0 #[])), #[], #[], #[.zero]⟩))
    result := result.push (asCase s!"mutual-self-{label}"
      "hide the same false proof in a one-member mutual block"
      (block #[definition kind everyProp (.recur 0 #[])]))
  result := result.push (asCase "mutual-two-member-cycle"
    "two declarations justify each other's proof of every proposition"
    (block #[definition .thm everyProp (.recur 1 #[]),
      definition .opaq everyProp (.recur 0 #[])]))
  result := result.push (asCase "mutual-cycle-in-let-initializer"
    "a let initializer hides a circular proof even when the body ignores it"
    (block #[definition .thm identityType
      (.leanLet true everyProp (.recur 1 #[]) identityValue),
      definition .thm everyProp (.recur 1 #[])]))
  result := result.push (asCase "mutual-cycle-through-sharing"
    "sharing must not hide an edge of a declaration cycle"
    (block #[definition .thm everyProp (.share 0),
      definition .opaq everyProp (.recur 0 #[])] #[.recur 1 #[]]))
  result := result.push (asCase "mutual-cycle-in-type"
    "a declaration type must not depend on its own definition"
    (block #[definition .defn (.recur 0 #[]) identityValue]))
  result := result.push (asCase "control-acyclic-forward-definition"
    "a forward reference to a genuine identity proof is valid"
    (block #[definition .thm identityType (.recur 1 #[]),
      definition .defn identityType identityValue]) true)
  result := result.push (asCase "control-acyclic-forward-type"
    "declaration types may depend on a later acyclic type alias"
    (block #[definition .thm (.recur 1 #[]) identityValue,
      definition .defn (.sort 0) identityType]) true)
  result := result.push (asCase "control-acyclic-shared-diamond"
    "shared live references are traversed, but unused sharing creates no dependency"
    (block #[definition .thm identityType (.share 0),
      definition .opaq identityType (.share 0),
      definition .defn identityType identityValue] #[.recur 2 #[]]) true)
  return result

/-- IxVM classifies theorems as logical regardless of the safety byte, and
opaque declarations as logical unless explicitly unsafe. Mutual ingress must
use that effective classification too, as standalone ingress already does. -/
private def ixvmSafetyCases : Array ExploitCase :=
  #[("theorem-unsafe", Ix.DefKind.thm, Ix.DefinitionSafety.unsaf),
    ("theorem-partial", .thm, .part), ("opaque-partial", .opaq, .part)].map
    fun (label, kind, safety) =>
      asCase s!"mutual-self-{label}"
        "the wire safety byte must not bypass the safe declaration peer-slot restriction"
        (block #[{ definition kind everyProp (.recur 0 #[]) with safety }])

def run : IO UInt32 := do
  let control := asCase "control-closed-identity"
    "a genuine closed proof must still be accepted"
    (storeAt {} ⟨.defn (definition .thm identityType identityValue), #[], #[], #[.zero]⟩) true
  let ixvmCases := cases.filter (fun c => !c.expectAccept) ++ ixvmSafetyCases ++ #[control]
  Tests.Ix.IxVM.runCases "ixvm-definition-dependencies" (ixvmCases.map fun c _ => c.toCase)

end Tests.Ix.IxVM.DefinitionDependencies
