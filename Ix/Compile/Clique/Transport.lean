/-
  Ix.Compile.Clique.Transport: the interface of the clique transport `Φ_σ`
  (design document §5), its fallbacks and the causes it records.

  **Input.** One clique as Lean elaborated it: its members in Lean's clique
  order (`EqnInfo.declNames`, or `all` for a theorem clique), every other
  constant of its encoding (the packed function and its abstracted proofs for
  well-founded recursion; the `_f` functionals and the transformed matchers
  for structural recursion; the `mutual` fixpoint and its monotonicity proof
  for `partial_fixpoint`), the permutation `σ` (Lean index ↦ canonical
  position, from Pass 1's clique order), and the canonical name of the packed
  constant (step (R)). Structural recursion also needs the environment, to
  read the `below` dictionaries' definitions.

  **Output.** The transported constants (canonical names), the renaming of
  Lean's encoding constants to canonical ones, and the non-canonical causes:
  * a proof body outside the grammar is kept verbatim under its transported
    statement (§5.1; it proves it by conversion), cause `SHAPE`;
  * a `partial_fixpoint` monotonicity proof outside the grammar takes the
    composition fallback `monotone_compose (mono φ) h` (§5.2), cause `SHAPE`;
  * anything else outside the grammar (the packed function, a statement, a
    member, a functional) leaves the whole clique in Lean's form (the
    baseline, §0.1), cause `SHAPE` on every constant.

  The function is total and pure: no `MetaM`, no kernel, no `partial`.
-/
module
public import Ix.Compile.Clique.WF
public import Ix.Compile.Clique.WFConjugation
public import Ix.Compile.Clique.Structural
public import Ix.Compile.Clique.PartialFixpoint
public import Ix.Compile.Clique.PFConjugation
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs stripMdata)

inductive Encoding where
  | wellFounded
  | structural
  | partialFixpoint
  deriving BEq, Repr, Inhabited

structure Input where
  encoding : Encoding
  /-- the clique's members, in Lean's clique order -/
  members : Array Decl
  /-- every other constant of the encoding -/
  aux : Array Decl
  /-- Lean index ↦ canonical position -/
  sigma : Array Nat
  /-- the canonical name of the packed constant (`f₀._mutual` ↦ this) -/
  newEncName : Name
  /-- the environment (structural recursion reads `below`) -/
  const? : Name → Option ConstantInfo := fun _ => none
  /-- equation lemmas carried with the clique (A5 proper), each with its
  output name: the members' own lemmas keep their names; the packed
  function's `eq_def` is regenerated under the canonical name, retaining its
  source-domain indexing through the decoded input adapter (`WFConjugation.lean`) -/
  lemmas : Array (Decl × Name) := #[]

structure Output where
  decls : Array Decl
  /-- Lean's encoding constant ↦ its canonical name -/
  renames : Array (Name × Name)
  /-- constant (canonical name), cause, reason -/
  causes : Array (Name × Cause × String)
  /-- the clique was left in Lean's form -/
  baseline : Bool := false
  log : Array String := #[]

/-- The packed function of a well-founded clique: the constant every member
applies. -/
def findPacked? (members : Array Decl) (aux : Array Decl) : Option Decl := do
  let m ← members[0]?
  let (_, body) := peelLams (lamArity m.value) m.value #[]
  let (h, _) := getAppFnArgs (stripMdata body)
  let (_, base) := projChain h
  let (h, _, _) ← constApp? (if (projChain h).1.isEmpty then body else base)
  aux.find? (·.name == h)

/-- The baseline: Lean's constants unchanged, every one recorded. -/
def Output.baselineOf (inp : Input) (why : String) : Output :=
  let decls := inp.aux ++ inp.members
  { decls, renames := #[], baseline := true
    causes := decls.map fun d => (d.name, .shape, why) }

/-- Transport a clique (`Φ_σ`), or leave it in Lean's form. -/
def transport (inp : Input) : Output :=
  if inp.sigma.size != inp.members.size || !isPerm inp.sigma then
    .baselineOf inp "transport: bad permutation (expected one distinct position for every member)"
  else if (List.range inp.sigma.size).all (fun i => inp.sigma[i]! == i) then
    -- identity: nothing moves
    { decls := inp.aux ++ inp.members, renames := #[], causes := #[] }
  else
  match inp.encoding with
  | .wellFounded =>
    match findPacked? inp.members inp.aux with
    | none => .baselineOf inp "no packed function"
    | some packed =>
      let proofs := inp.aux.filter fun d => d.name != packed.name
      match (transportWF inp.members packed proofs inp.sigma inp.newEncName inp.lemmas inp.const?).run {} with
      | .error e => .baselineOf inp e
      | .ok (out, st) =>
        { decls := out.decls.map (·.decl), renames := out.renames, log := st.log
          causes := out.decls.filterMap fun t => t.fallback.map fun why => (t.decl.name, .shape, why) }
  | .structural =>
    match (transportStructural inp.members inp.aux inp.sigma inp.const? inp.lemmas).run {} with
    | .error e => .baselineOf inp e
    | .ok (out, st) =>
      { decls := out.map (·.decl), renames := #[], log := st.log
        causes := out.filterMap fun t => t.fallback.map fun why => (t.decl.name, .shape, why) }
  | .partialFixpoint =>
    match findPacked? inp.members inp.aux with
    | none => .baselineOf inp "no packed fixpoint"
    | some packed =>
      let proofs := inp.aux.filter fun d => d.name != packed.name
      match (transportPF inp.members packed proofs inp.sigma inp.newEncName inp.const? inp.lemmas).run {} with
      | .error e => .baselineOf inp e
      | .ok (out, st) =>
        { decls := out.decls.map (·.decl), renames := out.renames, log := st.log
          causes := out.decls.filterMap fun t => t.fallback.map fun why => (t.decl.name, .shape, why) }

end Ix.Compile.Clique

end
