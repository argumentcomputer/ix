import Ix.Cert.ChangedCone
import Ix.Cert.SourceReverse
import Ix.LeanIngress.Rename
import Ix.Compile.ConeCheck
import Ix.Resource.Typing

/-! # The changed-cone validator

`coneValidator` is a `ConeValidator` (`Ix.Cert.ChangedCone`): from a compile's
input, artifact and changed set, it reads off what the validation hypotheses
name (`planOf`) and checks it with the runtime check (`Ix.Compile.ConeCheck`):

* **the roots**, over the whole input: every changed entry the artifact
  publishes and every published clique row of a clique entry (as the selector
  `SelectedRoots` enumerates them), and the cascade: every published constant
  outside the set from which a changed constant is reached along the closure
  relation and the ground edges between role-keyed names (`groundAffected`: the
  reverse index `SourceReverse.build` with the ground edges reversed, walked
  once from the changed names). Every closure's roots are among them, so each
  root is checked once per artifact, whatever the closure;
* **the image computation-rule rows**: for every image head of the set that is a
  recursor of the input, the row `r._ix.rule.i` of each of its rules. A required
  row the artifact does not publish refuses the compile (`ChangeKind.Present`);
* **acceptance**: the compiled closure of all roots and rows (over references,
  owners, and the ground, literal and recursor edges), in one run of the certified
  entry;
* **Source forms**: for every root whose terms the compiler rewrote (callers,
  image heads, regenerated auxiliaries), its own compiled closure is checked, and
  in the environment that installs, the terms of its quotient Source declaration,
  renamed to the artifact's addresses, must infer at full grade. The declaration
  is read from the preparation of the root's own closure (`closure env [n]`);
  when Source does not prepare that closure, there is nothing to infer. -/

namespace Ix.Cert.ConeValidator

open Ix.Compile.ChangedSet (ChangedSet Cause)
open Ix.Compile

/-- **The image computation-rule rows a compile requires**: for every image head
of the changed set that is a recursor of the input, the row of each of its rules,
with the address the artifact publishes it at (none when it does not). -/
def imageRuleRows (env : Ix.Environment) (ixe : Ixon.Env) (cs : ChangedSet) :
    Array (Ix.Name × Nat × Option Address) :=
  cs.entries.foldl (init := #[]) fun acc e =>
    if e.cause = .imageHead then
      match env.consts.get? e.name with
      | some (.recInfo rv) =>
        (List.range rv.rules.size).foldl (init := acc) fun acc i =>
          acc.push (e.name, i, (ixe.named.get? (imageRuleRowName e.name i)).map (·.addr))
      | _ => acc
    else acc

/-- The causes whose records carry rewritten terms (`ChangeKind.rewritesTerms`,
read through `ChangeKind.reason?`). -/
def rewrites : Cause → Bool
  | .caller | .imageHead | .regenerated => true
  | _ => false

/-- The role quotient Source keys a name as, at the role table `t`, under the
artifact's alias fibers `ρ` (`quotientKey`, with the fiber map computed once). -/
def roleKeyOf (ρ : Ix.LeanIngress.FiberMap) (n : Ix.Name) : Option Ix.Kernel.Role :=
  match Ix.LeanIngress.Key.subst ρ (Ix.LeanIngress.ingressKey n) with
  | .role r => some r
  | _ => none

/-- **The ground edges among names, reversed**: from every input name keyed as a
role `s` to every name keyed as a role whose install reads `s` (`groundRoles`).
`targets` are the input's names (a ground edge ends at a constant of the closure);
`sources` are every name a walk can reach, missing dependencies included. -/
def groundReverse (ρ : Ix.LeanIngress.FiberMap) (targets sources : Array Ix.Name) :
    SourceReverse.Index :=
  let byRole (names : Array Ix.Name) : Std.HashMap Ix.Kernel.Role (Array Ix.Name) :=
    names.foldl (init := {}) fun m n =>
      match roleKeyOf ρ n with
      | some r => m.insert r ((m.getD r #[]).push n)
      | none => m
  let ys := byRole targets
  let xs := byRole sources
  Ix.Kernel.Role.all.foldl (init := {}) fun m r =>
    (ConeCheck.groundRoles r).foldl (init := m) fun m s =>
      (ys.getD s #[]).foldl (init := m) fun m y => m.insert y ((m.getD y #[]) ++ xs.getD r #[])

/-- The union of two reverse indexes. -/
def mergeIndex (a b : SourceReverse.Index) : SourceReverse.Index :=
  b.fold (init := a) fun m k vs => m.insert k ((m.getD k #[]) ++ vs)

/-- **The names from which a changed name is reached** along the closure relation
and the ground edges, at the role table `t`. -/
def groundAffected (env : Ix.Environment) (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (cs : ChangedSet) : Std.HashSet Ix.Name :=
  let index := SourceReverse.build env
  let ρ := Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t)
  let names := env.consts.keys.toArray
  let reached := index.fold (init := names) fun acc k _ => acc.push k
  (SourceReverse.walk (mergeIndex index (groundReverse ρ names reached)) cs.names).seen

/-- **The roots over the whole input**: the selector's direct roots and published
clique rows, and the ground-aware cascade. -/
def rootsOf (input : ConeInput) (t : Ix.Kernel.RoleTable) : List SelectedRoots.Root :=
  let cs := input.changed
  let affected := groundAffected input.env input.ixe t cs
  SelectedRoots.directRoots cs input.env input.ixe ++
    (input.env.consts.toList.filterMap fun (n, _) =>
      if cs.contains n = false ∧ affected.contains n = true then
        (SelectedRoots.published? input.env input.ixe n).map fun a => ⟨n, a, .cascade⟩
      else none) ++ SelectedRoots.rowRoots cs input.env input.ixe

/-- **What the validator checks** on a compile (see the module docstring). -/
def planOf (input : ConeInput) (t : Ix.Kernel.RoleTable) : ConeCheck.Plan :=
  let roots := rootsOf input t
  let rows := imageRuleRows input.env input.ixe input.changed
  { seeds := (roots.map (·.address)).toArray ++ rows.filterMap (·.2.2)
    missingRows := rows.filterMap fun (h, i, a?) => if a?.isNone then some (h, i) else none
    rewritten := (SelectedRoots.directRoots input.changed input.env input.ixe).toArray.filterMap
      fun r => match r.reason with
        | .direct c => if rewrites c then some (r.source, r.address) else none
        | _ => none }

/-- **The Source terms of a rewritten root** `n`: quotient Source's preparation of
`n`'s own closure, at the role table `t`, the prelude `pre`, the bundle `b` and the
artifact's per-fiber hints; the terms (`sourceFormTerms`) of every prepared
declaration that declares `n`'s quotient key, renamed to the artifact's addresses.
`none` when Source does not prepare the closure. -/
def sourceTerms (env : Ix.Environment) (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (pre : Ix.Kernel.Reader.Prelude .source) (b : Ix.RoleEvidence.Bundle)
    (hints : Std.HashMap (Ix.Kernel.Key .source) Ix.Kernel.ReducibilityHint) (n : Ix.Name) :
    Except String (Option (List (Ix.Kernel.Expr .anon))) :=
  let sub := closure env [n]
  match Ix.LeanIngress.prepareSourceCollapsedAt ixe t (hints[·]?) pre sub (blocksOf sub) with
  | .error _ => .ok none
  | .ok ds => .ok (some ((ds.toList.filter fun d => decide (quotientKey ixe t n ∈ declKeys d)).flatMap
      fun d => sourceFormTerms (d.mapKeys (Ix.LeanIngress.evAddr ixe b))))

/-- The validator's check of a compile, with what it did. -/
def checkWith (mode : ConeCheck.Mode) (limits : Ix.Kernel.Admission.Limits) (input : ConeInput) :
    Except String ConeCheck.Stats := do
  let s ← ConeCheck.defaultSetting input.ixe limits
  let t ← Ix.Kernel.Reader.defaultTable
  let pre ← Ix.Kernel.Reader.builtinPrelude
  let b ← Ix.RoleEvidence.committedBundle ()
  let hints := Ix.LeanIngress.fiberHintsMap input.ixe
  ConeCheck.runWithStats s mode (planOf input t) (sourceTerms input.env input.ixe t pre b hints)
    input.ixe

/-- The validator at a check mode and batch limits. -/
def validatorWith (mode : ConeCheck.Mode) (limits : Ix.Kernel.Admission.Limits) : ConeValidator :=
  fun input => (checkWith mode limits input).map fun _ => ()

/-- **The changed-cone validator**: the roots' acceptance in one run, at the typing
limits. -/
def coneValidator : ConeValidator := validatorWith .union Ix.Resource.typingLimits

end Ix.Cert.ConeValidator
