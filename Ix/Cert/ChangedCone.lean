import Ix.Cert.SelectedRoots
import Ix.Cert.StrongCommutation
import Ix.LeanIngress.Rename

/-! # The changed cone: change kinds, their validation hypotheses and the validator

`compile` publishes most constants as a renaming of their Source form: the
record at a constant's address is the compile of its Lean declaration, with
every reference read at the address the artifact publishes for it. Quotient
Source (`SourceAcceptsQ`) absorbs the renamings that are not one-to-one: alias
fibers that span Source's groups, canonical universes and the merged hints of a
fiber. Everything else the compiler does to a constant is a **change**, and the
changed set of a compile (`Ix.Compile.ChangedSet.ofCompile`) names every input
constant it applies to, with a typed cause.

This module gives the final statement (`Ix.Cert.CompileCorrect`) its
validation hypotheses, one per kind of change, and the interface of the
validator that discharges them on each compile:

* `ChangeKind`: every rewrite the compiler performs, by the records it
  produces; `CallRewrite`: the rewrites of one call site inside a rewritten
  record (the occurrence passes and the baseline);
* `KindRoot`: the records of a kind in a closure, read off the changed set
  (`Ix.Cert.SelectedRoots`: the direct causes, the published clique rows and
  the cascade), and the required image computation-rule rows;
* `KindAccepted`: each such record is accepted at the reference level with
  its own compiled closure (and, for image rule rows, each required row is
  published);
* `SourceFormInfers`: for each record whose terms the compiler rewrote, the
  Source form of its declaration, renamed to the artifact's addresses, infers
  in that same compiled closure. This is what lets a conversion argument turn
  into a value equality (the semantic conclusion of a conversion needs both
  sides graded);
* `ConeValidator`: what the validator receives and what its success must
  assert (`ConeValidator.Sound`).

Acceptance is checked on the changed records and their cones. Value
preservation is not: the static proofs per kind carry it (the call-site
rewrites, the transported cliques through their rows, the images through their
rule rows, which the checker verifies per artifact). -/

namespace Ix.Cert

open Ix.Kernel (Env)
open Ix.Kernel.Admission (Binding)
open Ix.Compile.ChangedSet (ChangedSet Cause)
open Ix.Cert.SelectedRoots (Root Reason ClassifiedRoot)

/-! ## Change kinds -/

/-- **A rewrite of one call site** of an image head (`Ix.Compile.Pass.Translate`,
with the occurrence engine `Ix.Compile.Pass.Opt.engine`). A full application of
an image-kind auxiliary of a changed block is either developed from the image
or rewritten by the first occurrence pass that applies, in the engine's order
O11a, O2, O3, O4, O6. A bare or partial occurrence keeps the Lean name, which
the artifact publishes as the image, so it is no rewrite. The artifact does not
record which rewrite fired at an occurrence, so these are not record kinds:
the record that contains the call site is a `ChangeKind.callSite` record (or an
`image` record, for a Lean auxiliary over images), and the rewrite of each of
its call sites is one of these. -/
inductive CallRewrite where
  /-- The baseline: the image's body at the arguments, developed by hereditary
  substitution (β, projection of a constructor, η; never ι). -/
  | inline
  /-- O11a: the `sizeOf` instance's projection (`Ix.Compile.Pass.Opt.O11a`). -/
  | o11a
  /-- O2: recursive minors relocated, with recursive calls rewritten again
  (`Ix.Compile.Pass.Opt.O2`). -/
  | o2
  /-- O3 (`Ix.Compile.Pass.Opt.O3`). -/
  | o3
  /-- O4: the `below`/`brecOn` family (`Ix.Compile.Pass.Opt.O4`). -/
  | o4
  /-- O6: the canonical recursor with permuted motives and minors
  (`Ix.Compile.Pass.Opt.O6`). -/
  | o6
  deriving DecidableEq, Repr

/-- Every call-site rewrite. -/
def CallRewrite.all : List CallRewrite := [.inline, .o11a, .o2, .o3, .o4, .o6]

theorem CallRewrite.mem_all (r : CallRewrite) : r ∈ CallRewrite.all := by
  cases r <;> simp [CallRewrite.all]

/-- The rewrite the occurrence engine names (`Ix.Compile.Pass.Opt.engineN`'s
first component). -/
def CallRewrite.ofEngine? : String → Option CallRewrite
  | "O11a" => some .o11a
  | "O2" => some .o2
  | "O3" => some .o3
  | "O4" => some .o4
  | "O6" => some .o6
  | _ => none

/-- **The kinds of compiled records that are not a renaming of their Source
form**, by the stage that makes them. Together they cover every rewrite the
compiler performs; the rewrites of single call sites are `CallRewrite`s inside
`callSite` and `image` records. -/
inductive ChangeKind where
  /-- The canonical form of a component differs from Lean's: an inductive
  component split, collapsed, permuted, or with a nested auxiliary moved or
  evaporated (`Ix.Compile.ChangedSet.BlockCause`), a Lean-generated
  `IndPredBelow` family stored in another order, or a definition component two
  of whose members share a class. Its members and their constructors. -/
  | block
  /-- A regenerated auxiliary whose published record is not the compile of
  Lean's own form (the driver's byte verdict, `Ix.AuxGen.AuxTable.identical`). -/
  | regenerated
  /-- An image-kind auxiliary of a Lean block with a changed component
  (`Ix.Compile.Pass.imageKinds`), published as its image: a recursor's generated
  image over the canonical recursors, or Lean's own `casesOn`, `recOn`, `below`,
  `brecOn` value with its call sites rewritten. -/
  | image
  /-- The row of one computation rule of an image of a Lean recursor
  (`imageRuleRowName`): the rule's equation, which the checker verifies on the
  artifact, standing in for a static simulation of the image. -/
  | imageRule
  /-- A constant whose call sites of image heads are rewritten (one
  `CallRewrite` per occurrence), with the other members of its block; and a
  member of a block that references a clique's encoding constant. -/
  | callSite
  /-- A member of an input clique, or an equation lemma carried with one: its
  value may be transported over the clique's canonical constants. -/
  | clique
  /-- The equation row of a transported clique member
  (`Ix.Compile.Pass.Clique.rowName`): Lean's value, over faithful copies of the
  encoding, equals the member. -/
  | cliqueRow
  /-- A constant outside the changed set whose closure meets it: compiled as a
  renaming of its Source form, against changed records. -/
  | cascade
  deriving DecidableEq, Repr

/-- Every change kind. -/
def ChangeKind.all : List ChangeKind :=
  [.block, .regenerated, .image, .imageRule, .callSite, .clique, .cliqueRow, .cascade]

theorem ChangeKind.mem_all (k : ChangeKind) : k ∈ ChangeKind.all := by
  cases k <;> simp [ChangeKind.all]

/-- The root reason of the changed set's selector (`Ix.Cert.SelectedRoots`) for a
kind; none for image rule rows, which the selector does not enumerate. -/
def ChangeKind.reason? : ChangeKind → Option Reason
  | .block => some (.direct .member)
  | .regenerated => some (.direct .regenerated)
  | .image => some (.direct .imageHead)
  | .imageRule => none
  | .callSite => some (.direct .caller)
  | .clique => some (.direct .clique)
  | .cliqueRow => some .row
  | .cascade => some .cascade

/-- The kinds whose records carry rewritten terms (a type or a definition's
value that is not the renamed Source term), so that their Source form must infer
in the compiled closure (`SourceFormInfers`). A transported clique member's value
is related to its Source value by its row instead, and the other kinds keep
their Source terms up to renaming. -/
def ChangeKind.rewritesTerms : ChangeKind → Bool
  | .regenerated | .image | .callSite => true
  | _ => false

/-! ## The records of a kind -/

/-- **The changed set of a compile**: `Ix.Compile.ChangedSet.ofCompile` at the
compile's own condensation and aux table. -/
def changedSetOf (env : Ix.Environment) (ixe : Ixon.Env) : ChangedSet :=
  Ix.Compile.ChangedSet.ofCompile env (compileBlocks env) (compileTable env) ixe

/-- The reserved name of the row of computation rule `i` of the image of the Lean
recursor `r`: `r._ix.rule.i`. -/
def imageRuleRowName (r : Ix.Name) (i : Nat) : Ix.Name :=
  Ix.Compile.Pass.appendComps r [.s Ix.Compile.Pass.ixComponent, .s "rule", .n i]

/-- **A required image rule row**: `head` is an image head of the changed set, a
recursor of the closure `sub` with a computation rule `i`. -/
def ImageRuleRequired (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (head : Ix.Name) (i : Nat) : Prop :=
  ∃ e ∈ (changedSetOf env ixe).entries, e.cause = .imageHead ∧ e.name = head ∧
    ∃ rv, sub.consts.get? head = some (.recInfo rv) ∧ i < rv.rules.size

/-- **The records of kind `k` in the closure `sub`**: the published address `a` of
the name `n`, for
* a kind the selector enumerates, a root of that reason (`ClassifiedRoot`): an
  entry of the changed set with that cause, a published clique row of a clique
  entry, or a constant of `sub` outside the set whose closure meets it;
* image rule rows, the published row of a required rule. -/
def KindRoot (k : ChangeKind) (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (n : Ix.Name) (a : Address) : Prop :=
  match k.reason? with
  | some reason => ClassifiedRoot env (changedSetOf env ixe) sub ixe ⟨n, a, reason⟩
  | none => ∃ head i, ImageRuleRequired env ixe sub head i ∧ n = imageRuleRowName head i ∧
      ∃ named, ixe.named.get? n = some named ∧ named.addr = a

/-- **The record at `a` is accepted with its compiled closure**, at the reference
level, under the role table `binding`. -/
def RootAccepted (binding : Binding) (ixe : Ixon.Env) (a : Address) : Prop :=
  ∃ limits order envA, IxonAcceptsRef binding limits ixe (· = a) order envA

/-- What a kind requires to be published: every required image rule row; nothing
for the other kinds, whose records are the changed set's own. -/
def ChangeKind.Present (k : ChangeKind) (env : Ix.Environment) (ixe : Ixon.Env)
    (sub : Ix.Environment) : Prop :=
  match k with
  | .imageRule => ∀ head i, ImageRuleRequired env ixe sub head i →
      ∃ named, ixe.named.get? (imageRuleRowName head i) = some named
  | _ => True

/-- **The validation hypothesis of kind `k`** for the closure `sub`: what the kind
requires is published, and under the default role table every record of the kind
is accepted, at the reference level, with its own compiled closure. -/
def KindAccepted (k : ChangeKind) (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment) :
    Prop :=
  k.Present env ixe sub ∧
    ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
      ∀ n a, KindRoot k env ixe sub n a → RootAccepted binding ixe a

/-! ## Source forms -/

/-- **The quotient key of an input name**: its ingress key, renamed onto its
alias fiber's representative under the table rule (`Ix.LeanIngress.fiberAliasAt`
at the table `t`'s inverse), as quotient Source keys it. -/
def quotientKey (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (n : Ix.Name) : Ix.Kernel.Key .source :=
  Ix.LeanIngress.Key.subst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
    (Ix.LeanIngress.ingressKey n)

/-- The keys a declaration installs. -/
def declKeys {md : Ix.Kernel.Mode} : Ix.Kernel.Declaration md → List (Ix.Kernel.Key md)
  | .axiomDecl v | .defnDecl v _ _ | .thmDecl v _ | .opaqueDecl v _ | .quotDecl _ v => [v.name]
  | .basisDecl _ => []
  | .indDecl block _ => block.map (·.name)

/-- **The terms of a declaration a value model reads**: every type it installs, and
a definition's value. A theorem's or opaque's value is not one (a value model
records no value for them). -/
def sourceFormTerms {md : Ix.Kernel.Mode} : Ix.Kernel.Declaration md → List (Ix.Kernel.Expr md)
  | .axiomDecl v | .thmDecl v _ | .opaqueDecl v _ | .quotDecl _ v => [v.type]
  | .defnDecl v e _ => [v.type, e]
  | .basisDecl _ => []
  | .indDecl block _ => block.map (·.toConstantVal.type)

/-- **Source forms infer in the compiled closure.** For the closure `sub` at the
role table `t`, take quotient Source's prepared stream (the one `SourceAcceptsQ`
checks) and the committed bundle. Then every record of a kind whose terms the
compiler rewrote (`ChangeKind.rewritesTerms`) is accepted with its compiled
closure, and in the environment that installs, every term of its Source
declaration (`sourceFormTerms` of the declaration of its quotient key), renamed
to the artifact's addresses by IxC's renaming (`Ix.LeanIngress.evAddr`), infers at
full grade.

The renamed Source form is what the static proof of each rewrite converts to the
compiled term. The semantic conclusion of a conversion needs both sides graded,
which inference at full grade supplies; the compiled side's comes from its
acceptance. -/
def SourceFormInfers (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (t : Ix.Kernel.RoleTable) : Prop :=
  ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
    ∀ pre ds b, Ix.Kernel.Reader.builtinPrelude = .ok pre →
      Ix.RoleEvidence.committedBundle () = .ok b →
      Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
        (blocksOf sub) = .ok ds →
      ∀ k n a, k.rewritesTerms = true → KindRoot k env ixe sub n a →
        ∃ limits order envA, IxonAcceptsRef binding limits ixe (· = a) order envA ∧
          ∀ d ∈ ds, quotientKey ixe t n ∈ declKeys d →
            ∀ e ∈ sourceFormTerms (d.mapKeys (Ix.LeanIngress.evAddr ixe b)),
              ∃ F type, Ix.Kernel.inferTypeCore .verified envA F 0 e = .ok type

/-! ## The changed-cone validator -/

/-- **What the changed-cone validator receives**: the compiler's input, the
result `compileReport` returned for it (the artifact and its failures) and the
changed set of that result. -/
structure ConeInput where
  env : Ix.Environment
  ixe : Ixon.Env
  failures : Failures
  changed : ChangedSet

/-- The validator's input for a compile: its changed set is `changedSetOf`. -/
def coneInput (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) : ConeInput :=
  ⟨env, ixe, failures, changedSetOf env ixe⟩

/-- **A changed-cone validator**: a check over a compile's result, which fails
with a message or passes. -/
abbrev ConeValidator := ConeInput → Except String Unit

/-- **What the validator's success asserts.** On every result `compileReport`
returns that the validator passes, for every closure `sub` of the input and the
default role table `t`:
* `block`, `regenerated`, `image`, `callSite`, `clique`: every changed record of
  the closure, accepted with its compiled closure;
* `imageRule`: every required image rule row published, and accepted with its
  compiled closure;
* `cliqueRow`: every published row of a clique member of the closure, accepted;
* `cascade`: every constant of the closure whose closure meets the changed set,
  accepted with its compiled closure;
* and for the `regenerated`, `image` and `callSite` records, their Source forms
  infer in their compiled closures (`SourceFormInfers`).

A validator checks the whole artifact once; each closure's hypotheses are its
records' share. -/
def ConeValidator.Sound (v : ConeValidator) : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures),
    compileReport env = .ok (ixe, failures) → v (coneInput env ixe failures) = .ok () →
    ∀ (roots : List Ix.Name) (sub : Ix.Environment) (t : Ix.Kernel.RoleTable),
      IsClosure env roots sub → Ix.Kernel.Reader.defaultTable = .ok t →
      (∀ k, KindAccepted k env ixe sub) ∧ SourceFormInfers env ixe sub t

/-- **The compile with the validator wired**: `compileReport`, then the validator on
its result; its failure is the compile's. -/
def compileValidated (v : ConeValidator) (env : Ix.Environment) :
    Except String (Ixon.Env × Failures) := do
  let out ← compileReport env
  v (coneInput env out.1 out.2)
  pure out

/-- A validated compile is a `compileReport` result that the validator passed. -/
theorem compileValidated_ok {v : ConeValidator} {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} (h : compileValidated v env = .ok (ixe, failures)) :
    compileReport env = .ok (ixe, failures) ∧ v (coneInput env ixe failures) = .ok () := by
  have e : compileValidated v env = Except.bind (compileReport env) fun out =>
      Except.bind (v (coneInput env out.1 out.2)) fun _ => Except.ok out := rfl
  rw [e] at h
  cases hr : compileReport env with
  | error err => rw [hr] at h; cases h
  | ok out =>
    rw [hr] at h
    change Except.bind (v (coneInput env out.1 out.2)) (fun _ => Except.ok out) =
      Except.ok (ixe, failures) at h
    cases hv : v (coneInput env out.1 out.2) with
    | error err => rw [hv] at h; cases h
    | ok u =>
      rw [hv] at h
      change Except.ok out = Except.ok (ixe, failures) at h
      cases h
      exact ⟨rfl, hv⟩

end Ix.Cert
