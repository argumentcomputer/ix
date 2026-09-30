/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress.Constant
import Ix.Kernel.Consistency

/-! # Checking Ixon-shaped in-memory input

The host supplies declaration order, constant pairs, and literal blobs.
The pure driver checks key uniqueness, validates projection records, reads
each primary declaration exactly, and executes the certified declaration
checker. No byte decoding, hashing, or host-checker verdict enters this path.
-/

namespace Ix.Kernel.Ingress

def context (constants : Constants) (blobs : Blobs) (family : Option (ConstRef Address))
    (pair : Address × Ixon.Constant) : Context :=
  ⟨constants, blobs, pair.1, pair.2, family⟩

/-- Projection records contribute names for an existing owner. Primary records
contribute one declaration each, preserving their relative input order. -/
inductive DeclarationsRead (constants : Constants) (blobs : Blobs)
    (family : Option (ConstRef Address)) : Constants → List (Decl Address) → Prop where
  | nil : DeclarationsRead constants blobs family [] []
  | declaration : BlockReads (context constants blobs family pair) block →
      DeclarationsRead constants blobs family rest decls →
      DeclarationsRead constants blobs family (pair :: rest) (⟨pair.1, block⟩ :: decls)
  | projection : isProjection pair.2.info = true → referenceSource constants pair.1 pair.2 = some ref →
      DeclarationsRead constants blobs family rest decls →
      DeclarationsRead constants blobs family (pair :: rest) decls

theorem DeclarationsRead.primary {constants : Constants} {blobs : Blobs}
    {family : Option (ConstRef Address)} {inputs : Constants} {decls : List (Decl Address)}
    (h : DeclarationsRead constants blobs family inputs decls)
    {pair : Address × Ixon.Constant} (member : pair ∈ inputs)
    (primary : isProjection pair.2.info = false) :
    ∃ block, BlockReads (context constants blobs family pair) block ∧
      (⟨pair.1, block⟩ : Decl Address) ∈ decls := by
  induction h generalizing pair with
  | nil => simp at member
  | @declaration head block rest decls reading _ ih =>
    rcases List.mem_cons.mp member with same | member
    · subst pair
      exact ⟨block, reading, List.mem_cons_self⟩
    · obtain ⟨block, reading, found⟩ := ih member primary
      exact ⟨block, reading, List.mem_cons_of_mem _ found⟩
  | @projection head ref rest decls projection _ _ ih =>
    rcases List.mem_cons.mp member with same | member
    · subst pair
      simp [primary] at projection
    · exact ih member primary

def readDeclarationsC (constants : Constants) (blobs : Blobs)
    (family : Option (ConstRef Address)) (fuel : Nat) : (inputs : Constants) →
    Search { decls : List (Decl Address) // DeclarationsRead constants blobs family inputs decls }
  | [] => .ok ⟨[], .nil⟩
  | pair :: rest => do
    if hp : isProjection pair.2.info = true then
      match hr : referenceSource constants pair.1 pair.2 with
      | none => throw (.malformed "projection record has invalid tables, owner, kind, or position")
      | some _ref =>
        let decls ← readDeclarationsC constants blobs family fuel rest
        return ⟨decls.val, .projection hp hr decls.property⟩
    else
      let block ← readBlockC (context constants blobs family pair) fuel
      let decls ← readDeclarationsC constants blobs family fuel rest
      return ⟨⟨pair.1, block.val⟩ :: decls.val, .declaration block.property decls.property⟩

/-- The executable declaration reader without its proof component. -/
def readDeclarations (constants : Constants) (blobs : Blobs)
    (family : Option (ConstRef Address)) (fuel : Nat) (inputs : Constants) :
    Search (List (Decl Address)) :=
  (readDeclarationsC constants blobs family fuel inputs).map Subtype.val

theorem readDeclarations_reading {constants : Constants} {blobs : Blobs}
    {family : Option (ConstRef Address)} {fuel : Nat} {inputs : Constants}
    {decls : List (Decl Address)}
    (h : readDeclarations constants blobs family fuel inputs = .ok decls) :
    DeclarationsRead constants blobs family inputs decls := by
  obtain ⟨⟨_, reading⟩, _, rfl⟩ := Except.map_eq_ok h
  exact reading

/-- The declaration reading is a function of the records: the records
describe at most one declaration list. -/
theorem DeclarationsRead.deterministic {constants : Constants} {blobs : Blobs}
    {family : Option (ConstRef Address)} {inputs : Constants} {left right : List (Decl Address)}
    (h : DeclarationsRead constants blobs family inputs left)
    (other : DeclarationsRead constants blobs family inputs right) : left = right := by
  induction h generalizing right with
  | nil => cases other; rfl
  | declaration hb _ ih =>
    cases other with
    | declaration hb' rest' => rw [BlockReads.deterministic hb hb', ih rest']
    | projection hp _ _ =>
      have := InfoReads.not_projection hb
      simp_all [context]
  | projection hp _ _ ih =>
    cases other with
    | declaration hb' _ =>
      have := InfoReads.not_projection hb'
      simp_all [context]
    | projection _ _ rest' => exact ih rest'

/-- The supplied Ixon records read as declarations (`DeclarationsRead`, an exact
reading of every table, sharing node, and reference), and each declaration's
type and body reading is installed in the accepted environment
(`Block.Installed`, whose scope `Ix.Kernel.Fidelity` states). This is separate
from the existence of its model. -/
structure Installed (constants : Constants) (blobs : Blobs)
    (family : Option (ConstRef Address)) (env : Env Address) : Prop where
  constantKeys : (constants.map Prod.fst).Nodup
  blobKeys : (blobs.map Prod.fst).Nodup
  declarations : ∃ decls, DeclarationsRead constants blobs family constants decls ∧
    ∀ d ∈ decls, d.block.Installed d.address env.toEnvironment

/-- Every supplied primary record has its own installed type and body reading. -/
theorem Installed.primary {constants : Constants} {blobs : Blobs}
    {family : Option (ConstRef Address)} {env : Env Address}
    (h : Installed constants blobs family env) {pair : Address × Ixon.Constant}
    (member : pair ∈ constants) (primary : isProjection pair.2.info = false) :
    ∃ block, BlockReads (context constants blobs family pair) block ∧
      block.Installed pair.1 env.toEnvironment := by
  obtain ⟨decls, reading, installed⟩ := h.declarations
  obtain ⟨block, hb, found⟩ := reading.primary member primary
  exact ⟨block, hb, installed _ found⟩

universe v

def checkEnvC (cfg : Config) (constants : Constants) (blobs : Blobs)
    (family : Option (ConstRef Address)) : Except Error { env : Env Address //
      Installed constants blobs family env ∧
      ∀ (V : Type v) [Model.SetTheory V], Nonempty (Model V env) } := do
  if hc : (constants.map Prod.fst).Nodup then
    if hb : (blobs.map Prod.fst).Nodup then
      let declarations ← (readDeclarationsC constants blobs family cfg.fuel constants).mapError
        (Error.ofSearch "Ixon ingress")
      let checked ← checkDeclsC.{0,v} cfg Env.empty declarations.val
      return ⟨checked.val, ⟨hc, hb, declarations.val, declarations.property, checked.property.2⟩,
        fun V _ => checked.property.1.step V (Model.emptyEnv V)⟩
    else throw (.rejected "duplicate blob address")
  else throw (.rejected "duplicate constant address")

end Ix.Kernel.Ingress

namespace Ix.Kernel

universe v

/-- Check ordered Ixon constant pairs and their literal blobs. The optional
literal family must acquire the kernel's natural-number fact before use. -/
def checkEnv (cfg : Config) (constants : Ingress.Constants) (blobs : Ingress.Blobs)
    (family : Option (ConstRef Address) := none) : Except Error (Env Address) :=
  (Ingress.checkEnvC.{v} cfg constants blobs family).map Subtype.val

theorem checkEnv_reading {cfg : Config} {constants : Ingress.Constants} {blobs : Ingress.Blobs}
    {family : Option (ConstRef Address)} {env : Env Address}
    (h : checkEnv.{v} cfg constants blobs family = .ok env) :
    Ingress.Installed constants blobs family env := by
  obtain ⟨⟨_, reading, _⟩, _, rfl⟩ := Except.map_eq_ok h
  exact reading

theorem checkEnv_has_model (V : Type v) [Model.SetTheory V] {cfg : Config}
    {constants : Ingress.Constants} {blobs : Ingress.Blobs}
    {family : Option (ConstRef Address)} {env : Env Address}
    (h : checkEnv.{v} cfg constants blobs family = .ok env) : Nonempty (Model V env) := by
  obtain ⟨⟨_, _, model⟩, _, rfl⟩ := Except.map_eq_ok h
  exact model V

/-- The exact acceptance domain of the Ixon entry point, as two stages: the
record and blob keys are distinct, the records read as declarations at the
configured fuel (`Ingress.readDeclarations_reading`; the reading is
deterministic), and the closed `check` accepts those declarations. -/
theorem checkEnv_ok_iff {cfg : Config} {constants : Ingress.Constants} {blobs : Ingress.Blobs}
    {family : Option (ConstRef Address)} {env : Env Address} :
    checkEnv.{v} cfg constants blobs family = .ok env ↔
      (constants.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup ∧
        ∃ decls, Ingress.readDeclarations constants blobs family cfg.fuel constants = .ok decls ∧
          check.{0,v} cfg decls = .ok env := by
  unfold checkEnv Ingress.checkEnvC Ingress.readDeclarations check checkDecls
  by_cases hc : (constants.map Prod.fst).Nodup
  · by_cases hb : (blobs.map Prod.fst).Nodup
    · cases hr : Ingress.readDeclarationsC constants blobs family cfg.fuel constants with
      | error failure =>
        simp [hc, hb, Except.mapError, bind, Except.bind, Except.map]
      | ok declarations =>
        cases hk : checkDeclsC.{0,v} cfg Env.empty declarations.val with
        | error failure =>
          simp [hc, hb, hk, Except.mapError, bind, Except.bind, Except.map]
        | ok checked =>
          simp [hc, hb, hk, Except.mapError, bind, Except.bind, Except.map, pure, Except.pure]
    · simp [hc, hb, Except.map]
  · simp [hc, Except.map]

/-- No constant accepted from Ixon records inhabits a type that denotes the
empty set in every model of the checked environment. -/
theorem checkEnv_no_proof_of_False (V : Type v) [Model.SetTheory V] {cfg : Config}
    {constants : Ingress.Constants} {blobs : Ingress.Blobs}
    {family : Option (ConstRef Address)} {env : Env Address}
    (h : checkEnv.{v} cfg constants blobs family = .ok env)
    {r : ConstRef Address} {entry : Model.ConstantEntry Address}
    (hr : env.toEnvironment r = some entry)
    (hA : env.EmptyType.{0,v} entry.universes entry.type) : False := by
  obtain ⟨m⟩ := checkEnv_has_model V h
  have hmem := m.realizes.member r entry hr (List.replicate entry.universes 0)
    (by simp) (fun _ => Model.SetTheory.empty)
  rw [hA V m _ (by simp) _] at hmem
  exact Model.SetTheory.not_mem_empty _ hmem

/-- The Ixon form of `no_inhabitant_of_empty`: once a constructor-free family's
eliminator is installed, no accepted record inhabits the family. -/
theorem checkEnv_no_inhabitant_of_empty (V : Type v) [Model.SetTheory V] {cfg : Config}
    {constants : Ingress.Constants} {blobs : Ingress.Blobs}
    {family : Option (ConstRef Address)} {env : Env Address}
    (h : checkEnv.{v} cfg constants blobs family = .ok env) {source : Address}
    {recursor : ConstRef Address}
    (hE : Certified.Basis.Empty.Interface env.toEnvironment source recursor)
    {r : ConstRef Address} {entry : Model.ConstantEntry Address}
    (hr : env.toEnvironment r = some entry)
    (hu : entry.universes = 0) (ht : entry.type = .const (.member source 0) []) : False :=
  checkEnv_no_proof_of_False V h hr (by rw [hu, ht]; exact Env.emptyType_of_empty hE)

end Ix.Kernel
