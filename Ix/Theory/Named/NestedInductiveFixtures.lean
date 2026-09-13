/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.NestedInductive

/-!
# Nested flattening fixtures

Executable pins for `nestedElimination?` on the two ladder fixtures — a
universe-polymorphic rose tree through `List` and a nested indexed family
through a `PVec`-style vector — plus the nearest structural rejections.
Every family, constructor, auxiliary specification, and acceptance bit is
compared against a hand-written expected descriptor.  The kernel
differential for the same shapes lives in
`Ix.Theory.Named/Verify/Environment/NestedTransformation.lean`.
-/

namespace Ix.Theory.Named.NestedInductiveFixtures

open VInductDecl

/-! ## Target blocks

Hand-written copies of the nested-into metadata, in each block's own
universe parameters; the Verify differential checks the same shapes
against Lean's stored metadata. -/

/-- `List` as a nested target: one family, one parameter. -/
def listTarget : NestedTargetBlock where
  nparams := 1
  families :=
    [{ name := `List
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const `List [.param 0]) (.bvar 0))⟩, `List.nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0]) (.bvar 1))
                 (.app (.const `List [.param 0]) (.bvar 2))))⟩, `List.cons⟩] }]

/-- A `PVec`-style indexed vector as a nested target: one parameter, one
`Nat` index, indices spelled with `Nat.zero`/`Nat.succ`. -/
def pvecTarget : NestedTargetBlock where
  nparams := 1
  families :=
    [{ name := `PVec
       uvars := 0
       type := .forallE (.sort (.succ .zero))
         (.forallE (.const `Nat []) (.sort (.succ .zero)))
       ctors :=
         [⟨⟨0, .forallE (.sort (.succ .zero))
             (.app (.app (.const `PVec []) (.bvar 0)) (.const `Nat.zero []))⟩,
           `PVec.nil⟩,
          ⟨⟨0, .forallE (.sort (.succ .zero))
             (.forallE (.bvar 0)
               (.forallE (.const `Nat [])
                 (.forallE (.app (.app (.const `PVec []) (.bvar 2)) (.bvar 0))
                   (.app (.app (.const `PVec []) (.bvar 3))
                     (.app (.const `Nat.succ []) (.bvar 1))))))⟩,
           `PVec.cons⟩] }]

/-! ## Rose tree through `List` -/

def roseAux : Lean.Name := (`_nested ++ `List).appendIndexAfter 1

/-- `inductive Rose (α : Type u) | node : α → List (Rose α) → Rose α` -/
def roseSource : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0])
                   (.app (.const `Rose [.param 0]) (.bvar 1)))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] }]

/-- The expected flattened rose block: the rewritten source family plus one
auxiliary family, exactly the shapes pinned against the kernel by the
representation probes. -/
def roseFlat : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] },
     { name := roseAux
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const roseAux [.param 0]) (.bvar 0))⟩, roseAux ++ `nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.app (.const `Rose [.param 0]) (.bvar 0))
               (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
                 (.app (.const roseAux [.param 0]) (.bvar 2))))⟩,
           roseAux ++ `cons⟩] }]

/-- The expected auxiliary specification: `List (Rose α)`, open over the
block parameter. -/
def roseSpec : NestedAuxSpec where
  aux := roseAux
  target := `List
  levels := [.param 0]
  values := [.app (.const `Rose [.param 0]) (.bvar 0)]

def roseElim? : Option (NestedElimination roseSource) :=
  nestedElimination? [listTarget] roseSource

#guard roseElim?.isSome
#guard (roseElim?.map fun elim => elim.flat == roseFlat).getD false
#guard (roseElim?.map fun elim => elim.specs == [roseSpec]).getD false
#guard (roseElim?.map (·.numNested)).getD 0 == 1
#guard roseFlat.stage3
#guard nestedStage3 [listTarget] roseSource
-- acceptance behavior of the raw analyzers on the source is unchanged
#guard !roseSource.stage3

/-! ## Nested indexed family through `PVec` -/

def nvAux : Lean.Name := (`_nested ++ `PVec).appendIndexAfter 1

/-- `inductive NV | node : (n : Nat) → PVec NV n → NV` -/
def nvSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `NV
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.app (.const `PVec []) (.const `NV []))
                 (.bvar 0))
               (.const `NV []))⟩, `NV.node⟩] }]

/-- The expected flattened indexed block: the auxiliary family keeps the
`Nat` index, its `nil` instantiates the index at `Nat.zero`, and its
`cons` retains sibling recursion through `NV` plus the successor index. -/
def nvFlat : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `NV
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.const nvAux []) (.bvar 0))
               (.const `NV []))⟩, `NV.node⟩] },
     { name := nvAux
       uvars := 0
       type := .forallE (.const `Nat []) (.sort (.succ .zero))
       ctors :=
         [⟨⟨0, .app (.const nvAux []) (.const `Nat.zero [])⟩, nvAux ++ `nil⟩,
          ⟨⟨0, .forallE (.const `NV [])
             (.forallE (.const `Nat [])
               (.forallE (.app (.const nvAux []) (.bvar 0))
                 (.app (.const nvAux [])
                   (.app (.const `Nat.succ []) (.bvar 1)))))⟩,
           nvAux ++ `cons⟩] }]

/-- The expected specification: the closed partial application `PVec NV`;
the index argument stays behind on each occurrence. -/
def nvSpec : NestedAuxSpec where
  aux := nvAux
  target := `PVec
  levels := []
  values := [.const `NV []]

def nvElim? : Option (NestedElimination nvSource) :=
  nestedElimination? [pvecTarget] nvSource

#guard nvElim?.isSome
#guard (nvElim?.map fun elim => elim.flat == nvFlat).getD false
#guard (nvElim?.map fun elim => elim.specs == [nvSpec]).getD false
#guard nvFlat.stage3
#guard nestedStage3 [pvecTarget] nvSource
#guard !nvSource.stage3

/-! ## Nearest structural rejections -/

/-- A parametric argument mentioning a constructor-local binder:
`node : (n : Nat) → List (Loose n) → Loose` — the kernel's "parameters
cannot contain local variables" class.  Flattening itself rejects. -/
def looseSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Loose
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.const `List [.zero])
                 (.app (.const `Loose []) (.bvar 0)))
               (.const `Loose []))⟩, `Loose.node⟩] }]

#guard (nestedElimination? [listTarget] looseSource).isNone
#guard !nestedStage3 [listTarget] looseSource

/-- A well-scoped but ill-shaped parametric argument:
`node : Bad → List (Bad Nat.zero) → Bad` flattens, but the auxiliary
constructor then mentions `Bad` applied off the parameter spine, which the
unchanged block analyzer rejects. -/
def badAppSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Bad
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Bad [])
             (.forallE (.app (.const `List [.zero])
                 (.app (.const `Bad []) (.const `Nat.zero [])))
               (.const `Bad []))⟩, `Bad.node⟩] }]

#guard (nestedElimination? [listTarget] badAppSource).isSome
#guard !nestedStage3 [listTarget] badAppSource

-- Without the `List` target metadata the occurrence is not recognized,
-- the flattened block is the source itself, and the unchanged analyzer
-- rejects the under-a-foreign-head family mention.
#guard (nestedElimination? [] roseSource).isSome
#guard ((nestedElimination? [] roseSource).map
  fun elim => elim.flat == roseSource && elim.specs == []).getD false
#guard !nestedStage3 [] roseSource

/-- A source family occupying the first canonical auxiliary name collides
with the created auxiliary family; `blockNamesOK` rejects the flattened
block exactly where the kernel's `checkName` rejects its own duplicate
insertion. -/
def collisionSource : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0])
                   (.app (.const `Rose [.param 0]) (.bvar 1)))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] },
     { name := (`_nested ++ `List).appendIndexAfter 1
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors := [] }]

#guard (nestedElimination? [listTarget] collisionSource).isSome
#guard !nestedStage3 [listTarget] collisionSource

/-! ## Restoration checks

Structural pins for the restored generation artifacts; the exact
comparison against Lean's stored recursor types and rule RHSs lives in the
Verify differential. -/

def roseNested? : Option (NestedBlockChecked roseSource) :=
  nestedBlockChecked? [listTarget] roseSource

def nvNested? : Option (NestedBlockChecked nvSource) :=
  nestedBlockChecked? [pvecTarget] nvSource

#guard roseNested?.isSome
#guard nvNested?.isSome

-- the restored recursor inventory: one per source family plus one per
-- auxiliary family, on the main family's `appendIndexAfter` names
#guard (roseNested?.map fun n => n.recursors.map (·.name)).getD [] ==
  [`Rose.rec, ((.str `Rose "rec" : Lean.Name)).appendIndexAfter 1]
#guard (nvNested?.map fun n => n.recursors.map (·.name)).getD [] ==
  [`NV.rec, ((.str `NV "rec" : Lean.Name)).appendIndexAfter 1]

def roseAuxConsts : List Lean.Name :=
  [roseAux, roseAux ++ `nil, roseAux ++ `cons, .str roseAux "rec"]

def nvAuxConsts : List Lean.Name :=
  [nvAux, nvAux ++ `nil, nvAux ++ `cons, .str nvAux "rec"]

/-- No auxiliary constant survives restoration in any recursor type or
rule component. -/
def restoredClean {source : VInductDecl} (auxConsts : List Lean.Name)
    (nested : NestedBlockChecked source) : Bool :=
  nested.recursors.all (fun r => !VExpr.hasAnyConst auxConsts r.type) &&
    nested.generatedRules.all fun df =>
      !VExpr.hasAnyConst auxConsts df.lhs &&
        !VExpr.hasAnyConst auxConsts df.rhs &&
        !VExpr.hasAnyConst auxConsts df.type

#guard (roseNested?.map (restoredClean roseAuxConsts)).getD false
#guard (nvNested?.map (restoredClean nvAuxConsts)).getD false

-- the globally flattened rule inventory: one node rule plus the two
-- restored `List`/`PVec` rules
#guard (roseNested?.map fun n => n.generatedRules.length).getD 0 == 3
#guard (nvNested?.map fun n => n.generatedRules.length).getD 0 == 3

-- the nested transaction inserts the source payload and the restored
-- recursors, and no auxiliary constant
def roseNestedEnv? : Option VEnv := do
  VEnv.empty.addInductNested (← roseNested?)

#guard roseNestedEnv?.isSome
#guard (roseNestedEnv?.map fun env =>
  (env.constants `Rose).isSome && (env.constants `Rose.node).isSome &&
    (env.constants `Rose.rec).isSome &&
    (env.constants (((.str `Rose "rec" : Lean.Name)).appendIndexAfter 1)).isSome &&
    (env.constants roseAux).isNone &&
    (env.constants (roseAux ++ `cons)).isNone &&
    (env.constants (.str roseAux "rec")).isNone).getD false

end Ix.Theory.Named.NestedInductiveFixtures
