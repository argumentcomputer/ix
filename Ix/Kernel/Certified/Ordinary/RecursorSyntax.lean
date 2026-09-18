/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RecursorSyntax.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block, so the bare `recursor` address parameter is
the family's `source`.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Reading
import Ix.Kernel.Inductive.Levels

/-!
Annotated ordinary source syntax. Every source expression is transported
through the explicit source-universe map; the motive keeps its own universe.
The generated syntax is subsequently compared with the complete stored type
and rule, and is checked for formation before any equation is published.
-/

namespace Ix.Kernel.Certified.Ordinary

open Model Inductive

universe u
variable {β : Type u}

namespace Shape

def motiveType (shape : Shape β) (source : β) (mode : ElimMode) : AExpr β :=
  .forallN .never (shape.indices.map (AExpr.instL (mode.sourceLevels shape.universes))) <|
    .forallE .never
      ((shape.familyApp source shape.indices.length (parameterVars 0 shape.indices.length)).instL
        (mode.sourceLevels shape.universes))
      (.sort mode.motiveLevel)

def minorFields (shape : Shape β) (source : β) (mode : ElimMode) (ctor : Constructor β) :
    List (AExpr β) :=
  Telescope.lift 1 ((ctor.fields ++ ctor.recursiveTypes shape source).map
    (AExpr.instL (mode.sourceLevels shape.universes)))

def ihType (shape : Shape β) (mode : ElimMode) (ctor : Constructor β)
    (j : Nat) (field : RecursiveField β) : AExpr β :=
  let sl := mode.sourceLevels shape.universes
  let a := ctor.fields.length
  let b := ctor.recursive.length
  let d := field.domains.length
  .forallN (zeroCondition mode.motiveLevel)
    (Telescope.lift b (Telescope.lift 1 (field.domains.map (AExpr.instL sl)) a))
    (.appN (.bvar (a + b + d))
      (field.indices.map (fun e => ((e.instL sl).liftN 1 (a + d)).liftN b d) ++
        [.appN (.bvar (b - 1 - j + d)) (parameterVars 0 d)]))

def ihTypesSyntax (shape : Shape β) (mode : ElimMode) (ctor : Constructor β) : List (AExpr β) :=
  Telescope.independent (ctor.recursive.zipIdx.map fun (field, j) => shape.ihType mode ctor j field)

def minorResult (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  let sl := mode.sourceLevels shape.universes
  let a := ctor.fields.length
  let b := ctor.recursive.length
  .appN (.bvar (a + b + b))
    (ctor.indices.map (fun e => ((e.instL sl).liftN 1 a).liftN (b + b)) ++
      [.appN (.const (.ctor source 0 i) sl)
        (parameterVars (1 + a + b + b) shape.parameters.length ++ parameterVars b (a + b))])

def minorType (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .forallN (zeroCondition mode.motiveLevel) (shape.minorFields source mode ctor) <|
    .forallN (zeroCondition mode.motiveLevel) (shape.ihTypesSyntax mode ctor) <|
      shape.minorResult source mode i ctor

def minorTypesSyntax (shape : Shape β) (source : β) (mode : ElimMode) : List (AExpr β) :=
  Telescope.independent (shape.constructors.zipIdx.map fun (ctor, i) => shape.minorType source mode i ctor)

def recursorTail (shape : Shape β) (source : β) (mode : ElimMode) : AExpr β :=
  let sl := mode.sourceLevels shape.universes
  let pv := zeroCondition mode.motiveLevel
  let c := shape.constructors.length
  let n := shape.indices.length
  .forallN pv (Telescope.lift (1 + c) (shape.indices.map (AExpr.instL sl))) <|
    .forallE pv
      (((shape.familyApp source n (parameterVars 0 n)).instL sl).liftN (1 + c) n)
      (.appN (.bvar (c + n + 1)) (parameterVars 1 n ++ [.bvar 0]))

def recursorType (shape : Shape β) (source : β) (mode : ElimMode) : AExpr β :=
  let pv := zeroCondition mode.motiveLevel
  .forallN pv (shape.parameters.map (AExpr.instL (mode.sourceLevels shape.universes))) <|
    .forallE pv (shape.motiveType source mode) <|
      .forallN pv (shape.minorTypesSyntax source mode) <|
        shape.recursorTail source mode

def ruleBinders (shape : Shape β) (source : β) (mode : ElimMode) (ctor : Constructor β) :
    List (AExpr β) :=
  shape.parameters.map (AExpr.instL (mode.sourceLevels shape.universes)) ++
    [shape.motiveType source mode] ++ shape.minorTypesSyntax source mode ++
    Telescope.lift (1 + shape.constructors.length)
      ((ctor.fields ++ ctor.recursiveTypes shape source).map
        (AExpr.instL (mode.sourceLevels shape.universes)))

def ruleCall (shape : Shape β) (source : β) (mode : ElimMode)
    (ctor : Constructor β) (j : Nat) (field : RecursiveField β) : AExpr β :=
  let sl := mode.sourceLevels shape.universes
  let common := 1 + shape.constructors.length
  let a := ctor.fields.length
  let b := ctor.recursive.length
  let d := field.domains.length
  .lamN (zeroCondition mode.motiveLevel)
    (Telescope.lift b (Telescope.lift common (field.domains.map (AExpr.instL sl)) a))
    (.appN (.const (.member source 1) (mode.recLevels shape.universes))
      (parameterVars (a + b + d) (shape.parameters.length + common) ++
        field.indices.map (fun e => ((e.instL sl).liftN common (a + d)).liftN b d) ++
        [.appN (.bvar (b - 1 - j + d)) (parameterVars 0 d)]))

def ruleRhsBody (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .appN (.bvar (shape.constructors.length - 1 - i + ctor.fields.length + ctor.recursive.length))
    (parameterVars 0 (ctor.fields.length + ctor.recursive.length) ++
      ctor.recursive.zipIdx.map (fun (field, j) => shape.ruleCall source mode ctor j field))

def ruleRhs (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .lamN (zeroCondition mode.motiveLevel) (shape.ruleBinders source mode ctor)
    (shape.ruleRhsBody source mode i ctor)

def ruleIndices (shape : Shape β) (mode : ElimMode) (ctor : Constructor β) : List (AExpr β) :=
  ctor.indices.map fun e =>
    ((e.instL (mode.sourceLevels shape.universes)).liftN (1 + shape.constructors.length)
      ctor.fields.length).liftN ctor.recursive.length

def ruleConstructor (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  let n := ctor.fields.length + ctor.recursive.length
  .appN (.const (.ctor source 0 i) (mode.sourceLevels shape.universes))
    (parameterVars (1 + shape.constructors.length + n) shape.parameters.length ++ parameterVars 0 n)

def ruleResult (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .appN (.bvar (shape.constructors.length + ctor.fields.length + ctor.recursive.length))
    (shape.ruleIndices mode ctor ++ [shape.ruleConstructor source mode i ctor])

def ruleType (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .forallN (zeroCondition mode.motiveLevel) (shape.ruleBinders source mode ctor)
    (shape.ruleResult source mode i ctor)

def ruleLhsBody (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .appN (.const (.member source 1) (mode.recLevels shape.universes))
    (parameterVars (ctor.fields.length + ctor.recursive.length)
      (shape.parameters.length + 1 + shape.constructors.length) ++
      shape.ruleIndices mode ctor ++ [shape.ruleConstructor source mode i ctor])

def ruleLhs (shape : Shape β) (source : β) (mode : ElimMode) (i : Nat)
    (ctor : Constructor β) : AExpr β :=
  .lamN (zeroCondition mode.motiveLevel) (shape.ruleBinders source mode ctor)
    (shape.ruleLhsBody source mode i ctor)

end Shape
end Ix.Kernel.Certified.Ordinary
