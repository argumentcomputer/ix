/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Annotated
import Ix.Kernel.Model.BetaSpine
import Ix.Kernel.Model.BetaSubstitution
import Ix.Kernel.Model.Checking
import Ix.Kernel.Model.Context
import Ix.Kernel.Model.ContextTransport
import Ix.Kernel.Model.Environment
import Ix.Kernel.Model.Extension
import Ix.Kernel.Model.Inductive.Codes
import Ix.Kernel.Model.Inductive.Container
import Ix.Kernel.Model.Inductive.Recursor
import Ix.Kernel.Model.Inductive.Telescope
import Ix.Kernel.Model.Instantiation
import Ix.Kernel.Model.Interpret
import Ix.Kernel.Model.Judgment
import Ix.Kernel.Model.LevelCongruence
import Ix.Kernel.Model.PrimitiveValues
import Ix.Kernel.Model.ReferenceMap
import Ix.Kernel.Model.SetModel.Container
import Ix.Kernel.Model.SetModel.Iter
import Ix.Kernel.Model.SetModel.Ops
import Ix.Kernel.Model.SetModel.RecGraph
import Ix.Kernel.Model.SetModel.TaggedSum
import Ix.Kernel.Model.SetModel.TupleTower
import Ix.Kernel.Model.SetTheory.Core
import Ix.Kernel.Model.SetTheory.Derive.Choice
import Ix.Kernel.Model.SetTheory.Derive.Empty
import Ix.Kernel.Model.SetTheory.Derive.Graphs
import Ix.Kernel.Model.SetTheory.Derive.Lfp
import Ix.Kernel.Model.SetTheory.Derive.LfpFam
import Ix.Kernel.Model.SetTheory.Derive.Omega
import Ix.Kernel.Model.SetTheory.Derive.Pair
import Ix.Kernel.Model.SetTheory.Derive.Pt
import Ix.Kernel.Model.SetTheory.Derive.Quot
import Ix.Kernel.Model.SetTheory.Derive.Sep
import Ix.Kernel.Model.SetTheory.Derive.Sigma
import Ix.Kernel.Model.SetTheory.Derive.Univ
import Ix.Kernel.Model.SetTheory.Derive.Universe
import Ix.Kernel.Model.Signature
import Ix.Kernel.Model.Substitution
import Ix.Kernel.Model.Support
import Ix.Kernel.Model.TelescopeSemantics
import Ix.Kernel.Model.UniverseBounds
import Ix.Kernel.Model.Value
import Ix.Kernel.Model.WellDenoted

/-! # The ported set model

Umbrella for the semantic model of `Ix.Kernel`: the set theory interface and
derivations, set constructions, annotated syntax, total interpretation,
semantic judgments, and model-extension support. Every module here was ported
from the `jcb/ix-kernel-consistency` branch; see
`Tests/Ix/Kernel/ImportManifest.lean`. -/
