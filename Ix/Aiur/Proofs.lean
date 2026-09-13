/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Activity
import Ix.Aiur.Proofs.CallOrder
import Ix.Aiur.Proofs.Lookup
import Ix.Aiur.Proofs.Execution
import Ix.Aiur.Proofs.Memory
import Ix.Aiur.Proofs.Field
import Ix.Aiur.Proofs.LocalConstraints
import Ix.Aiur.Proofs.ByteArithmetic
import Ix.Aiur.Proofs.ByteLookups
import Ix.Aiur.Proofs.LookupMessages
import Ix.Aiur.Proofs.LookupShapes
import Ix.Aiur.Proofs.GlobalLookups
import Ix.Aiur.Proofs.LookupBudget
import Ix.Aiur.Proofs.SelectorMessages
import Ix.Aiur.Proofs.SelectorControl
import Ix.Aiur.Proofs.ReturnGates
import Ix.Aiur.Proofs.BranchSelection
import Ix.Aiur.Proofs.OperationRows
import Ix.Aiur.Proofs.CallInventory
import Ix.Aiur.Proofs.BlockRows
import Ix.Aiur.Proofs.BlockRowProjection
import Ix.Aiur.Proofs.BlockRowExecution
import Ix.Aiur.Proofs.BlockRowCalls
import Ix.Aiur.Proofs.BlockRowInputs
import Ix.Aiur.Proofs.FunctionRows
import Ix.Aiur.Proofs.QuerySlots
import Ix.Aiur.Proofs.BlockQuerySlots
import Ix.Aiur.Proofs.QuerySlotMessages
import Ix.Aiur.Proofs.BlockQueryPool
import Ix.Aiur.Proofs.CircuitRows
import Ix.Aiur.Proofs.CircuitRowMembers
import Ix.Aiur.Proofs.CircuitRowQueries
import Ix.Aiur.Proofs.CircuitRowReturns
import Ix.Aiur.Proofs.CircuitRowExecution
import Ix.Aiur.Proofs.RowCounts
import Ix.Aiur.Proofs.CircuitRowCounts
import Ix.Aiur.Proofs.ProviderEquivalence
import Ix.Aiur.Proofs.CircuitTableData
import Ix.Aiur.Proofs.CircuitTableExecution
import Ix.Aiur.Proofs.PublicCircuitExecution
import Ix.Aiur.Proofs.BranchlessSlots
import Ix.Aiur.Proofs.EncodedCircuitExecution
import Ix.Aiur.Proofs.CircuitTraces
import Ix.Aiur.Proofs.CircuitMembership
import Ix.Aiur.Proofs.LookupLayout
import Ix.Aiur.Proofs.MemoryColumns
import Ix.Aiur.Proofs.ByteColumns
import Ix.Aiur.Proofs.Metadata
import Ix.Aiur.Proofs.Renaming
import Ix.Aiur.Proofs.Dedup
import Ix.Aiur.Proofs.TailMatches
import Ix.Aiur.Proofs.NormalizationFrames
import Ix.Aiur.Proofs.Compilation
import Ix.Aiur.Proofs.Grouping
import Ix.Aiur.Proofs.Audit

/-! Audited compiler, grouping and verifier-binding components for Aiur.
These roots do not yet establish full public acceptance-to-model soundness. -/
