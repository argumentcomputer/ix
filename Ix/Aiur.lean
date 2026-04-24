module

-- Stage 1 (Source) IR
public import Ix.Aiur.Goldilocks
public import Ix.Aiur.Meta
public import Ix.Aiur.Stages.Source
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Interpret

-- Stage 2 (Typed) IR
public import Ix.Aiur.Stages.Typed
public import Ix.Aiur.Semantics.TypedEval

-- Stage 3 (Simple) IR
public import Ix.Aiur.Stages.Simple

-- Stage 4 (Concrete) IR
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Semantics.ConcreteEval

-- Stage 5 (Bytecode)
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Semantics.BytecodeFfi
public import Ix.Aiur.Semantics.BytecodeEval
public import Ix.Aiur.Protocol

-- Semantic relation layer
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Semantics.Compatible

-- Compiler pipeline
public import Ix.Aiur.Compiler.Check
public import Ix.Aiur.Compiler.Match
public import Ix.Aiur.Compiler.Simple
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Layout
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Compiler.Dedup
public import Ix.Aiur.Compiler
public import Ix.Aiur.Statistics

-- Proofs
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Proofs.ConcreteEvalInversion
public import Ix.Aiur.Proofs.StructCompatible
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.LowerShared
public import Ix.Aiur.Proofs.LowerCalleesFromLayout
public import Ix.Aiur.Proofs.LowerSoundCore
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeProgress
public import Ix.Aiur.Proofs.SimplifySound
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.CompilerPreservation
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Proofs.CompilerCorrect
