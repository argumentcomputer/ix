module
public import Ix.MultiStark.Verify.Basic
public import Ix.MultiStark.Verify.Codec
public import Ix.MultiStark.Verify.Key
public import Ix.MultiStark.Verify.Claim
public import Ix.MultiStark.Verify.Transcript
public import Ix.MultiStark.Verify.Shape
public import Ix.MultiStark.Verify.Ood
public import Ix.MultiStark.Verify.Mmcs
public import Ix.MultiStark.Verify.Pcs
public import Ix.MultiStark.Verify.Check
public import Ix.MultiStark.Verify.Source

/-! Pure deterministic Stage 2 verifier and closed-CheckEnv source wrapper.
This umbrella deliberately imports no native FFI or Aiur DSL. Independent
protocol refinement, cryptographic soundness, guest compilation, and generic
Flock/terminal verification remain separate certification gates. -/
