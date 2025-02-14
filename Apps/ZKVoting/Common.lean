import Ix.BuiltIn

inductive Candidate
  | abe | bam | cot
  deriving Inhabited

abbrev Vote := Commitment Candidate

abbrev proofPath : System.FilePath :=
  "Apps" / "ZKVoting" / "proof"
