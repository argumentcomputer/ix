import LSpec
import Ix.CompileM

/-! Finite structured-payload controls for production array admission.
The unrepresentable array-size boundary is checked symbolically in proofs;
these are codec/assembly controls, not source-typing certificates. -/

namespace Tests.Ix.Compile.PayloadArrays

open LSpec
open _root_.Ix.CompileM

private def definition : Ixon.Definition :=
  { kind := .defn, safety := .safe, lvls := 0, typ := .var 0, value := .var 0 }

private def inductiveValue (count : Nat) : Ixon.Inductive := {
  isUnsafe := false
  lvls := 0
  params := 0
  indices := 0
  typ := .var 0
  ctors := Array.replicate count { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .var 0 } }

private def recursorValue (count : Nat) : Ixon.Recursor := {
  k := false
  isUnsafe := false
  lvls := 0
  params := 0
  indices := 0
  motives := 0
  minors := 0
  typ := .var 0
  rules := Array.replicate count { fields := 0, rhs := .var 0 } }

private def context : CompileEnv × BlockEnv :=
  (default, { all := {}, current := _root_.Ix.Name.mkAnon, mutCtx := {}, univCtx := [] })

private def raw (action : CompileM α) (state : BlockState := {}) : Except CompileError α × BlockState :=
  (action context).run state

private def agrees (members : Array Ixon.MutConst) : Bool :=
  let expected := buildCompiledMutualBlock context.1.sharingLimits [] members #[] {}
  let actual := (raw (finishMutualCompilation [] members #[])).1
  match expected, actual with
  | .ok before, .ok after => before.blockBytes == after.blockBytes && before.blockAddr == after.blockAddr &&
      (match Ixon.deConstant after.blockBytes with
        | .ok decoded => Ixon.serConstant decoded == after.blockBytes
        | .error _ => false)
  | .error first, .error last => toString first == toString last
  | _, _ => false

def controls : List (String × Bool) := Id.run do
  let mut result := []
  for count in [0, 1, 31, 32, 127, 128, 256] do
    let members := #[Ixon.MutConst.defn definition, .indc (inductiveValue count), .recr (recursorValue count)]
    result := result ++ [(s!"nested arrays of size {count} pass admission", (raw (checkMutualPayloadCounts members)).1.isOk)]
  result := result ++ [
    ("empty mutual payload is admitted", (raw (checkMutualPayloadCounts #[])).1.isOk),
    ("definition collapse retains the pure builder's bytes", agrees #[.defn definition]),
    ("recursor collapse retains the pure builder's bytes", agrees #[.recr (recursorValue 2)]),
    ("single inductive retains the mutual wrapper's bytes", agrees #[.indc (inductiveValue 2)]),
    ("mixed mutual payload retains bytes and round-trip", agrees #[.defn definition, .indc (inductiveValue 3), .recr (recursorValue 3)]),
    ("sharing refusal remains the builder's refusal", agrees #[.defn { definition with typ := .share 0 }])]
  let initial : BlockState := {
    refs := #[default]
    univs := #[.zero]
    univsFinal := true }
  let (accepted, after) := raw (checkMutualPayloadCounts #[.indc (inductiveValue 2), .recr (recursorValue 3)]) initial
  result := result ++ [("array admission retains state tables and flag", accepted.isOk &&
    after.refs == initial.refs && after.univs == initial.univs && after.univsFinal)]
  return result

def suite : List TestSeq := controls.map fun (label, ok) => test s!"payload arrays: {label}" ok

end Tests.Ix.Compile.PayloadArrays
