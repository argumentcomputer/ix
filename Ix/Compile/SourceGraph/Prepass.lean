module
public import Ix.Compile.SourceGraph.Stream

@[expose] public section
namespace Ix.Compile.SourceGraph.Prepass

/-! The existing three-product name prepass, as an owned pure fold. These
exact placeholders serve only the ground check, never logical admission.
The actual CompileDriver call remains a separately reviewed integration. -/

def placeholderHeader : ConstantVal := ⟨.mkAnon, #[], Expr.mkSort Level.mkZero⟩
def phAxiom : ConstantInfo := .axiomInfo { cnst := placeholderHeader, isUnsafe := false }
def phCtor : ConstantInfo := .ctorInfo
  { cnst := placeholderHeader, induct := .mkAnon, cidx := 0,
    numParams := 0, numFields := 0, isUnsafe := false }
def placeholder : Lean.ConstantInfo → ConstantInfo
  | .ctorInfo _ => phCtor
  | _ => phAxiom

structure Names where
  leanByIx : Map Name (Lean.Name × Lean.ConstantInfo) := {}
  thinConsts : Map Name ConstantInfo := {}
  labelled : Array (Name × Lean.ConstantInfo) := #[]

def addNamed (state : Names) (ixn : Name) (source : Lean.Name × Lean.ConstantInfo) : Names :=
  let ⟨leanByIx, thinConsts, labelled⟩ := state
  ⟨leanByIx.insert ixn source, thinConsts.insert ixn (placeholder source.2),
    labelled.push (ixn, source.2)⟩

def nameStep (state : Names) (source : Lean.Name × Lean.ConstantInfo) : Names :=
  addNamed state (Id.run ((CanonM.canonName source.1).run {})).1 source

def run (input : Array (Lean.Name × Lean.ConstantInfo)) : Names := input.foldl nameStep {}

/-- Names and original Lean records are prepared once; complete canonical
bodies remain transient in Stream's chunk-local producer. -/
def produce (reserved : Lean.ConstantInfo → Bool) (input : Array (Lean.Name × Lean.ConstantInfo))
    (workers : Nat) : Names × Stream.Output :=
  let p := run input
  (p, Stream.runLabelled { consts := p.thinConsts } reserved p.labelled workers)

end Ix.Compile.SourceGraph.Prepass
