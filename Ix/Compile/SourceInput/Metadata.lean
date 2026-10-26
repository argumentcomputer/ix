module
public import Ix.Compile.SourceInput

@[expose] public section
namespace Ix.Compile.SourceInput.Metadata

/-- Occurrences in the five family/constructor metadata fields. The index
belongs to the original field, including duplicate names. These are lookup
and grouping obligations, not expression uses or strict scheduling edges. -/
inductive Ref where
  | inductAll (index : Nat) (name : Ix.Name)
  | inductCtor (index : Nat) (name : Ix.Name)
  | ctorInduct (name : Ix.Name)
  | recAll (index : Nat) (name : Ix.Name)
  | ruleCtor (index : Nat) (name : Ix.Name)
  deriving Repr, DecidableEq

def Ref.name : Ref → Ix.Name
  | .inductAll _ n | .inductCtor _ n | .ctorInduct n | .recAll _ n | .ruleCtor _ n => n

def indexed (tag : Nat → Ix.Name → Ref) (names : Array Ix.Name) : List Ref :=
  names.toList.zipIdx.map fun (name,index) => tag index name

/-- Keep complete structural names and every field position. No lookup,
comparison, set insertion or family-consistency check filters these rows. -/
def capture : Ix.ConstantInfo → List Ref
  | .inductInfo d => indexed .inductAll d.all ++ indexed .inductCtor d.ctors
  | .ctorInfo d => [.ctorInduct d.induct]
  | .recInfo d => indexed .recAll d.all ++ indexed .ruleCtor (d.rules.map (·.ctor))
  | _ => []

end Ix.Compile.SourceInput.Metadata
namespace Ix.Compile.SourceInput

/-- Canonicalize the actual original winner through valueAt, then retain
only its indexed metadata occurrences. Existing lookup errors propagate. -/
def Carrier.captureMetadataAt (s : Carrier) (name : Ix.Name) : Except Error (List Metadata.Ref) :=
  (fun form => Metadata.capture form.original) <$> s.valueAt name

end Ix.Compile.SourceInput
end
