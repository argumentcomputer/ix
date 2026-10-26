module
public import Ix.Compile.SourceInput

@[expose] public section
namespace Ix.Compile.SourceInput.GroupView

/-- The fields inspected by grouping decisions. Type/value/rule bodies are
deliberately absent; this is not a replacement ConstantInfo or environment. -/
inductive Kind where
  | axiomDecl | definitionDecl | theoremDecl | opaqueDecl | quotientDecl
  | inductiveDecl (all ctors : Array Ix.Name) (numNested : Nat)
  | constructorDecl (induct : Ix.Name) (cidx : Nat)
  | recursorDecl (all : Array Ix.Name)
  deriving Repr

structure Meta where
  headerName : Ix.Name
  kind : Kind
  deriving Repr

def project (ci : Ix.ConstantInfo) : Meta :=
  ⟨ci.getCnst.name,match ci with
    | .axiomInfo _ => .axiomDecl | .defnInfo _ => .definitionDecl
    | .thmInfo _ => .theoremDecl | .opaqueInfo _ => .opaqueDecl
    | .quotInfo _ => .quotientDecl
    | .inductInfo d => .inductiveDecl d.all d.ctors d.numNested
    | .ctorInfo d => .constructorDecl d.induct d.cidx
    | .recInfo d => .recursorDecl d.all⟩

structure Row where
  storedKey : Ix.Name
  grouping : Meta
  deriving Repr

end Ix.Compile.SourceInput.GroupView
namespace Ix.Compile.SourceInput

def Carrier.groupKeys (s : Carrier) : List Ix.Name := s.byName.toList.map Prod.fst

def Carrier.groupMetaAt (s : Carrier) (name : Ix.Name) : Except Error GroupView.Meta :=
  (fun form => GroupView.project form.original) <$> s.valueAt name

def Carrier.groupRowAt (s : Carrier) (name : Ix.Name) : Except Error GroupView.Row :=
  (GroupView.Row.mk name) <$> s.groupMetaAt name

/-- Visit the complete raw-winner domain in its actual stored-key order.
valueAt canonicalizes one whole original declaration transiently per row;
only compact grouping metadata survives. No body map, filtering or sort. -/
def Carrier.groupView (s : Carrier) : Except Error (List GroupView.Row) :=
  s.groupKeys.mapM s.groupRowAt

end Ix.Compile.SourceInput
end
