module
public import Ix.Compile.SourceGraph.Prepass

@[expose] public section
namespace Ix.Compile.SourceInput

abbrev Raw := Lean.Name × Lean.ConstantInfo

/-- Only the original winner map is retained. The prepass's thin environment,
label array and transient canonical bodies are not captured here. -/
structure Carrier where
  byName : Ix.Map Ix.Name Raw

def ofPrepass (p : SourceGraph.Prepass.Names) : Carrier := ⟨p.leanByIx⟩

/-- The existing singleton-canon fallback, now shared with Source validation.
This lookup does not consult the transformed compile environment. -/
def canonical? (p : Raw) : Option Ix.ConstantInfo :=
  ((Ix.CanonM.canonChunk #[p])[0]?).map (·.2)

def Carrier.lookup? (s : Carrier) (name : Ix.Name) : Option Ix.ConstantInfo :=
  (s.byName.get? name).bind canonical?

def Carrier.representative? (s : Carrier) (name : Ix.Name) : Option Ix.Name :=
  s.byName.getKey? name

inductive Error where
  | missing (requested : Ix.Name)
  | headerMismatch (requested : Ix.Name) (tuple header : Lean.Name)
  | canonicalMissing (requested : Ix.Name)
  deriving Repr

inductive ValueKind where
  | defn | thm | opaq
  deriving Repr, DecidableEq

/-- Non-value declarations remain explicit; they are not failed readings.
Their complete header/family/rules remain in `Form.original`. -/
inductive Body where
  | value (kind : ValueKind) (expression : Ix.Expr)
  | axiomDecl | quotientDecl | inductiveDecl | constructorDecl | recursorDecl
  deriving Repr

structure Form where
  original : Ix.ConstantInfo
  body : Body

def Form.header (f : Form) : Ix.ConstantVal := f.original.getCnst

def formOf (ci : Ix.ConstantInfo) : Form := ⟨ci, match ci with
  | .defnInfo d => .value .defn d.value
  | .thmInfo d => .value .thm d.value
  | .opaqueInfo d => .value .opaq d.value
  | .axiomInfo _ => .axiomDecl | .quotInfo _ => .quotientDecl
  | .inductInfo _ => .inductiveDecl | .ctorInfo _ => .constructorDecl | .recInfo _ => .recursorDecl⟩

/-- Missing input and an inconsistent original tuple/header are explicit
errors. Canonicalization is local to this one original declaration. -/
def Carrier.canonicalAt (s : Carrier) (name : Ix.Name) : Except Error Ix.ConstantInfo := do
  let some raw := s.byName.get? name | throw (.missing name)
  unless raw.1 == raw.2.name do throw (.headerMismatch name raw.1 raw.2.name)
  let some ci := canonical? raw | throw (.canonicalMissing name)
  pure ci

/-- Every kind is returned explicitly; all three value kinds carry their
entire original body and unchanged original header/universe parameters. -/
def Carrier.valueAt (s : Carrier) (name : Ix.Name) : Except Error Form :=
  formOf <$> s.canonicalAt name

/-- Visit every requested row in order, stopping at an explicit error.
The caller can stream the real closure without retaining all canonical bodies. -/
def Carrier.fold {α} (s : Carrier) (names : List Ix.Name) (initial : α)
    (visit : α → Ix.Name → Form → Except Error α) : Except Error α :=
  names.foldlM (fun state name => s.valueAt name >>= visit state name) initial

end Ix.Compile.SourceInput

end
