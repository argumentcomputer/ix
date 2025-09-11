import Ix.Common
import Ix.Address
import Ix.Prove
import Ix.Claim
import Lean.Declaration
import Ix.Ixon.Serialize
import Ix.Ixon.Metadata
import Ix.Ixon.Expr

namespace Ixon

structure Quotient where
  kind : Lean.QuotKind
  lvls : Nat
  type : Address
  deriving BEq, Repr

instance : Serialize Quotient where
  put := fun x => Serialize.put (x.kind, x.lvls, x.type)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Axiom where
  isUnsafe: Bool
  lvls : Nat
  type : Address
  deriving BEq, Repr

instance : Serialize Axiom where
  put := fun x => Serialize.put (x.isUnsafe, x.lvls, x.type)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Definition where
  kind : Ix.DefKind
  safety : Lean.DefinitionSafety
  lvls : Nat
  type : Address
  value : Address
  deriving BEq, Repr

instance : Serialize Definition where
  put := fun x => Serialize.put (x.kind, x.safety, x.lvls, x.type, x.value)
  get := (fun (a,b,c,d,e) => .mk a b c d e) <$> Serialize.get

structure Constructor where
  isUnsafe: Bool
  lvls : Nat
  cidx : Nat
  params : Nat
  fields : Nat
  type : Address
  deriving BEq, Repr

instance : Serialize Constructor where
  put := fun x => Serialize.put (x.isUnsafe, x.lvls, x.cidx, x.params, x.fields, x.type)
  get := (fun (a,b,c,d,e,f) => .mk a b c d e f) <$> Serialize.get

structure RecursorRule where
  fields : Nat
  rhs : Address
  deriving BEq, Repr

instance : Serialize RecursorRule where
  put := fun x => Serialize.put (x.fields, x.rhs)
  get := (fun (a,b) => .mk a b) <$> Serialize.get

structure Recursor where
  k : Bool
  isUnsafe: Bool
  lvls : Nat
  params : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  type : Address
  rules : List RecursorRule
  deriving BEq, Repr

instance : Serialize Recursor where
  put := fun x => Serialize.put ((x.k, x.isUnsafe), x.lvls, x.params, x.indices, x.motives, x.minors, x.type, x.rules)
  get := (fun ((a,b),c,d,e,f,g,h,i) => .mk a b c d e f g h i) <$> Serialize.get

structure Inductive where
  recr : Bool
  refl : Bool
  isUnsafe: Bool
  lvls : Nat
  params : Nat
  indices : Nat
  nested : Nat
  type : Address
  ctors : List Constructor
  recrs : List Recursor
  deriving BEq, Repr

instance : Serialize Inductive where
  put := fun x => Serialize.put ((x.recr,x.refl,x.isUnsafe), x.lvls, x.params, x.indices, x.nested, x.type, x.ctors, x.recrs)
  get := (fun ((a,b,c),d,e,f,g,h,i,j) => .mk a b c d e f g h i j) <$> Serialize.get

structure InductiveProj where
  idx : Nat
  block : Address
  deriving BEq, Repr

instance : Serialize InductiveProj where
  put := fun x => Serialize.put (x.idx, x.block)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure ConstructorProj where
  idx : Nat
  cidx : Nat
  block : Address
  deriving BEq, Repr

instance : Serialize ConstructorProj where
  put := fun x => Serialize.put (x.idx, x.cidx, x.block)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure RecursorProj where
  idx : Nat
  ridx : Nat
  block : Address
  deriving BEq, Repr

instance : Serialize RecursorProj where
  put := fun x => Serialize.put (x.idx, x.ridx, x.block)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure DefinitionProj where
  idx : Nat
  block : Address
  deriving BEq, Repr

instance : Serialize DefinitionProj where
  put := fun x => Serialize.put (x.idx, x.block)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr

structure Env where
  env : List (Address × Address)
  deriving BEq, Repr

instance : Serialize Env where
  put x := Serialize.put x.env
  get := .mk <$> Serialize.get

instance : Serialize Comm where
  put := fun x => Serialize.put (x.secret, x.payload)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

instance : Serialize CheckClaim where
  put x := Serialize.put (x.lvls, x.type, x.value)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

instance : Serialize EvalClaim where
  put x := Serialize.put (x.lvls, x.input, x.output, x.type)
  get := (fun (w,x,y,z) => .mk w x y z) <$> Serialize.get

instance : Serialize Claim where
  put
  | .evals x => putTag4 ⟨0xE, 2⟩ *> Serialize.put x
  | .checks x => putTag4 ⟨0xE, 3⟩ *> Serialize.put x
  get := do match <- getTag4 with
  | ⟨0xE,2⟩ => .evals <$> Serialize.get
  | ⟨0xE,3⟩ => .checks <$> Serialize.get
  | e => throw s!"expected Claim with tag 0xE2 or 0xE3, got {repr e}"

instance : Serialize Proof where
  put := fun x => Serialize.put (x.claim, x.bin)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

end Ixon
