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
  lvls : Nat
  type : Address
  kind : Lean.QuotKind
  deriving BEq, Repr

instance : Serialize Quotient where
  put := fun x => Serialize.put (x.lvls, x.type, x.kind)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Axiom where
  lvls : Nat
  type : Address
  isUnsafe: Bool
  deriving BEq, Repr

instance : Serialize Axiom where
  put := fun x => Serialize.put (x.lvls, x.type, x.isUnsafe)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Definition where
  lvls : Nat
  type : Address
  mode : Ix.DefKind
  value : Address
  safety : Lean.DefinitionSafety
  deriving BEq, Repr

instance : Serialize Definition where
  put := fun x => Serialize.put (x.lvls, x.type, x.mode, x.value, x.safety)
  get := (fun (a,b,c,d,e) => .mk a b c d e) <$> Serialize.get

structure Constructor where
  lvls : Nat
  type : Address
  cidx : Nat
  params : Nat
  fields : Nat
  isUnsafe: Bool
  deriving BEq, Repr

instance : Serialize Constructor where
  put x := do
    Serialize.put x.lvls
    Serialize.put x.type
    Serialize.put x.cidx
    Serialize.put x.params
    Serialize.put x.fields
    Serialize.put x.isUnsafe
  get := do
    let lvls <- Serialize.get
    let type <- Serialize.get
    let cidx <- Serialize.get
    let params <- Serialize.get
    let fields <- Serialize.get
    let isUnsafe <- Serialize.get
    return .mk lvls type cidx params fields isUnsafe

structure RecursorRule where
  fields : Nat
  rhs : Address
  deriving BEq, Repr

instance : Serialize RecursorRule where
  put x := do
    Serialize.put x.fields
    Serialize.put x.rhs
  get := do
    let fields <- Serialize.get
    let rhs <- Serialize.get
    return .mk fields rhs

structure Recursor where
  lvls : Nat
  type : Address
  params : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  rules : List RecursorRule
  k : Bool
  isUnsafe: Bool
  deriving BEq, Repr

instance : Serialize Recursor where
  put x := do
    Serialize.put x.lvls
    Serialize.put x.type
    Serialize.put x.params
    Serialize.put x.indices
    Serialize.put x.motives
    Serialize.put x.minors
    Serialize.put x.rules
    Serialize.put (x.k, x.isUnsafe)
  get := do
    let lvls <- Serialize.get
    let type <- Serialize.get
    let params <- Serialize.get
    let indices <- Serialize.get
    let motives <- Serialize.get
    let minors <- Serialize.get
    let rules <- Serialize.get
    let (k, isUnsafe) := <- Serialize.get
    return .mk lvls type params indices motives minors rules k isUnsafe

structure Inductive where
  lvls : Nat
  type : Address
  params : Nat
  indices : Nat
  ctors : List Constructor
  recrs : List Recursor
  nested : Nat
  recr : Bool
  refl : Bool
  isUnsafe: Bool
  deriving BEq, Repr

instance : Serialize Inductive where
  put x := do
    Serialize.put x.lvls
    Serialize.put x.type
    Serialize.put x.params
    Serialize.put x.indices
    Serialize.put x.ctors
    Serialize.put x.recrs
    Serialize.put x.nested
    Serialize.put (x.recr, x.refl, x.isUnsafe)
  get := do
    let lvls : Nat <- Serialize.get
    let type : Address <- Serialize.get
    let params : Nat <- Serialize.get
    let indices : Nat <- Serialize.get
    let ctors : List Constructor <- Serialize.get
    let recrs : List Recursor <- Serialize.get
    let nested: Nat <- Serialize.get
    let (recr, refl, isUnsafe) : (Bool × Bool × Bool) := <- Serialize.get
    return .mk lvls type params indices ctors recrs nested recr refl isUnsafe

structure InductiveProj where
  block : Address
  idx : Nat
  deriving BEq, Repr

instance : Serialize InductiveProj where
  put := fun x => Serialize.put (x.block, x.idx)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure ConstructorProj where
  block : Address
  idx : Nat
  cidx : Nat
  deriving BEq, Repr

instance : Serialize ConstructorProj where
  put := fun x => Serialize.put (x.block, x.idx, x.cidx)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure RecursorProj where
  block : Address
  idx : Nat
  ridx : Nat
  deriving BEq, Repr

instance : Serialize RecursorProj where
  put := fun x => Serialize.put (x.block, x.idx, x.ridx)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure DefinitionProj where
  block : Address
  idx : Nat
  deriving BEq, Repr

instance : Serialize DefinitionProj where
  put := fun x => Serialize.put (x.block, x.idx)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr

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
  | .checks x => putTag4 ⟨0xE, 2⟩ *> Serialize.put x
  | .evals x => putTag4 ⟨0xE, 3⟩ *> Serialize.put x
  get := do match <- getTag4 with
  | ⟨0xE,2⟩ => .checks <$> Serialize.get
  | ⟨0xE,3⟩ => .checks <$> Serialize.get
  | e => throw s!"expected Claim with tag 0xE2 or 0xE3, got {repr e}"

instance : Serialize Proof where
  put := fun x => Serialize.put (x.claim, x.bin)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

end Ixon
