module

public import Ix.Ixon
public import Ix.Address.Admission
public import IxC.Kernel.Ixon.Reader

/-! # Writing the role table's closed proof evidence

The existing PinGen theorem-record writer, shared for artifact-specific
binding emission. Its reference lookup must come from the actual published
records. This writer is untrusted: the resulting exact bytes and their proofs
still need canonical decoding, authentication, reading and certified checking.
The extraction keeps the existing sharing and binder-contract encoding.
-/

@[expose] public section

namespace Ix.RoleBinding.Evidence

open Ix.Kernel.Reader (CName CExpr CLevel)

/-- The writer's state: the record's tables and the blobs its literals need. -/
structure Egress (md : Ix.Kernel.Mode) where
  refs : Array Address := #[]
  refIdx : Std.HashMap Address Nat := {}
  univs : Array Ixon.Univ := #[]
  univIdx : Std.HashMap Ixon.Univ Nat := {}
  sharing : Array Ixon.Expr := #[]
  shareIdx : Std.HashMap (CExpr md) Nat := {}
  blobs : Array (Address × ByteArray) := #[]

abbrev EgressM (md : Ix.Kernel.Mode) := StateT (Egress md) (Except String)

def refOf {md : Ix.Kernel.Mode} (a : Address) : EgressM md UInt64 := do
  if let some i := (← get).refIdx[a]? then return i.toUInt64
  let i := (← get).refs.size
  modify fun s => { s with refs := s.refs.push a, refIdx := s.refIdx.insert a i }
  return i.toUInt64

def convLevel : CLevel → Ixon.Univ
  | .zero => .zero
  | .succ u => .succ (convLevel u)
  | .max u v => .max (convLevel u) (convLevel v)
  | .imax u v => .imax (convLevel u) (convLevel v)
  | .param i => .var i.toUInt64

def univOf {md : Ix.Kernel.Mode} (l : CLevel) : EgressM md UInt64 := do
  let u := convLevel l
  if let some i := (← get).univIdx[u]? then return i.toUInt64
  let i := (← get).univs.size
  modify fun s => { s with univs := s.univs.push u, univIdx := s.univIdx.insert u i }
  return i.toUInt64

/-- A natural number's blob: little-endian bytes, no trailing zero (the
reader's `natural`). -/
def natBytes (n : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := .empty
  let mut k := n
  while k > 0 do
    out := out.push (k % 256).toUInt8
    k := k / 256
  return out

def blobOf {md : Ix.Kernel.Mode} (bytes : ByteArray) : EgressM md UInt64 := do
  let a := Address.admissionHash bytes
  unless (← get).blobs.any (·.1 == a) do
    modify fun s => { s with blobs := s.blobs.push (a, bytes) }
  refOf a

/-- How often each node occurs in `e`'s DAG (each parent edge counted once
per distinct parent). -/
partial def countUses {md : Ix.Kernel.Mode} (e : CExpr md) : StateM (Std.HashMap (CExpr md) Nat) Unit := do
  let seen := (← get)[e]?
  modify fun m => m.insert e (seen.getD 0 + 1)
  if seen.isSome then return
  match e with
  | .app f a => countUses f; countUses a
  | .lam t b _ | .forallE t b _ => countUses t; countUses b
  | .letE t v b _ => countUses t; countUses v; countUses b
  | .proj _ _ x => countUses x
  | .fvar _ t => countUses t
  | _ => pure ()

/-- An expression as an Ixon expression under the writer's tables: every
node used more than once (and not a leaf) becomes a sharing entry, written
after the entries it uses. `addrOf` names a constant's record. -/
partial def egress {md : Ix.Kernel.Mode} (uses : Std.HashMap (CExpr md) Nat)
    (addrOf : CName md → Option Address) (e : CExpr md) : EgressM md Ixon.Expr := do
  let leaf := match e with
    | .bvar _ | .sort _ | .const .. | .lit _ => true
    | _ => false
  if !leaf && uses.getD e 0 > 1 then
    if let some i := (← get).shareIdx[e]? then return .share i.toUInt64
    let x ← build
    let i := (← get).sharing.size
    modify fun s => { s with sharing := s.sharing.push x, shareIdx := s.shareIdx.insert e i }
    return .share i.toUInt64
  build
where
  build : EgressM md Ixon.Expr := do
    match e with
    | .bvar i => pure (.var i.toUInt64)
    | .sort u => pure (.sort (← univOf u))
    | .const n us =>
      let some a := addrOf n | throw s!"no record for constant {n}"
      pure (.ref (← refOf a) (← us.toArray.mapM univOf))
    | .app f a => pure (.app (← egress uses addrOf f) (← egress uses addrOf a))
    | .lam t b m => pure (.lam m.contract (← egress uses addrOf t) (← egress uses addrOf b))
    | .forallE t b m =>
      pure (.all m.contract m.result (← egress uses addrOf t) (← egress uses addrOf b))
    | .letE t v b l =>
      pure (.letE l.contract (← egress uses addrOf t) (← egress uses addrOf v) (← egress uses addrOf b))
    | .lit (.natVal n) => pure (.nat (← blobOf (natBytes n)))
    | .lit (.strVal s) => pure (.str (← blobOf s.toUTF8))
    | .proj s i x =>
      let some a := addrOf s | throw s!"no record for structure {s}"
      pure (.prj (← refOf a) i.toUInt64 (← egress uses addrOf x))
    | .fvar .. => throw "a free variable in a proof"

/-- **A theorem record** with statement `type` and proof `value`: level
monomorphic, safe, its constants named through `addrOf`. -/
def theoremRecord {md : Ix.Kernel.Mode} (addrOf : CName md → Option Address) (type value : CExpr md) :
    Except String (Ixon.Constant × Array (Address × ByteArray)) := do
  let uses := ((countUses type *> countUses value).run {}).2
  let ((typ, val), eg) ← (do
      let t ← egress uses addrOf type
      let v ← egress uses addrOf value
      pure (t, v) : EgressM md _).run {}
  let c : Ixon.Constant :=
    { info := .defn { kind := .thm, safety := .safe, lvls := 0, typ, value := val },
      sharing := eg.sharing, refs := eg.refs, univs := eg.univs }
  pure (c, eg.blobs)

end Ix.RoleBinding.Evidence
