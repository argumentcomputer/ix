import Ix.Compiler.IxIR0.Decode

/-!
# Cycle-safe IxIR₀ mutual-block identities

An ordinary declaration preimage spells every global edge as a 32-byte
address.  That representation cannot independently content-address two
declarations which refer to each other.  This module supplies the artifact
boundary for such a strongly connected component:

* references inside the ordered block are represented by a local member
  index;
* references outside the block retain their full address;
* the complete ordered symbolic block is hashed once; and
* each executable environment key is derived, with a separate domain, from
  the block hash and its member index.

`runCertified` converts transiently keyed IxIR₀ declarations to this form,
derives the final keys, materializes local edges, rejects every observed
namespace/hash collision, and retains an erased executable audit relating the
result to the input.  The hash calls are native, so successful runs belong at
compiled artifact boundaries and in `Tests.lean`, not elaboration-time
`#guard`s.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Address Owned Uses)
open Ix.Compiler.IxIR

namespace MutualBlock

/-! ## Symbolic block syntax -/

/-- A global edge in a mutual-block preimage. -/
inductive Ref where
  | local (index : Nat)
  | external (address : Address)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- IxIR₀ expressions with block-local references made explicit. -/
inductive Expr where
  | var (index : Nat)
  | ref (target : Ref)
  | app (fn arg : Expr)
  | lam (uses : Uses) (body : Expr)
  | letE (uses : Uses) (value body : Expr)
  | proj (index : Nat) (struct : Expr)
  | lit (literal : IxIR0.Literal)
  | erased
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-- A recursor rule in a symbolic mutual block. -/
structure RecRule where
  fields : Nat
  rhs : Expr
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-- A declaration in a symbolic mutual block. -/
inductive Decl where
  | defn (result : Owned) (body : Expr)
  | ctor (tag arity : Nat)
  | recursor (numArgs : Nat) (natLit : Bool) (rules : Array RecRule)
  | extern (arity : Nat)
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-! ## Temporary-name abstraction -/

/-- Return the first zero-based position of an address.  Successful block
construction rejects duplicate keys, so the first position is the unique
position at that boundary. -/
def localIndex? (keys : List Address) (address : Address) : Option Nat :=
  let rec loop : Nat → List Address → Option Nat
    | _, [] => none
    | index, key :: rest =>
        if key == address then some index else loop (index + 1) rest
  loop 0 keys

namespace Ref

/-- Classify one concrete address against the ordered temporary namespace. -/
def abstract (keys : List Address) (address : Address) : Ref :=
  match localIndex? keys address with
  | some index => .local index
  | none => .external address

/-- Concrete external references carried by a symbolic edge. -/
def externalReferences : Ref → List Address
  | .local _ => []
  | .external address => [address]

/-- Whether every local edge lies within the block. -/
def wellScoped (memberCount : Nat) : Ref → Bool
  | .local index => index < memberCount
  | .external _ => true

/-- Resolve a symbolic edge against the final ordered member keys. -/
def materialize (memberKeys : Array Address) : Ref → Except String Address
  | .local index =>
      match memberKeys[index]? with
      | some address => .ok address
      | none => .error s!"mutual-block local reference {index} is out of range"
  | .external address => .ok address

end Ref

namespace Expr

/-- Replace concrete references by local indices whenever they name a member
of the same block. -/
def abstract (keys : List Address) : IxIR0.Expr → Expr
  | .var index => .var index
  | .ref address => .ref (Ref.abstract keys address)
  | .app fn arg => .app (abstract keys fn) (abstract keys arg)
  | .lam uses body => .lam uses (abstract keys body)
  | .letE uses value body =>
      .letE uses (abstract keys value) (abstract keys body)
  | .proj index struct => .proj index (abstract keys struct)
  | .lit literal => .lit literal
  | .erased => .erased

/-- Materialize every local edge using the final member-key array. -/
def materialize (memberKeys : Array Address) : Expr → Except String IxIR0.Expr
  | .var index => .ok (.var index)
  | .ref target => return .ref (← target.materialize memberKeys)
  | .app fn arg =>
      return .app (← materialize memberKeys fn)
        (← materialize memberKeys arg)
  | .lam uses body => return .lam uses (← materialize memberKeys body)
  | .letE uses value body =>
      return .letE uses (← materialize memberKeys value)
        (← materialize memberKeys body)
  | .proj index struct =>
      return .proj index (← materialize memberKeys struct)
  | .lit literal => .ok (.lit literal)
  | .erased => .ok .erased

/-- Concrete external references carried anywhere in a symbolic expression. -/
def externalReferences : Expr → List Address
  | .var _ => []
  | .ref target => target.externalReferences
  | .app fn arg => externalReferences fn ++ externalReferences arg
  | .lam _ body => externalReferences body
  | .letE _ value body =>
      externalReferences value ++ externalReferences body
  | .proj _ struct => externalReferences struct
  | .lit _ | .erased => []

/-- Executable local-scope check. -/
def wellScoped (memberCount : Nat) : Expr → Bool
  | .var _ => true
  | .ref target => target.wellScoped memberCount
  | .app fn arg => wellScoped memberCount fn && wellScoped memberCount arg
  | .lam _ body => wellScoped memberCount body
  | .letE _ value body =>
      wellScoped memberCount value && wellScoped memberCount body
  | .proj _ struct => wellScoped memberCount struct
  | .lit _ | .erased => true

end Expr

namespace RecRule

def abstract (keys : List Address) (rule : IxIR0.RecRule) : RecRule :=
  { fields := rule.fields, rhs := Expr.abstract keys rule.rhs }

def materialize (memberKeys : Array Address)
    (rule : RecRule) : Except String IxIR0.RecRule :=
  return { fields := rule.fields, rhs := ← rule.rhs.materialize memberKeys }

def externalReferences (rule : RecRule) : List Address :=
  rule.rhs.externalReferences

def wellScoped (memberCount : Nat) (rule : RecRule) : Bool :=
  rule.rhs.wellScoped memberCount

end RecRule

namespace Decl

/-- Abstract one ordinary IxIR₀ declaration against an ordered member-key
namespace. -/
def abstract (keys : List Address) : IxIR0.Decl → Decl
  | .defn result body => .defn result (Expr.abstract keys body)
  | .ctor tag arity => .ctor tag arity
  | .recursor numArgs natLit rules =>
      .recursor numArgs natLit (rules.map (RecRule.abstract keys))
  | .extern arity => .extern arity

/-- Materialize one symbolic declaration using final member keys. -/
def materialize (memberKeys : Array Address) : Decl → Except String IxIR0.Decl
  | .defn result body => return .defn result (← body.materialize memberKeys)
  | .ctor tag arity => .ok (.ctor tag arity)
  | .recursor numArgs natLit rules =>
      return .recursor numArgs natLit
        (← rules.mapM (RecRule.materialize memberKeys))
  | .extern arity => .ok (.extern arity)

def externalReferences : Decl → List Address
  | .defn _ body => body.externalReferences
  | .ctor _ _ | .extern _ => []
  | .recursor _ _ rules =>
      rules.toList.flatMap RecRule.externalReferences

def wellScoped (memberCount : Nat) : Decl → Bool
  | .defn _ body => body.wellScoped memberCount
  | .ctor _ _ | .extern _ => true
  | .recursor _ _ rules =>
      rules.all (RecRule.wellScoped memberCount)

end Decl

/-- Abstract the declarations of a transiently keyed ordered block.  Keys are
not serialized; they are used only to recognize local edges. -/
def abstractMembers (members : List (Address × IxIR0.Decl)) : List Decl :=
  let keys := members.map (·.1)
  members.map fun member => Decl.abstract keys member.2

/-! ## Canonical bytes and cryptographic identities -/

namespace Ref

/-- Canonical reference payload.  The tag distinguishes local indices from
full external addresses. -/
def bytes : Ref → ByteArray
  | .local index => Encoding.tag 0 ++ Encoding.nat index
  | .external address => Encoding.tag 1 ++ Encoding.address address

end Ref

namespace Expr

/-- Canonical symbolic expression payload. -/
def bytes : Expr → ByteArray
  | .var index => Encoding.tag 0 ++ Encoding.nat index
  | .ref target => Encoding.tag 1 ++ target.bytes
  | .app fn arg => Encoding.tag 2 ++ bytes fn ++ bytes arg
  | .lam uses body =>
      Encoding.tag 3 ++ Encoding.tag uses.toBits ++ bytes body
  | .letE uses value body =>
      Encoding.tag 4 ++ Encoding.tag uses.toBits ++
        bytes value ++ bytes body
  | .proj index struct =>
      Encoding.tag 5 ++ Encoding.nat index ++ bytes struct
  | .lit literal => Encoding.tag 6 ++ IxIR0.Literal.bytes literal
  | .erased => Encoding.tag 7

end Expr

namespace RecRule

def bytes (rule : RecRule) : ByteArray :=
  Encoding.nat rule.fields ++ rule.rhs.bytes

end RecRule

namespace Decl

/-- Canonical symbolic declaration payload. -/
def bytes : Decl → ByteArray
  | .defn result body =>
      Encoding.tag 0 ++ Encoding.tag result.toBits ++ body.bytes
  | .ctor tag arity =>
      Encoding.tag 1 ++ Encoding.nat tag ++ Encoding.nat arity
  | .recursor numArgs natLit rules =>
      Encoding.tag 2 ++ Encoding.nat numArgs ++ Encoding.bool natLit ++
        Encoding.array RecRule.bytes rules
  | .extern arity => Encoding.tag 3 ++ Encoding.nat arity

end Decl

namespace Block

/-- Versioned domain for a complete ordered IxIR₀ mutual block. -/
def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir0/mutual-block/1" ++ Encoding.tag 0

/-- Complete canonical mutual-block hash preimage. -/
def preimage (members : List Decl) : ByteArray :=
  addressDomain ++ Encoding.list Decl.bytes members

/-- Content identity of a complete symbolic mutual block. -/
def address (members : List Decl) : Address :=
  Address.blake3 (preimage members)

/-- Block-address equality exposes exact preimage equality under the one
pairwise cryptographic premise actually needed. -/
theorem address_eq_iff_preimage_eq (left right : List Decl)
    (hcollision : Address.Blake3NoCollision (preimage left) (preimage right)) :
    address left = address right ↔ preimage left = preimage right := by
  constructor
  · exact hcollision
  · intro h
    simp only [address]
    rw [h]

end Block

namespace Member

/-- Versioned domain for a member key derived from a mutual-block identity. -/
def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir0/mutual-member/1" ++ Encoding.tag 0

/-- Canonical member-key preimage. -/
def preimage (block : Address) (index : Nat) : ByteArray :=
  addressDomain ++ Encoding.address block ++ Encoding.nat index

/-- Derive one executable declaration key from its block and local index. -/
def address (block : Address) (index : Nat) : Address :=
  Address.blake3 (preimage block index)

/-- Member-address equality exposes exact preimage equality under the one
pairwise cryptographic premise actually needed. -/
theorem address_eq_iff_preimage_eq (leftBlock rightBlock : Address)
    (leftIndex rightIndex : Nat)
    (hcollision : Address.Blake3NoCollision
      (preimage leftBlock leftIndex) (preimage rightBlock rightIndex)) :
    address leftBlock leftIndex = address rightBlock rightIndex ↔
      preimage leftBlock leftIndex = preimage rightBlock rightIndex := by
  constructor
  · exact hcollision
  · intro h
    simp only [address]
    rw [h]

end Member

/-! ## Strict block-preimage decoder -/

open Ix.Compiler.IxIR.Decode
open Ix.Compiler.Ixon

def getRefTag : UInt8 → GetM Ref
  | 0 => do return .local (← Decode.getNat)
  | 1 => do return .external (← Decode.getAddress)
  | tag => throw s!"IxIR0 mutual-block reference: invalid tag {tag}"

def getRef : GetM Ref := do
  getRefTag (← getU8)

def getExprTag (recur : GetM Expr) : UInt8 → GetM Expr
  | 0 => do return .var (← Decode.getNat)
  | 1 => do return .ref (← getRef)
  | 2 => do return .app (← recur) (← recur)
  | 3 => do return .lam (← IxIR0.getUses) (← recur)
  | 4 => do
      let uses ← IxIR0.getUses
      let value ← recur
      return .letE uses value (← recur)
  | 5 => do return .proj (← Decode.getNat) (← recur)
  | 6 => do return .lit (← IxIR0.getLiteral)
  | 7 => pure .erased
  | tag => throw s!"IxIR0 mutual-block expression: invalid tag {tag}"

def getExprFuel : Nat → GetM Expr
  | 0 => throw "IxIR0 mutual-block expression: recursion limit"
  | fuel + 1 => do
      getExprTag (getExprFuel fuel) (← getU8)

def getExpr : GetM Expr := do
  let state ← get
  getExprFuel (state.bytes.size + 1)

def getRecRule : GetM RecRule := do
  return ⟨← Decode.getNat, ← getExpr⟩

def getDeclTag : UInt8 → GetM Decl
  | 0 => do return .defn (← IxIR0.getOwned) (← getExpr)
  | 1 => do return .ctor (← Decode.getNat) (← Decode.getNat)
  | 2 => do
      let numArgs ← Decode.getNat
      let natLit ← Decode.getBool
      return .recursor numArgs natLit (← Decode.getArray getRecRule)
  | 3 => do return .extern (← Decode.getNat)
  | tag => throw s!"IxIR0 mutual-block declaration: invalid tag {tag}"

def getDecl : GetM Decl := do
  getDeclTag (← getU8)

def getBlockPreimage : GetM (List Decl) := do
  Decode.expectBytes Block.addressDomain
  Decode.getList getDecl

/-- Decode one complete canonical symbolic block preimage.  This is the codec
layer and therefore accepts an empty list or a syntactically valid
out-of-range local edge; `decodeArtifact` applies those semantic checks. -/
def Block.decodePreimage (bytes : ByteArray) : Except String (List Decl) :=
  Decode.runCanonical getBlockPreimage Block.preimage bytes

/-- Decode and validate an artifact-shaped block. -/
def Block.decodeArtifact (bytes : ByteArray) : Except String (List Decl) := do
  let members ← Block.decodePreimage bytes
  if members.isEmpty then
    throw "mutual block must contain at least one member"
  unless members.all (Decl.wellScoped members.length) do
    throw "mutual block contains an out-of-range local reference"
  return members

/-! ### Cursor-relative decoder proofs -/

theorem getRef_spec : ∀ target : Ref, GetSpec getRef target.bytes target
  | .local index => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec index) Ref.local
      have htotal := GetSpec.bind (next := getRefTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getRef, Ref.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .external address => by
      have hpayload := Decode.getSpecMap
        (Decode.getAddress_spec address) Ref.external
      have htotal := GetSpec.bind (next := getRefTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getRef, Ref.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

/-- Recursive parser depth.  Every encoded symbolic expression has at least
this many constructor-tag bytes along its deepest branch. -/
def Expr.decodeDepth : Expr → Nat
  | .var _ | .ref _ | .lit _ | .erased => 1
  | .app function argument =>
      1 + Nat.max function.decodeDepth argument.decodeDepth
  | .lam _ body => 1 + body.decodeDepth
  | .letE _ value body =>
      1 + Nat.max value.decodeDepth body.decodeDepth
  | .proj _ target => 1 + target.decodeDepth

theorem Expr.decodeDepth_le_bytes (expression : Expr) :
    expression.decodeDepth ≤ expression.bytes.size := by
  induction expression with
  | var index => simp [Expr.decodeDepth, Expr.bytes]
  | ref target => simp [Expr.decodeDepth, Expr.bytes]
  | app function argument hfunction hargument =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      have hleft : function.decodeDepth ≤
          function.bytes.size + argument.bytes.size := by omega
      have hright : argument.decodeDepth ≤
          function.bytes.size + argument.bytes.size := by omega
      have hmax : Nat.max function.decodeDepth argument.decodeDepth ≤
          function.bytes.size + argument.bytes.size :=
        Nat.max_le.mpr ⟨hleft, hright⟩
      omega
  | lam uses body hbody =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | letE uses value body hvalue hbody =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      have hleft : value.decodeDepth ≤ value.bytes.size + body.bytes.size := by
        omega
      have hright : body.decodeDepth ≤ value.bytes.size + body.bytes.size := by
        omega
      have hmax : Nat.max value.decodeDepth body.decodeDepth ≤
          value.bytes.size + body.bytes.size :=
        Nat.max_le.mpr ⟨hleft, hright⟩
      omega
  | proj index target htarget =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | lit literal =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | erased => simp [Expr.decodeDepth, Expr.bytes]

theorem getExprFuel_spec (expression : Expr) (fuel : Nat)
    (hfuel : expression.decodeDepth < fuel) :
    GetSpec (getExprFuel fuel) expression.bytes expression := by
  induction expression generalizing fuel with
  | var index =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap (Decode.getNat_spec index) Expr.var
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 0) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | ref target =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap (getRef_spec target) Expr.ref
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 1) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | app function argument hfunction hargument =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hmax : Nat.max function.decodeDepth argument.decodeDepth < fuel := by
            omega
          have hfunctionFuel : function.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
          have hargumentFuel : argument.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
          have hpayload := Decode.getSpecMap2
            (hfunction fuel hfunctionFuel) (hargument fuel hargumentFuel)
            Expr.app
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 2) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | lam uses body hbody =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hbodyFuel : body.decodeDepth < fuel := by omega
          have hpayload := Decode.getSpecMap2 (IxIR0.getUses_spec uses)
            (hbody fuel hbodyFuel) Expr.lam
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 3) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | letE uses value body hvalue hbody =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hmax : Nat.max value.decodeDepth body.decodeDepth < fuel := by
            omega
          have hvalueFuel : value.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
          have hbodyFuel : body.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
          have hpayload := Decode.getSpecMap3 (IxIR0.getUses_spec uses)
            (hvalue fuel hvalueFuel) (hbody fuel hbodyFuel) Expr.letE
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 4) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | proj index target htarget =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have htargetFuel : target.decodeDepth < fuel := by omega
          have hpayload := Decode.getSpecMap2 (Decode.getNat_spec index)
            (htarget fuel htargetFuel) Expr.proj
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 5) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | lit literal =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap
            (IxIR0.getLiteral_spec literal) Expr.lit
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 6) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | erased =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload : GetSpec (getExprTag (getExprFuel fuel) 7)
              ByteArray.empty Expr.erased := GetSpec.pure Expr.erased
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 7) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal

theorem getExpr_spec (expression : Expr) :
    GetSpec getExpr expression.bytes expression := by
  intro pre suffix
  let fuel := (pre ++ expression.bytes ++ suffix).size + 1
  have hfuel : expression.decodeDepth < fuel := by
    have hdepth := expression.decodeDepth_le_bytes
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  have hspec := getExprFuel_spec expression fuel hfuel pre suffix
  simpa [getExpr, fuel] using hspec

theorem getRecRule_spec (rule : RecRule) :
    GetSpec getRecRule rule.bytes rule := by
  have hspec := Decode.getSpecMap2 (Decode.getNat_spec rule.fields)
    (getExpr_spec rule.rhs) RecRule.mk
  simpa [getRecRule, RecRule.bytes] using hspec

theorem getDecl_spec : ∀ declaration : Decl,
    GetSpec getDecl declaration.bytes declaration
  | .defn result body => by
      have hpayload := Decode.getSpecMap2 (IxIR0.getOwned_spec result)
        (getExpr_spec body) Decl.defn
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .ctor tag arity => by
      have hpayload := Decode.getSpecMap2 (Decode.getNat_spec tag)
        (Decode.getNat_spec arity) Decl.ctor
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .recursor numArgs natLit rules => by
      have hpayload := Decode.getSpecMap3 (Decode.getNat_spec numArgs)
        (Decode.getBool_spec natLit)
        (Decode.getArray_spec getRecRule RecRule.bytes getRecRule_spec rules)
        Decl.recursor
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 2) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .extern arity => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec arity) Decl.extern
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 3) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

theorem getBlockPreimage_spec (members : List Decl) :
    GetSpec getBlockPreimage (Block.preimage members) members := by
  let next : Unit → GetM (List Decl) := fun _ => Decode.getList getDecl
  have htotal := GetSpec.bind (next := next)
    (Decode.expectBytes_spec Block.addressDomain)
    (Decode.getList_spec getDecl Decl.bytes getDecl_spec members)
  simpa [getBlockPreimage, Block.preimage, next] using htotal

/-! ### Strict top-level codec laws -/

/-- Every symbolic block decodes from its canonical framed preimage. -/
theorem Block.decodePreimage_roundtrip (members : List Decl) :
    Block.decodePreimage (Block.preimage members) = .ok members := by
  exact Decode.runCanonical_of_spec getBlockPreimage Block.preimage members
    (getBlockPreimage_spec members)

/-- Every accepted byte string is the canonical preimage of its result. -/
theorem Block.decodePreimage_canonical {bytes : ByteArray}
    {members : List Decl}
    (hdecode : Block.decodePreimage bytes = .ok members) :
    Block.preimage members = bytes := by
  exact Decode.runCanonical_canonical getBlockPreimage Block.preimage hdecode

/-- Canonical symbolic block preimages are injective. -/
theorem Block.preimage_injective : Function.Injective Block.preimage := by
  intro left right hbytes
  have hok : (Except.ok left : Except String (List Decl)) = .ok right := by
    calc
      .ok left = Block.decodePreimage (Block.preimage left) :=
        (Block.decodePreimage_roundtrip left).symm
      _ = Block.decodePreimage (Block.preimage right) :=
        congrArg Block.decodePreimage hbytes
      _ = .ok right := Block.decodePreimage_roundtrip right
  exact Except.ok.inj hok

/-! ## Materializing a transient block -/

/-- Old transient member key to final derived member key. -/
abbrev Renaming := List (Address × Address)

namespace Renaming

def lookup (mapping : Renaming) (address : Address) : Option Address :=
  (mapping.find? fun entry => entry.1 == address).map (·.2)

def apply (mapping : Renaming) (address : Address) : Address :=
  (mapping.lookup address).getD address

def contains (mapping : Renaming) (address : Address) : Bool :=
  mapping.any fun entry => entry.1 == address

end Renaming

namespace Concrete

namespace Expr

/-- Rename every concrete global edge in an ordinary IxIR₀ expression. -/
def mapAddresses (rename : Address → Address) : IxIR0.Expr → IxIR0.Expr
  | .var index => .var index
  | .ref address => .ref (rename address)
  | .app fn arg => .app (mapAddresses rename fn) (mapAddresses rename arg)
  | .lam uses body => .lam uses (mapAddresses rename body)
  | .letE uses value body =>
      .letE uses (mapAddresses rename value) (mapAddresses rename body)
  | .proj index struct => .proj index (mapAddresses rename struct)
  | .lit literal => .lit literal
  | .erased => .erased

def references : IxIR0.Expr → List Address
  | .var _ => []
  | .ref address => [address]
  | .app fn arg => references fn ++ references arg
  | .lam _ body => references body
  | .letE _ value body => references value ++ references body
  | .proj _ struct => references struct
  | .lit _ | .erased => []

end Expr

namespace RecRule

def mapAddresses (rename : Address → Address)
    (rule : IxIR0.RecRule) : IxIR0.RecRule :=
  { rule with rhs := Expr.mapAddresses rename rule.rhs }

def references (rule : IxIR0.RecRule) : List Address :=
  Expr.references rule.rhs

end RecRule

namespace Decl

def mapAddresses (rename : Address → Address) : IxIR0.Decl → IxIR0.Decl
  | .defn result body => .defn result (Expr.mapAddresses rename body)
  | .ctor tag arity => .ctor tag arity
  | .recursor numArgs natLit rules =>
      .recursor numArgs natLit (rules.map (RecRule.mapAddresses rename))
  | .extern arity => .extern arity

def references : IxIR0.Decl → List Address
  | .defn _ body => Expr.references body
  | .ctor _ _ | .extern _ => []
  | .recursor _ _ rules => rules.toList.flatMap RecRule.references

end Decl

end Concrete

/-- A completely materialized mutual-block result. -/
structure Result where
  blockAddress : Address
  blockMembers : List Decl
  members : List (Address × IxIR0.Decl)
  addressMap : Renaming

namespace Result

def transientAddresses (result : Result) : List Address :=
  result.addressMap.map (·.1)

def derivedAddresses (result : Result) : List Address :=
  result.addressMap.map (·.2)

/-- Every recorded destination is the domain-separated derivation at its
position, and the emitted key list is exactly that destination list. -/
def memberKeysDerived (result : Result) : Bool :=
  let rec loop : Nat → Renaming → Bool
    | _, [] => true
    | index, entry :: rest =>
        entry.2 == Member.address result.blockAddress index &&
          loop (index + 1) rest
  loop 0 result.addressMap &&
    result.members.map (·.1) == result.derivedAddresses

/-- Re-abstracting the final declarations recovers the exact canonical
symbolic block. -/
def blockStable (result : Result) : Bool :=
  abstractMembers result.members == result.blockMembers

def noTransientKeys (result : Result) : Bool :=
  !(result.members.map (·.1)).any result.transientAddresses.contains

def noTransientReferences (result : Result) : Bool :=
  let references := result.members.flatMap fun member =>
    Concrete.Decl.references member.2
  !references.any result.transientAddresses.contains

/-- Executable certificate that the materialized environment is exactly the
address-renamed image of the transient environment and that the symbolic
artifact remains stable after materialization. -/
def semanticAudit (result : Result)
    (raw : List (Address × IxIR0.Decl)) : Bool :=
  let rename := Renaming.apply result.addressMap
  let original := IxIR0.Env.ofList raw
  let emitted := IxIR0.Env.ofList result.members
  result.blockMembers == abstractMembers raw &&
    result.blockAddress == Block.address result.blockMembers &&
    result.memberKeysDerived && result.blockStable &&
    result.noTransientKeys && result.noTransientReferences &&
    raw.all (fun entry =>
      match original entry.1, emitted (rename entry.1) with
      | some before, some after =>
          after == Concrete.Decl.mapAddresses rename before
      | _, _ => false) &&
    result.members.all (fun entry =>
      match emitted entry.1 with
      | some declaration =>
          Concrete.Decl.mapAddresses rename declaration == declaration
      | none => false)

end Result

/-- A successful block construction carries its runtime-erased audit. -/
abbrev CertifiedResult (raw : List (Address × IxIR0.Decl)) :=
  { result : Result // result.semanticAudit raw = true }

private def firstDuplicate? : List Address → Option Address
  | [] => none
  | address :: rest =>
      if rest.contains address then some address else firstDuplicate? rest

private def firstOverlap? (left right : List Address) : Option Address :=
  left.find? right.contains

private def deriveMap (block : Address) :
    Nat → List (Address × IxIR0.Decl) → Renaming
  | _, [] => []
  | index, member :: rest =>
      (member.1, Member.address block index) :: deriveMap block (index + 1) rest

/-- A decoded and materialized block artifact, independent of any transient
producer namespace. -/
structure Artifact where
  blockAddress : Address
  blockMembers : List Decl
  members : List (Address × IxIR0.Decl)

namespace Artifact

def memberKeysDerived (artifact : Artifact) : Bool :=
  let rec loop : Nat → List (Address × IxIR0.Decl) → Bool
    | _, [] => true
    | index, member :: rest =>
        member.1 == Member.address artifact.blockAddress index &&
          loop (index + 1) rest
  loop 0 artifact.members

def stable (artifact : Artifact) : Bool :=
  abstractMembers artifact.members == artifact.blockMembers

def audit (artifact : Artifact) : Bool :=
  artifact.blockAddress == Block.address artifact.blockMembers &&
    artifact.members.length == artifact.blockMembers.length &&
    artifact.blockMembers.all
      (Decl.wellScoped artifact.blockMembers.length) &&
    artifact.memberKeysDerived && artifact.stable

end Artifact

private def deriveKeys (block : Address) : Nat → Nat → List Address
  | _, 0 => []
  | index, count + 1 =>
      Member.address block index :: deriveKeys block (index + 1) count

/-- Validate and materialize already-symbolic members, as used after decoding
a stored block. -/
def Block.materializeArtifact (reserved : List Address)
    (blockMembers : List Decl) : Except String Artifact := do
  if blockMembers.isEmpty then
    throw "mutual block must contain at least one member"
  unless blockMembers.all (Decl.wellScoped blockMembers.length) do
    throw "mutual block contains an out-of-range local reference"
  let blockAddress := Block.address blockMembers
  if reserved.contains blockAddress then
    throw s!"mutual-block identity collides with reserved identity {Address.toHex blockAddress}"
  let external := blockMembers.flatMap Decl.externalReferences
  if external.contains blockAddress then
    throw s!"mutual-block identity collides with an external reference {Address.toHex blockAddress}"
  let derived := deriveKeys blockAddress 0 blockMembers.length
  if let some duplicate := firstDuplicate? derived then
    throw s!"BLAKE3 collision between mutual-block member keys {Address.toHex duplicate}"
  if derived.contains blockAddress then
    throw s!"mutual-block member key collides with its block identity {Address.toHex blockAddress}"
  if let some overlap := firstOverlap? derived reserved then
    throw s!"mutual-block member key collides with reserved identity {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived external then
    throw s!"mutual-block member key captures an external reference {Address.toHex overlap}"
  let declarations ← blockMembers.mapM
    (Decl.materialize derived.toArray)
  let artifact : Artifact :=
    { blockAddress, blockMembers, members := derived.zip declarations }
  unless artifact.audit do
    throw "internal: decoded mutual block failed materialization audit"
  return artifact

/-- Strictly decode, scope-check, collision-check, and materialize a stored
mutual block. -/
def Block.decodeMaterialized (reserved : List Address)
    (bytes : ByteArray) : Except String Artifact := do
  Block.materializeArtifact reserved (← Block.decodeArtifact bytes)

private def certify (raw : List (Address × IxIR0.Decl))
    (result : Result) : Except String (CertifiedResult raw) :=
  if haudit : result.semanticAudit raw then .ok ⟨result, haudit⟩
  else .error "internal: mutual-block materialization failed semantic audit"

/-- Construct and certify a cycle-safe block while protecting all caller-owned
address identities.  `reserved` should contain every non-member declaration
or artifact key in the surrounding closed world.

The function rejects empty blocks, duplicate/overlapping temporary keys,
observed BLAKE3 collisions between derived members, and capture of any
temporary, external, reserved, or block-artifact identity. -/
def runCertified (reserved : List Address)
    (raw : List (Address × IxIR0.Decl)) :
    Except String (CertifiedResult raw) := do
  if raw.isEmpty then
    throw "mutual block must contain at least one member"
  let transient := raw.map (·.1)
  if let some duplicate := firstDuplicate? transient then
    throw s!"duplicate mutual-block temporary address {Address.toHex duplicate}"
  if let some overlap := firstOverlap? transient reserved then
    throw s!"mutual-block temporary address overlaps reserved identity {Address.toHex overlap}"
  let blockMembers := abstractMembers raw
  unless blockMembers.all (Decl.wellScoped blockMembers.length) do
    throw "internal: abstracted mutual block contains an out-of-range local reference"
  let blockAddress := Block.address blockMembers
  if transient.contains blockAddress then
    throw s!"mutual-block identity overlaps temporary namespace {Address.toHex blockAddress}"
  if reserved.contains blockAddress then
    throw s!"mutual-block identity collides with reserved identity {Address.toHex blockAddress}"
  let external := blockMembers.flatMap Decl.externalReferences
  if external.contains blockAddress then
    throw s!"mutual-block identity collides with an external reference {Address.toHex blockAddress}"
  let addressMap := deriveMap blockAddress 0 raw
  let derived := addressMap.map (·.2)
  if let some duplicate := firstDuplicate? derived then
    throw s!"BLAKE3 collision between mutual-block member keys {Address.toHex duplicate}"
  if derived.contains blockAddress then
    throw s!"mutual-block member key collides with its block identity {Address.toHex blockAddress}"
  if let some overlap := firstOverlap? derived transient then
    throw s!"mutual-block member key overlaps temporary namespace {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived reserved then
    throw s!"mutual-block member key collides with reserved identity {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived external then
    throw s!"mutual-block member key captures an external reference {Address.toHex overlap}"
  let memberKeys := derived.toArray
  let materialized ← blockMembers.mapM (Decl.materialize memberKeys)
  let members := derived.zip materialized
  let result : Result :=
    { blockAddress, blockMembers, members, addressMap }
  certify raw result

/-- Artifact-facing projection of `runCertified`. -/
def run (reserved : List Address)
    (raw : List (Address × IxIR0.Decl)) : Except String Result := do
  return (← runCertified reserved raw).1

/-- Every successful artifact-facing run retains the erased semantic audit
constructed by `runCertified`. -/
theorem semanticAudit_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × IxIR0.Decl)}
    {result : Result} (hrun : run reserved raw = .ok result) :
    result.semanticAudit raw = true := by
  unfold run at hrun
  cases hcertified : runCertified reserved raw with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2

/-! Pure structural format guards.  Digest and executable construction
fixtures live in the compiled test executable. -/

private def fixtureA : Address := Address.replicate 0xfa
private def fixtureB : Address := Address.replicate 0xfb
private def fixtureExternal : Address := Address.replicate 0xee

#guard Ref.bytes (.local 128) == ByteArray.mk #[0, 128, 1]
#guard (Ref.bytes (.external fixtureExternal)).size == 33
#guard Expr.bytes (.ref (.local 1)) == ByteArray.mk #[1, 0, 1]
#guard Decl.bytes (.defn .shared (.ref (.local 1))) ==
  ByteArray.mk #[0, 1, 1, 0, 1]
#guard
  abstractMembers
    [(fixtureA, .defn .shared (.ref fixtureB)),
     (fixtureB, .defn .shared (.ref fixtureA))] ==
    [.defn .shared (.ref (.local 1)),
     .defn .shared (.ref (.local 0))]

end MutualBlock

end Ix.Compiler.IxIR0
