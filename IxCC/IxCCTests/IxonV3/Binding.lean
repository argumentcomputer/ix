import IxCC.Ixon.V3.Env
import IxCC.Src.Ingress
import IxCC.Src.Hints
import IxCC.Src.Table.Check
import IxCCTests.IxonV3.Catalog.Fixtures

/-! # Role-bound environments

`tests-ixon-v3` runs `Binding.run`: the binding section's decoder against
sections written in the kernel's grammar (`IxCK/Kernel/Ixon/RoleTable.lean`)
and their refusals; the role-bound envelope (`0xE5`) against the unbound one
of the same closure, and its refusals; the pins a role table gives, an
identity whose role the table does not bind being absent; the refusal of a
projection record that names no block member; a catalog's refusal of a
role-bound piece; and, on the role-bound fixtures `ix compile` writes
(`fixtures/ixon-v4/bound`), the binding, its pins against the fixed table and
the program ingress reads (`IxCC/docs/byte-contract.md`). -/

namespace IxCCTests.IxonV3.Binding

open IxCC.Ixon IxCC.Ixon.V3 IxCC.Src

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"role binding: {message}")

private def errorOf {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-- A binding section in the kernel's grammar: roles by index, evidence
`none` for definitional and `some a` for a proof. -/
def sectionBytes (version : Nat) (bound : List (Nat × IxCC.Ixon.Address))
    (evidence : List (Nat × List (Option IxCC.Ixon.Address))) : ByteArray :=
  let addr := fun (a : IxCC.Ixon.Address) => a.hash.data.toList
  let ev := fun (e : Option IxCC.Ixon.Address) => match e with
    | none => [(0 : UInt8)]
    | some a => (1 : UInt8) :: addr a
  let bytes : List UInt8 :=
    [(0xE8 : UInt8), 0x03, version.toUInt8, bound.length.toUInt8] ++
      bound.flatMap (fun (r, a) => r.toUInt8 :: addr a) ++
      [evidence.length.toUInt8] ++
      evidence.flatMap (fun (r, es) => r.toUInt8 :: es.length.toUInt8 :: es.flatMap ev)
  ⟨bytes.toArray⟩

/-- `env` in the envelope ix writes: role-bound, with `binding`'s address,
length and bytes after the assumptions, when it is given; with the root
recomputed from the constants. -/
def envelope (env : Env) (binding : Option (IxCC.Ixon.Address × ByteArray)) : ByteArray :=
  _root_.Ixon.runPut do
    let constants := env.consts.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
    let blobs := env.blobs.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
    _root_.Ixon.putTagN 4 0xE (if binding.isSome then boundEnvVersion else envVersion)
    _root_.Ixon.putBytes (Merkle.rootCanonicalBy IxCC.Ixon.Address.blake3Pure (constants.map Prod.fst)).hash
    match env.main with
    | none => _root_.Ixon.putU8 0
    | some a => _root_.Ixon.putU8 1; _root_.Ixon.putBytes a.hash
    _root_.Ixon.putTagN 0 0 env.assumptions.size.toUInt64
    for a in env.assumptions do _root_.Ixon.putBytes a.hash
    if let some (address, bytes) := binding then
      _root_.Ixon.putBytes address.hash
      _root_.Ixon.putTagN 0 0 bytes.size.toUInt64
      _root_.Ixon.putBytes bytes
    for table in #[blobs, constants] do
      _root_.Ixon.putTagN 0 0 table.size.toUInt64
      for (address, raw) in table do
        _root_.Ixon.putBytes address.hash
        _root_.Ixon.putTagN 0 0 raw.size.toUInt64
        _root_.Ixon.putBytes raw
    let hints := env.hints.qsort (fun a b => Merkle.addressLT a.1 b.1)
    _root_.Ixon.putTagN 0 0 hints.size.toUInt64
    let mut cursor := 0
    for (address, hint) in hints do
      let index := (constants.findIdx? (·.1 == address)).getD 0
      _root_.Ixon.putTagN 0 0 (index + 1 - cursor).toUInt64
      _root_.Ixon.putTagN 0 0 hint
      cursor := index + 1
    _root_.Ixon.putBytes env.metadata

/-- The kernel's role indices this suite writes (positions in `Role.all`). -/
def natIdx : Nat := roleIdx .nat
def boolIdx : Nat := roleIdx .bool

/-- The section decoder: the grammar, and every refusal the kernel's decoder
makes. -/
def sections : IO Nat := do
  let a1 := IxCC.Ixon.Address.replicate 1
  let a2 := IxCC.Ixon.Address.replicate 2
  let a3 := IxCC.Ixon.Address.replicate 3
  require (natIdx == 0 && boolIdx == 4 && roleIdx .natAdd == 42 && roleIdx .stringBack == 102 &&
    Ix.Kernel.Role.all.length == 103) "the kernel's role indices moved"
  let good := sectionBytes 3 [(natIdx, a1), (boolIdx, a2)] [(roleIdx .natAdd, [none, some a3])]
  let some t := RoleTable.decode good.data.toList | throw (IO.userError "role binding: section refused")
  require (t.version == 3 && t.bound.map (·.1) == [.nat, .bool] && t.bound.map (·.2) == [a1, a2])
    "bound roles misread"
  require (t.evidence.map (·.1) == [.natAdd] &&
    t.evidence.map (·.2) == [[RoleEvidence.defeq, .proof a3]]) "evidence misread"
  require (t.addressOf? .bool == some a2 && t.addressOf? .eq == none) "addressOf?"
  let refused := fun (label : String) (bytes : ByteArray) =>
    require (RoleTable.decode bytes.data.toList).isNone s!"accepted {label}"
  refused "descending roles" (sectionBytes 3 [(boolIdx, a1), (natIdx, a2)] [])
  refused "a repeated role" (sectionBytes 3 [(natIdx, a1), (natIdx, a2)] [])
  refused "descending evidence" (sectionBytes 3 [] [(roleIdx .natMul, []), (roleIdx .natAdd, [])])
  refused "an unknown role" (sectionBytes 3 [(103, a1)] [])
  refused "a trailing byte" (good.push 0)
  refused "another tag" (good.set! 1 0x02)
  refused "an unknown evidence kind" (sectionBytes 3 [] [(roleIdx .natAdd, [none])] |>.set! 7 2)
  for length in [:good.size] do refused s!"a prefix of {length} bytes" (good.extract 0 length)
  let twice := sectionBytes 3 [(natIdx, a1), (boolIdx, a1)] []
  require ((errorOf (Binding.ofSection (IxCC.Ixon.Address.blake3Pure twice) twice)).endsWith
    "is bound to two roles") "an address bound to two roles"
  return 14 + good.size

/-- The role-bound envelope of a committed closure: the same anonymous
sections and the binding; its refusals. -/
def envelopes (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "bench-k1/fib.ixe")
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  require (envelope env none == raw) "the test writer does not reproduce the unbound fixture"
  require (!env.isBound) "an unbound fixture read as role-bound"
  let sec := sectionBytes 3 [(natIdx, IxCC.Ixon.Address.replicate 1)] []
  let address := IxCC.Ixon.Address.blake3Pure sec
  let bound := envelope env (some (address, sec))
  require (bound[0]! == 0xE5 && raw[0]! == 0xE4) "envelope header bytes"
  let benv ← IO.ofExcept (decodeAnonymousEnv bound)
  let some b := benv.binding | throw (IO.userError "role binding: binding not kept")
  require (b.address == address && b.bytes == sec && b.table.bound.length == 1) "binding not kept"
  require (benv.root == env.root && benv.consts.size == env.consts.size &&
    env.consts.toList.all (fun (a, bs) => benv.consts[a]? == some bs) &&
    benv.blobs.size == env.blobs.size && benv.hints == env.hints && benv.main == env.main &&
    benv.metadata == env.metadata) "the role-bound envelope read differently from the unbound one"
  let refusal := fun (label expected : String) (bytes : ByteArray) =>
    require ((errorOf (decodeAnonymousEnv bytes)).startsWith expected)
      s!"{label}: {errorOf (decodeAnonymousEnv bytes)}"
  refusal "a binding whose bytes do not hash to its address"
    "role binding: the section's bytes do not hash to its address"
    (envelope env (some (IxCC.Ixon.Address.replicate 7, sec)))
  let long := sec.push 0
  refusal "a noncanonical section" "role binding: not a canonical binding section"
    (envelope env (some (IxCC.Ixon.Address.blake3Pure long, long)))
  let twice := sectionBytes 3 [(natIdx, IxCC.Ixon.Address.replicate 1), (boolIdx, IxCC.Ixon.Address.replicate 1)] []
  refusal "an address bound twice" "role binding: address"
    (envelope env (some (IxCC.Ixon.Address.blake3Pure twice, twice)))
  let header := (envelope env none).extract 0 (1 + 32 + 1 + 1)
  let oversized := header.set! 0 0xE5 ++ (IxCC.Ixon.Address.replicate 1).hash ++
    _root_.Ixon.runPut (_root_.Ixon.putTagN 0 0 (RoleTable.maxBytes + 1).toUInt64)
  refusal "an oversized section" "role binding: the section exceeds the format's size" oversized
  require (decodeAnonymousEnv (raw.set! 0 0xE5)).toOption.isNone
    "a role-bound header without a binding"
  let swapped := bound.set! 0 0xE4
  require (decodeAnonymousEnv swapped).toOption.isNone "an unbound header over a binding"
  for header in [0xE3, 0xE6, 0xF5] do
    require (decodeAnonymousEnv (raw.set! 0 header.toUInt8)).toOption.isNone
      s!"envelope header {header}"
  return 15

/-- The pins of a role table: each identity with a role at the address the
table binds to it, none for a role it does not bind; the fixed table for an
unbound environment; the program ingress reads carries them. -/
def pins (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "bench-k1/fib.ixe")
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  require (reprStr (Pinned.pinsOf env) == reprStr Pins.fixed) "an unbound environment's pins"
  let at_ := fun (pin : Option Nat) => (pin.map Pinned.addrOfNat).getD (IxCC.Ixon.Address.replicate 0)
  -- Nat, its constructors and recursor, and Eq: not `Bool`, not the addition.
  let bound : List (Nat × IxCC.Ixon.Address) :=
    [(roleIdx .nat, at_ Pins.fixed.nat), (roleIdx .natZero, at_ Pins.fixed.natZero),
      (roleIdx .natSucc, at_ Pins.fixed.natSucc), (roleIdx .natRec, at_ Pins.fixed.natRec),
      (roleIdx .eq, at_ Pins.fixed.eq)]
  let sec := sectionBytes 3 bound []
  let benv ← IO.ofExcept (decodeAnonymousEnv (envelope env (some (IxCC.Ixon.Address.blake3Pure sec, sec))))
  let p ← IO.ofExcept (Ingress.ofEnv benv #[])
  let q ← IO.ofExcept (Ingress.ofEnv env #[])
  require (reprStr p.known.pins == reprStr (Pinned.pinsOf benv)) "ingress's pins (ofEnv_pins)"
  let ps := p.known.pins
  require (ps.nat == Pins.fixed.nat && ps.eq == Pins.fixed.eq && ps.bool == none &&
    ps.boolTrue == none && ps.decIsTrue == none) "pins of the bound roles and of the others"
  require (ps.prims.isEmpty && ps.prim? .add == none &&
    ps.stdAxioms.isEmpty && ps.opaqueByValue == Pins.fixed.opaqueByValue)
    "the primitives', the standard axioms' and the allowlist's pins"
  let kp := Pinned.known p
  let kq := Pinned.known q
  require (kp.nat == kq.nat && kp.natZero == kq.natZero && kp.natSucc == kq.natSucc &&
    kp.natRec == kq.natRec && kp.eq == kq.eq && kp.nat.isSome) "the bound identities resolve alike"
  require (kp.bool == none && kp.boolTrue == none && kp.decIsTrue == none)
    "an identity whose role is not bound is absent"
  let pk := { p with known := kp }
  require (Pinned.knownOk pk && Pinned.knownOk { q with known := kq }) "knownOk"
  require (!Pinned.knownOk { pk with known := { kp with bool := kq.nat } })
    "knownOk accepted an identity without a pin"
  -- A primitive without a pin is not a primitive.
  let some add := q.lookup (Pinned.primAddr .add) | throw (IO.userError "role binding: no Nat.add")
  require ((Table.checkPrim pk add .add PrimOp.all).toOption.isNone &&
    (Table.checkPrim { q with known := kq } add .add PrimOp.all).toOption.isSome)
    "a primitive whose role is not bound was accepted"
  require ((Pinned.primAt? ps (Pinned.primAddr .add)).isNone &&
    Pinned.primAt? Pins.fixed (Pinned.primAddr .add) == some .add) "primAt?"
  return 9

/-- A projection record that names no member of a block in the closure is
refused; one that names a member is an alias. -/
def projections (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "bench-k1/fib.ixe")
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  let dangling := constantBytes ⟨.dPrj ⟨0, IxCC.Ixon.Address.replicate 9⟩, #[], #[], #[]⟩
  let env' := { env with consts := env.consts.insert (IxCC.Ixon.Address.blake3Pure dangling) dangling }
  let decoded ← IO.ofExcept (decodeAnonymousEnv (envelope env' none))
  let message := errorOf (Ingress.ofEnv decoded #[])
  require (message.startsWith "src ingress: projection record" &&
    message.endsWith "names no member of a block in the closure")
    s!"a dangling projection record: {message}"
  let projectionCount := env.consts.toList.countP fun (_, bs) =>
    match decodeConstant bs with
    | .ok d => match d.value.info with
      | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => true
      | _ => false
    | .error _ => false
  require (projectionCount > 0 && (Ingress.ofEnv env #[]).toOption.isSome)
    "a closure with projection records"
  return 2

/-- A catalog's pieces are unbound. -/
def catalog (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "bench-k1/fib.ixe")
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  let sec := sectionBytes 3 [(natIdx, IxCC.Ixon.Address.replicate 1)] []
  let raws := #[envelope env (some (IxCC.Ixon.Address.blake3Pure sec, sec))]
  let m ← IO.ofExcept (CatalogFixtures.fat raws)
  match Catalog.load (CatalogFixtures.manifestBytes m) raws with
  | .ok _ => throw (IO.userError "role binding: a catalog accepted a role-bound piece")
  | .error e =>
    require ((reprStr e).contains "must be an unbound environment") s!"catalog refusal: {reprStr e}"
  let plain := #[raw]
  let mPlain ← IO.ofExcept (CatalogFixtures.fat plain)
  require (Catalog.load (CatalogFixtures.manifestBytes mPlain) plain).toOption.isSome
    "a catalog refused an unbound piece"
  return 2

/-- The pinned identities of a role-bound closure, by name: the role table's pin
and the fixed table's. -/
def pinPairs (t : RoleTable) : List (String × Option Nat × Option Nat) :=
  let rp := Pinned.ofRoles t
  let fp := Pins.fixed
  [("Nat", rp.nat, fp.nat), ("Nat.zero", rp.natZero, fp.natZero),
    ("Nat.succ", rp.natSucc, fp.natSucc), ("Nat.rec", rp.natRec, fp.natRec),
    ("Bool", rp.bool, fp.bool), ("Bool.true", rp.boolTrue, fp.boolTrue),
    ("Bool.false", rp.boolFalse, fp.boolFalse), ("Eq", rp.eq, fp.eq),
    ("Decidable.isFalse", rp.decIsFalse, fp.decIsFalse),
    ("Decidable.isTrue", rp.decIsTrue, fp.decIsTrue)] ++
  PrimOp.all.map (fun op => (op.name, rp.prim? op, fp.prim? op)) ++
  (Pinned.stdAxiomRoles.zip Pinned.stdAxiomRows).map (fun ((name, r), (_, hex)) =>
    (name, (t.addressOf? r).map Pinned.addrNat, some (Pinned.addrNat (Pinned.addr hex))))

/-- The role-bound closures `ix compile` writes (`fixtures/ixon-v4/bound`):
the binding is authenticated and read; every identity that both the role table
and the fixed table pin is pinned at the same address, and where the table
binds no role the fixed table's constant is absent from the closure; ingress
reads the program with the role table's pins, and its pinned identities
resolve to the constants the fixed table's would. -/
def boundFixtures (root : System.FilePath) : IO Nat := do
  let mut count := 0
  for name in ["tuple", "fib"] do
    let raw ← IO.FS.readBinFile (root / "bound" / s!"{name}.ixe")
    require (raw[0]! == 0xE5) s!"{name}: not a role-bound envelope"
    let env ← IO.ofExcept (decodeAnonymousEnv raw)
    let some b := env.binding | throw (IO.userError s!"role binding: {name}: no binding read")
    require (IxCC.Ixon.Address.blake3Pure b.bytes == b.address &&
      b.table.bound.length > 0) s!"{name}: binding"
    let present := fun (pin : Option Nat) => match pin with
      | some n => env.consts.contains (Pinned.addrOfNat n)
      | none => false
    for (label, r, f) in pinPairs b.table do
      require (r == f || (r.isNone && !present f))
        s!"{name}: the role table pins {label} differently from the fixed table"
      count := count + 1
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (root / "bound" / s!"{name}.equations.json")))
    let hints ← IO.ofExcept (Hints.ofK1Json json)
    let p ← IO.ofExcept (Ingress.ofEnv env (hints.roots.map (·.1)))
    require (reprStr p.known.pins == reprStr (Pinned.ofRoles b.table)) s!"{name}: ingress's pins"
    let kp := Pinned.known p
    let kf := Pinned.known { p with known := { pins := Pins.fixed } }
    require (reprStr { kp with pins := Pins.fixed } == reprStr kf && kp.nat.isSome)
      s!"{name}: the role table's and the fixed table's pins resolve differently"
    require (Pinned.knownOk { p with known := kp }) s!"{name}: knownOk"
    count := count + 4
  return count

def run (root : System.FilePath) : IO Nat := do
  return (← sections) + (← envelopes root) + (← pins root) + (← projections root) +
    (← catalog root) + (← boundFixtures root)

end IxCCTests.IxonV3.Binding
