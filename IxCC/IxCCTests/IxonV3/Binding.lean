import IxCC.Ixon.V3.Env
import IxCC.Src.Ingress
import IxCC.Src.Hints
import IxCC.Src.Table.Check
import IxCC.Recheck.Produce
import IxCCTests.Support.Envelope

/-! # Role-bound environments

`tests-ixon-v3` runs `Binding.run`: sections written in the kernel's grammar
(`IxCK/Kernel/Ixon/RoleTable.lean`) against the kernel's decoder, which IxCC
reads the binding with, and its refusals; the role-bound envelope (`0xE5`)
against the unbound one of the same closure, and the refusals of IxCC's
decoder and of the kernel's acceptance; the pins a role table gives
(`KernelFront.pinsOfTable`), an identity whose role the table does not bind
being absent; the refusal of a projection record that names no block member;
and, on two committed closures (every committed closure is role-bound, as
`ix compile` writes it; the unbound envelope is the same closure without its
binding), the binding as the kernel decodes it, its pins against the fixed
table and the program ingress reads (`IxCC/docs/byte-contract.md`). -/

namespace IxCCTests.IxonV3.Binding

open IxCC.Ixon IxCC.Ixon.V3 IxCC.Src
open IxCCTests.Support.Envelope

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

/-- The unbound twin of `bench-k1/fib`. -/
def unboundFib (root : System.FilePath) : IO ByteArray := unboundTwin (root / "bench-k1/fib.ixe")

/-- The kernel's role indices this suite writes (positions in `Role.all`). -/
def roleIdx (r : Ix.Kernel.Role) : Nat := r.idx
def natIdx : Nat := roleIdx .nat
def boolIdx : Nat := roleIdx .bool

/-- The suite's section writer (`sectionBytes`) against the kernel's decoder
(`Ix.Kernel.RoleTable.ofBytes`), which IxCC reads the binding with: the
grammar, the decoder's refusals, and the table check's refusal of an address
bound to two roles (`Ix.Kernel.RoleTable.check`). -/
def sections : IO Nat := do
  let a1 := IxCC.Ixon.Address.replicate 1
  let a2 := IxCC.Ixon.Address.replicate 2
  let a3 := IxCC.Ixon.Address.replicate 3
  let k := KernelFront.kaddr
  require (natIdx == 0 && boolIdx == 4 && roleIdx .natAdd == 42 && roleIdx .stringBack == 102 &&
    Ix.Kernel.Role.all.length == 103) "the kernel's role indices moved"
  let good := sectionBytes 3 [(natIdx, a1), (boolIdx, a2)] [(roleIdx .natAdd, [none, some a3])]
  let some t := Ix.Kernel.RoleTable.ofBytes good | throw (IO.userError "role binding: section refused")
  require (t.version == 3 && t.bound.map (·.1) == #[.nat, .bool] && t.bound.map (·.2) == #[k a1, k a2])
    "bound roles misread"
  require (t.evidence.map (·.1) == #[.natAdd] &&
    t.evidence.map (·.2) == #[#[Ix.Kernel.Evidence.defeq, .proof (k a3)]]) "evidence misread"
  require (t.addressOf? .bool == some (k a2) && t.addressOf? .eq == none) "addressOf?"
  let refused := fun (label : String) (bytes : ByteArray) =>
    require (Ix.Kernel.RoleTable.ofBytes bytes).isNone s!"accepted {label}"
  refused "descending roles" (sectionBytes 3 [(boolIdx, a1), (natIdx, a2)] [])
  refused "a repeated role" (sectionBytes 3 [(natIdx, a1), (natIdx, a2)] [])
  refused "descending evidence" (sectionBytes 3 [] [(roleIdx .natMul, []), (roleIdx .natAdd, [])])
  refused "an unknown role" (sectionBytes 3 [(103, a1)] [])
  refused "a trailing byte" (good.push 0)
  refused "another tag" (good.set! 1 0x02)
  refused "an unknown evidence kind" (sectionBytes 3 [] [(roleIdx .natAdd, [none])] |>.set! 7 2)
  for length in [:good.size] do refused s!"a prefix of {length} bytes" (good.extract 0 length)
  let twice := sectionBytes 3 [(natIdx, a1), (boolIdx, a1)] []
  let some tt := Ix.Kernel.RoleTable.ofBytes twice | throw (IO.userError "role binding: section refused")
  require ((errorOf tt.check).endsWith "is bound to two roles") "an address bound to two roles"
  return 14 + good.size

/-- The role-bound envelope of a committed closure: the same anonymous
sections and the binding; IxCC's decoder's refusals (the hash, the size, the
header), and the kernel's acceptance's refusals of a section that is not a
canonical role table or binds an address twice. -/
def envelopes (root : System.FilePath) : IO Nat := do
  let committed ← IO.FS.readBinFile (root / "bench-k1/fib.ixe")
  let cenv ← IO.ofExcept (decodeAnonymousEnv committed)
  let some cb := cenv.binding | throw (IO.userError "role binding: bench-k1/fib is not role-bound")
  require (envelope cenv (some (cb.address, cb.bytes)) == committed)
    "the test writer does not reproduce the role-bound fixture"
  let raw := envelope cenv none
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  require (!env.isBound) "an unbound fixture read as role-bound"
  let sec := sectionBytes 3 [(natIdx, IxCC.Ixon.Address.replicate 1)] []
  let address := IxCC.Ixon.Address.blake3Pure sec
  let bound := envelope env (some (address, sec))
  require (bound[0]! == 0xE5 && raw[0]! == 0xE4) "envelope header bytes"
  let benv ← IO.ofExcept (decodeAnonymousEnv bound)
  let some b := benv.binding | throw (IO.userError "role binding: binding not kept")
  require (b.address == address && b.bytes == sec) "binding not kept"
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
  -- the committed closure's own table, made noncanonical or binding one address
  -- twice: IxCC's decoder keeps it, the kernel's acceptance refuses the binding
  let some ct := Ix.Kernel.RoleTable.ofBytes cb.bytes
    | throw (IO.userError "role binding: the kernel does not decode bench-k1/fib's binding")
  let kernelRefusal := fun (label expected : String) (secBytes : ByteArray) => do
    let tampered ← IO.ofExcept (decodeAnonymousEnv
      (envelope cenv (some (IxCC.Ixon.Address.blake3Pure secBytes, secBytes))))
    match KernelFront.accept tampered with
    | .ok _ => throw (IO.userError s!"role binding: {label}: the kernel accepted it")
    | .error r =>
      require (r.stage == .binding && (expected.isEmpty || (r.message.splitOn expected).length > 1))
        s!"{label}: {r.render}"
  kernelRefusal "a noncanonical section" "" (cb.bytes.push 0)
  let some (_, first) := ct.bound[0]? | throw (IO.userError "role binding: an empty committed table")
  let twice : Ix.Kernel.RoleTable := { ct with bound := ct.bound.modify 1 fun (r, _) => (r, first) }
  kernelRefusal "an address bound twice" "bound to two roles" twice.toBytes
  let header := (envelope env none).extract 0 (1 + 32 + 1 + 1)
  let oversized := header.set! 0 0xE5 ++ (IxCC.Ixon.Address.replicate 1).hash ++
    _root_.Ixon.runPut (_root_.Ixon.putTagN 0 0 (Binding.maxBytes + 1).toUInt64)
  refusal "an oversized section" "role binding: the section exceeds the format's size" oversized
  require (decodeAnonymousEnv (raw.set! 0 0xE5)).toOption.isNone
    "a role-bound header without a binding"
  let swapped := bound.set! 0 0xE4
  require (decodeAnonymousEnv swapped).toOption.isNone "an unbound header over a binding"
  for header in [0xE3, 0xE6, 0xF5] do
    require (decodeAnonymousEnv (raw.set! 0 header.toUInt8)).toOption.isNone
      s!"envelope header {header}"
  return 15


/-- The pins of a role table, as ingress takes them from the table the kernel
admitted (`KernelFront.pinsOfTable`): each identity with a role at the address
the table binds to it, none for a role it does not bind, the allowlist at its
fixed address. The program is the reading of every record of a committed closure
(`Ingress.readAll`); `q` keeps the default pins (the fixed table). -/
def pins (root : System.FilePath) : IO Nat := do
  let raw ← unboundFib root
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  let at_ := fun (pin : Option Nat) =>
    KernelFront.kaddr ((pin.map Pinned.addrOfNat).getD (IxCC.Ixon.Address.replicate 0))
  -- Nat, its constructors and recursor, and Eq: not `Bool`, not the addition.
  let t : Ix.Kernel.RoleTable := { version := 3, evidence := #[], bound :=
    #[(.nat, at_ Pins.fixed.nat), (.natZero, at_ Pins.fixed.natZero),
      (.natSucc, at_ Pins.fixed.natSucc), (.natRec, at_ Pins.fixed.natRec), (.eq, at_ Pins.fixed.eq)] }
  let q ← IO.ofExcept (Ingress.readAll env #[])
  let ps := KernelFront.pinsOfTable t
  let p := { q with known := { pins := ps } }
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
  return 8

/-- A projection record that names no member of a block in the closure is
refused by ingress's reading as compile paths run it (the records the seeds
reach, `Ingress.reach`, then `Ingress.readConsts`), the record reached as a
sidecar root would reach it; one that names a member is an alias. (On a compile
path the kernel's acceptance, which runs first, refuses such a record too.) -/
def projections (root : System.FilePath) : IO Nat := do
  let raw ← unboundFib root
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  let dangling := constantBytes ⟨.dPrj ⟨0, IxCC.Ixon.Address.replicate 9⟩, #[], #[], #[]⟩
  let danglingAddr := IxCC.Ixon.Address.blake3Pure dangling
  let env' := { env with consts := env.consts.insert danglingAddr dangling }
  let decoded ← IO.ofExcept (decodeAnonymousEnv (envelope env' none))
  let message := errorOf do
    let records ← Ingress.reach decoded { statement := #[danglingAddr] }
    Ingress.readConsts decoded records #[]
  require (message.startsWith "src ingress: projection record" &&
    message.endsWith "names no member of a block in the closure")
    s!"a dangling projection record: {message}"
  let projectionCount := env.consts.toList.countP fun (_, bs) =>
    match decodeConstant bs with
    | .ok d => match d.value.info with
      | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => true
      | _ => false
    | .error _ => false
  require (projectionCount > 0 && (Ingress.readAll env #[]).toOption.isSome)
    "a closure with projection records"
  return 2

/-- The pinned identities of a role-bound closure, by name: the pin of the
role table as the kernel decodes it (`KernelFront.pinsOfTable`) and the fixed
table's. -/
def pinPairs (t : Ix.Kernel.RoleTable) : List (String × Option Nat × Option Nat) :=
  let rp := KernelFront.pinsOfTable t
  let fp := Pins.fixed
  [("Nat", rp.nat, fp.nat), ("Nat.zero", rp.natZero, fp.natZero),
    ("Nat.succ", rp.natSucc, fp.natSucc), ("Nat.rec", rp.natRec, fp.natRec),
    ("Bool", rp.bool, fp.bool), ("Bool.true", rp.boolTrue, fp.boolTrue),
    ("Bool.false", rp.boolFalse, fp.boolFalse), ("Eq", rp.eq, fp.eq),
    ("Decidable.isFalse", rp.decIsFalse, fp.decIsFalse),
    ("Decidable.isTrue", rp.decIsTrue, fp.decIsTrue)] ++
  PrimOp.all.map (fun op => (op.name, rp.prim? op, fp.prim? op)) ++
  (Pinned.stdAxiomRoles.zip Pinned.stdAxiomRows).map (fun ((name, r), (_, hex)) =>
    (name, (t.addressOf? r).map KernelFront.addrNatK, some (Pinned.addrNat (Pinned.addr hex))))

/-- The role-bound closures `ix compile` writes (two committed fixtures, `phase1-scalar`'s
`tuple` and `bench-k1`'s `fib`):
the binding is authenticated and the kernel decodes it; every identity that
both its table and the fixed table pin is pinned at the same address, and where
the table binds no role the fixed table's constant is absent from the closure;
ingress reads the program with the pins of the table the kernel admitted, and
its pinned identities resolve to the constants the fixed table's would. -/
def boundFixtures (root : System.FilePath) : IO Nat := do
  let mut count := 0
  for (name, stem) in [("tuple", root / ".." / "corpus" / "phase1-scalar" / "tuple"), ("fib", root / "bench-k1" / "fib")] do
    let raw ← IO.FS.readBinFile (stem.toString ++ ".ixe")
    require (raw[0]! == 0xE5) s!"{name}: not a role-bound envelope"
    let env ← IO.ofExcept (decodeAnonymousEnv raw)
    let some b := env.binding | throw (IO.userError s!"role binding: {name}: no binding read")
    let some t := Ix.Kernel.RoleTable.ofBytes b.bytes
      | throw (IO.userError s!"role binding: {name}: the kernel does not decode the binding section")
    require (IxCC.Ixon.Address.blake3Pure b.bytes == b.address && t.bound.size > 0) s!"{name}: binding"
    let present := fun (pin : Option Nat) => match pin with
      | some n => env.consts.contains (Pinned.addrOfNat n)
      | none => false
    for (label, r, f) in pinPairs t do
      require (r == f || (r.isNone && !present f))
        s!"{name}: the role table pins {label} differently from the fixed table"
      count := count + 1
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (stem.toString ++ ".equations.json")))
    let inp ← match IxCC.Recheck.ingress raw json [] with
      | .ok inp => pure inp
      | .error e => throw (IO.userError s!"role binding: {name}: ingress refused it: {e.render}")
    let p := inp.program
    require (reprStr p.known.pins == reprStr (KernelFront.pinsOfTable t)) s!"{name}: ingress's pins"
    let kf := Pinned.known { p with known := { pins := Pins.fixed } }
    require (reprStr { p.known with pins := Pins.fixed } == reprStr kf && p.known.nat.isSome)
      s!"{name}: the role table's and the fixed table's pins resolve differently"
    require (Pinned.knownOk p) s!"{name}: knownOk"
    count := count + 4
  return count

def run (root : System.FilePath) : IO Nat := do
  return (← sections) + (← envelopes root) + (← pins root) + (← projections root) +
    (← boundFixtures root)

end IxCCTests.IxonV3.Binding
