import CompilatrixTests.IxonV3.TypingFixtures

namespace CompilatrixTests.IxonV3.Primitives

open Compilatrix.Ixon Compilatrix.Ixon.V3 TypingFixtures

private def expect (label : String) (result : Except String α) (accepted : Bool) : IO Unit :=
  unless result.toOption.isSome == accepted do
    let detail := match result with | .ok _ => "accepted" | .error e => e
    throw (IO.userError s!"v3 primitive {label}: expected {accepted}, got {detail}")

def storeLiteral (env : Environment) (blob : ByteArray) (string : Bool)
    (type : Compilatrix.Ixon.Address) : Environment :=
  let address := Address.blake3 blob
  let env := { env with blobs := env.blobs.insert address blob }
  (store env ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], if string then .str 1 else .nat 1⟩,
    #[], #[type, address], #[]⟩).1

def arithmeticWitness (env : Environment) (result : Nat) : Environment := Id.run do
  let p := Tc.PrimAddrs.canonical
  let mut env := env
  let mut refs := #[p.nat, p.eq, p.eqRefl, p.natAdd]
  for n in #[20, 22, result] do
    let blob : ByteArray := ⟨Tc.tcNatBytesLE n⟩
    let address := Address.blake3 blob
    env := { env with blobs := env.blobs.insert address blob }
    refs := refs.push address
  let lhs : E := .app (.app (.ref 3 #[]) (.nat 4)) (.nat 5)
  let typ : E := .app (.app (.app (.ref 1 #[0]) (.ref 0 #[])) lhs) (.nat 6)
  let value : E := .app (.app (.ref 2 #[0]) (.ref 0 #[])) (.nat 6)
  return (store env ⟨.defn ⟨.thm, .safe, 0, typ, value⟩, #[], refs, #[.succ .zero]⟩).1

def run (root : System.FilePath) : IO Nat := do
  let p := Tc.PrimAddrs.canonical
  let cases := #[
    ("Nat", p.nat, 4), ("Nat.add", p.natAdd, 18),
    ("String", p.string, 307), ("Quot.lift", p.quotLift, 5)]
  let mut environments : Array Environment := #[]
  for (name, main, count) in cases do
    let raw ← IO.FS.readBinFile (root / "typing" / s!"{name}.ixe")
    let env ← IO.ofExcept (decodeAnonymousEnv raw)
    unless env.main == some main && env.consts.size == count do
      throw (IO.userError s!"v3 primitive fixture changed: {name}")
    expect s!"producer {name} closure" (validate raw (standardProfile env).bytes) true
    environments := environments.push env
  let natEnv := environments[0]!
  let stringEnv := environments[2]!
  let natLiteral := storeLiteral natEnv ⟨#[42]⟩ false p.nat
  expect "canonical Nat literal" (validate (bytes natLiteral) (standardProfile natLiteral).bytes) true
  let stringLiteral := storeLiteral stringEnv "v3 λ".toUTF8 true p.string
  expect "canonical String literal" (validate (bytes stringLiteral) (standardProfile stringLiteral).bytes) true
  let invalidUtf8 := storeLiteral stringEnv ⟨#[255]⟩ true p.string
  expect "invalid UTF-8" (Tc.checkEnv invalidUtf8) false
  let wrongType := storeLiteral stringEnv ⟨#[42]⟩ false p.string
  expect "Nat literal is not String" (Tc.checkEnv wrongType) false
  let redirected := { standardProfile stringLiteral with natType := some p.string }
  expect "combined literal pin redirection" (validate (bytes stringLiteral) redirected.bytes) false
  let eqEnv := environments[3]!
  let arithmeticConsts := eqEnv.consts.fold (init := environments[1]!.consts)
    fun acc address raw => acc.insert address raw
  let arithmeticEnv := { environments[1]! with consts := arithmeticConsts }
  let good := arithmeticWitness arithmeticEnv 42
  expect "native Nat addition agrees with Eq.refl"
    (validate (bytes good) (standardProfile good).bytes) true
  let bad := arithmeticWitness arithmeticEnv 43
  expect "false arithmetic equality" (Tc.checkEnv bad) false
  return 15

end CompilatrixTests.IxonV3.Primitives
