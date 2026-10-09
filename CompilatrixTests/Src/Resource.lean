import CompilatrixTests.Src.Table
import Compilatrix.Src.Table.Cert

/-! Address/header transport and hostile resource metadata. Program mutations
test the structural checker; corpus tests separately exercise byte ingress. -/

namespace CompilatrixTests.Src.Resource

open Compilatrix Compilatrix.Src Compilatrix.Ixon CompilatrixTests.Src

private def check (a : Assert) (r : Except String α) (ok : Bool) (label : String) : IO Unit :=
  expect a (r.isOk == ok) s!"resource binding: {label}"

private def written : V3.BinderContract := { uses := .affine, value := .localUnique }

private def piHeader (t : Term) : Term := match t with
  | .pi b r d body => .pi { b with contract := written } r d body
  | _ => t

private def lamHeader (t : Term) : Term := match t with
  | .lam b d body => .lam { b with contract := written } d body
  | _ => t

private def context (p : Program) (f thm eq : CId) : Src.Resource.Context :=
  let profile : Src.Resource.Profile := {
    depth := 1, steps := 1
    eqType := some (p.addr eq), equations := #[(p.addr f, p.addr thm)] }
  let bytes := profile.bytes
  let address := Compilatrix.Ixon.Address.blake3Pure bytes
  { address, bytes, pairs := [{
    definition := p.addr f, equation := p.addr thm, profile := address
    contracts := [{ position := 0, contract := written }] }] }

private def codec (a : Assert) (eq f thm : Compilatrix.Ixon.Address) : IO Unit := do
  -- Independent TagN byte samples: empty address lists/options, limits 1/1,
  -- equation extension flag 2, zero interfaces, and one definition/theorem pair.
  let header := "ixon-v4/resource-v1/profile\x00".toUTF8
  let base := header ++ ByteArray.mk #[0, 0, 0, 0, 0, 1, 1]
  let bytes := base ++ ByteArray.mk #[2, 0] ++ eq.hash ++ ByteArray.mk #[1] ++ f.hash ++ thm.hash
  let p ← IO.ofExcept (Src.Resource.Profile.ofBytes bytes)
  expect a (p.eqType == some eq && p.equations == #[(f, thm)] && p.bytes == bytes)
    "resource binding: independent equation profile framing"
  check a (Src.Resource.Profile.ofBytes base) true "legacy profile framing"
  for n in [1, 127, 128, 129, 16511, 16512, 16513, 82047, 82048, 82049,
      16859263, 16859264, 16859265, 4311826559, 4311826560, 4311826561, UInt64.size - 1] do
    let q : Src.Resource.Profile := { depth := n, steps := n }
    expect a (q.byteList == q.bytes.data.toList && (Src.Resource.Profile.ofBytes q.bytes).isOk)
      s!"resource binding: list/native TagN encoders agree at {n}"
  let extended : Src.Resource.Profile := {
    assumptions := #[f], shareableTypes := #[f], choices := #[f]
    natType := some f, stringType := some thm, cases := true
    interfaces := #[(f, ByteArray.mk #[0])], eqType := some eq, equations := #[(f, thm)]
    caseDefinitions := #[f], crossing := true, linearTypes := #[f], scalarTypes := #[f] }
  expect a (extended.byteList == extended.bytes.data.toList &&
    (Src.Resource.Profile.ofBytes extended.bytes).isOk)
    "resource binding: list/native framing agrees for every profile extension"
  for (label, bad) in [("trailing byte", bytes.push 0), ("truncation", bytes.extract 0 (bytes.size - 1)),
      ("unknown flags", base ++ ByteArray.mk #[64, 0]), ("empty extension", base ++ ByteArray.mk #[0, 0]),
      ("empty equation list", base ++ ByteArray.mk #[2, 0] ++ eq.hash ++ ByteArray.mk #[0]),
      ("duplicate definitions", base ++ ByteArray.mk #[2, 0] ++ eq.hash ++ ByteArray.mk #[2] ++
        f.hash ++ thm.hash ++ f.hash ++ thm.hash),
      ("invalid optional tag", header ++ ByteArray.mk #[0, 0, 0, 2, 0, 1, 1]),
      ("zero limits", header ++ ByteArray.mk #[0, 0, 0, 0, 0, 0, 1])] do
    check a (Src.Resource.Profile.ofBytes bad) false label

def run (a : Assert) : IO Unit := do
  let loaded ← loadK1
  let (f, thm) ← Table.eqnNamed loaded "Nat.add"
  let base := { loaded.program with table := {} }
  let some eq := base.known.eq | throw (IO.userError "resource binding tests: Eq missing")
  codec a (base.addr eq) (base.addr f) (base.addr thm)
  let some (.defn fk fs fn ft fv) := base.decl? f | throw (IO.userError "subject missing")
  let some (.defn tk ts tn tt tv) := base.decl? thm | throw (IO.userError "theorem missing")
  let p := (base.setDecl f (.defn fk fs fn (piHeader ft) (lamHeader fv))).setDecl thm
    (.defn tk ts tn (piHeader tt) tv)
  let ctx := context p f thm eq
  let p := { p with resource := some ctx }
  check a (Src.Resource.validate p) true "matching authenticated-address/header records"
  let wrongDomain := match piHeader tt with
    | .pi b r _ body => .pi b r (.sort .zero) body
    | t => t
  check a (Src.Resource.validate (p.setDecl thm (.defn tk ts tn wrongDomain tv))) false
    "theorem domain mismatch rejected without selected roots"
  let rec wrongResult : Term → Term
    | .pi b r d body => .pi b r d (wrongResult body)
    | body => match body.spine with
      | (head, [(_, mode), lhs, rhs]) => Term.mkApps head [(.sort .zero, mode), lhs, rhs]
      | _ => body
  check a (Src.Resource.validate (p.setDecl thm (.defn tk ts tn (wrongResult (piHeader tt)) tv))) false
    "equation result type mismatch rejected without selected roots"
  let entry ← IO.ofExcept (Src.Table.checkEqn p f thm)
  match entry with
  | .eqn _ (.lam b d _) =>
    expect a (b.contract == written) "resource binding: usage/ownership/locality header retained"
    expect a (ft.pis.1.head?.any fun (_, original) => d.eqv original) "resource binding: original header domain retained"
  | _ => expect a false "resource binding: no rebuilt lambda"
  let cert : Src.Table.TableCert := { resolve := [(f, .eqn thm)] }
  let table ← IO.ofExcept (Src.Table.ofCert {} p cert)
  check a (Src.Table.validate {} { p with table }) true "certificate and validator agree"
  check a (Src.Table.ofCert {} p {}) false "omitted bound equation"
  check a (Src.Resource.selected p { resolve := NatMap.ofList [(f, .prim .add)] }) false "primitive override"
  check a (Src.Table.checkCsimp p f f thm) false "csimp with resource context"
  check a (Src.Table.checkEqn { p with resource := none } f thm) false "missing binding"
  check a (Src.Table.checkEqn { p with resource := some { ctx with pairs := [] } } f thm) false "missing checked pair"
  check a (Src.Resource.validate { p with resource := some { ctx with pairs := ctx.pairs ++ ctx.pairs } }) false
    "duplicate checked pair"
  for contracts in [[], [{ position := 1, contract := written }], [{ position := 0, contract := .many }]] do
    let pairs := ctx.pairs.map fun q => { q with contracts }
    check a (Src.Resource.validate { p with resource := some { ctx with pairs } }) false "forged header record"
  check a (Src.Table.checkEqn (p.setDecl f (.defn fk fs fn ft (lamHeader fv))) f thm) false "type/body header disagreement"
  check a (Src.Table.checkEqn (p.setDecl thm (.defn tk ts tn tt tv)) f thm) false "theorem drops header"
  let curried := match piHeader ft with
    | .pi b _ d body => .pi b .unique d body
    | t => t
  check a (Src.Table.checkEqn (p.setDecl f (.defn fk fs fn curried (lamHeader fv))) f thm) false
    "intermediate curried-result contract"
  let wrongPair := ctx.pairs.map fun q => { q with equation := p.addr f }
  check a (Src.Resource.validate { p with resource := some { ctx with pairs := wrongPair } }) false
    "changed equation address"
  check a (Src.Resource.validate { p with resource := some { ctx with address := p.addr f } }) false
    "changed profile address"
  let (_, unrelated) ← Table.eqnNamed loaded "List.map"
  let unrelatedProfile : Src.Resource.Profile := { eqType := some (p.addr eq), equations := #[(p.addr f, p.addr unrelated)] }
  let unrelatedBytes := unrelatedProfile.bytes
  let unrelatedAddress := Compilatrix.Ixon.Address.blake3Pure unrelatedBytes
  check a (Src.Resource.validate { p with resource := some {
    address := unrelatedAddress, bytes := unrelatedBytes
    pairs := [{
      definition := p.addr f, equation := p.addr unrelated, profile := unrelatedAddress
      contracts := [{ position := 0, contract := written }] }] } }) false
    "rehashed profile cannot bind a theorem of another definition"
  let rec internal : Term → Term
    | .lam b d body => .lam b d (internal body)
    | body => .letE { binder := written, nonDep := true } .rel (.sort .zero) (.natLit 0) body
  check a (Src.Table.checkEqn (p.setDecl f (.defn fk fs fn (piHeader ft) (internal (lamHeader fv)))) f thm) false
    "body-internal let contract"
  -- Hash-consistent malformed profile data must still fail structural decoding.
  let malformed := ctx.bytes.push 0
  let changed := Compilatrix.Ixon.Address.blake3Pure malformed
  let bad := { ctx with
    bytes := malformed, address := changed
    pairs := ctx.pairs.map fun q => { q with profile := changed } }
  check a (Src.Resource.validate { p with resource := some bad }) false "consistently rehashed malformed profile"
  let wrongProfile : Src.Resource.Profile := { eqType := some (p.addr eq), equations := #[(p.addr thm, p.addr f)] }
  let bytes := wrongProfile.bytes
  let address := Compilatrix.Ixon.Address.blake3Pure bytes
  check a (Src.Resource.validate { p with resource := some {
    address, bytes
    pairs := [{ definition := p.addr thm, equation := p.addr f, profile := address }] } }) false
    "consistently rebound wrong declaration kinds"
  let scalar : Src.Resource.Profile := { scalarTypes := #[p.addr f] }
  check a (Src.Resource.validate { p with resource := some {
    bytes := scalar.bytes
    address := Compilatrix.Ixon.Address.blake3Pure scalar.bytes } }) false "scalar ownership crossing remains disabled"

end CompilatrixTests.Src.Resource
