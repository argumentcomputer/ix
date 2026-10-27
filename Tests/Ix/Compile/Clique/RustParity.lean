/-
  The clique fixtures' helpers that `clique-rows` reads: the fixtures'
  cliques (`cliques`), with their equation lemmas realised (`withEqLemmas`),
  the carried lemmas (`carriedOf`), and the name-hash and content addresses
  (`nameAddr`, `contentAddr`). They served the comparison of the Lean clique
  library with a Rust one, which is removed.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Image.RawExact
import Ix.Compile.Pass.Clique
import Tests.Ix.Compile.Clique.Common
import Tests.Ix.Compile.Clique.Transport
import Tests.Ix.Compile.Clique.Recognition

open Lean Meta

namespace Tests.Ix.Compile.Clique.RustParity

open Tests.Ix.Compile.Clique.Common
open _root_.Ix.Compile.Pass.Clique (Decl CliqueOutcome CliquePlan constOccurrences foldDistinct
  renameConsts memberEqLemmas isEncodingName)

/-! ## The cliques -/

/-- The fixtures' roots: the clique twins, the library's own fixtures and the
ownership suite's sources and lemma cliques. -/
def roots : List Name :=
  [`Tests.Ix.Compile.Twins.Cliques, fixturesRoot, `Tests.Ix.Compile.Clique.Ownership.Src,
   `Tests.Ix.Compile.Clique.Ownership.Lem]

def userName (n : Name) : Name := (Lean.privateToUserName? n).getD n

def underRoots (n : Name) : Bool := roots.any (·.isPrefixOf (userName n))

/-- Every clique of two or more members under the roots, in Lean's order:
the `EqnInfo` cliques (`declNames`) and the theorem cliques (`all`), each
once, by the first member in `Name.quickLt` order. -/
def cliques (env : Environment) : Array (Array Name) := Id.run do
  let eqn := Tests.Ix.Compile.Clique.Transport.eqnCliques env
  let names := (env.constants.fold (init := #[]) fun acc n _ =>
    if underRoots n then acc.push n else acc).qsort Name.quickLt
  let mut seen : Std.HashSet Name := {}
  let mut out : Array (Array Name) := #[]
  for n in names do
    if seen.contains n then continue
    let some ci := env.find? n | continue
    let order? : Option (Array Name) := match eqn.get? n with
      | some (_, ms) => some ms
      | none => match ci with
        | .thmInfo v => if v.all.length ≥ 2 then some v.all.toArray else none
        | _ => none
    let some order := order? | continue
    if order.size < 2 then continue
    for a in order do seen := seen.insert a
    out := out.push order
  return out

/-- The fixtures' environment with the members' equation lemmas realised
(`m.eq_def`, and `m.eq_<k>`), and how many were asked for successfully. -/
def withEqLemmas (env : Environment) (cls : Array (Array Name)) : IO (Environment × Nat) := do
  let act : MetaM (Environment × Nat) := do
    let mut n := 0
    for ms in cls do
      for m in ms do
        let some (.defnInfo _) := (← getEnv).find? m | continue
        for s in ["eq_def", "eq_1"] do
          try
            discard <| realizeGlobalConstNoOverloadCore (Name.str m s)
            n := n + 1
          catch _ => pure ()
    return ((← getEnv), n)
  let ctx : Core.Context := { fileName := "<clique-rust-parity>", fileMap := default,
                              maxHeartbeats := 0 }
  Prod.fst <$> act.toIO ctx { env }

/-- A definition, theorem or opaque's value. -/
def valueOf' : IxConst → Option IxExpr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants a constant's type and value mention. -/
def refsOf (ci : IxConst) : Array IxName :=
  constOccurrences (fun _ => true) ci.getCnst.type ++
    ((valueOf' ci).map (constOccurrences fun _ => true)).getD #[]

/-- The clique table's carried lemmas of a clique: the members' equation
lemmas (`memberEqLemmas`) that reference a member and one of Lean's encoding
constants of the clique, in pretty-name order. -/
def carriedOf (const? : IxName → Option IxConst) (all : Array IxName) : Array IxName :=
  let found := all.foldl (init := #[]) fun acc m =>
    (memberEqLemmas const? {} m).foldl (init := acc) fun acc c =>
      match const? c with
      | some ci =>
        let rs := refsOf ci
        if rs.any (isEncodingName all ·) && rs.any all.contains then acc.push c else acc
      | none => acc
  found.qsort fun a b => a.pretty < b.pretty

/-! ## Addresses -/

/-- `n` is under the namespace `ns` (by its user name, for a private name). -/
def isUnder (ns : Name) (n : IxName) : Bool := ns.isPrefixOf (userName (toLeanName n))

/-- A name-hash address: every name by its pretty form. -/
def nameAddr (n : IxName) : Option Address := some (Address.blake3 n.pretty.toUTF8)

/-- A content address: a constant under the clique's namespace by its type
and value with that namespace erased (so the same matcher in two
presentations has one address), any other name by its name. -/
def contentAddr (get? : IxName → Option IxConst) (ns : Name) (n : IxName) : Option Address :=
  if isUnder ns n then
    (get? n).map fun ci =>
      let rel := renameConsts fun m =>
        if isUnder ns m then some (ixName ((toLeanName m).replacePrefix ns `_pres)) else none
      let v := match valueOf' ci with
        | some e => toString (rel e).getHash
        | none => ""
      Address.blake3 s!"{(rel ci.getCnst.type).getHash}|{v}".toUTF8
  else some (Address.blake3 (toLeanName n).toString.toUTF8)

end Tests.Ix.Compile.Clique.RustParity
