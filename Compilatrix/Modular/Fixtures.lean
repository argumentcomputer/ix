import Compilatrix.Modular.Wire
import Compilatrix.Coverage.Sources
import Compilatrix.X86.ValidatedScalar

/-! Canonical source fixtures with explicit modular dependency graphs. -/

namespace Compilatrix.Modular.Fixtures

open Ixon (Address Constant Expr)

def policy : Policy := {}
def limits : Limits := {}

structure Case where
  name : String
  inputs : List Input
  root : Address
  expected : Nat

def definition (value : Expr) (refs : Array Address := #[]) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value }
    sharing := #[], refs, univs := #[.zero] }

def literal (name : String) (number : Nat) : Except String (Input × Address) := do
  let constant ← Coverage.addressed (X86.ValidatedScalar.constant number)
  return ({
    name, constants := [constant],
    blobs := [(X86.ValidatedScalar.literalAddress number, .natB number)] }, constant.1)

def editCase (edited : Bool) : Except String Case := do
  let (leaf, leafRoot) ← literal "leaf" (if edited then 38 else 37)
  let (unaffected, unaffectedRoot) ← literal "unaffected" 99
  let dependent ← Coverage.addressed (definition (.ref 0 #[]) #[leafRoot])
  let root ← Coverage.addressed (definition
    (.letE false (.sort 0) (.ref 0 #[]) (.ref 1 #[])) #[unaffectedRoot, dependent.1])
  return {
    name := if edited then "edited" else "baseline"
    inputs := [
      { name := "root", constants := [root], imports := ["unaffected", "dependent"] },
      { name := "dependent", constants := [dependent], imports := ["leaf"] },
      unaffected, leaf]
    root := root.1, expected := if edited then 38 else 37 }

/-- A literal-oracle edit keeps every source address unchanged. Its exact
payload must still invalidate the leaf certificate and its dependent cone. -/
def blobEditCase : Except String Case := do
  let baseline ← editCase false
  return { baseline with
    name := "blob-edited"
    inputs := baseline.inputs.map fun input =>
      if input.name == "leaf" then
        { input with blobs := [(X86.ValidatedScalar.literalAddress 37, .natB 38)] }
      else input
    expected := 38 }

def sequence (references : List Address) : Expr :=
  let count := references.length
  let initial := Expr.ref (count - 1).toUInt64 #[]
  ((List.range (count - 1)).reverse).foldl
    (fun body index => .letE false (.sort 0) (.ref index.toUInt64 #[]) body) initial

/-- A recursor and its caller remain inside one source mutual constant. A
separate unit imports the checked group, widens the simultaneous scope, and
applies its public projection to an independently supplied literal. -/
def mutualCase : Except String Case := do
  let nat : Expr := .recur 0 #[]
  let typ : Expr := .all .many .shared nat nat
  let zero := X86.ValidatedScalar.literalAddress 0
  let five := X86.ValidatedScalar.literalAddress 5
  let block ← Coverage.addressed {
    info := .muts #[
      .indc {
        isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
        ctors := #[
          { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := nat },
          { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1, typ }] },
      .recr {
        k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0,
        motives := 0, minors := 0, typ,
        rules := #[{ fields := 0, rhs := .nat 0 },
          { fields := 1, rhs := .lam .many nat (.var 0) }] },
      .defn {
        kind := .defn, safety := .safe, lvls := 0, typ,
        value := .lam .many nat (.app (.recur 1 #[]) (.var 0)) }]
    sharing := #[], refs := #[zero], univs := #[.zero] }
  let projection ← Coverage.addressed {
    info := .dPrj { idx := 2, block := block.1 }, sharing := #[], refs := #[], univs := #[] }
  let additional ← Coverage.addressed {
    info := .muts #[.defn {
      kind := .defn, safety := .safe, lvls := 0, typ := .sort 0
      value := .app (.ref 0 #[])
        (.app (.lam .erased (.sort 0) (.nat 1)) (.sort 0)) }]
    sharing := #[], refs := #[projection.1, five], univs := #[.zero] }
  let root ← Coverage.addressed {
    info := .dPrj { idx := 0, block := additional.1 }, sharing := #[], refs := #[], univs := #[] }
  let group : Input := {
    name := "recursive-group", constants := [block], blobs := [(zero, .natB 0)], natBlock := some block.1 }
  let entry : Input := {
    name := "entry", constants := [projection, additional, root], blobs := [(five, .natB 5)],
    natBlock := some block.1, imports := [group.name] }
  return { name := "mutual", inputs := [entry, group], root := root.1, expected := 4 }

/-- Every literal is reached through its group's gateway; the root reaches
every gateway. Larger cases therefore grow the reachable source closure. -/
def wideCase (count : Nat) (groupSize : Nat := 64) : Except String Case := do
  ensure (count > 0 && count ≤ 1024 && groupSize > 0 && groupSize ≤ 128)
    "invalid modular fixture size"
  let groups := (count + groupSize - 1) / groupSize
  let mut inputs := []
  let mut roots := []
  for group in [:groups] do
    let start := group * groupSize
    let size := min groupSize (count - start)
    let mut constants := []
    let mut blobs := []
    for offset in [:size] do
      let number := 1000 + start + offset
      let constant ← Coverage.addressed (X86.ValidatedScalar.constant number)
      constants := constant :: constants
      blobs := (X86.ValidatedScalar.literalAddress number, .natB number) :: blobs
    constants := constants.reverse
    let references := constants.map (·.1)
    let gateway ← Coverage.addressed (definition (sequence references) references.toArray)
    inputs := { name := s!"group-{group}", constants := constants ++ [gateway], blobs := blobs.reverse } :: inputs
    roots := gateway.1 :: roots
  let orderedRoots := roots.reverse
  let root ← Coverage.addressed (definition (sequence orderedRoots) orderedRoots.toArray)
  let groups := inputs.reverse
  return {
    name := s!"wide-{count}"
    inputs := { name := "root", constants := [root], imports := groups.map (·.name) } :: groups
    root := root.1, expected := 1000 + count - 1 }

def observe {root} (compiled : Compiled policy root .shared) (expected : Nat) : Except String Unit := do
  let source := compiled.program.source policy
  match Ixon.Eval.eval source 10000 (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource with
  | .ok (.litV (.natL actual)) => ensure (actual == expected) "source fixture result mismatch"
  | _ => throw "source fixture did not return a Nat"
  match IxIR0.eval compiled.source.rawCtx 10000 [] (.ref root) with
  | .ok (.lit (.nat actual)) => ensure (actual == expected) "raw erasure fixture result mismatch"
  | _ => throw "raw erasure fixture did not return a Nat"
  match IxIR0.eval { env := compiled.artifact.erasedDecls |> IxIR0.Env.ofList }
      10000 [] compiled.source.erasure.result.main with
  | .ok (.lit (.nat actual)) => ensure (actual == expected) "addressed erasure fixture result mismatch"
  | _ => throw "addressed erasure fixture did not return a Nat"
  match IxIR1.runOwnedMain { decls := compiled.artifact.targetDeclEnv } .shared compiled.artifact.main 10000 with
  | .ok (store, .lit (.nat actual)) =>
      ensure (actual == expected && store.live == 0) "IxIR1 result or reclamation mismatch"
  | _ => throw "IxIR1 fixture did not return a Nat"

end Compilatrix.Modular.Fixtures
