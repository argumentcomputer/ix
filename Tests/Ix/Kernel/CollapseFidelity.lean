import LSpec
import Ix.CompileResource
import Ix.EnvScope
import Ix.KernelFidelity.Reader
import Ix.Meta

namespace Tests.Ix.Kernel.CollapseFidelity

open LSpec Tests.Ix.Kernel.ReaderFidelity Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep (Hints Setup setup)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def check : IO Nat := do
  let lean ← getFileEnv "Tests/Ix/Compile/Fixtures/LocalCollapse.lean"
  let seeds := lean.constants.toList.filterMap fun (n, _) =>
    if (`LocalCollapse).isPrefixOf n then some n else none
  let out ← IO.ofExcept ((← _root_.Ix.CompileM.compileLeanConstsValidated
    (_root_.Ix.EnvScope.collectSelectedDeps lean seeds) (numWorkers := 1)).mapError toString)
  ensure (out.ungroundedCount == 0) "LocalCollapse did not compile completely"
  let access ← IO.ofExcept (InputAccess.ofBytes lean out.bytes)
  let report ← runAccess access
  ensure (report.constants == access.names.size && report.constants > 0 &&
    report.problems.isEmpty && report.unexplained.isEmpty && report.unmatched.isEmpty &&
    report.reorderedBlocks.size == 2) s!"collapsed source fidelity failed:\n{report.summary}"
  let table ← IO.ofExcept defaultTable
  let pre ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore access.store access.hints
  let s : Setup := setup access.store (access.blobs[·]?) table pre hints.lookup
    (literals := access.literals)
  let addr := fun n => access.address (_root_.Ix.Name.fromLeanName n)
  let ref := fun n => (addr n).bind (resolve (s.store[·]?))
  let rcx : RefCx := { find := lean.find?, addrOf := addr, refOf := ref, roles := s.cx.roles }
  let mut named : Std.HashMap Lean.Name NamedFacts := {}
  for n in access.names do
    let nd ← IO.ofExcept (access.metadata (_root_.Ix.Name.fromLeanName n))
    named := named.insert n { addr := nd.addr, original := nd.original.isSome }
  let cx : Cx := {
    lean := lean.find?, rcx, named, byName := {}, foreign := {}, keep := fun _ => false
    advisory := fun _ => none, aliases := fun _ => 0, recursorKey := canonicalRecursor s.cx }
  let roots := [`LocalCollapse.PA, `LocalCollapse.TA]
  let mut cases := 0
  for n in roots do
    let some (.inductInfo iv) := lean.find? n | throw (IO.userError "missing source type")
    let some refs := iv.all.mapM ref | throw (IO.userError "missing source projection")
    ensure (iv.all.length == 2 && refs.eraseDups.length == 1) "fixture lost actual many-to-one projection"
    let some r := ref n | throw (IO.userError "missing root reference")
    let source ← IO.ofExcept (access.records.get r.block)
    let rd ← IO.ofExcept ((readRecord s.cx {} r.block source).mapError toString)
    let some block := rd.decls.findSome? (fun | .indDecl b _ => some b | _ => none)
      | throw (IO.userError "missing canonical declaration block")
    ensure (flatCollapseOrder cx iv block) "real flat collapse was refused"
    let other := (roots.filter (· != n)).head!
    let some otherRef := ref other | throw (IO.userError "missing other owning type")
    let some wrongRec := canonicalRecursor s.cx otherRef | throw (IO.userError "missing other recursor")
    let extra := Ix.Kernel.ConstantInfo.indInfo { block.head!.toConstantVal with name := wrongRec } {}
    let wrong := block.map fun
      | .recInfo cv m p rs => .recInfo { cv with name := wrongRec } m p rs
      | ci => ci
    let variants := [
      ("missing member", block.tail),
      ("missing constructor", block.filter fun | .ctorInfo .. => false | _ => true),
      ("missing recursor", block.filter fun | .recInfo .. => false | _ => true),
      ("extra member", block ++ [extra]), ("duplicate", block ++ [block.head!]),
      ("wrong owning recursor", wrong)]
    for (label, changed) in variants do
      ensure (!flatCollapseOrder cx iv changed) s!"{n}: accepted {label}"
      cases := cases + 1
    ensure (!flatCollapseOrder { cx with named := cx.named.erase (n ++ `rec) } iv block)
      "one missing original was accepted"
    ensure (!flatCollapseOrder cx { iv with all := [n] } block) "non-collapse entered the exception"
    ensure (!flatCollapseOrder cx { iv with numNested := 1 } block) "nested block entered the exception"
    ensure (!flatCollapseOrder { cx with recursorKey := fun _ => none } iv block) "missing recursor mapping was accepted"
    ensure ((canonicalRecursor s.cx (.member r.block 9999)).isNone) "wrong owning type resolved"
    let some shape := s.cx.index.blocks[r.block]? | throw (IO.userError "missing decoded index block")
    let repeated := { shape with recs := shape.recs ++ shape.recs }
    let duplicated := { s.cx.index with blocks := s.cx.index.blocks.insert r.block repeated }
    ensure ((canonicalRecursor { s.cx with index := duplicated } r).isNone) "ambiguous recursor was selected"
    cases := cases + 6
    IO.println s!"flat collapse {n}: {iv.all.length} source types -> {refs.eraseDups.length} \
      decoded member refs; {block.length} canonical declarations"
  ensure (cases == 24) "collapse negative controls did not all execute"
  IO.println s!"flat-collapse fidelity: {report.constants}/{access.names.size} source comparisons, \
    2 real blocks and {cases} missing/extra/duplicate/recursor/boundary refusals"
  return cases

def suite : List TestSeq := [
  .individualIO "flat collapse uses exact decoded members and owning recursors" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.CollapseFidelity
