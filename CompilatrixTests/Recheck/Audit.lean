import Compilatrix.Recheck.Run
import Compilatrix.Anf.Semantics
import Lean

/-! # The recheck path's kernel-style audit (M1.K1)

A build-time check over every constant `Recheck.run`'s value reaches through
definitions (proofs and types are not walked): no `Compilatrix` constant on
the path may

* be compiled by well-founded recursion (`WellFounded.fix`, `Acc.rec`),
  which the kernel unfolds through accessibility proofs;
* use `Std.HashMap`, `Std.HashSet` or their dependent forms;
* carry `implemented_by` or `extern` (the kernel would run a different
  definition from the native one);
* loop over an `Array` with the library's `all`, `any`, `contains`, `map`,
  `mapM`, `foldl`, `foldlM` or `forIn` (well-founded or index-walking loops
  in the kernel), or
* build a `ByteArray` by `append`, `extract`, `copySlice`, `push` or `set!`
  (each copies the whole array in the kernel).

`allowed` lists the constants that break a rule on a failure or diagnostic
path only, which the kernel never evaluates on an accepted artifact. A new
violation fails the build with its name and rule. -/

namespace CompilatrixTests.Recheck.Audit

open Lean Elab Command

/-- The constants a definition's value mentions. -/
def valueConsts (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo d) => d.value.getUsedConstants
  | some (.opaqueInfo d) => d.value.getUsedConstants
  | _ => #[]

/-- Every constant a value reaches from `root`. -/
def reach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      for c in valueConsts env n do
        unless seen.contains c do todo := c :: todo
  return seen

def wellFounded : List Name := [``WellFounded.fix, ``WellFounded.fixF, ``Acc.rec]

def arrayLoops : List Name :=
  [``Array.all, ``Array.any, ``Array.contains, ``Array.map, ``Array.mapM, ``Array.foldl, ``Array.foldlM,
   ``Array.forIn', ``Array.anyM, ``Array.allM]

def byteCopies : List Name :=
  [``ByteArray.append, ``ByteArray.instAppend, ``ByteArray.extract, ``ByteArray.copySlice, ``ByteArray.push,
   ``ByteArray.set!]

def hashed (c : Name) : Bool :=
  [`Std.HashMap, `Std.DHashMap, `Std.HashSet].any (·.isPrefixOf c)

/-- Constants that break a rule on failure or diagnostic paths only. -/
def allowed : List Name :=
  [ -- A diagnostic address rendering (`Array.foldl`).
    ``Compilatrix.Ixon.Address.toHex ]

/-- The violations on the path from `root`, as `(constant, rule)`. -/
def violations (env : Environment) (root : Name) : Array (Name × String) := Id.run do
  let mut out := #[]
  for n in (reach env root).toList do
    unless (`Compilatrix).isPrefixOf n do continue
    if allowed.contains n then continue
    let cs := valueConsts env n
    if cs.any wellFounded.contains then out := out.push (n, "well-founded recursion")
    if cs.any hashed then out := out.push (n, "hash map")
    if (Compiler.getImplementedBy? env n).isSome || isExtern env n then
      out := out.push (n, "implemented_by/extern")
    if cs.any arrayLoops.contains then out := out.push (n, "Array loop")
    if cs.any byteCopies.contains then out := out.push (n, "ByteArray copy")
  return out.qsort fun a b => a.1.toString < b.1.toString

run_cmd do
  let env ← getEnv
  let found := violations env ``Compilatrix.Recheck.run
  unless found.isEmpty do
    throwError "Recheck.run's path is not in kernel-evaluable style: {found.toList}"

/-! Sanity: the audit sees what it looks for off the path. -/

run_cmd do
  let env ← getEnv
  unless (violations env ``Compilatrix.Lir.Func.predCounts).any (·.2 == "Array loop") do
    throwError "the audit missed Lir.Func.predCounts' Array.foldl"
  unless (violations env ``Compilatrix.Anf.eval).any (·.2 == "well-founded recursion") do
    throwError "the audit missed Anf.eval's well-founded recursion"
  unless (violations env ``Compilatrix.X86.ELF.write).any (·.2 == "ByteArray copy") do
    throwError "the audit missed ELF.write's ByteArray appends"

end CompilatrixTests.Recheck.Audit
