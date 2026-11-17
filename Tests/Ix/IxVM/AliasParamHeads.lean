import Tests.Ix.IxVM.AliasFormers
import IxVM.Source
import Aiur.Generic.Runtime
import IxVMRefinement.Core.Rep
import IxC.Kernel.Semantics.Inductives.DeclNativeJ

/-! # Alias constructor parameter heads and the local zero-check boundary

The corpus pass measures raw occurrences and family heads after the reader's zeta expansion,
restricted to safe non-telescope formers. It does not execute a whole declaration claim.
The source pass executes the actual `ctor_zero_ok` function on a parameter-domain let and two
controls, then compares the kernel predicate on the read type. No claim of full declaration
acceptance follows from this local function measurement.
-/

namespace Tests.Ix.IxVM.AliasParamHeads

open AliasFormers

partial def zeta : RE → RE
  | .app f a => .app (zeta f) (zeta a)
  | .lam d t b => .lam d (zeta t) (zeta b)
  | .all d t b => .all d (zeta t) (zeta b)
  | .letE _ v b => zeta (RE.inst (zeta v) 0 b)
  | .prj t i e => .prj t i (zeta e)
  | e => e

partial def famHead (t : Address) : RE → Bool
  | .all _ _ b => famHead t b
  | .app f _ => famHead t f
  | .const a _ => a == t
  | _ => false

partial def parameterDomains : Nat → RE → Except String (List RE)
  | 0, _ => .ok []
  | n + 1, .all _ t b => (parameterDomains n b).map (t :: ·)
  | _ + 1, _ => .error "parameter spine is not syntactically forall"

open Aiur Aiur.Generic
open IxVM.Refinement.Core

private def ep (n : Nat) : SourceValue IxVM.F := .ptr (.enum kexprEnum) n
private def lp (n : Nat) : SourceValue IxVM.F := .ptr (.enum klevelEnum) n
private def ap : SourceValue IxVM.F := .ptr addrTy 5
private def xs : SourceValue IxVM.F := .ptr (.enum klevelListEnum) 4

/-- The raw parameter is a let whose value is a Pi ending in the family. `expanded` selects
the direct Pi control, and `correct` changes its binder datum to the required zero datum. -/
private def testHeap (expanded correct : Bool) : Heap IxVM.F :=
  [.construct klevelEnum "Zero" [],
   .construct klevelEnum "Succ" [lp 0],
   .construct kexprEnum "Srt" [lp 1],
   .construct kexprEnum "Srt" [lp 0],
   .construct klevelListEnum "Nil" [],
   .tuple (List.replicate 32 (.field 0)),
   .construct kexprEnum "Const" [ap, xs],
   .construct kexprEnum "Forall" [ep 3, ep 6, lp (if correct then 0 else 1)],
   .construct kexprEnum "BVar" [.field 0],
   .construct kexprEnum "Let" [ep 2, ep 7, ep 8],
   .construct kexprEnum "Forall" [ep (if expanded then 7 else 9), ep 6, lp 0]]

private def localRun (expanded correct : Bool) : Except String (SourceValue IxVM.F) := do
  let w := IxVM.source.world
  let (types, locals, body) ← (w.prepare "KernelCheck::ctor_zero_ok" [ep 10, ap, lp 0]).mapError reprStr
  let (r, _) ← (SourceSemantics.evalFunctionWith w SourceSemantics.unavailable types locals
    5000 body (testHeap expanded correct)).mapError reprStr
  return r

private def kernelZero (correct : Bool) : Bool :=
  let T : Ix.Kernel.Key .anon := .role .false
  let inner : Ix.Kernel.Expr .anon := .forallE (.sort .zero) (.const T [])
    (bmeta (if correct then .zero else .succ .zero))
  let readType : Ix.Kernel.Expr .anon := .forallE inner (.const T []) (bmeta .zero)
  Ix.Kernel.Semantics.ctorZeroOk T (Ix.Kernel.Level.zeronessOf .zero) readType

private def localChecks : IO Bool := do
  let a := localRun false false
  let b := localRun true false
  let c := localRun true true
  IO.println s!"local ctor_zero_ok raw-let: {reprStr a}"
  IO.println s!"local ctor_zero_ok expanded-wrong-datum: {reprStr b}"
  IO.println s!"local ctor_zero_ok expanded-correct-datum: {reprStr c}"
  IO.println s!"kernel read-type predicates: wrong={kernelZero false}; correct={kernelZero true}"
  return a.isOk && !b.isOk && c.isOk && !kernelZero false && kernelZero true

def run : IO UInt32 := do
  let localOk ← localChecks
  let some path ← IO.getEnv "IX_ALIAS_IXE" | throw (IO.userError "set IX_ALIAS_IXE")
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  IO.println s!"corpus {path}: records={env.consts.size}; names={env.named.size}"
  let mut aliases := 0
  let mut constructors := 0
  let mut parameters := 0
  let mut mentions := 0
  let mut heads := 0
  let mut lets := 0
  let mut errors := 0
  let mut badBlocks : Std.HashSet Address := {}
  let mut names : Std.HashMap Address String := {}
  for (n, d) in env.named.toArray do
    if !names.contains d.addr then names := names.insert d.addr (toString n)
  for (a, lc) in env.consts.toArray do
    if lc.peekTag != .ok .muts then continue
    let some c := lc.get? | continue
    let .muts ms := c.info | continue
    let cx : RCx := { refs := c.refs, univs := c.univs, recur := recurOf a ms }
    for j in [:ms.size] do
      let some (.indc ind) := ms[j]? | continue
      if ind.isUnsafe then continue
      let off := rootOffset ms j
      let f ← match readRoots c cx #[(off, ind.typ)] 5000000 with
        | .ok fs => pure (some fs[0]!)
        | .error e =>
          IO.println s!"read-error {a}/{j}: {e}"
          errors := errors + 1
          pure none
      let some f := f | continue
      if formerIsTele (ind.params.toNat + ind.indices.toNat) f then continue
      aliases := aliases + 1
      let t := iprjAddr a j
      for k in [:ind.ctors.size] do
        let ct := ind.ctors[k]!
        constructors := constructors + 1
        match readRoots c cx #[(off + 1 + k, ct.typ)] 5000000 with
        | .error e =>
          errors := errors + 1
          IO.println s!"ctor-read-error {names.getD t (toString t)}: {e}"
        | .ok ts =>
          match parameterDomains ind.params.toNat ts[0]! with
          | .error e =>
            errors := errors + 1
            IO.println s!"parameter-error {names.getD t (toString t)}: {e}"
          | .ok ds =>
            for d in ds do
              parameters := parameters + 1
              if RE.hasLet d then lets := lets + 1
              if RE.mentions t d then mentions := mentions + 1
              if famHead t (zeta d) then
                heads := heads + 1
                badBlocks := badBlocks.insert a
                IO.println s!"family-headed parameter {names.getD t (toString t)} ctor={k}"
  IO.println s!"aliases={aliases}; constructors={constructors}; parameters={parameters}"
  IO.println s!"raw self-occurrences={mentions}; zeta-read family heads={heads}; parameter lets={lets}; errors={errors}"
  IO.println s!"affected blocks={badBlocks.size}"
  if badBlocks.isEmpty then IO.println "affected dependent names=0 (the affected block set is empty)"
  return if localOk && aliases == 31 && errors == 0 && heads == 0 then 0 else 1

end Tests.Ix.IxVM.AliasParamHeads
