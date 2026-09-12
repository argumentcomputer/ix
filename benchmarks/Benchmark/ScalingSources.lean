import Compilatrix.X86.PhysicalHeapSources

/-! Bounded, canonical Ixon workload families. The parameter describes source
structure; reports also count the actual generated IR. No intermediate program
or native plan is supplied by the generator. -/
namespace Benchmark.Scaling
open Compilatrix Compilatrix.Ixon

def policy : Coverage.Policy :=
  { limits := Pipeline.defaultLimits
    checkFuel := 10000, eraseFuel := 10000, validateFuel := 10000
    lowerFuel := 10000, maxDepth := 10000, evalFuel := 100000
    controlFuel := 100000, heapFuel := 100000 }

def definition (typ value : Expr) (refs : Array Address := #[]) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

def natInductive : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

def declarations (count : Nat) : Except String Coverage.Source := do
  let block ← Coverage.addressed {
    info := .muts #[.indc natInductive], sharing := #[], refs := #[], univs := #[.zero] }
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := block.1 }))
  let nat : Expr := .ref 0 #[]
  let typ : Expr := .all .many .shared nat nat
  let stable ← Coverage.addressed (definition typ (.lam .many nat (.var 0)) #[natType.1])
  let mut entries := []
  for i in [:count] do
    let entry ← Coverage.addressed (X86.ValidatedScalar.constant (1000 + i))
    entries := entry :: entries
  return {
    name := "declarations", constants := entries ++ [stable, natType, block], root := stable.1
    literals := (List.range count).map (1000 + ·), policy, expected := .scalar 0 false }

def branches (count : Nat) : Except String Coverage.Source := do
  let nat : Expr := .recur 0 #[]
  let typ : Expr := .all .many .shared nat nat
  let mut members : Array MutConst := #[.indc natInductive]
  for i in [:count] do
    let successor := if i == 0 then Expr.var 0 else .app (.recur i.toUInt64 #[]) (.var 0)
    members := members.push (.recr {
      k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := 0
      typ, rules := #[{ fields := 0, rhs := .nat 0 },
        { fields := 1, rhs := .lam .many nat successor }] })
  members := members.push (.defn {
    kind := .defn, safety := .safe, lvls := 0, typ
    value := .lam .many nat (.app (.recur count.toUInt64 #[]) (.var 0)) })
  let block ← Coverage.addressed {
    info := .muts members, sharing := #[], refs := #[X86.ValidatedScalar.literalAddress 0], univs := #[.zero] }
  let entry ← Coverage.addressed (projection (.dPrj { idx := (count + 1).toUInt64, block := block.1 }))
  return {
    name := "branches", constants := [block, entry], root := entry.1
    literals := [0], natBlock := some block.1, policy, expected := .scalar 0 false }

def allocations (count : Nat) : Except String Coverage.Source := do
  let base ← X86.PhysicalHeap.Examples.source "leaf-call"
  let some natType := base.constants[1]? | throw "allocation generator Nat type is missing"
  let some boxType := base.constants[2]? | throw "allocation generator box type is missing"
  let some builder := base.constants[4]? | throw "allocation generator builder is missing"
  let some consumer := base.constants[5]? | throw "allocation generator consumer is missing"
  let mut body : Expr := .var 0
  for _ in [:count] do
    body := .app (.app (.ref 3 #[]) (.app (.ref 2 #[]) (.sort 0))) body
  let nat : Expr := .ref 0 #[]
  let entry ← Coverage.addressed (definition (.all .many .shared nat nat) (.lam .many nat body)
    #[natType.1, boxType.1, builder.1, consumer.1])
  return { base with name := "allocations", constants := base.constants.take 6 ++ [entry], root := entry.1, policy }

def callDepth (count : Nat) (edited : Bool) : Except String Coverage.Source := do
  let base ← X86.PhysicalHeap.Examples.source "shared-pair"
  let some natType := base.constants[1]? | throw "call generator Nat type is missing"
  let some boxType := base.constants[2]? | throw "call generator box type is missing"
  let some ctor := base.constants[3]? | throw "call generator constructor is missing"
  let nat : Expr := .ref 0 #[]
  let typ : Expr := .all .many .shared nat nat
  let stable ← Coverage.addressed (definition typ (.lam .many nat (.var 0)) #[natType.1])
  let leaf ← Coverage.addressed (definition typ
    (.lam .many nat (.prj 1 (if edited then 0 else 1)
      (.app (.app (.ref 2 #[]) (.var 0)) (.var 0)))) #[natType.1, boxType.1, ctor.1])
  -- Callers precede their dependencies, exercising the coverage fixpoint.
  let mut entries := [leaf]
  let mut previous := leaf.1
  for _ in [1:count] do
    let entry ← Coverage.addressed (definition typ
      (.lam .many nat (.app (.ref 1 #[]) (.var 0))) #[natType.1, previous])
    entries := entry :: entries
    previous := entry.1
  return { base with
    name := "call-depth", constants := entries ++ [stable] ++ base.constants.take 4
    root := previous, policy }

/-- Minimal type projections isolate the inclusive candidate cap from the
combined source-node charge. All constants still have canonical source keys. -/
def candidates (count : Nat) : Except String Coverage.Source := do
  let mut entries := []
  let mut root := Address.blake3 ByteArray.empty
  for i in [:count] do
    let block ← Coverage.addressed {
      info := .muts #[.indc { natInductive with ctors := #[] }], sharing := #[]
      refs := #[X86.ValidatedScalar.literalAddress i], univs := #[.zero] }
    let entry ← Coverage.addressed (projection (.iPrj { idx := 0, block := block.1 }))
    entries := entry :: block :: entries
    root := entry.1
  return { name := "candidates", constants := entries, root, literals := [], policy, expected := .scalar 0 false }

def source (family : String) (count : Nat) (edited : Bool := false) : Except String Coverage.Source := do
  if count == 0 || count > 1024 then throw "scaling parameter must be in 1..1024"
  if edited && family != "call-depth" then throw "only call-depth has a dependency edit"
  match family with
  | "declarations" => declarations count
  | "call-depth" => callDepth count edited
  | "branches" => branches count
  | "allocations" => allocations count
  | "candidates" => candidates count
  | _ => throw "unknown compiler-scaling family"

def expected (family : String) (count : Nat) (_edited : Bool) (argument : Nat) : Nat :=
  if family == "declarations" then argument
  else if family == "call-depth" then argument
  else if family == "branches" then argument - count
  else argument

end Benchmark.Scaling
