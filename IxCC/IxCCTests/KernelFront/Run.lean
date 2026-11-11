import IxCCTests.KernelFront.Diff
import IxCCTests.Src.Support

/-! # `tests-kernel-front`: the kernel front end on the committed role-bound closures

On each committed role-bound closure (`fixtures/ixon-v4/bound`): the kernel
accepts it; the two front ends (`Diff.diff`) give the same program, the same
annotation, the same certificate and the same object, and the kernel front
end's Stage A accepts its own certificate. Then the refusals:

* an unbound envelope (the closures' committed unbound twins);
* a role binding whose bytes do not hash to its address, a closure missing a
  record its root references, a role table naming a record the closure lacks;
* a certificate whose annotation differs from the kernel annotator's in one
  tag (Stage A);
* a program that is not the kernel's reading: a constant's value changed, a
  constructor's field count changed, a constant keyed by another address.

Then the tuple closure with one more record, a constant whose ∀ chain shares
one type at each of 200 steps (`sharedLevelConstants`), is accepted with every
record: the kernel keeps the chain's universe level small.

Then, on every closure of the registered role-bound family
(`fixtures/corpus/phase1-bound`): the kernel accepts it, and the two front ends
give the same program and, root by root, the same annotation, certificate
and object, or refuse the root alike.

Differential runs over other role-bound closures, written into scratch by the
tree's `ix`, are `tests-kernel-front diff …` (`Main`). -/

namespace IxCCTests.KernelFront

open IxCC IxCC.Src
open IxCCTests.Src (Assert expect)

/-- The committed role-bound closures, their unbound twins and their root. -/
def fixtures : List (String × String × String × String) :=
  [("tuple", "fixtures/ixon-v4/bound/tuple", "fixtures/corpus/phase1-scalar/tuple", "entry"),
   ("fib", "fixtures/ixon-v4/bound/fib", "fixtures/ixon-v4/bench-k1/fib", "entry")]

/-- The closures of the registered role-bound family (`fixtures/corpus/phase1-bound`). -/
def boundFamily : List String :=
  ["strictAndOr", "tuple", "bigctor", "typeFormerPolymorphism", "natShiftr"]

def read (stem : String) : IO (ByteArray × Lean.Json) := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  return (bytes, json)

def isRefusal (r : Except KernelFront.Refusal α) (stage : KernelFront.Stage) : Bool :=
  match r with
  | .error e => e.stage == stage
  | .ok _ => false

/-- Two constants whose ∀ chains share one type at every step, at length `k`:
`dag` is `def L : Type := T k` with `T 1 = Prop → Prop`, `T (j+1) = T j → T j`
and each `T j` a sharing entry; `let` is
`def L : (let a0 : Type := Prop; let a(j+1) : Type := aj → aj; …; Type) := Prop`.
Until the kernel built the ∀ rule's level with `mk_imax`'s folds, its level was
shared as a DAG whose tree doubled per step, and each took time doubling in
`k`. -/
def sharedLevelConstants (k : Nat) : List (String × _root_.Ixon.Constant) :=
  let arrow := _root_.Ixon.Expr.leanAll (.var 0) (.var 1)
  let letType := Id.run do
    let mut body : _root_.Ixon.Expr := .sort 1
    for _ in [0:k] do
      body := _root_.Ixon.Expr.leanLet false (.sort 1) arrow body
    return _root_.Ixon.Expr.leanLet false (.sort 1) (.sort 0) body
  let table : Array _root_.Ixon.Expr := (Array.range k).map fun j =>
    if j == 0 then _root_.Ixon.Expr.leanAll (.sort 0) (.sort 0)
    else _root_.Ixon.Expr.leanAll (.share (j - 1).toUInt64) (.share (j - 1).toUInt64)
  let univs : Array _root_.Ixon.Univ := #[.zero, .succ .zero]
  [("dag", ⟨.defn ⟨.defn, .safe, 0, .sort 1, .share (k - 1).toUInt64⟩, table, #[], univs⟩),
   ("let", ⟨.defn ⟨.defn, .safe, 0, letType, .sort 0⟩, #[], #[], univs⟩)]

/-- Flip the class of one argument tag (the first relevant one). -/
def flipOne : List (TermKey × List Relevance.Tag) → List (TermKey × List Relevance.Tag)
  | [] => []
  | (k, ts) :: rest =>
    match ts.findIdx? (fun | .arg .rel => true | _ => false) with
    | some i => (k, ts.set i (.arg .type)) :: rest
    | none => (k, ts) :: flipOne rest

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    for (label, bound, unbound, root) in fixtures do
      let (bb, bj) ← read bound
      let (ub, _) ← read unbound
      let benv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bb)
      let uenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv ub)
      -- acceptance
      let acc ← match KernelFront.accept benv with
        | .ok acc => pure acc
        | .error e => throw (IO.userError s!"{label}: the kernel refused the role-bound closure: {e}")
      expect a (acc.records.length == benv.consts.size && acc.decls.size > 0)
        s!"{label}: the kernel's entry did not receive every record"
      expect a (isRefusal (KernelFront.accept uenv) .envelope)
        s!"{label}: the unbound twin was not refused as unbound"
      -- the differential
      let rep ← diff label bb bj
      expect a (rep.findings.isEmpty && rep.program.isEmpty && rep.roots.size ≥ 1)
        s!"{label}: the front ends differ: {rep.program} {rep.findings}"
      -- refusals of the bytes
      let some b := benv.binding | throw (IO.userError s!"{label}: not role-bound")
      let tampered := { benv with binding := some { b with bytes := b.bytes.push 0 } }
      expect a (isRefusal (KernelFront.accept tampered) .binding)
        s!"{label}: a binding section that does not hash to its address was accepted"
      let some (rootAddr, _) := (← IO.ofExcept (Src.Hints.ofK1Json bj)).roots[0]?
        | throw (IO.userError s!"{label}: the sidecar names no root")
      let some rootBytes := benv.consts[rootAddr]? | throw (IO.userError s!"{label}: no root record")
      let rootConst ← IO.ofExcept (Ixon.V3.decodeConstant rootBytes)
      let some dep := rootConst.value.refs.find? (benv.consts.contains ·)
        | throw (IO.userError s!"{label}: the root references no record")
      let missing := { benv with consts := benv.consts.erase dep }
      expect a ((KernelFront.accept missing).toOption.isNone)
        s!"{label}: a closure missing a record its root references was accepted"
      let some (_, bnat) := (acc.table.bound.find? (·.1 == .nat))
        | throw (IO.userError s!"{label}: the table binds no Nat")
      let natAddr : Ixon.Address := match Ixon.Address.ofBytes? bnat.hash with
        | some x => x
        | none => default
      let unboundNat := { benv with consts := benv.consts.erase natAddr }
      expect a ((KernelFront.accept unboundNat).toOption.isNone)
        s!"{label}: a role table naming a record the closure lacks was accepted"
      -- Stage A
      let cfg : Recheck.Config := { names := [root] }
      let k ← match KernelFront.ingress bb bj [root] with
        | .ok k => pure k
        | .error e => throw (IO.userError s!"{label}: kernel ingress: {e.render}")
      let cert ← match KernelFront.produce cfg k with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"{label}: kernel produce: {e.render}")
      expect a (KernelFront.checkCanonicalRelevance cfg k cert.table cert.relevance)
        s!"{label}: Stage A refused the kernel annotator's own annotation"
      let flipped := { cert.relevance with nodes := flipOne cert.relevance.nodes }
      expect a (flipped != cert.relevance &&
          !KernelFront.checkCanonicalRelevance cfg k cert.table flipped)
        s!"{label}: Stage A accepted an annotation with one tag changed"
      -- a program that is not the kernel's reading
      let p := k.inp.program
      let some (_, rootId) := p.roots.head? | throw (IO.userError s!"{label}: no root")
      let wrongValue := p.setTerm (.value rootId) (.natLit 7)
      expect a ((KernelFront.annotate k.fe k.rd wrongValue).toOption.isNone)
        s!"{label}: a value that is not the kernel's reading was annotated"
      let ctorIds := (List.range p.size).filter fun c =>
        match p.decl? c with | some (.ctor ..) => true | _ => false
      let some c0 := ctorIds.head? | throw (IO.userError s!"{label}: no constructor")
      let wrongCtor := match p.decl? c0 with
        | some (.ctor s l i x pa f ty) => p.setDecl c0 (.ctor s l i x pa (f + 1) ty)
        | _ => p
      expect a ((KernelFront.Reading.build acc wrongCtor).toOption.isNone)
        s!"{label}: a constructor with another field count was read as the kernel's"
      let wrongAddr : Src.Program := { p with consts := p.consts.modify rootId fun e =>
        { e with addr := Ixon.Address.replicate 7 } }
      expect a ((KernelFront.Reading.build acc wrongAddr).toOption.isNone)
        s!"{label}: a constant keyed by another address was read as the kernel's"
      IO.println s!"{label}: accepted, {acc.records.length} records, {acc.decls.size} declarations; \
        ingress {rep.newIngressMs} ms (kernel {rep.newAcceptMs} ms) against {rep.oldIngressMs} ms \
        (erased typing {rep.oldTypingMs} ms); annotation, certificate and object the same"
    -- a role-bound closure carrying a constant whose ∀ chain shares one type: the
    -- kernel's entry checks every record, and the chain's levels stay small
    let (tb, _) ← read "fixtures/ixon-v4/bound/tuple"
    let tenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv tb)
    for (name, c) in sharedLevelConstants 200 do
      let bytes := _root_.Ixon.serConstant c
      let env := { tenv with consts := tenv.consts.insert (Ixon.Address.blake3Pure bytes) bytes }
      let t0 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => KernelFront.accept env
      let t1 ← IO.monoMsNow
      match r with
      | .ok acc =>
        expect a (acc.records.length == tenv.consts.size + 1)
          s!"tuple with the {name} chain: the kernel's entry did not receive every record"
        IO.println s!"tuple with the {name} chain at length 200 ({bytes.size} bytes): accepted, \
          {acc.records.length} records, {t1 - t0} ms"
      | .error e =>
        throw (IO.userError s!"tuple with the {name} chain at length 200: refused: {e}")
    -- the registered role-bound family: acceptance and the differential, every root
    for name in boundFamily do
      let label := s!"phase1-bound/{name}"
      let (bb, bj) ← read s!"fixtures/corpus/phase1-bound/{name}"
      let rep ← diff label bb bj
      expect a (rep.bound && rep.newAccept.startsWith "accepted" && rep.findings.isEmpty &&
          rep.program.isEmpty && rep.roots.size ≥ 1)
        s!"{label}: {rep.newAccept}; the front ends differ: {rep.program} {rep.findings}"
      IO.println s!"{label}: accepted, {rep.records} records, {rep.roots.size} roots alike; \
        kernel {rep.newAcceptMs} ms against erased typing {rep.oldTypingMs} ms"
    IO.println s!"tests-kernel-front: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: kernel front end: {error}"
    return false

end IxCCTests.KernelFront
