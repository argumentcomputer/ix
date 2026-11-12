import IxCCTests.KernelFront.Report
import IxCCTests.KernelFront.Bound
import IxCCTests.KernelFront.Hints
import IxCCTests.Src.Support
import IxCCTests.Support.Envelope

/-! # `tests-kernel-front`: the front end over the certified kernel on the committed closures

Since the switch, ingress (`Recheck.ingress`) is the kernel's acceptance and
the producer's annotator and Stage A are the kernel's. On two committed
closures (`phase1-scalar`'s `tuple` and `bench-k1`'s `fib`; every committed
closure is role-bound, as `ix compile` writes it): the kernel accepts it,
ingress reads it, and Stage A accepts the producer's certificate of every root
(`Report.report`). Then the
refusals:

* an unbound envelope (the same records without the binding,
  `Support.Envelope.unboundTwin`);
* a role binding whose bytes do not hash to its address, a closure missing a
  record its root references, a role table naming a record the closure lacks;
* a certificate whose annotation differs from the kernel annotator's in one
  tag (Stage A);
* a program that is not the kernel's reading: a constant's value changed, a
  constructor's field count changed, a constant keyed by another address.

Then the tuple closure with one more record, a constant whose ∀ chain shares
one type at each of 200 steps (`sharedLevelConstants`), is accepted with every
record: the kernel keeps the chain's universe level small.

Then, on every committed role-bound closure: the envelope decodes it and the
kernel accepts it, but for `src-diag`'s `sorry.ixe`, which the kernel declines
for its `sorry`; on `phase1-boundary`'s `fields255` and `tags126`, whose roots
reach a record over IxCC's consumer budget, ingress refuses at `decode`, naming
the record; and on the others under 512 KiB ingress reads every root and every
root that compiles has its certificate accepted by Stage A; on `sorry.ixe`
ingress declines.

Then the role-bound test builder (`IxCCTests.Support.Bound`), with the hostile
family's enumeration case ported to it (`Bound`).

Then the artifact's reducibility hints (`Hints`): the closure the kernel checks
in exponential time without them accepted within a bound, the hint function
the statements name read a second way, and hostile and missing hints through
the front end, each ending in the honest object and certificate or a clean
decline.

The same report on other role-bound closures, written into scratch by the
tree's `ix`, is `tests-kernel-front report …` (`Main`). -/

namespace IxCCTests.KernelFront

open IxCC IxCC.Src
open IxCCTests.Src (Assert expect)

/-- The committed closures the suite tampers with, and their root. -/
def fixtures : List (String × String × String) :=
  [("tuple", "fixtures/corpus/phase1-scalar/tuple", "entry"),
   ("fib", "fixtures/ixon-v4/bench-k1/fib", "entry")]

/-- Every committed role-bound closure under `fixtures/`: not the resource
handoff vectors (unbound, ix's fixture package). -/
def committedClosures : IO (Array System.FilePath) := do
  let all ← System.FilePath.walkDir "fixtures"
  let skip := ["/handoff/"]
  let ixe := all.filter fun p => p.extension == some "ixe" && !skip.any fun s => (p.toString.splitOn s).length > 1
  return ixe.qsort (·.toString < ·.toString)

/-- The closures whose every root reaches a record over IxCC's consumer budget:
the envelope decodes them and the kernel accepts them; ingress refuses every
root at `ingress: decode`, naming the record (their expected decline). -/
def reachRefused : List String :=
  ["phase1-boundary/fields255.ixe", "phase1-boundary/tags126.ixe"]

/-- The closures the kernel declines (`sorryAx`, on purpose). -/
def kernelDeclined : List String := ["src-diag/sorry.ixe"]

/-- Closures below this size are also run root by root through ingress, the
producer and Stage A (`report`); the larger ones have many roots, which the
corpus checks compile. -/
def reportBytes : Nat := 512 * 1024

/-- A closure's sidecar: `NAME.equations.json` beside it, or the RC input's. -/
def sidecarOf (path : System.FilePath) : IO (Option System.FilePath) := do
  let stem := path.withExtension "equations.json"
  if ← stem.pathExists then return some stem
  let rc := path.withFileName "consumer.equations.json"
  if ← rc.pathExists then return some rc
  return none

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
    for (label, bound, root) in fixtures do
      let (bb, bj) ← read bound
      let ub ← IxCCTests.Support.Envelope.unboundTwin s!"{bound}.ixe"
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
      -- ingress, every root produced, Stage A on each certificate
      let rep ← report label bb bj
      expect a (rep.findings.isEmpty && rep.roots.size ≥ 1)
        s!"{label}: ingress refused it or Stage A refused a certificate: {rep.findings}"
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
      let k ← match Recheck.ingress bb bj [root] with
        | .ok k => pure k
        | .error e => throw (IO.userError s!"{label}: kernel ingress: {e.render}")
      let cert ← match Recheck.produce cfg k with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"{label}: kernel produce: {e.render}")
      expect a (Recheck.checkCanonicalRelevance cfg k cert.table cert.relevance)
        s!"{label}: Stage A refused the kernel annotator's own annotation"
      let flipped := { cert.relevance with nodes := flipOne cert.relevance.nodes }
      expect a (flipped != cert.relevance &&
          !Recheck.checkCanonicalRelevance cfg k cert.table flipped)
        s!"{label}: Stage A accepted an annotation with one tag changed"
      -- a program that is not the kernel's reading
      let p := k.program
      let some (_, rootId) := p.roots.head? | throw (IO.userError s!"{label}: no root")
      let wrongValue := p.setTerm (.value rootId) (.natLit 7)
      expect a ((KernelFront.annotate k.kernel.fe k.kernel.rd wrongValue).toOption.isNone)
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
        ingress {rep.ingressMs} ms (kernel {rep.acceptMs} ms); Stage A accepts every certificate"
    -- a role-bound closure carrying a constant whose ∀ chain shares one type: the
    -- kernel's entry checks every record, and the chain's levels stay small
    let (tb, _) ← read "fixtures/corpus/phase1-scalar/tuple"
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
    -- every committed closure: the kernel accepts it, but for the three that
    -- are refused for their own reasons; and the report on the small ones
    let mut accepted := 0
    let mut compared := 0
    for path in ← committedClosures do
      let label := path.toString
      let bytes ← IO.FS.readBinFile path
      match Ixon.V3.decodeAnonymousEnv bytes with
      | .error e =>
        -- every committed closure decodes: IxCC's budget applies to what a root reaches
        expect a false s!"{label}: the envelope does not decode: {e}"
      | .ok env =>
        match KernelFront.accept env with
        | .ok _ =>
          expect a (!kernelDeclined.any (label.endsWith ·)) s!"{label}: accepted, but expected declined"
          accepted := accepted + 1
        | .error r =>
          -- the diagnostics fixture holds `sorry` on purpose
          expect a (kernelDeclined.any (label.endsWith ·) && (match r.outcome with | some .declined => true | _ => false) &&
              (r.message.splitOn "sorryAx").length > 1)
            s!"{label}: the kernel refused it: {r.render}"
          -- what `ixcc` prints: the kernel's line verbatim, then the plain-words line
          if kernelDeclined.any (label.endsWith ·) then
            expect a (r.policy == some .sorryAx) s!"{label}: not classified as the sorryAx policy decline"
            if let some sidecar ← sidecarOf path then
              let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
              let expected := r.render ++ "\n" ++ KernelFront.PolicyDecline.sorryAx.explain
              expect a (match Recheck.ingress bytes bj [] with
                  | .error e => e.stage == .ingress && e.code == "kernel" && e.message == expected
                  | .ok _ => false)
                s!"{label}: ingress did not report the kernel's line and the explanation"
        if reachRefused.any (label.endsWith ·) then
          -- every root reaches a record over IxCC's budget: refused at decode, the record named
          if let some sidecar ← sidecarOf path then
            let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
            expect a (match Recheck.ingress bytes bj [] with
                | .error e => e.stage == .ingress && e.code == "decode" &&
                    (e.message.splitOn "constant exceeds the consumer budget (record").length > 1
                | .ok _ => false)
              s!"{label}: ingress did not refuse the reached over-budget record at decode"
        else if bytes.size < reportBytes then
          if let some sidecar ← sidecarOf path then
            let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
            let rep ← report label bytes bj
            if kernelDeclined.any (label.endsWith ·) then
              -- the diagnostics fixture: ingress declines it (the kernel, `sorry`)
              expect a (rep.bound && rep.findings.size == 1 &&
                  rep.findings.all fun f => f.startsWith "ingress: " &&
                    (f.splitOn "declined").length > 1 && (f.splitOn "sorryAx").length > 1)
                s!"{label}: expected only ingress to decline (sorryAx): {rep.findings}"
            else
              expect a (rep.bound && rep.findings.isEmpty)
                s!"{label}: ingress refused it or Stage A refused a certificate: {rep.findings}"
            compared := compared + 1
    IO.println s!"every committed closure: {accepted} accepted by the kernel, the reached-budget and the \
      kernel's refusals as expected; {compared} under {reportBytes} bytes run through ingress, \
      the producer and Stage A, root by root"
    -- the role-bound test builder, and the hostile enumeration case ported to it
    for line in ← Bound.run a do IO.println line
    IxCCTests.KernelFront.Hints.run a
    IO.println s!"tests-kernel-front: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: kernel front end: {error}"
    return false

end IxCCTests.KernelFront
