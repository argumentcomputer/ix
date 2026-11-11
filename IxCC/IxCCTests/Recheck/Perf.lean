import IxCCTests.Recheck.Deep

/-! # The producer's cost: scaling inputs and stage timings

The producer (`Recheck.produceWith`, `RcReplay.produceWith`, the oracles they
call) is untrusted and is not bounded by the checker's budgets, so its cost is
measured separately. This module writes the scaling inputs as Ixon v4 bytes
and runs the producer and the checker on a closure stage by stage, timing each
stage, so that a script around `ixcc compile` and `ixcc check-cert` can say
where the time goes.

* `dag d`: `k (a b : E) : E := a` and `main : E`, a balanced `k`-tree of depth
  `d` over `c₁`, stored as a share DAG of `d + 1` nodes (`2^(d+1) - 1` calls of
  `k` once expanded).
* `fns n`: `n + 1` functions over `inductive T | leaf | node (l r : T)`:
  `f₀ x := node x x` and `fᵢ x := let a := fᵢ₋₁ x; let b := f_(i/2) x; t₆`,
  where `t₀ := node a b` and `tⱼ₊₁ := node tⱼ tⱼ` (a share DAG, 127
  constructors once expanded, so no `fᵢ` is small enough to inline); `main :=
  fₙ leaf`. A closure of many small, distinct, non-recursive definitions.
  `fns6 n` is the same with bodies `t₅` (63 constructors), and `body d` has
  four functions with bodies `t_(d-1)`.
* the shapes of `Deep` (`tree`, `wide`, `many`, `deep`, `deepApp`, `deepLet`).

`stages` mirrors `Recheck.produceWith` (and, for `--rc on` and `auto`, the
plain-RC producer and the policy choice of `RcReplay.produceAuto`) and then
the checker (`Recheck.run`, `RcReplay.run`), timing each step and counting
its allocations (the runtime's heartbeats); with `PERF_DETAIL` set it also
times the allocator's and `Backend.finish`'s parts. `anfStages` does the same
from an Anf program (`anfProgram`: the loop shapes `loop` and `loop0`, or one
of `Deep.chainProgram`'s) through the producer's back end and the checker's.
They are measurement tools; `ixcc compile` remains what the suites test. -/

namespace IxCCTests.Recheck.Perf

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Recheck.Hostile
open IxCCTests.Recheck.Deep (treeEnv manyEnv deepEnv deepAppEnv deepLetEnv)
open IxCCTests.IxonV3.TypingFixtures (store arrow lambda)
open IxCCTests.Support.Bound (loadBase addTree)

/-- `dag d` (see the module note). -/
def dagEnv (env0 : Env) (d : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  let (e, k) := store b.env
    ⟨defn (arrow enumC (arrow enumC enumC)) (lambda enumC (lambda enumC (.var 1))), #[], #[b.enumI], #[]⟩
  -- refs: 0 E, 1 k, 2 c₁
  let mut sh : Array X := #[.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 2 #[])]
  for i in [1:d+1] do
    let prev : X := .share (i - 1).toUInt64
    sh := sh.push (.app (.app (.ref 1 #[]) prev) prev)
  let (e, main) := store e ⟨defn enumC (.share d.toUInt64), sh, #[b.enumI, k, b.ctors[1]!], #[]⟩
  return (e, main)

/-- `fns n` (see the module note), with bodies `depth` constructor levels deep. -/
def fnsEnv (env0 : Env) (n : Nat) (depth : Nat := 7) : Env × Addr := Id.run do
  let (e, t) := addTree env0
  let tI := t.ind
  let leaf := t.ctors[0]!
  let node := t.ctors[1]!
  let tT : X := .ref 0 #[]
  -- f₀ x := node x x; refs: 0 T, 1 node
  let (e, f0) := store e
    ⟨defn (arrow tT tT) (lambda tT (.app (.app (.ref 1 #[]) (.var 0)) (.var 0))), #[], #[tI, node], #[]⟩
  let mut e := e
  let mut fs : Array Addr := #[f0]
  let c : LetContract := { nonDep := false }
  for i in [1:n+1] do
    -- refs: 0 T, 1 node, 2 fᵢ₋₁, 3 f_(i/2); under the two lets: 0 b, 1 a, 2 x
    let mut sh : Array X := #[.app (.app (.ref 1 #[]) (.var 1)) (.var 0)]
    for j in [1:depth] do
      let prev : X := .share (j - 1).toUInt64
      sh := sh.push (.app (.app (.ref 1 #[]) prev) prev)
    let body : X := .letE c tT (.app (.ref 2 #[]) (.var 0))
      (.letE c tT (.app (.ref 3 #[]) (.var 1)) (.share (depth - 1).toUInt64))
    let (e', f) := store e ⟨defn (arrow tT tT) (lambda tT body), sh, #[tI, node, fs[i - 1]!, fs[i / 2]!], #[]⟩
    e := e'
    fs := fs.push f
  -- main := fₙ leaf; refs: 0 T, 1 fₙ, 2 leaf
  let (eM, main) := store e ⟨defn tT (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[tI, fs[n]!, leaf], #[]⟩
  return (eM, main)

/-- A scaling shape's environment and root. -/
def shapeEnv (env0 : Env) (name : String) (n : Nat) : Except String (Env × Addr) :=
  match name with
  | "dag" => .ok (dagEnv env0 n)
  | "fns" => .ok (fnsEnv env0 n)
  | "fns6" => .ok (fnsEnv env0 n 6)
  | "body" => .ok (fnsEnv env0 4 n)
  | "tree" => .ok (treeEnv env0 n)
  | "wide" => let (e, _, _, main) := ampEnv env0 n 0; .ok (e, main)
  | "many" => .ok (manyEnv env0 n)
  | "deep" => .ok (deepEnv env0 n)
  | "deepApp" => .ok (deepAppEnv env0 n)
  | "deepLet" => .ok (deepLetEnv env0 n)
  | _ => .error s!"unknown shape {name}"

/-- `tests-recheck --perf-write DIR SHAPE N`: `SHAPE-N.ixe` and
`SHAPE-N.equations.json` in `DIR`. -/
def write (dir : System.FilePath) (name : String) (n : Nat) : IO Unit := do
  let (e, main) ← IO.ofExcept (shapeEnv (← loadBase) name n)
  let bs := bytes e
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"{name}-{n}.ixe") bs
  IO.FS.writeFile (dir / s!"{name}-{n}.equations.json") (sidecar [("main", main)]).compress
  IO.println s!"{name}-{n}: {bs.size} bytes"

/-! ## Stage timings -/

/-- Per stage, its label, wall time in microseconds and allocations (the
runtime's heartbeat count, `IO.getNumHeartbeats`: one per small object
allocated), in order. -/
abbrev Rows := IO.Ref (Array (String × Nat × Nat))

/-- Run a pure stage when this action runs, recording its wall time and
allocations. -/
def stage {α : Type} (rows : Rows) (label : String) (x : Unit → Except Recheck.Err α) : IO α := do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure x
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  rows.modify (·.push (label, (t1 - t0) / 1000, h1 - h0))
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {e.render}")

def errOf (stage : Recheck.Stage) (code : String) (message : String) : Recheck.Err :=
  { stage, code, message }

/-- `Anf.Pipeline.produce`, step by step. -/
def middle (rows : Rows) (B : Anf.Pipeline.Budgets) (L : Lam.Program) : IO Anf.Program := do
  let anfErr := errOf .anf "anf.produce"
  let mut P ← stage rows "P1" fun _ => (Anf.Pipeline.checkLamNodes L >>= Anf.convert).mapError anfErr
  let (_, P2, _) ← stage rows "P2 produce" fun _ => (Anf.Shrink.produce B.shrink P).mapError anfErr
  P := P2
  P ← stage rows "prune" fun _ => .ok (Anf.Prune.run P)
  for phase in [0:4] do
    if phase > 0 then
      let Q := P
      let sc ← stage rows "P4 oracle" fun _ => .ok (Anf.Specialize.produce B.spec (phase - 1) Q)
      let P4 ← stage rows "P4 run" fun _ => (Anf.Specialize.run sc Q).mapError anfErr
      if phase > 1 && P4.size == P.size then break
      let (_, P2, _) ← stage rows "P2 produce" fun _ => (Anf.Shrink.produce B.shrink P4).mapError anfErr
      P := P2
    for _ in [0:B.inline.rounds] do
      let Q := P
      let r ← stage rows "P3 oracle" fun _ => .ok (Anf.Inline.produce B.inline Q)
      if r.isEmpty then break
      let (P3, _) ← stage rows "P3 round" fun _ => (Anf.Inline.round Q r).mapError anfErr
      let (_, P2, _) ← stage rows "P2 produce" fun _ => (Anf.Shrink.produce B.shrink P3).mapError anfErr
      P := P2
  let Q := P
  stage rows "prune" fun _ => .ok (Anf.Prune.run Q)

/-- What the producer's front half made (`RcReplay.produceFir`'s parts). -/
structure Front where
  src : Src.Program
  fir : Fir.Program
  tableCert : Src.Table.TableCert
  relevance : Src.Relevance.Ann
  mid : Anf.Pipeline.Cert

/-- The producer's front half: `Recheck.produceWith` up to `Fir.lower`. -/
def front (rows : Rows) (cfg : Recheck.Config) (inp : Recheck.Input) : IO Front := do
  let P := inp.program
  let (table, _, _) ← stage rows "table.build" fun _ => .ok (Src.Table.build cfg.table P inp.hints.proposals)
  let p0 := { P with table }
  stage rows "table.validate" fun _ => (Src.Table.validate cfg.table p0).mapError (errOf .table "table.entry")
  let ann ← stage rows "annotate" fun _ =>
    (inp.kernel.annotateChecked p0).mapError (errOf .relevance "relevance-oracle")
  let (src, checked) ← stage rows "annotation" fun _ =>
    (Src.Recheck.annotation p0 ann).mapError fun _ => errOf .relevance "relevance" "refused"
  stage rows "admit" fun _ =>
    match Src.admit src (Recheck.sidecarName inp.hints) cfg.admit with
    | .ok _ => .ok ()
    | .error ds => .error (errOf .admit "admit" ((ds[0]?.map (·.render)).getD "declined"))
  let (lam, _) ← stage rows "erase" fun _ => (Lam.erase src checked).mapError Recheck.Err.ofErase
  -- the certificate's middle end, as `Anf.Pipeline.produce` makes it
  let trace ← stage rows "(middle certificate)" fun _ =>
    (Anf.Pipeline.produce cfg.budgets lam).mapError (errOf .anf "anf.produce")
  let anf ← middle rows cfg.budgets lam
  let sizes := anf.globalList.map fun (_, gd) => gd.body.nodes
  rows.modify (·.push (s!"  (Anf: {anf.size} globals, {sizes.foldl (· + ·) 0} nodes, largest \
    {sizes.foldl max 0}, back work {Anf.backWork anf} of {Anf.maxBackWork})", 0, 0))
  let fir ← stage rows "fir.lower" fun _ => (Fir.lower anf).mapError Recheck.Err.ofFir
  return { src, fir, tableCert := Src.Table.TableCert.ofTable table, relevance := ann, mid := trace.cert }

/-- Allocation, frames, tunnelling and block order: the producer's back end
from Lir. -/
def back (rows : Rows) (env : Xv.Xl.Env) (lir : Lir.Program)
    (reps : Lir.FunId → Option (List Xv.Stacking.ArgRep)) :
    IO (List Xv.Alloc.Output × List Xv.Stacking.FrameLayout × X86.Layout.Order) := do
  let (xv, _) ← stage rows "select.run" fun _ => (Xv.Select.run lir).mapError Recheck.Err.ofSelect
  let r ← stage rows "alloc.run" fun _ => (Xv.Alloc.runProducer env xv).mapError (errOf .alloc "alloc.fallback")
  if (← IO.getEnv "PERF_DETAIL").isSome then
    -- the allocator's parts again, function by function (diagnosis only)
    for h : fi in [:xv.funcs.size] do
      let f := xv.funcs[fi]
      let o ← stage rows "  alloc: linear scan" fun _ =>
        (Xv.Alloc.LinearScan.run env f).mapError (errOf .alloc "alloc.scan")
      stage rows "  alloc: validate" fun _ =>
        (Xv.Validate.func env fi f o).mapError fun e => errOf .alloc "alloc.validate" e.text
    stage rows "  alloc: final Validate.run" fun _ =>
      (Xv.Validate.run env xv r.outs).map (fun _ => ()) |>.mapError (errOf .alloc "alloc.final")
    let blocks := xv.funcs.foldl (fun n f => n + f.blocks.size) 0
    let insts := xv.funcs.foldl (fun n f => n + f.blocks.foldl (fun m b => m + b.body.size + 1) 0) 0
    let widest := xv.funcs.foldl (fun n f => max n f.blocks.size) 0
    rows.modify (·.push (s!"  (Xv: {xv.funcs.size} functions, {blocks} blocks, {insts} instructions, \
      at most {widest} blocks in a function)", 0, 0))
  let layouts ← stage rows "stacking.produce" fun _ => .ok (Xv.Stacking.produce r.program)
  let stacked ← stage rows "stacking.run" fun _ =>
    (Xv.Stacking.run r.program layouts reps env).mapError (Recheck.Err.ofBackend ∘ .stacking)
  let tunnelled ← stage rows "tunnel" fun _ => .ok (X86.Layout.tunnel stacked.program)
  let order ← stage rows "order.produce" fun _ => .ok (X86.Layout.Order.produce tunnelled stacked.shape)
  return (r.outs, layouts, order)

/-- The zero-RC certificate from a front half (`RcReplay.finishZeroRcCert`). -/
def zeroCert (rows : Rows) (cfg : Recheck.Config) (f : Front) : IO Recheck.Cert := do
  let C ← stage rows "cfg.lower" fun _ => .ok (Cfg.lower (Own.immortal f.fir))
  stage rows "checkParams" fun _ => Recheck.checkParams cfg C (C.exports.zipIdx.map fun (g, i) => (i, g))
  let lowered ← stage rows "rt.lower" fun _ => (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
  let (alloc, frames, order) ← back rows cfg.env lowered.program lowered.reps
  return { table := f.tableCert, relevance := f.relevance, mid := f.mid, alloc, frames, order }

/-- The plain-RC certificate from a front half (`RcReplay.finishPlainRcCert`). -/
def plainCert (rows : Rows) (cfg : Recheck.Config) (f : Front) : IO Recheck.RcReplay.Cert := do
  let own ← stage rows "own.canonical" fun _ => .ok (Own.Plain.Program.canonicalForSrc f.src f.fir)
  let ownJson ← stage rows "own.encode" fun _ => .ok (Own.Plain.Certificate.encode own.bodies)
  let admitted ← stage rows "own.admit" fun _ =>
    (Own.Plain.Certificate.admit f.fir ownJson).mapError (errOf .cert "own.plain")
  let candidate ← stage rows "rc.generate" fun _ =>
    match Cfg.Rc.generate f.fir admitted.bodies with
    | some c => .ok c
    | none => .error (errOf .rt "rc.cfg" "ownership candidate lowering declined")
  stage rows "rc.scope" fun _ =>
    if Cfg.Rc.checkScopedProgram f.fir admitted.bodies candidate then .ok ()
    else .error (errOf .rt "rc.scope" "scoped dense-source RC gate refused")
  stage rows "checkParams" fun _ =>
    Recheck.checkParams cfg candidate.base (candidate.base.exports.zipIdx.map fun (g, i) => (i, g))
  let lowered ← stage rows "rc.lower" fun _ =>
    (Cfg.Rc.Public.lower { names := cfg.names } f.fir admitted.bodies candidate).mapError (errOf .rt "rc.lower")
  let reps : Lir.FunId → Option (List Xv.Stacking.ArgRep) :=
    (⟨lowered.runtime, lowered.drop⟩ : Cfg.Rc.Public.Lowered).reps
  let layout : Cfg.Rc.Native.Layout := ⟨candidate.base.size, candidate.base.ctors.filter (fun c => c.arity > 0)⟩
  let (alloc, frames, order) ← back rows (layout.env cfg.env) lowered.runtime.program reps
  let base : Recheck.Cert :=
    { table := f.tableCert, relevance := f.relevance, mid := f.mid, alloc, frames, order }
  return { base, own := ownJson }

/-- `Recheck.run` from Cfg on, step by step. -/
def checkBack (rows : Rows) (cfg : Recheck.Config) (C : Cfg.Program) (root : Addr)
    (c : Recheck.Cert) : IO Nat := do
  stage rows "check rt.checkSwitches" fun _ => (Rt.checkSwitches C).mapError Recheck.Err.ofSwitch
  let l ← stage rows "check rt.lower" fun _ => (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
  let xv ← stage rows "check select" fun _ => (Xv.Select.select l.program).mapError Recheck.Err.ofSelect
  stage rows "check validate" fun _ => (Xv.Validate.program cfg.env xv c.alloc).mapError Recheck.Err.ofValidate
  let xl ← stage rows "check apply" fun _ => (Xv.Alloc.applyProgram xv c.alloc).mapError (errOf .alloc "alloc.apply")
  let bcfg := Recheck.backendConfig cfg l root c
  let stacked ← stage rows "check stacking.run" fun _ =>
    (Xv.Stacking.run xl c.frames bcfg.reps bcfg.env).mapError (Recheck.Err.ofBackend ∘ .stacking)
  let tunnelled ← stage rows "check tunnel" fun _ => .ok (X86.Layout.tunnel stacked.program)
  let (program, pos) ← stage rows "check layout.run" fun _ =>
    (X86.Layout.run tunnelled stacked.shape c.order).mapError (Recheck.Err.ofBackend ∘ .layout)
  let exports := stacked.exports.map fun e => (e.symbol, UInt32.ofNat ((pos.get? e.block).getD e.block))
  stage rows "check checkSymbols" fun _ => Recheck.checkSymbols stacked.exports
  let a ← stage rows "check finish" fun _ =>
    (Backend.finish xl.main stacked program exports (cfg.provenance.getD (Recheck.defaultProvenance root))).mapError
      Recheck.Err.ofBackend
  if (← IO.getEnv "PERF_DETAIL").isSome then
    -- `Backend.finish`'s parts again (diagnosis only)
    let checked ← stage rows "  finish: Program.checkK" fun _ =>
      program.checkK.mapError (Recheck.Err.ofBackend ∘ .check)
    let stream ← stage rows "  finish: Stream.encodeK" fun _ =>
      (X86.Stream.encodeK checked).mapError (Recheck.Err.ofBackend ∘ .stream)
    let some entry := stacked.exports.find? (·.fn == xl.main) | pure ()
    let _ ← stage rows "  finish: ELF.writeCheckedK" fun _ =>
      (X86.ELF.writeCheckedK
        { encoded := stream.output, entryBlock := program.entry, exportName := entry.symbol,
          exports := exports.filter (·.1 != entry.symbol),
          provenance := cfg.provenance.getD (Recheck.defaultProvenance root) }).mapError
        (Recheck.Err.ofBackend ∘ .elf)
    rows.modify (·.push (s!"  (text {a.encoded.text.size} bytes, {program.blocks.size} x86 blocks)", 0, 0))
  return a.object.size

/-- `Recheck.run`, step by step. -/
def check (rows : Rows) (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.Cert) : IO Nat := do
  let (src, checked) ← stage rows "check front" fun _ => Recheck.front cfg P c
  let (lam, _) ← stage rows "check erase" fun _ => (Lam.erase src checked).mapError Recheck.Err.ofErase
  let (_, _, _, C) ← stage rows "check middle" fun _ => Recheck.middle c src lam
  stage rows "check checkParams" fun _ =>
    Recheck.checkParams cfg C (C.exports.zipIdx.map fun (g, i) => (i, g))
  checkBack rows cfg C ((src.roots.head?.map (·.1)).getD default) c

/-- The summed time and allocations of each label, in first-appearance order,
with its count. -/
def summary (rows : Array (String × Nat × Nat)) : Array (String × Nat × Nat × Nat) := Id.run do
  let mut out : Array (String × Nat × Nat × Nat) := #[]
  for (l, us, a) in rows do
    match out.findIdx? (·.1 == l) with
    | some i => out := out.modify i fun (l, t, b, n) => (l, t + us, b + a, n + 1)
    | none => out := out.push (l, us, a, 1)
  return out

def ms (us : Nat) : String :=
  let s := toString (us / 1000) ++ "." ++ toString (us % 1000 / 100)
  s

/-- Whether a row is the producer's (not ingress, the checker's or a
diagnostic one). -/
def producerRow (l : String) : Bool :=
  !(l.startsWith "check" || l.startsWith " " || l == "ingress" || l == "(middle certificate)")

/-- Print the outcome and the stage table: the producer's total (every stage
but ingress, the checker's and the diagnostic rows), the checker's total, and
each stage, with its allocations. -/
def report (rows : Rows) (label : String) (result : Except IO.Error String) : IO UInt32 := do
  let out := match result with
    | .ok s => s
    | .error e => s!"stopped: {e}"
  let rs ← rows.get
  let produce := rs.foldl (fun (t, b) (l, us, a) => if producerRow l then (t + us, b + a) else (t, b)) (0, 0)
  let checkT := rs.foldl (fun (t, b) (l, us, a) => if l.startsWith "check" then (t + us, b + a) else (t, b)) (0, 0)
  IO.println s!"{label}: {out}"
  IO.println s!"  produce {ms produce.1} ms ({produce.2} allocations), check {ms checkT.1} ms ({checkT.2} allocations)"
  for (l, us, a, n) in summary rs do
    IO.println s!"  {l}: {ms us} ms{if n > 1 then s!" ({n}×)" else ""}{if a > 0 then s!", {a} allocations" else ""}"
  return 0

/-- `tests-recheck --perf-stages FILE.ixe EQUATIONS.json MODE [ROOT...]`: the
producer (`MODE` `off`, `on` or `auto`, as `ixcc compile --rc MODE`) and then
the checker on its certificate, each stage timed (milliseconds; a stage run
more than once is summed, with its count). Ingress runs the certified kernel's
acceptance, as in `ixcc compile`. -/
def stages (file eqs : System.FilePath) (mode : String) (roots : List String) : IO UInt32 := do
  let rows : Rows ← IO.mkRef #[]
  let bs ← IO.FS.readBinFile file
  let text ← IO.FS.readFile eqs
  let json ← IO.ofExcept (Lean.Json.parse text)
  let inp ← stage rows "ingress" fun _ => Recheck.ingress bs json roots
  let cfg := Recheck.Config.forInput {} inp
  let result ← (do
    let f ← front rows cfg inp
    let policy ← if mode == "auto" then
        stage rows "rc.select" fun _ => .ok (Own.Plain.selectRcPolicyForSrc f.src f.fir)
      else pure (if mode == "on" then Own.Plain.RcPolicy.plainRc else .zeroRc)
    let zero : IO String := do
      let c ← zeroCert rows cfg f
      let size ← check rows cfg inp.program c
      pure s!"zero-rc, certificate {c.toText.utf8ByteSize} bytes, object {size} bytes"
    let plain : IO String := do
      let c ← plainCert rows cfg f
      let a ← stage rows "check (plain-RC replay)" fun _ => Recheck.RcReplay.run cfg inp.program c
      pure s!"plain-rc, certificate {c.toText.utf8ByteSize} bytes, object {a.backend.object.size} bytes"
    match policy with
    | .zeroRc => zero
    | .plainRc =>
      if mode == "auto" then
        match ← plain.toBaseIO with
        | .ok s => pure s
        | .error e => return s!"{← zero} (immortal fallback after: {e})"
      else plain :
    IO String).toBaseIO
  report rows s!"{file} --rc {mode}" result

/-! ## The back end from Anf -/

/-- A self-recursive loop body: `k` two-way branches in sequence, each
joining before the next (through a join point of `arity` parameters: with
one, the arms pass the join point different literals, so both arms do work;
with none, both arms are empty jumps that tunnelling removes, so the branch's two
edges reach the same block), then the self tail call (`self x`), which Cfg
makes a back edge to the function's entry. `d` is the number of join
parameters bound above, so the parameter `x` is variable `d`. -/
def loopExp (self arity : Nat) : Nat → Nat → Anf.Exp
  | 0, d => .bind Anf.freshLet (.call self [.var d]) (.ret (.var 0))
  | k + 1, d =>
    let arms : List Anf.Alt := if arity == 0 then
        [.mk (.src 0) 0 (.jump 0 []), .mk (.src 1) 0 (.jump 0 [])]
      else [.mk (.src 0) 0 (.jump 0 [.lit (.nat 1)]), .mk (.src 1) 0 (.jump 0 [.lit (.nat 2)])]
    .join arity false (loopExp self arity k (d + arity)) (.case (.var d) arms none)

/-- `k` globals of one parameter, each `n` levels of `kind`: `loop` (a
self-recursive loop of `n` branches whose arms pass a value to their join
point, `loopExp`), `loop0` (the same with empty arms), or one of
`Deep.chainProgram`'s kinds. -/
def anfProgram (kind : String) (n k : Nat) : Anf.Program :=
  if kind == "loop" || kind == "loop0" then
    let arity := if kind == "loop" then 1 else 0
    let g := fun i => ({ key := .dispatch i, ps := [{}], body := loopExp i arity n 0 } : Anf.GDef)
    { globals := Src.NatMap.ofList ((List.range k).map fun i => (i, g i)), size := k, roots := [k - 1],
      ctors := Deep.anfCtors, known := {} }
  else Deep.chainProgram kind n k

/-- `tests-recheck --perf-anf KIND N K`: `anfProgram KIND N K` through the
producer's back end (Fir to the block order) and the checker's from Cfg on,
each stage timed. The middle end's budgets are reported, not enforced, so a
shape past them shows what the producer would spend on it. -/
def anfStages (kind : String) (n k : Nat) : IO UInt32 := do
  let rows : Rows ← IO.mkRef #[]
  let P := anfProgram kind n k
  let cfg : Recheck.Config := {}
  let budget := match Anf.Pipeline.checkGlobalNodes P with
    | .ok _ => "within the middle end's budgets"
    | .error m => m
  let result ← (do
    let fir ← stage rows "fir.lower" fun _ => (Fir.lower P).mapError Recheck.Err.ofFir
    let C ← stage rows "cfg.lower" fun _ => .ok (Cfg.lower (Own.immortal fir))
    let lowered ← stage rows "rt.lower" fun _ => (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
    let (alloc, frames, order) ← back rows cfg.env lowered.program lowered.reps
    let size ← checkBack rows cfg C default { alloc, frames, order }
    pure s!"object {size} bytes" : IO String).toBaseIO
  report rows s!"anf {kind} {n} x{k} ({budget})" result

end IxCCTests.Recheck.Perf
