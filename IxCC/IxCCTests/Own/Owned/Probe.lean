import IxCCTests.Own.Owned.Live
import IxCC.Own.Plain.Certificate
import IxCC.Recheck.Rc.Produce
import IxCC.Src.Hints

/-! # Heap stage 2, milestone 2: the checker's cost under the verifier's limits (probe, H6)

Probe only (target `probe-own-h6`; removed before the landing). Synthetic Fir programs and maps
built to the limits the verifier enforces before the ownership check runs (`Anf.maxGlobalNodes`,
`Anf.maxBackWork`, `Anf.maxProgramNodes`, the JSON text's depth and size), timed under
`checkOwned` and `checkPlainMap`; and a survey of the registered roots (the captured tokens their
maps take at jumps, their certificates' depth). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.Probe

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var Arg)

def fun1 (params : List Var) (body : Fir.Code) (vars : Nat) : Fir.Fun :=
  { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }

def prog (fs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (f, i) => (i, f)), size := fs.length,
    exports := [0], ctors := [], known := {} }

/-- A binary tree of `case x` with `k` leaves, leaves numbered from `base`. -/
def tree (x : Var) (leaf : Nat → Fir.Code) : Nat → Nat → Nat → Fir.Code
  | 0, base, _ => leaf base
  | fuel + 1, base, k =>
    if k ≤ 1 then leaf base
    else
      let h := k / 2
      .case x [.mk default (tree x leaf fuel base h), .mk default (tree x leaf fuel (base + h) (k - h))] none

/-- The Own code with no action and the given captured list per join. -/
mutual
def toOwn (cap : Nat → List Var) : Fir.Code → Code
  | .bind x r k => .bind x r (toOwn cap k)
  | .jp j ps rec b k => .jp j ps (cap j) rec (toOwn cap b) (toOwn cap k)
  | .jmp j as => .jmp j as
  | .case x alts d => .case x (toOwnAlts cap alts) (toOwnOpt cap d)
  | .ret a => .ret a
  | .tcall f as => .tcall f as
  | .trap => .trap
def toOwnAlts (cap : Nat → List Var) : List Fir.Alt → List Alt
  | [] => []
  | .mk key b :: rest => .mk key (toOwn cap b) :: toOwnAlts cap rest
def toOwnOpt (cap : Nat → List Var) : Option Fir.Code → Option Code
  | none => none
  | some c => some (toOwn cap c)
end

def scope (P : Nat) : List Var := List.range (P + 1)

/-- `fanParams P K`: `f(x, p₁…p_P)`, one join capturing all `P + 1` parameters, jumped to from the
`K` leaves of a `case` tree on `x`; its body is `trap`. Anf nodes `2K + 1`. -/
def fanParams (P K : Nat) : Fir.Fun × Code :=
  let body : Fir.Code := .jp 0 [] false .trap (tree 0 (fun _ => .jmp 0 []) 64 0 K)
  (fun1 (scope P) body (P + 1), toOwn (fun _ => scope P) body)

/-- `fanJoin P K`: `f(x)`, an outer join with `P` parameters (jumped to once, with literals), whose
body declares a join capturing `x` and them, jumped to from `K` leaves. Anf nodes `P + 2K + 4`. -/
def fanJoin (P K : Nat) : Fir.Fun × Code :=
  let ps := (List.range P).map (· + 1)
  let body : Fir.Code :=
    .jp 1 ps false (.jp 0 [] false .trap (tree 0 (fun _ => .jmp 0 []) 64 0 K))
      (.jmp 1 (List.replicate P (.lit (.nat 0))))
  (fun1 [0] body (P + 1), toOwn (fun j => if j == 1 then [0] else scope P) body)

/-- `leafJoins P K`: `f(x, p₁…p_P)`, a `case` tree with `K` leaves, each declaring a join that
captures all `P + 1` parameters (body and scope `trap`). Anf nodes `4K - 1`. -/
def leafJoins (P K : Nat) : Fir.Fun × Code :=
  let body : Fir.Code := tree 0 (fun i => .jp i [] false .trap .trap) 64 0 K
  (fun1 (scope P) body (P + 1), toOwn (fun _ => scope P) body)

partial def padLeaves (pad : List Action) : Code → Code
  | .case x alts d => .case x (alts.map fun | .mk k b => .mk k (padLeaves pad b)) d
  | c => actionPrefix pad c

/-- `acts M K`: `f(x)`, a `case` tree with `K` leaves, each `M` pairs `inc x; dec x` then `ret x`. -/
def acts (M K : Nat) : Fir.Fun × Code :=
  let body : Fir.Code := tree 0 (fun _ => .ret (.var 0)) 64 0 K
  let pad : List Action := (List.range M).flatMap fun _ => [.inc 0 1, .dec 0]
  (fun1 [0] body 1, padLeaves pad (toOwn (fun _ => []) body))

/-- `deepCase D`: `D` nested `case x` (one alternative each) around `ret x`. -/
def deepCase (D : Nat) : Fir.Fun × Code :=
  let body := (List.range D).foldl (fun c _ => Fir.Code.case 0 [.mk default c] none) (.ret (.var 0))
  (fun1 [0] body 1, toOwn (fun _ => []) body)

/-- `deepJoin D`: `D` nested join bodies (join `i`'s body declares join `i+1`), innermost `ret x`,
each scope `trap`; every join captures `x`. -/
def deepJoin (D : Nat) : Fir.Fun × Code :=
  let body := (List.range D).foldl (fun c i => Fir.Code.jp (D - i) [] false c .trap) (.ret (.var 0))
  (fun1 [0] body 1, toOwn (fun _ => [0]) body)

def family (name : String) (P K : Nat) : Option (Fir.Fun × Code) :=
  match name with
  | "fanParams" => some (fanParams P K)
  | "fanJoin" => some (fanJoin P K)
  | "leafJoins" => some (leafJoins P K)
  | "acts" => some (acts P K)
  | "deepCase" => some (deepCase P)
  | "deepJoin" => some (deepJoin P)
  | _ => none

/-- `G` copies of one function (ids `0…G-1`). -/
def program (fd : Fir.Fun) (body : Code) (G : Nat) : Fir.Program × Src.NatMap Code :=
  (prog (List.replicate G fd), Src.NatMap.ofList ((List.range G).map (·, body)))

/-! ## Static counts over a map -/

structure Counts where
  jumps : Nat := 0
  jumpCaptured : Nat := 0
  joins : Nat := 0
  joinCaptured : Nat := 0
  maxCaptured : Nat := 0
  actions : Nat := 0
  nodes : Nat := 0
  depth : Nat := 0
  deriving Inhabited

def Counts.add (a b : Counts) : Counts :=
  { jumps := a.jumps + b.jumps, jumpCaptured := a.jumpCaptured + b.jumpCaptured,
    joins := a.joins + b.joins, joinCaptured := a.joinCaptured + b.joinCaptured,
    maxCaptured := max a.maxCaptured b.maxCaptured, actions := a.actions + b.actions,
    nodes := a.nodes + b.nodes, depth := max a.depth b.depth }

/-- Counts of one body: captured tokens taken at jumps (`Δ` as the checker builds it), at joins,
actions, Fir nodes, nesting depth of the code tree (each `act`, `bind`, join body/scope and case
alternative one level). -/
partial def count (Δ : Src.NatMap Nat) (d : Nat) : Code → Counts
  | .act _ k => ({ actions := 1 } : Counts).add (count Δ (d + 1) k)
  | .bind _ _ k => ({ nodes := 1 } : Counts).add (count Δ (d + 1) k)
  | .jp j _ cap rec b k =>
    let here : Counts := { joins := 1, joinCaptured := cap.length, maxCaptured := cap.length, nodes := 1 }
    let Δb := if rec then Δ.insert j cap.length else Δ
    (here.add (count Δb (d + 1) b)).add (count (Δ.insert j cap.length) (d + 1) k)
  | .jmp j _ => { jumps := 1, jumpCaptured := Δ.getD j 0, nodes := 1, depth := d }
  | .case _ alts dflt =>
    let a := alts.foldl (fun acc (.mk _ b) => acc.add (count Δ (d + 2) b)) ({ nodes := 1, depth := d } : Counts)
    match dflt with
    | none => a
    | some c => a.add (count Δ (d + 2) c)
  | _ => { nodes := 1, depth := d }

def countMap (m : Src.NatMap Code) : Counts :=
  m.toList.foldl (fun acc (_, b) => acc.add (count .leaf 0 b)) {}

partial def jsonDepth : Lean.Json → Nat
  | .arr a => 1 + a.foldl (fun acc j => max acc (jsonDepth j)) 0
  | .obj _ => 1
  | _ => 0

/-! ## Timing -/

def timeMs {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1e6)

def fmt (x : Float) : String :=
  let s := toString (Float.round (x * 10) / 10)
  s

def front (closure eqs : System.FilePath) (root : String) : IO (Fir.Program × Src.NatMap Code) := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
  return (fr.fir, (Program.canonicalForSrc fr.src fr.fir).bodies)

/-- The new admission, as `Certificate.admit` will run it: the text checks, the parse, the decode,
then `checkOwned`. -/
def admitNew (F : Fir.Program) (text : String) : Except String Bool := do
  Src.Hints.checkJsonText text
  let j ← Lean.Json.parse text
  let bodies ← Certificate.decode F j
  return checkOwned F bodies

def admitOld (F : Fir.Program) (text : String) : Except String Bool := do
  Src.Hints.checkJsonText text
  let j ← Lean.Json.parse text
  let bodies ← Certificate.decode F j
  return checkPlainMap F bodies

def verdict (r : Except String Bool) : String :=
  match r with
  | .ok b => toString b
  | .error e => s!"error: {e}"

def hostile (name : String) (P K G : Nat) (mode : String) : IO UInt32 := do
  let some (fd, body) := family name P K
    | do IO.eprintln s!"unknown family {name}"; return 2
  let (F, m) := program fd body G
  let c := countMap m
  IO.println s!"{name} P={P} K={K} G={G}: fir nodes {c.nodes} (per function {c.nodes / max G 1}), jumps {c.jumps}, captured tokens at jumps {c.jumpCaptured}, joins {c.joins}, captured at joins {c.joinCaptured}, max captured {c.maxCaptured}, actions {c.actions}, code depth {c.depth}"
  match mode with
  | "info" =>
    let text := Certificate.toText m
    IO.println s!"certificate {text.utf8ByteSize} bytes, JSON depth {jsonDepth (Certificate.encode m)} (+1 in the rc-cert envelope); checkJsonText: {verdict ((Src.Hints.checkJsonText text).map fun _ => true)}"
  | "owned" =>
    let (r, t) ← timeMs fun _ => checkOwned F m
    IO.println s!"checkOwned {r} {fmt t} ms"
  | "parts" =>
    let (r1, t1) ← timeMs fun _ => programDomain F
    let (r2, t2) ← timeMs fun _ => (checkMapE F m).isOk
    IO.println s!"programDomain {r1} {fmt t1} ms; checkMapE {r2} {fmt t2} ms"
  | "plain" =>
    let (r, t) ← timeMs fun _ => checkPlainMap F m
    IO.println s!"checkPlainMap {r} {fmt t} ms"
  | "canonical" =>
    let (r, t) ← timeMs fun _ => (Program.canonical F).bodies.toList.length
    IO.println s!"canonical map built ({r} entries) {fmt t} ms"
  | "text" =>
    let text := Certificate.toText m
    IO.println s!"certificate {text.utf8ByteSize} bytes"
    let (r, t) ← timeMs fun _ => admitNew F text
    IO.println s!"admit (new: checkOwned) {verdict r} {fmt t} ms"
  | "textold" =>
    let text := Certificate.toText m
    IO.println s!"certificate {text.utf8ByteSize} bytes"
    let (r, t) ← timeMs fun _ => admitOld F text
    IO.println s!"admit (old: checkPlainMap) {verdict r} {fmt t} ms"
  | _ =>
    IO.eprintln s!"unknown mode {mode}"
    return 2
  return 0

/-- One line per root: counts of the canonical and liveness maps, the certificate depth, and the two
checkers' times. -/
def survey (tsv : System.FilePath) : IO UInt32 := do
  let lines := (← IO.FS.readFile tsv).splitOn "\n" |>.filter (· ≠ "")
  let mut best : List (String × Nat × String) := []
  IO.println "label\tmap\tjumps\tcapturedAtJumps\tjoins\tcapturedAtJoins\tmaxCaptured\tactions\tcodeDepth\tjsonDepth\tbytes\tcheckOwned\tms\tcheckPlainMap\tms"
  for line in lines do
    match line.splitOn "\t" with
    | [clo, eqs, root, label] =>
      try
        let (F, canonical) ← front clo eqs root
        let live := liveMap F
        for (mname, m) in [("canonical", canonical), ("liveness", live)] do
          let c := countMap m
          let j := Certificate.encode m
          let bytes := j.compress.utf8ByteSize
          let jd := jsonDepth j
          let (ro, to) ← timeMs fun _ => checkOwned F m
          let (rp, tp) ← timeMs fun _ => checkPlainMap F m
          IO.println s!"{label}\t{mname}\t{c.jumps}\t{c.jumpCaptured}\t{c.joins}\t{c.joinCaptured}\t{c.maxCaptured}\t{c.actions}\t{c.depth}\t{jd}\t{bytes}\t{ro}\t{fmt to}\t{rp}\t{fmt tp}"
          if ro then
            best := (s!"{mname} capturedAtJumps", c.jumpCaptured, label) :: (s!"{mname} capturedAtJoins", c.joinCaptured, label) ::
              (s!"{mname} capturedTotal", c.jumpCaptured + c.joinCaptured, label) :: (s!"{mname} jsonDepth", jd, label) ::
              (s!"{mname} maxCaptured", c.maxCaptured, label) :: (s!"{mname} jumps", c.jumps, label) :: best
      catch e =>
        IO.println s!"{label}\tfront-end error: {e}"
    | _ => pure ()
  let keys := best.map (·.1) |>.eraseDups
  for k in keys do
    let rows := best.filter (·.1 == k)
    let top := rows.foldl (fun acc r => if r.2.1 > acc.2.1 then r else acc) (k, 0, "-")
    IO.println s!"MAX {k} {top.2.1} at {top.2.2}"
  return 0

end IxCCTests.Own.Owned.Probe

def main (args : List String) : IO UInt32 :=
  match args with
  | ["survey", tsv] => IxCCTests.Own.Owned.Probe.survey tsv
  | ["hostile", name, P, K, G, mode] =>
    IxCCTests.Own.Owned.Probe.hostile name P.toNat! K.toNat! G.toNat! mode
  | _ => do
    IO.eprintln "usage: probe-own-h6 survey TSV | hostile FAMILY P K G info|owned|parts|plain|canonical|text|textold"
    return 2
