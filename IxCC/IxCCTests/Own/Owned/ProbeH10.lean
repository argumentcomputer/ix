import IxCC.Own.Plain.Certificate
import IxCC.Own.Plain.Owned
import IxCC.Own.Plain.ScopeSet
import IxCC.Recheck.Rc.Produce
import IxCC.Cfg.Rc.Public
import IxCC.Cfg.Rc.Scoped

/-! # The parameter total: cost at the limit (probe, H10)

Probe only (target `probe-own-h10`; removed before the landing). Times the scope check
(`programDomain`), a prototype of the parameter total (function parameters plus join parameters,
both of which cost no Anf node) and the verifier's steps from Fir on synthetic programs: H9's
`trap` family (function parameters), `joinChain` (join parameters) and `joinList` (many joins in
scope at many jumps: the scope check's join list is still a list). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.ProbeH10

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

structure Synth where
  F : Fir.Program
  map : Option (Src.NatMap Code)

/-- `trap P G` (H9): `G` copies of `f(p₀…p_{P-1}) := trap`; the map has no action. -/
def trapFam (P G : Nat) : Synth :=
  { F := prog (List.replicate G (fun1 (List.range P) .trap P)),
    map := some (Src.NatMap.ofList ((List.range G).map (·, .trap))) }

/-- `joinChain P J G`: `G` copies of `f() := jp 0 (P params) := trap in … jp (J-1) … in trap`: `J`
nested joins of `P` fresh parameters each, never jumped to; the map has no action. -/
def joinChain (P J G : Nat) : Synth :=
  let body := (List.range J).foldr
    (fun i k => Fir.Code.jp i ((List.range P).map (i * P + ·)) false .trap k) .trap
  { F := prog (List.replicate G (fun1 [] body (P * J))),
    map := some (Src.NatMap.ofList ((List.range G).map (·, toOwn (fun _ => []) body))) }

/-- `joinList D K G`: `G` copies of `f(x) := jp 0 [] := trap in … jp (D-1) … in` a `case` tree on
`x` with `K` leaves, each `jmp 0 []` (the oldest join: each lookup walks the whole list). The
canonical map. -/
def joinList (D K G : Nat) : Synth :=
  let body := (List.range D).foldr (fun i k => Fir.Code.jp i [] false .trap k)
    (tree 0 (fun _ => .jmp 0 []) 64 0 K)
  { F := prog (List.replicate G (fun1 [0] body 1)), map := none }

def family (name : String) (P K G : Nat) : Option Synth :=
  match name with
  | "trap" => some (trapFam P G)
  | "joinChain" => some (joinChain P K G)
  | "joinList" => some (joinList P K G)
  | _ => none

/-! ## The parameter total (prototype) -/

mutual
def joinParamsCode (acc : Nat) : Fir.Code → Nat
  | .bind _ _ k => joinParamsCode acc k
  | .jp _ ps _ b k => joinParamsCode (joinParamsCode (acc + ps.length) b) k
  | .case _ alts d => joinParamsOpt (joinParamsAlts acc alts) d
  | .jmp .. | .ret _ | .tcall .. | .trap => acc
def joinParamsAlts (acc : Nat) : List Fir.Alt → Nat
  | [] => acc
  | .mk _ b :: rest => joinParamsAlts (joinParamsCode acc b) rest
def joinParamsOpt (acc : Nat) : Option Fir.Code → Nat
  | none => acc
  | some c => joinParamsCode acc c
end

/-- Function parameters plus join parameters, over the numbered functions. -/
def paramTotal (F : Fir.Program) : Nat :=
  (List.range F.size).foldl (fun acc f =>
    match F.fun? f with
    | none => acc
    | some fd => joinParamsCode (acc + fd.params.length) fd.body) 0

/-! ## Timing -/

def timeMs {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1e6)

def fmt (x : Float) : String := toString (Float.round (x * 10) / 10)

def mapOf (s : Synth) : Src.NatMap Code := s.map.getD (Program.canonical s.F).bodies

/-- The verifier's steps from Fir (`RcReplay.runFront` after `Fir.lower`, without the root
parameter check), as H9's probe: admission from text, `generate`, `checkScopedProgram`,
`Public.lower`. -/
def front (F : Fir.Program) (text : String) : IO Unit := do
  let (r1, t1) ← timeMs fun _ => Certificate.ofText F text
  match r1 with
  | .error e =>
    IO.println s!"verify: admit refused ({fmt t1} ms): {e.take 200}"
    IO.println s!"verify total {fmt t1} ms"
  | .ok own =>
    IO.println s!"verify: admit ok {fmt t1} ms"
    let (r2, t2) ← timeMs fun _ => Cfg.Rc.generate F own.bodies
    match r2 with
    | none =>
      IO.println s!"verify: generate declined ({fmt t2} ms)"
      IO.println s!"verify total {fmt (t1 + t2)} ms"
    | some cand =>
      IO.println s!"verify: generate ok {fmt t2} ms"
      let (r3, t3) ← timeMs fun _ => Cfg.Rc.checkScopedProgram F own.bodies cand
      IO.println s!"verify: checkScopedProgram {r3} {fmt t3} ms"
      if !r3 then
        IO.println s!"verify total {fmt (t1 + t2 + t3)} ms"
      else
        let (r4, t4) ← timeMs fun _ => (Cfg.Rc.Public.lower {} F own.bodies cand).map (fun _ => ())
        match r4 with
        | .ok _ => IO.println s!"verify: lower ok {fmt t4} ms"
        | .error e => IO.println s!"verify: lower refused {fmt t4} ms: {e.take 200}"
        IO.println s!"verify total {fmt (t1 + t2 + t3 + t4)} ms"

def hostile (name : String) (P K G : Nat) (mode : String) : IO UInt32 := do
  let some s := family name P K G
    | do IO.eprintln s!"unknown family {name}"; return 2
  let F := s.F
  let (total, tt) ← timeMs fun _ => paramTotal F
  IO.println s!"{name} P={P} K={K} G={G}: functions {F.size}, parameter total {total} ({fmt tt} ms)"
  match mode with
  | "domain" =>
    let (r, t) ← timeMs fun _ => programDomain F
    IO.println s!"programDomain {r} {fmt t} ms"
  | "cdomain" =>
    let (r, t) ← timeMs fun _ => contractProgramDomain F
    IO.println s!"contractProgramDomain {r} {fmt t} ms"
  | "owned" =>
    let m := mapOf s
    let (r, t) ← timeMs fun _ => checkOwned F m
    IO.println s!"checkOwned {r} {fmt t} ms"
  | "info" =>
    let m := mapOf s
    let text := Certificate.toText m
    IO.println s!"certificate {text.utf8ByteSize} bytes; captured work {Certificate.capturedWork m}; checkJsonText {match Src.Hints.checkJsonText text with | .ok _ => "ok" | .error e => e}"
  | "verify" =>
    let m := mapOf s
    let (text, tp) ← timeMs fun _ => Certificate.toText m
    IO.println s!"certificate {text.utf8ByteSize} bytes (map and text {fmt tp} ms, not counted)"
    front F text
  | _ =>
    IO.eprintln s!"unknown mode {mode}"
    return 2
  return 0

end IxCCTests.Own.Owned.ProbeH10

def main (args : List String) : IO UInt32 :=
  match args with
  | ["hostile", name, P, K, G, mode] =>
    IxCCTests.Own.Owned.ProbeH10.hostile name P.toNat! K.toNat! G.toNat! mode
  | _ => do
    IO.eprintln "usage: probe-own-h10 hostile trap|joinChain|joinList P K G domain|cdomain|owned|info|verify"
    return 2
