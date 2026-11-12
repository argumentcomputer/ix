import IxCC.Own.Plain.Certificate
import IxCC.Own.Plain.Owned
import IxCC.Own.Plain.ScopeSet
import IxCC.Recheck.Rc.Produce
import IxCC.Cfg.Rc.Public
import IxCC.Cfg.Rc.Scoped

/-! # `programDomain` over sets: cost and agreement (probe, H9)

Probe only (target `probe-own-h9`; removed before the landing). Times `programDomain` and the
verifier's steps from Fir on synthetic programs built to the middle end's limits (functions of up
to 2,049 parameters, which cost no Anf node), and compares the list form of the scope check
(`fresh`/`scopeOk` over `signatures`, the definition at `52205307d`) with the set form
(`freshSet`/`scopeOkSet` over `signatureArity`) on the registered roots, on deliberately ill-scoped
mutants of them, and on the synthetic programs. -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.ProbeH9

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var Arg)

/-! ## The two forms -/

/-- The list form: `programDomain`'s definition at `52205307d`. -/
def listDomainWith (dom : Fir.Fun → Bool) (P : Fir.Program) : Bool :=
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd => dom fd && fresh [] (fd.params.map (·.1)) &&
        scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

/-- The set form. -/
def setDomainWith (dom : Fir.Fun → Bool) (P : Fir.Program) : Bool :=
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd => dom fd && freshSet .leaf (fd.params.map (·.1)) &&
        scopeOkSet P (insertVars .leaf (fd.params.map (·.1))) [] fd.body

def listDomain := listDomainWith funDomain
def setDomain := setDomainWith funDomain
def listContract := listDomainWith contractFunDomain
def setContract := setDomainWith contractFunDomain

def listFun (P : Fir.Program) (fd : Fir.Fun) : Bool :=
  fresh [] (fd.params.map (·.1)) && scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

def setFun (P : Fir.Program) (fd : Fir.Fun) : Bool :=
  freshSet .leaf (fd.params.map (·.1)) && scopeOkSet P (insertVars .leaf (fd.params.map (·.1))) [] fd.body

/-! ## Synthetic programs -/

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

def scope (P : Nat) : List Var := List.range (P + 1)

/-- A synthetic program and, when not the canonical one, its certificate map. -/
structure Synth where
  F : Fir.Program
  map : Option (Src.NatMap Code)

/-- `fanParams P K G` (H6): `G` copies of `f(x, p₁…p_P)`, one join capturing all `P + 1`
parameters, jumped to from the `K` leaves of a `case` tree on `x`; the map captures them all. -/
def fanParams (P K G : Nat) : Synth :=
  let body : Fir.Code := .jp 0 [] false .trap (tree 0 (fun _ => .jmp 0 []) 64 0 K)
  let fd := fun1 (scope P) body (P + 1)
  let own := toOwn (fun _ => scope P) body
  { F := prog (List.replicate G fd), map := some (Src.NatMap.ofList ((List.range G).map (·, own))) }

/-- `trap P G`: `G` copies of `f(p₀…p_P) := trap` (one Anf node each). The map has no action (a
trap may leak, so the checker accepts it); the canonical map drops every parameter first, a chain
of `P + 1` actions that the certificate's JSON depth limit (512) refuses past about 500. -/
def trapFam (P G : Nat) : Synth :=
  { F := prog (List.replicate G (fun1 (scope P) .trap (P + 1))),
    map := some (Src.NatMap.ofList ((List.range G).map (·, .trap))) }

/-- `retLast P K G`: `G` copies of `f(p₀…p_P)`: a `case` tree on `p_P` with `K` leaves, each
`ret p_P` (every node reads the last parameter); the canonical map drops the other parameters at
each leaf. -/
def retLast (P K G : Nat) : Synth :=
  let body := tree P (fun _ => .ret (.var P)) 64 0 K
  { F := prog (List.replicate G (fun1 (scope P) body (P + 1))), map := none }

/-- `callLast P K G`: functions `0 … G-2` are `f(p₀…p_P)`: `K` bindings `y := call (G-1) []`, then
`trap`; function `G-1` is `g() := ret 0` (every call looks the last function's arity up). The map
has no action (the trap leaks). -/
def callLast (P K G : Nat) : Synth :=
  let g := G - 1
  let body := (List.range K).foldr (fun i k => Fir.Code.bind (P + 1 + i) (.call g []) k) .trap
  let fd := fun1 (scope P) body (P + 1 + K)
  let last := fun1 [] (.ret (.lit (.nat 0))) 0
  { F := prog (List.replicate g fd ++ [last]),
    map := some (Src.NatMap.ofList ((List.range G).map fun f =>
      (f, if f == g then Code.ret (.lit (.nat 0)) else toOwn (fun _ => []) body))) }

def family (name : String) (P K G : Nat) : Option Synth :=
  match name with
  | "fanParams" => some (fanParams P K G)
  | "trap" => some (trapFam P G)
  | "retLast" => some (retLast P K G)
  | "callLast" => some (callLast P K G)
  | _ => none

/-! ## Timing -/

def timeMs {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1e6)

def fmt (x : Float) : String := toString (Float.round (x * 10) / 10)

def paramsTotal (F : Fir.Program) : Nat :=
  (List.range F.size).foldl (fun acc f => acc + ((F.fun? f).map (·.params.length)).getD 0) 0

def mapOf (s : Synth) : Src.NatMap Code := s.map.getD (Program.canonical s.F).bodies

/-- The verifier's steps from Fir (`RcReplay.runFront` after `Fir.lower`, without the root
parameter check): the certificate admitted from text (text checks, parse, decode, budget,
`checkOwned`), `Cfg.Rc.generate`, `Cfg.Rc.checkScopedProgram`, `Cfg.Rc.Public.lower`. -/
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
  IO.println s!"{name} P={P} K={K} G={G}: functions {F.size}, parameters {paramsTotal F}"
  match mode with
  | "domain" =>
    let (r, t) ← timeMs fun _ => programDomain F
    IO.println s!"programDomain {r} {fmt t} ms"
  | "cdomain" =>
    let (r, t) ← timeMs fun _ => contractProgramDomain F
    IO.println s!"contractProgramDomain {r} {fmt t} ms"
  | "list" =>
    let (r, t) ← timeMs fun _ => listDomain F
    IO.println s!"list form {r} {fmt t} ms"
  | "set" =>
    let (r, t) ← timeMs fun _ => setDomain F
    IO.println s!"set form {r} {fmt t} ms"
  | "agree" =>
    let (a, ta) ← timeMs fun _ => listDomain F
    let (b, tb) ← timeMs fun _ => setDomain F
    let (c, tc) ← timeMs fun _ => listContract F
    let (d, td) ← timeMs fun _ => setContract F
    IO.println s!"agree domain list {a} {fmt ta} ms set {b} {fmt tb} ms; contract list {c} {fmt tc} ms set {d} {fmt td} ms; {if a == b && c == d then "SAME" else "DIFFER"}"
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

/-! ## Agreement on the registered roots and their ill-scoped mutants -/

mutual
/-- Apply `edit` at the first node (preorder) it accepts. -/
partial def editFirst (edit : Fir.Code → Option Fir.Code) (c : Fir.Code) : Option Fir.Code :=
  match edit c with
  | some c' => some c'
  | none =>
    match c with
    | .bind x r k => (editFirst edit k).map (.bind x r ·)
    | .jp j ps rec b k =>
      match editFirst edit b with
      | some b' => some (.jp j ps rec b' k)
      | none => (editFirst edit k).map (.jp j ps rec b ·)
    | .case x alts d =>
      match editAlts edit alts with
      | some alts' => some (.case x alts' d)
      | none =>
        match d with
        | some dc => (editFirst edit dc).map fun dc' => .case x alts (some dc')
        | none => none
    | _ => none
partial def editAlts (edit : Fir.Code → Option Fir.Code) : List Fir.Alt → Option (List Fir.Alt)
  | [] => none
  | .mk key b :: rest =>
    match editFirst edit b with
    | some b' => some (.mk key b' :: rest)
    | none => (editAlts edit rest).map (.mk key b :: ·)
end

def zeros (n : Nat) : List Arg := List.replicate n (.lit (.nat 0))

/-- The ill-scoped (and two well-scoped) edits of one function, by name. `v` is a variable no
binder of the function uses. -/
def edits (F : Fir.Program) (fd : Fir.Fun) : List (String × Option Fir.Fun) :=
  let v := fd.vars + 1
  let ps := fd.params.map (·.1)
  let body (e : Fir.Code → Option Fir.Code) : Option Fir.Fun :=
    (editFirst e fd.body).map fun b => { fd with body := b }
  let g? := (List.range F.size).find? fun g => ((F.fun? g).map (·.arity)).isSome
  let gArity := (g?.bind fun g => (F.fun? g).map (·.arity)).getD 0
  [ ("useBeforeBind", body fun | .bind x r k => some (.bind v (.arg (.var x)) (.bind x r k)) | _ => none),
    ("rebind", body fun | .bind x r k => some (.bind x r (.bind x (.arg (.var x)) k)) | _ => none),
    ("bindParam", (ps.head?).map fun p => { fd with body := .bind p (.arg (.lit (.nat 0))) fd.body }),
    ("dupParam", (ps.head?).map fun p => { fd with params := fd.params ++ [(p, .tobj)] }),
    ("unboundRet", some { fd with body := .ret (.var v) }),
    ("unboundCase", body fun | .case _ alts d => some (.case v alts d) | _ => none),
    ("unboundProj", body fun | .bind x (.proj _ c i) k => some (.bind x (.proj v c i) k) | _ => none),
    ("unboundArg", body fun
      | .bind x (.call f (_ :: as)) k => some (.bind x (.call f (.var v :: as)) k)
      | .bind x (.ctor c (_ :: as)) k => some (.bind x (.ctor c (.var v :: as)) k)
      | .bind x (.prim p (_ :: as)) k => some (.bind x (.prim p (.var v :: as)) k)
      | .tcall f (_ :: as) => some (.tcall f (.var v :: as))
      | .jmp j (_ :: as) => some (.jmp j (.var v :: as))
      | _ => none),
    ("callArityPlus", body fun
      | .bind x (.call f as) k => some (.bind x (.call f (as ++ zeros 1)) k)
      | .tcall f as => some (.tcall f (as ++ zeros 1))
      | _ => none),
    ("callArityMinus", body fun
      | .bind x (.call f (_ :: as)) k => some (.bind x (.call f as) k)
      | .tcall f (_ :: as) => some (.tcall f as)
      | _ => none),
    ("callUnknown", some { fd with body := .bind v (.call (F.size + 3) []) fd.body }),
    ("callGood", g?.map fun g => { fd with body := .bind v (.call g (zeros gArity)) fd.body, vars := v + 1 }),
    ("callWrongArity", g?.map fun g => { fd with body := .bind v (.call g (zeros (gArity + 1))) fd.body }),
    ("jumpArity", body fun | .jmp j as => some (.jmp j (as ++ zeros 1)) | _ => none),
    ("jumpUnknown", body fun | .jmp j as => some (.jmp (j + 100000) as) | _ => none),
    ("dupJoin", body fun | .jp j ps' rec b k => some (.jp j ps' rec b (.jp j [] false .trap k)) | _ => none),
    ("joinParamLive", body fun
      | .jp j ps' rec b k => (ps.head?).map fun p => .jp j (ps' ++ [p]) rec b k
      | _ => none),
    ("joinParamDup", body fun
      | .jp j (q :: ps') rec b k => some (.jp j (q :: q :: ps') rec b k)
      | _ => none),
    ("selfJumpNonRec", body fun | .jp j ps' _ _ k => some (.jp j ps' false (.jmp j (zeros ps'.length)) k) | _ => none),
    ("selfJumpRec", body fun | .jp j ps' _ _ k => some (.jp j ps' true (.jmp j (zeros ps'.length)) k) | _ => none) ]

/-- Per program: a function `f`'s edit, the program with it in place of `f`. -/
def withFun (F : Fir.Program) (f : Nat) (fd : Fir.Fun) : Fir.Program :=
  { F with funs := F.funs.insert f fd }

structure Tally where
  programs : Nat := 0
  functions : Nat := 0
  mutants : Nat := 0
  accepted : Nat := 0
  refused : Nat := 0
  differ : Nat := 0
  byKind : List (String × Nat × Nat × Nat) := []  -- kind, mutants, accepted, refused

def Tally.kind (t : Tally) (k : String) (acc : Bool) : Tally :=
  let rec go : List (String × Nat × Nat × Nat) → List (String × Nat × Nat × Nat)
    | [] => [(k, 1, if acc then 1 else 0, if acc then 0 else 1)]
    | (k', n, a, r) :: rest =>
      if k' == k then (k', n + 1, a + (if acc then 1 else 0), r + (if acc then 0 else 1)) :: rest
      else (k', n, a, r) :: go rest
  { t with byKind := go t.byKind }

/-- Compare the two forms on `F` (whole program, both domains, and function by function) and on
every edit of every function; `MUTANTS` bounds the functions mutated per program. -/
def compareProgram (label : String) (F : Fir.Program) (maxMut : Nat) (t0 : Tally) : IO Tally := do
  let mut t := { t0 with programs := t0.programs + 1 }
  let ld := listDomain F; let sd := setDomain F; let lc := listContract F; let sc := setContract F
  let cur := programDomain F; let curc := contractProgramDomain F
  if ld != sd || lc != sc || cur != ld || curc != lc then
    t := { t with differ := t.differ + 1 }
    IO.println s!"DIFFER {label}: domain list {ld} set {sd} current {cur}; contract list {lc} set {sc} current {curc}"
  let mut nmut := 0
  for f in List.range F.size do
    match F.fun? f with
    | none => pure ()
    | some fd =>
      t := { t with functions := t.functions + 1 }
      if listFun F fd != setFun F fd then
        t := { t with differ := t.differ + 1 }
        IO.println s!"DIFFER {label} f{f}: function list {listFun F fd} set {setFun F fd}"
      if nmut < maxMut then
        nmut := nmut + 1
        for (kind, m?) in edits F fd do
          match m? with
          | none => pure ()
          | some fd' =>
            let F' := withFun F f fd'
            let a := listFun F' fd'; let b := setFun F' fd'
            let pa := listContract F'; let pb := setContract F'
            let pd := listDomain F'; let pe := setDomain F'
            t := { t with mutants := t.mutants + 1 }
            t := t.kind kind a
            if a then t := { t with accepted := t.accepted + 1 } else t := { t with refused := t.refused + 1 }
            if a != b || pa != pb || pd != pe then
              t := { t with differ := t.differ + 1 }
              IO.println s!"DIFFER {label} f{f} {kind}: function list {a} set {b}; contract list {pa} set {pb}; domain list {pd} set {pe}"
  return t

def printTally (t : Tally) : IO Unit := do
  IO.println s!"TOTAL programs {t.programs}, functions {t.functions}, mutants {t.mutants} (function check: accepted {t.accepted}, refused {t.refused}), differing {t.differ}"
  for (k, n, a, r) in t.byKind.reverse do
    IO.println s!"KIND {k}: {n} mutants, accepted {a}, refused {r}"

def frontFir (closure eqs : System.FilePath) (root : String) : IO Fir.Program := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
  return fr.fir

def corpus (tsv : System.FilePath) (maxMut : Nat) : IO UInt32 := do
  let lines := (← IO.FS.readFile tsv).splitOn "\n" |>.filter (· ≠ "")
  let mut t : Tally := {}
  let mut skipped := 0
  for line in lines do
    match line.splitOn "\t" with
    | [clo, eqs, root, label] =>
      try
        let F ← frontFir clo eqs root
        IO.println s!"{label}: functions {F.size}, domain {programDomain F}, contract {contractProgramDomain F}"
        t ← compareProgram label F maxMut t
      catch e =>
        skipped := skipped + 1
        IO.println s!"{label}\tfront-end error: {e}"
    | _ => pure ()
  IO.println s!"roots skipped (front end) {skipped}"
  printTally t
  return 0

/-- Join parameters of a body: their sum and the largest list. -/
partial def joinStats : Fir.Code → Nat × Nat
  | .bind _ _ k => joinStats k
  | .jp _ ps _ b k =>
    let (s1, m1) := joinStats b
    let (s2, m2) := joinStats k
    (ps.length + s1 + s2, max ps.length (max m1 m2))
  | .case _ alts d =>
    (alts.map Fir.Alt.body ++ d.toList).foldl
      (fun (s, m) c => let (s', m') := joinStats c; (s + s', max m m')) (0, 0)
  | _ => (0, 0)

/-- One line per root: Fir functions, the sum and the largest of their parameter counts, the
same for join parameters, the program's Anf nodes (`programNodesUpTo`), and the ratio of the
function parameters to the Anf nodes. -/
def params (tsv : System.FilePath) : IO UInt32 := do
  let lines := (← IO.FS.readFile tsv).splitOn "\n" |>.filter (· ≠ "")
  IO.println "label\tfunctions\tparams\tmaxParams\tjoinParams\tmaxJoinParams\tanfNodes\tparams/anf"
  for line in lines do
    match line.splitOn "\t" with
    | [clo, eqs, root, label] =>
      try
        let bytes ← IO.FS.readBinFile clo
        let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
        let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
        let cfg := Recheck.Config.forInput {} inp
        let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
        let anf := Anf.Pipeline.programNodesUpTo fr.anf.globalList 0
        let F := fr.fir
        let fds := (List.range F.size).filterMap F.fun?
        let ps := fds.map (·.params.length)
        let js := fds.map (fun fd => joinStats fd.body)
        let sum := ps.foldl (· + ·) 0
        let r := if anf == 0 then 0.0 else sum.toFloat / anf.toFloat
        IO.println s!"{label}\t{F.size}\t{sum}\t{ps.foldl max 0}\t{js.foldl (fun a p => a + p.1) 0}\t{js.foldl (fun a p => max a p.2) 0}\t{anf}\t{r}"
      catch e =>
        IO.println s!"{label}\tfront-end error: {e}"
    | _ => pure ()
  return 0

/-- Small synthetic programs: each family at small sizes, and their edits. -/
def synthetic : IO UInt32 := do
  let mut t : Tally := {}
  for (name, P, K, G) in [("fanParams", 8, 9, 3), ("fanParams", 64, 33, 2), ("trap", 16, 0, 4),
      ("retLast", 32, 17, 3), ("callLast", 8, 5, 4), ("callLast", 0, 3, 2)] do
    match family name P K G with
    | some s => t ← compareProgram s!"{name} {P} {K} {G}" s.F 1000 t
    | none => pure ()
  -- A numbered entry past `size`: a call to it has no arity in either form.
  let s := callLast 4 2 3
  let extra : Fir.Program := { s.F with funs := s.F.funs.insert s.F.size (fun1 [] .trap 0) }
  let callPast : Fir.Fun := fun1 [0] (.bind 1 (.call s.F.size []) (.ret (.var 1))) 2
  let F' := withFun extra 0 callPast
  t ← compareProgram "entry past size" F' 1000 t
  IO.println s!"entry past size: list {listFun F' callPast} set {setFun F' callPast} (both must refuse)"
  printTally t
  return 0

end IxCCTests.Own.Owned.ProbeH9

def main (args : List String) : IO UInt32 :=
  match args with
  | ["corpus", tsv, n] => IxCCTests.Own.Owned.ProbeH9.corpus tsv n.toNat!
  | ["synthetic"] => IxCCTests.Own.Owned.ProbeH9.synthetic
  | ["params", tsv] => IxCCTests.Own.Owned.ProbeH9.params tsv
  | ["hostile", name, P, K, G, mode] =>
    IxCCTests.Own.Owned.ProbeH9.hostile name P.toNat! K.toNat! G.toNat! mode
  | _ => do
    IO.eprintln "usage: probe-own-h9 corpus TSV MAXMUT | synthetic | hostile FAMILY P K G domain|cdomain|list|set|agree|owned|info|verify"
    return 2
