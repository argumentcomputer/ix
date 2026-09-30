import Compilatrix.Anf.Pipeline

/-! Lam programs and middle-end certificates as Lean source, for kernel
probes (M1.K1, 02 Q17): `tests-anf --kernel-probe NAME` prints a module that
re-runs the Phase 1 middle end on a bench-k1 entry inside the kernel
(`decide +kernel`), so one kernel evaluation of the recheck on a real K1
artifact can be timed. Contracts are rendered as their defaults (the passes
only carry them). -/

namespace CompilatrixTests.Anf.LeanRender

open Compilatrix Compilatrix.Lam

def paren (s : String) : String := s!"({s})"

def ctorKey : Key.CtorKey → String
  | .src c => s!"(.src {c})"
  | k => paren (reprStr k)

def prim (p : Prim) : String := s!".{p.name}"

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

partial def term : Term → String
  | .var i => s!"(.var {i})"
  | .glob g => s!"(.glob {g})"
  | .lam m _ b => s!"(.lam .{if m == .name then "name" else "strict"} \{} {term b})"
  | .app f a m => s!"(.app {term f} {term a} .{if m == .name then "name" else "strict"})"
  | .letE _ v b => s!"(.letE \{ nonDep := true } {term v} {term b})"
  | .con c fs => s!"(.con {ctorKey c} {list (fs.map term)})"
  | .case s alts d =>
    let as := alts.map fun | .mk k n b => s!".mk {ctorKey k} {n} {term b}"
    let dd := match d with
      | some t => s!"(some {term t})"
      | none => "none"
    s!"(.case {term s} {list as} {dd})"
  | .proj c i s => s!"(.proj {ctorKey c} {i} {term s})"
  | .lit (.nat n) => s!"(.lit (.nat {n}))"
  | .lit (.str s) => s!"(.lit (.str {repr s}))"
  | .prim p args => s!"(.prim {prim p} {list (args.map term)})"
  | .tick t => s!"(.tick {term t})"
  | .box => ".box"
  | .trap => ".trap"

def optKey : Option Key.CtorKey → String
  | some k => s!"(some {ctorKey k})"
  | none => "none"

/-- A `Lam.Program` term. -/
def program (P : Lam.Program) : String :=
  let gs := P.globalList.map fun (g, gl) =>
    s!"  ({g}, \{ key := {reprStr gl.key}, body := {term gl.body} })"
  let cs := P.ctors.map fun c => s!"\{ key := {ctorKey c.key}, tag := {c.tag}, arity := {c.arity} }"
  s!"\{ globals := Src.NatMap.ofList [\n{",\n".intercalate gs}]\n  size := {P.size}\n" ++
  s!"  roots := {P.roots}\n  ctors := {list cs}\n" ++
  s!"  known := \{ natZero := {optKey P.known.natZero}, natSucc := {optKey P.known.natSucc}, " ++
  s!"boolFalse := {optKey P.known.boolFalse}, boolTrue := {optKey P.known.boolTrue} } }"

def step : Anf.Pipeline.Step → String
  | .shrink c => s!".shrink {c}"
  | .inline r => s!".inline {r}"
  | .specialize c =>
    let ds := c.decisions.map fun d =>
      s!"\{ caller := {d.caller}, callee := {d.callee}, mask := {d.mask} }"
    s!".specialize \{ inv := {c.inv}, decisions := {list ds} }"
  | .prune => ".prune"

/-- A `Pipeline.Cert` term. -/
def cert (c : Anf.Pipeline.Cert) : String :=
  s!"\{ shrink := \{ caseOfCase := {c.shrink.caseOfCase}, smallJoin := {c.shrink.smallJoin} }\n" ++
  s!"  steps := [{", ".intercalate (c.steps.map step)}] }"

/-- A module checking the recheck's result sizes in the kernel. -/
def module (name : String) (L : Lam.Program) (c : Anf.Pipeline.Cert) (globals nodes : Nat) :
    String :=
  s!"import Compilatrix.Anf.Pipeline\n\n/-! Kernel probe: the Phase 1 middle end re-run on bench-k1 `{name}`. -/\n\n" ++
  "open Compilatrix\n\n" ++
  s!"def lam : Lam.Program :=\n{program L}\n\n" ++
  s!"def cert : Anf.Pipeline.Cert :=\n{cert c}\n\n" ++
  "def sizes (P : Anf.Program) : Nat × Nat :=\n" ++
  "  (P.size, P.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0)\n\n" ++
  "set_option maxRecDepth 1000000 in\n" ++
  s!"example : (match Anf.Pipeline.run cert lam with | .ok P => some (sizes P) | .error _ => none) =\n    some ({globals}, {nodes}) := by\n" ++
  "  decide +kernel\n"

end CompilatrixTests.Anf.LeanRender
