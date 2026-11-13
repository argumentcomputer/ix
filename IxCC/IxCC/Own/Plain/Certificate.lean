import IxCC.Own.Plain.Check
import IxCC.Own.Plain.Owned
import IxCC.Recheck.Json
import IxCC.Src.Hints
import IxCC.Anf.Budget

set_option autoImplicit false
namespace IxCC.Own.Plain.Certificate
open Lean (Json toJson)
open IxCC.Recheck.CertJson (arr nat str nats getArr)

def format : String := "ixcc/own-plain/1"
def maxDepth : Nat := 4096

def action : Action → Json
  | .inc x n => arr [str "inc", nat x, nat n]
  | .dec x => arr [str "dec", nat x]

def action? (j : Json) : Except String Action := do
  match ← getArr j with
  | [.str "inc", x, n] => return .inc (← x.getNat?) (← n.getNat?)
  | [.str "dec", x] => return .dec (← x.getNat?)
  | _ => throw "own.cert.action: expected inc(x,n) or dec(x)"

mutual
def code : Code → Json
  | .act a k => arr [str "act", action a, code k]
  | .bind _ _ k => arr [str "bind", code k]
  | .jp _ _ captured _ b k => arr [str "join", toJson captured, code b, code k]
  | .jmp .. => arr [str "jump"]
  | .case _ alts dflt => arr [str "case", arr (alternatives alts), optional dflt]
  | .ret .. => arr [str "return"]
  | .tcall .. => arr [str "tail"]
  | .trap => arr [str "trap"]
def alternatives : List Alt → List Json
  | [] => []
  | .mk _ b :: bs => code b :: alternatives bs
def optional : Option Code → Json
  | none => .null
  | some c => code c
end

mutual
def code? : Nat → Json → Fir.Code → Except String Code
  | 0, _, _ => throw "own.cert.depth: decoding depth exhausted"
  | fuel + 1, j, source => do
    match (← getArr j), source with
    | [.str "act", a, k], source => return .act (← action? a) (← code? fuel k source)
    | [.str "bind", k], .bind x r next => return .bind x r (← code? fuel k next)
    | [.str "join", captured, b, k], .jp label params rec body next =>
      return .jp label params (← nats captured) rec (← code? fuel b body) (← code? fuel k next)
    | [.str "jump"], .jmp j as => return .jmp j as
    | [.str "case", branches, fallback], .case x alts dflt =>
      return .case x (← alternatives? fuel (← getArr branches) alts)
        (← optional? fuel fallback dflt)
    | [.str "return"], .ret a => return .ret a
    | [.str "tail"], .tcall f as => return .tcall f as
    | [.str "trap"], .trap => return .trap
    | _, _ => throw "own.cert.shape: source and ownership control trees differ"
def alternatives? : Nat → List Json → List Fir.Alt → Except String (List Alt)
  | _, [], [] => pure []
  | fuel + 1, j :: js, .mk key body :: bs => do
    return .mk key (← code? fuel j body) :: (← alternatives? fuel js bs)
  | 0, _, _ => throw "own.cert.depth: alternative decoding depth exhausted"
  | _, _, _ => throw "own.cert.alternatives: missing or extra branch"
def optional? : Nat → Json → Option Fir.Code → Except String (Option Code)
  | _, .null, none => pure none
  | fuel + 1, j, some body => do return some (← code? fuel j body)
  | 0, _, _ => throw "own.cert.depth: optional decoding depth exhausted"
  | _, _, _ => throw "own.cert.default: mismatched default branch"
end

def bodyMap : Src.NatMap Code → Json
  | .leaf => arr [str "leaf"]
  | .node value zero one => arr [str "node", optional value, bodyMap zero, bodyMap one]

def bodyMap? : Nat → Json → Src.NatMap Fir.Fun → Except String (Src.NatMap Code)
  | 0, _, _ => throw "own.cert.depth: function-map decoding depth exhausted"
  | fuel + 1, j, source => do
    match (← getArr j), source with
    | [.str "leaf"], .leaf => return .leaf
    | [.str "node", value, zero, one], .node fd zs os =>
      let body ← optional? fuel value (fd.map (·.body))
      return .node body (← bodyMap? fuel zero zs) (← bodyMap? fuel one os)
    | _, _ => throw "own.cert.functions: complete source and candidate map shapes differ"

def encode (bodies : Src.NatMap Code) : Json := arr [str format, bodyMap bodies]
def toText (bodies : Src.NatMap Code) : String := (encode bodies).compress

def decode (F : Fir.Program) (j : Json) : Except String (Src.NatMap Code) := do
  match ← getArr j with
  | [.str version, bodies] =>
    if version == format then bodyMap? maxDepth bodies F.funs
    else throw "own.cert.version: unsupported wire format"
  | _ => throw "own.cert.envelope: expected version and complete body map"

/-! ## The captured-work budget

The ownership checker takes, at each jump, one token of every variable the target join captures,
and at each declaration walks the captured list; a join may capture its whole lexical scope and be
jumped to from every branch, so its work is not linear in the certificate. Admission first sums
that work over the decoded map (a linear walk; `capturedCode` resolves a jump's target as the
checker's `Δ` does) and refuses a certificate past `budget` (by default `Anf.maxCapturedWork`)
before the checker runs. A refusal is policy, not soundness: acceptance is monotone in the budget
(`admit_mono`). `RcReplay.runFront` runs the checker twice more on the admitted map
(`checkScopedProgram`, `Public.lower`); their bound rests on `admit` having run first on the same
certificate (`RcReplay.runFront_budget`). -/

mutual
/-- Captured work of one body, accumulated in `acc`; `Δ` maps the joins in scope to the length of
their captured lists. -/
def capturedCode (Δ : Src.NatMap Nat) (acc : Nat) : Code → Nat
  | .act _ k => capturedCode Δ acc k
  | .bind _ _ k => capturedCode Δ acc k
  | .jp j _ captured rec body k =>
    let n := captured.length
    capturedCode (Δ.insert j n) (capturedCode (if rec then Δ.insert j n else Δ) (acc + n) body) k
  | .jmp j _ => acc + Δ.getD j 0
  | .case _ alts dflt => capturedOpt Δ (capturedAlts Δ acc alts) dflt
  | .ret _ => acc
  | .tcall .. => acc
  | .trap => acc
def capturedAlts (Δ : Src.NatMap Nat) (acc : Nat) : List Alt → Nat
  | [] => acc
  | .mk _ body :: rest => capturedAlts Δ (capturedCode Δ acc body) rest
def capturedOpt (Δ : Src.NatMap Nat) (acc : Nat) : Option Code → Nat
  | none => acc
  | some c => capturedCode Δ acc c
end

/-- The captured work of a whole body map: the sum over its bodies. -/
def capturedWork (bodies : Src.NatMap Code) : Nat :=
  bodies.toList.foldl (fun acc (_, body) => capturedCode .leaf acc body) 0

def checkBudget (budget : Nat) (bodies : Src.NatMap Code) : Except String Unit :=
  let work := capturedWork bodies
  if work ≤ budget then .ok ()
  else .error s!"own.cert.budget: the ownership certificate makes the checker take {work} captured tokens (jumps and join declarations), past the limit {budget} (Anf.maxCapturedWork)"

theorem checkBudget_ok {budget : Nat} {bodies : Src.NatMap Code} :
    checkBudget budget bodies = .ok () ↔ capturedWork bodies ≤ budget := by
  simp only [checkBudget]
  split <;> simp_all

/-! ## The parameter total

A function's parameters and a join point's cost no Anf node (a join counts one node whatever its
arity), so the node budgets do not bound them; but the source-domain check (`programDomain`,
`contractProgramDomain`: `freshSet` and `insertVars` over every parameter list) and the ownership
checker (a token for each parameter at every entry) walk every one, and the plain-RC verifier runs
both three times. Admission first counts them (a linear walk over the program) and refuses a
program past `params` (by default `Anf.maxParamTotal`) before it decodes the certificate;
`Recheck.runWithContracts` does the same before its domain check. A refusal is policy, not
soundness: acceptance is monotone in the limit (`admit_params_mono`). -/

mutual
/-- The parameters of the join points one body declares, added to `acc`. -/
def joinParamsCode (acc : Nat) : Fir.Code → Nat
  | .bind _ _ k => joinParamsCode acc k
  | .jp _ ps _ b k => joinParamsCode (joinParamsCode (acc + ps.length) b) k
  | .jmp .. => acc
  | .case _ alts dflt => joinParamsOpt (joinParamsAlts acc alts) dflt
  | .ret _ => acc
  | .tcall .. => acc
  | .trap => acc
def joinParamsAlts (acc : Nat) : List Fir.Alt → Nat
  | [] => acc
  | .mk _ body :: rest => joinParamsAlts (joinParamsCode acc body) rest
def joinParamsOpt (acc : Nat) : Option Fir.Code → Nat
  | none => acc
  | some c => joinParamsCode acc c
end

/-- The parameter total of a program: over its numbered functions (those `programDomain` checks),
each one's parameters and those of the join points its body declares. -/
def paramTotal (F : Fir.Program) : Nat :=
  (List.range F.size).foldl (fun acc f =>
    match F.fun? f with
    | none => acc
    | some fd => joinParamsCode (acc + fd.params.length) fd.body) 0

def checkParamTotal (limit : Nat) (F : Fir.Program) : Except String Unit :=
  let total := paramTotal F
  if total ≤ limit then .ok ()
  else .error s!"own.cert.params: the program has {total} parameters (of its functions and join points together), past the limit {limit} (Anf.maxParamTotal)"

theorem checkParamTotal_ok {limit : Nat} {F : Fir.Program} :
    checkParamTotal limit F = .ok () ↔ paramTotal F ≤ limit := by
  simp only [checkParamTotal]
  split <;> simp_all

/-- The refusal of a map the checker does not accept: the checker's first reason when the source
is in the domain and its pins are sound, the domain refusal otherwise. Computed only on refusal. -/
def checkRefusal (domain : Bool) (F : Fir.Program) (bodies : Src.NatMap Code) : String :=
  match domain && checkBoolPins F, checkMapE F bodies with
  | true, .error e => s!"own.cert.check: ownership proposal refused: {e}"
  | _, _ => "own.cert.check: ownership proposal or source domain refused"

/-- **Certificate admission.** The program must be within the parameter total (checked first, from
the program alone), the decoded map within the captured-work budget (linear), and the map accepted
by the ownership checker, which judges any placement of `inc`/`dec` (`Own.Plain.checkOwned`). -/
def admit (F : Fir.Program) (j : Json) (budget : Nat := Anf.maxCapturedWork)
    (params : Nat := Anf.maxParamTotal) : Except String Program := do
  checkParamTotal params F
  let bodies ← decode F j
  checkBudget budget bodies
  if checkOwned F bodies then return { source := F, bodies }
  else throw (checkRefusal (programDomain F) F bodies)

def ofText (F : Fir.Program) (text : String) (budget : Nat := Anf.maxCapturedWork)
    (params : Nat := Anf.maxParamTotal) : Except String Program := do
  Src.Hints.checkJsonText text
  admit F (← Json.parse text) budget params

/-- Contract-aware certificate admission: the same, with the checker's contract-aware domain
(`checkContractOwned`), admitting all frontend binder and let contract annotations (`0`, `1`,
`&`, `*`, `!`, `~`, `let borrow`). -/
def admitContract (F : Fir.Program) (j : Json) (budget : Nat := Anf.maxCapturedWork)
    (params : Nat := Anf.maxParamTotal) : Except String Program := do
  checkParamTotal params F
  let bodies ← decode F j
  checkBudget budget bodies
  if checkContractOwned F bodies then return { source := F, bodies }
  else throw (checkRefusal (contractProgramDomain F) F bodies)

def ofTextContract (F : Fir.Program) (text : String) (budget : Nat := Anf.maxCapturedWork)
    (params : Nat := Anf.maxParamTotal) : Except String Program := do
  Src.Hints.checkJsonText text
  admitContract F (← Json.parse text) budget params

end IxCC.Own.Plain.Certificate
