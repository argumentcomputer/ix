import Compilatrix.Own.Plain.Check
import Compilatrix.Recheck.Json

set_option autoImplicit false
namespace Compilatrix.Own.Plain.Certificate
open Lean (Json toJson)
open Compilatrix.Recheck.CertJson (arr nat str nats getArr)

def format : String := "compilatrix/own-plain/1"
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

def admit (F : Fir.Program) (j : Json) : Except String Program := do
  let bodies ← decode F j
  if checkPlainMap F bodies then return { source := F, bodies }
  else throw "own.cert.check: ownership proposal or source domain refused"

def ofText (F : Fir.Program) (text : String) : Except String Program := do
  admit F (← Json.parse text)

end Compilatrix.Own.Plain.Certificate
