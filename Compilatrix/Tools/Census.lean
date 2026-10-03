import Compilatrix.Ixon.V3.Validate
import Compilatrix.Tools.Check

/-! Admission census over an Ixon v3 closure.

For every constant, the census records the first stage that rejects it:
strict decoding, erased typing, then the compilation policy for constants
without usable kernel semantics (`partial` and `unsafe` definitions, plan
decision D12). Constants that pass every implemented stage report the next
stage of the rebuilt pipeline, which does not exist yet. The report also
records headroom against the v3 consumer budgets. Output is deterministic:
constants are sorted by address and every summary is a sorted count. -/

namespace Compilatrix.Tools.Census

open Lean Compilatrix.Ixon Compilatrix.Ixon.V3

/-- The first stage of the rebuilt pipeline, reported as the next stage for
constants that pass every implemented stage. -/
def nextStage : String := "src"

/-- Syntactic depth of a v3 expression; a `share` reference counts as a leaf. -/
def exprDepth : V3.Expr → Nat
  | .prj _ _ body => exprDepth body + 1
  | .app function argument => max (exprDepth function) (exprDepth argument) + 1
  | .lam _ type body => max (exprDepth type) (exprDepth body) + 1
  | .all _ _ type body => max (exprDepth type) (exprDepth body) + 1
  | .letE _ type value body =>
      max (exprDepth type) (max (exprDepth value) (exprDepth body)) + 1
  | _ => 1

def constantDepth (constant : V3.Constant) : Nat :=
  (constant.info.exprs ++ constant.sharing.toList).foldl (fun deepest e => max deepest (exprDepth e)) 0

def safetyName : Compilatrix.Ixon.DefinitionSafety → String
  | .safe => "safe"
  | .unsaf => "unsafe"
  | .part => "partial"

def definitionKind (definition : V3.Definition) : String :=
  match definition.kind with
  | .defn => "definition"
  | .opaq => "opaque"
  | .thm => "theorem"

def memberKind : V3.MutConst → String
  | .defn definition => definitionKind definition
  | .indc _ => "inductive"
  | .recr _ => "recursor"

/-- The kind of a constant, and the safety of any definition it contains. -/
def describe (constant : V3.Constant) : String × String :=
  let definitions := (selfMutsOf constant.info).filterMap fun
    | .defn definition => some definition
    | _ => none
  let safety := if definitions.any (·.safety == .unsaf) then "unsafe"
    else if definitions.any (·.safety == .part) then "partial" else "safe"
  match constant.info with
  | .defn definition => (definitionKind definition, safetyName definition.safety)
  | .recr recursor => ("recursor", if recursor.isUnsafe then "unsafe" else "safe")
  | .axio ax => ("axiom", if ax.isUnsafe then "unsafe" else "safe")
  | .quot _ => ("quotient", "safe")
  | .cPrj _ => ("constructor-projection", "safe")
  | .rPrj _ => ("recursor-projection", "safe")
  | .iPrj _ => ("inductive-projection", "safe")
  | .dPrj _ => ("definition-projection", "safe")
  | .muts members => ("mutual:" ++ ",".intercalate (members.toList.map memberKind), safety)

/-- One constant's census record. -/
structure Entry where
  address : Ixon.Address
  name : Option String
  kind : String
  safety : String
  bytes : Nat
  depth : Nat
  /-- The last stage passed. -/
  reached : String
  /-- The stage that rejected it, if any, with the message. -/
  rejected : Option (String × String)

def Entry.json (entry : Entry) : Json :=
  Json.mkObj <|
    [("address", Json.str entry.address.toHex)] ++
    (entry.name.map fun name => [("name", Json.str name)]).getD [] ++
    [("kind", Json.str entry.kind), ("safety", Json.str entry.safety),
     ("bytes", toJson entry.bytes), ("depth", toJson entry.depth),
     ("reached", Json.str entry.reached)] ++
    match entry.rejected with
    | none => [("next", Json.str nextStage)]
    | some (stage, message) =>
        [("rejected_at", Json.str stage), ("message", Json.str message)]

/-- A constant that strict decoding rejected. -/
def undecoded (address : Ixon.Address) (name : Option String) (bytes : Nat)
    (message : String) : Entry :=
  { address := address, name := name, kind := "undecodable", safety := "unknown",
    bytes := bytes, depth := 0, reached := "ingress", rejected := some ("decode", message) }

/-- Decode, type and classify every constant. Typing continues after a
rejection from the last accepted checker state, so one failure does not hide
the verdicts of unrelated constants. -/
def entries (env : V3.Env) (names : Std.HashMap Ixon.Address String) : Array Entry := Id.run do
  let addresses := env.consts.keys.toArray.qsort (fun a b => a.cmpBytes b == .lt)
  let mut state := Tc.initialState env
  let mut sinceClear := 0
  let mut output := #[]
  for address in addresses do
    let raw := env.consts[address]?.getD .empty
    let name := names[address]?
    let verified := Tc.getConstVerified env address
    match verified with
    | .error error =>
        output := output.push (undecoded address name raw.size (toString error))
    | .ok none =>
        output := output.push (undecoded address name raw.size "missing")
    | .ok (some constant) =>
      let (kind, safety) := describe constant
      let base : Entry :=
        { address := address, name := name, kind := kind, safety := safety,
          bytes := raw.size, depth := constantDepth constant, reached := "decode",
          rejected := none }
      let typing : Except String (Tc.TcState .anon) := do
        let target ← Tc.checkTarget address constant
        match (Tc.TcM.checkConst (⟨target, ()⟩ : Tc.KId .anon)).run
            { state with recFuel := state.fuelBudget } with
        | .error error _ => throw (toString (repr error))
        | .ok () next => pure next
      match typing with
      | .error message =>
          output := output.push { base with rejected := some ("typing", message) }
      | .ok next =>
        state := next
        sinceClear := sinceClear + 1
        if sinceClear == 50 then
          state := { state with env := state.env.clearReductionCaches }
          sinceClear := 0
        if safety == "partial" || safety == "unsafe" then
          let message := s!"{safety} definition: rejected by plan decision D12; \
            use partial_fixpoint, termination_by or fuel"
          output := output.push { base with reached := "typing", rejected := some ("policy", message) }
        else
          output := output.push { base with reached := "policy" }
  return output

/-- Sorted `(key, count)` pairs. -/
def counts (keys : Array String) : Json :=
  let sorted := keys.qsort (· < ·)
  let grouped := sorted.foldl (init := (#[] : Array (String × Nat))) fun acc key =>
    match acc.back? with
    | some (last, n) => if last == key then acc.pop.push (last, n + 1) else acc.push (key, 1)
    | none => acc.push (key, 1)
  Json.mkObj (grouped.toList.map fun (key, n) => (key, toJson n))

def headroom (label : String) (actual limit : Nat) : Json :=
  Json.mkObj [("budget", Json.str label), ("actual", toJson actual), ("limit", toJson limit)]

/-- The complete census report for one environment. -/
def report (raw : ByteArray) (names : Std.HashMap Ixon.Address String) : Json :=
  match decodeAnonymousEnv raw with
  | .error error =>
      Json.mkObj [("format", Json.str "compilatrix/census/1"),
        ("ingress", Json.str "rejected"), ("message", Json.str error)]
  | .ok env =>
    let all := entries env names
    let maxBytes := all.foldl (fun m e => max m e.bytes) 0
    let maxDepth := all.foldl (fun m e => max m e.depth) 0
    Json.mkObj [
      ("format", Json.str "compilatrix/census/1"),
      ("ingress", Json.str "accepted"),
      ("root", Json.str env.root.toHex),
      ("constants", toJson all.size),
      ("budgets", Json.arr #[
        headroom "environment bytes" raw.size (16 * 1024 * 1024),
        headroom "constants" env.consts.size 16384,
        headroom "blobs" env.blobs.size 16384,
        headroom "largest constant bytes" maxBytes (1024 * 1024),
        headroom "deepest expression" maxDepth 256,
        headroom "typing declarations" all.size 4096]),
      ("kinds", counts (all.map (·.kind))),
      ("reached", counts (all.map (·.reached))),
      ("rejected_at", counts (all.filterMap (·.rejected.map (·.1)))),
      ("entries", Json.arr (all.map Entry.json))]

/-- Addresses named by a K1-style `equations.json` (roots, definitions and
their unfolding equations), for readable reports. Names are diagnostic only. -/
def names (pack : Json) : IO (Std.HashMap Ixon.Address String) := do
  let mut map : Std.HashMap Ixon.Address String := {}
  let decode (hex : String) : IO Ixon.Address := do
    Compilatrix.Tools.Check.present (Address.ofBytes? (← Compilatrix.Tools.Check.checked
      (Compilatrix.Tools.Check.unhex hex))) s!"invalid address {hex}"
  for root in ← Compilatrix.Tools.Check.arrField pack "roots" do
    map := map.insert (← decode (← Compilatrix.Tools.Check.strField root "address"))
      (← Compilatrix.Tools.Check.strField root "name")
  for pair in ← Compilatrix.Tools.Check.arrField pack "equations" do
    map := map.insert (← decode (← Compilatrix.Tools.Check.strField pair "definition_address"))
      (← Compilatrix.Tools.Check.strField pair "definition")
    map := map.insert (← decode (← Compilatrix.Tools.Check.strField pair "equation_address"))
      (← Compilatrix.Tools.Check.strField pair "equation")
  return map

end Compilatrix.Tools.Census
