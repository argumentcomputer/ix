import Tests.Ix.AuxGen.LevelEgressTests
import Tests.Ix.AuxGen.Reference.Levels
import Lean.Elab.Command

namespace Tests.AuxGen.LevelReference
open Lean LSpec Ix.AuxGen

-- Read the original finite corpus, without duplicating or reducing it.
run_cmd do
  let env ← getEnv
  for (suffix, aliasName) in #[("kernelLevels", `corpus), ("lps", `scopeNames), ("toLean", `inputLevel)] do
    let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      if n.toString.startsWith "_private.Tests.Ix.AuxGen.LevelEgressTests." &&
          n.toString.endsWith (".Tests.AuxGen.LevelEgress." ++ suffix) then acc.push n else acc
    unless names.size == 1 do throwError "level reference corpus alias {suffix}: {names}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent names[0]!)))

private def arr (xs : List Json) : Json := .arr xs.toArray
private def nat (n : Nat) : Json := .str (toString n)
private def address (a : Address) : Json := arr [.str (toString a), nat a.hash.size]
private def name : Ix.Name → Json
  | .anonymous h => arr [.str "anonymous", address h]
  | .str p s h => arr [.str "str", name p, .str s, address h]
  | .num p n h => arr [.str "num", name p, nat n, address h]
private def level : Ix.Level → Json
  | .zero h => arr [.str "zero", address h]
  | .succ u h => arr [.str "succ", level u, address h]
  | .max u v h => arr [.str "max", level u, level v, address h]
  | .imax u v h => arr [.str "imax", level u, level v, address h]
  | .param n h => arr [.str "param", name n, address h]
  | .mvar n h => arr [.str "mvar", name n, address h]
private def input : Ix.Kernel.Level → Json
  | .zero => arr [.str "zero"]
  | .succ u => arr [.str "succ", input u]
  | .max u v => arr [.str "max", input u, input v]
  | .imax u v => arr [.str "imax", input u, input v]
  | .param i => arr [.str "param", nat i]
private def need (ok : Bool) (why : String) : Except String Unit :=
  unless ok do throw s!"level reference: {why}"

/-- Compare complete encodings: stored hashes are fields, not substitutes
for constructor/child/name equality. Every expected row is consumed. -/
private def check (document : Json) : Except String Unit := do
  let rows ← (← document.getObjVal? "rows").getArr?
  need (corpus.length == 1200 && rows.size == 1200 && scopeNames.size == 2) "coverage differs"
  let rangeInput : Ix.Kernel.Level := .max (.param 0) (.param 2)
  let refusal ← match Egress.egressLevel scopeNames rangeInput with
    | .error (.levelParamIndex 2) => pure (arr [.str "levelParamIndex", nat 2])
    | _ => throw "level reference: exact range refusal differs"
  let header := Json.mkObj [
    ("schema", .str "ix-level-expectations-v1"), ("parent", .str "33e23ffda0812dc64914627cdd77bedd1e6af1ca"),
    ("witness-sha256", .str "973dcd785e85c0a0faed5549bae3034d295f25e82c1f4b782b7748ae2c850eb9"),
    ("corpus-source-sha256", .str "e970a5bab6310d11a15da1e83c7df844469e4e3fdb4a183ef6785bdf931e8723"),
    ("scope", .arr (scopeNames.map name)), ("count", nat 1200),
    ("columns", arr (["position", "input", "tc-egress", "tc-normalize"].map Json.str)),
    ("rows", .arr rows), ("out-of-range", arr [input rangeInput, refusal])]
  need (document == header) "schema/identity/scope/range differs"
  for (raw, i) in corpus.zipIdx do
    let .arr #[position, original, expected, expectedNormalized] := rows[i]!
      | throw s!"level reference: row shape differs at {i}"
    need (position == nat i && original == input raw) s!"input/order differs at {i}"
    let actual ← (Egress.egressLevel scopeNames raw).mapError toString
    need (level actual == expected) s!"egress differs at {i}"
    need (level (Egress.normalize (inputLevel raw)) == expectedNormalized) s!"normalize differs at {i}"

def evaluate : IO Unit := do
  let document ← IO.ofExcept (Json.parse Reference.Levels.json)
  IO.ofExcept (check document)
  let rows ← IO.ofExcept ((← IO.ofExcept (document.getObjVal? "rows")).getArr?)
  let .arr #[position, original, .arr #[.str "zero", .arr #[.str hash, size]], normalized] := rows[0]!
    | throw (IO.userError "level reference: perturbation fixture shape differs")
  unless hash.length == 64 && size == nat 32 do throw (IO.userError "level reference: hash shape differs")
  let changedHash := (if hash.startsWith "0" then "1" else "0") ++ (hash.drop 1).toString
  let changed := arr [position, original, arr [.str "zero", arr [.str changedHash, size]], normalized]
  let mutated := document.setObjVal! "rows" (.arr (rows.set! 0 changed))
  match check mutated with
  | .error e => unless e == "level reference: egress differs at 0" do
      throw (IO.userError s!"level reference: wrong perturbation failure: {e}")
  | .ok _ => throw (IO.userError "level reference: changed stored hash escaped the same checker")
  IO.println "level reference: 1200 ordered inputs / 2400 complete legacy outputs; exact scope/range and stored-hash perturbation"

def suite : List TestSeq := [
  .individualIO "complete finite legacy level witnesses and hash perturbation" none
    (do evaluate; return (true, 1, 0, none)) .done]

end Tests.AuxGen.LevelReference
