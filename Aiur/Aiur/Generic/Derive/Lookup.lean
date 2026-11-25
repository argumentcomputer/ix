import Aiur.Generic.Derive.Basic
import Aiur.Generic.LookupFacts

/-! # Deriving a program's lookup facts -/

namespace Aiur.Generic.Derive
open Aiur.Generic

variable {F : Type} [Target F]

/-- **The lookup facts**: for every function with no type parameters (named by
its plain name), a theorem that the program resolves its name to its closure,
proved by `Program.sourceFunction?_of_mem` from the function's index and one
certificate that the names' keys are distinct (sort with `cbv`, then check
adjacent natural numbers with `decide +kernel`). Generic functions get no fact here.

The declarations are stated in the program's namespace, about its `program`, `functions`
and `maps` (`Aiur.Generic.LookupFacts` is to be imported where they are elaborated).

With `part := some (i, n)`, the `i`-th (from 1) of `n` parts of the functions' facts: the
facts do not depend on each other, but on the certificate, which the first part declares
and the others import. -/
def lookup (prog : Program F) (fnNames : List String) (part : Option (Nat × Nat) := none) :
    String := Id.run do
  let mut facts : List String := []
  let mut index := 0
  for name in fnNames do
    if let some f := prog.functions.find? (·.name == name) then
      if f.typeParams.isEmpty && name.toList.head? != some '$' then
        let leanName := functionName F name
        facts := facts ++ [s!"theorem {leanName}.lookup : program.sourceFunction? {q name} =\n" ++
          s!"    some \{ types := [], params := {leanName}.params.map fun (n, t) => (n, (t.subst []).toCore),\n" ++
          s!"           body := {leanName}.body } :=\n" ++
          s!"  Program.sourceFunction?_of_mem (f := {leanName}) functionNames_nodup\n" ++
          s!"    (List.getElem_mem (l := functions) (n := {index}) (by decide +kernel))\n" ++
          s!"    (head_ne_of_bytes (by decide +kernel)) rfl\n"]
    index := index + 1
  let (first, kept) : Bool × List String := match part with
    | none => (true, facts)
    | some (i, n) =>
      (i == 1, (facts.zipIdx.filter fun p => partOf n p.2 facts.length == i).map (·.1))
  let opening :=
    s!"namespace {Target.program F}\nopen Aiur.Generic\n\nset_option maxRecDepth 100000\n\n"
  let closing := "\n".intercalate kept ++ s!"\nend {Target.program F}\n"
  unless first do return opening ++ closing
  return opening ++
    "/-- The function names as numbers (`nameKey`). -/\n" ++
    s!"def functionKeys : List Nat := {listLines (fnNames.map fun n => toString (nameKey n))}\n\n" ++
    "/-- The keys are the names' keys: each name's key computed once. -/\n" ++
    "theorem functionKeys_eq : functions.map (fun f => nameKey f.name) = functionKeys := by decide +kernel\n\n" ++
    "set_option cbv.maxSteps 1000000 in\n" ++
    "theorem functionKeys_nodup : functionKeys.Nodup :=\n" ++
    "  nodup_of_sortedKeys (by cbv; decide +kernel)\n\n" ++
    "/-- **The function names are distinct**, certified on their keys. -/\n" ++
    "theorem functionNames_nodup : (functions.map (·.name)).Nodup :=\n" ++
    "  nodup_of_nameKeys (by simpa only [List.map_map, Function.comp_def, functionKeys_eq] using functionKeys_nodup)\n\n" ++
    "/-- **No map is named like a function.** -/\n" ++
    "theorem mapKeys_fresh : ∀ m ∈ maps, nameKey m.name ∉ functions.map (fun f => nameKey f.name) := by\n" ++
    "  rw [functionKeys_eq]; decide +kernel\n\n" ++ closing

end Aiur.Generic.Derive
