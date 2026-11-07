import Aiur.Optimized.Grouping.Snapshot
import Aiur.Trace.Export
import Aiur.Library.U32.Goldilocks

open Aiur Aiur.Optimized Lean
private abbrev F := Library.U32.Goldilocks.F
private instance : ToJson F := ⟨fun x => toJson x.val⟩
private instance : FromJson F := ⟨fun j => (fun n : Nat => (n : F)) <$> fromJson? j⟩

private def ident (snapshot : Grouping.Snapshot F) (name : String) : Except String Nat :=
  if snapshot.callables.contains name then .ok (snapshot.callables.idxOf name)
  else .error s!"unknown callable {name}"

private def maxDegree (ps : List (Optimized.Polynomial F)) : Nat :=
  ps.foldl (fun n p => max n p.simplify.degree) 0

private def metrics (snapshot : Grouping.Snapshot F) (origin : Circuit.Chip F)
    (optimize : Bool) : Except String Json := do
  let chip := Activation.compile origin
  let (provided, required) ← Grouping.messages (ident snapshot) chip
  let args := provided ++ required.flatMap (·.args)
  let privateCols ← Grouping.privateColumns chip origin.numVars (if optimize then args else [])
  let select := fun p => if optimize then Grouping.selectArgument origin.numVars privateCols p
    else (Grouping.gate origin.numVars privateCols p).simplify
  let lifted := (args.filter fun p => (select p).degree > 2).dedup
  let degree := fun ps => maxDegree (ps.map fun p =>
    if (select p).degree > 2 then .var 0 else select p)
  let constraints := (Grouping.member chip origin.numVars privateCols).constraints
  return Json.mkObj [
    ("name", toJson origin.name), ("width", toJson chip.numVars),
    ("private", toJson privateCols.length), ("shared", toJson (chip.numVars - privateCols.length)),
    ("lifted", toJson lifted.length), ("private_columns", toJson privateCols),
    ("constraint_degree", toJson (max (maxDegree constraints) (if lifted.isEmpty then 2 else 3))),
    ("lookups", toJson ((degree provided, (1 : Nat)) ::
      required.map (fun s => (degree s.args, s.enable.degree))))]

def main (args : List String) : IO Unit := do
  let some (input : String) := args[0]? | throw (IO.userError "usage: grouping_tune SNAPSHOT OUTPUT [--metrics] [--baseline] [--policy POLICY]")
  let some (output : String) := args[1]? | throw (IO.userError "missing output path")
  let snapshot : Grouping.Snapshot F ← IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse (← IO.FS.readFile input))))
  let optimize := !args.contains "--baseline"
  if args.contains "--metrics" then
    let chips ← IO.ofExcept (snapshot.chips.mapM fun c => metrics snapshot c optimize)
    IO.FS.writeFile output (Json.mkObj [("chips", toJson chips),
      ("groups", toJson snapshot.groups), ("entries", toJson snapshot.entries),
      ("representatives", toJson snapshot.representatives)]).compress
    return
  let policy ← if args.contains "--policy" then do
    let some path := args[args.idxOf "--policy" + 1]? | throw (IO.userError "missing policy path")
    IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse (← IO.FS.readFile path))))
  else pure snapshot.groups
  let resolve := fun name => ((snapshot.representatives.find? (·.1 == name)).map Prod.snd).getD name
  let mut used : List String := []
  let mut packed : List (Grouping.Packed F (ident snapshot)) := []
  for (name, names) in policy do
    let names := (names.map resolve).dedup
    let chips := snapshot.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !snapshot.entries.contains c.name
    if chips.length < 2 then continue
    let checked ← IO.ofExcept (Grouping.compile name (ident snapshot) chips optimize)
    used := used ++ chips.map (·.name)
    packed := packed ++ [⟨chips, checked⟩]
    IO.eprintln s!"{name}: {chips.length} members, {checked.layout.width + 1} main columns"
  let plan ← IO.ofExcept (Grouping.preparePlan {chips := snapshot.chips} (ident snapshot) packed)
  IO.FS.writeFile output (toJson (plan.groups.map fun p => Trace.groupJson ZMod.val p.checked.layout)).compress
