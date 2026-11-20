/-!
# `ixai mines`: a summary of the local Truth Mines index
-/

namespace IxAICli

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- Summarize the local Truth Mines index: every certified claim, grouped by subject. -/
def mines (path : System.FilePath) : IO UInt32 := do
  let rows := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
  let verified := rows.filter fun r => r.getD 8 "" == "verified"
  let failed := rows.filter fun r => (r.getD 8 "").startsWith "FAILED" || (r.getD 6 "") == "-"
  IO.println s!"{rows.length} records: {verified.length} verified, {rows.length - verified.length} not"
  let groupOf := fun (r : List String) => ".".intercalate ((r.getD 1 "").splitOn ".").dropLast
  let groups := rows.foldl (fun (acc : List String) r =>
    if acc.contains (groupOf r) then acc else acc ++ [groupOf r]) []
  for g in groups do
    IO.println s!"\n{g}"
    for r in rows.filter (groupOf · == g) do
      let name := ((r.getD 1 "").splitOn ".").getLast!
      let what := if r.getD 0 "" == "eval" then s!"{name} ⇒ {(r.getD 3 "").take 12}" else s!"{name} : checked"
      IO.println s!"  {r.getD 8 ""}  {what}  proof {(r.getD 5 "").take 12}  {r.getD 6 ""} s"
  let _ := failed
  return 0

end IxAICli
