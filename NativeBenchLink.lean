import Lean

def main (args : List String) : IO Unit := do
  let [source, output, object] := args | throw (IO.userError "expected source response, output response, object")
  let rsp ← IO.FS.readFile source
  let lines := rsp.splitOn "\n"
  let replaced := lines.map fun line =>
    if (line.splitOn "/Main.c.o.export").length == 2 then object else line
  IO.FS.writeFile output (String.intercalate "\n" replaced)
