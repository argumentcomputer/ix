import Compilatrix.Modular.Report

open Compilatrix Compilatrix.Modular

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["run", output] => Report.run output
    | ["replay", input, output] => Report.replay input output
    | _ =>
        IO.eprintln "usage: source-modular run <new-directory> | replay <retained-directory> <new-directory>"
        return 2
    return 0
  catch err =>
    IO.eprintln s!"source-modular: {err}"
    return 1
