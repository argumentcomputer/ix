/-
  `ix prims`: the primitive profile, the Ixon object binding the checker's
  pinned roles (literal types, `Nat` and `String` operations, `Quot`, ...)
  to content addresses.

    ix prims export <env.ixe> [--out <file>]   write the profile of the
                                               toolchain that compiled the
                                               env; prints its address
    ix prims info <file>                       describe a profile object

  The Rust checker takes `IX_PRIM_PROFILE=<file>` to bind its roles to the
  exported profile. The checker validates literal construction and optional
  reduction contracts before enabling rules at new addresses. Unsupported
  accelerations use ordinary reduction; required unsupported rules fail.
-/
module
public import Cli
public import Ix.Common

public section

namespace Ix.Cli.PrimsCmd

@[extern "rs_prim_profile_export"]
opaque rsPrimProfileExportFFI : @& String → @& String → IO String

@[extern "rs_prim_profile_info"]
opaque rsPrimProfileInfoFFI : @& String → IO String

def runPrimsExport (p : Cli.Parsed) : IO UInt32 := do
  let some ixeArg := p.positionalArg? "ixe"
    | p.printError "error: must specify <ixe-path>"; return 1
  let ixePath := ixeArg.as! String
  let outPath := match p.flag? "out" with
    | some flag => flag.as! String
    | none => ixePath ++ ".prims"
  let hex ← rsPrimProfileExportFFI ixePath outPath
  IO.eprintln s!"[prims] wrote {outPath}"
  IO.println hex
  return 0

def runPrimsInfo (p : Cli.Parsed) : IO UInt32 := do
  let some fileArg := p.positionalArg? "file"
    | p.printError "error: must specify <profile-path>"; return 1
  IO.println (← rsPrimProfileInfoFFI (fileArg.as! String))
  return 0

def runPrims (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.PrimsCmd

open Ix.Cli.PrimsCmd in
def primsExportCmd : Cli.Cmd := `[Cli|
  "export" VIA runPrimsExport;
  "Write the primitive profile object of the toolchain that compiled a `.ixe`, read from its named section, and print the object's address. Pass the file as IX_PRIM_PROFILE to `ix check-rs`."

  FLAGS:
    out : String; "Output path (default: `<ixe>.prims`)."

  ARGS:
    ixe : String; "Path to a serialized Ixon env (`.ixe`)."
]

open Ix.Cli.PrimsCmd in
def primsInfoCmd : Cli.Cmd := `[Cli|
  info VIA runPrimsInfo;
  "Describe a primitive profile as JSON: address, object format, schema version, every binding (null when absent), and whether it equals the built-in table."

  ARGS:
    file : String; "Path to a profile object written by `ix prims export`."
]

open Ix.Cli.PrimsCmd in
def primsCmd : Cli.Cmd := `[Cli|
  prims VIA runPrims;
  "Primitive profiles: which declarations play the checker's pinned roles"

  SUBCOMMANDS:
    primsExportCmd;
    primsInfoCmd
]

end
