module

public import Ix.Typing
public import IxC.Resource

/-!
# Mode checking of a compiled artifact (uncertified)

`checkArtifact` runs the mode checker (`IxC.Resource.check`) on an artifact:
every record of it is a seed. An artifact whose every mode is the default is
accepted without reading it (the checker's fast path). Otherwise the checker
reads its run program with the kernel as class oracle, over the environment
the artifact's certified typing installs (`Ix.Typing.checkCertified`), and
accepts, refuses with a witness, or declines at a limit.

**The checker is uncertified**: nothing proves its verdict (`IxC.Resource.CheckSound`
is a definition, the statement left to prove), and every message here says so.
-/

@[expose] public section

namespace Ix.ModeCheck

/-- A verdict's message. -/
def describe : IxC.Resource.Verdict → String
  | .accept _ true => "mode checking (uncertified): every mode is the default"
  | .accept n false => s!"mode checking (uncertified): {n} run bodies checked, accepted"
  | .refuse at_ w => s!"mode checking (uncertified) refuses {at_}: {w}"
  | .decline r => s!"mode checking (uncertified) declines: {r}"

/-- **Mode checking of an artifact** (uncertified): the message of an accept,
or the refusal or decline as the error. -/
def checkArtifact (ixe : Ixon.Env) : Except String String := do
  let input ← Ix.Typing.typingInput ixe
  let records : Std.HashMap Address Ixon.Constant :=
    input.ordered.foldl (fun m (a, c, _) => m.insert a c) {}
  let prelude : Std.HashMap Address Ixon.Constant :=
    (input.pre.records ++ input.pre.evidence).foldl (fun m (a, c) => m.insert a c) {}
  let blobs : Std.HashMap Address ByteArray := input.blobs.foldl (fun m (a, b) => m.insert a b) {}
  let s : IxC.Resource.Subject :=
    { table := input.table, store := fun a => records[a]? <|> prelude[a]?, blob := fun a => blobs[a]?,
      seeds := input.ordered.toList.map (·.1) }
  -- the fast path needs no typing
  let fast := IxC.Resource.check {} Ix.Kernel.Env.empty s
  if let .accept _ true := fast then return describe fast
  let env ← match Ix.Typing.checkCertified input (Ix.Typing.splitOf input) with
    | .ok env => pure env
    | .error (e, _) => throw s!"mode checking (uncertified): the typing it reads with failed: {e}"
  let v := IxC.Resource.check {} env s
  match v with
  | .accept .. => return describe v
  | _ => throw (describe v)

end Ix.ModeCheck

end
