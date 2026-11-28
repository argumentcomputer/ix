import IxCC.Ixon.V3.Env
import IxCC.Ixon.V3.PrimAddrs
import IxCC.Ixon.V3.Support
import IxCC.Tools.Check

/-! The primitive table's parity with `fixtures/ixon-v4/primitives.tsv` and the
`Nat` literal bytes. The retired v4 `addressed.tsv` roundtrip (superseded by
v5 `reject-parity.txt` and `testR5Ingress` in `IxCCTests.IxonV3.Ingress`) and
v4 resource handoff/validation cases (`R9`) are no longer read here. -/

namespace IxCCTests.IxonV3.Validation

open IxCC.Ixon IxCC.Ixon.V3

private def require (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError s!"v3 validation: {label}")

def run (root : System.FilePath) : IO Nat := do
  let mut assertions := 0
  let table := V3.PrimAddrs.leanParityTable
  let lines := (← IO.FS.readFile (root / "primitives.tsv")).splitOn "\n" |>.filter
    (fun line => !line.isEmpty && !line.startsWith "#")
  require (lines.length == table.size) "primitive inventory size differs"
  assertions := assertions + 1
  for line in lines do
    let [name, address] := line.splitOn "\t" | throw (IO.userError "invalid primitive fixture")
    if name == "eagerReduce" then
      -- The actual declaration aliases `id`. Only the synthetic, reserved
      -- marker may trigger eager reduction (the producer makes this exception).
      require (IxCC.Tools.Check.isHex 64 address &&
        address != V3.PrimAddrs.canonical.eagerReduce.toHex &&
        V3.PrimAddrs.canonical.eagerReduce.toHex ==
          "ff00000000000000000000000000000000000000000000000000000000000003")
        "synthetic eager-reduction marker"
    else
      require (table.any fun (n, a) => n == name && a.toHex == address) s!"primitive differs: {name}"
    assertions := assertions + 1
  for n in #[0, 1, 255, 256, 65535, 18446744073709551615, 2^130 + 513] do
    let blob : ByteArray := ⟨V3.natBytesLE n⟩
    require (V3.canonicalNatBytes blob && (V3.decodeNatBlob blob).toOption == some n) s!"natural bytes {n}"
    assertions := assertions + 1
  for bad in ([ByteArray.empty, ⟨#[0, 0]⟩, ⟨#[5, 0]⟩, ⟨#[0, 1, 0]⟩] : List ByteArray) do
    require (!V3.canonicalNatBytes bad && (V3.decodeNatBlob bad).toOption.isNone)
      s!"noncanonical natural blob {bad.data.toList}"
    assertions := assertions + 1
  require ((V3.natBytesLE 256) == #[0, 1]) "natural byte order"
  require ((V3.natBytesLE 0) == #[0]) "zero literal bytes"
  assertions := assertions + 2
  IO.println s!"v3 validation: {assertions} assertions passed"
  return assertions

end IxCCTests.IxonV3.Validation
