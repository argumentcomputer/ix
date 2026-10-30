import Aiur.Library.U32
import Aiur.Library.List.Word

namespace AiurLibraryInterfaces
open Aiur

/-- Clients are checked against interfaces, before selecting implementations.
The aliases are static module applications, with no interpreter dispatch. -/
def clients : Modules.Program Nat := aiur_library% Library.U32.templates "
module ByteClient<B: U8Signature> {
    fn run(a: Field, b: Field) -> Field {
        let x = B::from_field(a);
        B::to_field(B::xor(x, B::from_field(b)))
    }
}
module WordClient<W: U32Signature> {
    fn run(a: Field, b: Field) -> Field {
        let x = W::from_field(a);
        let y = W::from_field(b);
        W::compact_field(W::compact(W::add(x, y)))
    }
}
module InterfaceBytes = ByteClient::<UInt8>;
module InterfaceWords = WordClient::<UInt32>;
"

run_cmd do
  -- Sealing must also protect clients parameterized by an abstract provider.
  for (signature, type) in [("U8Signature", "U8"), ("U8Signature", "Parts4"),
      ("U8Signature", "Parts7"), ("U32Signature", "U32"), ("U32Signature", "Compact")] do
    let source := s!"module Bad<B: {signature}> \{ fn run() -> B::{type} \{ hint::<B::{type}>(0) } }"
    let bad ← match Modules.Frontend.parse (← Lean.getEnv) source with
      | .ok value => pure value
      | .error error => throwError "invalid interface test: {error}"
    unless (Modules.checkTemplates (Library.U32.templates.append bad)).toOption.isNone do
      throwError "hint fabricated an abstract opaque {signature}::{type}"
  -- A provider cannot silently omit a checked constructor from the contract.
  let broken := { Library.U32.templates with modules := Library.U32.templates.modules.map fun m =>
    if m.name != "UInt32" then m else
      { m with body := match m.body with
        | .definitions d => .definitions { d with program.functions := d.program.functions.filter (·.name != "from_fields") }
        | body => body } }
  unless (Modules.checkTemplates broken).toOption.isNone do
    throwError "incomplete word provider satisfied U32Signature"

end AiurLibraryInterfaces
