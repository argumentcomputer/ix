import Ix.Frontend

/-! Native-only inspection artifacts for the representative full ElabClaim
pipeline. These exports are not inputs to the direct Aiur implementation. -/
namespace FrontendFullExport
open Ix.Frontend

def syntaxJSON : Ix.Syntax → Lean.Json
  | .missing => .arr #[Lean.toJson (0 : Nat)]
  | .atom _ s => .arr #[Lean.toJson (1 : Nat), Lean.toJson s]
  | .ident _ _ n _ => .arr #[Lean.toJson (2 : Nat), Lean.toJson (Name.toStringTotal n)]
  | .node _ k args => .arr #[Lean.toJson (3 : Nat), Lean.toJson (Name.toStringTotal k),
      .arr (args.attach.map fun a => syntaxJSON a.val)]
termination_by s => sizeOf s
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem a.property) (by omega)

def write (stx : Ix.Syntax) (env : Ixon.Env) : IO Unit := do
  IO.FS.writeFile ".lake/frontend-benchmark/full-syntax.json" (syntaxJSON stx).compress
  let mut entries := #[]
  for (nm, n) in env.named.toArray do
    let name := Name.toStringTotal nm
    if name.startsWith "Demo." || (name.startsWith "Ix." && name.endsWith ".Demo.Pair") then
      let some c := env.getConst? n.addr | throw (IO.userError "missing compiled constant")
      entries := entries.push (Lean.Json.mkObj [
        ("name",Lean.toJson name), ("address",Lean.toJson (toString n.addr)),
        ("sharing_size",Lean.toJson c.sharing.size),
        ("constant",Lean.toJson (reprStr c)), ("metadata",Lean.toJson (reprStr n.constMeta)),
        ("bytes",Lean.toJson ((Ixon.ser c).data.map UInt8.toNat))])
  IO.FS.writeFile ".lake/frontend-benchmark/full-user-compiled.json" (Lean.Json.arr entries).compress
end FrontendFullExport
