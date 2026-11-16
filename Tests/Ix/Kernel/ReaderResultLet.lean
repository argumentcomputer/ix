import IxC.Kernel.Admission
import IxC.Kernel.Cached.Installed
import Ix.Address.Pure

/-! Recursor result lets are consumed before the result's motive is indexed. -/

namespace Tests.Ix.Kernel.ReaderResultLet

open _root_.Ix.Kernel _root_.Ix.Kernel.Reader

private def family : Ixon.Constant :=
  ⟨.muts #[.indc { isUnsafe := false, lvls := 0, params := 0, indices := 0,
    typ := .sort 0, ctors := #[] }], #[], #[], #[.succ (.succ (.succ .zero))], #[]⟩

private def address (c : Ixon.Constant) : _root_.Address := _root_.Address.blake3Pure (Ixon.serConstant c)

private def projection : Ixon.Constant := ⟨.iPrj ⟨0, address family⟩, #[], #[], #[], #[]⟩

private def input (wrapped shared : Bool) (badK unsafeFlag : Bool) :
    Except String (Array (_root_.Address × Ixon.Constant)) := do
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let result : Ixon.Expr := if wrapped then
    .leanLet true (.ref 1 #[]) (.ref 2 #[]) (.app (.var 2) (.var 1))
    else .app (.var 1) (.var 0)
  let type : Ixon.Expr :=
    .all (.all (.ref 0 #[]) (.sort 1)) (.all (.ref 0 #[]) (if shared then .share 0 else result))
  let recursor : Ixon.Constant :=
    ⟨.recr { k := badK, isUnsafe := unsafeFlag, lvls := 1, params := 0, indices := 0,
      motives := 1, minors := 0, typ := type, rules := #[] },
      if shared then #[result] else #[], #[address projection, nat, zero], #[.succ .zero, .var 0], #[]⟩
  pure #[(address family, family), (address projection, projection), (address recursor, recursor)]

def check (wrapped shared : Bool) (badK unsafeFlag : Bool := false) : Except String (Bool × Bool × Bool) := do
  let table ← defaultTable
  let pre ← (preludeFor table : Except String (Prelude .anon))
  let records ← input wrapped shared badK unsafeFlag
  let cx := contextOf table records [] (pre.records ++ pre.evidence) pre.blobs (fun _ => none)
    (Admission.projectionAddress _root_.Address.blake3Pure)
  let bare := (readRecordsBare cx pre.state records).isOk
  match readRecords cx pre.state records with
  | .error _ => pure (bare, false, false)
  | .ok (_, declarations) =>
    pure (bare, true, (Cached.checkDecls .verified [] (Frontend.preparePrelude pre.ix declarations)).isOk)

#guard (check false false).toOption == some (true, true, true)
#guard (check true false).toOption == some (true, true, true)
#guard (check false true).toOption == some (true, true, true)
#guard (check true true).toOption == some (true, true, true)
#guard (check true false true).toOption == some (false, false, false)
#guard (check true false false true).toOption == some (false, false, false)

end Tests.Ix.Kernel.ReaderResultLet
