import IxC.Kernel.Admission
import IxC.Kernel.Cached.Installed
import Ix.Address.Pure

/-! The last carrier of an indexed motive can occur after a let. -/

namespace Tests.Ix.Kernel.ReaderMotiveLet

open _root_.Ix.Kernel _root_.Ix.Kernel.Reader

private def family (nat : _root_.Address) : Ixon.Constant :=
  let ind : Ixon.Inductive := {
    isUnsafe := false
    lvls := 0
    params := 0
    indices := 1
    typ := .all (.ref 0 #[]) (.sort 0)
    ctors := #[] }
  ⟨.muts #[.indc ind], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩

private def address (constant : Ixon.Constant) : _root_.Address :=
  _root_.Address.blake3Pure (Ixon.serConstant constant)

private def input (wrapped shared badK unsafeFlag : Bool) :
    Except String (Array (_root_.Address × Ixon.Constant)) := do
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let family := family nat
  let projection : Ixon.Constant := ⟨.iPrj ⟨0, address family⟩, #[], #[], #[], #[]⟩
  let tail : Ixon.Expr := if wrapped then
    .leanLet true (.ref 1 #[]) (.ref 2 #[])
      (.all (.app (.ref 0 #[]) (.var 1)) (.sort 1))
    else .all (.app (.ref 0 #[]) (.var 0)) (.sort 1)
  let motive : Ixon.Expr := .all (.ref 1 #[]) tail
  let recursor : Ixon.Recursor := {
    k := badK
    isUnsafe := unsafeFlag
    lvls := 1
    params := 0
    indices := 1
    motives := 1
    minors := 0
    typ := .all (if shared then .share 0 else motive)
      (.all (.ref 1 #[]) (.all (.app (.ref 0 #[]) (.var 0))
        (.app (.app (.var 2) (.var 1)) (.var 0))))
    rules := #[] }
  let record : Ixon.Constant :=
    ⟨.recr recursor, if shared then #[motive] else #[],
      #[address projection, nat, zero], #[.succ .zero, .var 0], #[]⟩
  pure #[(address family, family), (address projection, projection), (address record, record)]

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

end Tests.Ix.Kernel.ReaderMotiveLet
