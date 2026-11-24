import IxCK.Kernel.Admission
import IxCK.Kernel.Cached.Installed
import Ix.Address.Pure

/-! The last carrier of an indexed motive can occur after a let. -/

namespace Tests.Ix.Kernel.ReaderMotiveLet

open _root_.Ix.Kernel _root_.Ix.Kernel.Reader

private def family (nat : _root_.Address) (polymorphic : Bool) : Ixon.Constant :=
  let ind : Ixon.Inductive := {
    isUnsafe := false
    lvls := if polymorphic then 1 else 0
    params := 0
    indices := 1
    typ := .all (.ref 0 #[]) (.sort 0)
    ctors := #[] }
  ⟨.muts #[.indc ind], #[], #[nat],
    if polymorphic then #[.var 0] else #[.succ (.succ (.succ .zero))], #[]⟩

private def address (constant : Ixon.Constant) : _root_.Address :=
  _root_.Address.blake3Pure (Ixon.serConstant constant)

private def input (wrapped shared badK unsafeFlag polymorphic : Bool) :
    Except String (Array (_root_.Address × Ixon.Constant)) := do
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let family := family nat polymorphic
  let projection : Ixon.Constant := ⟨.iPrj ⟨0, address family⟩, #[], #[], #[], #[]⟩
  let carrier : Ixon.Expr := .ref 0 (if polymorphic then #[0] else #[])
  let tail : Ixon.Expr := if wrapped then
    .leanLet true (.ref 1 #[]) (.ref 2 #[])
      (.all (.app carrier (.var 1)) (.sort 1))
    else .all (.app carrier (.var 0)) (.sort 1)
  let motive : Ixon.Expr := .all (.ref 1 #[]) tail
  let recursor : Ixon.Recursor := {
    k := badK
    isUnsafe := unsafeFlag
    lvls := if polymorphic then 2 else 1
    params := 0
    indices := 1
    motives := 1
    minors := 0
    typ := .all (if shared then .share 0 else motive)
      (.all (.ref 1 #[]) (.all (.app carrier (.var 0))
        (.app (.app (.var 2) (.var 1)) (.var 0))))
    rules := #[] }
  let record : Ixon.Constant :=
    ⟨.recr recursor, if shared then #[motive] else #[],
      #[address projection, nat, zero],
      if polymorphic then #[.var 1, .var 0] else #[.succ .zero, .var 0], #[]⟩
  pure #[(address family, family), (address projection, projection), (address record, record)]

def check (wrapped shared : Bool) (badK unsafeFlag polymorphic : Bool := false) :
    Except String (Bool × Bool × Bool) := do
  let table ← defaultTable
  let pre ← (preludeFor table : Except String (Prelude .anon))
  let records ← input wrapped shared badK unsafeFlag polymorphic
  let cx := contextOf table records [] (pre.records ++ pre.evidence) pre.blobs (fun _ => none)
    (Admission.projectionAddress _root_.Address.blake3Pure)
  let bare := (readRecordsBare cx pre.state records).isOk
  match readRecords cx pre.state records with
  | .error _ => pure (bare, false, false)
  | .ok (_, declarations) =>
    pure (bare, true, (Cached.checkDecls .verified [] (Frontend.preparePrelude pre.ix declarations)).isOk)

def correctLevels (wrapped shared : Bool) : Except String Bool := do
  let table ← defaultTable
  let pre ← (preludeFor table : Except String (Prelude .anon))
  let records ← input wrapped shared false false true
  let cx := contextOf table records [] (pre.records ++ pre.evidence) pre.blobs (fun _ => none)
    (Admission.projectionAddress _root_.Address.blake3Pure)
  let some (owner, _) := records[records.size - 1]? | pure false
  let some entry := cx.index.recs[ConstRef.member owner 0]? | pure false
  unless entry.large do return false
  let .ok (_, declarations) := readRecords cx pre.state records | pure false
  pure (declarations.any fun
    | .indDecl members _ => members.any fun
      | .recInfo cv _ _ _ => cv.name == .id owner && cv.levelParams == [1, 0]
      | _ => false
    | _ => false)

#guard (check false false).toOption == some (true, true, true)
#guard (check true false).toOption == some (true, true, true)
#guard (check false true).toOption == some (true, true, true)
#guard (check true true).toOption == some (true, true, true)
#guard (check true false true).toOption == some (false, false, false)
#guard (check true false false true).toOption == some (false, false, false)

#guard (check false false (polymorphic := true)).toOption == some (true, true, true)
#guard (check true false (polymorphic := true)).toOption == some (true, true, true)
#guard (check false true (polymorphic := true)).toOption == some (true, true, true)
#guard (check true true (polymorphic := true)).toOption == some (true, true, true)
#guard (correctLevels false false).toOption == some true
#guard (correctLevels true false).toOption == some true
#guard (correctLevels false true).toOption == some true
#guard (correctLevels true true).toOption == some true

end Tests.Ix.Kernel.ReaderMotiveLet
