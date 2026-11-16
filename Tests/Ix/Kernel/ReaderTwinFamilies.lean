import IxC.Kernel.Admission
import IxC.Kernel.Cached.Installed
import Ix.Address.Pure

/-! # Reading covered recursor records after their canonical entries change

The original stream checks successfully with each payload canonical. Earlier recursors
for two independent families make two payloads of one later record twins. Both the mixed
inductive and the recursor-only path must read those payloads against their own families.
-/

namespace Tests.Ix.Kernel.ReaderTwinFamilies

open Ix.Kernel Ix.Kernel.Reader

private def emptyFamily : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0, ctors := #[] }

private def family (level : Ixon.Univ) : Ixon.Constant :=
  ⟨.muts #[.indc emptyFamily], #[], #[], #[level], #[]⟩

private def address (c : Ixon.Constant) : _root_.Address := _root_.Address.blake3Pure (Ixon.serConstant c)
private def p : Ixon.Constant := family (.succ (.succ (.succ .zero)))
private def q : Ixon.Constant := family (.succ (.succ (.succ (.succ .zero))))
private def projection (c : Ixon.Constant) : Ixon.Constant :=
  ⟨.iPrj { block := address c, idx := 0 }, #[], #[], #[], #[]⟩

private def recType (carrier : Ixon.Expr) : Ixon.Expr :=
  .all (.all carrier (.sort 1)) (.all carrier (.app (.var 1) (.var 0)))

private def recursor (carrier : Ixon.Expr) : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
    motives := 1, minors := 0, typ := recType carrier, rules := #[] }

private def shared (pureRec : Bool) (unsafeFlag : Bool := false) (badK : Bool := false) : Ixon.Constant :=
  let own := if pureRec then #[] else
    #[Ixon.MutConst.indc emptyFamily, .recr (recursor (.recur 0 #[]))]
  ⟨.muts (own ++ #[.recr { recursor (.ref 0 #[]) with isUnsafe := unsafeFlag, k := badK },
    .recr (recursor (.ref 1 #[]))]), #[], #[address (projection p), address (projection q)],
    #[.succ .zero, .var 0], #[]⟩

private def separate (c : Ixon.Constant) : Ixon.Constant :=
  ⟨.recr (recursor (.ref 0 #[])), #[], #[address (projection c)], #[.succ .zero, .var 0], #[]⟩

private def row (c : Ixon.Constant) : _root_.Address × Ixon.Constant := (address c, c)

private def records (pureRec : Bool) (extra : Nat) (unsafeFlag : Bool := false) (badK : Bool := false) :
    Array (_root_.Address × Ixon.Constant) :=
  #[row p, row (projection p)] ++ (if extra > 0 then #[row (separate p)] else #[]) ++
  #[row q, row (projection q)] ++ (if extra > 1 then #[row (separate q)] else #[]) ++
  #[row (shared pureRec unsafeFlag badK)]

private def context (pre : Prelude .anon) (input : Array (_root_.Address × Ixon.Constant)) : Ctx .anon :=
  contextOf { version := specVersion, bound := #[], evidence := #[] } input []
    (pre.records ++ pre.evidence) pre.blobs (fun _ => none)
    (Admission.projectionAddress _root_.Address.blake3Pure)

private def checkOriginal (pureRec : Bool) : Except String Bool := do
  let pre ← (builtinPrelude : Except String (Prelude .anon))
  let input := records pureRec 0
  let cx := context pre input
  match readRecords cx pre.state input with
  | .error _ => pure false
  | .ok (_, decls) => pure (Cached.checkDecls .verified [] (Frontend.preparePrelude pre.ix decls)).isOk

private def readsBare (pureRec : Bool) (extra : Nat) (unsafeFlag : Bool := false) (badK : Bool := false) :
    Except String Bool := do
  let pre ← (builtinPrelude : Except String (Prelude .anon))
  let input := records pureRec extra unsafeFlag badK
  pure (readRecordsBare (context pre input) pre.state input).isOk

private def groupsInOrder (pureRec : Bool) : Except String Bool := do
  let pre ← (builtinPrelude : Except String (Prelude .anon))
  let cx := context pre (records pureRec 2)
  let constant := shared pureRec
  let .muts members := constant.info | pure false
  let first := if pureRec then 0 else 2
  let groups := groupTwins (recordTwins cx.index (address constant) members)
  pure (groups.toList.map (fun group => group.toList.map Prod.fst) ==
    [[.member (address constant) first], [.member (address constant) (first + 1)]])

#guard (checkOriginal false).toOption == some true
#guard (checkOriginal true).toOption == some true
#guard (readsBare false 0).toOption == some true
#guard (readsBare false 1).toOption == some true
#guard (readsBare false 2).toOption == some true
#guard (readsBare true 0).toOption == some true
#guard (readsBare true 1).toOption == some true
#guard (readsBare true 2).toOption == some true
#guard (groupsInOrder false).toOption == some true
#guard (groupsInOrder true).toOption == some true
#guard (readsBare false 2 true).toOption == some false
#guard (readsBare true 2 true).toOption == some false
#guard (readsBare false 2 false true).toOption == some false
#guard (readsBare true 2 false true).toOption == some false

end Tests.Ix.Kernel.ReaderTwinFamilies
