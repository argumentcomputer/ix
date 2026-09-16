import Compilatrix.Ixon.V3.Catalog.Load
import Compilatrix.Ixon.V3.Tc.Driver

/-! Catalog-v2 validator 1 certifies erased typing of the authenticated union.
It does not select a resource profile or confer ownership/locality claims. -/

namespace Compilatrix.Ixon.V3.Catalog

structure Admitted (limits : Limits) (manifestBytes : ByteArray)
    (pieceBytes : Array ByteArray) (supplied : Option MemberSets) where
  loaded : Loaded
  sourceLoaded : loadWith limits manifestBytes pieceBytes supplied = .ok loaded
  scopeChecked : loaded.manifest.scopeMatches = true
  rootChecked : loaded.env.root = loaded.manifest.contentRoot
  typingChecked : Tc.checkEnv loaded.env = .ok ()

def admitWith (limits : Limits) (manifestBytes : ByteArray) (pieceBytes : Array ByteArray)
    (supplied : Option MemberSets := none) :
    Except Error (Admitted limits manifestBytes pieceBytes supplied) := do
  match sourceLoaded : loadWith limits manifestBytes pieceBytes supplied with
  | .error error => throw error
  | .ok loaded =>
    if scopeChecked : loaded.manifest.scopeMatches = true then
      if rootChecked : loaded.env.root = loaded.manifest.contentRoot then
        match typingChecked : Tc.checkEnv loaded.env with
        | .error error => throw (.typing error)
        | .ok () => return { loaded, sourceLoaded, scopeChecked, rootChecked, typingChecked }
      else throw (.manifest "union root differs")
    else throw (.scope loaded.manifest.version loaded.manifest.objectFormat loaded.manifest.validator)

def admit (manifestBytes : ByteArray) (pieceBytes : Array ByteArray)
    (supplied : Option MemberSets := none) := admitWith {} manifestBytes pieceBytes supplied

variable {limits : Limits} {manifestBytes : ByteArray} {pieceBytes : Array ByteArray}
  {supplied : Option MemberSets}

theorem Admitted.source_loaded (input : Admitted limits manifestBytes pieceBytes supplied) :
    loadWith limits manifestBytes pieceBytes supplied = .ok input.loaded := input.sourceLoaded

theorem Admitted.scope_checked (input : Admitted limits manifestBytes pieceBytes supplied) :
    input.loaded.manifest.scopeMatches = true := input.scopeChecked

theorem Admitted.content_root (input : Admitted limits manifestBytes pieceBytes supplied) :
    input.loaded.env.root = input.loaded.manifest.contentRoot := input.rootChecked

theorem Admitted.typing_checked (input : Admitted limits manifestBytes pieceBytes supplied) :
    Tc.checkEnv input.loaded.env = .ok () := input.typingChecked

end Compilatrix.Ixon.V3.Catalog
