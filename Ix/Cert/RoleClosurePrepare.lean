import IxC.Kernel.Ixon.Prelude
import IxC.Kernel.Admission
import IxC.Kernel.Verify.Cached.Reference
import Ix.Address.Admission

/-! # Preparing a role table's closure (Route A, B6b)

The Ixon entry's reading of a role closure's records under a table, behind a
prelude (`prepareClosure`), and the executed check that it defines every
well-founded `Nat` operation and that the verified fold accepts it
(`closureCheck`). `kernel-pin-gen` runs the check on the closure it pins in
`IxC/Kernel/Ixon/RoleData.lean` before writing it; `Ix.Cert.RoleClosure` states
it on the committed file (`RoleEvidenceChecks`). -/

namespace Ix.Cert.RoleClosure

open Ix.Kernel Ix.Kernel.Reader

/-- A hint from its committed spelling: `opaque`, `abbrev`, or a height. -/
def hintOfString (s : String) : Option ReducibilityHint :=
  if s = "opaque" then some .opaque
  else if s = "abbrev" then some .abbrev
  else ReducibilityHint.regular <$> s.toNat?

/-- The committed spelling of a hint. -/
def hintString : ReducibilityHint → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => toString h

/-- The hint lookup of the closure: a definition block member's hint is its
projection record's, otherwise the record's (as `Ix.Cert.hintsOf` reads an
artifact's). -/
def hintLookup (records : Array (Address × Ixon.Constant)) (hints : Array (Address × ReducibilityHint)) :
    ConstRef Address → Option ReducibilityHint :=
  let projAt : Std.HashMap (ConstRef Address) Address := records.foldl (init := {}) fun m (a, c) =>
    match c.info with
    | .dPrj p => m.insert (.member p.block p.idx.toNat) a
    | _ => m
  let hintAt : Std.HashMap Address ReducibilityHint := hints.foldl (init := {}) fun m (a, h) => m.insert a h
  fun r => hintAt[(projAt[r]?).getD r.block]?

/-- **The prepared closure**: the closure records read by the Ixon entry's
reader under `t`, behind the prelude `pre` (whose state the reading continues
from and whose records and evidence back the store), with the prelude's
declarations in front: the table's evidence resolved against the reading, and
the declarations the fold runs over. -/
def prepareClosure (t : RoleTable) (pre : Prelude .anon) (records : Array (Address × Ixon.Constant))
    (blobs : List (Address × ByteArray)) (hints : Array (Address × ReducibilityHint)) :
    Except String (Evidences .anon × List (Declaration .anon)) :=
  match Admission.readStream Address.admissionHash t pre records.toList blobs (hintLookup records hints) with
  | .ok (ev, decls) => .ok (ev, (Frontend.preparePrelude pre.ix decls).toList)
  | .error e => .error s!"the role closure does not read: {e}"

/-- The declarations define every well-founded `Nat` operation. -/
def DefinesAll (ds : List (Declaration .anon)) : Prop :=
  ∀ k ∈ (natDivModNames : List (Key .anon)), ∃ cv value hint, Declaration.defnDecl cv value hint ∈ ds ∧ cv.name = k

/-- `DefinesAll`, decided. -/
def definesAll (ds : List (Declaration .anon)) : Bool :=
  (natDivModNames : List (Key .anon)).all fun k => ds.any fun
    | .defnDecl cv _ _ => cv.name == k
    | _ => false

theorem definesAll_iff (ds : List (Declaration .anon)) : definesAll ds = true ↔ DefinesAll ds := by
  unfold definesAll DefinesAll
  simp only [List.all_eq_true, List.any_eq_true]
  constructor
  · intro h k present
    obtain ⟨d, member, named⟩ := h k present
    match d, named with
    | .defnDecl cv value hint, named => exact ⟨cv, value, hint, member, by simpa using named⟩
  · intro h k present
    obtain ⟨cv, value, hint, member, named⟩ := h k present
    exact ⟨_, member, by simp [named]⟩

/-- The executed fold over a prepared closure, decided: it defines every
well-founded operation and the verified fold accepts it. -/
def closureCheck (prepared : Except String (Evidences .anon × List (Declaration .anon))) : Bool :=
  match prepared with
  | .ok (ev, ds) => definesAll ds && (Cached.checkDecls .verified ev ds.toArray).isOk
  | .error _ => false

end Ix.Cert.RoleClosure
