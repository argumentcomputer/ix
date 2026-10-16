import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Verify.Cached.Reference

/-!
# The certified entry's accept, at the reference level

An accept of the certified entry is an accept of the verified fold on the
reader's declarations behind the prelude (`Installed.reading`), and that is a
reference accept (`Ix.Kernel.Cached.checkDecls_refines_ref`): the pure fold
at some fuel accepts the same declarations with the same environment. The set
theory is a hypothesis of the walk behind it, not of the statement's meaning.
-/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

universe u

/-- **An installed environment is a reference accept** of the reader's
declarations behind the prelude, at the table's evidence. -/
theorem Installed.refines_ref (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : Installed hash t pre constants blobs hint env) :
    ∃ decls st', StreamRead (streamContext hash t pre constants blobs hint) pre.state constants st' decls ∧
      Ix.Kernel.Cached.AcceptsRef .verified (evidenceOf (streamContext hash t pre constants blobs hint) st' t)
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList env := by
  obtain ⟨decls, st', hs, hc⟩ := h.reading
  exact ⟨decls, st', hs, Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc⟩

/-- **The certified entry's accept is a reference accept**, for every hash
and every role table: the binding admits a table `t` with its prelude, the
records decode, and the reader's declarations behind the prelude are a
reference accept of the installed environment. -/
theorem checkBytes_refines_ref (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ t pre constants, admitBinding hash binding = .ok t ∧ preludeFor t = .ok pre ∧
      RecordsRead limits records constants ∧
      ∃ decls st', StreamRead (streamContext hash t pre constants blobs hint) pre.state constants st' decls ∧
        Ix.Kernel.Cached.AcceptsRef .verified (evidenceOf (streamContext hash t pre constants blobs hint) st' t)
          (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList env := by
  obtain ⟨t, pre, ht, hp, -, -, -, constants, -, hread, -, inst⟩ := checkBytes_reading h
  exact ⟨t, pre, constants, ht, hp, hread, inst.refines_ref V⟩

end Ix.Kernel.Admission
