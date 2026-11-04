import Ix.Cert.RoleClosure
import Ix.Cert.ReaderFallback

/-! # The reader's fallback records sit at the hashes of their bytes

The reader's store backs a stream's records with the committed prelude and evidence
records (`Ix.Kernel.Reader.preludeFor`), keyed by the addresses the committed file
states. The pinned configuration's check stores every committed row at the admission
hash of its bytes (`RoleClosure.FallbackHashed`), and every decoded committed record
comes from a row whose bytes decode canonically to it (`decoded_rows`), so every
fallback record sits at the admission hash of its canonical encoding
(`fallback_authentic`). -/

namespace Ix.Cert.FallbackStore

open Ix.Kernel.Reader
open Ix.CompileCert

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, h => by cases h
  | x :: _, _ :: _, .cons head tail, y, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x, List.mem_cons_self .., head⟩
    · obtain ⟨x', hx', r⟩ := forall₂_mem_right tail y h
      exact ⟨x', List.mem_cons_of_mem _ hx', r⟩

/-- **Every decoded committed record comes from a row**: its address and bytes parse,
and its bytes decode canonically to it. -/
theorem decoded_rows (what : String) (raw : Array (String × String))
    {out : Array (Address × Ixon.Constant)} (h : decodeCommitted what raw = .ok out) :
    ∀ e ∈ out.toList, ∃ row ∈ raw.toList, addressOfHex row.1 = some e.1 ∧
      ∃ b, bytesOfHex row.2 = some b ∧
        Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes b = .ok e.2 := by
  unfold decodeCommitted at h
  rw [Array.mapM_eq_mapM_toList] at h
  simp only [Functor.map, Except.map] at h
  split at h
  · cases h
  · rename_i ys hr
    cases h
    intro e he
    obtain ⟨row, hrow, step⟩ := forall₂_mem_right (Loop.mapM_forall₂ _ hr) e (by simpa using he)
    refine ⟨row, hrow, ?_⟩
    cases ha : addressOfHex row.1 with
    | none => simp [ha] at step
    | some a =>
      cases hb : bytesOfHex row.2 with
      | none => simp [ha, hb] at step
      | some bytes =>
        simp only [ha, hb] at step
        obtain ⟨c, decoded, done⟩ := Loop.except_bind_ok.mp step
        cases done
        refine ⟨rfl, bytes, rfl, ?_⟩
        cases hd : Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
        | error err => simp [hd, Except.mapError] at decoded
        | ok c' =>
          simp only [hd, Except.mapError, Except.ok.injEq] at decoded
          rw [decoded]

/-- **Every fallback record sits at the admission hash of its canonical encoding**, under
the pinned configuration's check, and decodes to a wire-valid constant. -/
theorem fallback_authentic (hashed : RoleClosure.FallbackHashed) {md : Ix.Kernel.Mode}
    {t : Ix.Kernel.RoleTable} {pre : Prelude md} (prepared : preludeFor t = .ok pre)
    {a : Address} {c : Ixon.Constant} (mem : (a, c) ∈ pre.records ++ pre.evidence) :
    a = Address.admissionHash (Ixon.serConstant c) ∧ c.wireWF := by
  obtain ⟨records, evidence⟩ := ReaderFallback.preludeFor_records prepared
  have decoded : ∃ row ∈ (RoleData.prelude ++ RoleData.evidence).toList, addressOfHex row.1 = some a ∧
      ∃ b, bytesOfHex row.2 = some b ∧
        Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes b = .ok c := by
    rcases Array.mem_append.mp mem with inRecords | inEvidence
    · obtain ⟨row, hrow, rest⟩ :=
        decoded_rows "prelude" RoleData.prelude records (a, c) (Array.mem_toList_iff.mpr inRecords)
      exact ⟨row, by simp [Array.toList_append, hrow], rest⟩
    · obtain ⟨row, hrow, rest⟩ :=
        decoded_rows "evidence" RoleData.evidence evidence (a, c) (Array.mem_toList_iff.mpr inEvidence)
      exact ⟨row, by simp [Array.toList_append, hrow], rest⟩
  obtain ⟨row, hrow, ha, b, hb, hd⟩ := decoded
  obtain ⟨-, wire, encoded⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hd
  have h := hashed row hrow
  rw [hb, ha] at h
  have h := Option.some.inj h
  refine ⟨?_, wire⟩
  rw [← h, encoded]

end Ix.Cert.FallbackStore
