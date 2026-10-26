import Ix.Cert.SourceContext.Maps
import Ix.Cert.ReaderClosureKeys
import Ix.CompileCert.Loop
import Ix.CompileCert.PreseedInsertion

namespace Ix.Cert.SourceContext.Rows
open Ix.Kernel Ix.Kernel.Admission Ix.Kernel.Reader Ix.CompileCert.Loop

private theorem bytes_eq (a b : ByteArray) : (a == b) = true ↔ a = b := by
  exact Ix.CompileCert.PreseedInsertion.bytes_beq_iff a b

/-- Existing admission uniqueness, followed by full addressed BYTE equality.
Equal addresses select payloads to compare; they never prove payload equality. -/
def check (before after : Records) : Except ByteError Bool := do
  uniqueKeys before []
  uniqueKeys after []
  pure (Maps.check (· == ·) (Std.HashMap.ofList before) (Std.HashMap.ofList after))

private theorem distinct {α : Type} {rows : List (Address × α)}
    (unique : (rows.map Prod.fst).Nodup) :
    rows.Pairwise (fun a b => (a.1 == b.1) = false) := by
  simpa only [List.Nodup,List.pairwise_map,beq_eq_false_iff_ne] using unique

private theorem index_mem {α : Type} {rows : List (Address × α)}
    (unique : (rows.map Prod.fst).Nodup) {a : Address} {value : α} :
    (Std.HashMap.ofList rows)[a]? = some value ↔ (a,value) ∈ rows := by
  constructor
  · intro found
    have present : (Std.HashMap.ofList rows).contains a = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?,found]
      rfl
    rw [Std.HashMap.contains_ofList,List.contains_iff_mem] at present
    obtain ⟨⟨key,stored⟩,member,same⟩ := List.mem_map.mp present
    dsimp only at same
    subst key
    have own : (Std.HashMap.ofList rows)[a]? = some stored :=
      Std.HashMap.getElem?_ofList_of_mem BEq.rfl (distinct unique) member
    rw [found] at own
    cases own
    exact member
  · intro member
    exact Std.HashMap.getElem?_ofList_of_mem BEq.rfl (distinct unique) member

private theorem pair_nodup {α : Type} {rows : List (Address × α)}
    (unique : (rows.map Prod.fst).Nodup) : rows.Nodup :=
  unique.of_map Prod.fst (fun _a _b different same => different (congrArg Prod.fst same))

/-- Success preserves every original (address,bytes) row, with multiplicity,
and retains the existing unique-key obligation on both actual input lists. -/
theorem check_sound {before after : Records} (accepted : check before after = .ok true) :
    (before.map Prod.fst).Nodup ∧ (after.map Prod.fst).Nodup ∧ before.Perm after := by
  unfold check at accepted
  obtain ⟨⟨⟩,first,rest⟩ := except_bind_ok.mp accepted
  obtain ⟨⟨⟩,second,done⟩ := except_bind_ok.mp rest
  have left := ((uniqueKeys_ok_iff before []).mp first).1
  have right := ((uniqueKeys_ok_iff after []).mp second).1
  have checked : Maps.check (· == ·) (Std.HashMap.ofList before) (Std.HashMap.ofList after) = true := by
    simpa only [pure,Except.pure,Except.ok.injEq] using done
  have agrees := Maps.check_sound (fun a b h => (bytes_eq a b).mp h) checked
  refine ⟨left,right,(List.perm_ext_iff_of_nodup (pair_nodup left) (pair_nodup right)).mpr ?_⟩
  rintro ⟨a,bytes⟩
  constructor
  · intro member
    exact (index_mem right).mp ((agrees a).symm.trans ((index_mem left).mpr member))
  · intro member
    exact (index_mem left).mp ((agrees a).trans ((index_mem right).mpr member))

theorem check_complete {before after : Records} (unique : (before.map Prod.fst).Nodup)
    (same : before.Perm after) : check before after = .ok true := by
  have nextUnique := (same.map Prod.fst).nodup unique
  have agree : Maps.Agrees (Std.HashMap.ofList before) (Std.HashMap.ofList after) := by
    intro a
    cases old : (Std.HashMap.ofList before)[a]? with
    | some bytes => exact ((index_mem nextUnique).mpr (same.mem_iff.mp ((index_mem unique).mp old))).symm
    | none =>
      cases next : (Std.HashMap.ofList after)[a]? with
      | none => rfl
      | some bytes =>
        have hit := (index_mem unique).mpr (same.mem_iff.mpr ((index_mem nextUnique).mp next))
        rw [old] at hit
        cases hit
  have equal := Maps.check_complete (fun bytes => (bytes_eq bytes bytes).mpr rfl) agree
  rw [check,(uniqueKeys_ok_iff before []).mpr ⟨unique,List.nodup_nil⟩]
  simp only [bind,Except.bind]
  rw [(uniqueKeys_ok_iff after []).mpr ⟨nextUnique,List.nodup_nil⟩]
  simpa only [bind,Except.bind,pure,Except.pure] using congrArg Except.ok equal

/-- Reordering actual byte rows reorders their canonical readings. This uses
the reader relation directly, with no address/hash injectivity assumption. -/
theorem reads_permute {limits : Limits} {before after : Records} (same : before.Perm after) :
    ∀ {old}, RecordsRead limits before old → ∃ next, RecordsRead limits after next ∧ old.Perm next := by
  induction same with
  | nil => intro old read; cases read; exact ⟨[],.nil,.nil⟩
  | cons row permutation ih =>
    intro old read
    cases read with
    | cons head tail =>
      obtain ⟨next,reads,perm⟩ := ih tail
      exact ⟨_,.cons head reads,.cons _ perm⟩
  | swap a b tail =>
    intro old read
    cases read with
    | cons first rest => cases rest with
      | cons second tailRead => exact ⟨_,.cons second (.cons first tailRead),.swap ..⟩
  | trans first second ihFirst ihSecond =>
    intro old read
    obtain ⟨middle,middleRead,firstPerm⟩ := ihFirst read
    obtain ⟨next,nextRead,secondPerm⟩ := ihSecond middleRead
    exact ⟨next,nextRead,firstPerm.trans secondPerm⟩

theorem decoded_permute {limits : Limits} {before after : Records}
    {old next : Ingress.Constants} (same : before.Perm after)
    (first : decodeRecords limits before = .ok old) (second : decodeRecords limits after = .ok next) :
    old.Perm next := by
  obtain ⟨other,read,permutation⟩ := reads_permute same ((decodeRecords_ok_iff ..).mp first)
  have equal := read.deterministic ((decodeRecords_ok_iff ..).mp second)
  exact equal ▸ permutation

theorem decode_success_of_permute {limits : Limits} {before after : Records}
    {old : Ingress.Constants} (same : before.Perm after)
    (first : decodeRecords limits before = .ok old) :
    ∃ next, decodeRecords limits after = .ok next ∧ old.Perm next := by
  obtain ⟨next,read,permutation⟩ := reads_permute same ((decodeRecords_ok_iff ..).mp first)
  exact ⟨next,(decodeRecords_ok_iff ..).mpr read,permutation⟩

end Ix.Cert.SourceContext.Rows
