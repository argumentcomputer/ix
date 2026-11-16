import IxVMRefinement.Assembly.AdmittedKeys

/-! # Selecting the final reader's physical records

Removing unneeded records preserves their byte provenance and coherent decoding. A kept
reading order retains its exact byte and decoded batches and its literal blobs. This does
not assert index or hint equality for arbitrary removed records.
-/

namespace IxVM.Refinement.Assembly

open IxVM.Consistency

def selectReaderRecords (env : Ixon.Env) (keep : _root_.Address → Bool) : Ixon.Env :=
  { env with consts := env.consts.filter fun address _ => keep address }

theorem selectReaderRecords_get (env : Ixon.Env) (keep : _root_.Address → Bool)
    (address : _root_.Address) :
    (selectReaderRecords env keep).consts.get? address =
      if keep address then env.consts.get? address else none := by
  change (env.consts.filter fun address _ => keep address)[address]? =
    if keep address then env.consts[address]? else none
  by_cases present : address ∈ env.consts
  · rw [Std.HashMap.getElem?_filter_of_getKey?_eq_some (Std.HashMap.getKey?_eq_some_getKey present)]
    have keyEq := eq_of_beq (Std.HashMap.getKey_beq present)
    rw [keyEq]
    cases keep address <;> cases env.consts[address]? <;> rfl
  · have absent : env.consts[address]? = none := Std.HashMap.getElem?_eq_none present
    have filtered : (env.consts.filter fun address _ => keep address)[address]? = none :=
      Std.HashMap.getElem?_eq_none fun found => present (Std.HashMap.mem_of_mem_filter found)
    rw [absent, filtered]
    simp

theorem selectReaderRecords_origin {env : Ixon.Env} {keep : _root_.Address → Bool}
    {address : _root_.Address} {entry : Ixon.LazyConstant}
    (found : (selectReaderRecords env keep).consts.get? address = some entry) :
    keep address = true ∧ env.consts.get? address = some entry := by
  rw [selectReaderRecords_get] at found
  cases kept : keep address with
  | false => simp only [kept, Bool.false_eq_true, ↓reduceIte] at found; cases found
  | true => exact ⟨kept, by simpa only [kept, ↓reduceIte] using found⟩

theorem selectReaderRecords_recordAt (env : Ixon.Env) (keep : _root_.Address → Bool)
    (address : _root_.Address) :
    Ix.Cert.recordAt (selectReaderRecords env keep) address =
      if keep address then Ix.Cert.recordAt env address else none := by
  unfold Ix.Cert.recordAt
  rw [selectReaderRecords_get]
  cases keep address <;> rfl

theorem selectReaderRecords_coherent {env : Ixon.Env} (coherent : ReaderCacheCoherent env)
    (keep : _root_.Address → Bool) : ReaderCacheCoherent (selectReaderRecords env keep) := by
  intro address entry found
  exact coherent address entry (selectReaderRecords_origin found).2

theorem selectReaderRecords_draws {env source : Ixon.Env}
    (draws : IxVM.Refinement.Draws env source) (keep : _root_.Address → Bool) :
    IxVM.Refinement.Draws (selectReaderRecords env keep) source :=
  ⟨fun _ _ found => draws.1 _ _ (selectReaderRecords_origin found).2, draws.2⟩

theorem selectReaderRecords_drawsRole {env source roles : Ixon.Env}
    (draws : DrawsRole env source roles) (keep : _root_.Address → Bool) :
    DrawsRole (selectReaderRecords env keep) source roles :=
  ⟨fun _ _ found => draws.1 _ _ (selectReaderRecords_origin found).2, draws.2⟩

private theorem filterMap_congr_on {α β : Type} {f g : α → Option β} :
    ∀ (items : List α), (∀ item ∈ items, f item = g item) → items.filterMap f = items.filterMap g
  | [], _ => rfl
  | item :: rest, same => by
    simp only [List.filterMap_cons, same item List.mem_cons_self,
      filterMap_congr_on rest (fun x hx => same x (List.mem_cons_of_mem _ hx))]

theorem selectReaderRecords_records (env : Ixon.Env) (keep : _root_.Address → Bool)
    (order : List _root_.Address) (kept : ∀ address ∈ order, keep address = true) :
    Ix.Cert.recordsOf (selectReaderRecords env keep) order = Ix.Cert.recordsOf env order := by
  apply filterMap_congr_on order
  intro address member
  rw [selectReaderRecords_get, kept address member]
  rfl

theorem selectReaderRecords_decoded (env : Ixon.Env) (keep : _root_.Address → Bool)
    (order : List _root_.Address) (kept : ∀ address ∈ order, keep address = true) :
    Ix.Cert.Stream.decodedOf (selectReaderRecords env keep) order = Ix.Cert.Stream.decodedOf env order := by
  apply filterMap_congr_on order
  intro address member
  rw [selectReaderRecords_recordAt, kept address member]
  rfl

theorem selectReaderRecords_blobs (env : Ixon.Env) (keep : _root_.Address → Bool)
    (order : List _root_.Address) (kept : ∀ address ∈ order, keep address = true) :
    Ix.Cert.blobsOf (selectReaderRecords env keep) order = Ix.Cert.blobsOf env order := by
  have folded : ∀ (items : List _root_.Address), (∀ address ∈ items, keep address = true) →
      ∀ (seen : Std.HashSet _root_.Address),
      items.foldl (fun acc address =>
        match Ix.Cert.recordAt (selectReaderRecords env keep) address with
        | some value => value.refs.foldl (·.insert ·) acc
        | none => acc) seen =
      items.foldl (fun acc address =>
        match Ix.Cert.recordAt env address with
        | some value => value.refs.foldl (·.insert ·) acc
        | none => acc) seen := by
    intro items
    induction items with
    | nil => intro _ _; rfl
    | cons address rest ih =>
      intro held seen
      simp only [List.foldl_cons, selectReaderRecords_recordAt, held address List.mem_cons_self, ↓reduceIte]
      exact ih (fun a ha => held a (List.mem_cons_of_mem _ ha)) _
  unfold Ix.Cert.blobsOf
  rw [folded order kept]
  rfl

end IxVM.Refinement.Assembly
