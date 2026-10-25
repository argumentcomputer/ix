import Ix.Cert.DefinitionSnapshots

/-! Actual receipt/snapshot visibility, with no interpretation involved.
The final index supplies positive entries; the actual installation bound
decides whether each is available in this definition's logical prefix.
Source dependency order and whole-source value preservation remain separate. -/
namespace Ix.Cert.PrefixVisibility
open Ix.Kernel Ix.Cert.DefinitionSnapshots

private theorem checked_names {md : Mode} {ev : Evidences md}
    {ds : Array (Declaration md)} {envA : Env md}
    (run : Cached.checkDecls .verified ev ds = .ok envA) : NodupNames envA := by
  obtain ⟨fc, finalEnv⟩ := Cached.checkDecls_fullyChecked .verified run
  obtain ⟨n, s, trace⟩ := fc.1.run
  have chain := (Cached.installRun_trace .verified trace (Cached.PushChain.refl Env.empty)).1
  rw [← finalEnv]
  exact chain.2.2 List.nodup_nil

private theorem snapshot_view {r : Receipt} {i : Nat} {s : Snapshot}
    (run : r.snapshot i = .ok s) : s.view = r.index.restrictTo s.counter := by
  unfold Receipt.snapshot at run
  split at run <;> try simp_all
  split at run <;> try simp_all
  split at run <;> try simp_all
  split at run <;> try simp_all
  simp only [pure, Except.pure, Except.ok.injEq] at run
  cases run
  rfl

/-- Every lookup in the actual definition prefix is the SAME accepted
final index gated at the actual snapshot bound. Neither a model nor a
caller-supplied absence/uniqueness premise is required. -/
theorem snapshot_lookup {binding limits records blobs hints r}
    (accepted : checkReceipt binding limits records blobs hints = .ok r)
    {i : Nat} {s : Snapshot} (snapshot : r.snapshot i = .ok s)
    (key : Key .anon) :
    s.before.find? key =
      match r.index.idx[key]? with
      | some (counter, ci) => if counter < s.counter then some ci else none
      | none => none := by
  obtain ⟨_, _, _, checked, canonical⟩ := checkReceipt_ok accepted
  have names := checked_names checked
  have shape := snapshot_view snapshot
  have before : s.before = r.env.prefixTo s.counter := by
    simp only [Snapshot.before, shape, FEnv.restrictTo, Receipt.env]
  rw [before, ← mkFEnv_find?_visibleBelow r.env s.counter key names, ← canonical]
  dsimp (config := { instances := true }) only [FEnv.find?, FEnv.restrictTo]
  cases r.index.idx[key]? with
  | none => simp only
  | some pair => cases pair; simp only

/-- A positively identified final entry is visible exactly when its
counter precedes the actual current definition. Its kind is unrestricted. -/
theorem snapshot_visible_iff {binding limits records blobs hints r}
    (accepted : checkReceipt binding limits records blobs hints = .ok r)
    {i : Nat} {s : Snapshot} (snapshot : r.snapshot i = .ok s)
    {key : Key .anon} {counter : Nat} {ci : Ix.Kernel.ConstantInfo .anon}
    (entry : r.index.idx[key]? = some (counter, ci)) :
    s.before.find? key = some ci ↔ counter < s.counter := by
  rw [snapshot_lookup accepted snapshot key, entry]
  split <;> simp_all

/-- Actual earlier installation supplies the prefix hit; this is the
condition an ordering producer must derive for a baseline dependency. -/
theorem snapshot_present_of_lt {binding limits records blobs hints r}
    (accepted : checkReceipt binding limits records blobs hints = .ok r)
    {i : Nat} {s : Snapshot} (snapshot : r.snapshot i = .ok s)
    {key : Key .anon} {counter : Nat} {ci : Ix.Kernel.ConstantInfo .anon}
    (entry : r.index.idx[key]? = some (counter, ci)) (earlier : counter < s.counter) :
    s.before.find? key = some ci :=
  (snapshot_visible_iff accepted snapshot entry).mpr earlier

/-- Actual later/current installation derives absence at this prefix,
even though the same key is present in the accepted final index. -/
theorem snapshot_absent_of_ge {binding limits records blobs hints r}
    (accepted : checkReceipt binding limits records blobs hints = .ok r)
    {i : Nat} {s : Snapshot} (snapshot : r.snapshot i = .ok s)
    {key : Key .anon} {counter : Nat} {ci : Ix.Kernel.ConstantInfo .anon}
    (entry : r.index.idx[key]? = some (counter, ci)) (later : s.counter ≤ counter) :
    s.before.find? key = none := by
  rw [snapshot_lookup accepted snapshot key, entry]
  simp only [Nat.not_lt.mpr later, ↓reduceIte]

end Ix.Cert.PrefixVisibility
