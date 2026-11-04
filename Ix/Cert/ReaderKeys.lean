import IxC.Kernel.Ixon.ReaderSpec
import IxC.Kernel.Ixon.RoleTableInj

/-! # Reader caches and role keys

Universal facts about the actual cache builders. Reconstruction compatibility
is an internal obligation, scoped to references that emit declarations or side
entries. This module does not discharge that obligation for compiler output or
prove a final target-prefix theorem.
-/

namespace Ix.Cert.ReaderKeys

open Ix.Kernel Ix.Kernel.Reader

variable {md : Mode} {store : Store} {roles : Bindings md}

theorem withKey_address (ks : Keys md store roles) (a : Address) (k : CName md)
    (h : keyOfAddress store roles a = some k) : (ks.withKey a k h).address = ks.address := by
  unfold Keys.withKey
  split <;> rfl

theorem withAddress_byAddress (ks : Keys md store roles) (r : ConstRef Address) (a : Address)
    (h : resolve store a = some r) : (ks.withAddress r a h).byAddress = ks.byAddress := by
  unfold Keys.withAddress
  split <;> rfl

theorem withAddress_keeps (ks : Keys md store roles) (r : ConstRef Address) (a : Address)
    (h : resolve store a = some r) {q : ConstRef Address} {b : Address}
    (hq : ks.address[q]? = some b) : (ks.withAddress r a h).address[q]? = some b := by
  unfold Keys.withAddress
  split
  · exact hq
  · rename_i hn
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i he
      have he : r = q := beq_iff_eq.mp he
      subst q
      exact (hn (by rw [Std.HashMap.contains_eq_isSome_getElem?, hq]; rfl)).elim
    · exact hq

theorem withAddress_origin (ks : Keys md store roles) (r : ConstRef Address) (a : Address)
    (h : resolve store a = some r) {q : ConstRef Address} {b : Address}
    (hq : (ks.withAddress r a h).address[q]? = some b) :
    ks.address[q]? = some b ∨ (q = r ∧ b = a) := by
  unfold Keys.withAddress at hq
  split at hq
  · exact .inl hq
  · rw [Std.HashMap.getElem?_insert] at hq
    split at hq
    · rename_i he
      exact .inr ⟨(beq_iff_eq.mp he).symm, (Option.some.inj hq).symm⟩
    · exact .inl hq

theorem withAddress_has (ks : Keys md store roles) (r : ConstRef Address) (a : Address)
    (h : resolve store a = some r) : ((ks.withAddress r a h).address[r]?).isSome = true := by
  unfold Keys.withAddress
  split
  · rename_i hc
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
    exact hc
  · change ((ks.address.insert r a)[r]?).isSome = true
    rw [Std.HashMap.getElem?_insert]
    simp only [BEq.rfl, ite_true, Option.isSome_some]

theorem withKey_origin (ks : Keys md store roles) (a : Address) (k : CName md)
    (h : keyOfAddress store roles a = some k) {b : Address} {v : CName md}
    (hb : (ks.withKey a k h).byAddress[b]? = some v) :
    ks.byAddress[b]? = some v ∨ b = a := by
  unfold Keys.withKey at hb
  split at hb
  · exact .inl hb
  · rw [Std.HashMap.getElem?_insert] at hb
    split at hb
    · rename_i he
      exact .inr (beq_iff_eq.mp he).symm
    · exact .inl hb

def keyStep (ks : Keys md store roles) (p : Address × Ixon.Constant) : Keys md store roles :=
  let ks := match h : resolve store p.1 with
    | some r => ks.withAddress r p.1 h
    | none => ks
  match h : keyOfAddress store roles p.1 with
  | some k => ks.withKey p.1 k h
  | none => ks

theorem keysOf_eq (records : Array (Address × Ixon.Constant)) :
    keysOf store roles records = records.toList.foldl keyStep {} := by
  unfold keysOf
  rw [← Array.foldl_toList]
  rfl

theorem keyStep_keeps (ks : Keys md store roles) (p : Address × Ixon.Constant)
    {r : ConstRef Address} {a : Address} (h : ks.address[r]? = some a) :
    (keyStep ks p).address[r]? = some a := by
  unfold keyStep
  dsimp only
  split <;> (try rw [withKey_address])
  all_goals
    split
    · exact withAddress_keeps ks _ _ _ h
    · exact h

theorem keyStep_has (ks : Keys md store roles) (p : Address × Ixon.Constant)
    {r : ConstRef Address} (h : resolve store p.1 = some r) :
    ((keyStep ks p).address[r]?).isSome = true := by
  unfold keyStep
  dsimp only
  split <;> (try rw [withKey_address])
  all_goals
    split
    · rename_i q hq
      have he : q = r := Option.some.inj (hq.symm.trans h)
      subst q
      exact withAddress_has ks r p.1 h
    · rename_i hn
      rw [h] at hn
      cases hn

theorem keyStep_address_origin (ks : Keys md store roles) (p : Address × Ixon.Constant)
    {r : ConstRef Address} {a : Address} (h : (keyStep ks p).address[r]? = some a) :
    ks.address[r]? = some a ∨ (a = p.1 ∧ resolve store p.1 = some r) := by
  unfold keyStep at h
  dsimp only at h
  split at h <;> (try rw [withKey_address] at h)
  all_goals
    split at h
    · rename_i q hq
      rcases withAddress_origin ks q p.1 hq h with ho | ⟨rfl, rfl⟩
      · exact .inl ho
      · exact .inr ⟨rfl, hq⟩
    · exact .inl h

theorem keyStep_key_origin (ks : Keys md store roles) (p : Address × Ixon.Constant)
    {a : Address} {k : CName md} (h : (keyStep ks p).byAddress[a]? = some k) :
    ks.byAddress[a]? = some k ∨ a = p.1 := by
  unfold keyStep at h
  dsimp only at h
  split at h
  · rename_i v hv
    split at h
    · rename_i q hq
      have hp := withKey_origin (ks.withAddress q p.1 hq) p.1 v hv h
      simpa only [withAddress_byAddress] using hp
    · exact withKey_origin ks p.1 v hv h
  · split at h
    · exact .inl (by simpa only [withAddress_byAddress] using h)
    · exact .inl h

theorem fold_origin {α σ β : Type} (f : σ → α → σ) (P : σ → β → Prop) (Q : α → β → Prop)
    (step : ∀ s x b, P (f s x) b → P s b ∨ Q x b) :
    ∀ (xs : List α) s b, P (xs.foldl f s) b → P s b ∨ ∃ x ∈ xs, Q x b := by
  intro xs
  induction xs with
  | nil => intro s b h; exact .inl h
  | cons x xs ih =>
    intro s b h
    rcases ih _ b h with h | ⟨y, hy, hq⟩
    · rcases step s x b h with h | h
      · exact .inl h
      · exact .inr ⟨x, List.mem_cons_self, h⟩
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hq⟩

theorem keysOf_address_origin {records : Array (Address × Ixon.Constant)}
    {r : ConstRef Address} {a : Address} (h : (keysOf store roles records).address[r]? = some a) :
    (∃ c, (a, c) ∈ records.toList) ∧ resolve store a = some r := by
  rw [keysOf_eq] at h
  have hi := fold_origin keyStep (fun ks (p : ConstRef Address × Address) => ks.address[p.1]? = some p.2)
    (fun x p => p.2 = x.1 ∧ resolve store x.1 = some p.1)
    (fun s x p h => keyStep_address_origin s x h) records.toList {} (r, a) h
  rcases hi with h | ⟨p, hp, ha, hr⟩
  · simp at h
  · dsimp only at ha hr
    subst a
    exact ⟨⟨p.2, hp⟩, hr⟩

theorem keysOf_key_origin {records : Array (Address × Ixon.Constant)}
    {a : Address} {k : CName md} (h : (keysOf store roles records).byAddress[a]? = some k) :
    ∃ c, (a, c) ∈ records.toList := by
  rw [keysOf_eq] at h
  have hi := fold_origin keyStep (fun ks (p : Address × CName md) => ks.byAddress[p.1]? = some p.2)
    (fun x p => p.1 = x.1) (fun s x p h => keyStep_key_origin s x h)
    records.toList {} (a, k) h
  rcases hi with h | ⟨p, hp, ha⟩
  · simp at h
  · dsimp only at ha
    subst a
    exact ⟨p.2, hp⟩

theorem fold_keys_keeps (xs : List (Address × Ixon.Constant)) (ks : Keys md store roles)
    {r : ConstRef Address} {a : Address} (h : ks.address[r]? = some a) :
    (xs.foldl keyStep ks).address[r]? = some a := by
  induction xs generalizing ks with
  | nil => exact h
  | cons p xs ih => exact ih _ (keyStep_keeps ks p h)

theorem fold_keys_covers (xs : List (Address × Ixon.Constant)) (ks : Keys md store roles)
    {p : Address × Ixon.Constant} {r : ConstRef Address}
    (hp : p ∈ xs) (hr : resolve store p.1 = some r) :
    ∃ a, (xs.foldl keyStep ks).address[r]? = some a := by
  induction xs generalizing ks with
  | nil => cases hp
  | cons q xs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · have hh := keyStep_has ks p hr
      cases ha : (keyStep ks p).address[r]? with
      | none => simp [ha] at hh
      | some a => exact ⟨a, fold_keys_keeps xs _ ha⟩
    · exact ih _ hp

/-- A record that resolves to a reference puts an address for that reference
in the actual cache. The first address may come from another such record. -/
theorem keysOf_covers {records : Array (Address × Ixon.Constant)}
    {a : Address} {c : Ixon.Constant} {r : ConstRef Address}
    (hp : (a, c) ∈ records.toList) (hr : resolve store a = some r) :
    ∃ b, (keysOf store roles records).address[r]? = some b := by
  rw [keysOf_eq]
  exact fold_keys_covers records.toList {} hp hr

def bindingStep (store : Store) (m : Std.HashMap (ConstRef Address) (CName md))
    (p : Role × Address) : Std.HashMap (ConstRef Address) (CName md) :=
  match resolve store p.2 with
  | some ref => if m.contains ref then m else m.insert ref (.role p.1)
  | none => m

theorem bindingsOf_eq (store : Store) (t : RoleTable) :
    (bindingsOf (md := md) store t).names = t.bound.toList.foldl (bindingStep store) {} := by
  unfold bindingsOf
  rw [← Array.foldl_toList]
  rfl

theorem bindingStep_origin (m : Std.HashMap (ConstRef Address) (CName md)) (p : Role × Address)
    {q : ConstRef Address} {r : Role} (h : (bindingStep store m p)[q]? = some (.role r)) :
    m[q]? = some (.role r) ∨ (p.1 = r ∧ resolve store p.2 = some q) := by
  unfold bindingStep at h
  split at h
  · rename_i ref hr
    split at h
    · exact .inl h
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        have he : ref = q := beq_iff_eq.mp he
        have hn : p.1 = r := Key.role.inj (Option.some.inj h)
        exact .inr ⟨hn, hr.trans (congrArg some he)⟩
      · exact .inl h
  · exact .inl h

theorem bindings_role_origin (store : Store) (t : RoleTable)
    {q : ConstRef Address} {r : Role}
    (h : (bindingsOf (md := md) store t).names[q]? = some (.role r)) :
    ∃ a, (r, a) ∈ t.bound.toList ∧ resolve store a = some q := by
  rw [bindingsOf_eq] at h
  have hi := fold_origin (bindingStep store) (fun m q => m[q]? = some (Key.role (md := md) r))
    (fun p q => p.1 = r ∧ resolve store p.2 = some q)
    (fun m p q h => bindingStep_origin m p h) t.bound.toList {} q h
  rcases hi with h | ⟨p, hp, hn, hr⟩
  · simp at h
  · refine ⟨p.2, ?_, hr⟩
    rw [← hn]
    exact hp

/-- One admitted role cannot be assigned to two different references by the
binding fold. This uses role uniqueness, without a hash injectivity claim. -/
theorem bindings_role_inj (store : Store) (t : RoleTable) (checked : t.check = .ok ())
    {q q' : ConstRef Address} {r : Role}
    (h : (bindingsOf (md := md) store t).names[q]? = some (.role r))
    (h' : (bindingsOf (md := md) store t).names[q']? = some (.role r)) : q = q' := by
  obtain ⟨a, ha, hr⟩ := bindings_role_origin store t h
  obtain ⟨b, hb, hr'⟩ := bindings_role_origin store t h'
  have hn : ((t.bound.toList.map Prod.swap).map Prod.snd).Nodup := by
    simpa only [List.map_map, Function.comp_def, Prod.swap] using (RoleTable.check_nodup checked).1
  have he : (a, r) = (b, r) := RoleTable.eq_of_nodup_map_snd hn
    (List.mem_map.mpr ⟨(r, a), ha, rfl⟩) (List.mem_map.mpr ⟨(r, b), hb, rfl⟩) rfl
  have hab : a = b := congrArg Prod.fst he
  rw [hab] at hr
  exact Option.some.inj (hr.symm.trans hr')

theorem singletonAt_resolves {r : ConstRef Address} {a : Address}
    (h : singletonAt store r = some a) : resolve store a = some r := by
  cases r with
  | ctor b i j => simp [singletonAt] at h
  | member b i =>
    cases i with
    | succ i => simp [singletonAt] at h
    | zero =>
      cases hs : store b with
      | none => simp [singletonAt, hs] at h
      | some c =>
        cases hc : c.info <;> simp [singletonAt, hs, hc] at h
        all_goals subst a; simp [resolve, resolveSource, hs, hc]

/-- The remaining reconstruction obligation is needed only for actual emitting
references that are unbound and miss both the address cache and singleton
lookup, when the reconstructed address already has a cached key. It is not a
compiler theorem or a final admission premise. -/
def ReconCompatible (cx : Ctx .anon) (emits : ConstRef Address → Prop) : Prop :=
  ∀ ref a, emits ref → cx.roles.names[ref]? = none → cx.keys.address[ref]? = none →
    singletonAt cx.store ref = none → cx.reconstruct ref = some a →
    (cx.keys.byAddress[a]?).isSome = true → resolve cx.store a = some ref

/-- Cache and singleton hits resolve unconditionally; the internal compatibility
condition is used exactly in the reconstruction/cache-hit branch. -/
theorem addressOf_resolves_of_cached {cx : Ctx .anon} {emits : ConstRef Address → Prop}
    (compatible : ReconCompatible cx emits) {ref : ConstRef Address} {a : Address}
    (emitted : emits ref) (unbound : cx.roles.names[ref]? = none)
    (ha : cx.addressOf ref = .ok a) (cached : (cx.keys.byAddress[a]?).isSome = true) :
    resolve cx.store a = some ref := by
  unfold Ctx.addressOf at ha
  split at ha
  · rename_i b hb
    cases ha
    exact cx.keys.address_sound ref _ hb
  · rename_i missing
    split at ha
    · rename_i b hb
      cases ha
      exact singletonAt_resolves hb
    · rename_i singleton
      split at ha
      · rename_i b hb
        cases ha
        exact compatible ref _ emitted unbound missing singleton hb cached
      · simp [declined, throw, throwThe, MonadExceptOf.throw] at ha

/-- An unbound emitting reference has an input key once its reconstruction
compatibility is supplied. No coverage is demanded for omitted projections. -/
theorem memberKey_unbound {cx : Ctx .anon} {emits : ConstRef Address → Prop}
    (compatible : ReconCompatible cx emits) {ref : ConstRef Address} {k : CName .anon}
    (emitted : emits ref) (unbound : cx.roles.names[ref]? = none)
    (h : cx.memberKey ref = .ok k) : ∃ a, cx.addressOf ref = .ok a ∧ k = .id a := by
  unfold Ctx.memberKey at h
  rw [unbound] at h
  cases ha : cx.addressOf ref with
  | error e => simp [ha, bind, Except.bind] at h
  | ok a =>
    simp only [ha, bind, Except.bind] at h
    cases hk : cx.keys.byAddress[a]? with
    | none =>
      simp only [hk, Mode.addressId?, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨a, rfl, h.symm⟩
    | some v =>
      have hr := addressOf_resolves_of_cached compatible emitted unbound ha (by rw [hk]; rfl)
      have hs := cx.keys.byAddress_sound a v hk
      have hv : v = .id a := by
        simpa [keyOfAddress, hr, unbound, Mode.addressId?] using hs.symm
      simp only [hk, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨a, rfl, h.symm.trans hv⟩

theorem memberKey_role_iff {cx : Ctx .anon} {emits : ConstRef Address → Prop}
    (compatible : ReconCompatible cx emits) {ref : ConstRef Address} {r : Role}
    (emitted : emits ref) :
    cx.memberKey ref = .ok (.role r) ↔ cx.roles.names[ref]? = some (.role r) := by
  constructor
  · intro h
    cases hr : cx.roles.names[ref]? with
    | none =>
      obtain ⟨_, _, impossible⟩ := memberKey_unbound compatible emitted hr h
      cases impossible
    | some k =>
      simp only [Ctx.memberKey, hr, pure, Except.pure, Except.ok.injEq] at h
      rw [h]
  · exact Ctx.memberKey_of_role

end Ix.Cert.ReaderKeys
