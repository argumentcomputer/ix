import Ix.Cert.Composition
import Ix.Cert.FallbackStore
import Ix.Cert.RecordHeaders
import Ix.Cert.ReaderKeys
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.ReaderUnits

/-! # The reader keys every representative as its renaming

In the reading context of an accepted compiled closure (`admissionContext`), a
quotient Source constant that reads, reads as its key renamed to the artifact's
addresses (`evAddr`), at its own level parameters (`readingAt_renamed`).

* **The store is authentic.** The reader's store holds the stream's decoded records,
  each at the admission hash of its canonical bytes (authentication and canonical
  decoding), behind the committed fallback, which the pinned configuration's check
  stores the same way (`RoleClosure.FallbackHashed`, `FallbackStore.fallback_authentic`).
* **Resolution is injective on it** (`resolve_inj`). A singleton resolves to itself, and
  a projection to its block's member, whose kind fixes the projection; so two addresses
  that resolve alike hold one constant, and sit at its one hash.
* **So the role bindings key a reference by the role bound at its own address**
  (`bindings_bound`, `bindings_unbound`): the table binds each address once.
* **Quotient Source names agree**: a representative's address is bound in the table
  exactly when it is a role key (`QRepAt` under the table rule, `qrepAt_unbound`), and
  the default table is the admitted one (`admitBinding_default`).

A quotient constant whose key sits at a closure constant's published address reads
(`readingAt_isSome_stored`, `readingAt_isSome_at`): the published key is an input name, the
readability check of `compileReport` (`publishedReadable`) stores its record as no block, the
record seeds the compiled closure, and the stream reads it, so it resolves.
`admissionContext` comes from the accepted preparation (`prepareWith_stages`). -/

namespace Ix.Cert.ReadingKeys

open Ix.Kernel Ix.Kernel.Reader

/-! ## The default table is the admitted one -/

/-- **The default binding admits as the default table.** The committed bytes are
abstracted first, so that no proof step evaluates them. -/
theorem admitBinding_default {t tA : RoleTable} {binding : Admission.Binding} {hash : ByteArray → Address}
    (table : defaultTable = .ok t) (hb : Admission.defaultBinding = .ok binding)
    (admitted : Admission.admitBinding hash binding = .ok tA) : tA = t := by
  unfold Admission.defaultBinding at hb
  unfold defaultTable at table
  generalize defaultTableBytes = bytesE at hb table
  generalize defaultTableAddress = addrE at hb
  cases bytesE with
  | error e => simp [bind, Except.bind] at table
  | ok bytes =>
    cases addrE with
    | error e => simp [bind, Except.bind] at hb
    | ok addr =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      simp only [bind, Except.bind] at table
      unfold Admission.admitBinding at admitted
      cases hT : RoleTable.ofBytes bytes with
      | none => simp [hT, throw, throwThe, MonadExceptOf.throw] at table
      | some t₀ =>
        simp only [hT] at table admitted
        cases hc : t₀.check with
        | error e => simp [hc, Except.mapError] at table
        | ok u =>
          simp only [hc, Except.mapError, pure, Except.pure, Except.ok.injEq] at table
          subst table
          split at admitted
          all_goals first
            | (simp [hc, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe,
                MonadExceptOf.throw] at admitted; done)
            | (simp [hc, Except.mapError, bind, Except.bind, pure, Except.pure] at admitted
               exact admitted.symm)

/-! ## The accepted preparation's stages -/

/-- **An accepted preparation passed each stage**: unique keys, authentication, the
table's admission, canonical decoding and the reading. -/
theorem prepareWith_stages {hash : ByteArray → Address} {binding : Admission.Binding} {pre : Prelude .anon}
    {limits : Admission.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ReducibilityHint} {ev : Evidences .anon}
    {ds : Array (Declaration .anon)}
    (h : Admission.prepareWith hash binding pre limits records blobs hint = .ok (ev, ds)) :
    ∃ t constants decls, Admission.UniqueKeys records blobs ∧ Admission.Authentic hash records blobs ∧
      Admission.admitBinding hash binding = .ok t ∧ Admission.decodeRecords limits records = .ok constants ∧
      Admission.readStream hash t pre constants blobs hint = .ok (ev, decls) ∧
      ds = Frontend.preparePrelude pre.ix decls := by
  unfold Admission.prepareWith at h
  cases hf : Admission.preflight limits records blobs with
  | error e => simp [hf, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases hu : Admission.uniqueKeys records blobs with
    | error e => simp [hf, hu, Except.mapError, bind, Except.bind] at h
    | ok v =>
      cases ha : Admission.authenticate hash records blobs with
      | error e => simp [hf, hu, ha, Except.mapError, bind, Except.bind] at h
      | ok w =>
        cases hb : Admission.admitBinding hash binding with
        | error e => simp [hf, hu, ha, hb, Except.mapError, bind, Except.bind] at h
        | ok t =>
          cases hd : Admission.decodeRecords limits records with
          | error e => simp [hf, hu, ha, hb, hd, Except.mapError, bind, Except.bind] at h
          | ok constants =>
            cases hs : Admission.readStream hash t pre constants blobs hint with
            | error e => simp [hf, hu, ha, hb, hd, hs, Except.mapError, bind, Except.bind] at h
            | ok pair =>
              obtain ⟨ev', decls⟩ := pair
              simp only [hf, hu, ha, hb, hd, hs, Except.mapError, bind, Except.bind, pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨t, constants, decls, (Admission.uniqueKeys_ok_iff _ _).mp hu,
                (Admission.authenticate_ok_iff _ _ _).mp ha, rfl, rfl, hs, rfl⟩

/-! ## The store -/

theorem lookup_mem : ∀ {xs : List (Address × Ixon.Constant)} {a : Address} {c : Ixon.Constant},
    xs.lookup a = some c → (a, c) ∈ xs
  | [], _, _, h => by cases h
  | (k, v) :: xs, a, c, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      rw [beq_iff_eq.mp he]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A record the reader's store holds is a stream record or a fallback record. -/
theorem context_store {hash : ByteArray → Address} {t : RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ReducibilityHint} {a : Address} {c : Ixon.Constant}
    (h : (Admission.streamContext hash t pre constants blobs hint).store a = some c) :
    (a, c) ∈ constants ∨ (a, c) ∈ pre.records ++ pre.evidence := by
  change ((recordMap constants.toArray)[a]? <|> ((recordMap (pre.records ++ pre.evidence))[a]? <|> none)) =
    some c at h
  rw [ReaderClosureKeys.recordMap_get, ReaderClosureKeys.recordMap_get] at h
  cases hs : constants.toArray.toList.lookup a with
  | some c' =>
    rw [hs] at h
    cases h
    exact .inl (by simpa using lookup_mem hs)
  | none =>
    rw [hs] at h
    cases hf : (pre.records ++ pre.evidence).toList.lookup a with
    | some c' =>
      rw [hf] at h
      cases h
      exact .inr (Array.mem_toList_iff.mp (lookup_mem hf))
    | none => rw [hf] at h; cases h

/-- **The reader's store is authentic**: every record it holds sits at the admission hash
of its canonical bytes. -/
theorem context_authentic (hashed : RoleClosure.FallbackHashed) {tA : RoleTable} {pre : Prelude .anon}
    (prelude : preludeFor tA = .ok pre) {limits : Admission.Limits} {records : Admission.Records}
    {constants : List (Address × Ixon.Constant)} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ReducibilityHint}
    (authentic : Admission.Authentic Address.admissionHash records blobs)
    (decoded : Admission.RecordsRead limits records constants) {a : Address} {c : Ixon.Constant}
    (h : (Admission.streamContext Address.admissionHash tA pre constants blobs hint).store a = some c) :
    a = Address.admissionHash (Ixon.serConstant c) := by
  rcases context_store h with stream | fallback
  · exact decoded.hashed authentic.1 (a, c) stream
  · exact (FallbackStore.fallback_authentic hashed prelude fallback).1

/-! ## Resolution is injective on an authentic store -/

/-- The member a store's block holds at a position. -/
def memberAt (store : Store) (b : Address) (i : Nat) : Option Ixon.MutConst := do
  let blk ← store b
  let .muts ms := blk.info | none
  ms[i]?

/-- **The one projection record that resolves to a reference**: the member's
projection of its kind, or the constructor's, with empty tables. -/
def projectionAt (store : Store) : ConstRef Address → Option Ixon.Constant
  | .member b i =>
    match memberAt store b i with
    | some (.defn _) => some ⟨.dPrj ⟨i.toUInt64, b⟩, #[], #[], #[]⟩
    | some (.indc _) => some ⟨.iPrj ⟨i.toUInt64, b⟩, #[], #[], #[]⟩
    | some (.recr _) => some ⟨.rPrj ⟨i.toUInt64, b⟩, #[], #[], #[]⟩
    | none => none
  | .ctor b i j => some ⟨.cPrj ⟨i.toUInt64, j.toUInt64, b⟩, #[], #[], #[]⟩

theorem empty_constant {c : Ixon.Constant} (h : emptyTables c = true) :
    c = ⟨c.info, #[], #[], #[]⟩ := by
  obtain ⟨i, s, r, u⟩ := c
  simp only [emptyTables, Bool.and_eq_true, Array.isEmpty_iff] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

/-- **What a successful resolution fixes**: a singleton resolves to itself, and any
other record is the one projection record of the reference it resolves to. -/
theorem resolveSource_cases {store : Store} {a : Address} {c : Ixon.Constant} {q : ConstRef Address}
    (h : resolveSource store a c = some q) :
    (q = .member a 0 ∧ ∀ ms, c.info ≠ .muts ms) ∨ projectionAt store q = some c := by
  unfold resolveSource at h
  cases kind : c.info with
  | defn _ | recr _ | axio _ | quot _ =>
    rw [kind] at h
    cases h
    exact .inl ⟨rfl, fun ms e => by cases e⟩
  | muts _ => rw [kind] at h; cases h
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    rw [kind] at h
    simp only [Option.bind_eq_bind] at h
    obtain ⟨_, hg, h⟩ := Option.bind_eq_some_iff.mp h
    have tables : emptyTables c = true := by
      cases he : emptyTables c with
      | true => rfl
      | false => simp [he, guard, failure] at hg
    have hc := empty_constant tables
    rw [kind] at hc
    obtain ⟨blk, hblk, h⟩ := Option.bind_eq_some_iff.mp h
    cases binfo : blk.info with
    | muts ms =>
      simp only [binfo] at h
      obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
      have at_ : memberAt store p.block p.idx.toNat = some m := by
        simp [memberAt, hblk, binfo, hm]
      right
      cases m with
      | defn d =>
        first
          | (cases h; simp only [projectionAt, at_, UInt64.ofNat_toNat]; rw [hc])
          | (simp at h; done)
      | indc d =>
        first
          | (cases h; simp only [projectionAt, at_, UInt64.ofNat_toNat]; rw [hc])
          | (simp at h; done)
          | (obtain ⟨ctor, _, h⟩ := Option.bind_eq_some_iff.mp h
             obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
             cases h
             simp only [projectionAt, UInt64.ofNat_toNat]
             rw [hc])
      | recr d =>
        first
          | (cases h; simp only [projectionAt, at_, UInt64.ofNat_toNat]; rw [hc])
          | (simp at h; done)
    | _ => simp [binfo] at h

/-- A block's member is never at an address that holds no block. -/
theorem memberAt_block {store : Store} {b : Address} {i : Nat} {m : Ixon.MutConst} {x : Ixon.Constant}
    (hx : store b = some x) (hnot : ∀ ms, x.info ≠ .muts ms) : memberAt store b i ≠ some m := by
  intro hm
  simp only [memberAt, hx, Option.bind_eq_bind, Option.bind_some] at hm
  cases hi : x.info with
  | muts ms => exact hnot ms hi
  | _ => simp at hm

/-- A projection record that resolves to a member holds a block at its block's address. -/
theorem projectionAt_member {store : Store} {b : Address} {i : Nat} {c : Ixon.Constant}
    (h : projectionAt store (.member b i) = some c) : ∃ m, memberAt store b i = some m := by
  simp only [projectionAt] at h
  split at h
  all_goals first | (cases h; done) | exact ⟨_, ‹_›⟩

/-- **Resolution is injective on an authentic store**: two addresses that resolve to one
reference are one address. -/
theorem resolve_inj {store : Store}
    (authentic : ∀ a c, store a = some c → a = Address.admissionHash (Ixon.serConstant c))
    {a a' : Address} {q : ConstRef Address} (h : resolve store a = some q) (h' : resolve store a' = some q) :
    a = a' := by
  unfold resolve at h h'
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h'
  rcases resolveSource_cases h with ⟨rfl, ns⟩ | proj <;>
    rcases resolveSource_cases h' with ⟨e, ns'⟩ | proj'
  · simpa using e
  · obtain ⟨m, hm⟩ := projectionAt_member proj'
    exact absurd hm (memberAt_block hc ns)
  · subst e
    obtain ⟨m, hm⟩ := projectionAt_member proj
    exact absurd hm (memberAt_block hc' ns')
  · rw [proj] at proj'
    cases proj'
    rw [authentic a c hc, authentic a' c hc']

/-! ## The role bindings -/

theorem bindingStep_keeps {store : Store} (m : Std.HashMap (ConstRef Address) (CName .anon))
    (p : Role × Address) {q : ConstRef Address} {v : CName .anon} (h : m[q]? = some v) :
    (ReaderKeys.bindingStep store m p)[q]? = some v := by
  unfold ReaderKeys.bindingStep
  split
  · split
    · exact h
    · rename_i ref _ hn
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i he
        have : ref = q := beq_iff_eq.mp he
        subst this
        exact absurd (by rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl) hn
      · exact h
  · exact h

theorem bindingStep_has {store : Store} (m : Std.HashMap (ConstRef Address) (CName .anon))
    (p : Role × Address) {q : ConstRef Address} (hq : resolve store p.2 = some q) :
    ((ReaderKeys.bindingStep store m p)[q]?).isSome = true := by
  unfold ReaderKeys.bindingStep
  rw [hq]
  dsimp only
  split
  · rename_i hc
    rwa [Std.HashMap.contains_eq_isSome_getElem?] at hc
  · simp

theorem fold_keeps {store : Store} :
    ∀ (l : List (Role × Address)) (m : Std.HashMap (ConstRef Address) (CName .anon)) {q : ConstRef Address}
      {v : CName .anon}, m[q]? = some v → (l.foldl (ReaderKeys.bindingStep store) m)[q]? = some v
  | [], _, _, _, h => h
  | p :: l, m, _, _, h => fold_keeps l _ (bindingStep_keeps m p h)

theorem fold_has {store : Store} :
    ∀ (l : List (Role × Address)) (m : Std.HashMap (ConstRef Address) (CName .anon)) {p : Role × Address}
      {q : ConstRef Address}, p ∈ l → resolve store p.2 = some q →
        ((l.foldl (ReaderKeys.bindingStep store) m)[q]?).isSome = true
  | [], _, _, _, h, _ => by cases h
  | p' :: l, m, p, q, h, hq => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (bindingStep_has (store := store) m p hq)
      rw [fold_keeps l _ hv]
      rfl
    · exact fold_has l _ h hq

/-- **A bound address keys its reference by its own role**, when no other bound address
resolves to the same reference. -/
theorem bindings_bound {store : Store} {t : RoleTable} (checked : t.check = .ok ()) {r : Role} {a : Address}
    {q : ConstRef Address} (hmem : (r, a) ∈ t.bound.toList) (hq : resolve store a = some q)
    (inj : ∀ a', resolve store a' = some q → a' = a) :
    (bindingsOf (md := .anon) store t).names[q]? = some (.role r) := by
  have has : ((bindingsOf (md := .anon) store t).names[q]?).isSome = true := by
    rw [ReaderKeys.bindingsOf_eq]
    exact fold_has _ _ hmem hq
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp has
  obtain ⟨r', rfl⟩ := ReaderUnits.bindingsOf_keyed store t q k hk
  obtain ⟨a', hmem', hq'⟩ := ReaderKeys.bindings_role_origin store t hk
  have ha := inj a' hq'
  subst ha
  have he := RoleTable.eq_of_nodup_map_snd (RoleTable.check_nodup checked).2 hmem hmem' rfl
  cases he
  exact hk

/-- **An address the table does not bind keys no role**, when no bound address resolves to
its reference. -/
theorem bindings_unbound {store : Store} {t : RoleTable} {q : ConstRef Address} {a : Address}
    (unbound : ∀ r, (r, a) ∉ t.bound.toList)
    (inj : ∀ a', resolve store a' = some q → a' = a) :
    (bindingsOf (md := .anon) store t).names[q]? = none := by
  cases hk : (bindingsOf (md := .anon) store t).names[q]? with
  | none => rfl
  | some k =>
    obtain ⟨r', rfl⟩ := ReaderUnits.bindingsOf_keyed store t q k hk
    obtain ⟨a', hmem', hq'⟩ := ReaderKeys.bindings_role_origin store t hk
    exact absurd (inj a' hq' ▸ hmem') (unbound r')

/-! ## Quotient Source's keys at the table -/

theorem eq_of_nodup_map_fst {α β : Type} :
    ∀ {l : List (α × β)} {p q : α × β}, (l.map (·.1)).Nodup → p ∈ l → q ∈ l → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => nomatch hp
  | x :: l, p, q, hn, hp, hq, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hp with hpx | hpl <;> rcases List.mem_cons.mp hq with hqx | hql
    · rw [hpx, hqx]
    · subst hpx; exact absurd ⟨q, hql, he.symm⟩ hn.1
    · subst hqx; exact absurd ⟨p, hpl, he⟩ hn.1
    · exact eq_of_nodup_map_fst hn.2 hpl hql he

/-- The address a table binds a role to is bound to it. -/
theorem bound_of_addressOf {t : RoleTable} {r : Role} {a : Address} (h : t.addressOf? r = some a) :
    (r, a) ∈ t.bound.toList := by
  unfold RoleTable.addressOf? at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hr : p.1 = r := by simpa using Array.find?_some hp
  have hm := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hp)
  rw [← hr]
  exact hm

/-- An address bound to a role is the table's address for it. -/
theorem addressOf_of_bound {t : RoleTable} (checked : t.check = .ok ()) {r : Role} {a : Address}
    (h : (r, a) ∈ t.bound.toList) : t.addressOf? r = some a := by
  unfold RoleTable.addressOf?
  cases hf : t.bound.find? (·.1 == r) with
  | none =>
    have := Array.find?_eq_none.mp hf (r, a) (Array.mem_toList_iff.mp h)
    simp at this
  | some p =>
    have hr : p.1 = r := by simpa using Array.find?_some hf
    have hm := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hf)
    have he := eq_of_nodup_map_fst (RoleTable.check_nodup checked).1 hm h hr
    simp [he]

/-- **A representative under the table rule sits at an address the table does not bind.** -/
theorem qrepAt_unbound {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    (bound : Ix.LeanIngress.TableBound ixe roles) {n : Ix.Kernel.Name} (rep : Ix.LeanIngress.QRepAt ixe roles n)
    {a : Address} (ha : (Ix.LeanIngress.sourceAddrs ixe)[n]? = some a) : roles[a]? = none := by
  obtain ⟨⟨noRole, -⟩, fixed⟩ := rep
  cases hr : roles[a]? with
  | none => rfl
  | some r =>
    exfalso
    have hrep : Ix.LeanIngress.repAt roles[a]?
        (Ix.LeanIngress.fiberRep ((Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD a []),
          ((Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD a []).filterMap
            Ix.LeanIngress.roleOf) = some (.role r) := by
      have hall : (((Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD a []).filterMap
          Ix.LeanIngress.roleOf).all (fun r' => decide (r' = r)) = true := by
        refine List.all_eq_true.mpr fun r' hr' => ?_
        obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hr'
        have := bound x r' a (Ix.LeanIngress.mem_fiberMembers.mp hx) hxr
        rw [hr] at this
        simp only [Option.some.injEq] at this
        exact decide_eq_true this.symm
      rw [hr]
      simp only [Ix.LeanIngress.repAt, hall, ↓reduceIte]
    have subst := Ix.LeanIngress.fiberAliasAt_subst ha hrep
    rw [Ix.LeanIngress.roleOf_eq_none noRole, fixed] at subst
    cases subst

/-- **The renaming of a representative is its address.** -/
theorem evAddr_published {ixe : Ixon.Env} {b : Ix.RoleEvidence.Bundle} {n : Ix.Kernel.Name} {a : Address}
    (ha : (Ix.LeanIngress.sourceAddrs ixe)[n]? = some a) : Ix.LeanIngress.evAddr ixe b n = a := by
  simp [Ix.LeanIngress.evAddr, ha]

/-! ## The reading -/

/-- The accepted run's reading context and what it rests on. -/
structure Accepted (binding : Admission.Binding) (limits : Admission.Limits) (ixe : Ixon.Env)
    (order : List Address) (tA : RoleTable) (pre : Prelude .anon) (constants : List (Address × Ixon.Constant))
    (cx : Ctx .anon) : Prop where
  admitted : Admission.admitBinding Address.admissionHash binding = .ok tA
  prelude : preludeFor tA = .ok pre
  authentic : Admission.Authentic Address.admissionHash (recordsOf ixe order) (blobsOf ixe order)
  unique : Admission.UniqueKeys (recordsOf ixe order) (blobsOf ixe order)
  decoded : Admission.RecordsRead limits (recordsOf ixe order) constants
  context : cx = Admission.streamContext Address.admissionHash tA pre constants (blobsOf ixe order) (hintsOf ixe)
  reads : ∃ st' decls, StreamRead cx pre.state constants st' decls
  admission : admissionContext binding limits ixe order = some cx

/-- **The admission context is the stream's reading context** at the admitted table,
the prelude and the decoded records. -/
theorem admissionContext_eq {binding : Admission.Binding} {limits : Admission.Limits} {ixe : Ixon.Env}
    {order : List Address} {tA : RoleTable} {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    (admitted : Admission.admitBinding Address.blake3Pure binding = .ok tA) (prelude : preludeFor tA = .ok pre)
    (decoded : Admission.decodeRecords limits (recordsOf ixe order) = .ok constants) :
    admissionContext binding limits ixe order =
      some (Admission.streamContext Address.blake3Pure tA pre constants (blobsOf ixe order) (hintsOf ixe)) := by
  -- rewritten step by step: a definitional comparison of the unfolded forms would make the
  -- kernel evaluate the committed prelude behind `preludeFor`
  have unfolded : admissionContext binding limits ixe order =
      (Admission.admitBinding Address.blake3Pure binding).toOption.bind fun t =>
        (preludeFor t : Except String (Prelude .anon)).toOption.bind fun pre =>
          (Admission.decodeRecords limits (recordsOf ixe order)).toOption.bind fun constants =>
            some (Admission.streamContext Address.blake3Pure t pre constants (blobsOf ixe order)
              (hintsOf ixe)) := rfl
  have h₁ : (Admission.admitBinding Address.blake3Pure binding).toOption = some tA := by rw [admitted]; rfl
  have h₂ : (preludeFor tA : Except String (Prelude .anon)).toOption = some pre := by rw [prelude]; rfl
  have h₃ : (Admission.decodeRecords limits (recordsOf ixe order)).toOption = some constants := by
    rw [decoded]; rfl
  rw [unfolded, h₁, Option.bind_some, h₂, Option.bind_some, h₃, Option.bind_some]

/-- **The accepted run's reading context** is the admission context. -/
theorem accepted {binding : Admission.Binding} {limits : Admission.Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (acc : IxonAcceptsRef binding limits ixe S order envA) :
    ∃ tA pre constants cx, Accepted binding limits ixe order tA pre constants cx := by
  obtain ⟨-, tA, pre, ev, ds, admitted, prelude, prepared, -⟩ := acc
  obtain ⟨t', constants, decls, unique, authentic, admitted', decoded, read, -⟩ := prepareWith_stages prepared
  rw [admitted] at admitted'
  cases admitted'
  obtain ⟨st', reads, -, -⟩ := Admission.readStream_spec read
  have admitted₀ := admitted
  rw [Address.admissionHash_eq] at admitted₀
  have context := admissionContext_eq admitted₀ prelude decoded
  rw [← Address.admissionHash_eq] at context
  exact ⟨tA, pre, constants, _, admitted, prelude, authentic, unique,
    (Admission.decodeRecords_ok_iff _ _ _).mp decoded, rfl, ⟨st', _, reads⟩, context⟩

/-- The key a reading at the table reads a quotient constant by, at the address its key
sits at. -/
theorem readingAt_eq {ixe : Ixon.Env} {t : RoleTable} {cx : Ctx .anon} {c : Ix.Kernel.ConstantInfo .source}
    {e : Ix.Kernel.Expr .anon} (h : readingAt ixe t cx c = some e) :
    ∃ a k, keyAddress ixe t c.name = some a ∧ cx.keyAt a = .ok k ∧
      e = .const k (c.toConstantVal.levelParams.map .param) := by
  unfold readingAt at h
  cases hk : keyAddress ixe t c.name with
  | none => simp [hk] at h
  | some a =>
    cases hkey : cx.keyAt a with
    | error err => simp [hk, hkey, Except.toOption] at h
    | ok k =>
      simp only [hk, hkey, Except.toOption, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨a, k, rfl, hkey, h.symm⟩

/-- **The reading at the table keys a quotient constant by its renaming.** -/
theorem readingAt_renamed {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {binding : Admission.Binding}
    (hbind : Admission.defaultBinding = .ok binding) {limits : Admission.Limits} {order : List Address}
    {tA : RoleTable} {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)} {cx : Ctx .anon}
    (A : Accepted binding limits ixe order tA pre constants cx) {b : Ix.RoleEvidence.Bundle}
    (hb : Ix.RoleEvidence.quotientBundle () = .ok b) :
    ∀ c ∈ envQ.consts, ∀ e, readingAt ixe t cx c = some e →
      e = .const (c.name.map (Ix.LeanIngress.evAddr ixe b)) (c.toConstantVal.levelParams.map .param) := by
  have checked := defaultTable_check P.table
  have same : tA = t := admitBinding_default P.table hbind A.admitted
  subst same
  have tableBound := tableBound_of checked P.bound
  -- the renamed quotient run relates every constant's key
  obtain ⟨-, preS, ds, -, prepared, run⟩ := P.source
  obtain ⟨b', hb', envR, -, rel⟩ :=
    Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt .verified tableBound prepared run
  rw [hb] at hb'
  cases hb'
  -- the store is authentic, so resolution is injective
  have auth : ∀ a c, cx.store a = some c → a = Address.admissionHash (Ixon.serConstant c) := by
    intro a c h
    rw [A.context] at h
    exact context_authentic P.evidence.2.1 A.prelude A.authentic A.decoded h
  have roles : cx.roles = bindingsOf cx.store tA := by
    rw [A.context]
    rfl
  intro c hc e he
  obtain ⟨a, k, hk, hkey, rfl⟩ := readingAt_eq he
  obtain ⟨q, hq, hkeyed⟩ := Ctx.keyAt_ok hkey
  have inj : ∀ a', resolve cx.store a' = some q → a' = a := fun a' h' => resolve_inj auth h' hq
  rw [roles] at hkeyed
  suffices hkeq : k = c.name.map (Ix.LeanIngress.evAddr ixe b) by rw [hkeq]
  cases hn : c.name with
  | aux k' d => rw [hn] at hk; simp [keyAddress] at hk
  | role r =>
    rw [hn] at hk
    simp only [keyAddress] at hk
    have named := bindings_bound checked (bound_of_addressOf hk) hq inj
    rcases hkeyed with hkeyed | ⟨hnone, -⟩
    · rw [named] at hkeyed
      exact (Option.some.inj hkeyed).symm
    · rw [named] at hnone
      cases hnone
  | id n =>
    rw [hn] at hk
    simp only [keyAddress] at hk
    -- the key is a representative's, bound nowhere in the table
    have good := (rel.all c hc).name
    rw [hn] at good
    simp only [Key.good_id, KeyScope.ofId_id] at good
    have repr : Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap tA) n := by
      rcases good with repr | ⟨-, none, -⟩
      · exact repr
      · rw [hk] at none; cases none
    have unboundRole := qrepAt_unbound tableBound repr hk
    have unbound : ∀ r, (r, a) ∉ tA.bound.toList := by
      intro r hmem
      have := (Ix.LeanIngress.roleAtMap_spec checked).mpr (addressOf_of_bound checked hmem)
      rw [unboundRole] at this
      cases this
    have hnone := bindings_unbound unbound inj
    rcases hkeyed with hkeyed | ⟨-, i, hi, rfl⟩
    · rw [hnone] at hkeyed
      cases hkeyed
    · simp only [Mode.addressId?, Option.some.injEq] at hi
      subst hi
      simp only [Key.map, evAddr_published hk]


/-! ## Every published name's representative reads -/

set_option maxRecDepth 8192 in
/-- A fiber's representative under the table rule that is a role key is the role bound at
the fiber's address. -/
theorem rep_role_bound {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    (bound : Ix.LeanIngress.TableBound ixe roles) {a : Address} {r : Role}
    (h : Ix.LeanIngress.repAt roles[a]?
      (Ix.LeanIngress.fiberRep ((Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD a []),
        ((Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD a []).filterMap
          Ix.LeanIngress.roleOf) = some (.role r)) :
    roles[a]? = some r := by
  cases hr : roles[a]? with
  | some r' =>
    rw [hr] at h
    simp only [Ix.LeanIngress.repAt] at h
    split at h
    · cases h; rfl
    · cases h
  | none =>
    rw [hr] at h
    simp only [Ix.LeanIngress.repAt] at h
    obtain ⟨k, hk, hkr⟩ := Ix.LeanIngress.fiberRep_mem h
    have hrole : Ix.LeanIngress.roleOf k = some r := by
      unfold Ix.LeanIngress.roleOf
      rw [hkr]
    have := bound k r a (Ix.LeanIngress.mem_fiberMembers.mp hk) hrole
    rw [hr] at this
    cases this

/-- **A published name's quotient key sits at its published address.** -/
theorem keyAddress_quotientKey {ixe : Ixon.Env} {t : RoleTable} (checked : t.check = .ok ())
    (bound : PublishedRolesBound t ixe) (agree : PublishedAgree ixe) {m : Ix.Name} {named : Ixon.Named}
    (hm : (m, named) ∈ ixe.named.toList) :
    keyAddress ixe t (quotientKey ixe t m) = some named.addr := by
  have tb := tableBound_of checked bound
  have ha := agree m named hm
  have hne : (Ix.LeanIngress.fiberMembers (Ix.LeanIngress.sourceAddrs ixe)).getD named.addr [] ≠ [] := by
    intro h
    have := Ix.LeanIngress.mem_fiberMembers.mpr ha
    rw [h] at this
    cases this
  obtain ⟨rep, hrep⟩ := Ix.LeanIngress.repAt_isSome (bound := (Ix.LeanIngress.roleAtMap t)[named.addr]?) hne
    fun x hx r hxr => tb x r named.addr (Ix.LeanIngress.mem_fiberMembers.mp hx) hxr
  unfold quotientKey Ix.LeanIngress.ingressKey
  rw [Ix.LeanIngress.fiberAliasAt_subst ha hrep]
  cases rep with
  | aux k d =>
    rcases Ix.LeanIngress.repAt_mem hrep with ⟨k', -, hk'⟩ | ⟨r, hr⟩
    · unfold Ix.Kernel.Key.ofName at hk'
      split at hk' <;> cases hk'
    · cases hr
  | role r =>
    simp only [keyAddress]
    exact (Ix.LeanIngress.roleAtMap_spec checked).mp (rep_role_bound tb hrep)
  | id n =>
    simp only [keyAddress]
    rcases Ix.LeanIngress.repAt_mem hrep with ⟨k, hk, hkr⟩ | ⟨r, hr⟩
    · have : k = n := by
        unfold Ix.Kernel.Key.ofName at hkr
        split at hkr <;> cases hkr
        rfl
      subst this
      exact Ix.LeanIngress.mem_fiberMembers.mp hk
    · cases hr

/-- Every record of a canonical reading decodes to a wire-valid constant encoding to it. -/
theorem recordsRead_mem {limits : Admission.Limits} {records : Admission.Records}
    {constants : List (Address × Ixon.Constant)} (reading : Admission.RecordsRead limits records constants)
    {a : Address} {bytes : ByteArray} (h : (a, bytes) ∈ records) :
    ∃ c, (a, c) ∈ constants ∧ c.wireWF ∧ Ixon.serConstant c = bytes := by
  induction reading with
  | nil => cases h
  | cons reads _ ih =>
    rcases List.mem_cons.mp h with he | h
    · cases he
      exact ⟨_, List.mem_cons_self .., reads.wire, reads.encoded⟩
    · obtain ⟨c, hc, wire, enc⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc, wire, enc⟩

/-- **A record the stream reads resolves**, unless it is a block. -/
theorem readRecord_resolves {cx : Ctx .anon} {st : State .anon} {a : Address} {c : Ixon.Constant}
    {r : Read .anon} (h : readRecord cx st a c = .ok r) (nb : ∀ ms, c.info ≠ .muts ms) :
    ∃ q, resolveSource cx.store a c = some q := by
  cases kind : c.info with
  | defn _ | recr _ | axio _ | quot _ => exact ⟨.member a 0, by simp [resolveSource, kind]⟩
  | muts ms => exact absurd kind (nb ms)
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    cases hres : resolveSource cx.store a c with
    | some q => exact ⟨q, rfl⟩
    | none =>
      exfalso
      unfold readRecord at h
      rw [kind] at h
      simp [hres, malformed, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- **A quotient constant keyed at a published input name's address, whose record is in
the stream, reads.** -/
theorem readingAt_isSome_at {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {binding : Admission.Binding}
    {limits : Admission.Limits} {order : List Address}
    {tA : RoleTable} {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)} {cx : Ctx .anon}
    (A : Accepted binding limits ixe order tA pre constants cx) {m : Ix.Name} {named : Ixon.Named}
    (hm : (m, named) ∈ ixe.named.toList) (input : env.consts.contains m = true)
    (inOrder : named.addr ∈ order) {c : Ix.Kernel.ConstantInfo .source}
    (hk : keyAddress ixe t c.name = some named.addr) :
    (readingAt ixe t cx c).isSome = true := by
  obtain ⟨lc, stored, header⟩ := publishedReadable P.compiled m named hm input
  -- the published record is one of the stream's records
  have inRecords : (named.addr, lc.rawBytes) ∈ recordsOf ixe order := by
    unfold recordsOf
    exact List.mem_filterMap.mpr ⟨named.addr, inOrder, by simp only [stored, Option.map_some]⟩
  obtain ⟨c', inConstants, wire, encoded⟩ := recordsRead_mem A.decoded inRecords
  have nb := RecordHeaders.not_muts_of_header wire encoded header
  -- the stream's store holds it
  have unique : (constants.map Prod.fst).Nodup := A.decoded.keys ▸ A.unique.1
  have stored' : cx.store named.addr = some c' := by
    rw [A.context]
    exact ReaderClosureKeys.context_input tA constants.toArray (pre.records ++ pre.evidence) (blobsOf ixe order)
      pre.blobs (hintsOf ixe) (Admission.projectionAddress Address.admissionHash)
      (by simpa using unique) (by simpa using inConstants)
  -- the stream read it, so it resolves
  obtain ⟨st', decls, reads⟩ := A.reads
  obtain ⟨st₀, r, read, -⟩ := reads.mem inConstants
  obtain ⟨q, hq⟩ := readRecord_resolves read nb
  have hres : resolve cx.store named.addr = some q := by
    simp [resolve, stored', hq]
  have hkey : ∃ k, cx.keyAt named.addr = .ok k := by
    cases hn : cx.roles.names[q]? with
    | some k => exact ⟨k, Ctx.keyAt_eq_ok.mpr (by simp [keyOfAddress, hres, hn])⟩
    | none => exact ⟨.id named.addr, Ctx.keyAt_eq_ok.mpr (by simp [keyOfAddress, hres, hn, Mode.addressId?])⟩
  obtain ⟨k, hk'⟩ := hkey
  simp [readingAt, hk, hk', Except.toOption]

/-- A stored entry of an environment is what a lookup of its name returns. -/
theorem stored_lookup {sub : Ix.Environment} {n : Ix.Name} {ci : Ix.ConstantInfo}
    (h : (n, ci) ∈ sub.consts.toList) : sub.consts.get? n = some ci := by
  rw [Std.HashMap.get?_eq_getElem?]
  exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp h).2

/-- **A quotient constant keyed at a closure constant's published address reads.** The
closure constant's published key is an input name (a lookup answers a key equal to it),
its record is stored as no block (`publishedReadable`), and it seeds the compiled
closure. -/
theorem readingAt_isSome_stored {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {binding : Admission.Binding}
    {limits : Admission.Limits} {order : List Address}
    (corder : ClosureOrder ixe (Seed ixe sub) order)
    {tA : RoleTable} {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)} {cx : Ctx .anon}
    (A : Accepted binding limits ixe order tA pre constants cx) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) {c : Ix.Kernel.ConstantInfo .source}
    (haddr : keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr)) :
    (readingAt ixe t cx c).isSome = true := by
  have hsub := stored_lookup hn
  have henv := P.source.1.mem_env hsub
  obtain ⟨named, hnamed⟩ := (compileCovers env ixe failures P.compiled n ci henv).mpr (P.none n ci hsub)
  rw [hnamed] at haddr
  rw [Std.HashMap.get?_eq_getElem?] at hnamed
  obtain ⟨k, hk, hmem⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp hnamed
  have input : env.consts.contains k = true := by
    rw [← Std.HashMap.contains_congr hk, Std.HashMap.contains_eq_isSome_getElem?,
      ← Std.HashMap.get?_eq_getElem?, henv]
    rfl
  obtain ⟨lc, stored, -⟩ := publishedReadable P.compiled k named hmem input
  have seed : Seed ixe sub named.addr := ⟨n, ci, named, hsub, by rw [Std.HashMap.get?_eq_getElem?]; exact hnamed, rfl⟩
  have has : ixe.consts.contains named.addr = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, stored]
    rfl
  have inOrder : named.addr ∈ order := (corder.complete named.addr).mpr (.seed seed has)
  exact readingAt_isSome_at P A hmem input inOrder haddr

/-! ## The obligation -/

/-- **The reader keys every representative as its renaming**, with the second conjunct over
the closure's stored entries, given that the representative's key sits at the
entry's published address (the address conjunct of `Obligation.SourceTotal`). -/
theorem readingKeys_stored {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    {binding : Admission.Binding} {limits : Admission.Limits} {order : List Address} {envA : Env .anon}
    {b : Ix.RoleEvidence.Bundle} (P : Premises env roots sub ixe failures t envQ)
    (hbind : Admission.defaultBinding = .ok binding)
    (acc : IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA)
    (hb : Ix.RoleEvidence.quotientBundle () = .ok b) :
    ∃ cx, admissionContext binding limits ixe order = some cx ∧
      (∀ c ∈ envQ.consts, ∀ e, readingAt ixe t cx c = some e →
        e = .const (c.name.map (Ix.LeanIngress.evAddr ixe b)) (c.toConstantVal.levelParams.map .param)) ∧
      ∀ n ci, (n, ci) ∈ sub.consts.toList → ∀ c ∈ envQ.consts, c.name = quotientKey ixe t n →
        keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr) →
        (readingAt ixe t cx c).isSome = true := by
  obtain ⟨tA, pre, constants, cx, A⟩ := accepted acc
  refine ⟨cx, A.admission, readingAt_renamed P hbind A hb, ?_⟩
  intro n ci hn c _ _ haddr
  exact readingAt_isSome_stored P acc.1 A hn haddr

/-- **The reader keys every representative as its renaming** (`Obligation.ReadingKeys`). -/
theorem readingKeys : Obligation.ReadingKeys := by
  intro env roots sub ixe failures t envQ binding limits order envA b P hbind acc hb
  obtain ⟨cx, hcx, keys, reads⟩ := readingKeys_stored P hbind acc hb
  exact ⟨cx, hcx, keys, reads⟩

/-- info: 'Ix.Cert.ReadingKeys.readingKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms readingKeys

end Ix.Cert.ReadingKeys
