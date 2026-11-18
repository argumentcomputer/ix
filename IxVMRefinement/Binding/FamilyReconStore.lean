import IxVMRefinement.Binding.FamilyReconLocal
import IxVMRefinement.Binding.FamilyReconRoute

/-! # The reconstruction over stores: a larger store, a used-closed sub-store

* `indDataAt_mono`, `ctorAt_mono`, `defnAt_mono`, `unfoldAt_mono`: a store that holds the
  first's records at the addresses read (and at a projection's block) and its blobs answers the
  same wherever the first answers (the canonical reading reads the record and the blobs only,
  `loadedAt_mono`).
* `reconOfStore_le`: a store holding the records and blobs of `E` answers as `E` everywhere;
  `reconOfStore_leOn_sub`, `reconOfStore_closedOn_sub`: a sub-store of `E₀` closed under used
  references and owners, holding `E₀`'s blobs, answers as `E₀` at the addresses it holds, and
  what `E₀` answers there names only addresses it holds (`read_keys`, through the raw reading
  under the canonical one: `keyIn_of_loadedAt`, `keys_held_of_loaded`).
* **`RFormS.grow`**, **`RFormS.of_sub`**: the record-level form passes to a larger store and to a
  used-closed sub-store of the run's store that holds the block and the record. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (KExpr KLevel KKey bmeta ExprLvEq)
open IxVM.Refinement.ReaderReads (exprReader_mono)

set_option linter.unusedVariables false

/-! ## The readers over two stores -/

section Readers

variable {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env} {Ok : _root_.Address → Prop}

theorem indDataAt_mono
    (hA : ∀ y c, Ok y → recordOf E y = some c → recordOf E' y = some c)
    (hOwn : ∀ y c, Ok y → recordOf E y = some c → Ok (Ix.Cert.ownerOf y c))
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {a : _root_.Address} (ha : Ok a) {x : IndData} (h : indDataAt t E a = some x) :
    indDataAt t E' a = some x := by
  unfold indDataAt at h ⊢
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
  rw [hc] at h
  rw [hA a c ha hc]
  simp only at h ⊢
  cases hci : c.info with
  | iPrj p =>
    simp only [hci] at h ⊢
    have hpb : Ok p.block := by
      have h1 := hOwn a c ha hc
      simp only [Ix.Cert.ownerOf, hci] at h1
      exact h1
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb =>
    rw [hcb] at h
    rw [hA _ cb hpb hcb]
    simp only at h ⊢
    cases hcbi : cb.info with
    | muts ms =>
      simp only [hcbi] at h ⊢
      cases hm : ms[p.idx.toNat]? with
      | none => simp [hm] at h
      | some m =>
        cases m with
        | indc ind =>
          simp only [hm] at h ⊢
          cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms)
              ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ with
          | none => rw [hr] at h; simp at h
          | some ty =>
            rw [loadedAt_mono hblob hr]
            rw [hr] at h
            exact h
        | defn _ => simp [hm] at h
        | recr _ => simp [hm] at h
    | _ => simp [hcbi] at h
  | _ => simp [hci] at h

theorem ctorAt_mono
    (hA : ∀ y c, Ok y → recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {b : _root_.Address} (hb : Ok b) {i j : Nat} {x : KExpr × Nat}
    (h : ctorAt t E b i j = some x) : ctorAt t E' b i j = some x := by
  unfold ctorAt at h ⊢
  cases hcb : recordOf E b with
  | none => simp [hcb] at h
  | some cb =>
  rw [hcb] at h
  rw [hA b cb hb hcb]
  simp only at h ⊢
  cases hcbi : cb.info with
  | muts ms =>
    simp only [hcbi] at h ⊢
    cases hm : ms[i]? with
    | none => simp [hm] at h
    | some m =>
      cases m with
      | indc ind =>
        simp only [hm] at h ⊢
        cases hct : ind.ctors[j]? with
        | none => simp [hct] at h
        | some ctor =>
          simp only [hct] at h ⊢
          cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t b ms) ctor.lvls.toNat
              (mutsRoot ms i + 1 + ((j : Nat) : IxVM.F)) ctor.typ with
          | none => rw [hr] at h; simp at h
          | some ty =>
            rw [loadedAt_mono hblob hr]
            rw [hr] at h
            exact h
      | defn _ => simp [hm] at h
      | recr _ => simp [hm] at h
  | _ => simp [hcbi] at h

theorem defnAt_mono
    (hA : ∀ y c, Ok y → recordOf E y = some c → recordOf E' y = some c)
    (hOwn : ∀ y c, Ok y → recordOf E y = some c → Ok (Ix.Cert.ownerOf y c))
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {a : _root_.Address} (ha : Ok a) {x : Option (Nat × KExpr)} (h : defnAt t E a = some x) :
    defnAt t E' a = some x := by
  unfold defnAt at h ⊢
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
  rw [hc] at h
  rw [hA a c ha hc]
  simp only at h ⊢
  cases hci : c.info with
  | defn d =>
    simp only [hci] at h ⊢
    cases hk : d.kind with
    | defn =>
      simp only [hk] at h ⊢
      cases hr : loadedAt t (fun y => E.blobs.get? y) c (soloSelf t a) d.lvls.toNat 1
          d.value with
      | none => rw [hr] at h; simp at h
      | some v =>
        rw [loadedAt_mono hblob hr]
        rw [hr] at h
        exact h
    | _ => simp only [hk] at h ⊢; exact h
  | dPrj p =>
    simp only [hci] at h ⊢
    have hpb : Ok p.block := by
      have h1 := hOwn a c ha hc
      simp only [Ix.Cert.ownerOf, hci] at h1
      exact h1
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb =>
    rw [hcb] at h
    rw [hA _ cb hpb hcb]
    simp only at h ⊢
    cases hcbi : cb.info with
    | muts ms =>
      simp only [hcbi] at h ⊢
      cases hm : ms[p.idx.toNat]? with
      | none => simp [hm] at h
      | some m =>
        cases m with
        | defn d =>
          simp only [hm] at h ⊢
          cases hk : d.kind with
          | defn =>
            simp only [hk] at h ⊢
            cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms)
                d.lvls.toNat (mutsRoot ms p.idx.toNat + 1) d.value with
            | none => rw [hr] at h; simp at h
            | some v =>
              rw [loadedAt_mono hblob hr]
              rw [hr] at h
              exact h
          | _ => simp only [hk] at h ⊢; exact h
        | indc _ => simp [hm] at h
        | recr _ => simp [hm] at h
    | _ => simp [hcbi] at h
  | _ => simp only [hci] at h ⊢; exact h

theorem unfoldAt_mono
    (hA : ∀ y c, Ok y → recordOf E y = some c → recordOf E' y = some c)
    (hOwn : ∀ y c, Ok y → recordOf E y = some c → Ok (Ix.Cert.ownerOf y c))
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {k : KKey} (hok : ∀ a, keyAddr t k = some a → Ok a) {us : List KLevel} {x : Option KExpr}
    (h : unfoldAt t E k us = some x) : unfoldAt t E' k us = some x := by
  unfold unfoldAt at h ⊢
  cases hk : keyAddr t k with
  | none => simp only [hk] at h ⊢; exact h
  | some a =>
    simp only [hk] at h ⊢
    cases hd : defnAt t E a with
    | none => simp [hd] at h
    | some y =>
      rw [defnAt_mono hA hOwn hblob (hok a hk) hd]
      rw [hd] at h
      exact h

theorem ctorOfAt_mono
    (hA : ∀ y c, Ok y → recordOf E y = some c → recordOf E' y = some c)
    (hOwn : ∀ y c, Ok y → recordOf E y = some c → Ok (Ix.Cert.ownerOf y c))
    {a : _root_.Address} (ha : Ok a) {x : Option CtorData} (h : ctorOfAt E a = some x) :
    ctorOfAt E' a = some x := by
  unfold ctorOfAt at h ⊢
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
  rw [hc] at h
  rw [hA a c ha hc]
  simp only at h ⊢
  cases hci : c.info with
  | cPrj p =>
    simp only [hci] at h ⊢
    have hpb : Ok p.block := by
      have h1 := hOwn a c ha hc
      simp only [Ix.Cert.ownerOf, hci] at h1
      exact h1
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb =>
    rw [hcb] at h
    rw [hA _ cb hpb hcb]
    exact h
  | _ => simp only [hci] at h ⊢; exact h

end Readers

/-! ## Inversions -/

section Inv

variable {t : Ix.Kernel.RoleTable} {E : Ixon.Env}

theorem indDataAt_inv {a : _root_.Address} {i : IndData} (h : indDataAt t E a = some i) :
    ∃ c p cb ms ind, recordOf E a = some c ∧ c.info = .iPrj p ∧ recordOf E p.block = some cb ∧
      cb.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms) ind.lvls.toNat
        (mutsRoot ms p.idx.toNat) ind.typ = some i.ty ∧ i.blk = p.block := by
  unfold indDataAt at h
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
  rw [hc] at h
  simp only at h
  cases hci : c.info with
  | iPrj p =>
    simp only [hci] at h
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb =>
    rw [hcb] at h
    simp only at h
    cases hcbi : cb.info with
    | muts ms =>
      simp only [hcbi] at h
      cases hm : ms[p.idx.toNat]? with
      | none => simp [hm] at h
      | some m =>
        cases m with
        | indc ind =>
          simp only [hm] at h
          cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms)
              ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ with
          | none => rw [hr] at h; simp at h
          | some ty =>
            rw [hr] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨c, p, cb, ms, ind, rfl, hci, hcb, hcbi, hm, hr, rfl⟩
        | defn _ => simp [hm] at h
        | recr _ => simp [hm] at h
    | _ => simp [hcbi] at h
  | _ => simp [hci] at h

theorem ctorAt_inv {b : _root_.Address} {i j : Nat} {ty : KExpr} {np : Nat}
    (h : ctorAt t E b i j = some (ty, np)) :
    ∃ cb ms ind ctor, recordOf E b = some cb ∧ cb.info = .muts ms ∧
      ms[i]? = some (.indc ind) ∧ ind.ctors[j]? = some ctor ∧
      loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t b ms) ctor.lvls.toNat
        (mutsRoot ms i + 1 + ((j : Nat) : IxVM.F)) ctor.typ = some ty := by
  unfold ctorAt at h
  cases hcb : recordOf E b with
  | none => simp [hcb] at h
  | some cb =>
  rw [hcb] at h
  simp only at h
  cases hcbi : cb.info with
  | muts ms =>
    simp only [hcbi] at h
    cases hm : ms[i]? with
    | none => simp [hm] at h
    | some m =>
      cases m with
      | indc ind =>
        simp only [hm] at h
        cases hct : ind.ctors[j]? with
        | none => simp [hct] at h
        | some ctor =>
          simp only [hct] at h
          cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t b ms) ctor.lvls.toNat
              (mutsRoot ms i + 1 + ((j : Nat) : IxVM.F)) ctor.typ with
          | none => rw [hr] at h; simp at h
          | some ty' =>
            rw [hr] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact ⟨cb, ms, ind, ctor, rfl, hcbi, hm, hct, hr⟩
      | defn _ => simp [hm] at h
      | recr _ => simp [hm] at h
  | _ => simp [hcbi] at h

theorem defnAt_inv {a : _root_.Address} {n : Nat} {v : KExpr}
    (h : defnAt t E a = some (some (n, v))) :
    ∃ c, recordOf E a = some c ∧
      ((∃ d, c.info = .defn d ∧
          loadedAt t (fun y => E.blobs.get? y) c (soloSelf t a) d.lvls.toNat 1 d.value =
            some v) ∨
        (∃ p cb ms d, c.info = .dPrj p ∧ recordOf E p.block = some cb ∧ cb.info = .muts ms ∧
          ms[p.idx.toNat]? = some (.defn d) ∧
          loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms) d.lvls.toNat
            (mutsRoot ms p.idx.toNat + 1) d.value = some v)) := by
  unfold defnAt at h
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
  rw [hc] at h
  simp only at h
  refine ⟨c, rfl, ?_⟩
  cases hci : c.info with
  | defn d =>
    simp only [hci] at h
    cases hk : d.kind with
    | defn =>
      simp only [hk] at h
      cases hr : loadedAt t (fun y => E.blobs.get? y) c (soloSelf t a) d.lvls.toNat 1
          d.value with
      | none => rw [hr] at h; simp at h
      | some w =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact Or.inl ⟨d, rfl, hr⟩
    | _ => simp [hk] at h
  | dPrj p =>
    simp only [hci] at h
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb =>
    rw [hcb] at h
    simp only at h
    cases hcbi : cb.info with
    | muts ms =>
      simp only [hcbi] at h
      cases hm : ms[p.idx.toNat]? with
      | none => simp [hm] at h
      | some m =>
        cases m with
        | defn d =>
          simp only [hm] at h
          cases hk : d.kind with
          | defn =>
            simp only [hk] at h
            cases hr : loadedAt t (fun y => E.blobs.get? y) cb (blockSelf t p.block ms)
                d.lvls.toNat (mutsRoot ms p.idx.toNat + 1) d.value with
            | none => rw [hr] at h; simp at h
            | some w =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact Or.inr ⟨p, cb, ms, d, rfl, hcb, hcbi, hm, hr⟩
          | _ => simp [hk] at h
        | indc _ => simp [hm] at h
        | recr _ => simp [hm] at h
    | _ => simp [hcbi] at h
  | _ => simp [hci] at h

theorem unfoldAt_inv {k : KKey} {us : List KLevel} {v : KExpr}
    (h : unfoldAt t E k us = some (some v)) :
    ∃ a n w, keyAddr t k = some a ∧ defnAt t E a = some (some (n, w)) ∧
      v = w.instantiateLevelParams (List.range n) us := by
  unfold unfoldAt at h
  cases hk : keyAddr t k with
  | none => simp [hk] at h
  | some a =>
    simp only [hk] at h
    cases hd : defnAt t E a with
    | none => simp [hd] at h
    | some y =>
      cases y with
      | none => simp [hd] at h
      | some p =>
        obtain ⟨n, w⟩ := p
        simp only [hd] at h
        split at h
        · simp only [Option.some.injEq] at h
          exact ⟨a, n, w, rfl, hd, h.symm⟩
        · simp at h

end Inv

/-! ## The views of two stores -/

section Views

variable {t : Ix.Kernel.RoleTable}

/-- **A store holding the records and blobs of `E` answers as `E` wherever `E` answers.** -/
theorem reconOfStore_le {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b) :
    (ReconView.ofStore t E).LeOn (fun _ => True) (ReconView.ofStore t E') where
  ind a x _ h := indDataAt_mono (Ok := fun _ => True) (fun y c _ hy => hle y c hy)
    (fun _ _ _ _ => trivial) hblob trivial h
  ctor b i c x _ h := ctorAt_mono (Ok := fun _ => True) (fun y c _ hy => hle y c hy) hblob
    trivial h
  ctorAddr := rfl
  key := rfl
  addr := rfl
  unfold k us x _ h := unfoldAt_mono (Ok := fun _ => True) (fun y c _ hy => hle y c hy)
    (fun _ _ _ _ => trivial) hblob (fun _ _ => trivial) h
  ctorOf a x _ h := ctorOfAt_mono (Ok := fun _ => True) (fun y c _ hy => hle y c hy)
    (fun _ _ _ _ => trivial) trivial h
  modeled b x _ h := blockRoute_grow hle x h

/-- Every view is closed on every address. -/
theorem ReconView.closedOn_true (V : ReconView) : V.ClosedOn (fun _ => True) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => trivial⟩

theorem held_of_sub {E₀ R : Ixon.Env}
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) {y : _root_.Address}
    {c : Ixon.Constant} (hy : Held R y) (h : recordOf E₀ y = some c) : recordOf R y = some c :=
  (recordOf_eq_of_held hsub hy).trans h

/-- **A used-closed sub-store of `E₀` holding `E₀`'s blobs answers as `E₀` at the addresses it
holds.** -/
theorem reconOfStore_leOn_sub {E₀ R : Ixon.Env}
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b) :
    (ReconView.ofStore t E₀).LeOn (Held R) (ReconView.ofStore t R) where
  ind a x ha h := indDataAt_mono (Ok := Held R) (fun y c hy h => held_of_sub hsub hy h)
    (fun y c hy h => (hcl.1 y c (held_of_sub hsub hy h)).1) hblob ha h
  ctor b i c x hb h := ctorAt_mono (Ok := Held R) (fun y c hy h => held_of_sub hsub hy h) hblob
    hb h
  ctorAddr := rfl
  key := rfl
  addr := rfl
  unfold k us x hk h := unfoldAt_mono (Ok := Held R) (fun y c hy h => held_of_sub hsub hy h)
    (fun y c hy h => (hcl.1 y c (held_of_sub hsub hy h)).1) hblob hk h
  ctorOf a x ha h := ctorOfAt_mono (Ok := Held R) (fun y c hy h => held_of_sub hsub hy h)
    (fun y c hy h => (hcl.1 y c (held_of_sub hsub hy h)).1) ha h
  modeled b x hb h := blockRoute_of_sub hsub hcl hb x h

/-- A block's members are held with it, so `recur` over a held block names held addresses. -/
theorem blockSelf_held {R : Ixon.Env} (hcl : UsedClosed R) {b : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hcbR : recordOf R b = some cb)
    (hci : cb.info = .muts ms) :
    ∀ (j : Nat) (k : Ix.Kernel.Key .anon), blockSelf t b ms j = some (Except.ok k) →
      ∃ z, Held R z ∧ k = keyOf t z := by
  intro j k hs
  unfold blockSelf at hs
  cases hmj : ms[j]? with
  | none =>
    rw [hmj] at hs
    cases hs
  | some mj =>
    rw [hmj] at hs
    cases Except.ok.inj (Option.some.inj hs)
    exact ⟨_, Option.isSome_iff_exists.mpr ⟨_, (hcl.2 b cb ms hcbR hci j mj hmj).1⟩, rfl⟩

/-- A member's expressions are among the block's used references. -/
theorem mem_used_of_member {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {m : Ixon.MutConst} (hci : cb.info = .muts ms) (hm : ms[i]? = some m) :
    ∀ j ∈ mutRefIdxs m, j ∈ usedRefIdxs cb := by
  intro j hj
  have hmem : m ∈ ms.toList :=
    List.mem_of_getElem? (show ms.toList[i]? = some m by rw [Array.getElem?_toList]; exact hm)
  simp only [usedRefIdxs, hci]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hmem, hj⟩)

/-- **The keys a reading over a held record makes name held addresses.** -/
theorem keys_held_of_read {E₀ R : Ixon.Env} (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hcl : UsedClosed R) {src : Ixon.Constant} {y0 : _root_.Address}
    (hsrc : recordOf R y0 = some src)
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ (j : Nat) (k : Ix.Kernel.Key .anon), self j = some (Except.ok k) →
      ∃ z, Held R z ∧ k = keyOf t z)
    {e : Ixon.Expr} (he : ∀ j ∈ exprRefIdxs e, j ∈ usedRefIdxs src)
    {blob : _root_.Address → Option ByteArray} {v : KExpr}
    (h : (exprReader t blob src id self).read e = .ok v) :
    RKeysAt (ReconView.ofStore t E₀) (Held R) v := by
  intro k hk a ha
  obtain ⟨z, hz, rfl⟩ := read_keys checked (P := fun k => ∃ z, Held R z ∧ k = keyOf t z)
    (fun j hj y hy => ⟨y, (hcl.1 y0 src hsrc).2 j hj y hy, rfl⟩) hself he h k hk
  have e : a = z := Option.some.inj (ha.symm.trans (keyAddr_keyOf hwf z))
  rw [e]
  exact hz

/-- **The keys the canonical reading of a held record makes name held addresses**: they are
keys of the raw reading (`keyIn_of_loadedAt`). -/
theorem keys_held_of_loaded {E₀ R : Ixon.Env} (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hcl : UsedClosed R) {src : Ixon.Constant} {y0 : _root_.Address}
    (hsrc : recordOf R y0 = some src)
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ (j : Nat) (k : Ix.Kernel.Key .anon), self j = some (Except.ok k) →
      ∃ z, Held R z ∧ k = keyOf t z)
    {e : Ixon.Expr} (he : ∀ j ∈ exprRefIdxs e, j ∈ usedRefIdxs src)
    {blob : _root_.Address → Option ByteArray} {nl : Nat} {root : IxVM.F} {v : KExpr}
    (h : loadedAt t blob src self nl root e = some v) :
    RKeysAt (ReconView.ofStore t E₀) (Held R) v := by
  intro k hk a ha
  obtain ⟨e₀, hr₀, hk₀⟩ := keyIn_of_loadedAt h hk
  exact keys_held_of_read (E₀ := E₀) checked hwf hcl hsrc hself he hr₀ k hk₀ a ha

/-- **What `E₀` answers at the addresses a used-closed sub-store holds names only addresses it
holds**: an inductive's block is its owner; the keys of an inductive's type, of a constructor's
type and of a definition's value are keys of references their records use or of the members of
their blocks (`read_keys`). -/
theorem reconOfStore_closedOn_sub {E₀ R : Ixon.Env} (checked : t.check = .ok ())
    (hwf : t.wf = true) (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hcl : UsedClosed R) : (ReconView.ofStore t E₀).ClosedOn (Held R) where
  indBlk a i ha h := by
    obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, hr, hblk⟩ :=
      indDataAt_inv (h : indDataAt t E₀ a = some i)
    have h1 := (hcl.1 a c (held_of_sub hsub ha hc)).1
    simp only [Ix.Cert.ownerOf, hci] at h1
    rw [hblk]
    exact h1
  indTy a i ha h := by
    obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, hr, hblk⟩ :=
      indDataAt_inv (h : indDataAt t E₀ a = some i)
    have hpb : Held R p.block := by
      have h1 := (hcl.1 a c (held_of_sub hsub ha hc)).1
      simp only [Ix.Cert.ownerOf, hci] at h1
      exact h1
    have hcbR := held_of_sub hsub hpb hcb
    exact keys_held_of_loaded checked hwf hcl hcbR (blockSelf_held hcl hcbR hcbi)
      (fun j hj => mem_used_of_member hcbi hm j (List.mem_append_left _ hj)) hr
  ctorTy b i c ty np hb h := by
    obtain ⟨cb, ms, ind, ctor, hcb, hcbi, hm, hct, hr⟩ :=
      ctorAt_inv (h : ctorAt t E₀ b i c = some (ty, np))
    have hcbR := held_of_sub hsub hb hcb
    have hcmem : ctor ∈ ind.ctors.toList :=
      List.mem_of_getElem? (show ind.ctors.toList[c]? = some ctor by
        rw [Array.getElem?_toList]; exact hct)
    exact keys_held_of_loaded checked hwf hcl hcbR (blockSelf_held hcl hcbR hcbi)
      (fun j hj => mem_used_of_member hcbi hm j
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ctor, hcmem, hj⟩))) hr
  unfold k us v hk h := by
    obtain ⟨a, n, w, hka, hd, rfl⟩ := unfoldAt_inv (h : unfoldAt t E₀ k us = some (some v))
    have ha : Held R a := hk a hka
    obtain ⟨c, hc, hdef⟩ := defnAt_inv hd
    have hcR := held_of_sub hsub ha hc
    intro k' hk' a' ha'
    have hk'' := keyIn_instantiateLevelParams w hk'
    rcases hdef with ⟨d, hci, hr⟩ | ⟨p, cb, ms, d, hci, hcb, hcbi, hm, hr⟩
    · refine keys_held_of_loaded checked hwf hcl hcR ?_ (fun j hj => ?_) hr k' hk'' a' ha'
      · intro j k hs
        unfold soloSelf at hs
        split at hs
        · cases Except.ok.inj (Option.some.inj hs)
          exact ⟨a, ha, rfl⟩
        · cases hs
      · simp only [usedRefIdxs, hci]
        exact List.mem_append_right _ (List.mem_append_right _ hj)
    · have hpb : Held R p.block := by
        have h1 := (hcl.1 a c hcR).1
        simp only [Ix.Cert.ownerOf, hci] at h1
        exact h1
      have hcbR := held_of_sub hsub hpb hcb
      exact keys_held_of_loaded checked hwf hcl hcbR (blockSelf_held hcl hcbR hcbi)
        (fun j hj => mem_used_of_member hcbi hm j (List.mem_append_right _ hj)) hr k' hk'' a' ha'

end Views

/-! ## The record-level form over two stores -/

theorem memberRecon_transport {TyRel : KExpr → KExpr → Prop} {t : Ix.Kernel.RoleTable}
    {E E' : Ixon.Env} {S : _root_.Address → Prop}
    (hV : (ReconView.ofStore t E).LeOn S (ReconView.ofStore t E'))
    (hC : (ReconView.ofStore t E).ClosedOn S)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {es : List FlatEntry}
    {off fuel k : Nat} {r : Ixon.Recursor}
    (hE : ∀ e ∈ es, REntryAt (ReconView.ofStore t E) S e)
    (h : MemberRecon TyRel t E rb crb rs es off fuel k r) :
    MemberRecon TyRel t E' rb crb rs es off fuel k r := by
  obtain ⟨ty, R, bodies, cbk, hty, hR, hrel, hb, hcb, hrules⟩ := h
  refine ⟨ty, R, bodies, cbk, loadedAt_mono hblob hty, recTypeAt_leOn hV hC hE hR, hrel,
    ruleBodiesAt_leOn hV hC hE hb, ctorsBefore_leOn hV es k cbk hE hcb, fun c ru hru => ?_⟩
  obtain ⟨rhs, cb, hrhs, hcbody, hf⟩ := hrules c ru hru
  exact ⟨rhs, cb, loadedAt_mono hblob hrhs, hcbody, hf⟩

/-- **The record-level form passes to a store that holds the first's records and blobs.** -/
theorem RFormS.grow {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {B rb : _root_.Address} (h : RFormS t E B rb) : RFormS t E' B rb := by
  obtain ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, hM⟩ := h
  exact ⟨crb, rs, es, off, fuel, hle _ _ hrb, hrs, hRF.of_blobs hblob,
    blockDerivedFlat_grow hle hblob hBD,
    fun k r hr => memberRecon_transport (reconOfStore_le hle hblob) (ReconView.closedOn_true _)
      hblob (fun e _ => ⟨trivial, fun _ _ _ _ _ _ => trivial⟩) (hM k r hr)⟩

/-- **The record-level form checked over the run's store `E₀` passes to a sub-store closed under
used references and owners that holds the block, the record and `E₀`'s blobs**: the
reconstruction reads only addresses the sub-store holds. -/
theorem RFormS.of_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    {B rb : _root_.Address} (hB : Held R B) (hrb : Held R rb) (h : RFormS t E₀ B rb) :
    RFormS t R B rb := by
  obtain ⟨crb, rs, es, off, fuel, hrb₀, hrs, hRF, hBD, hM⟩ := h
  have hE : ∀ e ∈ es, REntryAt (ReconView.ofStore t E₀) (Held R) e := by
    obtain ⟨n, hn⟩ := hBD
    intro e he
    have hx := derivedFlatAt_entryAt (ofStore_closedOn_sub checked hwf hsub hcl) hB hn e he
    exact ⟨hx.addr, hx.params⟩
  exact ⟨crb, rs, es, off, fuel, held_of_sub hsub hrb hrb₀, hrs, hRF.of_blobs hblob,
    blockDerivedFlat_of_closed_sub checked hwf hsub hcl hblob hB hBD,
    fun k r hr => memberRecon_transport (reconOfStore_leOn_sub hsub hcl hblob)
      (reconOfStore_closedOn_sub checked hwf hsub hcl) hblob hE (hM k r hr)⟩

end IxVM.Refinement.Binding.FamilyRecon
