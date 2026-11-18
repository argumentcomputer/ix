import IxVMRefinement.Binding.ClosureFoldSteps
import IxVMRefinement.Binding.OpInstall
import IxVMRefinement.Binding.ClosureRoute

/-! # The closure fold with the family form: the proof

`closureFoldStatement` proves `ClosureFoldStatement`: from the plain, family and twin steps, the
closure of a group in the family form with the walked records stored. The closure's store is
`closureStore` (the group's store without its new role unit's record); the closure's environment
is the fold's result (`closureFold_run`). What is left after the fold:

* the boundary invariant at the closure's store and environment: the store clauses of the
  group's store; the reading clause (a reading of an address held before the group is one over
  `R`, the run fact `readsDown`; a new address with a reading is no block, so its owner unit
  stored it with its reading); the stored kept roles, pins and model; the fold's clause; a block
  stored whole; the operations and shapes kept, since the fold stores no operation's key and only
  extends the environment (`opsPinned_findExt`, `shapes_findExt`);
* the group's kept roles stored as their records declare them: a record held before the group
  was checked, so the walked records stored it (`WalkedStored`); a new one is owned by a unit;
* the stored families: the group's selection joined to the map before it (`joinFam`);
* `WalkedStored` after the closure: the new records' owners stored them, the old ones were stored.

Also here:

* the `findExt` lemmas: the shapes, the operations' pinned types and `stdAxiomOk` are kept by an
  extension that keeps every lookup that succeeds (IxC's `EnvExt` also asks about projection
  tables, which the fold does not track);
* `familyOfBlock_of_closed`: the family of a block over a store closed under block members that
  holds the block and its family record. -/

universe u

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open Ix.Kernel (ConstantInfo)

set_option linter.unusedVariables false

/-! ## Extensions that keep every successful lookup -/

section FindExt

variable {env env' : Ix.Kernel.Env .anon}

/-- A test of one lookup that fails at a missing key is kept. -/
theorem testFind_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {f : Option (ConstantInfo .anon) → Bool} {k : Ix.Kernel.Key .anon}
    (h : f (env.find? k) = true) (hnone : f none = false) : f (env'.find? k) = true := by
  cases hk : env.find? k with
  | none =>
    rw [hk, hnone] at h
    cases h
  | some c =>
    rw [hfind hk]
    rw [hk] at h
    exact h

theorem key_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {k : Ix.Kernel.Key .anon} (hk : env.find? k ≠ none) : env'.find? k = env.find? k := by
  cases hc : env.find? k with
  | none => exact absurd hc hk
  | some c => exact hfind hc

theorem natOpCod_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {c : Core.KKey} {e : Core.KExpr}
    (hc : Ix.Kernel.natOpCod env c e = true) : Ix.Kernel.natOpCod env' c e = true := by
  unfold Ix.Kernel.natOpCod at hc ⊢
  by_cases hcb : (c = Ix.Kernel.natBeqName || c = Ix.Kernel.natBleName) = true
  · rw [ite_eq_left hcb] at hc ⊢
    simp only [Bool.and_eq_true] at hc ⊢
    refine ⟨hc.1, ?_⟩
    have h2 := hc.2
    cases hf : env.find? Ix.Kernel.boolName with
    | none => rw [hf] at h2; exact nomatch h2
    | some ci => rw [hfind hf]; rw [hf] at h2; exact h2
  · rw [ite_eq_right hcb] at hc ⊢
    exact hc

theorem natOpTyPinned_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {c : Core.KKey} {ty : Core.KExpr}
    (hp : Ix.Kernel.natOpTyPinned env c ty = true) : Ix.Kernel.natOpTyPinned env' c ty = true := by
  unfold Ix.Kernel.natOpTyPinned at hp ⊢
  by_cases hc : c = Ix.Kernel.natPredName
  · rw [ite_eq_left hc] at hp ⊢
    cases ty with
    | forallE dom body mb =>
      have hp' : (dom == .const Ix.Kernel.natName [] && Ix.Kernel.natOpCod env c body) = true :=
        hp
      show (dom == .const Ix.Kernel.natName [] && Ix.Kernel.natOpCod env' c body) = true
      simp only [Bool.and_eq_true] at hp' ⊢
      exact ⟨hp'.1, natOpCod_findExt hfind hp'.2⟩
    | _ => exact nomatch hp
  · rw [ite_eq_right hc] at hp ⊢
    cases ty with
    | forallE dom b mb =>
      cases b with
      | forallE dom2 body mb2 =>
        have hp' : (dom == .const Ix.Kernel.natName [] && dom2 == .const Ix.Kernel.natName [] &&
            Ix.Kernel.natOpCod env c body) = true := hp
        show (dom == .const Ix.Kernel.natName [] && dom2 == .const Ix.Kernel.natName [] &&
            Ix.Kernel.natOpCod env' c body) = true
        simp only [Bool.and_eq_true] at hp' ⊢
        exact ⟨hp'.1, natOpCod_findExt hfind hp'.2⟩
      | _ => exact nomatch hp
    | _ => exact nomatch hp

/-- **The stored operations' pins are kept** where no operation's key is stored anew. -/
theorem opsPinned_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    (h : RoleOps.OpsPinned env)
    (hnew : ∀ n ∈ RoleOps.opNames, (env'.find? n).isSome = true → (env.find? n).isSome = true) :
    RoleOps.OpsPinned env' := by
  intro n hn hs
  obtain ⟨cv, v, hint, hf, hlp, hp⟩ := RoleOps.natOpStoredOk_inv (h n hn (hnew n hn hs))
  exact RoleOps.natOpStoredOk_intro (hfind hf) hlp (natOpTyPinned_findExt hfind hp)

theorem stdAxiomOk_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {cvA : Ix.Kernel.ConstantVal .anon}
    (h : Ix.Kernel.stdAxiomOk env cvA = true) : Ix.Kernel.stdAxiomOk env' cvA = true := by
  unfold Ix.Kernel.stdAxiomOk at h ⊢
  by_cases hp : cvA.name = Ix.Kernel.propextName
  · rw [ite_eq_left hp] at h ⊢
    have n1 : env.find? Ix.Kernel.eqName ≠ none := fun hk => by rw [hk] at h; simp at h
    have n2 : env.find? Ix.Kernel.iffName ≠ none := fun hk => by rw [hk] at h; simp at h
    have n3 : env.find? Ix.Kernel.iffIntroName ≠ none := fun hk => by rw [hk] at h; simp at h
    have n4 : env.find? Ix.Kernel.iffRecName ≠ none := fun hk => by rw [hk] at h; simp at h
    rw [key_findExt hfind n1, key_findExt hfind n2, key_findExt hfind n3,
      key_findExt hfind n4]
    exact h
  · rw [ite_eq_right hp] at h ⊢
    by_cases hc : cvA.name = Ix.Kernel.choiceName
    · rw [ite_eq_left hc] at h ⊢
      have n5 : env.find? Ix.Kernel.nonemptyName ≠ none := fun hk => by
        rw [hk] at h; simp at h
      have n6 : env.find? Ix.Kernel.nonemptyIntroName ≠ none := fun hk => by
        rw [hk] at h; simp at h
      have n7 : env.find? Ix.Kernel.nonemptyRecName ≠ none := fun hk => by
        rw [hk] at h; simp at h
      rw [key_findExt hfind n5, key_findExt hfind n6, key_findExt hfind n7]
      exact h
    · rw [ite_eq_right hc] at h ⊢
      exact h

/-- **The stored shapes are kept.** -/
theorem shapes_findExt
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env'.find? k = some c)
    {G : Nat → Prop} (hs : Shapes G env) : Shapes G env' where
  bool := fun h => by
    obtain ⟨⟨ci, hf, hl, ht⟩, ⟨⟨a, ha, hla⟩, ⟨b, hb, hlb⟩⟩, ⟨⟨a', ha', hta⟩, ⟨b', hb', htb⟩⟩⟩ :=
      hs.bool h
    exact ⟨⟨ci, hfind hf, hl, ht⟩, ⟨⟨a, hfind ha, hla⟩, ⟨b, hfind hb, hlb⟩⟩,
      ⟨⟨a', hfind ha', hta⟩, ⟨b', hfind hb', htb⟩⟩⟩
  char := fun h => testFind_findExt hfind (hs.char h) rfl
  string := fun h => testFind_findExt hfind (hs.string h) rfl
  list := fun h => by
    obtain ⟨h1, h2, h3⟩ := hs.list h
    exact ⟨testFind_findExt hfind h1 rfl, testFind_findExt hfind h2 rfl,
      testFind_findExt hfind h3 rfl⟩
  charOfNat := fun h => testFind_findExt hfind (hs.charOfNat h) rfl
  stringOfList := fun h => testFind_findExt hfind (hs.stringOfList h) rfl
  iff := fun h cvA hn hm => stdAxiomOk_findExt hfind (hs.iff h cvA hn hm)
  nonempty := fun h cvA hn hm => stdAxiomOk_findExt hfind (hs.nonempty h cvA hn hm)

end FindExt

/-! ## The family of a block over a closed store, and the joined family map -/

/-- **The family of a block over a store closed under block members that holds the block and its
family record**: the readers read the two records only. -/
theorem familyOfBlock_of_closed {E S : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {flat : List _root_.Address}
    (hS : UsedClosed S) (hB : recordOf S B = some cb) (hrb : recordOf S rb = some crb)
    (h : FamilyOfBlock E B cb ms rb crb rs flat) : FamilyOfBlock S B cb ms rb crb rs flat where
  block := {
    record := hB
    muts := h.block.muts
    indcs := h.block.indcs
    logic := h.block.logic
    members := fun i m hm => (hS.2 B cb ms hB h.block.muts i m hm).1
    ctors := fun i ind j hm hj => (hS.2 B cb ms hB h.block.muts i _ hm).2 ind rfl j hj }
  record := {
    record := hrb
    muts := h.record.muts
    recrs := h.record.recrs
    logic := h.record.logic
    members := fun i m hm => (hS.2 rb crb rs hrb h.record.muts i m hm).1 }
  covers := h.covers
  originals := h.originals
  motives := h.motives
  carriers := h.carriers
  major := h.major

/-- **The family map after a group**: the group's selection, else the map before the group. -/
def joinFam (famOf famOf₀ : _root_.Address → Option _root_.Address) (B : _root_.Address) :
    Option _root_.Address :=
  match famOf B with
  | some rb => some rb
  | none => famOf₀ B

theorem joinFam_some {famOf famOf₀ : _root_.Address → Option _root_.Address}
    {B rb : _root_.Address} (h : famOf B = some rb) : joinFam famOf famOf₀ B = some rb := by
  simp only [joinFam, h]

theorem joinFam_none {famOf famOf₀ : _root_.Address → Option _root_.Address}
    {B : _root_.Address} (h : famOf B = none) : joinFam famOf famOf₀ B = famOf₀ B := by
  simp only [joinFam, h]

theorem joinFam_cases {famOf famOf₀ : _root_.Address → Option _root_.Address}
    {B rb : _root_.Address} (h : joinFam famOf famOf₀ B = some rb) :
    famOf B = some rb ∨ (famOf B = none ∧ famOf₀ B = some rb) := by
  cases hfa : famOf B with
  | some rb' =>
    have e : rb' = rb := Option.some.inj ((joinFam_some (famOf₀ := famOf₀) hfa).symm.trans h)
    rw [e]
    exact Or.inl rfl
  | none =>
    rw [joinFam_none hfa] at h
    exact Or.inr ⟨rfl, h⟩

/-! ## The proof -/

set_option maxRecDepth 100000 in
private theorem prelude_not_unit :
    ∀ r ∈ preludeRoles, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) := by
  decide

/-- **A stored constant at an address's key is a pin or keeps the record there.** -/
theorem stored_keptIn {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (htwf : t.wf = true) (hb : BndOver.{u} L t G R env) {a : _root_.Address}
    {ci : ConstantInfo .anon} (hf : env.find? (keyOf t a) = some ci) :
    PinnedBasis ci ∨ KeptIn t (recordOf R) (fun y => R.blobs.get? y) a ci := by
  obtain ⟨hclaimed, hna⟩ := seed_claimed hf
  rcases hb.shape.reading.provenance ci hclaimed with ⟨tbl, htbl⟩ | hpin | ⟨a', hk⟩
  · rw [htbl] at hna
    exact (hna tbl.structName .projTable rfl).elim
  · exact Or.inl hpin
  · have hname : ci.name = keyOf t a := Ix.Kernel.Semantics.Env.find?_name hf
    have haa : a' = a := Core.keyOf_inj htwf ((keptIn_name hk).symm.trans hname)
    rw [haa] at hk
    exact Or.inr hk

/-- **The closure fold with the family form** (`ClosureFoldStatement`). -/
theorem closureFoldStatement (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) :
    ClosureFoldStatement.{u} L := by
  intro calls ρ t g hg6 hg hall ht hunit hfam htwin R R' env famOf₀ famOf adv cont hb hW hSF hadm hrd
    hFam hFA
  obtain ⟨⟨bAddr, hGFC⟩, hRF⟩ := hFam
  have htwf : t.wf = true := wf_of_check ht
  have hspec := closureStore_spec (t := t) (g := g) hadm
  have hC : ClosureCtx.{u} L calls ρ t g R R' (closureStore t g R R') env famOf₀ famOf adv cont
      bAddr :=
    { bnd := hb, walked := hW, fams := hSF, admits := hadm, reads := hrd, checks := hGFC,
      run := hRF, famAdmits := hFA, store := hspec,
      closed := closureStore_usedClosed hadm hb.shape.usedClosed hRF.roleUnitForm,
      noUnit := fun a hu hn => closureStore_none ⟨hu, hn⟩ }
  obtain ⟨env₁, hI, hext, hdone, hframe⟩ := closureFold_run hC htwf hunit hfam htwin
  have hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env₁.find? k = some c :=
    fun h => find_of_ext hext hI.nodup h
  have hsomeFind : ∀ k, (env.find? k).isSome = true → (env₁.find? k).isSome = true := by
    intro k hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hk
    exact Option.isSome_iff_exists.mpr ⟨c, hfind hc⟩
  -- the new non-block records of the closure's store are stored, with their readings
  have newStored : ∀ x cx, New R (closureStore t g R R') x →
      recordOf (closureStore t g R R') x = some cx → ¬ IsBlock cx →
      ∃ ci, env₁.find? (keyOf t x) = some ci ∧ ∃ ci₀,
        Reads t (closureStore t g R R') x ci₀ ∧ StoredAs ci ci₀ := by
    intro x cx hn hcx hnb
    obtain ⟨U, hU, hown, -⟩ := closureUnit_owner hC hn hcx hnb
    obtain ⟨ci, hci, hname, ci₀, hr, hst⟩ := hdone U hU x hown
    refine ⟨ci, ?_, ci₀, hr, hst⟩
    rw [← hname]
    exact find_of_mem_nodup hI.nodup hci
  -- an owned address's unit stores every constant address of the same record
  have ownerStoresAll : ∀ U a, IsClosureUnit R (closureStore t g R R') famOf U →
      FamOwns (closureStore t g R R') famOf U a →
      ∃ D cD, recordOf (closureStore t g R R') D = some cD ∧ ConstAddrOf D cD a ∧
        New R (closureStore t g R R') D ∧
        ∀ y, ConstAddrOf D cD y → StoredAt t env₁ y := by
    intro U a hU hown
    have stored : ∀ y, FamOwns (closureStore t g R R') famOf U y → StoredAt t env₁ y := by
      intro y hy
      obtain ⟨ci, hci, hname, -⟩ := hdone U hU y hy
      exact ⟨ci, hci, hname⟩
    obtain ⟨cU, hcU, hxa | ⟨rb, crb, hfa, hcrb, hxr⟩⟩ := hown
    · exact ⟨U, cU, hcU, hxa, hU.1, fun y hy => stored y ⟨cU, hcU, Or.inl hy⟩⟩
    · obtain ⟨_cb, _crb, _ms, _rs, _, _, _, _, _, hnrb, _⟩ := fam_new hC hfa
      exact ⟨rb, crb, hcrb, hxr, hnrb,
        fun y hy => stored y ⟨cU, hcU, Or.inr ⟨rb, crb, hfa, hcrb, hy⟩⟩⟩
  -- the families before the group are not reselected
  have hf₀ : ∀ B rb, famOf₀ B = some rb → joinFam famOf famOf₀ B = some rb := by
    intro B rb h
    have hnone : famOf B = none := by
      cases hfa : famOf B with
      | none => rfl
      | some rb' =>
        exfalso
        obtain ⟨hnB, -⟩ := hGFC.famCall B rb' hfa
        obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hSF.family B rb h
        have hR := hF.block.record
        rw [hnB.2] at hR
        cases hR
    rw [joinFam_none hnone]
    exact h
  refine ⟨closureStore t g R R', env₁, joinFam famOf famOf₀, hspec.le₁, hspec.le₂, hspec.blobs,
    hspec.units, hext, ?bnd, ?kept, ?fams, hf₀, fun B rb h => joinFam_some h, ?walked⟩
  case bnd =>
    refine ⟨?shape, hI.clause, ?facts⟩
    case shape =>
      exact {
        needsClosed := hb.shape.needsClosed
        bound := hb.shape.bound
        prelude := hb.shape.prelude
        literals := hb.shape.literals
        hashed := closureStore_hashed hadm
        usedClosed := hC.closed
        committed := closureStore_committed hadm
        zeroFree := closureStore_zeroFree hadm
        kept := fun k r a hk hr hkr ha => by
          obtain ⟨ci, hci, hp⟩ := hb.shape.kept k r a hk hr hkr ha
          exact ⟨ci, hfind hci, hp.imp id (keptIn_closureStore hadm)⟩
        reading := ⟨hI.nodup, hI.prov, fun x hx => by
          obtain ⟨ci₀, hr⟩ := hx
          have hr' := hr
          obtain ⟨cx, hcx, hrr⟩ := hr'
          cases hRx : recordOf R x with
          | some c₀ =>
            have hrR := hRF.readsDown _ x ci₀ hspec (Option.isSome_iff_exists.mpr ⟨c₀, hRx⟩) hr
            obtain ⟨ci, hci, hp⟩ := hb.shape.reading.stored x ⟨ci₀, hrR⟩
            refine ⟨ci, hfind hci, hp.imp id ?_⟩
            rintro ⟨ci₁, hr₁, hst⟩
            exact ⟨ci₁, reads_closureStore_of_R hadm hr₁, hst⟩
          | none =>
            have hnb : ¬ IsBlock cx := by
              rintro ⟨ms, hms⟩
              rw [hms] at hrr
              exact hrr
            obtain ⟨ci, hci, ci₁, hr₁, hst⟩ :=
              newStored x cx ⟨Option.isSome_iff_exists.mpr ⟨cx, hcx⟩, hRx⟩ hcx hnb
            exact ⟨ci, hci, Or.inr ⟨ci₁, hr₁, hst⟩⟩⟩
        pins := fun kind ci hci => hext ci (hb.shape.pins kind ci hci)
        preludeKept := fun k r a hk hr hp ha => by
          obtain ⟨ci, hci, hq⟩ := hb.shape.preludeKept k r a hk hr hp ha
          exact ⟨ci, hfind hci, hq.imp id (keptIn_closureStore hadm)⟩
        model := by
          obtain ⟨E, hE⟩ := OpInstall.recordsFor_exists (closureStore_committed hadm)
          obtain ⟨Reg, hR⟩ := hI.clause
          exact claimedEnv_models_of_prefixInv
            (hR E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)).prefixInv
            hI.nodup hI.prov }
    case facts =>
      refine ⟨fun E hE a B c cb ms hfa hrec hown hne hrecB hmuts => ?_,
        opsPinned_findExt hfind hb.facts.opsPinned (fun n hn hs => by
          rw [hI.ops n hn] at hs
          exact hs),
        fun r hr hs => hb.facts.opsAdmitted r hr (by
          have hn : (Ix.Kernel.Key.role r : Core.KKey) ∈ RoleOps.opNames := by
            rw [RoleOps.opNames_eq_map]
            exact List.mem_map.mpr ⟨r, hr, rfl⟩
          rw [hI.ops _ hn] at hs
          exact hs),
        shapes_findExt hfind hb.facts.shapes⟩
      by_cases hsa : StoredAt t env a
      · have hbs := hb.facts.whole E (recordsFor_R_of_closureStore hadm hE) a B c cb ms
          (find_isSome_of_storedAt hsa) hrec hown hne hrecB hmuts
        intro i m hm
        obtain ⟨h1, h2⟩ := hbs i m hm
        exact ⟨hsomeFind _ h1, fun ind j hind hj => hsomeFind _ (h2 ind j hind hj)⟩
      · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hfa
        rcases hframe a (storedAt_of_find hci) with h | ⟨U, hU, hownU⟩
        · exact absurd h hsa
        obtain ⟨D, cD, hcD, haD, hnD, hall⟩ := ownerStoresAll U a hU hownU
        rcases constAddr_record hC.closed hcD haD with ⟨he, hs⟩ | ⟨hbl, P, hP, hPp, hPo⟩
        · exfalso
          rw [← he] at hcD
          have hca : Ix.Cert.recordAt E a = some cD := hE.2.1 a cD hcD
          rw [hca] at hrec
          have hcc : cD = c := Option.some.inj hrec
          rw [← hcc] at hown
          have hown' : Ix.Cert.ownerOf a cD = a := by
            rcases hs with ⟨d, hd⟩ | ⟨r', hd⟩ | ⟨ax, hd⟩ | ⟨q, hd⟩ <;>
              simp [Ix.Cert.ownerOf, hd]
          exact hne (hown.symm.trans hown')
        · have hPa : Ix.Cert.recordAt E a = some P := hE.2.1 a P hP
          rw [hPa] at hrec
          have hcc : P = c := Option.some.inj hrec
          rw [← hcc, hPo] at hown
          rw [← hown] at hrecB ⊢
          have hDE : Ix.Cert.recordAt E D = some cD := hE.2.1 D cD hcD
          rw [hDE] at hrecB
          have hcc' : cD = cb := Option.some.inj hrecB
          rw [← hcc'] at hmuts
          intro i m hm
          exact ⟨find_isSome_of_storedAt (hall _ (Or.inr ⟨ms, i, m, hmuts, hm, Or.inl rfl⟩)),
            fun ind j hind hj => find_isSome_of_storedAt
              (hall _ (Or.inr ⟨ms, i, m, hmuts, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩))⟩
  case kept =>
    have keptAt : ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) →
        ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → ∀ a, t.addressOf? r = some a →
        ∃ ci, env₁.find? (Ix.Kernel.Key.role r) = some ci ∧
          (PinnedBasis ci ∨ KeptIn t (recordOf (closureStore t g R R'))
            (fun y => (closureStore t g R R').blobs.get? y) a ci) := by
      intro r hr hk hnu a ha
      have hkey : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
      obtain ⟨c, hc, hnb, hlog, hlogB, hchk⟩ := hRF.keptRoles r hr hk hnu a ha
      have hnua : ¬ NewUnit t g R R' a := by
        rintro ⟨⟨r', hr', ha', hu⟩, -⟩
        have hs := roleGroup_unit hr' hu
        rw [hs, List.mem_singleton] at hr
        rw [hr] at hnu
        exact hnu hu
      have hc₁ : recordOf (closureStore t g R R') a = some c := by
        rw [recordOf_closureStore hnua]
        exact hc
      rw [← hkey]
      cases hRa : recordOf R a with
      | some c₀ =>
        have e : c₀ = c := rec_eq (recordOf_of_loaded hadm.mono hRa) hc
        rw [e] at hRa
        obtain ⟨n, hn⟩ := hchk (Option.isSome_iff_exists.mpr ⟨c, hRa⟩)
        have hsome := hW.1 a c n hRa hnb hlog
          (fun cb hcb => hlogB cb (recordOf_of_loaded hadm.mono hcb)) hn
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hsome
        exact ⟨ci, hfind hci, (stored_keptIn htwf hb hci).imp id (keptIn_closureStore hadm)⟩
      | none =>
        have hnb' : ¬ IsBlock c := fun ⟨ms, hms⟩ => hnb ms hms
        have hnew : New R (closureStore t g R R') a :=
          ⟨Option.isSome_iff_exists.mpr ⟨c, hc₁⟩, hRa⟩
        obtain ⟨ci, hci, ci₀, hr₀, hst⟩ := newStored a c hnew hc₁ hnb'
        refine ⟨ci, hci, Or.inr ⟨fun c' ax hc' hi => ?_, ci₀, hr₀, hst⟩⟩
        exact (new₁_not_axiomLike hadm hnew hc' (Or.inl ⟨ax, hi⟩)).elim
    exact ⟨fun r hr hk hnu a ha => keptAt r hr (Or.inl hk) hnu a ha,
      fun r hr hp a ha => keptAt r hr (Or.inr hp) (prelude_not_unit r hp) a ha⟩
  case fams =>
    refine ⟨fun B cb hcb hroute hst => ?_, fun B rb h => ?_, fun B rb cb h hcb x hx => ?_,
      fun B rb crb h hcrb => ?_⟩
    · cases hRB : recordOf R B with
      | none =>
        obtain ⟨rb, hrb⟩ :=
          hRF.routeNew _ B hspec ⟨Option.isSome_iff_exists.mpr ⟨cb, rec₁₂ hcb⟩, hRB⟩ hroute
        exact ⟨rb, joinFam_some hrb⟩
      | some cb₀ =>
        have e : cb₀ = cb := rec_eq (recordOf_closureStore_of_R hadm hRB) hcb
        rw [e] at hRB
        have hstR : ∀ x, ConstAddrOf B cb x → StoredAt t env x := by
          intro x hx
          rcases hframe x (hst x hx) with h | ⟨U, hU, hownU⟩
          · exact h
          · exfalso
            obtain ⟨D, cD, hcD, hxD, hnD, -⟩ := ownerStoresAll U x hU hownU
            have e : B = D := constAddr_same hC.closed hcb hcD hx hxD
            rw [← e] at hnD
            have hR := hnD.2
            rw [hRB] at hR
            cases hR
        have hrouteR : Route.blockRoute R B = some true := by
          rw [← blockRoute_closureStore hadm hb.shape.usedClosed hRB]
          exact hroute
        obtain ⟨rb, hrb⟩ := hSF.selected B cb hRB hrouteR hstR
        exact ⟨rb, hf₀ B rb hrb⟩
    · rcases joinFam_cases h with hfa | ⟨-, h₀⟩
      · obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hGFC.family B rb hfa
        obtain ⟨cb', crb', ms', rs', hcb, hcrb, -, -, -, -, -⟩ := fam_new hC hfa
        have e1 : cb' = cb := rec_eq (rec₂₀ hadm (rec₁₂ hcb)) hF.block.record
        have e2 : crb' = crb := rec_eq (rec₂₀ hadm (rec₁₂ hcrb)) hF.record.record
        rw [e1] at hcb
        rw [e2] at hcrb
        exact ⟨cb, ms, crb, rs, flat, familyOfBlock_of_closed hC.closed hcb hcrb hF⟩
      · obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hSF.family B rb h₀
        exact ⟨cb, ms, crb, rs, flat, familyOfBlock_of_closed hC.closed
          (recordOf_closureStore_of_R hadm hF.block.record)
          (recordOf_closureStore_of_R hadm hF.record.record) hF⟩
    · rcases joinFam_cases h with hfa | ⟨-, h₀⟩
      · obtain ⟨cb', crb, ms, rs, hcb', hcrb, -, -, hnB, -, -⟩ := fam_new hC hfa
        have e : cb' = cb := rec_eq hcb' hcb
        rw [e] at hcb'
        obtain ⟨ci, hci, hname, -⟩ := hdone B ⟨hnB, fam_unclaimed hC hfa, x, cb, hcb', Or.inl hx⟩
          x ⟨cb, hcb', Or.inl hx⟩
        exact ⟨ci, hci, hname⟩
      · obtain ⟨cbR, ms, crb, rs, flat, hF⟩ := hSF.family B rb h₀
        have e : cbR = cb := rec_eq (recordOf_closureStore_of_R hadm hF.block.record) hcb
        have hRB := hF.block.record
        rw [e] at hRB
        obtain ⟨ci, hci, hname⟩ := hSF.blockStored B rb cb h₀ hRB x hx
        exact ⟨ci, hext ci hci, hname⟩
    · have hst : ∀ x, ConstAddrOf rb crb x → StoredAt t env₁ x := by
        intro x hx
        rcases joinFam_cases h with hfa | ⟨-, h₀⟩
        · obtain ⟨cb, crb', ms, rs, hcb, hcrb', -, -, hnB, -, -⟩ := fam_new hC hfa
          have e : crb' = crb := rec_eq hcrb' hcrb
          rw [e] at hcrb'
          obtain ⟨ci, hci, hname, -⟩ := hdone B
            ⟨hnB, fam_unclaimed hC hfa, x, cb, hcb, Or.inr ⟨rb, crb, hfa, hcrb', hx⟩⟩
            x ⟨cb, hcb, Or.inr ⟨rb, crb, hfa, hcrb', hx⟩⟩
          exact ⟨ci, hci, hname⟩
        · obtain ⟨cbR, ms, crbR, rs, flat, hF⟩ := hSF.family B rb h₀
          have e : crbR = crb :=
            rec_eq (recordOf_closureStore_of_R hadm hF.record.record) hcrb
          have hRrb := hF.record.record
          rw [e] at hRrb
          obtain ⟨ci, hci, hname⟩ := (hSF.installed B rb crb h₀ hRrb).1 x hx
          exact ⟨ci, hext ci hci, hname⟩
      refine ⟨hst, hI.famInst B rb crb ?_ hcrb hst⟩
      rcases joinFam_cases h with hfa | ⟨-, h₀⟩
      · exact Or.inr hfa
      · exact Or.inl h₀
  case walked =>
    refine ⟨fun x c n hc hnb hlog hlogB hchk => ?_, fun r x hw hgr ha =>
      hsomeFind _ (hW.2 r x hw hgr ha)⟩
    cases hRx : recordOf R x with
    | some c₀ =>
      have e : c₀ = c := rec_eq (recordOf_closureStore_of_R hadm hRx) hc
      rw [e] at hRx
      exact hsomeFind _ (hW.1 x c n hRx hnb hlog
        (fun cb hcb => hlogB cb (recordOf_closureStore_of_R hadm hcb)) hchk)
    | none =>
      obtain ⟨ci, hci, -⟩ := newStored x c ⟨Option.isSome_iff_exists.mpr ⟨c, hc⟩, hRx⟩ hc
        (fun ⟨ms, hms⟩ => hnb ms hms)
      exact Option.isSome_iff_exists.mpr ⟨ci, hci⟩

end IxVM.Refinement.Binding
