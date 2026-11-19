import IxVMRefinement.TwinFamily.StoredTwinRow
import IxVMRefinement.Binding.FamilyReconStore
import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.L1.ConvertExpr
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Core.RomBound

/-! # Closed predecessor set excluding a claimed family record

Constructs, for a modeled block `B` with claimed family record `fam B = some rb` under a witness
environment satisfying `Ix.Kernel.EnvWF envT` and block-wholeness (`BlockStored`), a set `S` of
addresses such that:

* `S` is closed under both `(ReconView.ofStore t E₀)` and `(FlatView.ofStore t E₀)`;
* `B ∈ S`;
* every recursor projection `memberAddr rb j (.recr rc)` of `rb` lies outside `S`.

The set `S` is the union of:
1. addresses stored in `envT` (`StoredAt t envT`);
2. block records in `E₀` whose members and constructors are all stored in `envT` (`BlockStored`);
3. records held by the committed basis store (`Held StoreInhabit.basisStore`);
4. top-walked records of rank at most `rank B`;
5. member projection addresses of top-walked blocks of rank at most `rank B`.

Closure on stored records uses `EnvWF envT` (transferring keys through `Annotates` from `loadedAt`
to the stored constant) and `BlockStored` (through `hWhole`), delegating pinned basis constants to
the self-closed `StoreInhabit.basisStore`. Exclusion of `rb`'s recursors follows from
`FamilyGraph.famFresh` (for the stored and basis arms) and `TopGraph.owner` + `FamilyGraph.famAfter`
(for the top-walked arms). -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Binding (KeyIn read_keys)
open IxVM.Refinement.Binding.FamilyFlat (FlatView Held loadedAt keyAddr keyAddr_keyOf
  indInfoAt ctorTypeAt membersAt indInfoAt_inv ctorTypeAt_inv membersAt_inv
  mem_indcAddrs keyIn_of_loadedAt keyIn_exprInstLevels)
open IxVM.Refinement.Binding.FamilyRecon (ReconView RKeysAt indDataAt ctorAt unfoldAt
  defnAt indDataAt_inv ctorAt_inv unfoldAt_inv defnAt_inv mem_used_of_member)
open IxVM.Refinement.ReaderReads (exprReader_mono)

set_option linter.unusedVariables false

/-! ## Annotation and key-resolution helpers -/

private theorem applyBinderTrace_annotates (md : Ix.Kernel.Level → Ix.Kernel.BinderMeta) :
    ∀ (e : Core.KExpr) (levels : List Core.KLevel) (e' : Core.KExpr) (rest : List Core.KLevel),
      L1.applyBinderTrace md e levels = some (e', rest) →
      Annotates e' e
  | .bvar _, _, _, _, h => by
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; exact .bvar
  | .fvar _ ty, levels, e', rest, h => by
    cases h1 : L1.applyBinderTrace md ty levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨ty', a1⟩ := r1
      simp only [L1.applyBinderTrace, h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact .fvar (applyBinderTrace_annotates md ty levels ty' a1 h1)
  | .sort _, _, _, _, h => by
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; exact .sort
  | .const _ _, _, _, _, h => by
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; exact .const
  | .lit _, _, _, _, h => by
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; exact .lit
  | .app f a, levels, e', rest, h => by
    cases h1 : L1.applyBinderTrace md f levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨f', a1⟩ := r1
      cases h2 : L1.applyBinderTrace md a a1 with
      | none => simp [L1.applyBinderTrace, h1, h2] at h
      | some r2 =>
        obtain ⟨a', a2⟩ := r2
        simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        exact .app (applyBinderTrace_annotates md f levels f' a1 h1)
          (applyBinderTrace_annotates md a a1 a' a2 h2)
  | .lam dom body _, levels, e', rest, h => by
    cases levels with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv rem =>
      cases h1 : L1.applyBinderTrace md dom rem with
      | none => simp [L1.applyBinderTrace, h1] at h
      | some r1 =>
        obtain ⟨dom', a1⟩ := r1
        cases h2 : L1.applyBinderTrace md body a1 with
        | none => simp [L1.applyBinderTrace, h1, h2] at h
        | some r2 =>
          obtain ⟨body', a2⟩ := r2
          simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact .lam (applyBinderTrace_annotates md dom rem dom' a1 h1)
            (applyBinderTrace_annotates md body a1 body' a2 h2)
  | .forallE dom body _, levels, e', rest, h => by
    cases levels with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv rem =>
      cases h1 : L1.applyBinderTrace md dom rem with
      | none => simp [L1.applyBinderTrace, h1] at h
      | some r1 =>
        obtain ⟨dom', a1⟩ := r1
        cases h2 : L1.applyBinderTrace md body a1 with
        | none => simp [L1.applyBinderTrace, h1, h2] at h
        | some r2 =>
          obtain ⟨body', a2⟩ := r2
          simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact .forallE (applyBinderTrace_annotates md dom rem dom' a1 h1)
            (applyBinderTrace_annotates md body a1 body' a2 h2)
  | .letE ty val body _, levels, e', rest, h => by
    cases h1 : L1.applyBinderTrace md ty levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨_, a1⟩ := r1
      cases h2 : L1.applyBinderTrace md val a1 with
      | none => simp [L1.applyBinderTrace, h1, h2] at h
      | some r2 =>
        obtain ⟨val', a2⟩ := r2
        cases h3 : L1.applyBinderTrace md body a2 with
        | none => simp [L1.applyBinderTrace, h1, h2, h3] at h
        | some r3 =>
          obtain ⟨body', a3⟩ := r3
          simp only [L1.applyBinderTrace, h1, h2, h3, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact .letE (L1.annotates_instantiate1Lift
            (applyBinderTrace_annotates md body a2 body' a3 h3)
            (applyBinderTrace_annotates md val a1 val' a2 h2) 0)
  | .proj s i inner, levels, e', rest, h => by
    cases h1 : L1.applyBinderTrace md inner levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨inner', a1⟩ := r1
      simp only [L1.applyBinderTrace, h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact .proj (applyBinderTrace_annotates md inner levels inner' a1 h1)

private theorem loadedAt_annotates {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {nl : Nat} {root : F} {e : Ixon.Expr} {v : Core.KExpr}
    (h : loadedAt t blob src self nl root e = some v) :
    ∃ e₀, (exprReader t blob src id self).read e = .ok e₀ ∧ Annotates v e₀ := by
  unfold loadedAt at h
  cases hr : (exprReader t blob src id self).read e with
  | error _ => simp [hr, Except.toOption] at h
  | ok e₀ =>
    simp only [hr, Except.toOption, LoadedReads.canonAnn] at h
    cases hp : L1.binderRootPlan (LoadedReads.canonTree src.binders.toList)
        src.sharing.toList root e with
    | none => simp [hp] at h
    | some plan =>
      simp only [hp, Option.bind_some] at h
      cases ha : L1.applyBinderTrace
          (fun level => Core.bmeta (L1.invPosLevel (List.range nl) level)) e₀ plan with
      | none => simp [ha] at h
      | some res =>
        obtain ⟨v', rest⟩ := res
        simp only [ha, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨e₀, rfl, applyBinderTrace_annotates _ e₀ plan v' rest ha⟩

private theorem annotates_keyIn_mp {e₁ e₂ e₀ : Core.KExpr}
    (h₁ : Annotates e₁ e₀) (h₂ : Annotates e₂ e₀) {k : Core.KKey} :
    KeyIn k e₁ → KeyIn k e₂ := by
  induction h₁ generalizing e₂ with
  | bvar =>
    cases h₂; intro hk; cases hk
  | fvar _ ih =>
    cases h₂ with
    | fvar ht₂ =>
      intro hk; cases hk with | fvarTy h => exact .fvarTy (ih ht₂ h)
  | sort =>
    cases h₂; intro hk; cases hk
  | const =>
    cases h₂; intro hk; exact hk
  | lit =>
    cases h₂; intro hk; cases hk
  | app _ _ ihf iha =>
    cases h₂ with
    | app hf₂ ha₂ =>
      intro hk
      cases hk with
      | appFn h => exact .appFn (ihf hf₂ h)
      | appArg h => exact .appArg (iha ha₂ h)
  | lam _ _ iht ihb =>
    cases h₂ with
    | lam ht₂ hb₂ =>
      intro hk
      cases hk with
      | lamTy h => exact .lamTy (iht ht₂ h)
      | lamBody h => exact .lamBody (ihb hb₂ h)
  | forallE _ _ iht ihb =>
    cases h₂ with
    | forallE ht₂ hb₂ =>
      intro hk
      cases hk with
      | allTy h => exact .allTy (iht ht₂ h)
      | allBody h => exact .allBody (ihb hb₂ h)
  | proj _ ih =>
    cases h₂ with
    | proj he₂ =>
      intro hk
      cases hk with
      | proj => exact .proj _ _
      | projBody h => exact .projBody (ih he₂ h)
  | letE _ ih =>
    cases h₂ with
    | letE h₂' => exact ih h₂'

private theorem find_isSome_of_constsResolve_keyIn {env : Ix.Kernel.Env .anon}
    {e : Core.KExpr} (hres : e.constsResolve env = true) {k : Core.KKey}
    (hk : KeyIn k e) : (env.find? k).isSome = true := by
  induction hk with
  | const _ => simpa [Ix.Kernel.Expr.constsResolve] using hres
  | proj _ _ =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact hres.1
  | projBody _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.2
  | fvarTy _ ih => exact ih hres
  | appFn _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.1
  | appArg _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.2
  | lamTy _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.1
  | lamBody _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.2
  | allTy _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.1
  | allBody _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.2
  | letTy _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.1.1
  | letVal _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.1.2
  | letBody _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact ih hres.2

private theorem read_key_is_keyOf {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ i k, self i = some (Except.ok k) → ∃ z, k = keyOf t z)
    {e : Ixon.Expr} (he : ∀ i ∈ exprRefIdxs e, i ∈ usedRefIdxs src) {e₀ : Core.KExpr}
    (hr : (exprReader t blob src id self).read e = .ok e₀) {k : Core.KKey} (hk : KeyIn k e₀) :
    ∃ z, k = keyOf t z :=
  read_keys ht (P := fun k => ∃ z, k = keyOf t z)
    (fun _ _ a _ => ⟨a, rfl⟩) hself he hr k hk

private theorem blockSelf_is_keyOf (t : Ix.Kernel.RoleTable) (b : _root_.Address)
    (ms : Array Ixon.MutConst) :
    ∀ i k, blockSelf t b ms i = some (Except.ok k) → ∃ z, k = keyOf t z := by
  intro i k hs
  unfold blockSelf at hs
  cases hmj : ms[i]? with
  | none => rw [hmj] at hs; cases hs
  | some mj =>
    rw [hmj] at hs
    cases Except.ok.inj (Option.some.inj hs)
    exact ⟨memberAddr b i mj, rfl⟩

private theorem soloSelf_is_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    ∀ i k, soloSelf t a i = some (Except.ok k) → ∃ z, k = keyOf t z := by
  intro i k hs
  unfold soloSelf at hs
  split at hs
  · cases Except.ok.inj (Option.some.inj hs)
    exact ⟨a, rfl⟩
  · cases hs

/-! ## Committed basis store agreement and closure -/

private theorem pinned_names_basisRole (kind : Ix.Kernel.BasisKind) :
    ∀ n ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).map (·.name),
      n ∈ TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := by
  cases kind <;> decide

private theorem basisRoleOrder_sub_prelude :
    ∀ r ∈ TableInhabit.basisRoleOrder, r ∈ preludeRoles := by
  decide

private theorem basisRole_hasKey :
    TableInhabit.basisRoleOrder.all (fun r =>
      match RoleVal.committedDefaultRoleTable.addressOf? r with
      | some a => StoreInhabit.hasKey a
      | none => false) = true := by
  decide +kernel

private theorem basisRole_addr_eq {t : Ix.Kernel.RoleTable} (hpre : PreludePinned t)
    {r : Ix.Kernel.Role} (hr : r ∈ TableInhabit.basisRoleOrder) :
    t.addressOf? r = RoleVal.committedDefaultRoleTable.addressOf? r := by
  obtain ⟨b₀, t₀, hdef, hadm, heq⟩ := hpre
  rw [heq r (basisRoleOrder_sub_prelude r hr),
    RoleVal.admitBinding_committedDefault hdef hadm]

private theorem held_basisStore_of_pinned {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    (hpre : PreludePinned t) {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (hname : ci.name = keyOf t a) (hpin : PinnedBasis ci) :
    Held StoreInhabit.basisStore a := by
  obtain ⟨kind, hci⟩ := hpin
  obtain ⟨r, hr, hrk⟩ := List.mem_map.mp
    (pinned_names_basisRole kind ci.name (List.mem_map.mpr ⟨ci, hci, rfl⟩))
  have had : t.addressOf? r = some a :=
    Core.addressOf_of_keyOf htwf (by rw [LoadedReads.keyOf_eq]; exact hname.symm.trans hrk.symm)
  rw [basisRole_addr_eq hpre hr] at had
  have hall := List.all_eq_true.mp basisRole_hasKey r hr
  rw [had] at hall
  exact StoreInhabit.isSome_of_hasKey hall

private theorem basisRole_storedAt {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (htwf : t.wf = true) {r : Ix.Kernel.Role} (hr : r ∈ TableInhabit.basisRoleOrder)
    {a : _root_.Address} (ha : t.addressOf? r = some a) : StoredAt t envT a := by
  obtain ⟨ci, hfind, kind, hci⟩ := StoreInhabit.basisEnv_find hr
  exact storedAt_of_role htwf ha (hshape.pins kind ci hci)
    (Ix.Kernel.Semantics.Env.find?_name hfind)

private theorem recordAt_E_of_basisStore {R E : Ixon.Env} (hRF : RecordsFor R E)
    {a : _root_.Address} {c : Ixon.Constant} (h : recordOf StoreInhabit.basisStore a = some c) :
    Ix.Cert.recordAt E a = some c := by
  have hmem := StoreInhabit.store_record_inv h
  have hsub := StoreInhabit.basisRows_sub (a, c) hmem
  have hcm : (a, Ixon.serConstant c) ∈ committedRows := by
    rw [StoreInhabit.committedRows_eq]
    exact List.mem_map.mpr ⟨(a, c), hsub, rfl⟩
  obtain ⟨lc, hget, hraw⟩ := hRF.2.2.2 (a, Ixon.serConstant c) hcm
  have hdec : Ixon.deConstantExact lc.rawBytes = .ok c := by
    rw [hraw]
    exact (ClosedFacts.committedPrelude_rows (a, c) hsub).2
  have hrecE : recordOf E a = some c := by
    unfold recordOf
    rw [hget, Option.bind_some, hdec]
    rfl
  rw [← recordOf_eq_recordAt_of_decoded hRF.1 a]
  exact hrecE

private theorem basisStore_eq_of_held {R E E₀ : Ixon.Env} (hRF : RecordsFor R E)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    {a : _root_.Address} {c : Ixon.Constant} (ha : Held StoreInhabit.basisStore a)
    (hc : recordOf E₀ a = some c) : recordOf StoreInhabit.basisStore a = some c := by
  obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp ha
  have h1 := recordAt_E_of_basisStore hRF hcb
  have h2 := hrun a c hc
  have heq : cb = c := Option.some.inj (h1.symm.trans h2)
  rwa [heq] at hcb

private theorem keys_held_basisStore_of_loaded {t : Ix.Kernel.RoleTable} {R E E₀ : Ixon.Env}
    (ht : t.check = .ok ()) (htwf : t.wf = true) (hRF : RecordsFor R E)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    {src : Ixon.Constant} {y0 : _root_.Address}
    (hsrc : recordOf StoreInhabit.basisStore y0 = some src)
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ j k, self j = some (Except.ok k) →
      ∃ z, Held StoreInhabit.basisStore z ∧ k = keyOf t z)
    {e : Ixon.Expr} (he : ∀ j ∈ exprRefIdxs e, j ∈ usedRefIdxs src)
    {blob : _root_.Address → Option ByteArray} {nl : Nat} {root : F} {v : Core.KExpr}
    (h : loadedAt t blob src self nl root e = some v) :
    ∀ k, KeyIn k v → ∀ a, keyAddr t k = some a → Held StoreInhabit.basisStore a := by
  intro k hk a ha
  obtain ⟨e₀, hr₀, hk₀⟩ := keyIn_of_loadedAt h hk
  obtain ⟨z, hz, rfl⟩ := read_keys ht
    (P := fun k => ∃ z, Held StoreInhabit.basisStore z ∧ k = keyOf t z)
    (fun j hj y hy => ⟨y, (StoreInhabit.store_usedClosed.1 y0 src hsrc).2 j hj y hy, rfl⟩)
    hself he hr₀ k hk₀
  have eq : a = z := Option.some.inj (ha.symm.trans (keyAddr_keyOf htwf z))
  rwa [eq]

private theorem blockSelf_held_basisStore {t : Ix.Kernel.RoleTable}
    {b : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hcb : recordOf StoreInhabit.basisStore b = some cb) (hci : cb.info = .muts ms) :
    ∀ j k, blockSelf t b ms j = some (Except.ok k) →
      ∃ z, Held StoreInhabit.basisStore z ∧ k = keyOf t z := by
  intro j k hs
  unfold blockSelf at hs
  cases hmj : ms[j]? with
  | none => rw [hmj] at hs; cases hs
  | some mj =>
    rw [hmj] at hs
    cases Except.ok.inj (Option.some.inj hs)
    exact ⟨_, Option.isSome_iff_exists.mpr
      ⟨_, (StoreInhabit.store_usedClosed.2 b cb ms hcb hci j mj hmj).1⟩, rfl⟩

private theorem flat_closedOn_basisStore {t : Ix.Kernel.RoleTable} {R E E₀ : Ixon.Env}
    (ht : t.check = .ok ()) (htwf : t.wf = true) (hRF : RecordsFor R E)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c) :
    (FlatView.ofStore t E₀).ClosedOn (Held StoreInhabit.basisStore) where
  ciBlk a i ha h := by
    obtain ⟨c, p, _, _, _, hc, hci, -, -, -, rfl⟩ :=
      indInfoAt_inv (h : indInfoAt E₀ a = some (some i))
    have hcB := basisStore_eq_of_held hRF hrun ha hc
    have h1 := (StoreInhabit.store_usedClosed.1 a c hcB).1
    simp only [Ix.Cert.ownerOf, hci] at h1
    exact h1
  members b ms hb h := by
    obtain ⟨cb, arr, hcb, hci, rfl⟩ := membersAt_inv (h : membersAt E₀ b = some ms)
    have hcbB := basisStore_eq_of_held hRF hrun hb hcb
    intro a ha
    obtain ⟨i, m, hm, rfl⟩ := mem_indcAddrs arr.toList 0 ha
    have hm' : arr[i]? = some m := by simpa only [Array.getElem?_toList] using hm
    rw [Nat.zero_add]
    exact Option.isSome_iff_exists.mpr
      ⟨_, (StoreInhabit.store_usedClosed.2 b cb arr hcbB hci i m hm').1⟩
  ctorType b i c ty hb h := by
    obtain ⟨cb, ms, ind, ctor, hcb, hci, hm, hct, hr⟩ :=
      ctorTypeAt_inv (h : ctorTypeAt t E₀ b i c = some ty)
    have hcbB := basisStore_eq_of_held hRF hrun hb hcb
    have hcmem : ctor ∈ ind.ctors.toList :=
      List.mem_of_getElem? (show ind.ctors.toList[c]? = some ctor by
        rw [Array.getElem?_toList]; exact hct)
    exact keys_held_basisStore_of_loaded ht htwf hRF hrun hcbB
      (blockSelf_held_basisStore hcbB hci)
      (fun j hj => mem_used_of_member hci hm j
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ctor, hcmem, hj⟩))) hr

private theorem recon_closedOn_basisStore {t : Ix.Kernel.RoleTable} {R E E₀ : Ixon.Env}
    (ht : t.check = .ok ()) (htwf : t.wf = true) (hRF : RecordsFor R E)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c) :
    (ReconView.ofStore t E₀).ClosedOn (Held StoreInhabit.basisStore) where
  indBlk a i ha h := by
    obtain ⟨c, p, _, _, _, hc, hci, -, -, -, -, hblk⟩ :=
      indDataAt_inv (h : indDataAt t E₀ a = some (some i))
    have hcB := basisStore_eq_of_held hRF hrun ha hc
    have h1 := (StoreInhabit.store_usedClosed.1 a c hcB).1
    simp only [Ix.Cert.ownerOf, hci] at h1
    rwa [hblk]
  indTy a i ha h := by
    obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, hr, -⟩ :=
      indDataAt_inv (h : indDataAt t E₀ a = some (some i))
    have hpb : Held StoreInhabit.basisStore p.block := by
      have h1 := (StoreInhabit.store_usedClosed.1 a c (basisStore_eq_of_held hRF hrun ha hc)).1
      simp only [Ix.Cert.ownerOf, hci] at h1
      exact h1
    have hcbB := basisStore_eq_of_held hRF hrun hpb hcb
    exact keys_held_basisStore_of_loaded ht htwf hRF hrun hcbB
      (blockSelf_held_basisStore hcbB hcbi)
      (fun j hj => mem_used_of_member hcbi hm j (List.mem_append_left _ hj)) hr
  ctorTy b i c ty np hb h := by
    obtain ⟨cb, ms, ind, ctor, hcb, hcbi, hm, hct, hr⟩ :=
      ctorAt_inv (h : ctorAt t E₀ b i c = some (ty, np))
    have hcbB := basisStore_eq_of_held hRF hrun hb hcb
    have hcmem : ctor ∈ ind.ctors.toList :=
      List.mem_of_getElem? (show ind.ctors.toList[c]? = some ctor by
        rw [Array.getElem?_toList]; exact hct)
    exact keys_held_basisStore_of_loaded ht htwf hRF hrun hcbB
      (blockSelf_held_basisStore hcbB hcbi)
      (fun j hj => mem_used_of_member hcbi hm j
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ctor, hcmem, hj⟩))) hr
  unfold k us v hk h := by
    obtain ⟨a, n, w, hka, hd, rfl⟩ := unfoldAt_inv (h : unfoldAt t E₀ k us = some (some v))
    have ha : Held StoreInhabit.basisStore a := hk a hka
    obtain ⟨c, hc, hdef⟩ := defnAt_inv hd
    have hcB := basisStore_eq_of_held hRF hrun ha hc
    intro k' hk' a' ha'
    have hk'' := keyIn_exprInstLevels w hk'
    rcases hdef with ⟨d, hci, hr⟩ | ⟨p, cb, ms, d, hci, hcb, hcbi, hm, hr⟩
    · refine keys_held_basisStore_of_loaded ht htwf hRF hrun hcB ?_ (fun j hj => ?_) hr
        k' hk'' a' ha'
      · intro j k hs
        unfold soloSelf at hs
        split at hs
        · cases Except.ok.inj (Option.some.inj hs)
          exact ⟨a, ha, rfl⟩
        · cases hs
      · simp only [usedRefIdxs, hci]
        exact List.mem_append_right _ (List.mem_append_right _ hj)
    · have hpb : Held StoreInhabit.basisStore p.block := by
        have h1 := (StoreInhabit.store_usedClosed.1 a c hcB).1
        simp only [Ix.Cert.ownerOf, hci] at h1
        exact h1
      have hcbB := basisStore_eq_of_held hRF hrun hpb hcb
      exact keys_held_basisStore_of_loaded ht htwf hRF hrun hcbB
        (blockSelf_held_basisStore hcbB hcbi)
        (fun j hj => mem_used_of_member hcbi hm j (List.mem_append_right _ hj)) hr k' hk'' a' ha'

/-! ## Constructor-projection collision freedom -/

private theorem ctorProj_eq_of_noCollision {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hRS : LoadedReads.RunStore calls E₀) (hdecE : L1.EnvDecoded E)
    (hgood : Core.Good ⟨E, envT, t, lim⟩ calls)
    {b : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i c : Nat} {ind : Ixon.Inductive} {ctor : Ixon.Constructor} {cx : Ixon.Constant}
    (hrec_b : recordOf E₀ b = some cb) (hms : cb.info = .muts ms)
    (hm : ms[i]? = some (.indc ind)) (hc : ind.ctors[c]? = some ctor)
    (hrec_x : Ix.Cert.recordAt E (ctorAddr b i c) = some cx) :
    cx = constructorProjection b i c ∧ i < UInt64.size ∧ c < UInt64.size := by
  -- Extract raw bytes of `b` in `E₀`
  cases hget_b : E₀.consts.get? b with
  | none =>
    unfold recordOf at hrec_b; rw [hget_b] at hrec_b; cases hrec_b
  | some lc_b =>
    obtain ⟨cb', -, hde_b⟩ := hRS.decoded b lc_b hget_b
    have hcb_eq : cb' = cb := by
      unfold recordOf at hrec_b
      rw [hget_b, Option.bind_some, hde_b] at hrec_b
      exact Option.some.inj hrec_b
    subst hcb_eq
    obtain ⟨hhash_b, hb_hash⟩ := hRS.loaded.1 b lc_b hget_b
    -- Bound `i` and `c` using `Bounded calls` + `deConstantExact_resource_bound`
    obtain ⟨cl, hcl, hcl_name, input, hargs, hrep⟩ := hhash_b
    have hlen_b : lc_b.rawBytes.data.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hgood.2 hcl (by rw [hargs]; exact List.mem_cons_self ..) hrep
    have hres_b : cb'.resourceSize ≤ 2 * lc_b.rawBytes.size :=
      Ixon.Verify.ConstantBounds.deConstantExact_resource_bound lc_b.rawBytes cb' hde_b
    have hsz_eq : lc_b.rawBytes.size = lc_b.rawBytes.data.toList.length := by
      rw [Array.length_toList]; rfl
    have hi_lt_ms : i < ms.size := (Array.getElem?_eq_some_iff.mp hm).1
    have hc_lt_ct : c < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hc).1
    have hms_le : ms.size ≤ cb'.resourceSize := Claim.muts_size_le hms
    have hct_le : ind.ctors.size ≤ cb'.resourceSize :=
      Claim.ctors_size_le hms (by rwa [Array.getElem?_toList])
    have hi_u64 : i < UInt64.size := by change i < 2 ^ 64; omega
    have hc_u64 : c < UInt64.size := by change c < 2 ^ 64; omega
    -- Extract raw bytes of `ctorAddr b i c` in `E`
    have hrec_x' : recordOf E (ctorAddr b i c) = some cx :=
      (recordOf_eq_recordAt_of_decoded hdecE (ctorAddr b i c)).trans hrec_x
    cases hget_x : E.consts.get? (ctorAddr b i c) with
    | none =>
      unfold recordOf at hrec_x'; rw [hget_x] at hrec_x'; cases hrec_x'
    | some lc_x =>
      have hde_x : Ixon.deConstantExact lc_x.rawBytes = .ok cx := by
        unfold recordOf at hrec_x'
        rw [hget_x, Option.bind_some] at hrec_x'
        cases hd : Ixon.deConstantExact lc_x.rawBytes with
        | error _ => rw [hd] at hrec_x'; cases hrec_x'
        | ok c' =>
          rw [hd] at hrec_x'
          exact congrArg Except.ok (Option.some.inj hrec_x')
      let image := Ixon.serConstant (constructorProjection b i c)
      have himg_eq : image = lc_x.rawBytes := by
        by_contra hne
        apply hgood.1
        refine Or.inr (Or.inl ⟨ctorAddr b i c, lc_x.rawBytes, image, lc_b.rawBytes, cb', ms,
          Or.inl (Or.inl ⟨lc_x, hget_x, rfl⟩), ⟨cl, hcl, hcl_name, input, hargs, hrep⟩, hde_b, hms,
          Or.inr ⟨i.toUInt64, c.toUInt64, by rw [hb_hash]; rfl⟩, hne, rfl⟩)
      have hb_hash_sz : b.hash.size = 32 := by
        rw [← hb_hash]
        cases lc_b.rawBytes with
        | mk arr =>
          have h := L1.blake3Pure_eq arr.toList
          simp only [Array.toArray_toList] at h
          rw [h]
          exact (Blake3.Pure.digest arr.toList).size_toArray
      have hwf_cprj : (constructorProjection b i c).wireWF := by
        unfold constructorProjection
        rw [L1.emptyTablesConstant_wireWF]
        exact hb_hash_sz
      have hde_img : Ixon.deConstantExact image = .ok (constructorProjection b i c) :=
        Ixon.Verify.deConstantExact_serConstant _ hwf_cprj
      rw [← himg_eq, hde_img] at hde_x
      exact ⟨(Except.ok.inj hde_x).symm, hi_u64, hc_u64⟩

/-! ## Closed predecessor set construction -/

/-- **Predecessor set for a modeled block `B`**: stored constants in `envT`, whole-stored blocks
in `E₀`, committed basis records, top-walked records of rank at most `rank B`, and member
projection addresses of top-walked blocks of rank at most `rank B`. -/
def GraphPredSet (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat) (B : _root_.Address)
    (a : _root_.Address) : Prop :=
  StoredAt t envT a ∨
  (∃ cb ms, recordOf E₀ a = some cb ∧ cb.info = .muts ms ∧ BlockStored t envT a ms) ∨
  Held StoreInhabit.basisStore a ∨
  (Top a ∧ rank a ≤ rank B) ∨
  (∃ b cb ms i m, Top b ∧ rank b ≤ rank B ∧ recordOf E₀ b = some cb ∧ cb.info = .muts ms ∧
    ms[i]? = some m ∧ a = memberAddr b i m)

private theorem graphPredSet_of_top_used {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {B : _root_.Address}
    (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {a z : _root_.Address} (hTa : Top a) (hrk : rank a ≤ rank B) (hu : UsedRef E₀ a z) :
    GraphPredSet t envT E₀ Top rank B z := by
  rcases hG.closed a z hTa hu with ⟨hTz, hrkz⟩ | hcov
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTz, Nat.le_trans (Nat.le_of_lt hrkz) hrk⟩)))
  · exact Or.inl (covered_stored hshape htwf hcov)

private theorem graphPredSet_of_top_block_loaded {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {B : _root_.Address}
    (ht : t.check = .ok ()) (htwf : t.wf = true)
    (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    {b : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hTb : Top b) (hrk : rank b ≤ rank B) (hcb : recordOf E₀ b = some cb)
    (hci : cb.info = .muts ms) {e : Ixon.Expr}
    (he : ∀ j ∈ exprRefIdxs e, j ∈ usedRefIdxs cb)
    {nl : Nat} {root : F} {v : Core.KExpr}
    (h : loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t b ms) nl root e = some v) :
    ∀ k, KeyIn k v → ∀ a, keyAddr t k = some a → GraphPredSet t envT E₀ Top rank B a := by
  intro k hk a ha
  obtain ⟨e₀, hr₀, hk₀⟩ := keyIn_of_loadedAt h hk
  obtain ⟨z, hz, rfl⟩ := read_keys ht
    (P := fun k => ∃ z, GraphPredSet t envT E₀ Top rank B z ∧ k = keyOf t z)
    (fun j hj y hy => ⟨y, graphPredSet_of_top_used hG hshape htwf hTb hrk ⟨cb, j, hcb, hj, hy⟩, rfl⟩)
    (fun j k hs => by
      unfold blockSelf at hs
      cases hmj : ms[j]? with
      | none => rw [hmj] at hs; cases hs
      | some mj =>
        rw [hmj] at hs
        cases Except.ok.inj (Option.some.inj hs)
        exact ⟨memberAddr b j mj,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨b, cb, ms, j, mj, hTb, hrk, hcb, hci, hmj, rfl⟩))), rfl⟩)
    he hr₀ k hk₀
  have eq : a = z := Option.some.inj (ha.symm.trans (keyAddr_keyOf htwf z))
  rwa [eq]

private theorem storedAt_provenance {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (ht : t.check = .ok ()) (htwf : t.wf = true) {a : _root_.Address} (hst : StoredAt t envT a) :
    ∃ ci, envT.find? (keyOf t a) = some ci ∧
      (Held StoreInhabit.basisStore a ∨
        KeptIn t (recordOf R) (fun y => R.blobs.get? y) a ci) := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨ci, hfind⟩ := Option.isSome_iff_exists.mp (find_isSome_of_storedAt hst)
  have hname : ci.name = keyOf t a := Ix.Kernel.Semantics.Env.find?_name hfind
  obtain ⟨hclaimed, hna⟩ := seed_claimed hfind
  rcases hshape.reading.provenance ci hclaimed with ⟨tbl, htbl⟩ | hpin | ⟨a', hkept⟩
  · rw [htbl] at hna
    exact absurd rfl (hna tbl.structName .projTable)
  · exact ⟨ci, hfind, Or.inl (held_basisStore_of_pinned htwf hshape.prelude hname hpin)⟩
  · have haa : a' = a := keyOf_inj hroles ((keptIn_name hkept).symm.trans hname)
    exact ⟨ci, hfind, Or.inr (haa ▸ hkept)⟩

private theorem storedAt_of_envWF_annot {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    (ht : t.check = .ok ()) (htwf : t.wf = true)
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ i k, self i = some (Except.ok k) → ∃ z, k = keyOf t z)
    {e : Ixon.Expr} (he : ∀ i ∈ exprRefIdxs e, i ∈ usedRefIdxs src)
    {nl : Nat} {root : F} {v e₀ ci_e : Core.KExpr}
    (hld : loadedAt t blob src self nl root e = some v)
    (he0 : (exprReader t blob src id self).read e = .ok e₀)
    (hann_ci : Annotates ci_e e₀) (hres : ci_e.constsResolve envT = true) :
    ∀ k, KeyIn k v → ∀ a, keyAddr t k = some a → StoredAt t envT a := by
  obtain ⟨e₀', hr₀', hann_v⟩ := loadedAt_annotates hld
  have heq : e₀' = e₀ := Except.ok.inj (hr₀'.symm.trans he0)
  subst heq
  intro k hk a ha
  have hk_ci : KeyIn k ci_e := annotates_keyIn_mp hann_v hann_ci hk
  have hfind_some : (envT.find? k).isSome = true :=
    find_isSome_of_constsResolve_keyIn hres hk_ci
  obtain ⟨z, rfl⟩ := read_key_is_keyOf ht hself he hr₀' (keyIn_of_loadedAt hld hk |> fun ⟨_, hr1, hk1⟩ =>
    by rw [Except.ok.inj (hr1.symm.trans hr₀')] at hk1; exact hk1)
  have eq : a = z := Option.some.inj (ha.symm.trans (keyAddr_keyOf htwf z))
  subst eq
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hfind_some
  exact storedAt_of_find hci

/-- **Closed predecessor set for a modeled block `B` with claimed family record `rb`**, given
witness well-formedness (`EnvWF envT`) and block-wholeness (`hWhole`). -/
theorem graphStoreClosed_of_envWF
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    (hEnvWF : Ix.Kernel.EnvWF envT)
    (hWhole : ∀ E', RecordsFor R E' →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E' a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E' B = some cb → cb.info = .muts ms →
        BlockStored t envT B ms)
    {B rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hfam : fam B = some rb) (hrb : FamRecRecord E₀ rb crb rs) :
    ∃ S : _root_.Address → Prop,
      (ReconView.ofStore t E₀).ClosedOn S ∧
      (FlatView.ofStore t E₀).ClosedOn S ∧
      S B ∧
      (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc))) := by
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hFG := hFR.graph
  have hTB : Top B := hFG.famBlock B rb hfam
  let S := GraphPredSet t envT E₀ Top rank B
  have hF_basis := flat_closedOn_basisStore ht htwf hctx.recordsFor hctx.runRecord
  have hR_basis := recon_closedOn_basisStore ht htwf hctx.recordsFor hctx.runRecord
  -- Helper: `E`-agreement between `R` and `E₀`
  have hRE₀_eq : ∀ a cR c₀, recordOf R a = some cR → recordOf E₀ a = some c₀ → cR = c₀ := by
    intro a cR c₀ h1 h2
    exact Option.some.inj ((hctx.recordsFor.2.1 a cR h1).symm.trans (hctx.runRecord a c₀ h2))
  -- Helper: `ctorType` / `ctorTy` closure for `b ∈ S`
  have hCtor_keys : ∀ b i c cb ms ind ctor ty,
      S b → recordOf E₀ b = some cb → cb.info = .muts ms →
      ms[i]? = some (.indc ind) → ind.ctors[c]? = some ctor →
      loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t b ms) ctor.lvls.toNat
        (Binding.FamilyFlat.mutsRoot ms i + 1 + ((c : Nat) : F)) ctor.typ = some ty →
      ∀ k, KeyIn k ty → ∀ a, keyAddr t k = some a → S a := by
    intro b i c cb ms ind ctor ty hb hcb hcbi hm hct hr
    have hcmem : ctor ∈ ind.ctors.toList :=
      List.mem_of_getElem? (show ind.ctors.toList[c]? = some ctor by
        rw [Array.getElem?_toList]; exact hct)
    have he_ctor : ∀ j ∈ exprRefIdxs ctor.typ, j ∈ usedRefIdxs cb :=
      fun j hj => mem_used_of_member hcbi hm j
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ctor, hcmem, hj⟩))
    rcases hb with hst_b | ⟨cb', ms', hcb', hcbi', hbs⟩ | hbas_b | ⟨hTb, hrkb⟩ |
        ⟨b', cb', ms', i', m', hTb', _, hcb', hcbi', hm', rfl⟩
    · -- `StoredAt t envT b` on a block: either basis or impossible via `ReadsRecord (.muts _)`
      obtain ⟨ci, -, hbas | hkept⟩ := storedAt_provenance hctx.shape ht htwf hst_b
      · intro k hk a ha
        exact Or.inr (Or.inr (Or.inl (hF_basis.ctorType b i c ty hbas
          (by simp only [FlatView.ofStore, ctorTypeAt, hcb, hcbi, hm, hct, hr]) k hk a ha)))
      · obtain ⟨-, ci₀, ⟨cR, hcR, hread⟩, -⟩ := hkept
        have hceq := hRE₀_eq b cR cb hcR hcb
        subst cR
        rw [hcbi] at hread
        exact False.elim hread
    · -- `BlockStored t envT b ms`
      have hcb_eq : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
      subst cb'
      have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcbi'.symm.trans hcbi)
      subst ms'
      have hc_lt : c < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
      have hst_x : StoredAt t envT (ctorAddr b i c) := by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp ((hbs i (.indc ind) hm).2 ind c rfl hc_lt)
        exact storedAt_of_find hci
      obtain ⟨ci, hfind_ci, hbas_x | hkept_x⟩ := storedAt_provenance hctx.shape ht htwf hst_x
      · -- Constructor projection in `basisStore` -> owner `b` in `basisStore`
        obtain ⟨cx, hcx_bas⟩ := Option.isSome_iff_exists.mp hbas_x
        have hcx_E := recordAt_E_of_basisStore hctx.recordsFor hcx_bas
        obtain ⟨hcx_eq, -, -⟩ := ctorProj_eq_of_noCollision hWc.runStore hctx.recordsFor.1
          (hctx.good envT lim) hcb hcbi hm hct hcx_E
        subst cx
        have hbas_b : Held StoreInhabit.basisStore b := by
          have h1 := (StoreInhabit.store_usedClosed.1 (ctorAddr b i c)
            (constructorProjection b i c) hcx_bas).1
          simpa [Ix.Cert.ownerOf, constructorProjection] using h1
        intro k hk a ha
        exact Or.inr (Or.inr (Or.inl (hF_basis.ctorType b i c ty hbas_b
          (by simp only [FlatView.ofStore, ctorTypeAt, hcb, hcbi, hm, hct, hr]) k hk a ha)))
      · -- Constructor projection kept from `R` -> `EnvWF envT`
        obtain ⟨-, ci₀, ⟨cx_R, hcx_R, hread_x⟩, hstAs⟩ := hkept_x
        obtain ⟨hcx_eq, hi_u64, hc_u64⟩ := ctorProj_eq_of_noCollision hWc.runStore hctx.recordsFor.1
          (hctx.good envT lim) hcb hcbi hm hct (hctx.recordsFor.2.1 _ _ hcx_R)
        subst cx_R
        simp only [constructorProjection, ReadsRecord] at hread_x
        obtain ⟨cbR, msR, indR, ctR, hcbR, hmsR, hmR, hctR, -, -, -, -,
          ty₀, hread_ty₀, hci0_eq⟩ := hread_x
        have hi_nat : i.toUInt64.toNat = i := by
          change (UInt64.ofNat i).toNat = i
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi_u64]
        have hc_nat : c.toUInt64.toNat = c := by
          change (UInt64.ofNat c).toNat = c
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc_u64]
        rw [hi_nat] at hmR
        rw [hc_nat] at hctR
        have hcbR_eq : cbR = cb := hRE₀_eq b cbR cb hcbR hcb
        subst cbR
        have hmsR_eq : msR = ms := Ixon.ConstantInfo.muts.inj (hmsR.symm.trans hcbi)
        subst msR
        have hindR_eq : indR = ind :=
          Ixon.MutConst.indc.inj (Option.some.inj (hmR.symm.trans hm))
        subst indR
        have hctR_eq : ctR = ctor := Option.some.inj (hctR.symm.trans hct)
        subst ctR
        -- Align `exprReader` over `E₀.blobs` and `R.blobs` via `E.blobs`
        obtain ⟨e₀, hr_E₀, _⟩ := loadedAt_annotates hr
        have heq_e₀ : e₀ = ty₀ := Except.ok.inj
          ((exprReader_mono hctx.runBlob hr_E₀).symm.trans
            (exprReader_mono hctx.recordsFor.2.2.1 hread_ty₀))
        subst heq_e₀
        have hann_ci : Annotates ci.toConstantVal.type e₀ := by
          have h := hstAs.1.2.2; rw [hci0_eq] at h; exact h
        have hres_ci : ci.toConstantVal.type.constsResolve envT = true :=
          (hEnvWF ci (Ix.Kernel.Semantics.Env.find?_mem hfind_ci)).2.2.1
        intro k hk a ha
        exact Or.inl (storedAt_of_envWF_annot ht htwf (blockSelf_is_keyOf t b ms) he_ctor
          hr hr_E₀ hann_ci hres_ci k hk a ha)
    · -- `Held basisStore b`
      intro k hk a ha
      exact Or.inr (Or.inr (Or.inl (hF_basis.ctorType b i c ty hbas_b
        (by simp only [FlatView.ofStore, ctorTypeAt, hcb, hcbi, hm, hct, hr]) k hk a ha)))
    · -- `Top b ∧ rank b ≤ rank B`
      exact graphPredSet_of_top_block_loaded ht htwf hG hctx.shape hTb hrkb hcb hcbi he_ctor hr
    · -- Member projection of a top-walked block: cannot be `.muts`
      have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm').1
      have hceq : cb = memberProjection b' i' m' := Option.some.inj (hcb.symm.trans hmemP)
      rw [hceq] at hcbi
      cases m' <;> simp [memberProjection] at hcbi
  -- Helper: `indBlk` / `ciBlk` closure for `a ∈ S`
  have hInd_blk : ∀ a c p cb ms ind,
      S a → recordOf E₀ a = some c → c.info = .iPrj p →
      recordOf E₀ p.block = some cb → cb.info = .muts ms →
      ms[p.idx.toNat]? = some (.indc ind) → S p.block := by
    intro a c p cb ms ind ha hc hci hcb hcbi hm
    rcases ha with hst_a | ⟨cb', _, hcb', hcbi', -⟩ | hbas_a | ⟨hTa, hrka⟩ |
        ⟨b', cb', ms', i', m', hTb', hrkb', hcb', hcbi', hm', rfl⟩
    · have hne : p.block ≠ a := by
        intro heq; subst heq
        have hceq : c = cb := Option.some.inj (hc.symm.trans hcb)
        rw [hceq, hcbi] at hci; cases hci
      have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hci]
      have hbs := hWhole E hctx.recordsFor a p.block c cb ms (find_isSome_of_storedAt hst_a)
        (hctx.runRecord a c hc) hown hne (hctx.runRecord p.block cb hcb) hcbi
      exact Or.inr (Or.inl ⟨cb, ms, hcb, hcbi, hbs⟩)
    · have hceq : cb' = c := Option.some.inj (hcb'.symm.trans hc)
      rw [hceq, hci] at hcbi'; cases hcbi'
    · exact Or.inr (Or.inr (Or.inl (hF_basis.ciBlk a
        ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, p.block, p.idx.toNat⟩ hbas_a
        (by simp only [FlatView.ofStore, indInfoAt, hc, hci, hcb, hcbi, hm]))))
    · have hproj : IsProj c := Or.inr (Or.inl ⟨p, hci⟩)
      obtain ⟨hTpb, hrkpb⟩ := hG.owner a c hTa hc hproj
      simp only [Ix.Cert.ownerOf, hci] at hTpb hrkpb
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTpb, Nat.le_trans (Nat.le_of_lt hrkpb) hrka⟩)))
    · have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm').1
      have hceq : c = memberProjection b' i' m' := Option.some.inj (hc.symm.trans hmemP)
      have hown : Ix.Cert.ownerOf (memberAddr b' i' m') c = b' := by
        rw [hceq]; cases m' <;> rfl
      simp only [Ix.Cert.ownerOf, hci] at hown
      subst hown
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTb', hrkb'⟩)))
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- `(ReconView.ofStore t E₀).ClosedOn S`
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `indBlk`
      intro a i ha h
      obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, -, hblk⟩ :=
        indDataAt_inv (h : indDataAt t E₀ a = some (some i))
      rw [hblk]
      exact hInd_blk a c p cb ms ind ha hc hci hcb hcbi hm
    · -- `indTy`
      intro a i ha h
      obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, hr, -⟩ :=
        indDataAt_inv (h : indDataAt t E₀ a = some (some i))
      have he_ind : ∀ j ∈ exprRefIdxs ind.typ, j ∈ usedRefIdxs cb :=
        fun j hj => mem_used_of_member hcbi hm j (List.mem_append_left _ hj)
      rcases ha with hst_a | ⟨cb', _, hcb', hcbi', -⟩ | hbas_a | ⟨hTa, hrka⟩ |
          ⟨b', cb', ms', i', m', hTb', hrkb', hcb', hcbi', hm', rfl⟩
      · obtain ⟨ci, hfind_ci, hbas_a | hkept_a⟩ := storedAt_provenance hctx.shape ht htwf hst_a
        · intro k hk z hz
          exact Or.inr (Or.inr (Or.inl (hR_basis.indTy a i hbas_a h k hk z hz)))
        · obtain ⟨-, ci₀, ⟨cR, hcR, hread_a⟩, hstAs⟩ := hkept_a
          have hcR_eq : cR = c := hRE₀_eq a cR c hcR hc
          subst cR
          rw [hci] at hread_a
          obtain ⟨cbR, msR, indR, ⟨hcbR, hmsR, hmR, -, -, -⟩, ty₀, caps, hread_ty₀, hci0_eq⟩ :=
            hread_a
          have hcbR_eq : cbR = cb := hRE₀_eq p.block cbR cb hcbR hcb
          subst cbR
          have hmsR_eq : msR = ms := Ixon.ConstantInfo.muts.inj (hmsR.symm.trans hcbi)
          subst msR
          have hindR_eq : indR = ind :=
            Ixon.MutConst.indc.inj (Option.some.inj (hmR.symm.trans hm))
          subst indR
          obtain ⟨e₀, hr_E₀, _⟩ := loadedAt_annotates hr
          have heq_e₀ : e₀ = ty₀ := Except.ok.inj
            ((exprReader_mono hctx.runBlob hr_E₀).symm.trans
              (exprReader_mono hctx.recordsFor.2.2.1 hread_ty₀))
          subst heq_e₀
          have hann_ci : Annotates ci.toConstantVal.type e₀ := by
            have h1 := hstAs.1.2.2; rw [hci0_eq] at h1; exact h1
          have hres_ci : ci.toConstantVal.type.constsResolve envT = true :=
            (hEnvWF ci (Ix.Kernel.Semantics.Env.find?_mem hfind_ci)).2.2.1
          intro k hk z hz
          exact Or.inl (storedAt_of_envWF_annot ht htwf (blockSelf_is_keyOf t p.block ms) he_ind
            hr hr_E₀ hann_ci hres_ci k hk z hz)
      · have hceq : cb' = c := Option.some.inj (hcb'.symm.trans hc)
        rw [hceq, hci] at hcbi'; cases hcbi'
      · intro k hk z hz
        exact Or.inr (Or.inr (Or.inl (hR_basis.indTy a i hbas_a h k hk z hz)))
      · have hproj : IsProj c := Or.inr (Or.inl ⟨p, hci⟩)
        obtain ⟨hTpb, hrkpb⟩ := hG.owner a c hTa hc hproj
        simp only [Ix.Cert.ownerOf, hci] at hTpb hrkpb
        exact graphPredSet_of_top_block_loaded ht htwf hG hctx.shape hTpb
          (Nat.le_trans (Nat.le_of_lt hrkpb) hrka) hcb hcbi he_ind hr
      · have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm').1
        have hceq : c = memberProjection b' i' m' := Option.some.inj (hc.symm.trans hmemP)
        have hown : Ix.Cert.ownerOf (memberAddr b' i' m') c = b' := by
          rw [hceq]; cases m' <;> rfl
        simp only [Ix.Cert.ownerOf, hci] at hown
        subst hown
        exact graphPredSet_of_top_block_loaded ht htwf hG hctx.shape hTb' hrkb' hcb hcbi he_ind hr
    · -- `ctorTy`
      intro b i c ty np hb h
      obtain ⟨cb, ms, ind, ctor, hcb, hcbi, hm, hct, hr⟩ :=
        ctorAt_inv (h : ctorAt t E₀ b i c = some (ty, np))
      exact hCtor_keys b i c cb ms ind ctor ty hb hcb hcbi hm hct hr
    · -- `unfold`
      intro k us v hk h
      obtain ⟨a, n, w, hka, hd, rfl⟩ := unfoldAt_inv (h : unfoldAt t E₀ k us = some (some v))
      have ha : S a := hk a hka
      obtain ⟨c, hc, hdef⟩ := defnAt_inv hd
      intro k' hk' a' ha'
      have hk'' := keyIn_exprInstLevels w hk'
      rcases ha with hst_a | ⟨cb', _, hcb', hcbi', -⟩ | hbas_a | ⟨hTa, hrka⟩ |
          ⟨b', cb', ms', i', m', hTb', hrkb', hcb', hcbi', hm', rfl⟩
      · obtain ⟨ci, hfind_ci, hbas_a | hkept_a⟩ := storedAt_provenance hctx.shape ht htwf hst_a
        · exact Or.inr (Or.inr (Or.inl (hR_basis.unfold k us (Binding.FamilyFlat.exprInstLevels us w)
            (fun a₁ ha₁ => by
              have e : a₁ = a := Option.some.inj (ha₁.symm.trans hka)
              rwa [e]) h k' hk' a' ha')))
        · obtain ⟨-, ci₀, ⟨cR, hcR, hread_a⟩, hstAs⟩ := hkept_a
          have hcR_eq : cR = c := hRE₀_eq a cR c hcR hc
          subst cR
          rcases hdef with ⟨d, hci, hr⟩ | ⟨p, cb, ms, d, hci, hcb, hcbi, hm, hr⟩
          · -- Solo definition
            rw [hci] at hread_a
            obtain ⟨-, ty₀, val₀, -, hread_val₀, hshape_d⟩ := hread_a
            -- Recover `d.kind = .defn` from `defnAt`
            have hdkind : d.kind = .defn := by
              unfold defnAt at hd
              simp only [hc, hci] at hd
              cases hdk : d.kind <;> simp [hdk] at hd
              rfl
            rw [hdkind] at hshape_d
            obtain ⟨hint₀, hci0_eq⟩ := hshape_d
            have hci_defn : ∃ cv v_ci hint, ci = .defnInfo cv v_ci hint ∧ Annotates v_ci val₀ := by
              have hm2 := hstAs.2
              rw [hci0_eq] at hm2
              cases ci with
              | defnInfo cv v_ci hint => exact ⟨cv, v_ci, hint, rfl, hm2.1⟩
              | _ => exact False.elim hm2
            obtain ⟨cv, v_ci, hint, hci_eq, hann_v⟩ := hci_defn
            have hres_v : v_ci.constsResolve envT = true :=
              ((hEnvWF ci (Ix.Kernel.Semantics.Env.find?_mem hfind_ci)).2.2.2.2.1
                cv v_ci hint hci_eq).2.2.1
            obtain ⟨e₀, hr_E₀, _⟩ := loadedAt_annotates hr
            have heq_e₀ : e₀ = val₀ := Except.ok.inj
              ((exprReader_mono hctx.runBlob hr_E₀).symm.trans
                (exprReader_mono hctx.recordsFor.2.2.1 hread_val₀))
            subst heq_e₀
            have he_val : ∀ j ∈ exprRefIdxs d.value, j ∈ usedRefIdxs c := by
              intro j hj; simp only [usedRefIdxs, hci]
              exact List.mem_append_right _ (List.mem_append_right _ hj)
            exact Or.inl (storedAt_of_envWF_annot ht htwf (soloSelf_is_keyOf t a) he_val
              hr hr_E₀ hann_v hres_v k' hk'' a' ha')
          · -- Mutual definition projection `.dPrj p`
            rw [hci] at hread_a
            obtain ⟨cbR, msR, dR, ⟨hcbR, hmsR, hmR, -, -, -⟩,
              ty₀, val₀, -, hread_val₀, hshape_d⟩ := hread_a
            have hcbR_eq : cbR = cb := hRE₀_eq p.block cbR cb hcbR hcb
            subst cbR
            have hmsR_eq : msR = ms := Ixon.ConstantInfo.muts.inj (hmsR.symm.trans hcbi)
            subst msR
            have hdR_eq : dR = d :=
              Ixon.MutConst.defn.inj (Option.some.inj (hmR.symm.trans hm))
            subst dR
            have hdkind : d.kind = .defn := by
              unfold defnAt at hd
              simp only [hc, hci, hcb, hcbi, hm] at hd
              cases hdk : d.kind <;> simp [hdk] at hd
              rfl
            rw [hdkind] at hshape_d
            obtain ⟨hint₀, hci0_eq⟩ := hshape_d
            have hci_defn : ∃ cv v_ci hint, ci = .defnInfo cv v_ci hint ∧ Annotates v_ci val₀ := by
              have hm2 := hstAs.2
              rw [hci0_eq] at hm2
              cases ci with
              | defnInfo cv v_ci hint => exact ⟨cv, v_ci, hint, rfl, hm2.1⟩
              | _ => exact False.elim hm2
            obtain ⟨cv, v_ci, hint, hci_eq, hann_v⟩ := hci_defn
            have hres_v : v_ci.constsResolve envT = true :=
              ((hEnvWF ci (Ix.Kernel.Semantics.Env.find?_mem hfind_ci)).2.2.2.2.1
                cv v_ci hint hci_eq).2.2.1
            obtain ⟨e₀, hr_E₀, _⟩ := loadedAt_annotates hr
            have heq_e₀ : e₀ = val₀ := Except.ok.inj
              ((exprReader_mono hctx.runBlob hr_E₀).symm.trans
                (exprReader_mono hctx.recordsFor.2.2.1 hread_val₀))
            subst heq_e₀
            have he_val : ∀ j ∈ exprRefIdxs d.value, j ∈ usedRefIdxs cb :=
              fun j hj => mem_used_of_member hcbi hm j (List.mem_append_right _ hj)
            exact Or.inl (storedAt_of_envWF_annot ht htwf (blockSelf_is_keyOf t p.block ms) he_val
              hr hr_E₀ hann_v hres_v k' hk'' a' ha')
      · -- `a` cannot be `.muts`
        have hceq : cb' = c := Option.some.inj (hcb'.symm.trans hc)
        rcases hdef with ⟨_, hci, -⟩ | ⟨_, _, _, _, hci, -⟩ <;>
          (rw [hceq, hci] at hcbi'; cases hcbi')
      · -- `Held basisStore a`
        exact Or.inr (Or.inr (Or.inl (hR_basis.unfold k us (Binding.FamilyFlat.exprInstLevels us w)
          (fun a₁ ha₁ => by
            have e : a₁ = a := Option.some.inj (ha₁.symm.trans hka)
            rwa [e]) h k' hk' a' ha')))
      · -- `Top a ∧ rank a ≤ rank B`
        rcases hdef with ⟨d, hci, hr⟩ | ⟨p, cb, ms, d, hci, hcb, hcbi, hm, hr⟩
        · obtain ⟨e₀, hr₀, hk₀⟩ := keyIn_of_loadedAt hr hk''
          have he_val : ∀ j ∈ exprRefIdxs d.value, j ∈ usedRefIdxs c := by
            intro j hj; simp only [usedRefIdxs, hci]
            exact List.mem_append_right _ (List.mem_append_right _ hj)
          obtain ⟨z, hz, rfl⟩ := read_keys ht
            (P := fun k => ∃ z, S z ∧ k = keyOf t z)
            (fun j hj y hy => ⟨y, graphPredSet_of_top_used hG hctx.shape htwf hTa hrka
              ⟨c, j, hc, hj, hy⟩, rfl⟩)
            (fun j k hs => by
              unfold soloSelf at hs
              split at hs
              · cases Except.ok.inj (Option.some.inj hs)
                exact ⟨a, Or.inr (Or.inr (Or.inr (Or.inl ⟨hTa, hrka⟩))), rfl⟩
              · cases hs)
            he_val hr₀ k' hk₀
          have eq : a' = z := Option.some.inj (ha'.symm.trans (keyAddr_keyOf htwf z))
          rwa [eq]
        · have hproj : IsProj c := Or.inl ⟨p, hci⟩
          obtain ⟨hTpb, hrkpb⟩ := hG.owner a c hTa hc hproj
          simp only [Ix.Cert.ownerOf, hci] at hTpb hrkpb
          have he_val : ∀ j ∈ exprRefIdxs d.value, j ∈ usedRefIdxs cb :=
            fun j hj => mem_used_of_member hcbi hm j (List.mem_append_right _ hj)
          exact graphPredSet_of_top_block_loaded ht htwf hG hctx.shape hTpb
            (Nat.le_trans (Nat.le_of_lt hrkpb) hrka) hcb hcbi he_val hr k' hk'' a' ha'
      · -- Member projection of a top-walked block
        have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm').1
        have hceq : c = memberProjection b' i' m' := Option.some.inj (hc.symm.trans hmemP)
        rcases hdef with ⟨d, hci, -⟩ | ⟨p, cb, ms, d, hci, hcb, hcbi, hm, hr⟩
        · rw [hceq] at hci; cases m' <;> simp [memberProjection] at hci
        · have hown : Ix.Cert.ownerOf (memberAddr b' i' m') c = b' := by
            rw [hceq]; cases m' <;> rfl
          simp only [Ix.Cert.ownerOf, hci] at hown
          subst hown
          have he_val : ∀ j ∈ exprRefIdxs d.value, j ∈ usedRefIdxs cb :=
            fun j hj => mem_used_of_member hcbi hm j (List.mem_append_right _ hj)
          exact graphPredSet_of_top_block_loaded ht htwf hG hctx.shape hTb' hrkb' hcb hcbi
            he_val hr k' hk'' a' ha'
  · -- `(FlatView.ofStore t E₀).ClosedOn S`
    refine ⟨?_, ?_, ?_⟩
    · -- `ciBlk`
      intro a i ha h
      obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, rfl⟩ :=
        indInfoAt_inv (h : indInfoAt E₀ a = some (some i))
      exact hInd_blk a c p cb ms ind ha hc hci hcb hcbi hm
    · -- `members`
      intro b addrs hb h a ha
      obtain ⟨cb, arr, hcb, hcbi, rfl⟩ := membersAt_inv (h : membersAt E₀ b = some addrs)
      obtain ⟨i, m, hm, rfl⟩ := mem_indcAddrs arr.toList 0 ha
      have hm' : arr[i]? = some m := by simpa only [Array.getElem?_toList] using hm
      rw [Nat.zero_add] at ha ⊢
      rcases hb with hst_b | ⟨cb', ms', hcb', hcbi', hbs⟩ | hbas_b | ⟨hTb, hrkb⟩ |
          ⟨b', cb', ms', i', m', hTb', _, hcb', hcbi', hm'', rfl⟩
      · obtain ⟨_, _, hbas | hkept⟩ := storedAt_provenance hctx.shape ht htwf hst_b
        · exact Or.inr (Or.inr (Or.inl (hF_basis.members b _ hbas h _ ha)))
        · obtain ⟨-, -, ⟨cR, hcR, hread⟩, -⟩ := hkept
          have hceq := hRE₀_eq b cR cb hcR hcb
          subst cR; rw [hcbi] at hread; exact False.elim hread
      · have hcb_eq : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
        subst cb'
        have hms_eq : ms' = arr := Ixon.ConstantInfo.muts.inj (hcbi'.symm.trans hcbi)
        subst ms'
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hbs i m hm').1
        exact Or.inl (storedAt_of_find hci)
      · exact Or.inr (Or.inr (Or.inl (hF_basis.members b _ hbas_b h _ ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, cb, arr, i, m, hTb, hrkb, hcb, hcbi, hm', rfl⟩)))
      · have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm'').1
        have hceq : cb = memberProjection b' i' m' := Option.some.inj (hcb.symm.trans hmemP)
        rw [hceq] at hcbi; cases m' <;> simp [memberProjection] at hcbi
    · -- `ctorType`
      intro b i c ty hb h
      obtain ⟨cb, ms, ind, ctor, hcb, hcbi, hm, hct, hr⟩ :=
        ctorTypeAt_inv (h : ctorTypeAt t E₀ b i c = some ty)
      exact hCtor_keys b i c cb ms ind ctor ty hb hcb hcbi hm hct hr
  · -- `S B`
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTB, le_rfl⟩)))
  · -- `∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc))`
    intro j rc hj hSx
    have hconst : ConstAddrOf rb crb (memberAddr rb j (.recr rc)) :=
      Or.inr ⟨rs, j, .recr rc, hrb.muts, hj, Or.inl rfl⟩
    have hnot_st : ¬ StoredAt t envT (memberAddr rb j (.recr rc)) :=
      hFG.famFresh B rb crb _ hfam hrb.record hconst
    have hrec_x : recordOf E₀ (memberAddr rb j (.recr rc)) =
        some (memberProjection rb j (.recr rc)) :=
      hrb.members j (.recr rc) hj
    rcases hSx with hst | ⟨cb', _, hcb', hcbi', -⟩ | hbas | ⟨hTx, hrkx⟩ |
        ⟨b', cb', ms', i', m', hTb', hrkb', hcb', hcbi', hm', haddr_eq⟩
    · exact hnot_st hst
    · have hceq : cb' = memberProjection rb j (.recr rc) :=
        Option.some.inj (hcb'.symm.trans hrec_x)
      rw [hceq] at hcbi'; simp [memberProjection] at hcbi'
    · obtain ⟨cB, hcB⟩ := Option.isSome_iff_exists.mp hbas
      have hmemB := StoreInhabit.store_record_inv hcB
      have hceq : cB = memberProjection rb j (.recr rc) := Option.some.inj
        ((recordAt_E_of_basisStore hctx.recordsFor hcB).symm.trans (hctx.runRecord _ _ hrec_x))
      subst cB
      have hkp := List.all_eq_true.mp StoreInhabit.keys_pinned
        (memberAddr rb j (.recr rc), memberProjection rb j (.recr rc)) hmemB
      simp only [StoreInhabit.isMutsInfo, memberProjection, Bool.false_or] at hkp
      obtain ⟨r, hr, hkey_def⟩ := StoreInhabit.isBasisKey_role hkp
      have had_def : RoleVal.committedDefaultRoleTable.addressOf? r =
          some (memberAddr rb j (.recr rc)) :=
        Core.addressOf_of_keyOf (by
          unfold Ix.Kernel.RoleTable.wf
          rw [RoleVal.committedDefaultRoleTable_check]; rfl)
          (by rw [LoadedReads.keyOf_eq]; exact hkey_def)
      have had_t : t.addressOf? r = some (memberAddr rb j (.recr rc)) := by
        rw [basisRole_addr_eq hctx.shape.prelude hr, had_def]
      exact hnot_st (basisRole_storedAt hctx.shape htwf hr had_t)
    · have hproj : IsProj (memberProjection rb j (.recr rc)) :=
        Or.inr (Or.inr (Or.inr ⟨⟨j.toUInt64, rb⟩, rfl⟩))
      obtain ⟨hTrb, hrkrb⟩ := hG.owner _ _ hTx hrec_x hproj
      simp only [Ix.Cert.ownerOf, memberProjection] at hTrb hrkrb
      have hlt := hFG.famAfter B rb hfam (Or.inl hTrb)
      omega
    · have hmemP := (hG.members b' cb' ms' hTb' hcb' hcbi' i' m' hm').1
      rw [← haddr_eq] at hmemP
      have hceq : memberProjection b' i' m' = memberProjection rb j (.recr rc) :=
        Option.some.inj (hmemP.symm.trans hrec_x)
      have hown : b' = rb := by
        have := congrArg (Ix.Cert.ownerOf (memberAddr rb j (.recr rc))) hceq
        cases m' <;> simpa [Ix.Cert.ownerOf, memberProjection] using this
      subst b'
      have hlt := hFG.famAfter B rb hfam (Or.inl hTb')
      omega

end IxVM.Refinement.Typing.TwinFamily
