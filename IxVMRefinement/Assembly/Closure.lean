import IxVMRefinement.Assembly.ClaimsL1L6
import Ix.Cert.Order

/-! # Used-reference closure ordering and sub-store selection from `WalkedL6`

Constructs the walked sub-environment `E` (`Draws E E₀`) and the topological record order
`order : List Address` satisfying `IxVM.Consistency.UsedClosureOrderAt` from `Claim.WalkedL6`:

* `exprRefIdxs_eq`, `mutRefIdxs_eq`, `usedRefIdxs_eq`: syntactic equality between `Core.S0`'s
  used-reference index extractors and `IxVM.Consistency`'s;
* `subEnv`: restricts `E₀.consts` to a chosen checked predicate `Keep : Address → Prop` (preventing
  unwalked records in `E₀.consts` from being pulled in by unused role-table evidence entries) and
  optionally supplements recursor records at addresses absent from `E₀.consts`, preserving
  `IxVM.Refinement.Draws E E₀`, pure-BLAKE3 byte authentication, and `Ixon.deConstantExact`;
* `closureOrderByRank` and `usedClosureOrderAt_closureOrderByRank`: sorts the reachable keys of an
  owner-closed `Ixon.Env` by any `Nat`-valued rank strictly decreasing along `UsedRecordRef`;
* `twoTierRank` (`2 * rank a` on walked records, `2 * rank (iblock a) + 1` on extra recursor
  records): proves strict rank decrease along `UsedRecordRef` and discharges `UsedClosureOrderAt`
  both for pure walked sub-stores (`walkedSubEnv_usedClosureOrderAt`) and for walked sub-stores
  with modeled/prelude recursor supplements (`subEnv_twoTier_usedClosureOrderAt`). -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-! ## Agreement of `usedRefIdxs` between `Core.S0` and `IxVM.Consistency` -/

private theorem flatMap_congr_all {α β : Type _} {f g : α → List β}
    (h : ∀ x, f x = g x) : ∀ xs : List α, xs.flatMap f = xs.flatMap g
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, h x, flatMap_congr_all h xs]

/-- `Core.S0.exprRefIdxs` is definitionally identical to `IxVM.Consistency.exprRefIdxs`. -/
theorem exprRefIdxs_eq : ∀ e : Ixon.Expr,
    Core.S0.exprRefIdxs e = IxVM.Consistency.exprRefIdxs e
  | .sort _ => rfl
  | .var _ => rfl
  | .ref _ _ => rfl
  | .recur _ _ => rfl
  | .prj _ _ e => by
    simp only [Core.S0.exprRefIdxs, IxVM.Consistency.exprRefIdxs, exprRefIdxs_eq e]
  | .str _ => rfl
  | .nat _ => rfl
  | .app f a => by
    simp only [Core.S0.exprRefIdxs, IxVM.Consistency.exprRefIdxs,
      exprRefIdxs_eq f, exprRefIdxs_eq a]
  | .lam t b => by
    simp only [Core.S0.exprRefIdxs, IxVM.Consistency.exprRefIdxs,
      exprRefIdxs_eq t, exprRefIdxs_eq b]
  | .all t b => by
    simp only [Core.S0.exprRefIdxs, IxVM.Consistency.exprRefIdxs,
      exprRefIdxs_eq t, exprRefIdxs_eq b]
  | .letE _ _ t v b => by
    simp only [Core.S0.exprRefIdxs, IxVM.Consistency.exprRefIdxs,
      exprRefIdxs_eq t, exprRefIdxs_eq v, exprRefIdxs_eq b]
  | .share _ => rfl

/-- `Core.S0.mutRefIdxs` is identical to `IxVM.Consistency.mutRefIdxs`. -/
theorem mutRefIdxs_eq : ∀ m : Ixon.MutConst,
    Core.S0.mutRefIdxs m = IxVM.Consistency.mutRefIdxs m
  | .defn d => by
    simp only [Core.S0.mutRefIdxs, IxVM.Consistency.mutRefIdxs,
      exprRefIdxs_eq d.typ, exprRefIdxs_eq d.value]
  | .indc i => by
    have hctors :
        (i.ctors.toList.flatMap fun c => Core.S0.exprRefIdxs c.typ) =
        (i.ctors.toList.flatMap fun c => IxVM.Consistency.exprRefIdxs c.typ) :=
      flatMap_congr_all (fun c => exprRefIdxs_eq c.typ) i.ctors.toList
    simp only [Core.S0.mutRefIdxs, IxVM.Consistency.mutRefIdxs, exprRefIdxs_eq i.typ, hctors]
  | .recr r => by
    have hrules :
        (r.rules.toList.flatMap fun rl => Core.S0.exprRefIdxs rl.rhs) =
        (r.rules.toList.flatMap fun rl => IxVM.Consistency.exprRefIdxs rl.rhs) :=
      flatMap_congr_all (fun rl => exprRefIdxs_eq rl.rhs) r.rules.toList
    simp only [Core.S0.mutRefIdxs, IxVM.Consistency.mutRefIdxs, exprRefIdxs_eq r.typ, hrules]

/-- `Core.S0.usedRefIdxs` is identical to `IxVM.Consistency.usedRefIdxs`. -/
theorem usedRefIdxs_eq (c : Ixon.Constant) :
    Core.S0.usedRefIdxs c = IxVM.Consistency.usedRefIdxs c := by
  have hsh :
      c.sharing.toList.flatMap Core.S0.exprRefIdxs =
      c.sharing.toList.flatMap IxVM.Consistency.exprRefIdxs :=
    flatMap_congr_all exprRefIdxs_eq c.sharing.toList
  cases hinfo : c.info with
  | defn d =>
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh,
      exprRefIdxs_eq d.typ, exprRefIdxs_eq d.value]
  | recr r =>
    have hrules :
        (r.rules.toList.flatMap fun rl => Core.S0.exprRefIdxs rl.rhs) =
        (r.rules.toList.flatMap fun rl => IxVM.Consistency.exprRefIdxs rl.rhs) :=
      flatMap_congr_all (fun rl => exprRefIdxs_eq rl.rhs) r.rules.toList
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh,
      exprRefIdxs_eq r.typ, hrules]
  | axio a =>
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh, exprRefIdxs_eq a.typ]
  | quot q =>
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh, exprRefIdxs_eq q.typ]
  | muts ms =>
    have hms :
        ms.toList.flatMap Core.S0.mutRefIdxs = ms.toList.flatMap IxVM.Consistency.mutRefIdxs :=
      flatMap_congr_all mutRefIdxs_eq ms.toList
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh, hms]
  | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
    simp only [Core.S0.usedRefIdxs, IxVM.Consistency.usedRefIdxs, hinfo, hsh]

/-! ## Sub-environment builder (`subEnv`) and `Draws` -/

/-- A recursor supplement entry `(address, rawBytes, decodedConstant)` for `subEnv`. -/
abbrev SuppEntry := _root_.Address × ByteArray × Ixon.Constant

/-- Auxiliary filter keeping keys of `m` in `as` that satisfy `Keep`. -/
noncomputable def restrictConstsAux (m : Std.HashMap _root_.Address Ixon.LazyConstant)
    (Keep : _root_.Address → Prop) :
    List _root_.Address → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => {}
  | a :: as =>
    let rest := restrictConstsAux m Keep as
    haveI := Classical.propDecidable (Keep a)
    if Keep a then
      match m.get? a with
      | some lc => rest.insert a lc
      | none => rest
    else rest

/-- Restrict `m` to addresses satisfying `Keep`. -/
noncomputable def restrictConsts (m : Std.HashMap _root_.Address Ixon.LazyConstant)
    (Keep : _root_.Address → Prop) : Std.HashMap _root_.Address Ixon.LazyConstant :=
  restrictConstsAux m Keep m.keys

private theorem restrictConstsAux_get?_some_inv
    (m : Std.HashMap _root_.Address Ixon.LazyConstant) (Keep : _root_.Address → Prop) :
    ∀ (as : List _root_.Address) {x : _root_.Address} {lc : Ixon.LazyConstant},
      (restrictConstsAux m Keep as).get? x = some lc →
      Keep x ∧ m.get? x = some lc
  | [], _, _, h => by
    simp only [restrictConstsAux, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
    cases h
  | a :: as, x, lc, h => by
    simp only [restrictConstsAux] at h
    split at h
    · rename_i hka
      cases hma : m.get? a with
      | none =>
        rw [hma] at h
        exact restrictConstsAux_get?_some_inv m Keep as h
      | some lca =>
        rw [hma, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i heq
          injection h with hlc
          subst hlc
          have hax : a = x := beq_iff_eq.mp heq
          subst hax
          exact ⟨hka, hma⟩
        · rw [← Std.HashMap.get?_eq_getElem?] at h
          exact restrictConstsAux_get?_some_inv m Keep as h
    · exact restrictConstsAux_get?_some_inv m Keep as h

private theorem restrictConstsAux_get?_of_mem
    (m : Std.HashMap _root_.Address Ixon.LazyConstant) (Keep : _root_.Address → Prop) :
    ∀ (as : List _root_.Address) {x : _root_.Address} {lc : Ixon.LazyConstant},
      x ∈ as → Keep x → m.get? x = some lc →
      (restrictConstsAux m Keep as).get? x = some lc
  | [], _, _, hmem, _, _ => nomatch hmem
  | a :: as, x, lc, hmem, hkx, hmx => by
    simp only [restrictConstsAux]
    by_cases hax : a = x
    · subst hax
      simp only [hkx, ↓reduceIte, hmx, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, beq_self_eq_true]
    · have hmem' : x ∈ as := by
        rcases List.mem_cons.mp hmem with rfl | htl
        · exact absurd rfl hax
        · exact htl
      have ih := restrictConstsAux_get?_of_mem m Keep as hmem' hkx hmx
      split
      · cases hma : m.get? a with
        | none => exact ih
        | some lca =>
          have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hax
          rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
            ← Std.HashMap.get?_eq_getElem?]
          exact ih
      · exact ih

theorem restrictConsts_get?_some_iff
    (m : Std.HashMap _root_.Address Ixon.LazyConstant) (Keep : _root_.Address → Prop)
    (x : _root_.Address) (lc : Ixon.LazyConstant) :
    (restrictConsts m Keep).get? x = some lc ↔ Keep x ∧ m.get? x = some lc := by
  constructor
  · exact restrictConstsAux_get?_some_inv m Keep m.keys
  · rintro ⟨hk, hm⟩
    have hmem : x ∈ m.keys := by
      rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
        Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hm]
      rfl
    exact restrictConstsAux_get?_of_mem m Keep m.keys hmem hk hm

theorem restrictConsts_get?_eq_none_of_not_keep
    (m : Std.HashMap _root_.Address Ixon.LazyConstant) (Keep : _root_.Address → Prop)
    {x : _root_.Address} (hnk : ¬ Keep x) :
    (restrictConsts m Keep).get? x = none := by
  cases h : (restrictConsts m Keep).get? x with
  | none => rfl
  | some lc => exact absurd ((restrictConsts_get?_some_iff m Keep x lc).mp h).1 hnk

/-- Overlay supplement entries at addresses not already present in `m₀`. -/
def addSupplements (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    List SuppEntry → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => base
  | (a, raw, c) :: rest =>
    let tail := addSupplements m₀ base rest
    if m₀.contains a then tail else tail.insert a (Claim.mkLazy raw c)

theorem addSupplements_get?_of_contains
    (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ (supp : List SuppEntry) {x : _root_.Address},
      m₀.contains x = true →
      (addSupplements m₀ base supp).get? x = base.get? x
  | [], _, _ => rfl
  | (a, raw, c) :: rest, x, hcx => by
    simp only [addSupplements]
    have ih := addSupplements_get?_of_contains m₀ base rest hcx
    split
    · exact ih
    · rename_i hca
      have hne : a ≠ x := by
        intro heq
        rw [heq, hcx] at hca
        exact hca rfl
      have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hne
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
        ← Std.HashMap.get?_eq_getElem?]
      exact ih

theorem addSupplements_get?_some_inv
    (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ (supp : List SuppEntry) {x : _root_.Address} {lc : Ixon.LazyConstant},
      (addSupplements m₀ base supp).get? x = some lc →
      base.get? x = some lc ∨
        (m₀.contains x = false ∧ ∃ raw c, (x, raw, c) ∈ supp ∧ lc = Claim.mkLazy raw c)
  | [], _, _, h => Or.inl h
  | (a, raw, c) :: rest, x, lc, h => by
    simp only [addSupplements] at h
    split at h
    · rcases addSupplements_get?_some_inv m₀ base rest h with hb | ⟨hnc, raw', c', hm, hlc⟩
      · exact Or.inl hb
      · exact Or.inr ⟨hnc, raw', c', List.mem_cons_of_mem _ hm, hlc⟩
    · rename_i hca
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        injection h with hlc
        have hax : a = x := beq_iff_eq.mp heq
        subst hax
        have hca' : m₀.contains a = false := Bool.eq_false_iff.mpr hca
        exact Or.inr ⟨hca', raw, c, List.mem_cons_self, hlc.symm⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        rcases addSupplements_get?_some_inv m₀ base rest h with hb | ⟨hnc, raw', c', hm, hlc⟩
        · exact Or.inl hb
        · exact Or.inr ⟨hnc, raw', c', List.mem_cons_of_mem _ hm, hlc⟩

theorem addSupplements_get?_of_mem_nodup
    (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ {supp : List SuppEntry} {x : _root_.Address} {raw : ByteArray} {c : Ixon.Constant},
      (supp.map (·.1)).Nodup → (x, raw, c) ∈ supp → m₀.contains x = false →
      (addSupplements m₀ base supp).get? x = some (Claim.mkLazy raw c)
  | [], _, _, _, _, hm, _ => nomatch hm
  | (a, raw₀, c₀) :: rest, x, raw, c, hnd, hm, hnc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
      simp only [addSupplements, hnc, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
    · have hax : a ≠ x := by
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(a, raw, c), htl, rfl⟩)
      have ih := addSupplements_get?_of_mem_nodup m₀ base hnd.2 htl hnc
      simp only [addSupplements]
      split
      · exact ih
      · have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hax
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
          ← Std.HashMap.get?_eq_getElem?]
        exact ih

/-- Construct the sub-environment of `E₀` keeping `Keep` from `E₀.consts`, adding recursor
supplements `supp` at addresses absent from `E₀.consts`, and retaining `E₀`'s blobs and hints
with `roleBinding := none`. -/
noncomputable def subEnv (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) : Ixon.Env where
  consts := addSupplements E₀.consts (restrictConsts E₀.consts Keep) supp
  blobs := E₀.blobs
  anonHints := E₀.anonHints
  roleBinding := none

theorem subEnv_get?_of_contains (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address} (hc : E₀.consts.contains a = true) :
    (subEnv E₀ Keep supp).consts.get? a = (restrictConsts E₀.consts Keep).get? a :=
  addSupplements_get?_of_contains E₀.consts (restrictConsts E₀.consts Keep) supp hc

theorem subEnv_get?_of_keep (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hk : Keep a) (hget : E₀.consts.get? a = some lc) :
    (subEnv E₀ Keep supp).consts.get? a = some lc := by
  have hc : E₀.consts.contains a = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  rw [subEnv_get?_of_contains E₀ Keep supp hc]
  exact (restrictConsts_get?_some_iff E₀.consts Keep a lc).mpr ⟨hk, hget⟩

theorem subEnv_contains_of_keep (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address}
    (hk : Keep a) (hc : E₀.consts.contains a = true) :
    (subEnv E₀ Keep supp).consts.contains a = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc ⊢
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hc
  rw [← Std.HashMap.get?_eq_getElem?] at hlc ⊢
  rw [subEnv_get?_of_keep E₀ Keep supp hk hlc]
  rfl

theorem recordAt_subEnv_of_keep (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address} {c : Ixon.Constant}
    (hk : Keep a) (hrec : Ix.Cert.recordAt E₀ a = some c) :
    Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c := by
  unfold Ix.Cert.recordAt at hrec ⊢
  cases hget : E₀.consts.get? a with
  | none => rw [hget] at hrec; cases hrec
  | some lc =>
    rw [hget] at hrec
    rw [subEnv_get?_of_keep E₀ Keep supp hk hget]
    exact hrec

theorem subEnv_get?_some_inv (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (subEnv E₀ Keep supp).consts.get? a = some lc) :
    (Keep a ∧ E₀.consts.get? a = some lc) ∨
      (E₀.consts.contains a = false ∧ ∃ raw c, (a, raw, c) ∈ supp ∧ lc = Claim.mkLazy raw c) := by
  rcases addSupplements_get?_some_inv E₀.consts (restrictConsts E₀.consts Keep) supp h with
    hb | hsupp
  · exact Or.inl ((restrictConsts_get?_some_iff E₀.consts Keep a lc).mp hb)
  · exact Or.inr hsupp

theorem recordAt_subEnv_some_inv (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) {a : _root_.Address} {c : Ixon.Constant}
    (h : Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c) :
    (Keep a ∧ Ix.Cert.recordAt E₀ a = some c) ∨
      (E₀.consts.contains a = false ∧ ∃ raw, (a, raw, c) ∈ supp) := by
  unfold Ix.Cert.recordAt at h
  cases hget : (subEnv E₀ Keep supp).consts.get? a with
  | none => rw [hget] at h; cases h
  | some lc =>
    rw [hget] at h
    simp only [Option.bind_some] at h
    rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨hk, hget₀⟩ | ⟨hnc, raw, c', hm, rfl⟩
    ·refine Or.inl ⟨hk, ?_⟩
     unfold Ix.Cert.recordAt
     rw [hget₀]
     exact h
    · simp only [Claim.mkLazy_get?, Option.some.injEq] at h
      subst h
      exact Or.inr ⟨hnc, raw, hm⟩

/-- **`Draws (subEnv E₀ Keep supp) E₀`** holds whenever every supplement entry is a recursor
record (`IsRecursorRecord`). -/
theorem subEnv_draws (E₀ : Ixon.Env) (Keep : _root_.Address → Prop) (supp : List SuppEntry)
    (hsupp : ∀ entry ∈ supp, IxVM.Refinement.IsRecursorRecord entry.2.2) :
    IxVM.Refinement.Draws (subEnv E₀ Keep supp) E₀ := by
  refine ⟨fun a lc hget => ?_, fun _ _ hblob => hblob⟩
  rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨hnc, raw, c, hm, rfl⟩
  · exact Or.inl ⟨lc, hget₀, rfl⟩
  · exact Or.inr ⟨hnc, c, Claim.mkLazy_get? raw c, hsupp (a, raw, c) hm⟩

/-- Every constant stored in `subEnv E₀ Keep supp` has pure-BLAKE3 authenticated `rawBytes` and
decodes via `Ixon.deConstantExact` whenever `E₀` is `LoadedBy` with exact-decoded constants and
each supplement entry is authenticated and exact-decoded. -/
theorem subEnv_consts_authentic_exact {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      Address.blake3Pure raw = a ∧ Ixon.deConstantExact raw = .ok c)
    {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hget : (subEnv E₀ Keep supp).consts.get? a = some lc) :
    Address.blake3Pure lc.rawBytes = a ∧
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨_, raw, c, hm, rfl⟩
  · exact ⟨(hload.1 a lc hget₀).2, hexact₀ a lc hget₀⟩
  · obtain ⟨hblk, hex⟩ := hsupp a raw c hm
    simpa only [Claim.mkLazy_rawBytes, Claim.mkLazy_get?] using ⟨hblk, c, rfl, hex⟩

/-! ## General rank-based `UsedClosureOrderAt` for owner-closed stores -/

/-- A recursor record (`IsRecursorRecord`) is never a projection record, so its `ownerOf` is
itself. -/
theorem isRecursorRecord_ownerOf_eq (a : _root_.Address) {c : Ixon.Constant}
    (h : IxVM.Refinement.IsRecursorRecord c) :
    Ix.Cert.ownerOf a c = a := by
  unfold IxVM.Refinement.IsRecursorRecord at h
  cases hinfo : c.info <;> simp [Ix.Cert.ownerOf, hinfo] at h ⊢

theorem contains_of_recordAt {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : Ix.Cert.recordAt E a = some c) :
    E.consts.contains a = true := by
  have hk := Ix.Cert.Order.mem_keys_of_stored E h
  rwa [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains] at hk

/-- In an owner-closed `Ixon.Env`, every address reachable via `UsedCompiledReachAt` is stored in
`E.consts`. -/
theorem usedCompiledReachAt_contains {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S : _root_.Address → Prop}
    (hown : ∀ a c, Ix.Cert.recordAt E a = some c →
      E.consts.contains (Ix.Cert.ownerOf a c) = true)
    {a : _root_.Address} (hr : IxVM.Consistency.UsedCompiledReachAt t E S a) :
    E.consts.contains a = true := by
  induction hr with
  | seed _ hc => exact hc
  | step _ hedge _ =>
    obtain ⟨c, hrec, hstep⟩ := hedge
    rcases hstep with ⟨rfl, _⟩ | ⟨_, hc⟩
    · exact hown _ c hrec
    · exact hc
  | ground _ hg => exact hg.1
  | recursor _ hr => exact hr.1

/-- Reachable stored addresses of `E`, filtered from `E.consts.keys`. -/
noncomputable def closureReachKeys (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) : List _root_.Address :=
  E.consts.keys.filter fun a =>
    @decide (IxVM.Consistency.UsedCompiledReachAt t E S a) (Classical.propDecidable _)

/-- Explicit topological closure order obtained by filtering `E.consts.keys` to
`UsedCompiledReachAt t E S` and sorting ascending by `rk`. -/
noncomputable def closureOrderByRank (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) (rk : _root_.Address → Nat) : List _root_.Address :=
  (closureReachKeys t E S).mergeSort fun a b => decide (rk a ≤ rk b)

/-- Sorting the reachable keys of an owner-closed store `E` by any rank `rk` that strictly
decreases along `UsedRecordRef` satisfies `IxVM.Consistency.UsedClosureOrderAt`. -/
theorem usedClosureOrderAt_closureOrderByRank {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S : _root_.Address → Prop} {rk : _root_.Address → Nat}
    (hown : ∀ a c, Ix.Cert.recordAt E a = some c →
      E.consts.contains (Ix.Cert.ownerOf a c) = true)
    (hrk : ∀ a b,
      IxVM.Consistency.UsedCompiledReachAt t E S a →
      IxVM.Consistency.UsedCompiledReachAt t E S b →
      IxVM.Consistency.UsedRecordRef E a b →
      rk b < rk a) :
    IxVM.Consistency.UsedClosureOrderAt t E S (closureOrderByRank t E S rk) := by
  let reachKeys := closureReachKeys t E S
  have hnd_reach : reachKeys.Nodup :=
    List.Pairwise.filter _ Std.HashMap.nodup_keys
  have perm := List.mergeSort_perm reachKeys fun a b => decide (rk a ≤ rk b)
  have hmem_reach : ∀ a, a ∈ reachKeys ↔ IxVM.Consistency.UsedCompiledReachAt t E S a := by
    intro a
    simp only [reachKeys, closureReachKeys, List.mem_filter,
      @decide_eq_true_eq _ (Classical.propDecidable _)]
    constructor
    · exact fun h => h.2
    · intro hr
      refine ⟨?_, hr⟩
      rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains]
      exact usedCompiledReachAt_contains hown hr
  refine ⟨?_, ?_, ?_⟩
  · change ((closureReachKeys t E S).mergeSort fun a b => decide (rk a ≤ rk b)).Nodup
    exact perm.nodup_iff.mpr hnd_reach
  · intro a
    change a ∈ (closureReachKeys t E S).mergeSort (fun a b => decide (rk a ≤ rk b)) ↔ _
    exact perm.mem_iff.trans (hmem_reach a)
  · change ((closureReachKeys t E S).mergeSort fun a b => decide (rk a ≤ rk b)).Pairwise _
    have sorted := List.pairwise_mergeSort (le := fun a b => decide (rk a ≤ rk b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) reachKeys
    refine sorted.imp_of_mem fun {a b} ha hb hab href => ?_
    have hra : IxVM.Consistency.UsedCompiledReachAt t E S a :=
      (hmem_reach a).mp (perm.mem_iff.mp ha)
    have hrb : IxVM.Consistency.UsedCompiledReachAt t E S b :=
      (hmem_reach b).mp (perm.mem_iff.mp hb)
    have hlt := hrk a b hra hrb href
    simp only [decide_eq_true_eq] at hab
    omega

/-! ## Two-tier rank from `WalkedL6` (`2 * rank` on `Wk`, `2 * rank (iblock a) + 1` on extra recs) -/

/-- Two-tier rank placing walked records at even ranks `2 * rank a` and extra recursor records at
odd ranks `2 * rank (iblock a) + 1` immediately after their inductive block `iblock a`. -/
noncomputable def twoTierRank (Wk : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (iblock : _root_.Address → _root_.Address) (a : _root_.Address) : Nat :=
  haveI := Classical.propDecidable (Wk a)
  if Wk a then 2 * rank a else 2 * rank (iblock a) + 1

/-- Any `UsedRecordRef` out of a walked address `a` in `subEnv E₀ Keep supp` (where `Wk ⊆ Keep`)
resolves to a walked address `b` with `rank b < rank a`. -/
theorem usedRecordRef_of_wk {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    {a b : _root_.Address} (hwa : Wk a)
    (href : IxVM.Consistency.UsedRecordRef (subEnv E₀ Keep supp) a b) :
    Wk b ∧ rank b < rank a := by
  obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown_r, _⟩ := href
  obtain ⟨c₀, hrec_a0⟩ := hwk_rec a hwa
  have hrec_a' := recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep a hwa) hrec_a0
  rw [hrec_a] at hrec_a'
  injection hrec_a' with hc_eq
  subst hc_eq
  have hi_s0 : i ∈ Core.S0.usedRefIdxs c := by
    rw [usedRefIdxs_eq]
    exact hi
  have hedge_ar : Core.S0.WalkEdge E₀ a r := ⟨c, hrec_a0, Or.inr ⟨i, hi_s0, hr⟩⟩
  obtain ⟨hwr, hlt_ra⟩ := hwk_step a r hwa hedge_ar
  obtain ⟨cr₀, hrec_r0⟩ := hwk_rec r hwr
  have hrec_r' := recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep r hwr) hrec_r0
  rw [hrec_r] at hrec_r'
  injection hrec_r' with hcr_eq
  subst hcr_eq
  by_cases hbr : b = r
  · subst hbr
    exact ⟨hwr, hlt_ra⟩
  · have hedge_rb : Core.S0.WalkEdge E₀ r b := ⟨cr, hrec_r0, Or.inl ⟨hown_r, hbr⟩⟩
    obtain ⟨hwb, hlt_br⟩ := hwk_step r b hwr hedge_rb
    exact ⟨hwb, Nat.lt_trans hlt_br hlt_ra⟩

/-- Owner-closure of `subEnv E₀ Keep supp` when `Wk ⊆ Keep` and every non-`Wk` record in `subEnv`
is a recursor record (`IsRecursorRecord`). -/
theorem subEnv_ownerClosed_of_walked {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_rec : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Keep supp) x = some c →
      IxVM.Refinement.IsRecursorRecord c) :
    ∀ a c, Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      (subEnv E₀ Keep supp).consts.contains (Ix.Cert.ownerOf a c) = true := by
  intro a c hrec
  by_cases hwa : Wk a
  · obtain ⟨c₀, hrec₀⟩ := hwk_rec a hwa
    have hrec' := recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep a hwa) hrec₀
    rw [hrec] at hrec'
    injection hrec' with hceq
    subst hceq
    by_cases hown : Ix.Cert.ownerOf a c = a
    · rw [hown]
      exact contains_of_recordAt hrec
    · have hedge : Core.S0.WalkEdge E₀ a (Ix.Cert.ownerOf a c) :=
        ⟨c, hrec₀, Or.inl ⟨rfl, hown⟩⟩
      obtain ⟨hwb, _⟩ := hwk_step a (Ix.Cert.ownerOf a c) hwa hedge
      obtain ⟨cb, hrec_b⟩ := hwk_rec _ hwb
      exact contains_of_recordAt
        (recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep _ hwb) hrec_b)
  · rw [isRecursorRecord_ownerOf_eq a (hextra_rec a c hwa hrec)]
    exact contains_of_recordAt hrec

/-- Strict decrease of `twoTierRank` along `UsedRecordRef` on `subEnv E₀ Keep supp`. -/
theorem twoTierRank_lt_of_usedRecordRef {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {iblock : _root_.Address → _root_.Address}
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_refs : ∀ a c, ¬ Wk a → Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnv E₀ Keep supp) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a)))
    {a b : _root_.Address}
    (href : IxVM.Consistency.UsedRecordRef (subEnv E₀ Keep supp) a b) :
    twoTierRank Wk rank iblock b < twoTierRank Wk rank iblock a := by
  by_cases hwa : Wk a
  · obtain ⟨hwb, hlt⟩ := usedRecordRef_of_wk hwk_keep hwk_step hwk_rec hwa href
    simp only [twoTierRank, hwa, hwb, ↓reduceIte]
    omega
  · obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown, hne⟩ := href
    have hex := hextra_refs a c hwa hrec_a i hi r cr hr hrec_r (by rw [hown]; exact hne)
    rw [hown] at hex
    rcases hex with ⟨hwb, hle⟩ | ⟨hnwb, hlt⟩
    · simp only [twoTierRank, hwa, hwb, ↓reduceIte]
      omega
    · simp only [twoTierRank, hwa, hnwb, ↓reduceIte]
      omega

/-- **`UsedClosureOrderAt` for `subEnv E₀ Keep supp`** under the two-tier rank from `WalkedL6`. -/
theorem subEnv_twoTier_usedClosureOrderAt (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (Keep : _root_.Address → Prop) (supp : List SuppEntry) (S : _root_.Address → Prop)
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (iblock : _root_.Address → _root_.Address)
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_rec : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Keep supp) x = some c →
      IxVM.Refinement.IsRecursorRecord c)
    (hextra_refs : ∀ a c, ¬ Wk a → Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnv E₀ Keep supp) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a))) :
    IxVM.Consistency.UsedClosureOrderAt t (subEnv E₀ Keep supp) S
      (closureOrderByRank t (subEnv E₀ Keep supp) S (twoTierRank Wk rank iblock)) :=
  usedClosureOrderAt_closureOrderByRank
    (subEnv_ownerClosed_of_walked hwk_keep hwk_step hwk_rec hextra_rec)
    (fun _ _ _ _ href => twoTierRank_lt_of_usedRecordRef hwk_keep hwk_step hwk_rec hextra_refs href)

/-- **`UsedClosureOrderAt` on the pure walked sub-environment `subEnv E₀ Wk []`** directly from
`Claim.WalkedL6`, for any seed predicate `S`. -/
theorem walkedSubEnv_usedClosureOrderAt {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hwalk : Claim.WalkedL6 calls t E₀ seeds) (S : _root_.Address → Prop) :
    ∃ (E : Ixon.Env) (order : List _root_.Address),
      IxVM.Refinement.Draws E E₀ ∧
      IxVM.Consistency.UsedClosureOrderAt t E S order := by
  obtain ⟨_, _, _, _, _, _, Wk, rank, _, hstep, hwk_rec⟩ := hwalk
  have hrec_only : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c :=
    fun x hx => let ⟨c, hc, _⟩ := hwk_rec x hx; ⟨c, hc⟩
  have hvac : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Wk []) x = some c → False := by
    intro x c hnw hrec
    rcases recordAt_subEnv_some_inv E₀ Wk [] hrec with ⟨hw, _⟩ | ⟨_, _, hm⟩
    · exact hnw hw
    · cases hm
  exact ⟨subEnv E₀ Wk [],
    closureOrderByRank t (subEnv E₀ Wk []) S (twoTierRank Wk rank id),
    subEnv_draws E₀ Wk [] (fun _ hm => nomatch hm),
    subEnv_twoTier_usedClosureOrderAt t E₀ Wk [] S id (fun _ h => h) hstep hrec_only
      (fun x c hnw hrec => (hvac x c hnw hrec).elim)
      (fun a c hnw hrec => (hvac a c hnw hrec).elim)⟩

end IxVM.Refinement.Assembly
