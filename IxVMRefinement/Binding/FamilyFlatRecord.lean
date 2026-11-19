import IxVMRefinement.Binding.FamilyOfCall
import IxVMRefinement.Binding.FamilyFlatLocal
import IxVMRefinement.Binding.FamilyReconFlat

/-! # The flattened family a family record reads: `build_flat_block`, entry by entry

`KernelCheck::build_flat_block` reads a flattened family off a family record: the types of the
primary block (the block of the first recursor's major premise), then, recursor by recursor, the
auxiliary its major premise names when that is a type outside the primary block and not yet an
entry. `FamilyFlat.RecordFlat` states of such a list that recursor `k`'s major premise is over
entry `k`. `build_flat_block` alone does not place the entries at their recursors' positions: a
record whose recursors are complete (one per entry) and whose first recursors are over the block's
own types does.

* `auxOfMajor`, `majorAt`, `contribAt`, `auxWalk`, `primaryAt`, `recordFlatAt`: the list
  `build_flat_block` builds, over the canonical reading (`FamilyFlat.loadedAt`) and the store's
  readings (`FamilyFlat.FlatView.ofStore`).
* `auxWalk_prefix`, `auxWalk_full`, `auxWalk_skip`: the walk appends at most one entry per
  recursor; when it appends one per recursor, entry by entry in order; and it passes the recursors
  that contribute nothing.
* `recordFlat_of_model`: of a complete record whose first recursors have their major premises over
  the block's types at the elimination offset's levels (`horigHead`), the list is one entry per
  recursor position by position: `RecordFlat`, and the block's types first.
* `familyCall_recs_bound`, `recordFlat_of_call`, `familyOfBlock_of_model`: the same of an observed
  family check at any limit, and `FamilyOfBlock` with it.
* `spec_params_lower_spec`: `KernelCheck::spec_params_lower` on exactly represented parameters is
  `FamilyFlat.occParamsLower`.

The levels of an entry of the block's own types (`param (off + j)`) are no reading of the record:
`build_flat_originals` writes them from the block's level count and the elimination offset. That
recursor `k`'s major premise carries them (`horigHead`) is the comparison of its declared type
with the reconstruction at its own position (`KernelCheck::canonical_rules_at_pos`:
`kexpr_struct_eq (build_rec_type … self_pos) ty`, or `wrap_rel` outside a group's validation),
whose major premise is `Const (self_addr, self_occ_us)` of entry `self_pos`, with
`KernelModeled::check_rec_motive` placing `self_pos` at `k`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyFlatRecord

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding.FamilyOfCall (FamilyCallReaders)
open IxVM.Refinement.Core (KExpr KLevel KKey)

/-! ## The model of `build_flat_block` -/

/-- **What a recursor's major premise `d` adds to the flattened family**
(`aux_from_recrs_walk_ex`'s `entry_opt`, `extract_aux_spec_params_from_rec`,
`extract_aux_occ_us`): nothing (`some none`) when the type heading it is no inductive or one of
the primary block `prim`; otherwise the auxiliary entry of that type at the head's levels and the
major premise's first arguments lowered past `low` binders (the motives, minors and indices).
`none` where the circuit has no answer. -/
def auxOfMajor (V : FlatView) (prim : _root_.Address) (low : Nat) (d : KExpr) :
    Option (Option FlatEntry) :=
  match constOf (Ix.Kernel.Expr.getAppFn d) with
  | none => none
  | some (k, us) =>
    match V.addr k with
    | none => none
    | some a =>
      match V.ci a with
      | none => none
      | some none => some none
      | some (some i) =>
        match decide (i.blk = prim) with
        | true => some none
        | false =>
          match occParamsLower ((Ix.Kernel.Expr.getAppArgs d).take i.np) low with
          | none => none
          | some sp => some (some ⟨a, true, sp, us⟩)

/-- **The major premise's type of recursor `k` of the record**, in the canonical reading, with
the count of binders between the parameters and it (motives, minors and indices). -/
noncomputable def majorAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (k : Nat) : Option (KExpr × Nat) :=
  match rs[k]? with
  | some (.recr r) =>
    match loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs k) r.typ with
    | none => none
    | some ty =>
      match binderDomAfter
          (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty with
      | none => none
      | some d => some (d, r.motives.toNat + r.minors.toNat + r.indices.toNat)
  | _ => none

/-- What recursor `k` of the record adds to the flattened family over the primary block `prim`. -/
noncomputable def contribAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (prim : _root_.Address) (k : Nat) :
    Option (Option FlatEntry) :=
  match majorAt t E rb crb rs k with
  | none => none
  | some (d, low) => auxOfMajor (FlatView.ofStore t E) prim low d

/-- **`aux_from_recrs_walk_ex`**: the `n` recursors from position `k`, each one's auxiliary
appended unless already an entry (`aux_already_in`). -/
def auxWalk (c : Nat → Option (Option FlatEntry)) :
    Nat → Nat → List FlatEntry → Option (List FlatEntry)
  | 0, _, acc => some acc
  | n + 1, k, acc =>
    match c k with
    | none => none
    | some none => auxWalk c n (k + 1) acc
    | some (some e) =>
      auxWalk c n (k + 1)
        (if auxEntryIn acc e.addr e.params e.levels then acc else acc ++ [e])

/-- **`primary_parent_block_of`**: the block of the type heading the first recursor's major
premise; the block `B` for an empty record or a major premise over no inductive. -/
noncomputable def primaryAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (B : _root_.Address) :
    Option _root_.Address :=
  match rs[0]? with
  | none => some B
  | some _ =>
    match majorAt t E rb crb rs 0 with
    | none => none
    | some (d, _) =>
      match constOf (Ix.Kernel.Expr.getAppFn d) with
      | none => none
      | some (k, _) =>
        match keyAddr t k with
        | none => none
        | some a =>
          match indInfoAt E a with
          | none => none
          | some none => some B
          | some (some i) => some i.blk

/-- **`build_flat_block rb B off`**: the primary block's types at the elimination offset's levels
(`build_flat_originals`), then the recursors' auxiliaries (`detect_aux_from_recrs_ex`). -/
noncomputable def recordFlatAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (B : _root_.Address) (off : Nat) :
    Option (List FlatEntry) :=
  match primaryAt t E rb crb rs B with
  | none => none
  | some prim =>
    match membersAt E prim with
    | none => none
    | some as =>
      match originals (FlatView.ofStore t E) off as with
      | none => none
      | some os => auxWalk (contribAt t E rb crb rs prim) rs.size 0 os

/-! ## The walk, counted -/

/-- **The walk extends its entries by at most one per recursor.** -/
theorem auxWalk_prefix (c : Nat → Option (Option FlatEntry)) :
    ∀ (n k : Nat) (acc res : List FlatEntry), auxWalk c n k acc = some res →
      ∃ tl, res = acc ++ tl ∧ tl.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro k acc res h
    simp only [auxWalk, Option.some.injEq] at h
    exact ⟨[], by simp [h], Nat.le_refl _⟩
  | succ n ih =>
    intro k acc res h
    simp only [auxWalk] at h
    cases hc : c k with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none =>
        simp only [hc] at h
        obtain ⟨tl, htl, hlen⟩ := ih (k + 1) acc res h
        exact ⟨tl, htl, Nat.le_succ_of_le hlen⟩
      | some e =>
        simp only [hc] at h
        cases hin : auxEntryIn acc e.addr e.params e.levels with
        | true =>
          simp only [hin, ↓reduceIte] at h
          obtain ⟨tl, htl, hlen⟩ := ih (k + 1) acc res h
          exact ⟨tl, htl, Nat.le_succ_of_le hlen⟩
        | false =>
          simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨tl, htl, hlen⟩ := ih (k + 1) (acc ++ [e]) res h
          refine ⟨e :: tl, by rw [htl, List.append_assoc]; rfl, ?_⟩
          simp only [List.length_cons]
          omega

/-- **A walk that ends with one more entry per recursor appended every recursor's auxiliary, in
order**: recursor `k + j` contributes the entry `j` positions past the entries it started from. -/
theorem auxWalk_full (c : Nat → Option (Option FlatEntry)) :
    ∀ (n k : Nat) (acc res : List FlatEntry), auxWalk c n k acc = some res →
      res.length = acc.length + n →
      ∀ j, j < n → ∃ e, c (k + j) = some (some e) ∧ res[acc.length + j]? = some e := by
  intro n
  induction n with
  | zero => intro k acc res _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro k acc res h hlen j hj
    simp only [auxWalk] at h
    cases hc : c k with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none =>
        simp only [hc] at h
        obtain ⟨tl, htl, hl⟩ := auxWalk_prefix c n (k + 1) acc res h
        rw [htl, List.length_append] at hlen
        omega
      | some e =>
        simp only [hc] at h
        cases hin : auxEntryIn acc e.addr e.params e.levels with
        | true =>
          simp only [hin, ↓reduceIte] at h
          obtain ⟨tl, htl, hl⟩ := auxWalk_prefix c n (k + 1) acc res h
          rw [htl, List.length_append] at hlen
          omega
        | false =>
          simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
          have hlen' : res.length = (acc ++ [e]).length + n := by
            rw [hlen, List.length_append, List.length_singleton]
            omega
          cases j with
          | zero =>
            obtain ⟨tl, htl, -⟩ := auxWalk_prefix c n (k + 1) (acc ++ [e]) res h
            refine ⟨e, by rw [Nat.add_zero]; exact hc, ?_⟩
            rw [htl, Nat.add_zero, List.append_assoc]
            simp
          | succ j =>
            obtain ⟨e', hc', he'⟩ := ih (k + 1) (acc ++ [e]) res h hlen' j (by omega)
            refine ⟨e', by rw [show k + (j + 1) = k + 1 + j by omega]; exact hc', ?_⟩
            rw [List.length_append, List.length_singleton] at he'
            rw [show acc.length + (j + 1) = acc.length + 1 + j by omega]
            exact he'

/-- **The walk passes the recursors that contribute nothing.** -/
theorem auxWalk_skip (c : Nat → Option (Option FlatEntry)) :
    ∀ (m n k : Nat) (acc : List FlatEntry), (∀ j, j < m → c (k + j) = some none) →
      auxWalk c (m + n) k acc = auxWalk c n (k + m) acc := by
  intro m
  induction m with
  | zero => intro n k acc _; rw [Nat.zero_add, Nat.add_zero]
  | succ m ih =>
    intro n k acc hskip
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [auxWalk]
    have h0 := hskip 0 (Nat.succ_pos _)
    rw [Nat.add_zero] at h0
    rw [h0]
    simp only
    rw [ih n (k + 1) acc (fun j hj => by
      have := hskip (j + 1) (by omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this)]
    rw [show k + 1 + m = k + (m + 1) by omega]

/-! ## The originals and the lowered parameters -/

/-- **`originals`, entry by entry**: one entry per address, the address's own, at the levels of
its inductive type shifted by the offset. -/
theorem originals_get (V : FlatView) (off : Nat) :
    ∀ (as : List _root_.Address) (os : List FlatEntry), originals V off as = some os →
      os.length = as.length ∧
      ∀ (i : Nat) (a : _root_.Address), as[i]? = some a → ∃ info, V.ci a = some (some info) ∧
        os[i]? = some (⟨a, false, [], (List.range info.nl).map fun j => .param (off + j)⟩ :
          FlatEntry) := by
  intro as
  induction as with
  | nil =>
    intro os h
    simp only [originals, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i a hi => by simp at hi⟩
  | cons a as ih =>
    intro os h
    simp only [originals] at h
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none => simp [hc] at h
      | some info =>
        simp only [hc] at h
        cases ho : originals V off as with
        | none => simp [ho] at h
        | some os' =>
          simp only [ho, Option.some.injEq] at h
          subst h
          obtain ⟨hl, hget⟩ := ih os' ho
          refine ⟨by simp [hl], ?_⟩
          intro i b hi
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨info, hc, rfl⟩
          | succ i =>
            have hi' : as[i]? = some b := by simpa using hi
            obtain ⟨info', hc', hg⟩ := hget i b hi'
            exact ⟨info', hc', by simpa using hg⟩

/-- **`occParamsLower` lowers every parameter.** -/
theorem occParamsLower_eq : ∀ (xs : List KExpr) (d : Nat) (ys : List KExpr),
    occParamsLower xs d = some ys → ys = xs.map (Ix.Kernel.Expr.lowerBVars d 0)
  | [], d, ys, h => by
    simp only [occParamsLower, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, d, ys, h => by
    simp only [occParamsLower] at h
    cases hb : hasBVarIn 0 d x with
    | true => simp [hb] at h
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      cases ho : occParamsLower xs d with
      | none => simp [ho] at h
      | some zs =>
        simp only [ho, Option.some.injEq] at h
        subst h
        rw [occParamsLower_eq xs d zs ho]
        rfl

/-- The addresses of a block of inductive types, position by position. -/
theorem indcAddrs_get (b : _root_.Address) :
    ∀ (l : List Ixon.MutConst) (j : Nat), (∀ m ∈ l, ∃ ind, m = Ixon.MutConst.indc ind) →
      (indcAddrs b j l).length = l.length ∧
      ∀ i m, l[i]? = some m → (indcAddrs b j l)[i]? = some (memberAddr b (j + i) m)
  | [], _, _ => ⟨rfl, fun i m hi => by simp at hi⟩
  | m :: ms, j, hall => by
    obtain ⟨ind, rfl⟩ := hall m (List.mem_cons_self ..)
    obtain ⟨hl, hget⟩ := indcAddrs_get b ms (j + 1) (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
    simp only [indcAddrs]
    refine ⟨by simp [hl], ?_⟩
    intro i m' hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp
    | succ i =>
      have hi' : ms[i]? = some m' := by simpa using hi
      have := hget i m' hi'
      rw [show j + 1 + i = j + (i + 1) by omega] at this
      simpa using this

theorem take_min_length {α : Type} (n : Nat) (l : List α) :
    l.take (min n l.length) = l.take n := by
  rcases Nat.le_total n l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_length, List.take_of_length_le h]

theorem toUInt64_toNat_of_lt {k : Nat} (h : k < UInt64.size) : k.toUInt64.toNat = k := by
  change (UInt64.ofNat k).toNat = k
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- **The store's reading of a type of the block**: its level, parameter and constructor counts,
the block and its position. -/
theorem indInfoAt_member {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : FamBlockRecord E B cb ms) {k : Nat} {ind : Ixon.Inductive}
    (hk : ms[k]? = some (Ixon.MutConst.indc ind)) (hlt : k < UInt64.size) :
    indInfoAt E (memberAddr B k (.indc ind)) =
      some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, B, k⟩) := by
  have h := indInfoAt_of_iPrj (p := ⟨k.toUInt64, B⟩) (hB.members k _ hk) rfl hB.record hB.muts
    (by rw [toUInt64_toNat_of_lt hlt]; exact hk)
  rw [toUInt64_toNat_of_lt hlt] at h
  exact h

/-! ## The record's entries, position by position -/

/-- **The list `build_flat_block` builds of a complete record is the record's flattened family,
position by position.** Of the block's record facts and the readers of its family check
(`FamilyCallReaders`), a list that is the model's (`hmodel`) with one entry per recursor
(`hcov`), and the first recursors' major premises over the block's types at the elimination
offset's levels (`horigHead`: recursor `k` below the count of the block's types has its major
premise headed by the `k`-th type at the levels `param (off + j)`): recursor `k`'s major premise
is over entry `k` at its levels and, at an auxiliary, its parameters (`RecordFlat`), and the
block's types are the first entries. The auxiliaries' clauses are the walk's own
(`auxWalk_full`): a complete record's every recursor past the block's types appends its entry. -/
theorem recordFlat_of_model {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hF : FamilyCallReaders t E₀ B rb cb crb ms rs)
    (hB : FamBlockRecord E₀ B cb ms) (hpos : 0 < ms.size) (hrs_lt : rs.size < UInt64.size)
    {off : Nat} {es : List FlatEntry}
    (hmodel : recordFlatAt t E₀ rb crb rs B off = some es)
    (hcov : es.length = rs.size)
    (horigHead : ∀ (k : Nat) (r : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[k]? = some (Ixon.MutConst.recr r) → ms[k]? = some (Ixon.MutConst.indc ind) →
      ∃ ty d, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k) r.typ = some ty ∧
        binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty =
          some d ∧
        Ix.Kernel.Expr.getAppFn d = .const (keyOf t (memberAddr B k (.indc ind)))
          ((List.range ind.lvls.toNat).map fun j => .param (off + j))) :
    RecordFlat t E₀ rb crb rs es ∧
    ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      (es.map FlatEntry.addr)[i]? = some (memberAddr B i m) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hR := hF.record
  have hind_of : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      ∃ ind, m = Ixon.MutConst.indc ind := fun i m h =>
    hB.indcs m (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h))
  have hrec_of : ∀ (i : Nat) (m : Ixon.MutConst), rs[i]? = some m →
      ∃ r, m = Ixon.MutConst.recr r := fun i m h =>
    hR.recrs m (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h))
  have hmajor_orig : ∀ (k : Nat) (r : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[k]? = some (Ixon.MutConst.recr r) → ms[k]? = some (Ixon.MutConst.indc ind) →
      ∃ d, majorAt t E₀ rb crb rs k =
          some (d, r.motives.toNat + r.minors.toNat + r.indices.toNat) ∧
        Ix.Kernel.Expr.getAppFn d = .const (keyOf t (memberAddr B k (.indc ind)))
          ((List.range ind.lvls.toNat).map fun j => .param (off + j)) := by
    intro k r ind hk hm
    obtain ⟨ty, d, hty, hd, hfn⟩ := horigHead k r ind hk hm
    exact ⟨d, by simp only [majorAt, hk, hty, hd], hfn⟩
  have hprim : primaryAt t E₀ rb crb rs B = some B := by
    unfold primaryAt
    cases h0 : rs[0]? with
    | none => rfl
    | some m0 =>
      obtain ⟨r0, rfl⟩ := hrec_of 0 m0 h0
      have hm0 : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hpos
      obtain ⟨ind0, hind0⟩ := hind_of 0 _ hm0
      rw [hind0] at hm0
      obtain ⟨d, hmaj, hfn⟩ := hmajor_orig 0 r0 ind0 h0 hm0
      simp only [hmaj, hfn, constOf, keyAddr_keyOf htwf, indInfoAt_member hB hm0 (by decide)]
  unfold recordFlatAt at hmodel
  rw [hprim] at hmodel
  simp only [membersAt_of hB.record hB.muts] at hmodel
  cases ho : originals (FlatView.ofStore t E₀) off (indcAddrs B 0 ms.toList) with
  | none => simp [ho] at hmodel
  | some os =>
    simp only [ho] at hmodel
    obtain ⟨hol, hoget⟩ := originals_get _ off _ os ho
    obtain ⟨hal, haget⟩ := indcAddrs_get B ms.toList 0 hB.indcs
    have hos_len : os.length = ms.size := by rw [hol, hal, Array.length_toList]
    obtain ⟨tl, htl, htl_len⟩ := auxWalk_prefix _ _ _ _ _ hmodel
    have hle : ms.size ≤ rs.size := by
      rw [← hcov, htl, List.length_append, hos_len]
      omega
    have hms_lt : ms.size < UInt64.size := Nat.lt_of_le_of_lt hle hrs_lt
    have hos : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (Ixon.MutConst.indc ind) →
        os[i]? = some (⟨memberAddr B i (.indc ind), false, [],
          (List.range ind.lvls.toNat).map fun j => .param (off + j)⟩ : FlatEntry) := by
      intro i ind hi
      have hilt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
      have h1 := haget i _ (by rw [Array.getElem?_toList]; exact hi)
      rw [Nat.zero_add] at h1
      obtain ⟨info, hci, hg⟩ := hoget i _ h1
      have hci' : indInfoAt E₀ (memberAddr B i (.indc ind)) = some (some info) := hci
      rw [indInfoAt_member hB hi (Nat.lt_trans hilt hms_lt)] at hci'
      have hinfo := Option.some.inj (Option.some.inj hci')
      subst hinfo
      exact hg
    have hskip : ∀ j, j < ms.size → contribAt t E₀ rb crb rs B (0 + j) = some none := by
      intro j hj
      rw [Nat.zero_add]
      have hmj : ms[j]? = some ms[j] := Array.getElem?_eq_getElem hj
      obtain ⟨ind, hind⟩ := hind_of j _ hmj
      rw [hind] at hmj
      have hrj : rs[j]? = some rs[j] := Array.getElem?_eq_getElem (by omega)
      obtain ⟨r, hr⟩ := hrec_of j _ hrj
      rw [hr] at hrj
      obtain ⟨d, hmaj, hfn⟩ := hmajor_orig j r ind hrj hmj
      have hci : (FlatView.ofStore t E₀).ci (memberAddr B j (.indc ind)) =
          some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, B, j⟩) :=
        indInfoAt_member hB hmj (Nat.lt_trans hj hms_lt)
      have hadr : (FlatView.ofStore t E₀).addr (keyOf t (memberAddr B j (.indc ind))) =
          some (memberAddr B j (.indc ind)) := keyAddr_keyOf htwf _
      simp only [contribAt, hmaj, auxOfMajor, hfn, constOf, hadr, hci, decide_true]
    rw [show rs.size = ms.size + (rs.size - ms.size) by omega,
      auxWalk_skip _ _ _ _ _ hskip, Nat.zero_add] at hmodel
    have hfull := auxWalk_full _ _ _ _ _ hmodel (by rw [hcov, hos_len]; omega)
    have hes_lo : ∀ i, i < ms.size → es[i]? = os[i]? := by
      intro i hi
      rw [htl, List.getElem?_append_left (by omega)]
    refine ⟨?_, ?_⟩
    · intro k r e hk he
      rcases Nat.lt_or_ge k ms.size with hlt | hge
      · have hmk : ms[k]? = some ms[k] := Array.getElem?_eq_getElem hlt
        obtain ⟨ind, hind⟩ := hind_of k _ hmk
        rw [hind] at hmk
        rw [hes_lo k hlt, hos k ind hmk] at he
        have hee := Option.some.inj he
        subst hee
        obtain ⟨ty, d, hty, hd, hfn⟩ := horigHead k r ind hk hmk
        exact ⟨ty, d, hty, hd, hfn, fun h => by cases h⟩
      · have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hk).1
        obtain ⟨e', hc, he'⟩ := hfull (k - ms.size) (by omega)
        rw [hos_len, show ms.size + (k - ms.size) = k by omega] at he'
        rw [show ms.size + (k - ms.size) = k by omega] at hc
        have hee : e' = e := Option.some.inj (he'.symm.trans he)
        subst hee
        obtain ⟨a, hmaj, ty, d, ls, hty, hd, hfn⟩ := hF.major k r hk
        simp only [contribAt, majorAt, hk, hty, hd] at hc
        unfold auxOfMajor at hc
        rw [hfn] at hc
        have hadr : (FlatView.ofStore t E₀).addr (IxVM.Refinement.Core.keyOf t a) = some a :=
          keyAddr_keyOf htwf a
        simp only [constOf, hadr] at hc
        cases hci : (FlatView.ofStore t E₀).ci a with
        | none => simp [hci] at hc
        | some x =>
          cases x with
          | none => simp [hci] at hc
          | some i =>
            simp only [hci] at hc
            cases hdec : decide (i.blk = B) with
            | true => simp [hdec] at hc
            | false =>
              simp only [hdec] at hc
              cases hsp : occParamsLower ((Ix.Kernel.Expr.getAppArgs d).take i.np)
                  (r.motives.toNat + r.minors.toNat + r.indices.toNat) with
              | none => simp [hsp] at hc
              | some sp =>
                simp only [hsp, Option.some.injEq] at hc
                subst hc
                refine ⟨ty, d, hty, hd, hfn, fun _ => ?_⟩
                have hsp' := occParamsLower_eq _ _ _ hsp
                subst hsp'
                show ((Ix.Kernel.Expr.getAppArgs d).take
                  (((Ix.Kernel.Expr.getAppArgs d).take i.np).map _).length).map _ = _
                rw [List.length_map, List.length_take, take_min_length]
    · intro i m hi
      have hilt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
      obtain ⟨ind, rfl⟩ := hind_of i m hi
      rw [List.getElem?_map, hes_lo i hilt, hos i ind hi]
      rfl

/-! ## From an observed family check -/

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library in
/-- **The family record of an observed family check has fewer than `2^33` members**
(`KernelModeled::family_recs` loads it). -/
theorem familyCall_recs_bound {calls : List (Call IxVM.F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call IxVM.F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {crb : Ixon.Constant} {rs : Array Ixon.MutConst} (hR : FamRecRecord E₀ rb crb rs) :
    rs.size < 8589934592 := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, ⟨bR, hbR, rfl⟩, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have ext_674_784 : Heap.Extends C.m674 C.m784 :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans
      (C.evLenCtors.extends.trans C.evCtorMods.extends))
  have ext_0_784 : Heap.Extends h C.m784 :=
    ext_0_453.trans (C.evLoadBlk.extends.trans (ext_501_652.trans
      (C.evTypes.extends.trans ext_674_784)))
  exact FamilyAlias.family_recs_bound hS hH
    (Bytes.repAddressRef_heapMono₂ IxVM.Refinement.Core.addrTy ext_0_784 hbR) C.evRecs.obs
    (fun cl hcl => hsub cl (C.evRecs.sub cl hcl)) hR

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics in
/-- **`RecordFlat` of an observed family check**, at any limit, for the list `build_flat_block`
builds of its record (`hmodel`): of a complete record (`hcov`,
`KernelModeled::check_family`'s assertion that the record has one recursor per entry) whose first
recursors' major premises are over the block's types at the elimination offset's levels
(`horigHead`), `RecordFlat` and the block's types first (`recordFlat_of_model`). -/
theorem recordFlat_of_call {calls : List (Call IxVM.F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call IxVM.F)} (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms)
    (hrec : recordOf E₀ rb = some crb) (hmuts : crb.info = .muts rs)
    {off : Nat} {es : List FlatEntry}
    (hmodel : recordFlatAt t E₀ rb crb rs B off = some es)
    (hcov : es.length = rs.size)
    (horigHead : ∀ (k : Nat) (r : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[k]? = some (Ixon.MutConst.recr r) → ms[k]? = some (Ixon.MutConst.indc ind) →
      ∃ ty d, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k) r.typ = some ty ∧
        binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty =
          some d ∧
        Ix.Kernel.Expr.getAppFn d = .const (keyOf t (memberAddr B k (.indc ind)))
          ((List.range ind.lvls.toNat).map fun j => .param (off + j))) :
    RecordFlat t E₀ rb crb rs es ∧
    ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      (es.map FlatEntry.addr)[i]? = some (memberAddr B i m) := by
  obtain ⟨cb', crb', ms', rs', hF⟩ := FamilyOfCall.familyCall_readers ht hbd hS hH hfc
  have e1 : cb' = cb := Option.some.inj (hF.blockRecord.symm.trans hB.record)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hF.blockMuts.symm.trans hB.muts)
  subst e2
  have e3 : crb' = crb := Option.some.inj (hF.record.record.symm.trans hrec)
  subst e3
  have e4 : rs' = rs := Ixon.ConstantInfo.muts.inj (hF.record.muts.symm.trans hmuts)
  subst e4
  obtain ⟨cb₂, ms₂, hcb₂, hms₂, hpos, -, -⟩ := FamilyOfCall.familyCall_block_members hS hH hfc
  have e5 : cb₂ = cb' := Option.some.inj (hcb₂.symm.trans hB.record)
  subst e5
  have e6 : ms₂ = ms' := Ixon.ConstantInfo.muts.inj (hms₂.symm.trans hB.muts)
  subst e6
  have hrs := familyCall_recs_bound hS hH hfc hF.record
  exact recordFlat_of_model ht hF hB hpos (Nat.lt_trans hrs (by decide)) hmodel hcov horigHead

/-- **The family record of a block, position by position, from an observed family check and the
list `build_flat_block` builds** (`FamilyOfCall.familyOfBlock_of_call`, its count, first entries
and `RecordFlat` from `recordFlat_of_call`). Still taken of the flattened family: the carriers of
the motives past the block's own types (`haux`). -/
theorem familyOfBlock_of_model {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} (ht : t.check = .ok ())
    (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms)
    (hrec : recordOf E₀ rb = some crb) (hmuts : crb.info = .muts rs)
    {off : Nat} {es : List FlatEntry}
    (hmodel : recordFlatAt t E₀ rb crb rs B off = some es)
    (hcov : es.length = rs.size)
    (horigHead : ∀ (k : Nat) (r : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[k]? = some (Ixon.MutConst.recr r) → ms[k]? = some (Ixon.MutConst.indc ind) →
      ∃ ty d, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k) r.typ = some ty ∧
        binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty =
          some d ∧
        Ix.Kernel.Expr.getAppFn d = .const (keyOf t (memberAddr B k (.indc ind)))
          ((List.range ind.lvls.toNat).map fun j => .param (off + j)))
    (haux : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
      ∀ (j : Nat) (a : _root_.Address), ms.size ≤ j →
        (es.map FlatEntry.addr)[j]? = some a →
        ∃ n, motiveCarrierAt crb r j n = some a) :
    FamilyOfBlock E₀ B cb ms rb crb rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ rb crb rs es := by
  obtain ⟨hflat, horig⟩ :=
    recordFlat_of_call ht hbd hS hH hfc hB hrec hmuts hmodel hcov horigHead
  exact ⟨FamilyOfCall.familyOfBlock_of_call ht hbd hS hH hfc hB hrec hmuts hcov horig hflat haux,
    hflat⟩

/-! ## `spec_params_lower` -/

section Circuit

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Core (W kexprListEnum)
open IxVM (F)

/-- **`KernelCheck::spec_params_lower(sps, d)`** on exactly represented parameters is
`FamilyFlat.occParamsLower`: an observed call (the circuit asserts that no parameter mentions one
of the `d` binders) returns the parameters lowered past them, represented exactly. -/
theorem spec_params_lower_spec {κ : _root_.Address → KKey} {d : Nat}
    (hd : d < 4611686018427387904) :
    ∀ (xs : List KExpr) {x_sps r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)},
      RepList kexprListEnum (TmOExact κ) h xs x_sps →
      ObsFn W "KernelCheck::spec_params_lower" [x_sps, .field (d : F)] h r h' cs →
      Bounded cs → (∀ c ∈ cs, c ∈ root) →
      Heap.Extends h h' ∧ ∃ ys, occParamsLower xs d = some ys ∧
        RepList kexprListEnum (TmOExact κ) h' ys r := by
  intro xs
  induction xs with
  | nil =>
    intro x_sps r h h' cs root hrep ev _ _
    match Obs.«KernelCheck::spec_params_lower».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, [], rfl, Lib.rep_store_nil h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrep ld
      cases he
  | cons x xs ih =>
    intro x_sps r h h' cs root hrep ev hbd hroot
    match Obs.«KernelCheck::spec_params_lower».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons (x_sp := x_sp) (x_rest := x_rest) (v57 := v57) (m60 := m60) (cs68 := cs68)
        (v109 := v109) (v110 := v110) (m112 := m112) (cs120 := cs120) (m147 := m147)
        (cs155 := cs155) (ld12 := ld) (ev70 := evB) (heq100 := heq) (he105 := hr) (hm104 := hh)
        (ev122 := evL) (ev157 := evR) (hc174 := hc) =>
      obtain ⟨x', xs', he, hx, hrest⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2
      subst h1 h2
      have bB : Bounded cs68 := RomBound.bounded_mono hbd fun c hc' => by rw [hc]; simp [hc']
      have bL : Bounded cs120 := RomBound.bounded_mono hbd fun c hc' => by rw [hc]; simp [hc']
      have bR : Bounded cs155 := RomBound.bounded_mono hbd fun c hc' => by rw [hc]; simp [hc']
      have evB' : ObsFn W "KernelSubst::has_bvar_in_range"
          [x_sp, .field ((0 : Nat) : F), .field (d : F)] h (.field 0) m60 cs68 := by
        rw [heq] at evB
        simpa using evB
      obtain ⟨hm60, hno, hfalse⟩ :=
        has_bvar_in_range_zero_tmOExact (by decide) hd bB hx evB'
      subst hm60
      have evL' : ObsFn W "KernelSubst::expr_lower"
          [x_sp, .field (d : F), .field ((0 : Nat) : F)] m60 v109 m112 cs120 := by
        simpa using evL
      have hlow : TmOExact κ m112 (x.lowerBVars d 0) v109 :=
        expr_lower_tmOExact hd (by decide) bL hx (by rw [Nat.zero_add]; exact hno) evL'
      obtain ⟨ext, ys, hys, hrep'⟩ :=
        ih (root := root) (tmOExactList_mono evL.heap_extends hrest) evR bR
          (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      rw [hr, hh]
      refine ⟨evL.heap_extends.trans (ext.trans (Heap.Extends.snoc _ _)),
        x.lowerBVars d 0 :: ys, ?_, Lib.rep_store_cons tmOExact_heapMono₂ (hlow.mono ext) hrep'⟩
      simp only [occParamsLower, hfalse, hys, Bool.false_eq_true, ↓reduceIte]

end Circuit

end IxVM.Refinement.Binding.FamilyFlatRecord
