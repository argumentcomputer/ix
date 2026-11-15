import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Obs.KernelClaim0
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.Level
import Std.Data.HashSet.Lemmas

/-! # Twin recursor declaration refinement

Refinement of twin recursor declarations (`Ix.Kernel.Reader.lowerTwin` emitting
`.indDecl block nP` of `.recInfo` records) from `KernelCheck::check_const` and
`KernelClaim::check_muts_all` to `DeclRecTwinRunJ`, `IxVM.Consistency.InstallStep`,
`DeclStoreInv`, `EnvFacts`, and `DeclInv`:

* **Basis-pin exclusion, `letFree`, duplicate-key, and `lowerTwin` inversions**: every non-empty
  block starting with `.recInfo` has `basisPinHit block = none` (`installs (.indDecl block nP) =
  block`); heap-represented types and rule bodies are `letFree`; `firstRepeatedKey ks = none ↔
  ks.Nodup`; `recLps large (List.range n)` is a permutation of `List.range _`; and an accepted
  non-empty `lowerTwin` produces a single unpinned `.indDecl` of `.recInfo` members with distinct
  names and valid `recLps` permutations.
* **Twin block parts and canonical-to-twin peer renaming**: constructs `ws : List (TwinRecPart .anon)`
  (`mkTwinRecParts`, reading `w.model? := lookupModelInfo? env w.kC` from
  `env.find? (auxKey w.kC .model)`) and `twinPeerRename ws : KKey → KKey`, establishing key
  distinctness and freshness for `twinRecs ws ++ twinModels ws` and the peer-renaming contract.
* **Positional judgement package (`twinPosRulesJ`), staging `DeclStoreInv`, `InstallStep`, and
  `DeclInv` preservation**: establishes `JudgeFrames` and `JudgeSound` for `twinPosRulesJ`, lifts
  `rulesJ` derivations to `twinPosRulesJ`, proves intermediate `DeclStoreInv` preservation across
  `twinModels` and `twinProv`, proves `InstallStep env (.indDecl block nP) env₂` (accounting for
  `.aux _ .model` companion copies in `twinModels ws`), and proves full `DeclStoreInv`,
  `EnvModelT`, `EnvFacts`, and `DeclInv` preservation at both `twinPosRulesJ` and `rulesJ`.
* **Circuit extraction**: inverts `KernelCheck::check_const` on `Rec` constants into unconditional
  `ConstantValCheckJ twinPosRulesJ` (plus `ConstantValCheckJ rulesJ` under `PosSortLift`),
  `letFree` on the checked type and rule right-hand sides, `RuleStored` correspondence, and the
  dispatch to `KernelCheck::check_recursor_member` (native route) or
  `KernelModeled::check_family` (modeled route); and inverts `KernelClaim::check_muts_all` /
  `check_muts_member_at` on `.muts` blocks into per-member `rprjAddr` projection addresses and
  `KernelCheck::check_const` observations.
* **Parametric native/modeled interfaces and end-to-end step theorems**: defines crisp
  `TwinRuleCheckedOut`, `NativeTwinMemberOut` / `NativeTwinInputs`, and
  `ModeledTwinMemberOut` / `ModeledTwinInputs` contracts and proves end-to-end twin declaration
  refinement at both `twinPosRulesJ` and `rulesJ`. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule BasisKind EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ DeclRunJ IndRoutesJ
  TwinRuleJ TwinRecPart twinModels twinProv twinRecs DeclRecTwinRunJ WrapRel letFree)
open Ix.Kernel.Model (rulesJ EnvModel EnvModelM EnvModelT JudgeFrames JudgeSound NewSat)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Section 1: Basis-pin exclusion, `letFree`, `firstRepeatedKey`, `recLps`, and `lowerTwin` -/

/-- No pinned basis block starts with a `.recInfo` entry, so `canonEqList` against `k.decls` is
`false` for every `BasisKind`. -/
theorem canonEqList_recInfo_cons_basis_false (cv : ConstantVal md) (mI rP : Nat)
    (rules : List (RecRule md)) (rest : List (ConstantInfo md)) (k : BasisKind) :
    Ix.Kernel.canonEqList (.recInfo cv mI rP rules :: rest) k.decls = false := by
  rw [Ix.Kernel.canonEqList_eq_canonEqListFast]
  cases k <;> rfl

/-- Any block whose head is `.recInfo` is unpinned (`basisPinHit = none`). -/
theorem basisPinHit_recInfo_cons_none (cv : ConstantVal md) (mI rP : Nat)
    (rules : List (RecRule md)) (rest : List (ConstantInfo md)) :
    Ix.Kernel.basisPinHit (.recInfo cv mI rP rules :: rest) = none := by
  unfold Ix.Kernel.basisPinHit
  cases ([BasisKind.eqK, .natK, .punitK, .emptyK, .falseK].find? fun k =>
      k.decls.map (·.name) == (.recInfo cv mI rP rules :: rest).map (·.name)) with
  | none => rfl
  | some k =>
    simp [Option.filter, canonEqList_recInfo_cons_basis_false]

/-- Any non-empty twin recursor block is unpinned (`basisPinHit block = none`). -/
theorem basisPinHit_twinBlock_none {ws : List (TwinRecPart md)} {block : List (ConstantInfo md)}
    (hne : ws ≠ [])
    (hblk : block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW)) :
    Ix.Kernel.basisPinHit block = none := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons w rest =>
    rw [hblk, List.map_cons]
    exact basisPinHit_recInfo_cons_none w.cvW w.mI w.rP w.rulesW _

/-- `IxVM.Consistency.installs` on a non-empty twin recursor `.indDecl` equals `block`. -/
theorem installs_twinBlock_eq {ws : List (TwinRecPart .anon)} {block : List KConstantInfo}
    (nP : Nat) (hne : ws ≠ [])
    (hblk : block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW)) :
    IxVM.Consistency.installs (.indDecl block nP) = block := by
  simp [IxVM.Consistency.installs, basisPinHit_twinBlock_none hne hblk]

/-- Recover `letFree e = true` from `letFree (posOf ps e) = true` when
`ps.Perm (List.range ps.length)`. -/
theorem letFree_of_posOf_perm {ps : List LevelParam} {e : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hlf : letFree (posOf ps e) = true) :
    letFree e = true := by
  rw [← posOf_perm_inv hperm e]
  exact letFree_instantiateLevelParams (List.range ps.length) (ps.map .param) hlf

/-- Every constant whose header is represented by `ValRepExact` has a `letFree` type. -/
theorem ValRepExact.letFree_type {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty : SourceValue F} {cv : KConstantVal}
    (hv : ValRepExact κ h nl ty cv) :
    letFree cv.type = true := by
  obtain ⟨_, _, hperm, htm⟩ := hv
  exact letFree_of_posOf_perm hperm (TmExact.letFree (htm 0 (fun _ => .sort .zero)))

/-- Every recursor rule represented by `RuleRepExact` under a valid level-parameter permutation has
a `letFree` right-hand side. -/
theorem RuleRepExact.letFree_rhs {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List LevelParam} {j : Nat} {v : SourceValue F} {rl : RecRule .anon}
    (hperm : ps.Perm (List.range ps.length))
    (hr : RuleRepExact κ h ps j v rl) :
    letFree rl.rhs = true := by
  obtain ⟨_, _, _, htm⟩ := hr
  exact letFree_of_posOf_perm hperm (TmExact.letFree (htm 0 (fun _ => .sort .zero)))

/-- Every recursor rule in a `RulesRepExact` list under a valid level-parameter permutation has a
`letFree` right-hand side. -/
theorem RulesRepExact.letFree_rhs {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List LevelParam} {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)}
    (hperm : ps.Perm (List.range ps.length))
    (hrs : RulesRepExact κ h ps j v rls) :
    ∀ rl ∈ rls, letFree rl.rhs = true := by
  induction hrs with
  | nil => intro _ hm; exact nomatch hm
  | cons _ hr _ ih =>
    intro rl hmem
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact hr.letFree_rhs hperm
    · exact ih rl htl

private theorem foldl_firstRepeatedKeyStep_some :
    ∀ (l : List (Ix.Kernel.Reader.CName md)) (a : Ix.Kernel.Reader.CName md)
      (s : Std.HashSet (Ix.Kernel.Reader.CName md)),
      (l.foldl Ix.Kernel.Reader.firstRepeatedKeyStep (some a, s)).1 = some a
  | [], _, _ => rfl
  | _ :: l, a, s => foldl_firstRepeatedKeyStep_some l a s

private theorem foldl_firstRepeatedKeyStep_none :
    ∀ (l pre : List (Ix.Kernel.Reader.CName md))
      (s : Std.HashSet (Ix.Kernel.Reader.CName md)),
      (∀ x, s.contains x = true ↔ x ∈ pre) →
      pre.Nodup →
      ((l.foldl Ix.Kernel.Reader.firstRepeatedKeyStep (none, s)).1 = none ↔ (pre ++ l).Nodup)
  | [], pre, _, _, hn => by simpa using hn
  | x :: l, pre, s, hs, hn => by
    simp only [List.foldl_cons]
    by_cases hx : s.contains x = true
    · simp only [Ix.Kernel.Reader.firstRepeatedKeyStep, hx, ↓reduceIte]
      rw [foldl_firstRepeatedKeyStep_some]
      have hm : x ∈ pre := (hs x).mp hx
      simp only [reduceCtorEq, false_iff]
      intro hnd
      rw [List.nodup_append] at hnd
      exact hnd.2.2 x hm x List.mem_cons_self rfl
    · have hx' : x ∉ pre := fun hm => hx ((hs x).mpr hm)
      simp only [Ix.Kernel.Reader.firstRepeatedKeyStep, hx, Bool.false_eq_true, ↓reduceIte]
      have hs' : ∀ y, (s.insert x).contains y = true ↔ y ∈ pre ++ [x] := by
        intro y
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs y, beq_iff_eq, List.mem_append,
          List.mem_singleton]
        constructor
        · rintro (rfl | h)
          · exact Or.inr rfl
          · exact Or.inl h
        · rintro (h | rfl)
          · exact Or.inr h
          · exact Or.inl rfl
      have hn' : (pre ++ [x]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hn, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hx' ha
      rw [foldl_firstRepeatedKeyStep_none l (pre ++ [x]) (s.insert x) hs' hn']
      simp

/-- `Ix.Kernel.Reader.firstRepeatedKey ks = none` holds iff `ks.Nodup`. -/
theorem firstRepeatedKey_eq_none_iff_nodup {ks : List (Ix.Kernel.Reader.CName md)} :
    Ix.Kernel.Reader.firstRepeatedKey ks = none ↔ ks.Nodup := by
  have h := foldl_firstRepeatedKeyStep_none ks [] {} (by simp) List.nodup_nil
  rw [List.nil_append] at h
  exact h

/-- `Ix.Kernel.Reader.recLps large (List.range n)` is a permutation of `List.range` of its own
length (`n + 1` when `large = true`, `n` when `large = false`). -/
theorem recLps_perm_range (large : Bool) (n : Nat) :
    (Ix.Kernel.Reader.recLps large (List.range n)).Perm
      (List.range (Ix.Kernel.Reader.recLps large (List.range n)).length) := by
  cases large with
  | false =>
    simp only [Ix.Kernel.Reader.recLps, Bool.false_eq_true, ↓reduceIte, List.length_range]
    exact List.Perm.refl _
  | true =>
    simp only [Ix.Kernel.Reader.recLps, ↓reduceIte, List.length_cons, List.length_range]
    show ([n] ++ List.range n).Perm (List.range (n + 1))
    rw [List.range_succ]
    exact List.perm_append_comm

private theorem except_bind_ok_inv {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem readM_ite_ok {α : Type} {c : Prop} [Decidable c]
    {x y : Ix.Kernel.Reader.ReadM α} {r : α}
    (h : (if c then x else y) = .ok r) : x = .ok r ∨ y = .ok r := by
  by_cases hc : c
  · exact .inl (by simpa [hc] using h)
  · exact .inr (by simpa [hc] using h)

private theorem readM_throw_ok {α : Type} {e : Ix.Kernel.Reader.ReadError} {r : α}
    (h : (throw e : Ix.Kernel.Reader.ReadM α) = .ok r) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem readM_fail_bind {α β : Type} {e : Ix.Kernel.Reader.ReadError}
    {f : α → Ix.Kernel.Reader.ReadM β} {r : β}
    (h : ((throw e : Ix.Kernel.Reader.ReadM α) >>= f) = .ok r) : False := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

private theorem forIn_push_list_inv {α β : Type} (g : α → Ix.Kernel.Reader.ReadM β) :
    ∀ (xs : List α) (acc res : Array β),
      forIn (m := Ix.Kernel.Reader.ReadM) xs acc
        (fun x s => do let y ← g x; pure (ForInStep.yield (s.push y))) = .ok res →
      ∃ ys : List β, List.Forall₂ (fun x y => g x = .ok y) xs ys ∧
        res.toList = acc.toList ++ ys
  | [], acc, res, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], .nil, by simp⟩
  | x :: xs, acc, res, h => by
    simp only [List.forIn_cons] at h
    obtain ⟨step, hstep, hrest⟩ := except_bind_ok_inv h
    obtain ⟨y, hy, hpure⟩ := except_bind_ok_inv hstep
    simp only [pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    obtain ⟨ys, hrel, hlist⟩ := forIn_push_list_inv g xs (acc.push y) res hrest
    refine ⟨y :: ys, .cons hy hrel, ?_⟩
    rw [hlist, Array.toList_push, List.append_assoc, List.singleton_append]

/-- Inversion of `Ix.Kernel.Reader.readRecursor` on `.ok`: extracts the member reference shape,
member-key lookup, and `recLps` level-parameter list. -/
theorem readRecursor_ok_inv {cx : Ix.Kernel.Reader.Ctx md} {blockLps : List LevelParam}
    {ref : Ix.Kernel.ConstRef _root_.Address} {entry : Ix.Kernel.Reader.RecEntry}
    {res : Ix.Kernel.Reader.CVal md × Ix.Kernel.Reader.RecCounts × List (RecRule md)}
    (h : Ix.Kernel.Reader.readRecursor cx blockLps ref entry = .ok res) :
    (∃ rOwner j, ref = .member rOwner j) ∧
    cx.memberKey ref = .ok res.1.name ∧
    res.1.levelParams = Ix.Kernel.Reader.recLps entry.large blockLps := by
  unfold Ix.Kernel.Reader.readRecursor at h
  split at h
  · rename_i rOwner j
    split at h
    · split at h
      · rcases readM_ite_ok h with h | h
        · exact (readM_fail_bind h).elim
        · obtain ⟨key, hkey, h⟩ := except_bind_ok_inv h
          obtain ⟨typ, _, h⟩ := except_bind_ok_inv h
          split at h
          · rcases readM_ite_ok h with h | h
            · split at h
              · obtain ⟨rules, _, h⟩ := except_bind_ok_inv h
                simp only [pure, Except.pure, Except.ok.injEq] at h
                subst h
                exact ⟨⟨rOwner, j, rfl⟩, hkey, rfl⟩
              · exact (readM_throw_ok h).elim
            · exact (readM_fail_bind h).elim
          · exact (readM_throw_ok h).elim
      · exact (readM_throw_ok h).elim
    · exact (readM_throw_ok h).elim
  · exact (readM_throw_ok h).elim

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ b ∈ ys, ∃ a ∈ xs, R a b
  | [], [], .nil, _, hb => nomatch hb
  | a :: _, _ :: _, .cons hr _, _, .head _ => ⟨a, List.mem_cons_self, hr⟩
  | _ :: _, _ :: _, .cons _ htl, b, .tail _ hb =>
    let ⟨a', ha', hr⟩ := forall₂_mem_right htl b hb
    ⟨a', List.mem_cons_of_mem _ ha', hr⟩

/-- **Inversion of `Ix.Kernel.Reader.lowerTwin`** on a non-empty `twins` array: produces a single
unpinned `.indDecl block nPd` with `rd.generated = 0`, `block ≠ []`, pairwise distinct member
names `(block.map (·.name)).Nodup`, `basisPinHit block = none`, and a one-for-one `readRecursor`
correspondence with `twins.toList` ensuring every member's `levelParams` is `recLps entry.large
(List.range nLvls)` (hence a permutation of `List.range cv.levelParams.length`). -/
theorem lowerTwin_ok_inv {cx : Ix.Kernel.Reader.Ctx md}
    {twins : Array (Ix.Kernel.ConstRef _root_.Address × Ix.Kernel.Reader.RecEntry)}
    {rd : Ix.Kernel.Reader.Read md}
    (hne : twins ≠ #[])
    (h : Ix.Kernel.Reader.lowerTwin cx twins = .ok rd) :
    ∃ (block : List (ConstantInfo md)) (nPd nLvls : Nat)
      (recs : List (Ix.Kernel.Reader.CVal md × Ix.Kernel.Reader.RecCounts × List (RecRule md))),
      rd = { decls := #[.indDecl block nPd] } ∧
      rd.generated = 0 ∧
      block ≠ [] ∧
      Ix.Kernel.basisPinHit block = none ∧
      (block.map (·.name)).Nodup ∧
      List.Forall₂
        (fun x rv => Ix.Kernel.Reader.readRecursor cx (List.range nLvls) x.1 x.2 = .ok rv)
        twins.toList recs ∧
      block = recs.map (fun (cv, r, rules) =>
        .recInfo cv (r.params + r.motives + r.minors + r.indices)
          (r.params + r.motives + r.minors) rules) ∧
      (∀ ci ∈ block, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules ∧
        cv.levelParams.Perm (List.range cv.levelParams.length)) := by
  unfold Ix.Kernel.Reader.lowerTwin at h
  split at h
  · dsimp only at h
    rcases readM_ite_ok h with h | h
    · split at h
      · split at h
        · split at h
          · rcases readM_ite_ok h with h | h
            · split at h
              · rename_i first _
                rcases readM_ite_ok h with h | h
                · exact (readM_fail_bind h).elim
                · rcases readM_ite_ok h with h | h
                  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
                    obtain ⟨recsArr, hrecs, h⟩ := except_bind_ok_inv h
                    rw [← Array.forIn_toList] at hrecs
                    obtain ⟨recsList, hrel, htoList⟩ :=
                      forIn_push_list_inv
                        (fun x => Ix.Kernel.Reader.readRecursor cx (List.range first.lvls.toNat) x.1 x.2)
                        twins.toList #[] recsArr hrecs
                    rw [Array.toList_empty, List.nil_append] at htoList
                    simp only [ite_not, bne_iff_ne, ne_eq] at h
                    have finish :
                        let recInfos : List (ConstantInfo md) := recsArr.toList.map fun (cv, r, rules) =>
                          .recInfo cv (r.params + r.motives + r.minors + r.indices)
                            (r.params + r.motives + r.minors) rules
                        (if let some k := Ix.Kernel.Reader.firstRepeatedKey (recInfos.map (·.name)) then
                          Ix.Kernel.Reader.declined s!"recursor block declares {k} twice"
                        else (pure ({ decls := #[.indDecl recInfos first.params.toNat] } : Ix.Kernel.Reader.Read md) :
                          Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.Read md))) = .ok rd →
                        ∃ (block : List (ConstantInfo md)) (nPd nLvls : Nat)
                          (recs : List (Ix.Kernel.Reader.CVal md × Ix.Kernel.Reader.RecCounts × List (RecRule md))),
                          rd = { decls := #[.indDecl block nPd] } ∧
                          rd.generated = 0 ∧
                          block ≠ [] ∧
                          Ix.Kernel.basisPinHit block = none ∧
                          (block.map (·.name)).Nodup ∧
                          List.Forall₂
                            (fun x rv => Ix.Kernel.Reader.readRecursor cx (List.range nLvls) x.1 x.2 = .ok rv)
                            twins.toList recs ∧
                          block = recs.map (fun (cv, r, rules) =>
                            .recInfo cv (r.params + r.motives + r.minors + r.indices)
                              (r.params + r.motives + r.minors) rules) ∧
                          (∀ ci ∈ block, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules ∧
                            cv.levelParams.Perm (List.range cv.levelParams.length)) := by
                      intro recInfos hfin
                      cases hrep : Ix.Kernel.Reader.firstRepeatedKey (recInfos.map (·.name)) with
                      | some k =>
                        rw [hrep] at hfin
                        exact (readM_throw_ok hfin).elim
                      | none =>
                        rw [hrep] at hfin
                        simp only [pure, Except.pure, Except.ok.injEq] at hfin
                        subst hfin
                        have hnd : (recInfos.map (·.name)).Nodup :=
                          firstRepeatedKey_eq_none_iff_nodup.mp hrep
                        have hblk_eq : recInfos = recsList.map (fun (cv, r, rules) =>
                            .recInfo cv (r.params + r.motives + r.minors + r.indices)
                              (r.params + r.motives + r.minors) rules) := by
                          show recsArr.toList.map _ = recsList.map _
                          rw [htoList]
                        have htwins_ne : twins.toList ≠ [] := by
                          intro hempty
                          exact hne (Array.ext' hempty)
                        have hrecs_ne : recsList ≠ [] := by
                          intro hempty
                          have hlen := hrel.length_eq
                          rw [hempty] at hlen
                          exact htwins_ne (List.eq_nil_of_length_eq_zero hlen)
                        have hblk_ne : recInfos ≠ [] := by
                          rw [hblk_eq]
                          cases recsList with
                          | nil => exact absurd rfl hrecs_ne
                          | cons _ _ => simp
                        have hpin : Ix.Kernel.basisPinHit recInfos = none := by
                          rw [hblk_eq]
                          cases recsList with
                          | nil => exact absurd rfl hrecs_ne
                          | cons hd tl =>
                            exact basisPinHit_recInfo_cons_none hd.1 _ _ hd.2.2 _
                        refine ⟨recInfos, first.params.toNat, first.lvls.toNat, recsList,
                          rfl, rfl, hblk_ne, hpin, hnd, hrel, hblk_eq, ?_⟩
                        intro ci hci
                        rw [hblk_eq] at hci
                        obtain ⟨⟨cv, r, rules⟩, hmem, rfl⟩ := List.mem_map.mp hci
                        obtain ⟨x, _, hok⟩ := forall₂_mem_right hrel (cv, r, rules) hmem
                        obtain ⟨_, _, hlps⟩ := readRecursor_ok_inv hok
                        refine ⟨cv, _, _, rules, rfl, ?_⟩
                        rw [hlps]
                        exact recLps_perm_range x.2.large first.lvls.toNat
                    split at h
                    all_goals
                      rcases readM_ite_ok h with h | h
                      all_goals obtain ⟨_, _, h⟩ := except_bind_ok_inv h
                      all_goals exact finish h
                  · exact (readM_fail_bind h).elim
              · exact (readM_throw_ok h).elim
            · exact (readM_fail_bind h).elim
          · exact (readM_throw_ok h).elim
        · exact (readM_throw_ok h).elim
      · exact (readM_throw_ok h).elim
    · exact (readM_fail_bind h).elim
  · rename_i h0
    exfalso
    apply hne
    apply Array.ext'
    cases htl : twins.toList with
    | nil => rfl
    | cons x xs =>
      have hget0 : twins[0]? = some (x.1, x.2) := by
        have := congrArg (·[0]?) htl
        simpa [Array.getElem?_toList] using this
      exact False.elim (h0 x.1 x.2 hget0)

/-! ## Section 2: `lookupModelInfo?`, `ws` construction, and peer renaming `twinPeerRename` -/

/-- Read the stored `.model` companion definition `(cvm, mval, hint)` of a canonical recursor `kC`
from `env`, if `env` stores `.defnInfo cvm mval hint` at `auxKey kC .model`. -/
def lookupModelInfo? (env : Ix.Kernel.Env .anon) (kC : KKey) :
    Option (KConstantVal × KExpr × Ix.Kernel.ReducibilityHint) :=
  match env.find? (Ix.Kernel.auxKey kC .model) with
  | some (.defnInfo cvm mval hint) => some (cvm, mval, hint)
  | _ => none

theorem lookupModelInfo?_eq_some {env : Ix.Kernel.Env .anon} {kC : KKey}
    {cvm : KConstantVal} {mval : KExpr} {hint : Ix.Kernel.ReducibilityHint} :
    lookupModelInfo? env kC = some (cvm, mval, hint) ↔
      env.find? (Ix.Kernel.auxKey kC .model) = some (.defnInfo cvm mval hint) := by
  unfold lookupModelInfo?
  cases hf : env.find? (Ix.Kernel.auxKey kC .model) with
  | none => simp
  | some ci => cases ci <;> simp

theorem lookupModelInfo?_eq_none {env : Ix.Kernel.Env .anon} {kC : KKey} :
    lookupModelInfo? env kC = none ↔
      ∀ cvm mval hint,
        env.find? (Ix.Kernel.auxKey kC .model) ≠ some (.defnInfo cvm mval hint) := by
  unfold lookupModelInfo?
  cases hf : env.find? (Ix.Kernel.auxKey kC .model) with
  | none => simp
  | some ci => cases ci <;> simp

/-- Raw/checked/canonical data for one member of a twin recursor block, before attaching
`model? := lookupModelInfo? env kC`. -/
structure TwinMemberData where
  cvW : KConstantVal
  cvW' : KConstantVal
  cvC : KConstantVal
  kC : KKey
  mI : Nat
  rP : Nat
  rulesW : List (RecRule .anon)
  rulesW' : List (RecRule .anon)
  rulesC : List (RecRule .anon)

/-- Assemble a `TwinRecPart .anon` from `TwinMemberData` by reading `model?` from `env` at
`auxKey d.kC .model`. -/
def TwinMemberData.toPart (env : Ix.Kernel.Env .anon) (d : TwinMemberData) : TwinRecPart .anon where
  cvW := d.cvW
  cvW' := d.cvW'
  cvC := d.cvC
  kC := d.kC
  mI := d.mI
  rP := d.rP
  rulesW := d.rulesW
  rulesW' := d.rulesW'
  rulesC := d.rulesC
  model? := lookupModelInfo? env d.kC

/-- Build `ws : List (TwinRecPart .anon)` from a list of `TwinMemberData` against `env`. -/
def mkTwinRecParts (env : Ix.Kernel.Env .anon) (ds : List TwinMemberData) :
    List (TwinRecPart .anon) :=
  ds.map (TwinMemberData.toPart env)

/-- **Canonical-to-twin peer renaming** `f : KKey → KKey` induced by `ws`: maps each canonical
recursor key `w.kC` in `ws` to the first matching twin's key `w.cvW.name`, and fixes every other
key. -/
def twinPeerRename (ws : List (TwinRecPart .anon)) (k : KKey) : KKey :=
  match ws.find? (fun w => w.kC == k) with
  | some w => w.cvW.name
  | none => k

private theorem find?_kC_eq_some :
    ∀ {ws : List (TwinRecPart .anon)} {k : KKey} {w : TwinRecPart .anon},
      ws.find? (fun x => x.kC == k) = some w → w ∈ ws ∧ w.kC = k
  | [], _, _, h => nomatch h
  | x :: xs, k, w, h => by
    simp only [List.find?] at h
    cases hxk : (x.kC == k)
    · rw [hxk] at h
      obtain ⟨hm, heq⟩ := find?_kC_eq_some h
      exact ⟨List.mem_cons_of_mem _ hm, heq⟩
    · rw [hxk] at h
      obtain rfl := Option.some.inj h
      exact ⟨List.mem_cons_self, beq_iff_eq.mp hxk⟩

/-- `twinPeerRename ws` unconditionally satisfies the renaming contract of `DeclRecTwinRunJ`. -/
theorem twinPeerRename_spec (ws : List (TwinRecPart .anon)) (k : KKey) :
    twinPeerRename ws k = k ∨
      ∃ w' ∈ ws, k = w'.kC ∧ twinPeerRename ws k = w'.cvW.name := by
  unfold twinPeerRename
  cases hf : ws.find? (fun w => w.kC == k) with
  | none => exact Or.inl rfl
  | some w' =>
    obtain ⟨hmem, heq⟩ := find?_kC_eq_some hf
    exact Or.inr ⟨w', hmem, heq.symm, rfl⟩

/-- When `ws` assigns a coherent twin name to equal `kC` keys, `twinPeerRename ws` maps every
`w ∈ ws` from `w.kC` to `w.cvW.name`. -/
theorem twinPeerRename_apply_of_coherent {ws : List (TwinRecPart .anon)}
    (hcoh : ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁.kC = w₂.kC → w₁.cvW.name = w₂.cvW.name)
    {w : TwinRecPart .anon} (hw : w ∈ ws) :
    twinPeerRename ws w.kC = w.cvW.name := by
  unfold twinPeerRename
  cases hf : ws.find? (fun w' => w'.kC == w.kC) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf w hw
    simp at hfalse
  | some w' =>
    obtain ⟨hw', heq⟩ := find?_kC_eq_some hf
    exact hcoh w' hw' w hw heq

private theorem eq_of_mem_nodup_map {α β : Type} {f : α → β} :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b
  | [], _, _, ha, _, _, _ => nomatch ha
  | x :: xs, hnd, a, ha, b, hb, heq => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exfalso
        exact hnot (List.mem_map.mpr ⟨b, hb', heq.symm⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exfalso
        exact hnot (List.mem_map.mpr ⟨a, ha', heq⟩)
      · exact eq_of_mem_nodup_map hnd' a ha' b hb' heq

/-- When `(ws.map (·.kC)).Nodup`, `twinPeerRename ws w.kC = w.cvW.name` for every `w ∈ ws`. -/
theorem twinPeerRename_apply_of_nodup {ws : List (TwinRecPart .anon)}
    (hnd : (ws.map (·.kC)).Nodup) {w : TwinRecPart .anon} (hw : w ∈ ws) :
    twinPeerRename ws w.kC = w.cvW.name :=
  twinPeerRename_apply_of_coherent
    (fun w₁ hw₁ w₂ hw₂ heq => congrArg (·.cvW.name) (eq_of_mem_nodup_map hnd w₁ hw₁ w₂ hw₂ heq))
    hw

/-- `twinPeerRename ws` fixes every key outside `ws.map (·.kC)`. -/
theorem twinPeerRename_of_not_mem {ws : List (TwinRecPart .anon)} {k : KKey}
    (hnot : ∀ w ∈ ws, k ≠ w.kC) :
    twinPeerRename ws k = k := by
  unfold twinPeerRename
  cases hf : ws.find? (fun w => w.kC == k) with
  | none => rfl
  | some w =>
    obtain ⟨hw, heq⟩ := find?_kC_eq_some hf
    exact absurd heq.symm (hnot w hw)

/-- If `e` mentions no canonical recursor `w.kC` in `ws`, `e.renameConsts (twinPeerRename ws) = e`. -/
theorem renameConsts_twinPeerRename_eq_self (ws : List (TwinRecPart .anon)) :
    ∀ {e : KExpr}, (∀ w ∈ ws, e.mentionsConst w.kC = false) →
      e.renameConsts (twinPeerRename ws) = e := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [Expr.renameConsts]
    exact congrArg (Expr.fvar idx) (ih h)
  | const n us =>
    intro h
    simp only [Expr.renameConsts]
    have hfix : twinPeerRename ws n = n := by
      apply twinPeerRename_of_not_mem
      intro w hw hne
      have hm := h w hw
      rw [← hne] at hm
      simp [Expr.mentionsConst] at hm
    rw [hfix]
  | app a b iha ihb =>
    intro h
    have ha : ∀ w ∈ ws, a.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.1
    have hb : ∀ w ∈ ws, b.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.2
    simp only [Expr.renameConsts, iha ha, ihb hb]
  | lam ty bo m iht ihb =>
    intro h
    have ht : ∀ w ∈ ws, ty.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.1
    have hb : ∀ w ∈ ws, bo.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.2
    simp only [Expr.renameConsts, iht ht, ihb hb]
  | forallE ty bo m iht ihb =>
    intro h
    have ht : ∀ w ∈ ws, ty.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.1
    have hb : ∀ w ∈ ws, bo.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.2
    simp only [Expr.renameConsts, iht ht, ihb hb]
  | letE ty v bo lm iht ihv ihb =>
    intro h
    have ht : ∀ w ∈ ws, ty.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
      exact hm.1.1
    have hv : ∀ w ∈ ws, v.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
      exact hm.1.2
    have hb : ∀ w ∈ ws, bo.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
      exact hm.2
    simp only [Expr.renameConsts, iht ht, ihv hv, ihb hb]
  | proj s i sub ih =>
    intro h
    have hs : ∀ w ∈ ws, sub.mentionsConst w.kC = false := fun w hw => by
      have hm := h w hw; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm; exact hm.2
    simp only [Expr.renameConsts, ih hs]

private theorem auxKey_model_inj {k₁ k₂ : KKey}
    (h : Ix.Kernel.auxKey k₁ .model = Ix.Kernel.auxKey k₂ .model) : k₁ = k₂ := by
  unfold Ix.Kernel.auxKey at h
  injection h

private theorem twinModels_names_sub (ws : List (TwinRecPart .anon)) :
    ∀ ci ∈ twinModels ws,
      ∃ w ∈ ws, w.model?.isSome = true ∧ ci.name = Ix.Kernel.auxKey w.cvW.name .model := by
  intro ci hci
  obtain ⟨w, hw, hmi⟩ := List.mem_filterMap.mp hci
  unfold TwinRecPart.modelInfo? at hmi
  obtain ⟨⟨cvm, mval, hint⟩, hm, rfl⟩ := Option.map_eq_some_iff.mp hmi
  exact ⟨w, hw, by simp [hm], rfl⟩

private theorem twinModels_names_nodup :
    ∀ {ws : List (TwinRecPart .anon)},
      (ws.map (·.cvW.name)).Nodup →
      ((twinModels ws).map (·.name)).Nodup
  | [], _ => List.nodup_nil
  | w :: ws, hnd => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have ih := twinModels_names_nodup hnd'
    cases hm : w.model? with
    | none =>
      simp only [twinModels, List.filterMap_cons, TwinRecPart.modelInfo?, hm, Option.map_none]
      exact ih
    | some triple =>
      rcases triple with ⟨cvm, mval, hint⟩
      simp only [twinModels, List.filterMap_cons, TwinRecPart.modelInfo?, hm, Option.map_some,
        List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨ci, hci, heq⟩ := List.mem_map.mp hmem
      obtain ⟨w', hw', _, hname'⟩ := twinModels_names_sub ws ci hci
      have hsame : w'.cvW.name = w.cvW.name := by
        apply auxKey_model_inj
        rw [← hname', heq]
        rfl
      exact hnot (List.mem_map.mpr ⟨w', hw', hsame⟩)

/-- Distinctness of `(twinRecs ws ++ twinModels ws).map (·.name)` from distinctness of
`ws.map (·.cvW.name)`, name preservation `w.cvW'.name = w.cvW.name`, and non-`aux` keys for twin
recursors. -/
theorem twinRecs_append_twinModels_nodup {ws : List (TwinRecPart .anon)}
    (hnd : (ws.map (·.cvW.name)).Nodup)
    (hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name)
    (hnot_aux : ∀ w ∈ ws, ∀ k tk, w.cvW.name ≠ .aux k tk) :
    ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup := by
  have hmap_recs : (twinRecs ws).map (·.name) = ws.map (·.cvW.name) := by
    simp only [twinRecs, List.map_map]
    exact List.map_congr_left fun w hw => hname_eq w hw
  rw [List.map_append, hmap_recs]
  refine List.nodup_append.mpr ⟨hnd, twinModels_names_nodup hnd, ?_⟩
  intro x hx y hy hxy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hy
  obtain ⟨w', _, _, hci_name⟩ := twinModels_names_sub ws ci hci
  rw [hci_name] at hxy
  exact hnot_aux w hw w'.cvW.name .model hxy

/-- Freshness of `twinRecs ws ++ twinModels ws` in `env` from freshness of the twin recursor keys
and their `.model` companion keys. -/
theorem twinRecs_append_twinModels_fresh {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name)
    (hfr_rec : ∀ w ∈ ws, env.find? w.cvW.name = none)
    (hfr_mod : ∀ w ∈ ws, w.model?.isSome = true →
      env.find? (Ix.Kernel.auxKey w.cvW.name .model) = none) :
    ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none := by
  intro ci hci
  rcases List.mem_append.mp hci with hrec | hmod
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
    show env.find? w.cvW'.name = none
    rw [hname_eq w hw]
    exact hfr_rec w hw
  · obtain ⟨w, hw, hsome, hname⟩ := twinModels_names_sub ws ci hmod
    rw [hname]
    exact hfr_mod w hw hsome

/-! ## Section 3: `twinPosRulesJ`, staging `DeclStoreInv`, `InstallStep`, and `DeclInv` -/

namespace TwinPos

/-- Inverse of `posOf ps`, mapping positional parameters `0, …, ps.length - 1` back to `ps`. -/
def invPosOf (ps : List LevelParam) (e : KExpr) : KExpr :=
  e.instantiateLevelParams (List.range ps.length) (ps.map .param)

/-- Inverse of `Level.subst ps (posLevels ps)` on universe levels. -/
def invPosLevel (ps : List LevelParam) (u : KLevel) : KLevel :=
  Level.subst (List.range ps.length) (ps.map .param) u

theorem invPosOf_posOf {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (e : KExpr) : invPosOf ps (posOf ps e) = e :=
  posOf_perm_inv hperm e

theorem posOf_inj {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {a b : KExpr} (h : posOf ps a = posOf ps b) : a = b := by
  rw [← invPosOf_posOf hperm a, ← invPosOf_posOf hperm b, h]

private theorem subst_go_getElem_eq :
    ∀ (ks : List LevelParam) (vs : List KLevel) (i : Nat) (hnd : ks.Nodup)
      (hlen : vs.length = ks.length) (hi : i < ks.length),
      Level.subst.go ks vs ks[i] = vs[i]'(by rw [hlen]; exact hi)
  | [], _, _, _, _, hi => nomatch hi
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | k :: ks, v :: vs, 0, _, _, _ => by
    show (if k = k then v else Level.subst.go ks vs k) = v
    exact ite_eq_left rfl
  | k :: ks, v :: vs, i + 1, hnd, hlen, hi => by
    obtain ⟨hk_not_mem, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hlen' : vs.length = ks.length := Nat.succ.inj hlen
    have hne : k ≠ ks[i] := by
      intro heq
      rw [heq] at hk_not_mem
      exact hk_not_mem (List.getElem_mem hi')
    show (if k = ks[i] then v else Level.subst.go ks vs ks[i]) = vs[i]'(by rw [hlen']; exact hi')
    rw [ite_eq_right hne]
    exact subst_go_getElem_eq ks vs i hnd' hlen' hi'

theorem subst_invPosLevel {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) :
    ∀ u : KLevel, Level.subst ps (posLevels ps) (invPosLevel ps u) = u
  | .zero => rfl
  | .succ u => congrArg Level.succ (subst_invPosLevel hperm u)
  | .max a b => by
    simp only [invPosLevel, Level.subst]
    exact congrArg₂ Level.max (subst_invPosLevel hperm a) (subst_invPosLevel hperm b)
  | .imax a b => by
    simp only [invPosLevel, Level.subst]
    exact congrArg₂ Level.imax (subst_invPosLevel hperm a) (subst_invPosLevel hperm b)
  | .param p => by
    have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
    show Level.subst ps (posLevels ps)
      (Level.subst.go (List.range ps.length) (ps.map .param) p) = .param p
    by_cases hp : p < ps.length
    · have hp_len : p < (ps.map Level.param).length := by rw [List.length_map]; exact hp
      have hget := InferAux.getElem?_eq_subst_go_range (us := ps.map Level.param) hp_len
      rw [List.length_map, List.getElem?_map, List.getElem?_eq_getElem hp] at hget
      have hgo : Level.subst.go (List.range ps.length) (ps.map .param) p = .param ps[p] :=
        (Option.some.inj hget).symm
      rw [hgo]
      show Level.subst.go ps (posLevels ps) ps[p] = .param p
      have hlen : (posLevels ps).length = ps.length := by simp [posLevels]
      rw [subst_go_getElem_eq ps (posLevels ps) p hnd hlen hp]
      simp [posLevels]
    · have hp_range : p ∉ List.range ps.length := by rw [List.mem_range]; exact hp
      have hp_ps : p ∉ ps := fun hm => hp_range (hperm.mem_iff.mp hm)
      rw [InferAux.subst_go_of_not_mem hp_range]
      exact InferAux.subst_go_of_not_mem hp_ps

private theorem substPW_invPos {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (pw : Ix.Kernel.PropWhen) :
    Level.substPW ps (posLevels ps)
      (Level.substPW (List.range ps.length) (ps.map .param) pw) = pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Level.holds_substPW, Level.holds_substPW]
  congr 1
  funext p
  rw [← Level.eval_subst_go, ← Level.eval_subst]
  exact congrArg (Level.eval φ) (subst_invPosLevel hperm (.param p))

theorem posOf_invPosOf {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) :
    ∀ e : KExpr, posOf ps (invPosOf ps e) = e := by
  intro e
  unfold posOf invPosOf
  induction e with
  | bvar _ | lit _ => rfl
  | fvar idx ty ih => simp only [Expr.instantiateLevelParams, ih]
  | sort u =>
    simp only [Expr.instantiateLevelParams]
    exact congrArg Expr.sort (subst_invPosLevel hperm u)
  | const n us =>
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    have hmap : us.map (Level.subst ps (posLevels ps) ∘
        Level.subst (List.range ps.length) (ps.map .param)) = us.map id :=
      List.map_congr_left fun u _ => subst_invPosLevel hperm u
    simpa using hmap
  | app f a ihf iha => simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_invPos hperm m.pw]
  | forallE ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_invPos hperm m.pw]
  | letE ty val body l iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.instantiateLevelParams, ih]

def posVal (ps : List LevelParam) (φ : LevelParam → Nat) : LevelParam → Nat :=
  Level.substFn φ (List.range ps.length) (ps.map .param)

theorem substFn_posVal {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (φ : LevelParam → Nat) :
    Level.substFn (posVal ps φ) ps (posLevels ps) = φ := by
  funext p
  have hinv : Level.subst (List.range ps.length) (ps.map .param)
      (Level.subst ps (posLevels ps) (.param p)) = .param p :=
    Expr.sort.inj (posOf_perm_inv hperm (.sort (.param p)))
  have hev := congrArg (Level.eval φ) hinv
  rw [Level.eval_subst, Level.eval_subst] at hev
  exact hev

theorem denoteMeta_posOf {V : Type u} [Ix.Kernel.SetTheory V]
    {env : Ix.Kernel.Env .anon} (m : EnvModel V env)
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (φ : LevelParam → Nat) (d : Nat) (e : KExpr) :
    Ix.Kernel.Model.denoteMeta m.acval env (posVal ps φ) d (posOf ps e) =
      Ix.Kernel.Model.denoteMeta m.acval env φ d e := by
  unfold posOf
  rw [Ix.Kernel.Model.denotePInstLevels, substFn_posVal hperm]

theorem fvarsBelow_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (d : Nat),
      Expr.fvarsBelow d (e.instantiateLevelParams ks us) ↔ Expr.fvarsBelow d e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ =>
    intro _; simp [Expr.instantiateLevelParams, Expr.fvarsBelow]
  | fvar _ _ _ =>
    intro _; simp [Expr.instantiateLevelParams, Expr.fvarsBelow]
  | app _ _ ihf iha =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, ihf d, iha d]
  | lam _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihb d]
  | forallE _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihb d]
  | letE _ _ _ _ iht ihv ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihv d, ihb d]
  | proj _ _ _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, ih d]

theorem wscoped_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (d : Nat),
      Expr.WScoped d (e.instantiateLevelParams ks us) ↔ Expr.WScoped d e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ =>
    intro _; simp [Expr.instantiateLevelParams, Expr.WScoped]
  | fvar idx _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ih idx]
  | app _ _ ihf iha =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ihf d, iha d]
  | lam _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihb d]
  | forallE _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihb d]
  | letE _ _ _ _ iht ihv ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihv d, ihb d]
  | proj _ _ _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ih d]

theorem fvarLeaves_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).fvarLeaves =
      e.fvarLeaves.map (fun l => (l.1, l.2.instantiateLevelParams ks us)) := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => simp [Expr.instantiateLevelParams, Expr.fvarLeaves]
  | fvar idx ty ih =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_cons, ih]
  | app _ _ ihf iha =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, ihf, iha]
  | lam _ _ _ iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihb]
  | forallE _ _ _ iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihb]
  | letE _ _ _ _ iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihv, ihb]
  | proj _ _ _ ih =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, ih]

theorem leavesBounded_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (e : KExpr) :
    Expr.LeavesBounded (e.instantiateLevelParams ks us) ↔ Expr.LeavesBounded e := by
  unfold Expr.LeavesBounded
  rw [fvarLeaves_instantiateLevelParams]
  constructor
  · intro h l hl
    have h' := h (l.1, l.2.instantiateLevelParams ks us) (List.mem_map_of_mem hl)
    rwa [Expr.looseBVarsBounded_instantiateLevelParams] at h'
  · intro h l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact h l hl

theorem ctxOk_posOf {V : Type u} [Ix.Kernel.SetTheory V]
    {env : Ix.Kernel.Env .anon} {m : EnvModel V env}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {φ : LevelParam → Nat} {d : Nat} {Δa : List Ix.Kernel.Semantics.AnnotTerm} {e : KExpr}
    (hctx : Ix.Kernel.Model.CtxOk m φ d Δa e) :
    Ix.Kernel.Model.CtxOk m (posVal ps φ) d Δa (posOf ps e) := by
  obtain ⟨hlen, hleaves⟩ := hctx
  refine ⟨hlen, fun l' hl' => ?_⟩
  unfold posOf at hl'
  rw [fvarLeaves_instantiateLevelParams] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  obtain ⟨hlt, hfb, tya, Aa, hden, hΔ, hint, hwd⟩ := hleaves l hl
  refine ⟨hlt, (fvarsBelow_instantiateLevelParams ps (posLevels ps) l.2 l.1).mpr hfb,
    tya, Aa, ?_, hΔ, hint, hwd⟩
  show Ix.Kernel.Model.denoteMeta m.acval env (posVal ps φ) d (posOf ps l.2) = some tya
  rw [denoteMeta_posOf m hperm φ d l.2]
  exact hden

end TwinPos

/-- Derivation judgement package allowing a permutation `ps.Perm (List.range ps.length)` into
positional level-parameter space (supporting both small and large twin recursors uniformly). -/
def twinPosRulesJ : Judgements .anon where
  annot _ d e e' := Annot d e e'
  infer env d e t :=
    ∃ ps, ps.Perm (List.range ps.length) ∧ Infer env .full d (posOf ps e) (posOf ps t)
  defeq env d a b :=
    ∃ ps, ps.Perm (List.range ps.length) ∧ DefEq env d (posOf ps a) (posOf ps b)
  sort env d t u :=
    ∃ ps, ps.Perm (List.range ps.length) ∧
      Red env d (posOf ps t) (.sort (Level.subst ps (posLevels ps) u))
  isZero u := ∀ φ : LevelParam → Nat, Level.eval φ u = 0
  thmValue _ v' := v'

theorem twinPosRulesJ_infer_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {e t_pos : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hinf : Infer env .full d (posOf ps e) t_pos) :
    twinPosRulesJ.infer env d e (TwinPos.invPosOf ps t_pos) :=
  ⟨ps, hperm, by rw [TwinPos.posOf_invPosOf hperm]; exact hinf⟩

theorem twinPosRulesJ_defeq_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {a b : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hde : DefEq env d (posOf ps a) (posOf ps b)) :
    twinPosRulesJ.defeq env d a b :=
  ⟨ps, hperm, hde⟩

theorem twinPosRulesJ_sort_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {t_pos : KExpr} {u_pos : KLevel}
    (hperm : ps.Perm (List.range ps.length))
    (hred : Red env d t_pos (.sort u_pos)) :
    twinPosRulesJ.sort env d (TwinPos.invPosOf ps t_pos) (TwinPos.invPosLevel ps u_pos) :=
  ⟨ps, hperm, by
    rw [TwinPos.posOf_invPosOf hperm, TwinPos.subst_invPosLevel hperm]
    exact hred⟩

private theorem posOf_nil_eq (e : KExpr) : posOf [] e = e :=
  posOf_range 0 e

/-- Every `rulesJ.infer` derivation lifts directly to `twinPosRulesJ.infer` (`ps := []`). -/
theorem rulesJ_infer_to_twinPos {env : Ix.Kernel.Env .anon} {d : Nat} {e t : KExpr}
    (h : (rulesJ (md := .anon)).infer env d e t) :
    twinPosRulesJ.infer env d e t :=
  ⟨[], .nil, by rw [posOf_nil_eq e, posOf_nil_eq t]; exact h⟩

/-- Every `rulesJ.defeq` derivation lifts directly to `twinPosRulesJ.defeq` (`ps := []`). -/
theorem rulesJ_defeq_to_twinPos {env : Ix.Kernel.Env .anon} {d : Nat} {a b : KExpr}
    (h : (rulesJ (md := .anon)).defeq env d a b) :
    twinPosRulesJ.defeq env d a b :=
  ⟨[], .nil, by rw [posOf_nil_eq a, posOf_nil_eq b]; exact h⟩

/-- Every `rulesJ.sort` derivation lifts directly to `twinPosRulesJ.sort` (`ps := []`). -/
theorem rulesJ_sort_to_twinPos {env : Ix.Kernel.Env .anon} {d : Nat} {t : KExpr} {u : KLevel}
    (h : (rulesJ (md := .anon)).sort env d t u) :
    twinPosRulesJ.sort env d t u := by
  refine ⟨[], .nil, ?_⟩
  have hu : Level.subst [] (posLevels []) u = u :=
    Expr.sort.inj (posOf_nil_eq (.sort u))
  rw [posOf_nil_eq t, hu]
  exact h

/-- Scoping frames for `twinPosRulesJ`. -/
theorem judgeFrames_twinPosRulesJ (env : Ix.Kernel.Env .anon) :
    JudgeFrames twinPosRulesJ env :=
  let h := Ix.Kernel.Model.judgeFrames_rulesJ env
  ⟨h.annot_syntax, h.annot_wscoped, h.annot_bounded, h.annot_leaves⟩

/-- **Model soundness of `twinPosRulesJ`**, derived from `judgeSound_rulesJ_of` via
`TwinPos.denoteMeta_posOf`. -/
theorem judgeSound_twinPosRulesJ_of {V : Type u} [Ix.Kernel.SetTheory V]
    {μ : Ix.Kernel.CheckMode} {env : Ix.Kernel.Env .anon}
    (mp : EnvModelM V μ env) : JudgeSound twinPosRulesJ mp.base2 where
  toJudgeFrames := judgeFrames_twinPosRulesJ env
  accepted := by
    intro φ d e t ⟨ps, hperm, hpos⟩ hws hb hL
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    obtain ⟨ea, hea⟩ := hR.accepted (TwinPos.posVal ps φ) hpos hws' hb' hL'
    rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d e] at hea
    exact ⟨ea, hea⟩
  infer := by
    intro φ d e t Δa ⟨ps, hperm, hpos⟩ hws hb hL ea ta hctx hea hta
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    have hta' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps t)
        = some ta := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d t]; exact hta
    exact hR.infer (TwinPos.posVal ps φ) hpos hws' hb' hL' (TwinPos.ctxOk_posOf hperm hctx)
      hea' hta'
  defeq := by
    intro φ d a b Δa ⟨ps, hperm, hpos⟩ hwsa hba hLa hwsb hbb hLb aa ba hctxa hctxb haa hba_d
      hwda hwdb
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hwsa' : Expr.WScoped d (posOf ps a) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) a d).mpr hwsa
    have hba' : (posOf ps a).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hba
    have hLa' : Expr.LeavesBounded (posOf ps a) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) a).mpr hLa
    have hwsb' : Expr.WScoped d (posOf ps b) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) b d).mpr hwsb
    have hbb' : (posOf ps b).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbb
    have hLb' : Expr.LeavesBounded (posOf ps b) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) b).mpr hLb
    have haa' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps a)
        = some aa := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d a]; exact haa
    have hba_d' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps b)
        = some ba := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d b]; exact hba_d
    exact hR.defeq (TwinPos.posVal ps φ) hpos hwsa' hba' hLa' hwsb' hbb' hLb'
      (TwinPos.ctxOk_posOf hperm hctxa) (TwinPos.ctxOk_posOf hperm hctxb) haa' hba_d' hwda hwdb
  reads := by
    intro φ d e t Δa ea ⟨ps, hperm, hpos⟩ hws hb hL hctx hea
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    obtain ⟨ta, hta'⟩ := hR.reads (TwinPos.posVal ps φ) hpos hws' hb' hL'
      (TwinPos.ctxOk_posOf hperm hctx) hea'
    rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d t] at hta'
    exact ⟨ta, hta'⟩
  frame := by
    intro φ d e t Δa ea ⟨ps, hperm, hpos⟩ hws hb hL hctx hea
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (TwinPos.leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (TwinPos.posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [TwinPos.denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    obtain ⟨hwst', hbt', hsub'⟩ :=
      hR.frame (TwinPos.posVal ps φ) hpos hws' hb' hL' (TwinPos.ctxOk_posOf hperm hctx) hea'
    refine ⟨(TwinPos.wscoped_instantiateLevelParams ps (posLevels ps) t d).mp hwst', ?_, ?_⟩
    · unfold posOf at hbt'
      rwa [Expr.looseBVarsBounded_instantiateLevelParams] at hbt'
    · intro l hl
      have hl_pos : (l.1, posOf ps l.2) ∈ (posOf ps t).fvarLeaves := by
        unfold posOf
        rw [TwinPos.fvarLeaves_instantiateLevelParams]
        exact List.mem_map_of_mem hl
      have hm_pos := hsub' _ hl_pos
      unfold posOf at hm_pos
      rw [TwinPos.fvarLeaves_instantiateLevelParams] at hm_pos
      obtain ⟨m, hm, heq⟩ := List.mem_map.mp hm_pos
      obtain ⟨hm1, hm2⟩ := Prod.mk.inj heq
      have hm2' : m.2 = l.2 := TwinPos.posOf_inj hperm hm2
      have hml : m = l := Prod.ext hm1 hm2'
      rw [← hml]
      exact hm

/-- Lift `ConstantValCheckJ rulesJ` to `ConstantValCheckJ twinPosRulesJ`. -/
theorem ConstantValCheckJ.to_twinPos {env : Ix.Kernel.Env .anon} {cv cv' : KConstantVal}
    (h : ConstantValCheckJ rulesJ env cv cv') :
    ConstantValCheckJ twinPosRulesJ env cv cv' := by
  obtain ⟨ty', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, sty, u, hinf, hred⟩, heq⟩ := h
  exact ⟨ty', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
    sty, u, rulesJ_infer_to_twinPos hinf, rulesJ_sort_to_twinPos hred⟩, heq⟩

/-- Lift `TwinRuleJ rulesJ` to `TwinRuleJ twinPosRulesJ`. -/
theorem TwinRuleJ.to_twinPos {env envSelf : Ix.Kernel.Env .anon} {f : KKey → KKey}
    {recName : KKey} {lps : List LevelParam} {cvW' : KConstantVal} {mI rP : Nat}
    {rW rW' rC : RecRule .anon}
    (h : TwinRuleJ rulesJ env envSelf f recName lps cvW' mI rP rW rW' rC) :
    TwinRuleJ twinPosRulesJ env envSelf f recName lps cvW' mI rP rW rW' rC := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    rhsG, hw1, hw2, hgen⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    rhsG, hw1, hw2, ?_⟩
  rcases hgen with rfl | ⟨g1, g2, g3, g4, rty, hinf⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨g1, g2, g3, g4, rty, rulesJ_infer_to_twinPos hinf⟩

private theorem forall₂_imp {α β : Type} {R S : α → β → Prop}
    (himp : ∀ {a b}, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → List.Forall₂ S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hh htl => .cons (himp hh) (forall₂_imp himp htl)

private theorem semForall₂_imp {α β : Type} {R S : α → β → Prop}
    (himp : ∀ {a b}, R a b → S a b) :
    ∀ {xs : List α} {ys : List β},
      Ix.Kernel.Semantics.Forall₂ R xs ys → Ix.Kernel.Semantics.Forall₂ S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hh htl => .cons (himp hh) (semForall₂_imp himp htl)

/-- Lift `DeclRecTwinRunJ rulesJ` to `DeclRecTwinRunJ twinPosRulesJ`. -/
theorem DeclRecTwinRunJ.to_twinPos {env env₂ : Ix.Kernel.Env .anon}
    {block : List KConstantInfo}
    (h : DeclRecTwinRunJ rulesJ env block env₂) :
    DeclRecTwinRunJ twinPosRulesJ env block env₂ := by
  obtain ⟨ws, f, hne, hblk, rfl, hnd, hfr, hf, hall⟩ := h
  refine ⟨ws, f, hne, hblk, rfl, hnd, hfr, hf, fun w hw => ?_⟩
  obtain ⟨hcv, hlf, hfkC, hlps, hmod, ⟨tyG, htw1, htw2, htgen⟩, hlenW, hrules⟩ := hall w hw
  refine ⟨ConstantValCheckJ.to_twinPos hcv, hlf, hfkC, hlps, hmod, ⟨tyG, htw1, htw2, ?_⟩,
    hlenW, semForall₂_imp (fun hh => TwinRuleJ.to_twinPos hh) hrules⟩
  rcases htgen with rfl | ⟨t1, t2, t3, t4, sty, hinf⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨t1, t2, t3, t4, sty, rulesJ_infer_to_twinPos hinf⟩

/-- Staging `twinModels ws` extends `env` (`EnvExt`). -/
theorem envExt_twinModels {env : Ix.Kernel.Env .anon} {ws : List (TwinRecPart .anon)}
    (hndM : ((twinModels ws).map (·.name)).Nodup)
    (hfrM : ∀ ci ∈ twinModels ws, env.find? ci.name = none) :
    EnvExt env ⟨twinModels ws ++ env.consts⟩ := by
  refine Ix.Kernel.Semantics.envExt_append_shape hndM hfrM ?_
  intro c hc
  obtain ⟨w, _, _, hname⟩ := twinModels_names_sub ws c hc
  rw [hname]
  rfl

private theorem newSat_twinModels {env : Ix.Kernel.Env .anon} {ws : List (TwinRecPart .anon)}
    {Q : KConstantInfo → Prop}
    (hQd : ∀ cv v hint, Q (.defnInfo cv v hint)) :
    NewSat env ⟨twinModels ws ++ env.consts⟩ Q := by
  intro n x hf
  rcases Ix.Kernel.Semantics.find?_append_inv hf with hold | ⟨hmem, -⟩
  · exact .inl hold
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmem
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hw
    exact .inr (hQd _ _ _)

/-- Staging `twinModels ws` preserves `DeclStoreInv`. -/
theorem DeclStoreInv.step_twinModels {env : Ix.Kernel.Env .anon} {ws : List (TwinRecPart .anon)}
    (h : DeclStoreInv env)
    (hndM : ((twinModels ws).map (·.name)).Nodup)
    (hfrM : ∀ ci ∈ twinModels ws, env.find? ci.name = none)
    (hmod : ∀ w ∈ ws, ∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint)) :
    DeclStoreInv ⟨twinModels ws ++ env.consts⟩ := by
  have hext : EnvExt env ⟨twinModels ws ++ env.consts⟩ := envExt_twinModels hndM hfrM
  refine
    { store := (Ix.Kernel.Model.storeInv_twinModels h.store ws hndM hfrM hmod).1
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (newSat_twinModels fun _ _ _ _ _ heq => nomatch heq)
      recK := Ix.Kernel.Model.recK_step_noRec h.store h.recK hext.find
        (newSat_twinModels fun _ _ _ _ _ _ _ heq => nomatch heq)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (newSat_twinModels fun _ _ _ _ _ heq => nomatch heq)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (newSat_twinModels fun _ _ _ _ heq => nomatch heq)
      recShape := Ix.Kernel.Model.recShape_step_noRec h.store h.recShape hext.find
        (newSat_twinModels fun _ _ _ _ _ _ _ heq => nomatch heq) }

/-- Provisioning rule-less `twinProv ws` over `envM` extends `envM` (`EnvExt`). -/
theorem envExt_twinProv {J : Judgements .anon} {env envM : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hndP : ((twinProv ws).map (·.name)).Nodup)
    (hfrP : ∀ ci ∈ twinProv ws, envM.find? ci.name = none)
    (hcv : ∀ w ∈ ws, ConstantValCheckJ J env w.cvW w.cvW') :
    EnvExt envM ⟨twinProv ws ++ envM.consts⟩ := by
  refine Ix.Kernel.Semantics.envExt_append_shape hndP hfrP ?_
  intro c hc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  have hcW := hcv w hw
  show w.cvW'.name.isProjFnShape = false
  rw [hcW.name_eq]
  exact hcW.shape

private theorem newSat_twinProv {envM : Ix.Kernel.Env .anon} {ws : List (TwinRecPart .anon)}
    {Q : KConstantInfo → Prop}
    (hQr : ∀ cv mI rP, Q (.recInfo cv mI rP [])) :
    NewSat envM ⟨twinProv ws ++ envM.consts⟩ Q := by
  intro n x hf
  rcases Ix.Kernel.Semantics.find?_append_inv hf with hold | ⟨hmem, -⟩
  · exact .inl hold
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hmem
    exact .inr (hQr _ _ _)

/-- Provisioning rule-less `twinProv ws` over `envM` preserves `DeclStoreInv` (enabling `Core`
calls against `envSelf = ⟨twinProv ws ++ envM.consts⟩` during twin rule checking). -/
theorem DeclStoreInv.step_twinProv {J : Judgements .anon} {env envM : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hfrJ : JudgeFrames J env)
    (hM : DeclStoreInv envM)
    (hfindM : ∀ k ci, env.find? k = some ci → envM.find? k = some ci)
    (hndP : ((twinProv ws).map (·.name)).Nodup)
    (hfrP : ∀ ci ∈ twinProv ws, envM.find? ci.name = none)
    (hcv : ∀ w ∈ ws, ConstantValCheckJ J env w.cvW w.cvW') :
    DeclStoreInv ⟨twinProv ws ++ envM.consts⟩ := by
  have hext : EnvExt envM ⟨twinProv ws ++ envM.consts⟩ := envExt_twinProv hndP hfrP hcv
  have hnewNil : NewSat envM ⟨twinProv ws ++ envM.consts⟩
      (fun x => ∃ cv a b, x = .recInfo cv a b []) :=
    newSat_twinProv fun cv a b => ⟨cv, a, b, rfl⟩
  refine
    { store := (Ix.Kernel.Model.storeInv_twinProv hfrJ hM.store hfindM ws hndP hfrP hcv).1
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext hM.thmTyped
        (newSat_twinProv fun _ _ _ _ _ heq => nomatch heq)
      recK := Ix.Kernel.Model.recK_step hM.store hM.recK hext.find (by
        intro n cv mI rP rules hf hn0
        rcases hnewNil n _ hf with hold | ⟨cv', a', b', heq⟩
        · rw [hold] at hn0; exact nomatch hn0
        · obtain ⟨_, _, _, hrls⟩ := ConstantInfo.recInfo.inj heq
          subst hrls
          exact ⟨(fun _ hr => nomatch hr), (fun _ _ hr _ => nomatch hr)⟩)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext hM.etaTowers
        (newSat_twinProv fun _ _ _ _ _ heq => nomatch heq)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find hM.tableBodies
        (newSat_twinProv fun _ _ _ _ heq => nomatch heq)
      recShape := Ix.Kernel.Model.recShape_step hM.store hM.recShape hext.find (by
        intro n cv mI rP rules hf hn0
        rcases hnewNil n _ hf with hold | ⟨cv', a', b', heq⟩
        · rw [hold] at hn0; exact nomatch hn0
        · obtain ⟨_, _, _, hrls⟩ := ConstantInfo.recInfo.inj heq
          subst hrls
          exact ⟨(fun _ hr => nomatch hr), (fun _ _ hr _ => nomatch hr),
            (fun _ _ hr => nomatch hr), (fun _ _ heq' _ => nomatch heq')⟩) }

/-- Combined staging `DeclStoreInv` for `envSelf = ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩`
directly from the header hypotheses of `DeclRecTwinRunJ`. -/
theorem DeclStoreInv.step_twinSelf {J : Judgements .anon} {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hfrJ : JudgeFrames J env)
    (h : DeclStoreInv env)
    (hnd : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup)
    (hfrAll : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none)
    (hmod : ∀ w ∈ ws, ∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint))
    (hcv : ∀ w ∈ ws, ConstantValCheckJ J env w.cvW w.cvW') :
    DeclStoreInv ⟨twinModels ws ++ env.consts⟩ ∧
      DeclStoreInv ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ := by
  have hnamesEq : (twinProv ws).map (·.name) = (twinRecs ws).map (·.name) := by
    simp only [twinProv, twinRecs, List.map_map]; rfl
  rw [List.map_append] at hnd
  obtain ⟨hndR, hndM, hdisj⟩ := List.nodup_append.mp hnd
  have hfrM : ∀ ci ∈ twinModels ws, env.find? ci.name = none :=
    fun ci hci => hfrAll ci (List.mem_append_right _ hci)
  have hSM : DeclStoreInv ⟨twinModels ws ++ env.consts⟩ :=
    h.step_twinModels hndM hfrM hmod
  have hextM : EnvExt env ⟨twinModels ws ++ env.consts⟩ := envExt_twinModels hndM hfrM
  have hndP : ((twinProv ws).map (·.name)).Nodup := by rwa [hnamesEq]
  have hfrProvM : ∀ ci ∈ twinProv ws,
      (⟨twinModels ws ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = none := by
    intro ci hci
    have hmemN : ci.name ∈ (twinRecs ws).map (·.name) := by
      rw [← hnamesEq]; exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨cR, hcR, hnR⟩ := List.mem_map.mp hmemN
    have hnotM : ci.name ∉ (twinModels ws).map (·.name) :=
      fun hm => hdisj ci.name hmemN ci.name hm rfl
    refine Ix.Kernel.Semantics.find?_append_none_of_not_mem hnotM ?_
    rw [← hnR]
    exact hfrAll cR (List.mem_append_left _ hcR)
  exact ⟨hSM, hSM.step_twinProv hfrJ (fun _ _ hf => hextM.find hf) hndP hfrProvM hcv⟩

/-- **`InstallStep` for a twin recursor block**: `new := twinRecs ws ++ twinModels ws` installs
every member of `block` via `StoredAs` (`twinRecs ws`), while every copied model companion in
`twinModels ws` has derived key `.aux w.cvW.name .model`. -/
theorem installStep_of_twinParts {J : Judgements .anon} {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)} {block : List KConstantInfo} (nP : Nat)
    (hne : ws ≠ [])
    (hblk : block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW))
    (hnd : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup)
    (hfr : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none)
    (hcv : ∀ w ∈ ws, ConstantValCheckJ J env w.cvW w.cvW')
    (hstored : ∀ w ∈ ws,
      IxVM.Consistency.ValStored w.cvW' w.cvW ∧
      List.Forall₂ IxVM.Consistency.RuleStored w.rulesW' w.rulesW) :
    IxVM.Consistency.InstallStep env (.indDecl block nP)
      ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ := by
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block :=
    installs_twinBlock_eq nP hne hblk
  refine ⟨twinRecs ws ++ twinModels ws, ?_, hnd, hfr, ?_, ?_⟩
  · simp [List.append_assoc]
  · rw [hinst]
    intro ci₀ hci₀
    rw [hblk] at hci₀
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci₀
    obtain ⟨hvs, hrs⟩ := hstored w hw
    refine ⟨.recInfo w.cvW' w.mI w.rP w.rulesW',
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩), ?_⟩
    exact ⟨hvs, rfl, rfl, hrs⟩
  · rw [hinst]
    intro ci hci
    rcases List.mem_append.mp hci with hrec | hmod
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
      refine Or.inl ⟨.recInfo w.cvW w.mI w.rP w.rulesW, ?_, ?_⟩
      · rw [hblk]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
      · show w.cvW.name = w.cvW'.name
        exact (hcv w hw).name_eq.symm
    · obtain ⟨w, _, _, hname⟩ := twinModels_names_sub ws ci hmod
      exact Or.inr ⟨w.cvW.name, .model, hname⟩

/-- Full `DeclStoreInv` preservation across `DeclRecTwinRunJ J` for any judgement package `J`
satisfying `JudgeFrames`. -/
theorem DeclStoreInv.step_twinJ {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e)
    {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (h : DeclStoreInv env)
    (hrun : DeclRecTwinRunJ J env block env₂) :
    DeclStoreInv env₂ := by
  have hext : EnvExt env env₂ := Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun
  refine
    { store := Ix.Kernel.Model.storeInv_declRecTwinRunJ hfr h.store hrun
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (Ix.Kernel.Model.twin_newSat
          (fun _ _ _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ _ heq => nomatch heq) hrun)
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find
        (Ix.Kernel.Model.twin_recK_new h.store h.recK hrun)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (Ix.Kernel.Model.twin_newSat
          (fun _ _ _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ _ heq => nomatch heq) hrun)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (Ix.Kernel.Model.twin_newSat
          (fun _ _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq) hrun)
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find
        (Ix.Kernel.Model.twin_recShape_new h.store h.recShape hrun) }

/-- Specialization of `DeclStoreInv.step_twinJ` to `twinPosRulesJ`. -/
theorem DeclStoreInv.step_twin_pos {env env₂ : Ix.Kernel.Env .anon}
    {block : List KConstantInfo}
    (h : DeclStoreInv env)
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂) :
    DeclStoreInv env₂ :=
  h.step_twinJ judgeFrames_twinPosRulesJ hrun

/-- Specialization of `DeclStoreInv.step_twinJ` to `rulesJ`. -/
theorem DeclStoreInv.step_twin_rulesJ {env env₂ : Ix.Kernel.Env .anon}
    {block : List KConstantInfo}
    (h : DeclStoreInv env)
    (hrun : DeclRecTwinRunJ rulesJ env block env₂) :
    DeclStoreInv env₂ :=
  h.step_twinJ (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e) hrun

/-- `EnvModelT` preservation across `DeclRecTwinRunJ J` for any sound judgement package `J`. -/
theorem envModelT_step_twinJ {V : Type u} [Ix.Kernel.SetTheory V]
    {μ : Ix.Kernel.CheckMode} {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e)
    (hsnd : ∀ {e : Ix.Kernel.Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (hrun : DeclRecTwinRunJ J env block env₂)
    (hm : EnvModelT V μ env) :
    EnvModelT V μ env₂ := by
  obtain ⟨⟨mp, hT⟩, hE⟩ := hm
  have hE₂ : Ix.Kernel.EtaFamiliesClosed env₂ :=
    Ix.Kernel.Semantics.declRecTwinRunJ_etaClosed hE hrun
  obtain ⟨mp₂, hext⟩ := Ix.Kernel.Model.declRecTwinJ hfr (fun m => hsnd m) mp hrun
  exact ⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩

/-- `EnvModelT` preservation across `DeclRecTwinRunJ twinPosRulesJ`. -/
theorem envModelT_step_twin_pos {V : Type u} [Ix.Kernel.SetTheory V]
    {μ : Ix.Kernel.CheckMode} {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂)
    (hm : EnvModelT V μ env) :
    EnvModelT V μ env₂ :=
  envModelT_step_twinJ judgeFrames_twinPosRulesJ (fun m => judgeSound_twinPosRulesJ_of m) hrun hm

/-- `EnvModelT` preservation across `DeclRecTwinRunJ rulesJ`. -/
theorem envModelT_step_twin_rulesJ {V : Type u} [Ix.Kernel.SetTheory V]
    {μ : Ix.Kernel.CheckMode} {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (hrun : DeclRecTwinRunJ rulesJ env block env₂)
    (hm : EnvModelT V μ env) :
    EnvModelT V μ env₂ :=
  envModelT_step_twinJ (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
    (fun m => Ix.Kernel.Model.judgeSound_rulesJ_of m) hrun hm

/-- **Full `DeclInv` preservation** across `DeclRecTwinRunJ twinPosRulesJ`. -/
theorem DeclInv.step_twin_pos {V : Type u} [Ix.Kernel.SetTheory V]
    {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂)
    (h : DeclInv V env) :
    DeclInv V env₂ :=
  ⟨envModelT_step_twin_pos hrun h.model, h.store.step_twin_pos hrun⟩

/-- **Full `DeclInv` preservation** across `DeclRecTwinRunJ rulesJ`. -/
theorem DeclInv.step_twin_rulesJ {V : Type u} [Ix.Kernel.SetTheory V]
    {env env₂ : Ix.Kernel.Env .anon} {block : List KConstantInfo}
    (hrun : DeclRecTwinRunJ rulesJ env block env₂)
    (h : DeclInv V env) :
    DeclInv V env₂ :=
  ⟨envModelT_step_twin_rulesJ hrun h.model, h.store.step_twin_rulesJ hrun⟩

/-- **`EnvFacts` preservation** (`storeClosed`, `recRules`, `recPlain`, `recArity`,
`ruleCtorArity`, `etaTowers`, `recEta`, `tableCtorArity`, `familyArity`) across any
`DeclRecTwinRunJ J` step when combined with `CtxRoleFacts` at `env₂`. -/
theorem twinRec_envFacts_preserved {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e)
    {E : Ixon.Env} {env env₂ : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {block : List KConstantInfo}
    (hS : DeclStoreInv env)
    (hrun : DeclRecTwinRunJ J env block env₂)
    (htwf : t.wf = true)
    (hR₂ : CtxRoleFacts ⟨E, env₂, t, lim⟩) :
    EnvFacts ⟨E, env₂, t, lim⟩ :=
  (hS.step_twinJ hfr hrun).toEnvFacts htwf hR₂

/-! ## Section 4: Circuit extraction (`check_const` on `Rec` and `check_muts_all`) -/

/-- Exact inversion of `CIRepExact` on a `"Rec"` constructor value. -/
theorem cirepExact_rec_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k_flag rec_uns rec_block rec_idx : SourceValue F}
    {ci : KConstantInfo}
    (hci : CIRepExact κ h
      (.construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx]) ci) :
    ∃ (cv : KConstantVal) (mI rP : Nat) (rls : List (RecRule .anon)) (p i m mi : F),
      ci = .recInfo cv mI rP rls ∧
      ValRepExact κ h nl ty cv ∧
      np = .field p ∧ ni = .field i ∧ nm = .field m ∧ nmi = .field mi ∧
      (rP : F) = p + m + mi ∧ (mI : F) = p + m + mi + i ∧
      rP ≤ mI ∧ mI < 288230376151711744 ∧
      RulesRepExact κ h cv.levelParams 0 rules rls ∧
      (k_flag = .field 1 → ∃ rl, rls = [rl] ∧ rl.k = true ∧ rl.ctorParams = ZMod.val p) ∧
      (∃ (b : Bytes.Address) (idx_f : F),
        Bytes.RepAddressRef addrTy h b rec_block ∧ rec_idx = .field idx_f ∧
        (cv.name = κ (ixAddr b) ∨ cv.name = κ (rprjAddr (ixAddr b) (ZMod.val idx_f)))) := by
  generalize hv_eq :
    (Value.construct kciEnum "Rec"
      [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx] : SourceValue F) = v at hci
  cases hci with
  | axio _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | opaq _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | defn _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | thm _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | quot _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | induct _ _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | ctor _ _ _ _ _ => injection hv_eq with _ htag _; exact absurd htag (by decide)
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    injection hv_eq with _ _ hargs
    injection hargs with h1 hargs
    injection hargs with h2 hargs
    injection hargs with h3 hargs
    injection hargs with h4 hargs
    injection hargs with h5 hargs
    injection hargs with h6 hargs
    injection hargs with h7 hargs
    injection hargs with h8 hargs
    injection hargs with _ hargs
    injection hargs with h10 hargs
    injection hargs with h11 _
    rw [← h1, ← h2] at hv
    rw [← h3] at hnp
    rw [← h4] at hni
    rw [← h5] at hnm
    rw [← h6] at hnmi
    rw [← h7] at hrules
    rw [← h8] at hk
    rw [← h10, ← h11] at hkey
    exact ⟨_, _, _, _, _, _, _, _, rfl, hv, hnp, hni, hnm, hnmi, hrP, hmI,
      hcounts.1, hcounts.2, hrules, hk, hkey⟩

/-- `KernelCheck::is_unsafe_ci` on a `"Rec"` constant returns its `rec_uns` field without modifying
the heap or making calls. -/
theorem is_unsafe_ci_rec {nl ty np ni nm nmi rules k_flag rec_uns rec_block rec_idx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_unsafe_ci"
      [.construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx]] h r h' cs) :
    r = rec_uns ∧ h' = h ∧ cs = [] := by
  cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
  | Axiom _ _ _ hv _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Defn_Safe _ _ _ _ _ hv _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Defn_other _ _ _ _ _ _ hv _ _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Thm _ _ _ _ _ hv _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Opaque _ _ _ _ _ _ _ hv _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Quot _ _ _ _ _ _ _ hv _ _ _ => injection hv with _ htag _; exact absurd htag (by decide)
  | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv hr hh hc =>
    injection hv with _ _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with huns _
    rw [← huns] at hr
    exact ⟨hr, hh, hc⟩

/-- Branching dispatch of `KernelCheck::check_const` on a `"Rec"` constant after its common
well-scopedness and sort checks. -/
inductive TwinCheckRoute (c : Ctx) (rc v ap nm k_flag rec_uns rec_block : SourceValue F)
    (h : Heap F) (r : SourceValue F) (h' : Heap F) : Prop where
  | native (v_fam : SourceValue F) (h_fam h_fam' h_mid : Heap F)
      (cs_fam cs_mod cs_sub : List (Call F)) :
      nm = .field 1 →
      Heap.Extends h h_fam →
      Heap.Extends h_fam h_fam' →
      Heap.Extends h_fam' h_mid →
      ObsFn W "KernelModeled::rec_family_block" [ap] h_fam v_fam h_fam' cs_fam →
      ObsFn W "KernelModeled::block_is_modeled" [v_fam] h_fam' (.field 0) h_mid cs_mod →
      ObsFn W "KernelCheck::check_recursor_member" [rc, v, ap] h_mid r h' cs_sub →
      Good c cs_fam →
      Good c cs_mod →
      Good c cs_sub →
      TwinCheckRoute c rc v ap nm k_flag rec_uns rec_block h r h'
  | modeled (v_fam v_mod : SourceValue F) (h_fam h_fam' h_mid : Heap F)
      (cs_fam cs_mod cs_sub : List (Call F)) :
      k_flag = .field 0 →
      rec_uns = .field 0 →
      v_mod ≠ .field 0 →
      Heap.Extends h h_fam →
      Heap.Extends h_fam h_fam' →
      Heap.Extends h_fam' h_mid →
      ObsFn W "KernelModeled::rec_family_block" [ap] h_fam v_fam h_fam' cs_fam →
      ObsFn W "KernelModeled::block_is_modeled" [v_fam] h_fam' v_mod h_mid cs_mod →
      ObsFn W "KernelModeled::check_family" [rc, v_fam, rec_block] h_mid r h' cs_sub →
      Good c cs_fam →
      Good c cs_mod →
      Good c cs_sub →
      TwinCheckRoute c rc v ap nm k_flag rec_uns rec_block h r h'

theorem TwinCheckRoute.heap_extends {c : Ctx}
    {rc v ap nm k_flag rec_uns rec_block : SourceValue F} {h : Heap F} {r : SourceValue F}
    {h' : Heap F}
    (hr : TwinCheckRoute c rc v ap nm k_flag rec_uns rec_block h r h') :
    Heap.Extends h h' := by
  cases hr with
  | native _ _ _ _ _ _ _ _ e1 e2 e3 _ _ ev_sub _ _ _ =>
    exact e1.trans (e2.trans (e3.trans (ObsFn.heap_extends ev_sub)))
  | modeled _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 _ _ ev_sub _ _ _ =>
    exact e1.trans (e2.trans (e3.trans (ObsFn.heap_extends ev_sub)))

/-- Raw path inversion of `KernelCheck::check_const` on a `"Rec"` constant. -/
theorem check_const_rec_paths {c : Ctx}
    {rc nl ty np ni nm nmi rules k_flag rec_uns rec_block rec_idx ap r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hgood : Good c calls)
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx], ap]
      h r h' calls) :
    ∃ (v_sc v_sort : SourceValue F) (m_sc m_nil m_sort : Heap F)
      (cs_sc cs_sort : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v_sc m_sc cs_sc ∧
      m_nil = m_sc ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m_sc.length] m_nil v_sort m_sort cs_sort ∧
      Good c cs_sc ∧
      Good c cs_sort ∧
      TwinCheckRoute c rc
        (.construct kciEnum "Rec"
          [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx])
        ap nm k_flag rec_uns rec_block h r h' := by
  cases Obs.«KernelCheck::check_const».obs ev with
  | Rec_n0 v1 m2 cs12 x_nlvls x_ty w2576 w2577 x_n_mot w2578 w2579 x_k_flag x_rec_uns
      x_rec_block w2580 v2636 m2637 cs2647 v2673 m2674 cs2684 m2705 v2717 m2718 cs2728
      v_rules m_rules cs_rules
      v2747 m2748 cs2758 v2769 m2770 cs2780 m2792 cs2803 cs2848
      ev14 _ _ _ _ _ _ _ hv2574 ev2649 hm2713 ev2686 ev2730 ev_rules ev2760 ev2782 ev2805
      heq2844 ev2850 hc2875 =>
    obtain ⟨_, hm2, _⟩ := is_unsafe_ci_rec ev14
    rw [hm2] at ev2649
    injection hv2574 with _ _ hargs
    injection hargs with hnl hargs
    injection hargs with hty hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hnm hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hk hargs
    injection hargs with huns hargs
    injection hargs with hblk _
    rw [← hnl, ← hty] at ev2649
    rw [← hty] at ev2686
    rw [← hnm] at heq2844
    rw [← hblk] at ev2760
    have e_sc := ObsFn.heap_extends ev2649
    have e_nil : Heap.Extends m2637 m2705 := by
      rw [hm2713]; exact heap_extends_append m2637 _
    have e_sort := ObsFn.heap_extends ev2686
    have e_safe := ObsFn.heap_extends ev2730
    have e_rules := ObsFn.heap_extends ev_rules
    have e_kinds := ObsFn.heap_extends ev2760
    have e_to_fam : Heap.Extends h m2748 :=
      e_sc.trans (e_nil.trans (e_sort.trans (e_safe.trans (e_rules.trans e_kinds))))
    have hg_sc : Good c cs2647 := hgood.sub (by rw [hc2875]; intro x hx; simp [hx])
    have hg_sort : Good c cs2684 := hgood.sub (by rw [hc2875]; intro x hx; simp [hx])
    have hg_fam : Good c cs2780 := hgood.sub (by rw [hc2875]; intro x hx; simp [hx])
    have hg_mod : Good c cs2803 := hgood.sub (by rw [hc2875]; intro x hx; simp [hx])
    have hg_sub : Good c cs2848 := hgood.sub (by rw [hc2875]; intro x hx; simp [hx])
    exact ⟨v2636, v2673, m2637, m2705, m2674, cs2647, cs2684,
      ev2649, hm2713, ev2686, hg_sc, hg_sort,
      .native v2769 m2748 m2770 m2792 cs2780 cs2803 cs2848 heq2844
        e_to_fam (ObsFn.heap_extends ev2782) (ObsFn.heap_extends ev2805)
        ev2782 ev2805 ev2850 hg_fam hg_mod hg_sub⟩
  | Rec_other v1 m2 cs12 x_nlvls x_ty w2576 w2577 x_n_mot w2578 w2579 x_k_flag x_rec_uns
      x_rec_block w2580 v2636 m2637 cs2647 v2673 m2674 cs2684 m2705 v2717 m2718 cs2728
      v_rules m_rules cs_rules
      v2747 m2748 cs2758 v2769 m2770 cs2780 v2791 m2792 cs2803 cs2937
      ev14 _ _ _ _ _ _ _ hv2574 ev2649 hm2713 ev2686 ev2730 ev_rules ev2760 ev2782 ev2805
      hne2876 heq2906 heq2933 ev2939 hc2964 =>
    obtain ⟨_, hm2, _⟩ := is_unsafe_ci_rec ev14
    rw [hm2] at ev2649
    injection hv2574 with _ _ hargs
    injection hargs with hnl hargs
    injection hargs with hty hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hnm hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hk hargs
    injection hargs with huns hargs
    injection hargs with hblk _
    rw [← hnl, ← hty] at ev2649
    rw [← hty] at ev2686
    rw [← hk] at heq2906
    rw [← huns] at heq2933
    rw [← hblk] at ev2760 ev2939
    have e_sc := ObsFn.heap_extends ev2649
    have e_nil : Heap.Extends m2637 m2705 := by
      rw [hm2713]; exact heap_extends_append m2637 _
    have e_sort := ObsFn.heap_extends ev2686
    have e_safe := ObsFn.heap_extends ev2730
    have e_rules := ObsFn.heap_extends ev_rules
    have e_kinds := ObsFn.heap_extends ev2760
    have e_to_fam : Heap.Extends h m2748 :=
      e_sc.trans (e_nil.trans (e_sort.trans (e_safe.trans (e_rules.trans e_kinds))))
    have hg_sc : Good c cs2647 := hgood.sub (by rw [hc2964]; intro x hx; simp [hx])
    have hg_sort : Good c cs2684 := hgood.sub (by rw [hc2964]; intro x hx; simp [hx])
    have hg_fam : Good c cs2780 := hgood.sub (by rw [hc2964]; intro x hx; simp [hx])
    have hg_mod : Good c cs2803 := hgood.sub (by rw [hc2964]; intro x hx; simp [hx])
    have hg_sub : Good c cs2937 := hgood.sub (by rw [hc2964]; intro x hx; simp [hx])
    exact ⟨v2636, v2673, m2637, m2705, m2674, cs2647, cs2684,
      ev2649, hm2713, ev2686, hg_sc, hg_sort,
      .modeled v2769 v2791 m2748 m2770 m2792 cs2780 cs2803 cs2937 heq2906 heq2933 hne2876
        e_to_fam (ObsFn.heap_extends ev2782) (ObsFn.heap_extends ev2805)
        ev2782 ev2805 ev2939 hg_fam hg_mod hg_sub⟩
  | _ =>
    exfalso
    simp_all [kciEnum]

/-- Assemble `ConstantValCheckJ twinPosRulesJ` unconditionally from `ValStored`, `ValRepExact`,
`validate_expr_well_scoped`, and `k_ensure_sort` (supporting any `Perm` of `List.range`, including
`large = true` recursors). -/
theorem constantValCheckJ_twinPos_of_checked (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {cv cv' : KConstantVal} {nl ty rc v_sc v_sort : SourceValue F}
    {h m_sc m_nil m_sort : Heap F} {cs_sc cs_sort : List (Call F)}
    (hvs : IxVM.Consistency.ValStored cv' cv)
    (hv : ValRepExact c.κ h nl ty cv')
    (hlbd : cv.type.looseBVarsBounded 0 = true)
    (hfv : cv.type.hasFvar = false)
    (hfresh : c.env.find? cv.name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (hrc : RCRep c.t c.lim h rc) (hef : EnvFacts c) (hlf : LoadFacts c)
    (hg_sort : Good c cs_sort)
    (ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v_sc m_sc cs_sc)
    (hm_nil : m_nil = m_sc ++ [.construct kexprListEnum "Nil" []])
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort"
      [rc, ty, .ptr (.enum kexprListEnum) m_sc.length] m_nil v_sort m_sort cs_sort) :
    ConstantValCheckJ twinPosRulesJ c.env cv cv' := by
  obtain ⟨hnl_eq, hnl, hperm, hty_rep⟩ := hv
  have hnd_cv : LevelParam.nodup cv.levelParams = true := by
    rw [← hvs.2.1]
    exact nat_levelParam_nodup_of_nodup (hperm.nodup_iff.mpr List.nodup_range)
  have ev_sc' : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, .field (cv'.levelParams.length : F)] h v_sc m_sc cs_sc := by
    rwa [← hnl_eq]
  let Γ₀ : Nat → KExpr := fun _ => .sort .zero
  have hlpd_pos := validate_expr_well_scoped_spec hnl (hty_rep 0 Γ₀) ev_sc'
  have hlpd' := allLevelParamsDefined_of_posOf_perm hperm hlpd_pos
  rw [hvs.2.1] at hlpd'
  have e_sc := ObsFn.heap_extends ev_sc
  have e_nil : Heap.Extends h m_nil := by
    rw [hm_nil]; exact e_sc.trans (heap_extends_append m_sc _)
  have htypes : TypesRep c.κ Γ₀ m_nil 0 (.ptr (.enum kexprListEnum) m_sc.length) := by
    rw [hm_nil]; exact typesRep_alloc_nil c.κ Γ₀ m_sc
  obtain ⟨sty_pos, u_pos, _, hinf_pos, hred_pos, _, _⟩ :=
    core_ensure_sort hCore (hrc.mono e_nil) htypes (ghostScoped_zero Γ₀) hef hlf hg_sort
      ev_sort ((hty_rep 0 Γ₀).mono e_nil).toTm
  have hpos_nfv : (posOf cv'.levelParams cv'.type).hasFvar = false :=
    Tm.hasFvar_false (hty_rep 0 Γ₀).toTm
  have hcr_pos := infer_constsResolve hinf_pos hef.store hpos_nfv
  rw [constsResolve_posOf] at hcr_pos
  have hperm_cv : cv.levelParams.Perm (List.range cv.levelParams.length) := by
    rw [← hvs.2.1]; exact hperm
  have hinf_cv : Infer c.env .full 0 (posOf cv.levelParams cv'.type) sty_pos := by
    rw [← hvs.2.1]; exact hinf_pos
  have hcv_eq : cv' = { cv with type := cv'.type } := by
    cases cv; cases cv'
    cases hvs.1; cases hvs.2.1
    rfl
  exact ⟨cv'.type, ⟨Option.isNone_iff_eq_none.mpr hfresh, hbasis, hshape, hnd_cv,
    hlbd, hfv, annot_of_annotates hvs.2.2 hfv hlbd 0, hlpd', hcr_pos,
    TwinPos.invPosOf cv.levelParams sty_pos, TwinPos.invPosLevel cv.levelParams u_pos,
    twinPosRulesJ_infer_of_pos hperm_cv hinf_cv,
    twinPosRulesJ_sort_of_pos hperm_cv hred_pos⟩, hcv_eq⟩

/-- **Full circuit extraction for `KernelCheck::check_const` on a `"Rec"` constant**: proves
`ConstantValCheckJ twinPosRulesJ` unconditionally, `ConstantValCheckJ rulesJ` under `PosSortLift`,
`letFree` on the checked recursor type and all checked rule right-hand sides, `RuleStored`
correspondence, and `TwinCheckRoute` (`.native` or `.modeled`). -/
theorem check_const_rec_inv (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {rc nl ty np ni nm nmi rules k_flag rec_uns rec_block rec_idx ap r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    {cvW cvW' : KConstantVal} {mI rP : Nat} {rulesW rulesW' : List (RecRule .anon)}
    (hS : DeclStoreInv c.env)
    (htwf : c.t.wf = true)
    (hR : CtxRoleFacts c)
    (hlf : LoadFacts c)
    (hrc : RCRep c.t c.lim h rc)
    (hgood : Good c calls)
    (hci : CIRepExact c.κ h
      (.construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx])
      (.recInfo cvW' mI rP rulesW'))
    (hstored : IxVM.Consistency.StoredAs
      (.recInfo cvW' mI rP rulesW') (.recInfo cvW mI rP rulesW))
    (hlbd : cvW.type.looseBVarsBounded 0 = true)
    (hfv : cvW.type.hasFvar = false)
    (hfresh : c.env.find? cvW.name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains cvW.name = false)
    (hshape : cvW.name.isProjFnShape = false)
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx], ap]
      h r h' calls) :
    ConstantValCheckJ twinPosRulesJ c.env cvW cvW' ∧
      (PosSortLift c.env cvW' → ConstantValCheckJ rulesJ c.env cvW cvW') ∧
      letFree cvW'.type = true ∧
      (∀ rl ∈ rulesW', letFree rl.rhs = true) ∧
      rulesW.length = rulesW'.length ∧
      List.Forall₂ IxVM.Consistency.RuleStored rulesW' rulesW ∧
      TwinCheckRoute c rc
        (.construct kciEnum "Rec"
          [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx])
        ap nm k_flag rec_uns rec_block h r h' := by
  obtain ⟨cv0, mI0, rP0, rls0, _, _, _, _, heq_ci, hval0, _, _, _, _, _, _, _, _, hrules0, _, _⟩ :=
    cirepExact_rec_inv hci
  injection heq_ci with hcv_eq hmI_eq hrP_eq hrls_eq
  subst hcv_eq hmI_eq hrP_eq hrls_eq
  obtain ⟨hvs, _, _, hrs_stored⟩ := hstored
  have hef : EnvFacts c := hS.toEnvFacts htwf hR
  obtain ⟨v_sc, v_sort, m_sc, m_nil, m_sort, cs_sc, cs_sort,
    ev_sc, hm_nil, ev_sort, _, hg_sort, hroute⟩ := check_const_rec_paths hgood ev
  have hcv_pos : ConstantValCheckJ twinPosRulesJ c.env cvW cvW' :=
    constantValCheckJ_twinPos_of_checked hCore hvs hval0 hlbd hfv hfresh hbasis hshape
      hrc hef hlf hg_sort ev_sc hm_nil ev_sort
  have hcv_rules : PosSortLift c.env cvW' → ConstantValCheckJ rulesJ c.env cvW cvW' := by
    intro hlift
    let Γ₀ : Nat → KExpr := fun _ => .sort .zero
    have e_nil : Heap.Extends h m_nil := by
      rw [hm_nil]; exact (ObsFn.heap_extends ev_sc).trans (heap_extends_append m_sc _)
    have htypes : TypesRep c.κ Γ₀ m_nil 0 (.ptr (.enum kexprListEnum) m_sc.length) := by
      rw [hm_nil]; exact typesRep_alloc_nil c.κ Γ₀ m_sc
    exact (constantValCheckJ_of_checked hCore hvs hval0 hlbd hfv hfresh hbasis hshape
      hS.store hlift ev_sc e_nil (hrc.mono e_nil) htypes hef hlf hg_sort ev_sort).1
  have hlf_ty : letFree cvW'.type = true := hval0.letFree_type
  have hlf_rls : ∀ rl ∈ rulesW', letFree rl.rhs = true :=
    hrules0.letFree_rhs hval0.2.2.1
  have hlen_eq : rulesW.length = rulesW'.length := hrs_stored.length_eq.symm
  exact ⟨hcv_pos, hcv_rules, hlf_ty, hlf_rls, hlen_eq, hrs_stored, hroute⟩

/-- Inversion of `KernelClaim::check_muts_member_at`: computes the member's projection address via
`Ingress::projection_addr`, loads its `KConstantInfo` via `Ingress::get_ci` + `loadValue`, and
runs `KernelCheck::check_const`. -/
theorem check_muts_member_at_inv (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {pos : Nat} {rc bp lp m_val r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hpos : pos < ms.length) (hlen : ms.length < 2 ^ 39)
    (hgood : Good c calls)
    (hms : Specs.Callees.MembersRep h ms lp)
    (hb : RepAddr h b bp)
    (ev : ObsFn W "KernelClaim::check_muts_member_at"
      [rc, bp, lp, m_val, .field (pos : F)] h r h' calls) :
    ∃ (a : Bytes.Address) (ap ci_ptr ci_val : SourceValue F) (m_pa m_ci : Heap F)
      (cs_ci cs_chk : List (Call F)),
      Heap.Extends h m_pa ∧
      Heap.Extends m_pa m_ci ∧
      RepAddr m_pa a ap ∧
      ixAddr a = projAddr (Specs.Callees.memberProjInfo (ixAddr b) pos ms[pos]) ∧
      ObsFn W "Ingress::get_ci" [ap] m_pa ci_ptr m_ci cs_ci ∧
      loadValue m_ci ci_ptr = .ok ci_val ∧
      ObsFn W "KernelCheck::check_const" [rc, ci_val, ap] m_ci r h' cs_chk ∧
      (⟨"KernelCheck::check_const", [rc, ci_val, ap], m_ci⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) ∧
      Good c cs_ci ∧
      Good c cs_chk := by
  cases Obs.«KernelClaim::check_muts_member_at».obs ev with
  | run v1 m2 cs12 v39 m40 p47 cs53 cs67 ev14 ev55 ld49 ev69 hc94 =>
    have hg12 : Good c cs12 := hgood.sub (by rw [hc94]; intro x hx; simp [hx])
    have hg53 : Good c cs53 := hgood.sub (by rw [hc94]; intro x hx; simp [hx])
    have hg67 : Good c cs67 := hgood.sub (by rw [hc94]; intro x hx; simp [hx])
    obtain ⟨a, ha, ha_addr⟩ := ProjAddrAux.projection_addr_spec c hpos hlen hg12 hms hb ev14
    refine ⟨a, v1, p47, v39, m2, m40, cs53, cs67,
      ObsFn.heap_extends ev14, ObsFn.heap_extends ev55,
      ha, ha_addr, ev55, ld49, ev69,
      by rw [hc94]; simp,
      fun cl hcl => by rw [hc94]; simp [hcl],
      hg53, hg67⟩

/-- Inversion of `KernelClaim::check_muts_all` over a suffix `cur = ms.drop pos`: extracts the
per-member projection address and `KernelCheck::check_const` derivation for every `j < cur.length`. -/
theorem check_muts_all_inv (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {rc bp lp : SourceValue F} (hlen : ms.length < 2 ^ 39) :
    ∀ (cur : List Ixon.MutConst) {pos : Nat} {cur_p r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      ms.drop pos = cur →
      Good c calls →
      Specs.Callees.MembersRep h ms lp →
      RepAddr h b bp →
      Specs.Callees.MembersRep h cur cur_p →
      ObsFn W "KernelClaim::check_muts_all"
        [rc, bp, lp, cur_p, .field (pos : F)] h r h' calls →
      ∀ (j : Nat) (hj : j < cur.length),
        ∃ (a : Bytes.Address) (ap ci_ptr ci_val r_j : SourceValue F)
          (m_pa m_ci m_end : Heap F) (cs_ci cs_chk : List (Call F)),
          Heap.Extends h m_pa ∧
          Heap.Extends m_pa m_ci ∧
          RepAddr m_pa a ap ∧
          ixAddr a = projAddr (Specs.Callees.memberProjInfo (ixAddr b) (pos + j) cur[j]) ∧
          ObsFn W "Ingress::get_ci" [ap] m_pa ci_ptr m_ci cs_ci ∧
          loadValue m_ci ci_ptr = .ok ci_val ∧
          ObsFn W "KernelCheck::check_const" [rc, ci_val, ap] m_ci r_j m_end cs_chk ∧
          (⟨"KernelCheck::check_const", [rc, ci_val, ap], m_ci⟩ : Call F) ∈ calls ∧
          (∀ cl ∈ cs_chk, cl ∈ calls) ∧
          Good c cs_ci ∧
          Good c cs_chk := by
  intro cur
  induction cur with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ j hj
    exact nomatch hj
  | cons m rest ih =>
    intro pos cur_p r h h' calls hdrop hgood hms hb hcur ev j hj
    cases Obs.«KernelClaim::check_muts_all».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hcur ld12
    | Cons x_m x_rest v42 m43 cs53 cs99 v106 ld12 ev55 op148 ev101 hc150 =>
      obtain ⟨z, zs, he, _, hrest_rep⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with he1 he2
      subst he1 he2
      obtain ⟨hpos, hmi, hdrop'⟩ := ProjAddrAux.drop_succ_of_drop_cons ms pos hdrop
      have hg53 : Good c cs53 := hgood.sub (by rw [hc150]; intro x hx; simp [hx])
      have hg99 : Good c cs99 := hgood.sub (by rw [hc150]; intro x hx; simp [hx])
      cases j with
      | zero =>
        obtain ⟨a, ap, ci_ptr, ci_val, m_pa, m_ci, cs_ci, cs_chk,
          e1, e2, ha, ha_addr, ev_ci, ld_ci, ev_chk, hmem_chk, hsub_chk, hg_ci, hg_chk⟩ :=
          check_muts_member_at_inv c hpos hlen hg53 hms hb ev55
        rw [hmi] at ha_addr
        refine ⟨a, ap, ci_ptr, ci_val, v42, m_pa, m_ci, m43, cs_ci, cs_chk,
          e1, e2, ha, ?_, ev_ci, ld_ci, ev_chk,
          by rw [hc150]; simp [hmem_chk],
          fun cl hcl => by rw [hc150]; simp [hsub_chk cl hcl],
          hg_ci, hg_chk⟩
        simpa using ha_addr
      | succ k =>
        have ext55 := ObsFn.heap_extends ev55
        have hms' : Specs.Callees.MembersRep m43 ms lp :=
          RepLinkedList.mono (fun _ _ _ _ _ hx => hx) ext55 hms
        have hb' : RepAddr m43 b bp := Bytes.repAddressRef_heapMono₂ addrTy ext55 hb
        have hrest_rep' : Specs.Callees.MembersRep m43 rest x_rest :=
          RepLinkedList.mono (fun _ _ _ _ _ hx => hx) ext55 hrest_rep
        rw [evalBinOp_add_one pos op148] at ev101
        have hk : k < rest.length := Nat.lt_of_succ_lt_succ hj
        obtain ⟨a, ap, ci_ptr, ci_val, r_k, m_pa, m_ci, m_end, cs_ci, cs_chk,
          e1, e2, ha, ha_addr, ev_ci, ld_ci, ev_chk, hmem_chk, hsub_chk, hg_ci, hg_chk⟩ :=
          ih hdrop' hg99 hms' hb' hrest_rep' ev101 k hk
        refine ⟨a, ap, ci_ptr, ci_val, r_k, m_pa, m_ci, m_end, cs_ci, cs_chk,
          ext55.trans e1, e2, ha, ?_, ev_ci, ld_ci, ev_chk,
          by rw [hc150]; simp [hmem_chk],
          fun cl hcl => by rw [hc150]; simp [hsub_chk cl hcl],
          hg_ci, hg_chk⟩
        rw [show pos + (k + 1) = pos + 1 + k by omega]
        exact ha_addr

/-- Specialization of `check_muts_all_inv` at `pos = 0` for `.muts` blocks of `.recr` members:
member `j` projects to `rprjAddr (ixAddr b) j` and has an observed `KernelCheck::check_const`
derivation recorded in `calls`. -/
theorem check_muts_all_recr_inv (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {rc bp lp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hlen : ms.length < 2 ^ 39)
    (hgood : Good c calls)
    (hms : Specs.Callees.MembersRep h ms lp)
    (hb : RepAddr h b bp)
    (ev : ObsFn W "KernelClaim::check_muts_all" [rc, bp, lp, lp, .field 0] h r h' calls)
    {j : Nat} (hj : j < ms.length) {rd : Ixon.Recursor} (hm : ms[j] = .recr rd) :
    ∃ (a : Bytes.Address) (ap ci_ptr ci_val r_j : SourceValue F)
      (m_pa m_ci m_end : Heap F) (cs_ci cs_chk : List (Call F)),
      Heap.Extends h m_pa ∧
      Heap.Extends m_pa m_ci ∧
      RepAddr m_pa a ap ∧
      ixAddr a = rprjAddr (ixAddr b) j ∧
      ObsFn W "Ingress::get_ci" [ap] m_pa ci_ptr m_ci cs_ci ∧
      loadValue m_ci ci_ptr = .ok ci_val ∧
      ObsFn W "KernelCheck::check_const" [rc, ci_val, ap] m_ci r_j m_end cs_chk ∧
      (⟨"KernelCheck::check_const", [rc, ci_val, ap], m_ci⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) ∧
      Good c cs_ci ∧
      Good c cs_chk := by
  have ev' : ObsFn W "KernelClaim::check_muts_all"
      [rc, bp, lp, lp, .field ((0 : Nat) : F)] h r h' calls := by
    simpa using ev
  obtain ⟨a, ap, ci_ptr, ci_val, r_j, m_pa, m_ci, m_end, cs_ci, cs_chk,
    e1, e2, ha, ha_addr, ev_ci, ld_ci, ev_chk, hmem_chk, hsub_chk, hg_ci, hg_chk⟩ :=
    check_muts_all_inv c hlen ms (pos := 0) (by simp) hgood hms hb hms ev' j hj
  rw [Nat.zero_add, hm] at ha_addr
  exact ⟨a, ap, ci_ptr, ci_val, r_j, m_pa, m_ci, m_end, cs_ci, cs_chk,
    e1, e2, ha, ha_addr, ev_ci, ld_ci, ev_chk, hmem_chk, hsub_chk, hg_ci, hg_chk⟩

/-! ## Section 5: Parametric native/modeled interfaces and end-to-end twin refinement -/

/-- Semantic and rule-metadata correspondence for one checked twin recursor rule `rW'` against its
canonical recursor rule `rC` (the obligations not already discharged by `RuleStored` and
`RulesRepExact.letFree_rhs`). -/
structure TwinRuleCheckedOut (J : Judgements .anon) (env envSelf : Ix.Kernel.Env .anon)
    (f : KKey → KKey) (w : TwinRecPart .anon) (rW' rC : RecRule .anon) : Prop where
  rhs_lvls : rW'.rhs.allLevelParamsDefined w.cvC.levelParams = true
  rhs_res : rW'.rhs.constsResolve envSelf = true
  ctor_eq : rW'.ctor = rC.ctor
  nfields_eq : rW'.nfields = rC.nfields
  ctorParams_eq : rW'.ctorParams = rC.ctorParams
  fire_eq : rW'.fire = rC.fire
  k_eq : rW'.k = rC.k
  paramsBlind_eq : rW'.paramsBlind = rC.paramsBlind
  eta_eq : rW'.eta = Ix.Kernel.recRuleEtaOf env.find? w.cvW.name rC.ctor
  plain_shape :
    rW'.fire = .plain → ∀ cvj cnP cnF,
      env.find? rW'.ctor = some (.ctorInfo cvj cnP cnF) →
      Expr.recRulePlain w.cvW'.type w.mI w.rP rW'.ctorParams cvj.levelParams = true
  nested_shape :
    ∀ lvls pins, rW'.fire = .nested lvls pins →
      ∃ pre dom body bm D,
        w.cvW'.type.stripPis w.mI = some (pre, .forallE dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs =
          pins.map (Expr.liftLooseBVars (w.mI - w.rP) 0) ++
            (List.range (w.mI - w.rP)).map (fun i => Expr.bvar (w.mI - w.rP - 1 - i))
  rhs_gen :
    ∃ rhsG : KExpr,
      WrapRel env.find? rhsG rC.rhs ∧
      WrapRel env.find? (rhsG.renameConsts f) rW'.rhs ∧
      (rhsG = rC.rhs ∨
        (rhsG.hasFvar = false ∧ rhsG.allLevelParamsDefined w.cvC.levelParams = true ∧
          rhsG.constsResolve env = true ∧ rhsG.looseBVarsBounded 0 = true ∧
          ∃ rty, J.infer env 0 rhsG rty))

theorem TwinRuleCheckedOut.to_twinPos {env envSelf : Ix.Kernel.Env .anon} {f : KKey → KKey}
    {w : TwinRecPart .anon} {rW' rC : RecRule .anon}
    (h : TwinRuleCheckedOut rulesJ env envSelf f w rW' rC) :
    TwinRuleCheckedOut twinPosRulesJ env envSelf f w rW' rC where
  rhs_lvls := h.rhs_lvls
  rhs_res := h.rhs_res
  ctor_eq := h.ctor_eq
  nfields_eq := h.nfields_eq
  ctorParams_eq := h.ctorParams_eq
  fire_eq := h.fire_eq
  k_eq := h.k_eq
  paramsBlind_eq := h.paramsBlind_eq
  eta_eq := h.eta_eq
  plain_shape := h.plain_shape
  nested_shape := h.nested_shape
  rhs_gen := by
    obtain ⟨rhsG, hw1, hw2, hgen⟩ := h.rhs_gen
    refine ⟨rhsG, hw1, hw2, ?_⟩
    rcases hgen with rfl | ⟨g1, g2, g3, g4, rty, hinf⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨g1, g2, g3, g4, rty, rulesJ_infer_to_twinPos hinf⟩

/-- Assemble `TwinRuleJ` from `RuleStored`, raw closedness, `letFree`, and `TwinRuleCheckedOut`. -/
theorem twinRuleJ_of_checkedOut {J : Judgements .anon} {env envSelf : Ix.Kernel.Env .anon}
    {f : KKey → KKey} {w : TwinRecPart .anon} {rW rW' rC : RecRule .anon}
    (hann_bridge : ∀ d e e', Annot d e e' → J.annot envSelf d e e')
    (hst : IxVM.Consistency.RuleStored rW' rW)
    (hbvs : rW.rhs.looseBVarsBounded 0 = true)
    (hnfv : rW.rhs.hasFvar = false)
    (hlf : letFree rW'.rhs = true)
    (hout : TwinRuleCheckedOut J env envSelf f w rW' rC) :
    TwinRuleJ J env envSelf f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP rW rW' rC :=
  ⟨hst.1.symm, hst.2.1.symm, hbvs, hnfv,
    hann_bridge 0 rW.rhs rW'.rhs (annot_of_annotates hst.2.2 hnfv hbvs 0),
    hout.rhs_lvls, hout.rhs_res, hlf,
    hout.ctor_eq, hout.nfields_eq, hout.ctorParams_eq, hout.fire_eq,
    hout.k_eq, hout.paramsBlind_eq, hout.eta_eq,
    hout.plain_shape, hout.nested_shape, hout.rhs_gen⟩

private theorem forall₂_zip_twinRuleJ {J : Judgements .anon} {env envSelf : Ix.Kernel.Env .anon}
    {f : KKey → KKey} {w : TwinRecPart .anon}
    (hann_bridge : ∀ d e e', Annot d e e' → J.annot envSelf d e e') :
    ∀ {rulesW rulesW' rulesC : List (RecRule .anon)},
      List.Forall₂ IxVM.Consistency.RuleStored rulesW' rulesW →
      (∀ rW ∈ rulesW, rW.rhs.looseBVarsBounded 0 = true ∧ rW.rhs.hasFvar = false) →
      (∀ rW' ∈ rulesW', letFree rW'.rhs = true) →
      List.Forall₂ (TwinRuleCheckedOut J env envSelf f w) rulesW' rulesC →
      Ix.Kernel.Semantics.Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
        TwinRuleJ J env envSelf f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC)
        (rulesW.zip rulesW') rulesC
  | [], [], [], .nil, _, _, .nil => .nil
  | rW :: rsW, rW' :: rsW', rC :: rsC, .cons hst hsts, hraw, hlf, .cons hout houts => by
    obtain ⟨hbvs, hnfv⟩ := hraw rW List.mem_cons_self
    exact .cons
      (twinRuleJ_of_checkedOut hann_bridge hst hbvs hnfv (hlf rW' List.mem_cons_self) hout)
      (forall₂_zip_twinRuleJ hann_bridge hsts
        (fun x hx => hraw x (List.mem_cons_of_mem _ hx))
        (fun x hx => hlf x (List.mem_cons_of_mem _ hx))
        houts)

/-- Output of `KernelCheck::check_recursor_member` on a native/basis twin recursor `w`: confirms
`w.model? = none`, major-premise domain head/args agreement with `w.cvC.type`, a common generated
type `tyG` under `WrapRel`, and per-rule `TwinRuleCheckedOut` against `w.rulesC`. -/
structure NativeTwinMemberOut (J : Judgements .anon) (env envSelf : Ix.Kernel.Env .anon)
    (f : KKey → KKey) (w : TwinRecPart .anon) : Prop where
  model_none : w.model? = none
  major_agree :
    ∀ bsW domW bodyW bmW,
      w.cvW'.type.stripPis w.mI = some (bsW, .forallE domW bodyW bmW) →
      ∃ bsC domC bodyC bmC,
        w.cvC.type.stripPis w.mI = some (bsC, .forallE domC bodyC bmC) ∧
        domW.getAppFn = domC.getAppFn ∧
        domW.getAppArgs = domC.getAppArgs
  ty_gen :
    ∃ tyG : KExpr,
      WrapRel env.find? tyG w.cvC.type ∧
      WrapRel env.find? tyG w.cvW'.type ∧
      (tyG = w.cvC.type ∨
        (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
          tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
          ∃ sty, J.infer env 0 tyG sty))
  rules_out : List.Forall₂ (TwinRuleCheckedOut J env envSelf f w) w.rulesW' w.rulesC

theorem NativeTwinMemberOut.to_twinPos {env envSelf : Ix.Kernel.Env .anon} {f : KKey → KKey}
    {w : TwinRecPart .anon}
    (h : NativeTwinMemberOut rulesJ env envSelf f w) :
    NativeTwinMemberOut twinPosRulesJ env envSelf f w where
  model_none := h.model_none
  major_agree := h.major_agree
  ty_gen := by
    obtain ⟨tyG, hw1, hw2, hgen⟩ := h.ty_gen
    refine ⟨tyG, hw1, hw2, ?_⟩
    rcases hgen with rfl | ⟨t1, t2, t3, t4, sty, hinf⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t1, t2, t3, t4, sty, rulesJ_infer_to_twinPos hinf⟩
  rules_out := forall₂_imp (fun hh => hh.to_twinPos) h.rules_out

/-- Output of `KernelModeled::check_family` on a modeled twin recursor `w`: confirms
`w.model?.isSome = true` (matching `env.find? (auxKey w.kC .model)` via `lookupModelInfo?`), a
common generated type `tyG` under `WrapRel`, and per-rule `TwinRuleCheckedOut` against `w.rulesC`
under peer renaming `f`. -/
structure ModeledTwinMemberOut (J : Judgements .anon) (env envSelf : Ix.Kernel.Env .anon)
    (f : KKey → KKey) (w : TwinRecPart .anon) : Prop where
  model_some : w.model?.isSome = true
  ty_gen :
    ∃ tyG : KExpr,
      WrapRel env.find? tyG w.cvC.type ∧
      WrapRel env.find? tyG w.cvW'.type ∧
      (tyG = w.cvC.type ∨
        (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
          tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
          ∃ sty, J.infer env 0 tyG sty))
  rules_out : List.Forall₂ (TwinRuleCheckedOut J env envSelf f w) w.rulesW' w.rulesC

theorem ModeledTwinMemberOut.to_twinPos {env envSelf : Ix.Kernel.Env .anon} {f : KKey → KKey}
    {w : TwinRecPart .anon}
    (h : ModeledTwinMemberOut rulesJ env envSelf f w) :
    ModeledTwinMemberOut twinPosRulesJ env envSelf f w where
  model_some := h.model_some
  ty_gen := by
    obtain ⟨tyG, hw1, hw2, hgen⟩ := h.ty_gen
    refine ⟨tyG, hw1, hw2, ?_⟩
    rcases hgen with rfl | ⟨t1, t2, t3, t4, sty, hinf⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t1, t2, t3, t4, sty, rulesJ_infer_to_twinPos hinf⟩
  rules_out := forall₂_imp (fun hh => hh.to_twinPos) h.rules_out

/-- **Parametric native twin interface**: refines an observed `KernelCheck::check_recursor_member`
sub-derivation (after `block_is_modeled` returned `0` and `n_mot = 1`) into
`NativeTwinMemberOut J env envSelf (twinPeerRename ws) w`, given `DeclStoreInv` on both `env` and
`envSelf` and `ConstantValCheckJ J env w.cvW w.cvW'`. -/
def NativeTwinInputs (J : Judgements .anon) (env : Ix.Kernel.Env .anon)
    (ws : List (TwinRecPart .anon)) : Prop :=
  let envM : Ix.Kernel.Env .anon := ⟨twinModels ws ++ env.consts⟩
  let envSelf : Ix.Kernel.Env .anon := ⟨twinProv ws ++ envM.consts⟩
  ∀ (w : TwinRecPart .anon) (c : Ctx) (a : _root_.Address)
    (rc v ap nm k_flag rec_uns rec_block v_fam r : SourceValue F)
    (h h_fam h_fam' h_mid h' : Heap F) (cs_fam cs_mod cs_sub : List (Call F)),
    w ∈ ws →
    c.env = env →
    c.t.wf = true →
    DeclStoreInv env →
    DeclStoreInv envSelf →
    EnvFacts c →
    LoadFacts c →
    ConstantValCheckJ J env w.cvW w.cvW' →
    letFree w.cvW'.type = true →
    (∀ rl ∈ w.rulesW', letFree rl.rhs = true) →
    env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) →
    w.cvW.levelParams = w.cvC.levelParams →
    w.model? = lookupModelInfo? env w.kC →
    nm = .field 1 →
    RCRep c.t c.lim h_mid rc →
    S0.addr h_mid ap a →
    c.κ a = w.cvW.name →
    CIRepExact c.κ h_mid v (.recInfo w.cvW' w.mI w.rP w.rulesW') →
    Heap.Extends h h_fam →
    Heap.Extends h_fam h_fam' →
    Heap.Extends h_fam' h_mid →
    ObsFn W "KernelModeled::rec_family_block" [ap] h_fam v_fam h_fam' cs_fam →
    ObsFn W "KernelModeled::block_is_modeled" [v_fam] h_fam' (.field 0) h_mid cs_mod →
    ObsFn W "KernelCheck::check_recursor_member" [rc, v, ap] h_mid r h' cs_sub →
    Good c cs_fam →
    Good c cs_mod →
    Good c cs_sub →
    NativeTwinMemberOut J env envSelf (twinPeerRename ws) w

/-- Lift `NativeTwinInputs rulesJ` to `NativeTwinInputs twinPosRulesJ` whenever `PosSortLift`
holds on native members (or directly when `ConstantValCheckJ rulesJ` is supplied). -/
theorem NativeTwinInputs.to_twinPos_of_lift {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hlift : ∀ w ∈ ws, w.model? = none →
      ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW' →
      ConstantValCheckJ rulesJ env w.cvW w.cvW')
    (hN : NativeTwinInputs rulesJ env ws)
    (hmod_none : ∀ (c : Ctx) (v_fam : SourceValue F) (h_fam' h_mid : Heap F)
      (cs_mod : List (Call F)) (w : TwinRecPart .anon),
      w ∈ ws → c.env = env →
      ObsFn W "KernelModeled::block_is_modeled" [v_fam] h_fam' (.field 0) h_mid cs_mod →
      Good c cs_mod → w.model? = none) :
    NativeTwinInputs twinPosRulesJ env ws := by
  intro w c a rc v ap nm k_flag rec_uns rec_block v_fam r h h_fam h_fam' h_mid h'
    cs_fam cs_mod cs_sub hw hcenv htwf hS hS_self hef hlf hcv_pos hlf_ty hlf_rls hfkC hlps
    hmod_eq hnm hrc hadr hkey hci e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub
  have hm0 : w.model? = none := hmod_none c v_fam h_fam' h_mid cs_mod w hw hcenv ev_mod hg_mod
  have hcv_r : ConstantValCheckJ rulesJ env w.cvW w.cvW' := hlift w hw hm0 hcv_pos
  exact (hN w c a rc v ap nm k_flag rec_uns rec_block v_fam r h h_fam h_fam' h_mid h'
    cs_fam cs_mod cs_sub hw hcenv htwf hS hS_self hef hlf hcv_r hlf_ty hlf_rls hfkC hlps
    hmod_eq hnm hrc hadr hkey hci e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub).to_twinPos

/-- **Parametric modeled twin interface**: refines an observed `KernelModeled::check_family`
sub-derivation (after `block_is_modeled` returned non-zero, `k_flag = 0`, and `rec_uns = 0`) into
`ModeledTwinMemberOut J env envSelf (twinPeerRename ws) w`, given `DeclStoreInv` on both `env` and
`envSelf` and `ConstantValCheckJ J env w.cvW w.cvW'`. -/
def ModeledTwinInputs (J : Judgements .anon) (env : Ix.Kernel.Env .anon)
    (ws : List (TwinRecPart .anon)) : Prop :=
  let envM : Ix.Kernel.Env .anon := ⟨twinModels ws ++ env.consts⟩
  let envSelf : Ix.Kernel.Env .anon := ⟨twinProv ws ++ envM.consts⟩
  ∀ (w : TwinRecPart .anon) (c : Ctx) (a : _root_.Address)
    (rc v ap nm k_flag rec_uns rec_block v_fam v_mod r : SourceValue F)
    (h h_fam h_fam' h_mid h' : Heap F) (cs_fam cs_mod cs_sub : List (Call F)),
    w ∈ ws →
    c.env = env →
    c.t.wf = true →
    DeclStoreInv env →
    DeclStoreInv envSelf →
    EnvFacts c →
    LoadFacts c →
    ConstantValCheckJ J env w.cvW w.cvW' →
    letFree w.cvW'.type = true →
    (∀ rl ∈ w.rulesW', letFree rl.rhs = true) →
    env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) →
    w.cvW.levelParams = w.cvC.levelParams →
    w.model? = lookupModelInfo? env w.kC →
    k_flag = .field 0 →
    rec_uns = .field 0 →
    v_mod ≠ .field 0 →
    RCRep c.t c.lim h_mid rc →
    S0.addr h_mid ap a →
    c.κ a = w.cvW.name →
    CIRepExact c.κ h_mid v (.recInfo w.cvW' w.mI w.rP w.rulesW') →
    Heap.Extends h h_fam →
    Heap.Extends h_fam h_fam' →
    Heap.Extends h_fam' h_mid →
    ObsFn W "KernelModeled::rec_family_block" [ap] h_fam v_fam h_fam' cs_fam →
    ObsFn W "KernelModeled::block_is_modeled" [v_fam] h_fam' v_mod h_mid cs_mod →
    ObsFn W "KernelModeled::check_family" [rc, v_fam, rec_block] h_mid r h' cs_sub →
    Good c cs_fam →
    Good c cs_mod →
    Good c cs_sub →
    ModeledTwinMemberOut J env envSelf (twinPeerRename ws) w

/-- Per-member witness connecting a declared twin recursor `(d.cvW, d.mI, d.rP, d.rulesW)` to its
already-installed canonical recursor `d.kC` in `env` and its `KernelCheck::check_const` derivation
in `calls`. -/
structure TwinMemberWitness (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable)
    (calls : List (Call F)) (d : TwinMemberData) : Prop where
  canon_stored : env.find? d.kC = some (.recInfo d.cvC d.mI d.rP d.rulesC)
  lps_eq : d.cvW.levelParams = d.cvC.levelParams
  fresh_rec : env.find? d.cvW.name = none
  fresh_model :
    (lookupModelInfo? env d.kC).isSome = true →
      env.find? (Ix.Kernel.auxKey d.cvW.name .model) = none
  not_basis : Ix.Kernel.reservedBasisNames.contains d.cvW.name = false
  ty_bvs : d.cvW.type.looseBVarsBounded 0 = true
  ty_nfv : d.cvW.type.hasFvar = false
  rules_closed : ∀ rW ∈ d.rulesW, rW.rhs.looseBVarsBounded 0 = true ∧ rW.rhs.hasFvar = false
  observed :
    ∃ (lim : Option Nat) (a : _root_.Address)
      (rc nl ty np ni nm nmi rules k_flag rec_uns rec_block rec_idx ap r : SourceValue F)
      (h h' : Heap F) (cs : List (Call F)),
      keyOf t a = d.cvW.name ∧
      RCRep t lim h rc ∧
      S0.addr h ap a ∧
      CIRepExact (keyOf t) h
        (.construct kciEnum "Rec"
          [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx])
        (.recInfo d.cvW' d.mI d.rP d.rulesW') ∧
      IxVM.Consistency.StoredAs
        (.recInfo d.cvW' d.mI d.rP d.rulesW') (.recInfo d.cvW d.mI d.rP d.rulesW) ∧
      ObsFn W "KernelCheck::check_const"
        [rc, .construct kciEnum "Rec"
          [nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx], ap]
        h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls)

/-- Loader, reader, and closure-order facts for a twin recursor block `.indDecl block nP`. -/
structure TwinBlockWitness (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (block : List KConstantInfo) where
  E : Ixon.Env
  t : Ix.Kernel.RoleTable
  ds : List TwinMemberData
  tableWf : t.wf = true
  loads : ∀ lim, LoadFacts ⟨E, env, t, lim⟩
  good : Good ⟨E, env, t, none⟩ calls
  roleFacts : ∀ lim, DeclStoreInv env → CtxRoleFacts ⟨E, env, t, lim⟩
  ds_ne : ds ≠ []
  block_eq : block = ds.map (fun d => .recInfo d.cvW d.mI d.rP d.rulesW)
  names_nodup : (block.map (·.name)).Nodup
  members : ∀ d ∈ ds, TwinMemberWitness E env t calls d

/-- **End-to-end twin recursor refinement at `twinPosRulesJ`**: under `DeclStoreInv env`, refines
a `TwinBlockWitness` together with `NativeTwinInputs twinPosRulesJ` and
`ModeledTwinInputs twinPosRulesJ` to `InstallStep`, `DeclRecTwinRunJ twinPosRulesJ`, and
`DeclStoreInv env₂` (supporting both `large = false` and `large = true` twin recursors without
`PosSortLift`). -/
theorem twinRec_step_pos (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} (nP : Nat)
    (hS : DeclStoreInv env)
    (wb : TwinBlockWitness calls env block)
    (hNative : NativeTwinInputs twinPosRulesJ env (mkTwinRecParts env wb.ds))
    (hModeled : ModeledTwinInputs twinPosRulesJ env (mkTwinRecParts env wb.ds)) :
    let ws := mkTwinRecParts env wb.ds
    let env₂ : Ix.Kernel.Env .anon := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      DeclRecTwinRunJ twinPosRulesJ env block env₂ ∧
      DeclStoreInv env₂ := by
  intro ws env₂
  have hws_ne : ws ≠ [] := by
    cases hds : wb.ds with
    | nil => exact absurd hds wb.ds_ne
    | cons _ _ => simp [ws, mkTwinRecParts, hds]
  have hblk_ws : block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    rw [wb.block_eq]
    simp [ws, mkTwinRecParts, List.map_map, TwinMemberData.toPart]
  have hws_names : ws.map (·.cvW.name) = block.map (·.name) := by
    rw [hblk_ws, List.map_map]; rfl
  have hnd_ws_names : (ws.map (·.cvW.name)).Nodup := by
    rw [hws_names]; exact wb.names_nodup
  -- First pass: extract `ConstantValCheckJ twinPosRulesJ` and `StoredAs` for every `w ∈ ws`
  have hfront : ∀ w ∈ ws,
      ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW' ∧
      letFree w.cvW'.type = true ∧
      (∀ rl ∈ w.rulesW', letFree rl.rhs = true) ∧
      w.rulesW.length = w.rulesW'.length ∧
      IxVM.Consistency.ValStored w.cvW' w.cvW ∧
      List.Forall₂ IxVM.Consistency.RuleStored w.rulesW' w.rulesW ∧
      (∀ k tk, w.cvW.name ≠ .aux k tk) ∧
      env.find? w.cvW.name = none ∧
      (w.model?.isSome = true → env.find? (Ix.Kernel.auxKey w.cvW.name .model) = none) := by
    intro w hw
    obtain ⟨d, hd_mem, rfl⟩ := List.mem_map.mp hw
    have hm := wb.members d hd_mem
    obtain ⟨lim, a, rc, nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx,
      ap, r, h, h', cs, hkey, hrc, hadr, hci, hstored, ev_chk, hsub⟩ := hm.observed
    let c : Ctx := ⟨wb.E, env, wb.t, lim⟩
    have hgood_cs : Good c cs := (show Good c calls from wb.good).sub hsub
    have hshape : d.cvW.name.isProjFnShape = false := by
      rw [← hkey]; exact nat_keyOf_isProjFnShape_false wb.t a
    have hnot_aux : ∀ k tk, d.cvW.name ≠ .aux k tk := by
      intro k tk; rw [← hkey]; exact keyOf_not_aux wb.t a k tk
    obtain ⟨hcv_pos, _, hlf_ty, hlf_rls, hlen_eq, hrs_stored, _⟩ :=
      check_const_rec_inv hCore (c := c) hS wb.tableWf (wb.roleFacts lim hS)
        (wb.loads lim) hrc hgood_cs hci hstored hm.ty_bvs hm.ty_nfv
        hm.fresh_rec hm.not_basis hshape ev_chk
    exact ⟨hcv_pos, hlf_ty, hlf_rls, hlen_eq, hstored.1, hrs_stored,
      hnot_aux, hm.fresh_rec, hm.fresh_model⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name :=
    fun w hw => (hfront w hw).1.name_eq
  have hnd_all : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    twinRecs_append_twinModels_nodup hnd_ws_names hname_eq (fun w hw => (hfront w hw).2.2.2.2.2.2.1)
  have hfr_all : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => (hfront w hw).2.2.2.2.2.2.2.1)
      (fun w hw => (hfront w hw).2.2.2.2.2.2.2.2)
  have hmod_spec : ∀ w ∈ ws, ∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) := by
    intro w hw cvm mval hint hm_eq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
    exact lookupModelInfo?_eq_some.mp hm_eq
  -- Stage `DeclStoreInv` up to `envSelf`
  obtain ⟨_, hS_self⟩ := hS.step_twinSelf (judgeFrames_twinPosRulesJ env) hnd_all hfr_all
    hmod_spec (fun w hw => (hfront w hw).1)
  -- Second pass: assemble full `DeclRecTwinRunJ twinPosRulesJ`
  have hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂ := by
    refine ⟨ws, twinPeerRename ws, hws_ne, hblk_ws, rfl, hnd_all, hfr_all,
      twinPeerRename_spec ws, fun w hw => ?_⟩
    obtain ⟨d, hd_mem, rfl⟩ := List.mem_map.mp hw
    have hm := wb.members d hd_mem
    obtain ⟨lim, a, rc, nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx,
      ap, r, h, h', cs, hkey, hrc, hadr, hci, hstored, ev_chk, hsub⟩ := hm.observed
    let c : Ctx := ⟨wb.E, env, wb.t, lim⟩
    have hgood_cs : Good c cs := (show Good c calls from wb.good).sub hsub
    have hshape : d.cvW.name.isProjFnShape = false := by
      rw [← hkey]; exact nat_keyOf_isProjFnShape_false wb.t a
    have hef : EnvFacts c := hS.toEnvFacts wb.tableWf (wb.roleFacts lim hS)
    have hlf_c : LoadFacts c := wb.loads lim
    obtain ⟨hcv_pos, _, hlf_ty, hlf_rls, hlen_eq, hrs_stored, hroute⟩ :=
      check_const_rec_inv hCore (c := c) hS wb.tableWf (wb.roleFacts lim hS)
        hlf_c hrc hgood_cs hci hstored hm.ty_bvs hm.ty_nfv
        hm.fresh_rec hm.not_basis hshape ev_chk
    cases hroute with
    | native v_fam h_fam h_fam' h_mid cs_fam cs_mod cs_sub
        hnm e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub =>
      have e_mid : Heap.Extends h h_mid := e1.trans (e2.trans e3)
      have hout := hNative (d.toPart env) c a rc _ ap nm k_flag rec_uns rec_block v_fam r
        h h_fam h_fam' h_mid h' cs_fam cs_mod cs_sub
        (List.mem_map.mpr ⟨d, hd_mem, rfl⟩) rfl wb.tableWf hS hS_self hef hlf_c
        hcv_pos hlf_ty hlf_rls hm.canon_stored hm.lps_eq rfl hnm
        (hrc.mono e_mid) (S0.addr_mono e_mid hadr) hkey (hci.mono e_mid)
        e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub
      refine ⟨hcv_pos, hlf_ty, hm.canon_stored, hm.lps_eq, ?_, hout.ty_gen, hlen_eq,
        forall₂_zip_twinRuleJ (fun _ _ _ ha => ha) hrs_stored hm.rules_closed hlf_rls
          hout.rules_out⟩
      have hm_none : (d.toPart env).model? = none := hout.model_none
      rw [hm_none]
      exact ⟨lookupModelInfo?_eq_none.mp hm_none, hout.major_agree⟩
    | modeled v_fam v_mod h_fam h_fam' h_mid cs_fam cs_mod cs_sub
        hk_zero huns_zero hv_mod e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub =>
      have e_mid : Heap.Extends h h_mid := e1.trans (e2.trans e3)
      have hout := hModeled (d.toPart env) c a rc _ ap nm k_flag rec_uns rec_block v_fam v_mod r
        h h_fam h_fam' h_mid h' cs_fam cs_mod cs_sub
        (List.mem_map.mpr ⟨d, hd_mem, rfl⟩) rfl wb.tableWf hS hS_self hef hlf_c
        hcv_pos hlf_ty hlf_rls hm.canon_stored hm.lps_eq rfl hk_zero huns_zero hv_mod
        (hrc.mono e_mid) (S0.addr_mono e_mid hadr) hkey (hci.mono e_mid)
        e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub
      refine ⟨hcv_pos, hlf_ty, hm.canon_stored, hm.lps_eq, ?_, hout.ty_gen, hlen_eq,
        forall₂_zip_twinRuleJ (fun _ _ _ ha => ha) hrs_stored hm.rules_closed hlf_rls
          hout.rules_out⟩
      obtain ⟨⟨cvm, mval, hint⟩, hm_some⟩ := Option.isSome_iff_exists.mp hout.model_some
      rw [hm_some]
      exact lookupModelInfo?_eq_some.mp hm_some
  have hinst : IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ :=
    installStep_of_twinParts nP hws_ne hblk_ws hnd_all hfr_all
      (fun w hw => (hfront w hw).1)
      (fun w hw => ⟨(hfront w hw).2.2.2.2.1, (hfront w hw).2.2.2.2.2.1⟩)
  exact ⟨hinst, hrun, hS.step_twin_pos hrun⟩

/-- **`Decls`-compatible `DeclInv` step for a twin recursor block** via `twinPosRulesJ`
(quantifying `∃ env₂` outside `∀ V, DeclInv V env → DeclInv V env₂`). -/
theorem twinRec_declInv_step_pos (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hnodup : ((IxVM.Consistency.installs (.indDecl block nP)).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci₀.name = none)
    (hextra : DeclStoreInv env →
      ∃ wb : TwinBlockWitness calls env block,
        NativeTwinInputs twinPosRulesJ env (mkTwinRecParts env wb.ds) ∧
        ModeledTwinInputs twinPosRulesJ env (mkTwinRecParts env wb.ds)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨wb, hN, hM⟩ := hextra hS
    obtain ⟨hinst, hrun, _⟩ := twinRec_step_pos hCore nP hS wb hN hM
    exact ⟨_, hinst, fun _ _ hInv => hInv.step_twin_pos hrun⟩
  · obtain ⟨env₀, hinst⟩ := installStep_of_checked_fresh hchk hnodup hfresh
    exact ⟨env₀, hinst, fun _ _ hInv => absurd hInv.store hS⟩

/-- **End-to-end twin recursor refinement at `rulesJ`** (producing `DeclRecTwinRunJ rulesJ` and
`DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂` directly). -/
theorem twinRec_step_rulesJ (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} (nP : Nat)
    (hS : DeclStoreInv env)
    (wb : TwinBlockWitness calls env block)
    (hlift : ∀ d ∈ wb.ds, PosSortLift env d.cvW')
    (hNative : NativeTwinInputs rulesJ env (mkTwinRecParts env wb.ds))
    (hModeled : ModeledTwinInputs rulesJ env (mkTwinRecParts env wb.ds)) :
    let ws := mkTwinRecParts env wb.ds
    let env₂ : Ix.Kernel.Env .anon := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      DeclRecTwinRunJ rulesJ env block env₂ ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ ∧
      DeclStoreInv env₂ := by
  intro ws env₂
  have hws_ne : ws ≠ [] := by
    cases hds : wb.ds with
    | nil => exact absurd hds wb.ds_ne
    | cons _ _ => simp [ws, mkTwinRecParts, hds]
  have hblk_ws : block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    rw [wb.block_eq]
    simp [ws, mkTwinRecParts, List.map_map, TwinMemberData.toPart]
  have hpin : Ix.Kernel.basisPinHit block = none := basisPinHit_twinBlock_none hws_ne hblk_ws
  have hws_names : ws.map (·.cvW.name) = block.map (·.name) := by
    rw [hblk_ws, List.map_map]; rfl
  have hnd_ws_names : (ws.map (·.cvW.name)).Nodup := by
    rw [hws_names]; exact wb.names_nodup
  have hfront : ∀ w ∈ ws,
      ConstantValCheckJ rulesJ env w.cvW w.cvW' ∧
      letFree w.cvW'.type = true ∧
      (∀ rl ∈ w.rulesW', letFree rl.rhs = true) ∧
      w.rulesW.length = w.rulesW'.length ∧
      IxVM.Consistency.ValStored w.cvW' w.cvW ∧
      List.Forall₂ IxVM.Consistency.RuleStored w.rulesW' w.rulesW ∧
      (∀ k tk, w.cvW.name ≠ .aux k tk) ∧
      env.find? w.cvW.name = none ∧
      (w.model?.isSome = true → env.find? (Ix.Kernel.auxKey w.cvW.name .model) = none) := by
    intro w hw
    obtain ⟨d, hd_mem, rfl⟩ := List.mem_map.mp hw
    have hm := wb.members d hd_mem
    obtain ⟨lim, a, rc, nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx,
      ap, r, h, h', cs, hkey, hrc, hadr, hci, hstored, ev_chk, hsub⟩ := hm.observed
    let c : Ctx := ⟨wb.E, env, wb.t, lim⟩
    have hgood_cs : Good c cs := (show Good c calls from wb.good).sub hsub
    have hshape : d.cvW.name.isProjFnShape = false := by
      rw [← hkey]; exact nat_keyOf_isProjFnShape_false wb.t a
    have hnot_aux : ∀ k tk, d.cvW.name ≠ .aux k tk := by
      intro k tk; rw [← hkey]; exact keyOf_not_aux wb.t a k tk
    obtain ⟨_, hcv_rules, hlf_ty, hlf_rls, hlen_eq, hrs_stored, _⟩ :=
      check_const_rec_inv hCore (c := c) hS wb.tableWf (wb.roleFacts lim hS)
        (wb.loads lim) hrc hgood_cs hci hstored hm.ty_bvs hm.ty_nfv
        hm.fresh_rec hm.not_basis hshape ev_chk
    exact ⟨hcv_rules (hlift d hd_mem), hlf_ty, hlf_rls, hlen_eq, hstored.1, hrs_stored,
      hnot_aux, hm.fresh_rec, hm.fresh_model⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name :=
    fun w hw => (hfront w hw).1.name_eq
  have hnd_all : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    twinRecs_append_twinModels_nodup hnd_ws_names hname_eq (fun w hw => (hfront w hw).2.2.2.2.2.2.1)
  have hfr_all : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => (hfront w hw).2.2.2.2.2.2.2.1)
      (fun w hw => (hfront w hw).2.2.2.2.2.2.2.2)
  have hmod_spec : ∀ w ∈ ws, ∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) := by
    intro w hw cvm mval hint hm_eq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
    exact lookupModelInfo?_eq_some.mp hm_eq
  obtain ⟨_, hS_self⟩ := hS.step_twinSelf (Ix.Kernel.Model.judgeFrames_rulesJ env) hnd_all hfr_all
    hmod_spec (fun w hw => (hfront w hw).1)
  have hrun : DeclRecTwinRunJ rulesJ env block env₂ := by
    refine ⟨ws, twinPeerRename ws, hws_ne, hblk_ws, rfl, hnd_all, hfr_all,
      twinPeerRename_spec ws, fun w hw => ?_⟩
    obtain ⟨d, hd_mem, rfl⟩ := List.mem_map.mp hw
    have hm := wb.members d hd_mem
    obtain ⟨lim, a, rc, nl, ty, np, ni, nm, nmi, rules, k_flag, rec_uns, rec_block, rec_idx,
      ap, r, h, h', cs, hkey, hrc, hadr, hci, hstored, ev_chk, hsub⟩ := hm.observed
    let c : Ctx := ⟨wb.E, env, wb.t, lim⟩
    have hgood_cs : Good c cs := (show Good c calls from wb.good).sub hsub
    have hshape : d.cvW.name.isProjFnShape = false := by
      rw [← hkey]; exact nat_keyOf_isProjFnShape_false wb.t a
    have hef : EnvFacts c := hS.toEnvFacts wb.tableWf (wb.roleFacts lim hS)
    have hlf_c : LoadFacts c := wb.loads lim
    obtain ⟨_, hcv_rules_fn, hlf_ty, hlf_rls, hlen_eq, hrs_stored, hroute⟩ :=
      check_const_rec_inv hCore (c := c) hS wb.tableWf (wb.roleFacts lim hS)
        hlf_c hrc hgood_cs hci hstored hm.ty_bvs hm.ty_nfv
        hm.fresh_rec hm.not_basis hshape ev_chk
    have hcv_r : ConstantValCheckJ rulesJ env d.cvW d.cvW' := hcv_rules_fn (hlift d hd_mem)
    cases hroute with
    | native v_fam h_fam h_fam' h_mid cs_fam cs_mod cs_sub
        hnm e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub =>
      have e_mid : Heap.Extends h h_mid := e1.trans (e2.trans e3)
      have hout := hNative (d.toPart env) c a rc _ ap nm k_flag rec_uns rec_block v_fam r
        h h_fam h_fam' h_mid h' cs_fam cs_mod cs_sub
        (List.mem_map.mpr ⟨d, hd_mem, rfl⟩) rfl wb.tableWf hS hS_self hef hlf_c
        hcv_r hlf_ty hlf_rls hm.canon_stored hm.lps_eq rfl hnm
        (hrc.mono e_mid) (S0.addr_mono e_mid hadr) hkey (hci.mono e_mid)
        e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub
      refine ⟨hcv_r, hlf_ty, hm.canon_stored, hm.lps_eq, ?_, hout.ty_gen, hlen_eq,
        forall₂_zip_twinRuleJ (fun _ _ _ ha => ha) hrs_stored hm.rules_closed hlf_rls
          hout.rules_out⟩
      have hm_none : (d.toPart env).model? = none := hout.model_none
      rw [hm_none]
      exact ⟨lookupModelInfo?_eq_none.mp hm_none, hout.major_agree⟩
    | modeled v_fam v_mod h_fam h_fam' h_mid cs_fam cs_mod cs_sub
        hk_zero huns_zero hv_mod e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub =>
      have e_mid : Heap.Extends h h_mid := e1.trans (e2.trans e3)
      have hout := hModeled (d.toPart env) c a rc _ ap nm k_flag rec_uns rec_block v_fam v_mod r
        h h_fam h_fam' h_mid h' cs_fam cs_mod cs_sub
        (List.mem_map.mpr ⟨d, hd_mem, rfl⟩) rfl wb.tableWf hS hS_self hef hlf_c
        hcv_r hlf_ty hlf_rls hm.canon_stored hm.lps_eq rfl hk_zero huns_zero hv_mod
        (hrc.mono e_mid) (S0.addr_mono e_mid hadr) hkey (hci.mono e_mid)
        e1 e2 e3 ev_fam ev_mod ev_sub hg_fam hg_mod hg_sub
      refine ⟨hcv_r, hlf_ty, hm.canon_stored, hm.lps_eq, ?_, hout.ty_gen, hlen_eq,
        forall₂_zip_twinRuleJ (fun _ _ _ ha => ha) hrs_stored hm.rules_closed hlf_rls
          hout.rules_out⟩
      obtain ⟨⟨cvm, mval, hint⟩, hm_some⟩ := Option.isSome_iff_exists.mp hout.model_some
      rw [hm_some]
      exact lookupModelInfo?_eq_some.mp hm_some
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ :=
    declRunJ_of_twinRec hpin hrun
  have hinst : IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ :=
    installStep_of_twinParts nP hws_ne hblk_ws hnd_all hfr_all
      (fun w hw => (hfront w hw).1)
      (fun w hw => ⟨(hfront w hw).2.2.2.2.1, (hfront w hw).2.2.2.2.2.1⟩)
  exact ⟨hinst, hrun, hdecl, hS.step_twin_rulesJ hrun⟩

/-- **`Decls`-compatible `DeclInv` step for a twin recursor block** via `rulesJ` (`decls_step_of_store`). -/
theorem twinRec_declInv_step_rulesJ (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hnodup : ((IxVM.Consistency.installs (.indDecl block nP)).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci₀.name = none)
    (hextra : DeclStoreInv env →
      ∃ wb : TwinBlockWitness calls env block,
        (∀ d ∈ wb.ds, PosSortLift env d.cvW') ∧
        NativeTwinInputs rulesJ env (mkTwinRecParts env wb.ds) ∧
        ModeledTwinInputs rulesJ env (mkTwinRecParts env wb.ds)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  refine decls_step_of_store hchk hnodup hfresh fun hS => ?_
  obtain ⟨wb, hlift, hN, hM⟩ := hextra hS
  obtain ⟨hinst, _, hdecl, _⟩ := twinRec_step_rulesJ hCore nP hS wb hlift hN hM
  exact ⟨_, hinst, hdecl⟩

end IxVM.Refinement.Decl
