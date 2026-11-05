import Ix.Cert.SourceTrace
import Ix.LeanIngress.Rename
import Ix.LeanIngress.Theorems

/-! # Pre-lowering fiber safety and collapsed trace invariants

This module defines the structural predicates and executable boolean checkers
for pre-lowering fiber safety on a closure `(sub, blocks)` at an artifact and
role table `(ixe, t)`, and connects `prepareSourceCollapsedAt` to the collapsed
trace invariants in `Ix.Cert.SourceTrace`, `Ix.Cert.SourcePrelude`, and
`Ix.Cert.SourceReplay`:

* `GroupIntraInjective` and `checkGroupIntraInjective`: within every inductive
  and definition group of `groupsOf sub blocks`, `Key.subst` at
  `fiberAliasAt ixe (roleAtMap t)` maps the group's declared constants to
  pairwise distinct keys (`Nodup`);
* `HintsAgreeAt` and `checkHintsAgreeAt`: every definition in `sub` has its
  nominal reducibility hint matching `fiberHintsMap ixe` at its substituted key;
* `FiberAliasSafe`, `checkGroupFiberSafe`, and `checkGroupFiberSafe_sound`: the
  combined executable checker and its soundness theorem;
* `step_fresh_or_beqF`, `alias_fresh_or_beqF`, `collapseRead_fresh_or_beqF`,
  and `prepareSourceCollapsedAt_trace`: every step in a successful collapsed
  trace is either a fresh declaration/block or an exact structural match
  (`Declaration.beqF` / `BlockRead.beqF`) with an already-kept declaration or
  block, while `StableOwned`, `OwnerExact`, `KeptNoBasis`, `declsGoodB`,
  `bundleDisjointB`, `evidenceGoodB`, and `keepsPrelude` all hold.
-/

namespace Ix.LeanIngress

open Ix.Kernel
open Ix.Kernel.Reader (CName CExpr CVal CDecl ReadError State Read BlockRead Prelude)
open Ix.Cert.SourcePrelude (SKey OwnerExt ReadInv ReadBad readStep readLoop readFinish
  forIn_id_inv_or_array collapseRead_eq collapseRead_facts step_ownerFacts alias_none_fresh
  Trace lowerAllCollapsed_trace)
open Ix.Cert.SourceReplay (OwnerExact KeptNoBasis StableOwned step_drop collapseRead_ownerExact
  trace_ownerExact trace_keptNoBasis)

/-! ## Intra-group fiber injectivity and hint agreement -/

/-- Within an inductive or definition group, `Key.subst ρ` maps the group's
declared constants (and, for an inductive group, its converted `BlockRead.names`)
to pairwise distinct keys (`List.Nodup`). -/
def Group.IntraInjective (ρ : FiberMap) : Group → Prop
  | g@(.inductive _ _ _) =>
    ((g.names.toList.map ingressKey).map (Key.subst ρ)).Nodup ∧
      ∀ rb, convert g = .ok (.inductive rb) →
        ((BlockRead.names rb).map (Key.subst ρ)).Nodup
  | .definitions ms =>
    ((ms.toList.map (fun ci => ingressKey ci.getCnst.name)).map (Key.subst ρ)).Nodup
  | _ => True

/-- Within every inductive group and every definition group in `groupsOf sub blocks`,
`Key.subst (fiberAliasAt ixe (roleAtMap t))` is injective on the group's
declared keys (`Nodup` after `Key.subst`). -/
def GroupIntraInjective (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (sub : Ix.Environment) (blocks : Ix.CondensedBlocks) : Prop :=
  let ρ := fiberAliasAt ixe (roleAtMap t)
  ∀ g ∈ (groupsOf sub blocks).toList, Group.IntraInjective ρ g

/-- Executable boolean check for `Group.IntraInjective` on a single group. -/
def checkGroupIntraInjectiveOne (ρ : FiberMap) : Group → Bool
  | g@(.inductive _ _ _) =>
    decide (((g.names.toList.map ingressKey).map (Key.subst ρ)).Nodup) &&
      match convert g with
      | .ok (.inductive rb) => decide (((BlockRead.names rb).map (Key.subst ρ)).Nodup)
      | _ => true
  | .definitions ms =>
    decide (((ms.toList.map (fun ci => ingressKey ci.getCnst.name)).map (Key.subst ρ)).Nodup)
  | _ => true

/-- Executable boolean check for `GroupIntraInjective`. -/
def checkGroupIntraInjective (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (sub : Ix.Environment) (blocks : Ix.CondensedBlocks) : Bool :=
  let ρ := fiberAliasAt ixe (roleAtMap t)
  (groupsOf sub blocks).toList.all (checkGroupIntraInjectiveOne ρ)

theorem checkGroupIntraInjectiveOne_sound {ρ : FiberMap} {g : Group}
    (h : checkGroupIntraInjectiveOne ρ g = true) : Group.IntraInjective ρ g := by
  cases g with
  | «inductive» types ctors recs =>
    unfold checkGroupIntraInjectiveOne at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨of_decide_eq_true h1, fun rb hc => ?_⟩
    rw [hc] at h2
    exact of_decide_eq_true h2
  | definitions ms =>
    unfold checkGroupIntraInjectiveOne at h
    unfold Group.IntraInjective
    exact of_decide_eq_true h
  | «axiom» _ => trivial
  | quot _ => trivial
  | invalid _ _ => trivial

/-- Soundness of `checkGroupIntraInjective`. -/
theorem checkGroupIntraInjective_sound {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {sub : Ix.Environment} {blocks : Ix.CondensedBlocks}
    (h : checkGroupIntraInjective ixe t sub blocks = true) :
    GroupIntraInjective ixe t sub blocks := by
  unfold checkGroupIntraInjective GroupIntraInjective at *
  dsimp only at h ⊢
  intro g hg
  exact checkGroupIntraInjectiveOne_sound (List.all_eq_true.mp h g hg)

/-- Every definition in `sub` has its nominal reducibility hint (`definitionShape`)
matching `fiberHintsMap ixe` at its substituted key under
`fiberAliasAt ixe (roleAtMap t)`. -/
def HintsAgreeAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (sub : Ix.Environment) : Prop :=
  let ρ := fiberAliasAt ixe (roleAtMap t)
  let hints := fiberHintsMap ixe
  ∀ n ci, (n, ci) ∈ sub.consts.toList →
    ∀ kind safety hint, definitionShape ci = some (kind, safety, hint) →
      hints[Key.subst ρ (ingressKey n)]? = some hint

/-- Executable boolean check for `HintsAgreeAt`. -/
def checkHintsAgreeAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (sub : Ix.Environment) : Bool :=
  let ρ := fiberAliasAt ixe (roleAtMap t)
  let hints := fiberHintsMap ixe
  sub.consts.toList.all fun (n, ci) =>
    match definitionShape ci with
    | some (_, _, hint) =>
      hints[Key.subst ρ (ingressKey n)]? == some hint
    | none => true

/-- Soundness of `checkHintsAgreeAt`. -/
theorem checkHintsAgreeAt_sound {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} {sub : Ix.Environment}
    (h : checkHintsAgreeAt ixe t sub = true) : HintsAgreeAt ixe t sub := by
  unfold checkHintsAgreeAt HintsAgreeAt at *
  dsimp only at h ⊢
  intro n ci hmem kind safety hint hshape
  have hall := List.all_eq_true.mp h (n, ci) hmem
  dsimp only at hall
  rw [hshape] at hall
  simp only [beq_iff_eq] at hall
  exact hall

/-- Pre-lowering fiber safety on `(sub, blocks)` at `(ixe, t)`: intra-group
key injectivity after `Key.subst` and reducibility-hint agreement. -/
def FiberAliasSafe (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (sub : Ix.Environment) (blocks : Ix.CondensedBlocks) : Prop :=
  GroupIntraInjective ixe t sub blocks ∧ HintsAgreeAt ixe t sub

/-- Executable boolean checker for pre-lowering fiber safety (`GroupIntraInjective`
and `HintsAgreeAt`). -/
def checkGroupFiberSafe (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (sub : Ix.Environment) (blocks : Ix.CondensedBlocks) : Bool :=
  checkGroupIntraInjective ixe t sub blocks && checkHintsAgreeAt ixe t sub

/-- **Soundness of `checkGroupFiberSafe`**: when the executable check succeeds,
both `GroupIntraInjective` and `HintsAgreeAt` (`FiberAliasSafe`) hold. -/
theorem checkGroupFiberSafe_sound {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {sub : Ix.Environment} {blocks : Ix.CondensedBlocks}
    (h : checkGroupFiberSafe ixe t sub blocks = true) :
    GroupIntraInjective ixe t sub blocks ∧ HintsAgreeAt ixe t sub := by
  unfold checkGroupFiberSafe at h
  rw [Bool.and_eq_true] at h
  exact ⟨checkGroupIntraInjective_sound h.1, checkHintsAgreeAt_sound h.2⟩

/-! ## Step and trace characterization for `prepareSourceCollapsedAt` -/

/-- Every successful declaration-collapse step under `OwnerExact` either keeps a
declaration whose declared names are all fresh, or drops a declaration that
matches an already-kept declaration via `Declaration.beqF` (and therefore equals
it) with every declared name owned by that kept index. -/
theorem step_fresh_or_beqF {s s' : CollapseState} (owner : OwnerExact s)
    {first : SKey} {d : Declaration .source} {kept : Bool}
    (h : s.step first d = (s', .ok kept)) :
    (kept = true ∧ s'.kept = s.kept.push d ∧ ∀ k ∈ d.names, s.owner[k]? = none) ∨
    (kept = false ∧ s' = s ∧ ∃ i d₀, s.kept[i]? = some d₀ ∧
      Declaration.beqF d d₀ = true ∧ d = d₀ ∧ ∀ k ∈ d.names, s.owner[k]? = some i) := by
  cases kept with
  | true =>
    left
    exact ⟨rfl, by simpa using Ix.Cert.SourcePrelude.step_kept h, (step_ownerFacts h).2.2 rfl⟩
  | false =>
    right
    obtain ⟨rfl, i, held, hown⟩ := step_drop owner h
    exact ⟨rfl, rfl, i, d, held, Declaration.beqF_refl d, rfl, hown⟩

/-- Every successful inductive-block alias check either finds all of the block's
names fresh (`res = none`) or matches an already-kept block `rb₀` at index `k`
via `BlockRead.beqF` (`res = some k`, hence `rb = rb₀`). -/
theorem alias_fresh_or_beqF {kb : KeptBlocks} {s : CollapseState} {first : SKey}
    {rb : BlockRead .source} {res : Option Nat}
    (h : kb.alias s first rb = .ok res) :
    (res = none ∧ ∀ k ∈ BlockRead.names rb, s.owner[k]? = none) ∨
    ∃ k rb₀, res = some k ∧ kb.blocks[k]? = some rb₀ ∧
      BlockRead.beqF rb rb₀ = true ∧ rb = rb₀ ∧
      ∀ n ∈ BlockRead.names rb, kb.blockOf[n]? = some k := by
  cases res with
  | none =>
    exact .inl ⟨rfl, alias_none_fresh h⟩
  | some k =>
    right
    unfold KeptBlocks.alias at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i k' hk'
        split at h
        · rename_i hgood
          cases h
          obtain ⟨hall, hany⟩ := Bool.and_eq_true_iff.mp hgood
          cases hblk : kb.blocks[k]? with
          | none => simp [hblk] at hany
          | some rb₀ =>
            simp only [hblk, Option.any_some] at hany
            refine ⟨k, rb₀, rfl, hblk, hany, BlockRead.beqF_eq_true hany, fun n hn => ?_⟩
            exact beq_iff_eq.mp (List.all_eq_true.mp hall n hn)
        · cases h
      · cases h

/-- An `.alias` step in `collapseGroup` comes from an inductive block that
matches an already-kept block in `kb` via `BlockRead.beqF`. -/
theorem collapseGroup_alias_beqF {st : State .source} {s s' : CollapseState}
    {kb kb' : KeptBlocks} {first : SKey} {pos k : Nat} {c : Except ReadError Converted}
    (h : collapseGroup st s kb first pos c = .alias k s' kb') :
    s' = s ∧ kb' = kb ∧ ∃ rb rb₀, c = .ok (.inductive rb) ∧
      kb.blocks[k]? = some rb₀ ∧ BlockRead.beqF rb rb₀ = true ∧ rb = rb₀ ∧
      ∀ n ∈ BlockRead.names rb, kb.blockOf[n]? = some k := by
  cases c with
  | error e => simp [collapseGroup] at h
  | ok conv =>
    unfold collapseGroup at h
    dsimp only at h
    cases conv with
    | «inductive» rb =>
      dsimp only at h
      cases ha : kb.alias s first rb with
      | error e => simp [ha] at h
      | ok res =>
        cases res with
        | none =>
          simp only [ha] at h
          split at h
          · cases h
          · split at h <;> cases h
        | some k' =>
          simp only [ha, CollapseStep.alias.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rcases alias_fresh_or_beqF ha with ⟨hnone, _⟩ | ⟨k'', rb₀, hsome, hblk, hbeq, heq, hown⟩
          · cases hnone
          · cases hsome
            exact ⟨rfl, rfl, rb, rb₀, rfl, hblk, hbeq, heq, hown⟩
    | definitions ms =>
      dsimp only at h
      split at h
      · cases h
      · split at h <;> cases h
    | «axiom» cv =>
      dsimp only at h
      split at h
      · cases h
      · split at h <;> cases h
    | quot kind cv =>
      dsimp only at h
      split at h
      · cases h
      · split at h <;> cases h

private theorem getElem?_push_of_some {α : Type} {xs : Array α} {i : Nat} {v : α} (x : α)
    (h : xs[i]? = some v) : (xs.push x)[i]? = some v := by
  have hlt : i < xs.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [Array.getElem?_push]
  simp [h]
  omega

private theorem getElem?_push_self {α : Type} (xs : Array α) (x : α) :
    (xs.push x)[xs.size]? = some x := by
  rw [Array.getElem?_push]
  simp

/-- Every declaration of a lowered group that `collapseRead` processes is either
kept in `r.decls` (with all its names fresh prior to the group) or matches a
kept declaration in `s'.kept` via `Declaration.beqF`. -/
theorem collapseRead_fresh_or_beqF {s s' : CollapseState} (owner : OwnerExact s)
    {first : SKey} {raw r : Read .source} {dropped : Array SKey}
    (h : collapseRead s first raw = (s', .ok (r, dropped))) :
    OwnerExact s' ∧
    ∀ d ∈ raw.decls.toList,
      (d ∈ r.decls.toList ∧ ∀ k ∈ d.names, s.owner[k]? = none) ∨
      ∃ i d₀, s'.kept[i]? = some d₀ ∧ Declaration.beqF d d₀ = true ∧ d = d₀ ∧
        ∀ k ∈ d.names, s'.owner[k]? = some i := by
  have exact' := collapseRead_ownerExact owner h
  obtain ⟨_, claims, fresh, _, _, _, _⟩ := collapseRead_facts h
  refine ⟨exact', fun d hd => ?_⟩
  by_cases hmem : d ∈ r.decls.toList
  · exact .inl ⟨hmem, fun k hk => (fresh d hmem k hk).1⟩
  · -- `collapseRead` processes every declaration in `raw.decls` through `step`;
    -- whether kept or dropped, `s'.kept` holds a `Declaration.beqF`-equal copy when `d.names` is non-empty,
    -- and every declaration in `raw.decls` that was stepped either entered `r.decls` or matched `s'.kept`.
    let I (pre : List (Declaration .source × Nat)) (a : Ix.Cert.SourcePrelude.ReadAcc) : Prop :=
      a.1 = none ∧ OwnerExact a.2.1 ∧ OwnerExt s a.2.1 ∧
      ∀ x ∈ pre,
        (x.1 ∈ a.2.2.1.toList ∧ ∀ k ∈ x.1.names, s.owner[k]? = none) ∨
        ∃ i d₀, a.2.1.kept[i]? = some d₀ ∧ Declaration.beqF x.1 d₀ = true ∧ x.1 = d₀ ∧
          ∀ k ∈ x.1.names, a.2.1.owner[k]? = some i
    have init : I [] (none, s, #[], 0, #[]) :=
      ⟨rfl, owner, .refl s, fun _ hx => nomatch hx⟩
    have inv := forIn_id_inv_or_array I ReadBad (readStep first s.kept.size raw.generated)
      raw.decls.zipIdx (fun pre x _ a _ ha => by
        obtain ⟨hact, hown, hext, heach⟩ := ha
        rcases hs : a.2.1.step first x.1 with ⟨next, res⟩
        cases res with
        | error e =>
          simp only [readStep, hs, pure]
          exact ⟨next.restore s.kept.size, e, rfl⟩
        | ok b =>
          have hown' := OwnerExact.step hown hs
          have hf := step_ownerFacts hs
          have hext' : OwnerExt s next := hext.trans hf.1
          rcases step_fresh_or_beqF hown hs with ⟨rfl, hkept, hfr⟩ | ⟨rfl, rfl, i, d₀, held, hbeq, heq, hallk⟩
          · have stepEach (gen : Nat) : I (pre ++ [x]) (none, next, a.2.2.1.push x.1, gen, a.2.2.2.2) := by
              refine ⟨rfl, hown', hext', fun y hy => ?_⟩
              rcases List.mem_append.mp hy with hy | hy
              · rcases heach y hy with ⟨hmy, hfy⟩ | ⟨i, d₀, held, hbeq, heq, hk⟩
                · exact .inl ⟨by simp [hmy], hfy⟩
                · refine .inr ⟨i, d₀, ?_, hbeq, heq, fun k hk' => hf.1 k i (hk k hk')⟩
                  rw [hkept]
                  exact getElem?_push_of_some x.1 held
              · simp only [List.mem_singleton] at hy
                subst hy
                exact .inl ⟨by simp, fun k hk => hext.fresh (hfr k hk)⟩
            by_cases early : x.2 < raw.generated
            · simpa only [readStep, hs, early, ite_true, pure] using stepEach (a.2.2.2.1 + 1)
            · simpa only [readStep, hs, early, ite_false, pure] using stepEach a.2.2.2.1
          · simp only [readStep, hs, pure]
            refine ⟨rfl, hown, hext, fun y hy => ?_⟩
            rcases List.mem_append.mp hy with hy | hy
            · exact heach y hy
            · simp only [List.mem_singleton] at hy
              subst hy
              exact .inr ⟨i, d₀, held, hbeq, heq, hallk⟩) _ init
    change I raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
    rw [collapseRead_eq] at h
    rcases inv with ⟨hact, _, _, heach⟩ | ⟨t, e, he⟩
    · simp only [readFinish, hact, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      obtain ⟨j, hj⟩ := List.mem_map.mp
        (show d ∈ raw.decls.zipIdx.toList.map Prod.fst by simpa using hd)
      have := heach j hj.1
      rwa [hj.2] at this
    · simp [readFinish, he] at h

/-- After `collapseRead` succeeds from `OwnerExact s`, every declaration
`d ∈ raw.decls.toList` (whether kept as fresh or dropped as a duplicate) has a
`Declaration.beqF`-matching declaration `d₀` stored in `s'.kept` (with `d = d₀`). -/
theorem collapseRead_kept_beqF {s s' : CollapseState} (owner : OwnerExact s)
    {first : SKey} {raw r : Read .source} {dropped : Array SKey}
    (h : collapseRead s first raw = (s', .ok (r, dropped))) :
    OwnerExact s' ∧
    ∀ d ∈ raw.decls.toList,
      ∃ (i : Nat) (d₀ : Declaration .source), s'.kept[i]? = some d₀ ∧ Declaration.beqF d d₀ = true ∧ d = d₀ := by
  have exact' := collapseRead_ownerExact owner h
  refine ⟨exact', fun d hd => ?_⟩
  let I (pre : List (Declaration .source × Nat)) (a : Ix.Cert.SourcePrelude.ReadAcc) : Prop :=
    a.1 = none ∧ OwnerExact a.2.1 ∧
    ∀ x ∈ pre,
      ∃ (i : Nat) (d₀ : Declaration .source), a.2.1.kept[i]? = some d₀ ∧ Declaration.beqF x.1 d₀ = true ∧ x.1 = d₀
  have init : I [] (none, s, #[], 0, #[]) :=
    ⟨rfl, owner, fun _ hx => nomatch hx⟩
  have inv := forIn_id_inv_or_array I ReadBad (readStep first s.kept.size raw.generated)
    raw.decls.zipIdx (fun pre x _ a _ ha => by
      obtain ⟨hact, hown, heach⟩ := ha
      rcases hs : a.2.1.step first x.1 with ⟨next, res⟩
      cases res with
      | error e =>
        simp only [readStep, hs, pure]
        exact ⟨next.restore s.kept.size, e, rfl⟩
      | ok b =>
        have hown' := OwnerExact.step hown hs
        rcases step_fresh_or_beqF hown hs with ⟨rfl, hkept, _⟩ | ⟨rfl, rfl, i, d₀, held, hbeq, heq, _⟩
        · have stepEach (gen : Nat) : I (pre ++ [x]) (none, next, a.2.2.1.push x.1, gen, a.2.2.2.2) := by
            refine ⟨rfl, hown', fun y hy => ?_⟩
            rcases List.mem_append.mp hy with hy | hy
            · obtain ⟨i, d₀, held, hbeq, heq⟩ := heach y hy
              refine ⟨i, d₀, ?_, hbeq, heq⟩
              rw [hkept]
              exact getElem?_push_of_some x.1 held
            · simp only [List.mem_singleton] at hy
              subst y
              refine ⟨a.2.1.kept.size, x.1, ?_, Declaration.beqF_refl x.1, rfl⟩
              rw [hkept]
              exact getElem?_push_self a.2.1.kept x.1
          by_cases early : x.2 < raw.generated
          · simpa only [readStep, hs, early, ite_true, pure] using stepEach (a.2.2.2.1 + 1)
          · simpa only [readStep, hs, early, ite_false, pure] using stepEach a.2.2.2.1
        · simp only [readStep, hs, pure]
          refine ⟨rfl, hown, fun y hy => ?_⟩
          rcases List.mem_append.mp hy with hy | hy
          · exact heach y hy
          · simp only [List.mem_singleton] at hy
            subst hy
            exact ⟨i, d₀, held, hbeq, heq⟩) _ init
  change I raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
  rw [collapseRead_eq] at h
  rcases inv with ⟨hact, _, heach⟩ | ⟨t, e, he⟩
  · simp only [readFinish, hact, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    obtain ⟨j, hj⟩ := List.mem_map.mp
      (show d ∈ raw.decls.zipIdx.toList.map Prod.fst by simpa using hd)
    have := heach j hj.1
    rwa [hj.2] at this
  · simp [readFinish, he] at h

/-- **Connecting `Converted.quotient_eq_substKeys_canon` to `collapseRead`**:
for any converted group `c`, lowering the canonicalized key-substituted group
`Converted.substKeys ρ (Converted.canon c)` is identical to lowering
`Converted.quotient ρ c`, and when `collapseRead` succeeds from `OwnerExact s`,
every declaration `d ∈ raw.decls.toList` has a `Declaration.beqF`-matching
declaration `d₀` stored in `s'.kept` (with `d = d₀`). -/
theorem collapseRead_substKeys_canon_beqF {ρ : FiberMap} {st : State .source}
    {c : Converted} {raw r : Read .source}
    {s s' : CollapseState} {first : SKey} {dropped : Array SKey}
    (owner : OwnerExact s)
    (hlow : lower st (Converted.substKeys ρ (Converted.canon c)) = .ok raw)
    (hcol : collapseRead s first raw = (s', .ok (r, dropped))) :
    lower st (Converted.quotient ρ c) = .ok raw ∧
    OwnerExact s' ∧
    ∀ d ∈ raw.decls.toList,
      ∃ (i : Nat) (d₀ : Declaration .source), s'.kept[i]? = some d₀ ∧ Declaration.beqF d d₀ = true ∧ d = d₀ := by
  rw [← Converted.quotient_eq_substKeys_canon] at hlow
  exact ⟨hlow, collapseRead_kept_beqF owner hcol⟩

/-- When `collapsedChecksWith ixe t b ev ds = none`, all three executable
stream/bundle/evidence checks return `true`. -/
theorem collapsedChecksWith_booleans {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {b : Ix.RoleEvidence.Bundle} {ev : Ix.Kernel.Evidences .source}
    {ds : Array (Declaration .source)}
    (h : collapsedChecksWith ixe t b ev ds = none) :
    let ρ := fiberAliasAt ixe (roleAtMap t)
    let src := sourceAddrs ixe
    declsGoodB (qRepAtB src ρ) ds = true ∧
      bundleDisjointB ixe b = true ∧
      evidenceGoodB (qEvB src ρ (bundleAddrs b)) (evidenceSubst ρ ev) = true := by
  unfold collapsedChecksWith at h
  dsimp only at h ⊢
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Connection between `prepareSourceCollapsedAtUsing` and the trace invariants**,
over explicit bundle and evidence sources. -/
theorem prepareSourceCollapsedAtUsing_trace {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bundle : Except String Ix.RoleEvidence.Bundle} {ev : Ix.Kernel.Evidences .source}
    {hints : CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Prelude .source} {sub : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsedAtUsing bundle ev ixe t hints pre sub blocks = .ok ds) :
    let ρ := fiberAliasAt ixe (roleAtMap t)
    let src := sourceAddrs ixe
    ∃ b rs fin decls s kb,
      bundle = .ok b ∧
      Trace (graphCollapsed ρ hints sub blocks) pre.state
        (scheduleOf (graphCollapsed ρ hints sub blocks)).zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧
      fin = rs.foldl State.commit pre.state ∧
      decls.toList = rs.flatMap (·.decls.toList) ∧
      ds = Ix.Kernel.Frontend.preparePrelude pre.ix decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state fin = true ∧
      StableOwned s fin ∧
      OwnerExact s ∧
      KeptNoBasis s ∧
      declsGoodB (qRepAtB src ρ) ds = true ∧
      bundleDisjointB ixe b = true ∧
      evidenceGoodB (qEvB src ρ (bundleAddrs b)) (evidenceSubst ρ ev) = true ∧
      (∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t)))) ∧
      (evidenceSubst ρ ev).Good
        (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) := by
  dsimp only
  unfold prepareSourceCollapsedAtUsing at h
  cases hp : prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre sub blocks with
  | error e => rw [hp] at h; cases h
  | ok ds' =>
    rw [hp] at h
    dsimp only at h
    cases hc : collapsedChecksUsing bundle ev ixe t ds' with
    | error e => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      cases h
      obtain ⟨b, hbun, hcw⟩ := collapsedChecksUsing_spec hc
      obtain ⟨hdB, hbdB, hevB⟩ := collapsedChecksWith_booleans hcw
      obtain ⟨hdGood, _, _, hevGood⟩ := collapsedChecksWith_spec hcw
      obtain ⟨fin, decls, hl, hkeeps, hprep⟩ := prepareSourceCollapsed_keepsPrelude hp
      obtain ⟨rs, s, kb, htrace, hkept, hfin, hflat, hstable⟩ :=
        Ix.Cert.SourceTrace.lowerAllCollapsed_stable hl
      exact ⟨b, rs, fin, decls, s, kb, hbun, htrace, hkept, hfin, hflat, hprep, hkeeps,
        hstable, trace_ownerExact htrace, trace_keptNoBasis htrace,
        hdB, hbdB, hevB, hdGood, hevGood⟩

/-- **Connection between `prepareSourceCollapsedAt` and the trace invariants**:
whenever `prepareSourceCollapsedAt ixe t hints pre sub blocks = .ok ds`, there is
a committed quotient bundle `b` and a collapsed trace `(rs, fin, decls, s, kb)`
such that:
* `Trace` holds on `graphCollapsed (fiberAliasAt ixe (roleAtMap t)) hints sub blocks`,
  and `StableOwned s fin`, `OwnerExact s`, and `KeptNoBasis s` all hold;
* `State.keepsPrelude pre.state fin = true`, `declsGoodB ... ds = true`,
  `bundleDisjointB ixe b = true`, and `evidenceGoodB ... = true` all hold;
* every declaration and evidence item satisfies `Good` on representatives (and
  bundle-only names). -/
theorem prepareSourceCollapsedAt_trace {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Prelude .source} {sub : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsedAt ixe t hints pre sub blocks = .ok ds) :
    let ρ := fiberAliasAt ixe (roleAtMap t)
    let src := sourceAddrs ixe
    ∃ b rs fin decls s kb,
      Ix.RoleEvidence.quotientBundle () = .ok b ∧
      Trace (graphCollapsed ρ hints sub blocks) pre.state
        (scheduleOf (graphCollapsed ρ hints sub blocks)).zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧
      fin = rs.foldl State.commit pre.state ∧
      decls.toList = rs.flatMap (·.decls.toList) ∧
      ds = Ix.Kernel.Frontend.preparePrelude pre.ix decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state fin = true ∧
      StableOwned s fin ∧
      OwnerExact s ∧
      KeptNoBasis s ∧
      declsGoodB (qRepAtB src ρ) ds = true ∧
      bundleDisjointB ixe b = true ∧
      evidenceGoodB (qEvB src ρ (bundleAddrs b))
        (evidenceSubst ρ (Ix.RoleEvidence.quotientEvidence ())) = true ∧
      (∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t)))) ∧
      (evidenceSubst ρ (Ix.RoleEvidence.quotientEvidence ())).Good
        (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) :=
  prepareSourceCollapsedAtUsing_trace h

end Ix.LeanIngress
