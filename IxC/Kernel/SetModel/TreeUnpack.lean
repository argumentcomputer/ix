module

public import IxC.Kernel.Denotes
public import IxC.Kernel.SetModel.TaggedSum
public import IxC.Kernel.Term.UnpackSpec

@[expose] public section

/-!
# Bounded graph chains and tree unpacking for modeled structure projections

Supports `Denotes.proj_table` on modeled inductive structures (`entry.off ≥ 2`):

* `boundedGraph F n` restricts a meta-level operation `F : V → V` to the small
  graph `{⟨x, F x⟩ : x ∈ univ n ∧ F x ∈ univ n}`, which unconditionally inhabits
  `univ (n + 1)` (`boundedGraph_mem_univ`) and computes `F x` under `chainApp`
  whenever `x` and `F x` live in some common universe (`chainApp_boundedGraph`).
* `treeUnpack spec` traverses a tagged native auxiliary inductive value and
  rebuilds mimic-container constructors according to `spec : UnpackSpec`, leaving
  real-member values untouched.  Its finite-fuel approximation `treeUnpackOpt`
  is monotone in fuel, so the union over all fuels is functional and satisfies
  the passthrough and rebuild step equations.
-/

namespace Ix.Kernel.SetModel

open SetTheory
open Ix.Kernel.SetTheory.Tower
open Ix.Kernel.Term

universe w

variable {V : Type w} [SetTheory V]

/-! ## `projVal` branch equations -/

theorem projVal_of_le_one {md : Mode} {cval : Key md → (LevelParam → Nat) → V}
    {T : Key md} {i : Nat} {entry : ProjEntry md} (h : entry.off ≤ 1) (P : V) :
    projVal cval T i entry P = field (i + entry.off) P :=
  if_pos h

theorem projVal_of_gt_one {md : Mode} {cval : Key md → (LevelParam → Nat) → V}
    {T : Key md} {i : Nat} {entry : ProjEntry md} (h : ¬ entry.off ≤ 1) (P : V) :
    projVal cval T i entry P = chainApp (fun n => cval (projChainKey T i) (fun _ => n)) P :=
  if_neg h

theorem chainApp_congr {G₁ G₂ : Nat → V} {P : V} (h : ∀ n, G₁ n = G₂ n) :
    chainApp G₁ P = chainApp G₂ P := by
  have hfun : G₁ = G₂ := funext h
  rw [hfun]

/-! ## Bounded graph chains -/

/-- The restriction of `F : V → V` to arguments `x ∈ univ n` whose image also
lies in `univ n`, packaged as a Kuratowski function graph. -/
noncomputable def boundedGraph (F : V → V) (n : Nat) : V :=
  graph F (sep (univ n) (fun x => F x ∈ˢ univ n))

theorem kpair_mem_boundedGraph_iff {F : V → V} {n : Nat} {x v : V} :
    kpair x v ∈ˢ boundedGraph F n ↔ x ∈ˢ (univ n : V) ∧ F x ∈ˢ (univ n : V) ∧ v = F x := by
  unfold boundedGraph
  rw [mem_graph]
  constructor
  · rintro ⟨x', hx', hp⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    obtain ⟨h1, h2⟩ := mem_sep.mp hx'
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨hx, hFx, rfl⟩
    exact ⟨x, mem_sep.mpr ⟨hx, hFx⟩, rfl⟩

theorem boundedGraph_mem_univ (F : V → V) (n : Nat) :
    boundedGraph F n ∈ˢ (univ (n + 1) : V) := by
  have hU : IsTGUniverse (Mem (V := V)) (univ (n + 1)) :=
    univ_isTGUniverse (Nat.succ_ne_zero n)
  have hUn : (univ n : V) ∈ˢ univ (n + 1) := univ_mem_univ n
  have hDom : sep (univ n : V) (fun x => F x ∈ˢ univ n) ∈ˢ univ (n + 1) :=
    hU.sep_mem hUn
  unfold boundedGraph graph
  refine hU.image_mem hDom fun x hx => ?_
  obtain ⟨hxU, hFxU⟩ := mem_sep.mp hx
  exact hU.kpair_mem hUn (hU.transitive hUn hxU) (hU.transitive hUn hFxU)

theorem app_boundedGraph {F : V → V} {n : Nat} {x : V}
    (hx : x ∈ˢ (univ n : V)) (hFx : F x ∈ˢ (univ n : V)) :
    app (boundedGraph F n) x = F x :=
  app_graph (mem_sep.mpr ⟨hx, hFx⟩)

theorem chainApp_boundedGraph {F : V → V} {x : V}
    (h : ∃ n : Nat, x ∈ˢ (univ n : V) ∧ F x ∈ˢ (univ n : V)) :
    chainApp (boundedGraph F) x = F x := by
  obtain ⟨n₀, hx₀, hFx₀⟩ := h
  have hex : ∃ n : Nat, ∃ v : V, kpair x v ∈ˢ boundedGraph F n :=
    ⟨n₀, F x, kpair_mem_boundedGraph_iff.mpr ⟨hx₀, hFx₀, rfl⟩⟩
  unfold chainApp
  rw [dif_pos hex]
  obtain ⟨v, hv⟩ := Classical.choose_spec hex
  obtain ⟨hx', hFx', -⟩ := kpair_mem_boundedGraph_iff.mp hv
  exact app_boundedGraph hx' hFx'

theorem mem_univ_succ_of_mem_of_mem_univ {u : Nat} {A x : V}
    (hA : A ∈ˢ (univ u : V)) (hx : x ∈ˢ A) : x ∈ˢ (univ (u + 1) : V) :=
  (univ_isTGUniverse (Nat.succ_ne_zero u)).transitive (univ_subset_succ u _ hA) hx

theorem chainApp_boundedGraph_of_mem_univ {F : V → V} {u v : Nat} {A B x : V}
    (hA : A ∈ˢ (univ u : V)) (hx : x ∈ˢ A)
    (hB : B ∈ˢ (univ v : V)) (hFx : F x ∈ˢ B) :
    chainApp (boundedGraph F) x = F x := by
  have hx1 : x ∈ˢ (univ (u + 1) : V) := mem_univ_succ_of_mem_of_mem_univ hA hx
  have hFx1 : F x ∈ˢ (univ (v + 1) : V) := mem_univ_succ_of_mem_of_mem_univ hB hFx
  refine chainApp_boundedGraph ⟨Nat.max (u + 1) (v + 1), ?_, ?_⟩
  · exact univ_mono (Nat.le_max_left (u + 1) (v + 1)) _ hx1
  · exact univ_mono (Nat.le_max_right (u + 1) (v + 1)) _ hFx1

/-! ## Tree unpacking -/

/-- Rebuild a mimic container constructor's set-model value from its unpacked
field values. -/
noncomputable def rebuildCtor (kind : UnpackCtorKind) (args : List V) : V :=
  match kind with
  | .structMk => mkTower args
  | .sumMk ctorTag => inj ctorTag (mkTower (args ++ [pt]))
  | .psigmaMk =>
    match args with
    | a :: b :: _ => spair a b
    | _ => pt
  | .propMk => pt

/-- Unpack a sequence of fields from `payload` starting at index `idx`, invoking
`step` on recursive mimic fields (`true`) and passing non-recursive fields
(`false`) through unchanged. -/
noncomputable def treeUnpackFields (step : V → Option V) (payload : V) (idx : Nat) :
    List Bool → Option (List V)
  | [] => some []
  | isRec :: rest =>
    let f := projS idx payload
    match (if isRec then step f else some f), treeUnpackFields step payload (idx + 1) rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

open Classical in
/-- Finite-fuel unpacking of an `aux` value according to `spec`. -/
noncomputable def treeUnpackOpt (spec : UnpackSpec) : Nat → V → Option V
  | 0, _ => none
  | fuel + 1, x =>
    if h : ∃ j : Nat, sfst x = vnat j then
      match spec[Classical.choose h]? with
      | some (.rebuild kind recFlags) =>
        match treeUnpackFields (treeUnpackOpt spec fuel) (ssnd x) 0 recFlags with
        | some args => some (rebuildCtor kind args)
        | none => none
      | _ => some x
    else some x

open Classical in
/-- Total tree-unpacking function: the common value of `treeUnpackOpt` across
all fuels (or `x` if no fuel terminates). -/
noncomputable def treeUnpack (spec : UnpackSpec) (x : V) : V :=
  if h : ∃ n v, treeUnpackOpt spec n x = some v then
    Classical.choose (Classical.choose_spec h)
  else x

theorem treeUnpackFields_mono {s₁ s₂ : V → Option V}
    (hmono : ∀ y v, s₁ y = some v → s₂ y = some v) (payload : V) :
    ∀ (idx : Nat) (flags : List Bool) (vs : List V),
      treeUnpackFields s₁ payload idx flags = some vs →
      treeUnpackFields s₂ payload idx flags = some vs
  | _, [], _, h => h
  | idx, isRec :: rest, vs, h => by
    simp only [treeUnpackFields] at h ⊢
    cases h1 : (if isRec then s₁ (projS idx payload) else some (projS idx payload)) with
    | none => simp [h1] at h
    | some v =>
      cases h2 : treeUnpackFields s₁ payload (idx + 1) rest with
      | none => simp [h1, h2] at h
      | some vs' =>
        simp only [h1, h2, Option.some.injEq] at h
        have h1' : (if isRec then s₂ (projS idx payload) else some (projS idx payload)) = some v := by
          cases isRec
          · exact h1
          · exact hmono _ _ h1
        have h2' := treeUnpackFields_mono hmono payload (idx + 1) rest vs' h2
        simp [h1', h2', h]

theorem treeUnpackOpt_mono (spec : UnpackSpec) :
    ∀ {n m : Nat} {x v : V}, n ≤ m →
      treeUnpackOpt spec n x = some v → treeUnpackOpt spec m x = some v
  | 0, _, _, _, _, h => by simp [treeUnpackOpt] at h
  | n + 1, 0, _, _, hle, _ => absurd hle (Nat.not_succ_le_zero n)
  | n + 1, m + 1, x, v, hle, h => by
    have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
    simp only [treeUnpackOpt] at h ⊢
    split at h
    · rename_i hex
      rw [dif_pos hex]
      cases hsp : spec[Classical.choose hex]? with
      | none => simp [hsp] at h ⊢; exact h
      | some rule =>
        cases rule with
        | passthrough => simp [hsp] at h ⊢; exact h
        | rebuild kind recFlags =>
          simp only [hsp] at h ⊢
          cases hf : treeUnpackFields (treeUnpackOpt spec n) (ssnd x) 0 recFlags with
          | none => simp [hf] at h
          | some args =>
            simp only [hf, Option.some.injEq] at h
            have hf' := treeUnpackFields_mono (fun y w hw => treeUnpackOpt_mono spec hnm hw)
              (ssnd x) 0 recFlags args hf
            simp [hf', h]
    · rename_i hnex
      rw [dif_neg hnex]
      exact h

theorem treeUnpackOpt_unique {spec : UnpackSpec} {n₁ n₂ : Nat} {x v₁ v₂ : V}
    (h₁ : treeUnpackOpt spec n₁ x = some v₁) (h₂ : treeUnpackOpt spec n₂ x = some v₂) :
    v₁ = v₂ := by
  have hm₁ := treeUnpackOpt_mono spec (Nat.le_max_left n₁ n₂) h₁
  have hm₂ := treeUnpackOpt_mono spec (Nat.le_max_right n₁ n₂) h₂
  rw [hm₁] at hm₂
  exact Option.some.inj hm₂

theorem treeUnpack_of_opt {spec : UnpackSpec} {n : Nat} {x v : V}
    (h : treeUnpackOpt spec n x = some v) : treeUnpack spec x = v := by
  have hex : ∃ n v, treeUnpackOpt spec n x = some v := ⟨n, v, h⟩
  unfold treeUnpack
  rw [dif_pos hex]
  exact treeUnpackOpt_unique (Classical.choose_spec (Classical.choose_spec hex)) h

theorem treeUnpack_nil (x : V) : treeUnpack [] x = x := by
  refine treeUnpack_of_opt (n := 1) ?_
  simp only [treeUnpackOpt]
  split <;> simp

theorem choose_vnat_eq (j : Nat) (payload : V) :
    have hex : ∃ j' : Nat, sfst (inj j payload) = vnat j' := ⟨j, by rw [inj, sfst_spair]⟩
    Classical.choose hex = j := by
  intro hex
  have h1 : sfst (inj j payload) = vnat j := by rw [inj, sfst_spair]
  exact (vnat_inj (h1.symm.trans (Classical.choose_spec hex))).symm

theorem treeUnpackOpt_passthrough {spec : UnpackSpec} {j : Nat} (payload : V)
    (hsp : spec[j]? = some .passthrough ∨ spec[j]? = none) :
    treeUnpackOpt spec 1 (inj j payload) = some (inj j payload) := by
  have hex : ∃ j' : Nat, sfst (inj j payload) = vnat j' := ⟨j, by rw [inj, sfst_spair]⟩
  simp only [treeUnpackOpt, dif_pos hex]
  rw [choose_vnat_eq j payload]
  rcases hsp with h | h <;> simp [h]

theorem treeUnpack_passthrough {spec : UnpackSpec} {j : Nat} (payload : V)
    (hsp : spec[j]? = some .passthrough ∨ spec[j]? = none) :
    treeUnpack spec (inj j payload) = inj j payload :=
  treeUnpack_of_opt (treeUnpackOpt_passthrough payload hsp)

theorem treeUnpackFields_exists (spec : UnpackSpec) (payload : V) :
    ∀ (flags : List Bool) (idx : Nat),
      (∀ k (hk : k < flags.length), flags[k] = true →
        ∃ n v, treeUnpackOpt spec n (projS (idx + k) payload) = some v) →
      ∃ N, treeUnpackFields (treeUnpackOpt spec N) payload idx flags =
        some ((List.range flags.length).map fun k =>
          if flags.getD k false then treeUnpack spec (projS (idx + k) payload)
          else projS (idx + k) payload)
  | [], idx, _ => ⟨0, rfl⟩
  | isRec :: rest, idx, hall => by
    have hrest : ∀ k (hk : k < rest.length), rest[k] = true →
        ∃ n v, treeUnpackOpt spec n (projS ((idx + 1) + k) payload) = some v := by
      intro k hk htrue
      have hk' : k + 1 < (isRec :: rest).length := Nat.succ_lt_succ hk
      have harg := hall (k + 1) hk' htrue
      have heq : idx + (k + 1) = (idx + 1) + k := by omega
      rwa [heq] at harg
    obtain ⟨N₂, hN₂⟩ := treeUnpackFields_exists spec payload rest (idx + 1) hrest
    cases isRec with
    | false =>
      refine ⟨N₂, ?_⟩
      simp only [treeUnpackFields, Bool.false_eq_true, ↓reduceIte, hN₂]
      congr 1
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte, List.cons.injEq,
        true_and]
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_def, List.getD_cons_succ]
      have heq : idx + (k + 1) = (idx + 1) + k := by omega
      rw [heq]
    | true =>
      obtain ⟨n₀, v₀, hv₀⟩ := hall 0 (Nat.zero_lt_succ _) rfl
      rw [Nat.add_zero] at hv₀
      have hv₀_eq : v₀ = treeUnpack spec (projS idx payload) := (treeUnpack_of_opt hv₀).symm
      refine ⟨Nat.max n₀ N₂, ?_⟩
      have hv₀' : treeUnpackOpt spec (Nat.max n₀ N₂) (projS idx payload) = some v₀ :=
        treeUnpackOpt_mono spec (Nat.le_max_left n₀ N₂) hv₀
      have hN₂' := treeUnpackFields_mono
        (fun y w hw => treeUnpackOpt_mono spec (Nat.le_max_right n₀ N₂) hw)
        payload (idx + 1) rest _ hN₂
      simp only [treeUnpackFields, ↓reduceIte, hv₀', hN₂', hv₀_eq]
      congr 1
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, List.getD_cons_zero, ↓reduceIte, List.cons.injEq, true_and]
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_def, List.getD_cons_succ]
      have heq : idx + (k + 1) = (idx + 1) + k := by omega
      rw [heq]

theorem treeUnpackOpt_rebuild {spec : UnpackSpec} {j : Nat} {kind : UnpackCtorKind}
    {recFlags : List Bool} (payload : V)
    (hsp : spec[j]? = some (.rebuild kind recFlags))
    (hall : ∀ k (hk : k < recFlags.length), recFlags[k] = true →
      ∃ n v, treeUnpackOpt spec n (projS k payload) = some v) :
    ∃ N, treeUnpackOpt spec (N + 1) (inj j payload) =
      some (rebuildCtor kind ((List.range recFlags.length).map fun k =>
        if recFlags.getD k false then treeUnpack spec (projS k payload)
        else projS k payload)) := by
  have hall0 : ∀ k (hk : k < recFlags.length), recFlags[k] = true →
      ∃ n v, treeUnpackOpt spec n (projS (0 + k) payload) = some v := by
    intro k hk ht; rw [Nat.zero_add]; exact hall k hk ht
  obtain ⟨N, hN⟩ := treeUnpackFields_exists spec payload recFlags 0 hall0
  refine ⟨N, ?_⟩
  have hex : ∃ j' : Nat, sfst (inj j payload) = vnat j' := ⟨j, by rw [inj, sfst_spair]⟩
  simp only [treeUnpackOpt, dif_pos hex]
  rw [choose_vnat_eq j payload, hsp]
  dsimp only
  rw [inj, ssnd_spair]
  simp only [Nat.zero_add] at hN
  rw [hN]

theorem treeUnpack_rebuild {spec : UnpackSpec} {j : Nat} {kind : UnpackCtorKind}
    {recFlags : List Bool} (payload : V)
    (hsp : spec[j]? = some (.rebuild kind recFlags))
    (hall : ∀ k (hk : k < recFlags.length), recFlags[k] = true →
      ∃ n v, treeUnpackOpt spec n (projS k payload) = some v) :
    treeUnpack spec (inj j payload) =
      rebuildCtor kind ((List.range recFlags.length).map fun k =>
        if recFlags.getD k false then treeUnpack spec (projS k payload)
        else projS k payload) := by
  obtain ⟨N, hN⟩ := treeUnpackOpt_rebuild payload hsp hall
  exact treeUnpack_of_opt hN

end Ix.Kernel.SetModel
