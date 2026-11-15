import Ix.IxVM.Consistency.Statement

/-! # Grouping generated auxiliary declarations into their public install step

An inductive reader may emit auxiliary model declarations before the declaration of the
inductive family. Grouping those auxiliary installs preserves the complete installed environment.
-/

namespace IxVM.Refinement.Assembly

/-- Every constant declared by `d` has an `.aux` key (e.g. generated inductive model declarations
in `prepareWith`). -/
def DeclAllAux (d : Ix.Kernel.Declaration .anon) : Prop :=
  ∀ ci₀ ∈ IxVM.Consistency.installs d, ∃ k t, ci₀.name = .aux k t

private theorem list_find?_append_none :
    ∀ {xs ys : List (Ix.Kernel.ConstantInfo .anon)} {n : Ix.Kernel.Key .anon},
      (xs ++ ys).find? (·.name == n) = none →
      (∀ ci ∈ xs, ci.name ≠ n) ∧ ys.find? (·.name == n) = none
  | [], _, _, h => ⟨fun _ hm => (nomatch hm), h⟩
  | x :: xs, ys, n, h => by
    simp only [List.cons_append, List.find?_cons] at h
    cases hxn : x.name == n with
    | true => rw [hxn] at h; cases h
    | false =>
      rw [hxn] at h
      obtain ⟨hxs, hys⟩ := list_find?_append_none h
      refine ⟨fun ci hci => ?_, hys⟩
      rcases List.mem_cons.mp hci with rfl | hci'
      · exact fun heq => absurd (beq_iff_eq.mpr heq) (by rw [hxn]; decide)
      · exact hxs ci hci'

private theorem nodup_map_append {α β : Type _} {f : α → β} :
    ∀ {xs ys : List α},
      (xs.map f).Nodup → (ys.map f).Nodup →
      (∀ x ∈ xs, ∀ y ∈ ys, f x ≠ f y) →
      ((xs ++ ys).map f).Nodup
  | [], _, _, hnd_y, _ => hnd_y
  | x :: xs, ys, hnd_x, hnd_y, hdisj => by
    simp only [List.cons_append, List.map_cons, List.nodup_cons] at hnd_x ⊢
    refine ⟨fun hmem => ?_,
      nodup_map_append hnd_x.2 hnd_y (fun x' hx' y hy => hdisj x' (List.mem_cons_of_mem x hx') y hy)⟩
    rw [List.map_append, List.mem_append] at hmem
    rcases hmem with hmem_x | hmem_y
    · exact hnd_x.1 hmem_x
    · obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem_y
      exact hdisj x List.mem_cons_self y hy hfy.symm

/-- **Unconditional `.aux` absorption in `InstallStep`**: an auxiliary declaration `d_aux`
installed immediately before `d` merges directly into `d`'s `InstallStep`, because
`IxVM.Consistency.InstallStep` permits arbitrary `.aux`-named constants alongside `installs d`. -/
theorem installStep_absorb_aux_left
    {env₀ env₁ env₂ : Ix.Kernel.Env .anon}
    {d_aux d : Ix.Kernel.Declaration .anon}
    (haux : DeclAllAux d_aux)
    (hstep₁ : IxVM.Consistency.InstallStep env₀ d_aux env₁)
    (hstep₂ : IxVM.Consistency.InstallStep env₁ d env₂) :
    IxVM.Consistency.InstallStep env₀ d env₂ := by
  obtain ⟨new₁, rfl, hnd₁, hnone₁, _, hshape₁⟩ := hstep₁
  obtain ⟨new₂, rfl, hnd₂, hnone₂, hinst₂, hshape₂⟩ := hstep₂
  refine ⟨new₂ ++ new₁, congrArg Ix.Kernel.Env.mk (List.append_assoc new₂ new₁ env₀.consts).symm,
    ?_, ?_, ?_, ?_⟩
  · apply nodup_map_append hnd₂ hnd₁
    intro ci₂ hci₂ ci₁ hci₁ heq
    have hsplit := list_find?_append_none (hnone₂ ci₂ hci₂)
    exact hsplit.1 ci₁ hci₁ heq.symm
  · intro ci hci
    rcases List.mem_append.mp hci with hci₂ | hci₁
    · exact (list_find?_append_none (hnone₂ ci hci₂)).2
    · exact hnone₁ ci hci₁
  · intro ci₀ hci₀
    obtain ⟨ci, hci, hst⟩ := hinst₂ ci₀ hci₀
    exact ⟨ci, List.mem_append_left _ hci, hst⟩
  · intro ci hci
    rcases List.mem_append.mp hci with hci₂ | hci₁
    · exact hshape₂ ci hci₂
    · rcases hshape₁ ci hci₁ with ⟨ci₀, hci₀, hname⟩ | hkt
      · obtain ⟨k, t, hk⟩ := haux ci₀ hci₀
        exact Or.inr ⟨k, t, hname.symm.trans hk⟩
      · exact Or.inr hkt

private theorem snoc_inj {α : Type _} :
    ∀ {xs ys : List α} {x y : α}, xs ++ [x] = ys ++ [y] → xs = ys ∧ x = y
  | [], [], x, y, h => by
    simp only [List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨rfl, h⟩
  | [], y₀ :: ys, x, y, h => by
    cases ys with
    | nil => simp at h
    | cons _ _ => simp at h
  | x₀ :: xs, [], x, y, h => by
    cases xs with
    | nil => simp at h
    | cons _ _ => simp at h
  | x₀ :: xs, y₀ :: ys, x, y, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hpre, hxy⟩ := snoc_inj h.2
    exact ⟨congrArg₂ List.cons h.1 hpre, hxy⟩

theorem installs_snoc_inv {ds : List (Ix.Kernel.Declaration .anon)}
    {d : Ix.Kernel.Declaration .anon} {env₂ : Ix.Kernel.Env .anon}
    (h : IxVM.Consistency.Installs (ds ++ [d]) env₂) :
    ∃ env₁, IxVM.Consistency.Installs ds env₁ ∧ IxVM.Consistency.InstallStep env₁ d env₂ := by
  generalize h_eq : ds ++ [d] = full at h
  cases h with
  | nil => simp at h_eq
  | snoc hpre hstep =>
    obtain ⟨rfl, rfl⟩ := snoc_inj h_eq
    exact ⟨_, hpre, hstep⟩

/-- **Unconditional `.aux`-block grouping for `Installs`**: any run of auxiliary model
declarations `auxs` emitted immediately before a bare declaration `d` (such as
`[aux₁, …, auxₖ, .indDecl …]` in `prepareWith`) collapses into `d`'s single `InstallStep`,
yielding `IxVM.Consistency.Installs (ds ++ [d]) env₂`. -/
theorem installs_absorb_aux_block :
    ∀ (auxs : List (Ix.Kernel.Declaration .anon))
      {ds : List (Ix.Kernel.Declaration .anon)}
      {d : Ix.Kernel.Declaration .anon} {env₂ : Ix.Kernel.Env .anon},
      (∀ d_a ∈ auxs, DeclAllAux d_a) →
      IxVM.Consistency.Installs ((ds ++ auxs) ++ [d]) env₂ →
      IxVM.Consistency.Installs (ds ++ [d]) env₂
  | [], _, _, _, _, h => by simpa using h
  | a :: rest, ds, d, env₂, haux, h => by
    have h_assoc : ((ds ++ [a]) ++ rest) ++ [d] = (ds ++ (a :: rest)) ++ [d] := by
      simp [List.append_assoc]
    have h_mid : IxVM.Consistency.Installs ((ds ++ [a]) ++ [d]) env₂ :=
      installs_absorb_aux_block rest
        (fun d_a hd => haux d_a (List.mem_cons_of_mem a hd))
        (by rw [h_assoc]; exact h)
    obtain ⟨env₁, h₁, hstep_d⟩ := installs_snoc_inv h_mid
    obtain ⟨env₀, h₀, hstep_a⟩ := installs_snoc_inv h₁
    exact .snoc h₀ (installStep_absorb_aux_left (haux a List.mem_cons_self) hstep_a hstep_d)

/-- Each public declaration follows its own block of generated auxiliary declarations. -/
inductive AuxGrouped : List (Ix.Kernel.Declaration .anon) →
    List (Ix.Kernel.Declaration .anon) → Prop where
  | nil : AuxGrouped [] []
  | snoc {full bare : List (Ix.Kernel.Declaration .anon)}
      (prior : AuxGrouped full bare) (auxs : List (Ix.Kernel.Declaration .anon))
      (d : Ix.Kernel.Declaration .anon) (auxiliary : ∀ a ∈ auxs, DeclAllAux a) :
      AuxGrouped ((full ++ auxs) ++ [d]) (bare ++ [d])

theorem AuxGrouped.refl (ds : List (Ix.Kernel.Declaration .anon)) : AuxGrouped ds ds := by
  induction ds using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton ds d ih =>
    simpa using AuxGrouped.snoc ih [] d (by simp)

theorem AuxGrouped.append {full₁ bare₁ full₂ bare₂ : List (Ix.Kernel.Declaration .anon)}
    (h₁ : AuxGrouped full₁ bare₁) (h₂ : AuxGrouped full₂ bare₂) :
    AuxGrouped (full₁ ++ full₂) (bare₁ ++ bare₂) := by
  induction h₂ with
  | nil => simpa using h₁
  | snoc _prior auxs d haux ih =>
    simpa [List.append_assoc] using AuxGrouped.snoc ih auxs d haux

/-- Auxiliary grouping preserves the final environment, including its model artifacts. -/
theorem AuxGrouped.installs {full bare : List (Ix.Kernel.Declaration .anon)}
    (hgroup : AuxGrouped full bare) {env : Ix.Kernel.Env .anon}
    (hinst : IxVM.Consistency.Installs full env) : IxVM.Consistency.Installs bare env := by
  induction hgroup generalizing env with
  | nil => exact hinst
  | snoc _prior auxs d haux ih =>
    obtain ⟨env₀, hpre, hstep⟩ := installs_snoc_inv (installs_absorb_aux_block auxs haux hinst)
    exact .snoc (ih hpre) hstep

end IxVM.Refinement.Assembly
