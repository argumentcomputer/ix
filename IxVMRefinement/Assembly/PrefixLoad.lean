import IxVMRefinement.Assembly.ReadBare
import IxVMRefinement.Core.Good
import IxVMRefinement.L1.Records
import IxC.Ixon.Verify.Framing
import Ix.IxVM.Consistency.Restrict

/-! # Collision lifting, `L1.EnvDecoded` on sub-stores, and prefix `Installs` helpers

Connects the walked sub-environment `subEnv E₀ Keep supp` (`Assembly.Closure`) and prefix
environments built by `IxVM.Consistency.Installs` to the `L1` / `Core` / `L5` hypotheses:

* `hashedCollision_subEnv_to_view`, `good_subEnv_of_noCollision`, `good_subEnv_of_hashed_supp`,
  and `good_walkedSubEnv_of_noCollision`: lift `View.HashedCollision { env := subEnv E₀ Keep supp }
  [] calls` to `V.HashedCollision extra calls`, discharging `Core.Good` on any `Ctx` backed by
  `subEnv E₀ Keep supp`;
* `subEnv_envDecoded`, `subEnv_envDecoded_of_serConstant`, and `subEnv_envDecoded_of_walkedL6`:
  establish `L1.EnvDecoded (subEnv E₀ Keep supp)` from `WalkedL6` and exact/serialized supplements;
* `installs_consts_origin`, `installs_find?_none_of_not_installed`, `installs_prefix_fresh`, and
  `installs_prefix_stored`: characterize every constant in an `Installs` prefix as either declared
  by an earlier declaration or auxiliary (`Key.aux`), discharging `InstallStep` freshness and
  `Nodup` obligations along the declaration fold. -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-! ## Lifting `View.HashedCollision` from `subEnv E₀ Keep supp` to `V.HashedCollision extra calls` -/

/-- Every preimage held by `{ env := subEnv E₀ Keep supp }` is either held by `V`, hashed in
`calls`, or drawn from a non-padding entry in `extra`. -/
theorem subEnv_preimage_to_view {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    {x : _root_.Address} {held : ByteArray}
    (hpre : ({ env := subEnv E₀ Keep supp } : IxVM.Refinement.View).Preimage x held) :
    V.Preimage x held ∨
      (IxVM.Refinement.Hashed calls held ∧ _root_.Address.blake3Pure held = x) ∨
      (held ∈ extra ∧ _root_.Address.blake3Pure held = x ∧
        x ≠ Ix.HostAdmission.Merkle.padding) := by
  rcases hpre with ⟨lc, hget, rfl⟩ | hblob | ⟨rb, hrb, -, -⟩ | ⟨t, ht, -, -⟩
  · rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨_, raw, c, hm, rfl⟩
    · exact Or.inr (Or.inl (hload.1 x lc hget₀))
    · simp only [Claim.mkLazy_rawBytes]
      obtain ⟨hblk, hsrc⟩ := hsupp x raw c hm
      rcases hsrc with hv | hh | ⟨hex, hne⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl ⟨hh, hblk⟩)
      · exact Or.inr (Or.inr ⟨hex, hblk, hne⟩)
  · exact Or.inr (Or.inl (hload.2 x held hblob))
  · cases hrb
  · cases ht

/-- **Collision lifting**: any `HashedCollision` against `{ env := subEnv E₀ Keep supp }` lifts to
`V.HashedCollision extra calls`. -/
theorem hashedCollision_subEnv_to_view {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hcol : IxVM.Refinement.View.HashedCollision { env := subEnv E₀ Keep supp } [] calls) :
    V.HashedCollision extra calls := by
  rcases hcol with ⟨x, held, bytes, hsrc, hh, hne, hblk⟩ | ⟨bytes, hsrc, hpad⟩
  · refine Or.inl ⟨x, held, bytes, ?_, hh, hne, hblk⟩
    rcases hsrc with hpre | ⟨hmem, -⟩ | hh_held
    · rcases subEnv_preimage_to_view hload hsupp hpre with hv | hh' | ⟨hex, hblk_held, -⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inr hh')
      · exact Or.inr (Or.inl ⟨hex, hblk_held⟩)
    · cases hmem
    · exact Or.inr (Or.inr hh_held)
  · rcases hsrc with hpre | hh
    · rcases subEnv_preimage_to_view hload hsupp hpre with hv | ⟨hh', -⟩ | ⟨-, -, hne⟩
      · exact Or.inr ⟨bytes, Or.inl hv, hpad⟩
      · exact Or.inr ⟨bytes, Or.inr hh', hpad⟩
      · exact absurd rfl hne
    · exact Or.inr ⟨bytes, Or.inr hh, hpad⟩

/-- **`Core.Good` on `subEnv E₀ Keep supp`** from `¬ V.HashedCollision extra calls` and
`Bounded calls`. -/
theorem good_subEnv_of_noCollision {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hno : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨subEnv E₀ Keep supp, env, t, lim⟩ calls :=
  ⟨fun hcol => hno (hashedCollision_subEnv_to_view hload hsupp hcol), hbound⟩

/-- `Core.Good` on `subEnv E₀ Keep supp` when every supplement entry was hashed in `calls`. -/
theorem good_subEnv_of_hashed_supp {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧ IxVM.Refinement.Hashed calls raw)
    (hno : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨subEnv E₀ Keep supp, env, t, lim⟩ calls :=
  good_subEnv_of_noCollision env t lim hload
    (fun a raw c hm =>
      let ⟨hblk, hh⟩ := hsupp a raw c hm
      ⟨hblk, Or.inr (Or.inl hh)⟩)
    hno hbound

/-- `Core.Good` on the pure walked sub-environment `subEnv E₀ Keep []`. -/
theorem good_walkedSubEnv_of_noCollision {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hno : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨subEnv E₀ Keep [], env, t, lim⟩ calls :=
  good_subEnv_of_hashed_supp env t lim hload (fun _ _ _ hm => nomatch hm) hno hbound

/-! ## `L1.EnvDecoded` on `subEnv E₀ Keep supp` -/

/-- **`L1.EnvDecoded (subEnv E₀ Keep supp)`** from exact decoding on `E₀` and on `supp`. -/
theorem subEnv_envDecoded {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp → Ixon.deConstantExact raw = .ok c) :
    L1.EnvDecoded (subEnv E₀ Keep supp) := by
  intro x lc hget
  rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨_, raw, c, hm, rfl⟩
  · exact hexact₀ x lc hget₀
  · exact ⟨c, rfl, by simpa only [Claim.mkLazy_rawBytes] using hsupp x raw c hm⟩

/-- `L1.EnvDecoded (subEnv E₀ Keep supp)` when each supplement entry's bytes are `Ixon.serConstant c`
for a wire-well-formed constant `c`. -/
theorem subEnv_envDecoded_of_serConstant {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry}
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp → raw = Ixon.serConstant c ∧ c.wireWF) :
    L1.EnvDecoded (subEnv E₀ Keep supp) :=
  subEnv_envDecoded hexact₀ fun a raw c hm => by
    obtain ⟨rfl, hwf⟩ := hsupp a raw c hm
    exact Ixon.Verify.deConstantExact_serConstant c hwf

/-- **`L1.EnvDecoded (subEnv E₀ Keep supp)`** directly from `Claim.WalkedL6` and exact-decoded
supplements. -/
theorem subEnv_envDecoded_of_walkedL6 {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (Keep : _root_.Address → Prop) {supp : List SuppEntry}
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp → Ixon.deConstantExact raw = .ok c) :
    L1.EnvDecoded (subEnv E₀ Keep supp) := by
  obtain ⟨_, _, _, hdec₀, _, _, _, _, _, _, _⟩ := hwalk
  exact subEnv_envDecoded
    (fun a lc hget =>
      let ⟨_, c, hc, _, hex⟩ := hdec₀ a lc hget
      ⟨c, hc, hex⟩)
    hsupp

/-! ## Prefix `Installs` origin, freshness, `Nodup`, and lookup helpers -/

/-- Every constant stored in an `Installs ds env` environment either shares its name with some
constant declared by a declaration in `ds`, or sits at an auxiliary key (`Key.aux`). -/
theorem installs_consts_origin {ds : List (Ix.Kernel.Declaration .anon)}
    {env : Ix.Kernel.Env .anon} (h : IxVM.Consistency.Installs ds env) :
    ∀ ci ∈ env.consts,
      (∃ d ∈ ds, ∃ ci₀ ∈ IxVM.Consistency.installs d, ci.name = ci₀.name) ∨
        ∃ b s, ci.name = .aux b s := by
  induction h with
  | nil => intro _ hm; nomatch hm
  | @snoc ds₀ d env₀ env₂ _ hstep ih =>
    obtain ⟨new, rfl, -, -, -, horig⟩ := hstep
    intro ci hmem
    rcases List.mem_append.mp hmem with hnew | hold
    · rcases horig ci hnew with ⟨ci₀, hci₀, hname⟩ | haux
      · exact Or.inl ⟨d, List.mem_append_right _ (List.mem_singleton.mpr rfl),
          ci₀, hci₀, hname.symm⟩
      · exact Or.inr haux
    · rcases ih ci hold with ⟨d₀, hd₀, ci₀, hci₀, hname⟩ | haux
      · exact Or.inl ⟨d₀, List.mem_append_left _ hd₀, ci₀, hci₀, hname⟩
      · exact Or.inr haux

/-- A non-auxiliary key `k` not declared by any declaration in `ds_pre` is absent (`find? = none`)
from any `Installs ds_pre env_pre` environment. -/
theorem installs_find?_none_of_not_installed {ds_pre : List (Ix.Kernel.Declaration .anon)}
    {env_pre : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    (h : IxVM.Consistency.Installs ds_pre env_pre)
    (hna : NonAuxKey k)
    (hnot : ∀ d₀ ∈ ds_pre, ∀ ci₀ ∈ IxVM.Consistency.installs d₀, ci₀.name ≠ k) :
    env_pre.find? k = none := by
  cases hfind : env_pre.find? k with
  | none => rfl
  | some ci =>
    have hmem := Ix.Kernel.Semantics.Env.find?_mem hfind
    have hname := Ix.Kernel.Semantics.Env.find?_name hfind
    rcases installs_consts_origin h ci hmem with ⟨d₀, hd₀, ci₀, hci₀, hci_eq⟩ | ⟨b, s, haux⟩
    · exact absurd (hci_eq.symm.trans hname) (hnot d₀ hd₀ ci₀ hci₀)
    · exact absurd (hname.symm.trans haux) (hna b s)

/-- Prefix freshness and `Nodup` for a `DeclNonAux` declaration `d` whose installed names do not
appear in any earlier declaration of `ds_pre`. -/
theorem installs_prefix_fresh {ds_pre : List (Ix.Kernel.Declaration .anon)}
    {env_pre : Ix.Kernel.Env .anon} {d : Ix.Kernel.Declaration .anon}
    (h : IxVM.Consistency.Installs ds_pre env_pre)
    (hd : DeclNonAux d)
    (hdisj : ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∀ d₀ ∈ ds_pre, ∀ ci₁ ∈ IxVM.Consistency.installs d₀, ci₁.name ≠ ci₀.name) :
    (∀ ci₀ ∈ IxVM.Consistency.installs d, env_pre.find? ci₀.name = none) ∧
      ((IxVM.Consistency.installs d).map (·.name)).Nodup :=
  ⟨fun ci₀ hci₀ =>
    installs_find?_none_of_not_installed h (hd.1 ci₀ hci₀).1 (hdisj ci₀ hci₀),
   hd.2⟩

/-- Every constant declared by an earlier declaration `d₀ ∈ ds_pre` is already stored (`StoredAs`)
in `env_pre`. -/
theorem installs_prefix_stored {ds_pre : List (Ix.Kernel.Declaration .anon)}
    {env_pre : Ix.Kernel.Env .anon} {d₀ : Ix.Kernel.Declaration .anon}
    {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : IxVM.Consistency.Installs ds_pre env_pre)
    (hd₀ : d₀ ∈ ds_pre) (hci₀ : ci₀ ∈ IxVM.Consistency.installs d₀) :
    ∃ ci, env_pre.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀ :=
  h.stored hd₀ hci₀

end IxVM.Refinement.Assembly
