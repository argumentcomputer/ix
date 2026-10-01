module

import ConLeche.Semantics.DeclIndRun
public import ConLeche.Model.ProjInstall
public section

/-!
# The modeled-inductive block, assembled at the reading (task #161,
IND TIER part 10)

`declIndS`'s twin, and the ind tier's summit: the four phases compose
at the P tier exactly as they do at v1's.

* `indMembersPM` — the non-recursor members (part 2);
* `indRecs` — the recursor group, provision/fire/swap (part 10);
* `projInstall` — the projection functions (part 10);

**Everything between them is v1's bookkeeping, unchanged**: the block
split, the freshness chains, `EtaPins.transport`, the `hidR`
identification of the stored former.  Only two facts are genuinely new,
and both are the annotated half of a v1 predicate the phases already
carry: `BlockAcvalInstalled` (vacuous at the base, for the same reason
`BlockInstalledTT` is — no block name is stored before the fold runs)
and `ProjPhaseAcval` at the group's output (its first two conjuncts
are `BlockAcvalInstalled` at `T` and at the constructor; its third is
vacuous, the projection slots being fresh there).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName projModelName Declaration)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

set_option maxHeartbeats 3200000 in
/-- **The modeled-inductive block install, P tier.**  The v1 carriers
are taken from the v1 phases (`indRecsS` at the group), which the
install runs anyway; the P phases carry the annotated invariants. -/
theorem declInd (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env)
    (h : DeclIndRun μ F env block env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  obtain ⟨hsplit, hmain⟩ := h
  -- list bookkeeping about the block's split (v1's, verbatim)
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => false | _ => true),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hEC0 : ConLeche.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hnostore : ∀ {caps : IndCaps} {envM envR : Env},
      IndMembersRun μ F (block.map (·.name)) caps env
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM →
      IndRecsRun μ F (block.map (·.name)) envM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR →
      ∀ n, (block.map (·.name)).contains n = true →
        ∀ ci : ConstantInfo, env.find? n = some ci → False := by
    intro caps envM envR hmem hrecs n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersRun_mono _ hmem _ _ hf
      rw [indRecsRun_fresh hrecs ci₀ hci₀] at hup
      exact nomatch hup
  have hI0gen : ∀ {caps : IndCaps} {envM envR : Env},
      IndMembersRun μ F (block.map (·.name)) caps env
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM →
      IndRecsRun μ F (block.map (·.name)) envM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR →
      BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun hmem hrecs n hn ci hf =>
      absurd (hnostore hmem hrecs n hn ci hf) (fun h => h)
  -- the annotated half, vacuous at the base for the same reason
  have hIA0gen : ∀ {caps : IndCaps} {envM envR : Env},
      IndMembersRun μ F (block.map (·.name)) caps env
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM →
      IndRecsRun μ F (block.map (·.name)) envM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR →
      BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun hmem hrecs n hn ci hf =>
      absurd (hnostore hmem hrecs n hn ci hf) (fun h => h)
  have hallGen : ∀ {caps : IndCaps} {envM : Env},
      IndMembersRun μ F (block.map (·.name)) caps env
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM →
      ∀ n, (block.map (·.name)).contains n = true →
        (envM.find? n).isSome = true ∨
        ∃ ci ∈ block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
    intro caps envM hmem n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersRun_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  rcases hmain with ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, harm⟩ |
    ⟨-, envM, hmem, hrecs⟩
  · -- the single-constructor arm
    obtain ⟨envM, envR, hmem, hrecs, -, hprojFresh, hproj⟩ := harm
    have hmemFil : ∀ {p : ConstantInfo → Bool} {x : ConstantInfo},
        block.filter p = [x] → x ∈ block := by
      intro p x hfil
      have hx : x ∈ block.filter p := by
        rw [hfil]; exact List.mem_singleton_self _
      exact (List.mem_filter.mp hx).1
    have hsingle : ∀ {p : ConstantInfo → Bool} {x y : ConstantInfo},
        block.filter p = [x] → y ∈ block → p y = true → y = x := by
      intro p x y hfil hy hpy
      have hx : y ∈ block.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
      rw [hfil, List.mem_singleton] at hx
      exact hx
    have hTin : ConstantInfo.indInfo cvT capsT ∈ block :=
      hmemFil hIfilt
    have hCin : ConstantInfo.ctorInfo cvC nP nF ∈ block :=
      hmemFil hCfilt
    have hTnon : ConstantInfo.indInfo cvT capsT ∈ block.filter
        (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true) :=
      List.mem_filter.mpr ⟨hTin, rfl⟩
    have hTblock : (block.map (·.name)).contains cvT.name = true :=
      hbnAll _ hTin
    have hCblockN : (block.map (·.name)).contains cvC.name = true :=
      hbnAll _ hCin
    have hbshape : ∀ n, (block.map (·.name)).contains n = true →
        n.isProjFnShape = false := by
      intro n hn
      have hmm : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hx | hx
      · exact (indMembersRun_nameGuards _ hmem ci₀ hx).1
      · exact (indRecsRun_nameGuards hrecs ci₀ hx).1
    have hTnres : ConLeche.reservedBasisNames.contains cvT.name = false :=
      (indMembersRun_nameGuards _ hmem _ hTnon).2
    -- **the group's keep-fact, off the run record** (task #161 S11b):
    -- `indRecsRun_keep` is strictly stronger than the `hnonrecUp` the
    -- carrier-building `indRecsCoreR` used to report — an equation, no
    -- "not a recursor" side condition — so the ind tier's P summit no
    -- longer runs a second, model-free *install* for it.
    have hkeepR : ∀ (n : Name) (ci : ConstantInfo),
        env.find? n = some ci → envR.find? n = some ci :=
      fun n ci hf => indRecsRun_keep hrecs n ci
        (indMembersRun_mono _ hmem n ci hf)
    have hmonoR : ∀ n, (env.find? n).isSome = true →
        (envR.find? n).isSome = true := by
      intro n hn
      rcases hf : env.find? n with _ | ci
      · rw [hf] at hn; exact nomatch hn
      · rw [hkeepR n ci hf]; rfl
    have hpf0 : 0 < nF → env.find? (projFnName cvT.name 0) = none := by
      intro h0
      have hnone := List.all_eq_true.mp hprojFresh 0
        (List.mem_range.mpr h0)
      rcases hf : env.find? (projFnName cvT.name 0) with _ | ci
      · rfl
      · exfalso
        have hs := hmonoR _ (by rw [hf]; rfl)
        rcases hfR : envR.find? (projFnName cvT.name 0) with _ | ci'
        · rw [hfR] at hs; exact nomatch hs
        · rw [hfR] at hnone; exact nomatch hnone
    have hBP0 : ConLeche.BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    -- the member fold, both tiers
    obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
      indMembersPM memberEtaLaw memberUnitLaw _ mp hbnNon
        (fun cv caps₂ hmm => by
          obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
            (hsingle hIfilt (List.mem_filter.mp hmm).1 rfl)
          exact ⟨etaPins_of_indBlockCaps, fun _ => hCblockN,
            fun _ h0 => hpf0 h0⟩)
        hmem (hI0gen hmem hrecs) (hIA0gen hmem hrecs) hEC0 hBP0
    -- the recursor group
    obtain ⟨mp₂, hI₂, hIA₂⟩ :=
      indRecs hμ memberEtaLaw memberUnitLaw mp₁ hI₁ hIA₁
        hbnRec (hallGen hmem) hEC₁ hBP₁ hrecs
    -- the stored former, identified (v1's argument, verbatim)
    have hidR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        cvT'.levelParams = cvT.levelParams ∧
        capsT' = indBlockCaps μ env cvT cvC nP nF := by
      intro cvT' capsT' hf
      obtain ⟨cvA, hnameA, hlpsA, hfM⟩ :=
        indMembersRun_indEntry _ hmem cvT capsT hTnon
      have hfR := indRecsRun_keep hrecs cvT.name
        (.indInfo cvA (indBlockCaps μ env cvT cvC nP nF)) hfM
      rw [hf] at hfR
      obtain ⟨h1, h2⟩ :=
        ConstantInfo.indInfo.inj (Option.some.inj hfR)
      exact ⟨by rw [h1]; exact hlpsA, h2⟩
    -- the projection phase's block-level premises, both tiers
    have hinvR : ProjPhaseInvS cvT.name cvC.name nF envR
        mp₂.base2.cvalE := by
      refine ⟨?_, ?_, ?_⟩
      · intro ci hf
        obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
          hI₂ cvT.name hTblock ci hf
        exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
      · intro ci hf
        obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
          hI₂ cvC.name hCblockN ci hf
        exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
      · intro j hj ci hf
        exfalso
        have hnone := List.all_eq_true.mp hprojFresh j
          (List.mem_range.mpr hj)
        rw [hf] at hnone
        exact nomatch hnone
    have hinvAR : ProjPhaseAcval cvT.name cvC.name nF envR
        mp₂.base2.acval := by
      refine ⟨?_, ?_, ?_⟩
      · intro hs ψ
        rcases hf : envR.find? cvT.name with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · exact (hIA₂ cvT.name hTblock ci hf ψ).symm
      · intro hs ψ
        rcases hf : envR.find? cvC.name with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · exact (hIA₂ cvC.name hCblockN ci hf ψ).symm
      · intro j hj hs ψ
        exfalso
        have hnone := List.all_eq_true.mp hprojFresh j
          (List.mem_range.mpr hj)
        rcases hf : envR.find? (projFnName cvT.name j) with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · rw [hf] at hnone; exact nomatch hnone
    have hpinsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        ConLeche.EtaPins μ envR cvT.name cvT'.levelParams capsT' := by
      intro cvT' capsT' hf
      obtain ⟨hlps', rfl⟩ := hidR cvT' capsT' hf
      rw [hlps']
      exact ConLeche.EtaPins.transport etaPins_of_indBlockCaps
        (fun n ci hf' _ => hkeepR n ci hf')
    have hCblockR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        capsT'.eta = true →
        (block.map (·.name)).contains capsT'.etaCtor = true := by
      intro cvT' capsT' hf _
      obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
      exact hCblockN
    have hFieldsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        capsT'.eta = true → capsT'.etaFields = nF := by
      intro cvT' capsT' hf _
      obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
      rfl
    -- the projection fold
    obtain ⟨mp₃, -, -, -, -⟩ :=
      projInstall hμ hTblock hbshape _ mp₂ hproj hinvR
        hinvAR hI₂ hIA₂ hpinsR hCblockR hFieldsR
    exact ⟨mp₃⟩
  · -- the generic arm: an empty capability record
    have hBP0 : ConLeche.BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
      indMembersPM memberEtaLaw memberUnitLaw _ mp hbnNon
        (fun cv caps₂ _ => ⟨etaPins_empty,
          ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
        hmem (hI0gen hmem hrecs) (hIA0gen hmem hrecs) hEC0 hBP0
    obtain ⟨mp₂, -, -⟩ :=
      indRecs hμ memberEtaLaw memberUnitLaw mp₁ hI₁ hIA₁
        hbnRec (hallGen hmem) hEC₁ hBP₁ hrecs
    exact ⟨mp₂⟩

end ConLeche.Model
