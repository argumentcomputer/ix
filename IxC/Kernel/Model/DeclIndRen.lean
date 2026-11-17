module

public import IxC.Kernel.Model.IndRecsRen
public import IxC.Kernel.Model.DeclIndJ
public import IxC.Kernel.Model.JudgeRules
public import IxC.Kernel.Model.IndRenRecord
public import IxC.Kernel.Semantics.IndBlockRun
import IxC.Kernel.Model.IndRenJudge
import IxC.Kernel.Model.IndMembers
import IxC.Kernel.Model.IndEtaLaw
import IxC.Kernel.Model.IndUnitLaw

public section

/-!
# The modeled route with the rule typings renamed, at a model

`declIndJ` (`Model/DeclIndJ.lean`) over the renamed record (`DeclIndRenRunJ`,
`Model/IndRenRecord.lean`): a block whose rules are typed on the renamed terms extends an
environment model. The hypotheses and the conclusion are `declIndJ`'s.

* The members are installed at the empty capability record (`indMembersPM`, generic in its
  package, here `renameJ f J`).
* The recursor group is `indRecsRen`. It needs, beyond `indRecs`'s premises, that no block name
  is a model's key, which the members' and recursors' front doors state
  (`MemberValRunJ`'s `isModelSuffix` conjunct), so the block renaming is idempotent.

`declIndStepRenJ` adds the η-family closure (from the record at the shape package), the two
facts the restated fold asks of the inductive kind; `foldRulesRen` is the fold at the
derivation package with every inductive block on the renamed route.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal
  RecRule IndCaps Declaration)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## No block name is a model's key -/

/-- The members' front doors: no member's name is a model's key. -/
theorem indMembersRunJ_noModel {K : Judgements md} {blockNames : List (Key md)}
    {caps : IndCaps md} :
    ∀ {env' : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ K blockNames caps env' members env₂ →
      ∀ ci ∈ members, ci.name.isModelSuffix = false
  | _, [], _, _ => fun ci hci => nomatch hci
  | _, ci :: rest, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    obtain ⟨type', -, hcvA, hsuf, -⟩ := hmv
    have hhead : ci.name.isModelSuffix = false := by
      have hn : cvA.name = ci.name := by rw [hcvA]; rfl
      rw [← hn]; exact hsuf
    have htail : ∀ c ∈ rest, c.name.isModelSuffix = false := by
      cases ci with
      | indInfo _ _ => exact indMembersRunJ_noModel hm
      | ctorInfo _ _ _ => exact indMembersRunJ_noModel hm
      | axiomInfo _ => exact nomatch hm
      | defnInfo _ _ _ => exact nomatch hm
      | thmInfo _ _ => exact nomatch hm
      | recInfo _ _ _ _ => exact nomatch hm
      | projInfo _ => exact nomatch hm
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hhead
    · exact htail c hc'

/-- The recursors' front doors: no recursor's name is a model's key. -/
theorem provisionRecsRunJ_noModel {K : Judgements md} {blockNames : List (Key md)} :
    ∀ {envAcc : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ K blockNames envAcc recs envSelf checked →
      ∀ ci ∈ recs, ci.name.isModelSuffix = false
  | _, [], _, _, _ => fun ci hci => nomatch hci
  | _, ci :: rest, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, -⟩ := h
    obtain ⟨type', -, hcvA, hsuf, -⟩ := hmv
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · have hn : cvA.name = c.name := by rw [hcvA]; rfl
      rw [← hn]; exact hsuf
    · exact provisionRecsRunJ_noModel hrec c hc

/-- **No block name is a model's key**, on the renamed record. -/
theorem declIndRenRunJ_noModel {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJ J env block env₂) :
    ∀ n, (block.map (·.name)).contains n = true → n.isModelSuffix = false := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  intro n hn
  have hmm : n ∈ block.map (·.name) := by simpa using hn
  obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
  rw [hsplit] at hci₀
  rcases List.mem_append.mp hci₀ with hci₀ | hci₀
  · exact indMembersRunJ_noModel hmem ci₀ hci₀
  · rcases hrecs with ⟨hnil, -⟩ | ⟨-, -, envSelf, checked, hprov, -⟩
    · rw [hnil] at hci₀; exact nomatch hci₀
    · exact provisionRecsRunJ_noModel hprov ci₀ hci₀

/-! ## The model step -/

set_option maxHeartbeats 1600000 in
/-- **A modeled block extends the model, with its rules typed on the renamed terms**
(`declIndJ` over `DeclIndRenRunJ`). -/
theorem declIndRenJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJ J env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  have hns := declIndRenRunJ_noModel h
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  -- the block's split
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
  have hEC0 : Ix.Kernel.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  -- no block name is stored before the block
  have hnostore : ∀ n, (block.map (·.name)).contains n = true →
      ∀ ci : ConstantInfo md, env.find? n = some ci → False := by
    intro n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersRun_mono _ hmem _ _ hf
      rw [indRecsRun_fresh (indRecsRenRunJ_shape hrecs) ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hBP0 : Ix.Kernel.BlockEtaPinned μ (block.map (·.name)) env :=
    fun n cvS capsS hnb hf _ => absurd (hnostore n hnb _ hf) (fun h => h)
  -- every block name is a stored member or a recursor of the block
  have hall : ∀ n, (block.map (·.name)).contains n = true →
      (envM.find? n).isSome = true ∨
      ∃ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersRun_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  -- the members, at the empty capability record
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁, hext₁⟩ :=
    indMembersPM memberEtaLaw memberUnitLaw (fun e => judgeFrames_renameJ (hfr e)) _ mp
      hbnNon
      (fun cv caps₂ _ => ⟨etaPins_empty,
        ⟨fun h => absurd h (by (cases md <;> decide)),
          fun h => absurd h (by (cases md <;> decide))⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  -- the recursor group, its rules typed renamed
  obtain ⟨mp₂, -, -, hext₂⟩ :=
    indRecsRen memberEtaLaw memberUnitLaw hfr hJ mp₁ hI₁ hIA₁ hbnRec hall hns hEC₁ hBP₁
      hrecs
  exact ⟨mp₂, hext₁.trans hext₂⟩

/-- **The modeled step, with the rules typed on the renamed terms**: the η-family closure and
a model extension, the two facts `foldJ` asks of the inductive kind. -/
theorem declIndStepRenJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJ J env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  ⟨declIndEtaClosedRunJ hE h.shape, declIndRenJ hfr hJ mp hE h⟩

/-- **A modeled block on the renamed route, over derivations**: the record at `rulesJ` gives
the two facts `foldRules` asks of the inductive kind. -/
theorem modeledStepRen_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)}
    (mp : EnvModelM V μ env) (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJ rulesJ env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  declIndStepRenJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m) mp hE h

/-- **The fold at the derivation package, every inductive block on the renamed route**
(`foldRulesModeled` for `DeclIndRenRunJ`). -/
theorem foldRulesRen {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (fun e b _ e₂ => DeclIndRenRunJ rulesJ e b e₂)
      env ds env' →
    EnvModelT V μ env → EnvModelT V μ env' :=
  foldRules (fun {_} mp _ hE {_ _ _} h => modeledStepRen_rulesJ mp hE h)

end Ix.Kernel.Model
