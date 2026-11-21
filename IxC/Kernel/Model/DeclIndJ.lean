module

public import IxC.Kernel.Model.IndRecs
public import IxC.Kernel.Model.JudgeSound
public import IxC.Kernel.Semantics.IndBlockRun
import IxC.Kernel.Model.IndEtaLaw
import IxC.Kernel.Model.IndUnitLaw

public section

/-!
# The modeled inductive route over a judgement package, at a model

`declInd`'s second case (`Model/DeclInd.lean`) stated over a judgement package
(`DeclIndRunJ`, `Semantics/DeclIndJ.lean`): a modeled block extends an
environment model. Its two phases are the package forms of the kernel's:

* `indMembersPM`, the members at the empty capability record;
* `indRecs`, the recursor group: provision, fire each rule against its `iota`
  theorem, attach the rules.

What it needs of the package: its annotations keep scoping (`JudgeFrames`), and
it is sound at every model (`JudgeSound`). Both the kernel's runs (`runJ`, with
`judgeSound_runJ`) and the derivations of the rules tier (`rulesJ`, with
`judgeSound_rulesJ_of`) satisfy it.

The new model extends the old one (`ModelExt`): the members and the provisioned
recursors are fresh conses, and attaching the rules keeps every leaf. So a
modeled step keeps stored theorem values read (`ThmValOk.of_ext`), which is what
the restated fold asks of the inductive kind (`foldJ`'s `hind`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

set_option maxHeartbeats 1600000 in
/-- **A modeled block extends the model**, over a judgement package. -/
theorem declIndJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRunJ J env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
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
      rw [indRecsRun_fresh hrecs ci₀ hci₀] at hup
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
    indMembersPM memberEtaLaw memberUnitLaw hfr _ mp hbnNon
      (fun cv caps₂ _ => ⟨etaPins_empty,
        ⟨fun h => absurd h (by (cases md <;> decide)),
          fun h => absurd h (by (cases md <;> decide))⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  -- the recursor group
  obtain ⟨mp₂, -, -, hext₂⟩ :=
    indRecs memberEtaLaw memberUnitLaw hfr hJ mp₁ hI₁ hIA₁ hbnRec hall hEC₁ hBP₁ hrecs
  exact ⟨mp₂, hext₁.trans hext₂⟩

/-- **The modeled step**: the η-family closure and a model extension, the two
facts `foldJ` asks of the inductive kind. -/
theorem declIndStepJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRunJ J env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  ⟨declIndEtaClosedRunJ hE h, declIndJ hfr hJ mp hE h⟩

end Ix.Kernel.Model
