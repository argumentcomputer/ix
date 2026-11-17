module

public import IxC.Kernel.Model.IndRenAt
public import IxC.Kernel.Model.IndBlockRunAt
public import IxC.Kernel.Model.IndMembersAt
public import IxC.Kernel.Model.IndRecsRenAt
public import IxC.Kernel.Model.DeclIndRen
public import IxC.Kernel.Model.IndRecsRen
public import IxC.Kernel.Model.DeclIndJ
public import IxC.Kernel.Model.JudgeRules
public import IxC.Kernel.Model.IndRenRecord
public import IxC.Kernel.Semantics.IndBlockRun
import IxC.Kernel.Model.IndRenJudge
import IxC.Kernel.Model.IndMembers

public section

/-!
# The modeled route with the rule typings renamed, at given model and theorem keys, at a model

`declIndRenJ` (`Model/DeclIndRen.lean`) over `DeclIndRenRunJAt J g thmKey`
(`Model/IndRenAt.lean`), with `declIndRenJ`'s hypotheses: a block whose members' models are
stored at `g n`, whose rules' `iota` theorems are stored at `thmKey R j`, and whose rules are
typed on the terms renamed by `blockRenAt g`, extends an environment model.

* The members are installed at the empty capability record (`indMembersPMAt`).
* The recursor group is `indRecsRenAt`.
* Where `declIndRenJ` reads the members' `isModelSuffix` guards (no block name is a model's key),
  this reads the record's own conjunct: `g` maps every block name outside the block.

`declIndStepRenJAt` adds the η-family closure; `foldRulesRenAt` is the fold at the derivation
package with every inductive block on the renamed route at some keys. `declIndRenRunJ_at` makes
the original record the instance at the aux keys.
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

/-! ## The original record is the instance at the aux keys -/

/-- **The original renamed record is the parametric one at the aux keys**: the model of `n` at
`auxKey n .model`, the `iota` theorem of `R`'s rule `j` at `auxKey (auxKey R .model) (.iota j)`.
The record's extra conjunct holds because no block name is a model's key. -/
theorem declIndRenRunJ_at {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJ J env block env₂) :
    DeclIndRenRunJAt J (fun n => auxKey n .model)
      (fun R j => auxKey (auxKey R .model) (.iota j)) env block env₂ := by
  have hns := declIndRenRunJ_noModel h
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  refine ⟨hsplit, ?_, envM, indMembersRunJ_at hmem, indRecsRenRunJ_at hrecs⟩
  intro n _
  show (block.map (·.name)).contains (auxKey n .model) = false
  cases hc : (block.map (·.name)).contains (auxKey n .model) with
  | false => rfl
  | true => exact absurd rfl (Ix.Kernel.auxKey_model_ne (hns _ hc))

/-! ## The model step -/

set_option maxHeartbeats 1600000 in
/-- **A modeled block extends the model, with its rules typed on the renamed terms, at given
model and theorem keys** (`declIndRenJ` over `DeclIndRenRunJAt`). -/
theorem declIndRenJAt {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {g : Key md → Key md} {thmKey : Key md → Nat → Key md}
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJAt J g thmKey env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨hsplit, hout, envM, hmem, hrecs⟩ := h
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
    · rw [indMembersRun_freshAt _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersRun_monoAt _ hmem _ _ hf
      rw [indRecsRun_freshAt (indRecsRenRunJ_shapeAt hrecs) ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTTAt g (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalledAt g (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hNE0 : BlockNoEta (block.map (·.name)) env :=
    fun n hn _ _ hf => absurd (hnostore n hn _ hf) (fun h => h)
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
    · exact Or.inl (indMembersRun_storedAt _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  -- the members, at the empty capability record
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hNE₁, hext₁⟩ :=
    indMembersPMAt (fun e => judgeFrames_renameJ (hfr e)) hout _ mp hbnNon hmem
      hI0 hIA0 hEC0 hNE0
  -- the recursor group, its rules typed renamed
  obtain ⟨mp₂, -, -, hext₂⟩ :=
    indRecsRenAt hfr hJ mp₁ hI₁ hIA₁ hbnRec hall hout hEC₁ hNE₁ hrecs
  exact ⟨mp₂, hext₁.trans hext₂⟩

/-- **The modeled step, with the rules typed on the renamed terms, at given keys**: the η-family
closure and a model extension, the two facts `foldJ` asks of the inductive kind. -/
theorem declIndStepRenJAt {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {g : Key md → Key md} {thmKey : Key md → Nat → Key md}
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJAt J g thmKey env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  ⟨declIndEtaClosedRunJAt hE h.shape, declIndRenJAt hfr hJ mp hE h⟩

/-- **A modeled block on the renamed route at given keys, over derivations**: the record at
`rulesJ` gives the two facts `foldRules` asks of the inductive kind. -/
theorem modeledStepRenAt_rulesJ {g : Key md → Key md} {thmKey : Key md → Nat → Key md}
    {env env₂ : Env md} {block : List (ConstantInfo md)}
    (mp : EnvModelM V μ env) (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJAt rulesJ g thmKey env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  declIndStepRenJAt judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m) mp hE h

/-- **The fold at the derivation package, every inductive block on the renamed route at some
model and theorem keys** (`foldRulesRen` for `DeclIndRenRunJAt`). -/
theorem foldRulesRenAt {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (fun e b _ e₂ => ∃ g thmKey, DeclIndRenRunJAt rulesJ g thmKey e b e₂)
      env ds env' →
    EnvModelT V μ env → EnvModelT V μ env' :=
  foldRules (fun {_} mp _ hE {_ _ _} h => by
    obtain ⟨g, thmKey, h⟩ := h
    exact modeledStepRenAt_rulesJ mp hE h)

end Ix.Kernel.Model
