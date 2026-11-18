import IxVMRefinement.FamilyAlias.CallTables
import IxVMRefinement.FamilyAlias.FamilyCall

/-! # The cells of the terms `check_family` renames, at a step's environment

`rename_stored_of_members` represents a renamed term at the keying of a step's prefix once each
cell of the term is stored or is a member of the family (in `src`). A cell of a term the check
loads is a reference the block or the family record uses, or a recursion address of one of them
(`L1.RawConvExpr.addrIn_used`); a recursion address is in `src` (`FamilyTables`). This module
places a used reference:

* `usedRef_stored_or_src`: at an environment a step of the block is handed (`FamilyStepEnv`), a
  reference the block or the family record uses is stored or is in `src`: the step's clauses
  give it stored, a constant address of the family (in `src`, `famAddr_mem_src`), or one no step
  needs; the last is excluded by the block's walk (`blockRefs`) and, for the family record, by
  the check's own reading of its references (covered at the limit, hence stored, or needed);
* `rename_stored_of_src`: `rename_stored_of_members` with the members given as the addresses
  of `src`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Decl.FamilyAlias (aliasMap)
open Ix.Kernel.Semantics (NativeFam)

set_option linter.unusedVariables false

universe u

/-- **A reference the block or the family record uses is stored, or is in `src`**, at an
environment a step of the block is handed, where each reference the family record uses is
covered at the limit or needed (`FamilyCallFacts.recRefs`). -/
theorem usedRef_stored_or_src {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    (hrec : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x)
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {h : Heap F} {typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address}
    {xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F}
    (T : FamilyTables B rb ms rs h typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM
      xrM xsrc xdst)
    {x : _root_.Address} (hx : UsedRef E₀ B x ∨ UsedRef E₀ rb x) :
    (∃ ci, env.find? (Core.keyOf t x) = some ci) ∨ x ∈ (typeAs ++ (ctorAs ++ recAs)).map ixAddr := by
  rcases hE.refs x hx with hs | hf | hn
  · exact Or.inl (Option.isSome_iff_exists.mp hs)
  · exact Or.inr (famAddr_mem_src hB hR T hf)
  · rcases hx with hb | hr
    · rcases hE.blockRefs x hb with hs | hneed
      · exact Or.inl (Option.isSome_iff_exists.mp hs)
      · exact absurd hneed hn
    · rcases hrec x hr with hcov | hneed
      · exact Or.inl (Option.isSome_iff_exists.mp (hE.covered x hcov))
      · exact absurd hneed hn

/-- **The renamed term at the keying of a prefix that stores every model**, where each cell of
the term is stored or is an address of `src` (`rename_stored_of_members`). -/
theorem rename_stored_of_src {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : Decl.TmExact (Core.keyOf t) 0 Γ₁ h k E e)
    (hmodels : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci)
    (hcells : ∀ a, AddrIn h e a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr) :
    Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h' k
      (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b)))) E) r := by
  refine rename_stored_of_members hwf ev hlen hsrc hdst he hmodels (fun a ha => ?_)
  rcases hcells a ha with hs | hm
  · exact Or.inl hs
  · obtain ⟨b, hb, hab⟩ := List.mem_map.mp hm
    rw [Decl.ixAddr_injective hab] at hb
    exact Or.inr hb

end IxVM.Refinement.Typing.FamilyAlias
