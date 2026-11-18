import IxVMRefinement.Assembly.FoldClauseSteps
import IxVMRefinement.Assembly.NativeAliasOpenTrace

/-! # The fold's clause at the opened head trace

The link the fold's clause carries between a registered family's stored former and its telescope
constant (`FamRead.link`, `Assembly/FoldClause.lean`) is the opened head trace
`FormerOpenTraceAt` (`Assembly/NativeAliasOpenTrace.lean`): the telescope constant has the
traced binders of the stored former's type, and the result-sort walk from it ends in a sort
level-equivalent to the family's.

* `linkLaws_formerOpenTrace`: the trace satisfies the laws the clause asks of a link. It is kept
  along lookups, and a family whose former is declared at its telescope has it with no head
  step.
* `FamRead.withLink`: a family read off the store at one link is read at another, given that
  link.
* `FoldClauseWith.aliasInstall`: the install of a block whose former is declared at a
  definition keeps the clause at this link. One premise is not yet produced by any theorem,
  `hfollow`: the registered telescope constant has the traced binders of the stored former and
  the family's sort is the traced sort. It is what the circuit's telescope builder gives once
  it is shown to follow the head trace at a term that needs head steps.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key)
open Ix.Kernel.Semantics (NativeFam)

/-- A term with no free variable has every free variable below any index. -/
theorem fvarIdxLt_of_closed (d : Nat) :
    ∀ {e : Ix.Kernel.Expr .anon}, e.hasFvar = false → Decl.fvarIdxLt d e = true
  | .fvar _ _, h => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Decl.fvarIdxLt, fvarIdxLt_of_closed d h.1, fvarIdxLt_of_closed d h.2]
  | .lam t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Decl.fvarIdxLt, fvarIdxLt_of_closed d h.1, fvarIdxLt_of_closed d h.2]
  | .forallE t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Decl.fvarIdxLt, fvarIdxLt_of_closed d h.1, fvarIdxLt_of_closed d h.2]
  | .letE t v b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Decl.fvarIdxLt, fvarIdxLt_of_closed d h.1.1, fvarIdxLt_of_closed d h.1.2,
      fvarIdxLt_of_closed d h.2]
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.hasFvar] at h
    simp [Decl.fvarIdxLt, fvarIdxLt_of_closed d h]

/-- **The opened head trace satisfies the laws the clause asks of a link.** -/
theorem linkLaws_formerOpenTrace : LinkLaws FormerOpenTraceAt where
  mono := fun hf h => h.mono (fun k ci hk => hf hk)
  ofTele := fun htele hsort htc => by
    obtain ⟨bs, hs⟩ := hsort
    refine FormerOpenTraceAt.of_syntactic htele hs (fvarIdxLt_of_closed 0 ?_) ?_
    · rw [← htele]
      exact htc.closed
    · rw [← htele]
      exact htc.bounded

section

variable {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {lim : Option Nat}
  {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}

/-- **A family read off the store at one link is read at another**, given that link. Every
other field is independent of the link. -/
theorem FamRead.withLink {L₀ L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {fam : NativeFam .anon} (h : FamRead L₀ t E env fam) (hl : L env fam) :
    FamRead L t E env fam :=
  { stored := h.stored
    lps := h.lps
    tele := h.tele
    sort := h.sort
    isProp := h.isProp
    kinds := h.kinds
    nodup := h.nodup
    ctorFields := h.ctorFields
    record := h.record
    retHead := h.retHead
    noProj := h.noProj
    link := hl }

/-- **The install of a block whose former is declared at a definition keeps the clause at the
opened head trace**, registering its family.

`hfacts` is IxC's record of the install at the registered family; its telescope constant is the
traced term of the stored former. `hres`, `hloads`, `heta`, `hkeys₂`, `hnoTable` and `hread`
are what the block's unit step reads off its run at the new environment (`hread` is the
family's reading with nothing said of the link; `hnoTable` says the install stores no
projection table, which holds because such a family has an index, and is all the guard
certificates need).

`hfollow` is the one premise no theorem produces yet: the registered telescope constant has the
traced binders of the stored former's type and the family's sort is the traced sort. It follows
from the circuit's telescope builder once that is shown to follow the head trace at a term that
needs head steps. -/
theorem FoldClauseWith.aliasInstall {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : FoldClauseWith.{u} FormerOpenTraceAt t E lim env Reg)
    (hfacts : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ Core.unresolvedKey)
    (hloads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env₂, t, lim⟩))
    (heta : Decl.EtaStable env₂) (hkeys₂ : HashKeyed t env₂)
    (hnoTable : ∀ (k : Key .anon) (tbl : Ix.Kernel.ProjTable .anon),
      env₂.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
      env.find? (Ix.Kernel.projTableName k) = none → False)
    (hread : FamRead (fun _ _ => True) t E env₂ fam)
    (hfollow : FormerOpenTraceAt env₂ fam) :
    FoldClauseWith.{u} FormerOpenTraceAt t E lim env₂ (fun f => Reg f ∨ f = fam) :=
  h.nativeAt linkLaws_formerOpenTrace hfacts hpin hna hres hloads heta hkeys₂
    (guardCerts_noTable h.guard hfacts.envExt hnoTable) (hread.withLink hfollow)

end

end IxVM.Refinement.Typing
