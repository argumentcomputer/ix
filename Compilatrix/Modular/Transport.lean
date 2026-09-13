import Compilatrix.EraseValidator

/-!
# Transport of checked source evidence

The erasure relation observes successful source, blob, and target lookups.
Keeping those bindings permits a certificate to move into a larger context;
unrelated bindings need not agree. Mutual-member scopes may grow, but existing
keys cannot disappear. This is a proof transformation, not another invocation
of the source validator. Semantic oracle agreement remains a premise of the
existing simulation theorem in the destination context.
-/

namespace Compilatrix.Sim

open Ixon (Address Constant MutConst)

structure ContextExtension (before : Ixon.Eval.EvalCtx) (raw : IxIR0.Ctx)
    (after : Ixon.Eval.EvalCtx) (target : IxIR0.Ctx) : Prop where
  source : ∀ {address constant}, before.resolve address = some constant →
    after.resolve address = some constant
  blob : ∀ {address value}, before.blobs address = some value →
    after.blobs address = some value
  declaration : ∀ {address decl}, raw.env address = some decl →
    target.env address = some decl
  externArity : ∀ {address arity}, before.externArity address = some arity →
    after.externArity address = some arity
  quotientKind : ∀ {address kind}, before.quotientKind address = some kind →
    after.quotientKind address = some kind
  natBlock : before.natBlock = after.natBlock
  strict : before.Strict → after.Strict

namespace ContextExtension

variable {before after : Ixon.Eval.EvalCtx} {raw target : IxIR0.Ctx}

theorem refl (source : Ixon.Eval.EvalCtx) (target : IxIR0.Ctx) :
    ContextExtension source target source target :=
  ⟨id, id, id, id, id, rfl, id⟩

theorem resolveMut (extension : ContextExtension before raw after target)
    {block idx constant member}
    (resolved : Ixon.Eval.resolveMut before block idx = .ok (constant, member)) :
    Ixon.Eval.resolveMut after block idx = .ok (constant, member) := by
  unfold Ixon.Eval.resolveMut at resolved ⊢
  cases h : before.resolve block with
  | none => simp [h] at resolved
  | some found => simpa [h, extension.source h] using resolved

theorem ctorShape (extension : ContextExtension before raw after target)
    {block indIdx cidx params fields}
    (shape : CtorShape before block indIdx cidx params fields) :
    CtorShape after block indIdx cidx params fields := by
  obtain ⟨bc, ind, ct, resolved, rest⟩ := shape
  exact ⟨bc, ind, ct, extension.resolveMut resolved, rest⟩

theorem inlineSharing (extension : ContextExtension before raw after target) :
    ContextExtension before.inlineSharing raw after.inlineSharing target where
  source := by
    intro address constant resolved
    simp only [Ixon.Eval.EvalCtx.inlineSharing_resolve] at resolved ⊢
    cases h : before.resolve address with
    | none => simp [h] at resolved
    | some found => simpa [h, extension.source h] using resolved
  blob := extension.blob
  declaration := extension.declaration
  externArity := extension.externArity
  quotientKind := extension.quotientKind
  natBlock := extension.natBlock
  strict := fun h => (extension.strict ⟨h.neutralElims, h.stringLiterals⟩).inlineSharing

theorem recPrefix (extension : ContextExtension before raw after target)
    {refs muts sa expression recursor}
    (head : RecPrefix before refs muts sa expression recursor) :
    RecPrefix after refs muts sa expression recursor := by
  cases head with
  | refH href hc hi hm hx =>
      exact .refH href (extension.source hc) hi (extension.resolveMut hm) hx
  | recurH hs hm hx => exact .recurH hs hm hx

theorem recSpine (extension : ContextExtension before raw after target)
    {refs muts sa expression recursor count}
    (spine : RecSpine before refs muts sa expression recursor count) :
    RecSpine after refs muts sa expression recursor count := by
  induction spine with
  | head first => exact .head (extension.recPrefix first)
  | step _ bound ih => exact .step ih bound

theorem defSpine (extension : ContextExtension before raw after target)
    {refs expression residual} (spine : DefSpine before refs expression residual) :
    DefSpine after refs expression residual := by
  induction spine with
  | head href hc hi hu => exact .head href (extension.source hc) hi hu
  | step _ ih => exact .step ih

theorem ctorSpine (extension : ContextExtension before raw after target)
    {refs expression address block indIdx cidx params fields consumed}
    (spine : CtorParamSpine before refs expression address block indIdx cidx
      params fields consumed) :
    CtorParamSpine after refs expression address block indIdx cidx
      params fields consumed := by
  induction spine with
  | head href hc hi hs =>
      exact .head href (extension.source hc) hi (extension.ctorShape hs)
  | step _ bound ih => exact .step ih bound

end ContextExtension

section

variable {oldScope newScope : MemberScope}
  {before after : Ixon.Eval.EvalCtx} {raw target : IxIR0.Ctx}

mutual

theorem PErase.extend {sc refs muts sa mask source output}
    (related : @PErase oldScope before raw sc refs muts sa mask source output)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @PErase newScope after target sc refs muts sa mask source output :=
  match related with
  | .var (scope := .(oldScope)) h => .var h
  | .sortE (scope := .(oldScope)) => .sortE
  | .allE (scope := .(oldScope)) => .allE
  | .lamK (scope := .(oldScope)) h body => .lamK h (body.extend extension scope)
  | .lamD (scope := .(oldScope)) h body => .lamD h (body.extend extension scope)
  | .app (scope := .(oldScope)) fn arg => .app (fn.extend extension scope) (arg.extend extension scope)
  | .appE (scope := .(oldScope)) h fn => .appE h (fn.extend extension scope)
  | .appG (scope := .(oldScope)) spine h fn => .appG (extension.recSpine spine) h (fn.extend extension scope)
  | .appDG (scope := .(oldScope)) spine h fn => .appDG (extension.defSpine spine) h (fn.extend extension scope)
  | .recP (scope := .(oldScope)) spine => .recP (spine.extend extension scope)
  | .recW (scope := .(oldScope)) spine h => .recW (spine.extend extension scope) h
  | .letE (scope := .(oldScope)) val body => .letE (val.extend extension scope) (body.extend extension scope)
  | .ctorP (scope := .(oldScope)) h spine decl => .ctorP h (extension.ctorSpine spine) (extension.declaration decl)
  | .ctorW (scope := .(oldScope)) spine h decl => .ctorW (extension.ctorSpine spine) h (extension.declaration decl)
  | .ref (scope := .(oldScope)) h covered => .ref h (covered.extend extension scope)
  | .recurS (scope := .(oldScope)) hi hx => .recurS hi hx
  | .recurI (scope := .(oldScope)) hs hm hr hi hd => .recurI hs (extension.resolveMut hm) hr hi (extension.declaration hd)
  | .recurD (scope := .(oldScope)) hs hm hr hi hu member => .recurD hs (extension.resolveMut hm) hr hi hu (scope member)
  | .recurO (scope := .(oldScope)) hs hm hr hi hu arity member =>
      .recurO hs (extension.resolveMut hm) hr hi hu (extension.externArity arity) (scope member)
  | .recurR (scope := .(oldScope)) hs hm hr hi hx member => .recurR hs (extension.resolveMut hm) hr hi hx (scope member)
  | .natE (scope := .(oldScope)) href blob => .natE href (extension.blob blob)
  | .strE (scope := .(oldScope)) href blob => .strE href (extension.blob blob)
  | .natDualE (scope := .(oldScope)) href blob => .natDualE href (extension.blob blob)
  | .strDualE (scope := .(oldScope)) href blob => .strDualE href (extension.blob blob)
  | .prjE (scope := .(oldScope)) val => .prjE (val.extend extension scope)
termination_by structural related

theorem RecEraseSpine.extend {sc refs muts sa mask source output recursor policies}
    (related : @RecEraseSpine oldScope before raw sc refs muts sa mask source output recursor policies)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @RecEraseSpine newScope after target sc refs muts sa mask source output recursor policies :=
  match related with
  | .head (scope := .(oldScope)) href hc hi hm hx hd member =>
      .head href (extension.source hc) hi (extension.resolveMut hm) hx
        (extension.declaration hd) (member.extend extension scope)
  | .selfHead (scope := .(oldScope)) hc hs hi hm hr ht hx => .selfHead hc hs hi (extension.resolveMut hm) hr ht hx
  | .memberHead (scope := .(oldScope)) hs hm hr hi hx member => .memberHead hs (extension.resolveMut hm) hr hi hx (scope member)
  | .keep (scope := .(oldScope)) fn arg => .keep (fn.extend extension scope) (arg.extend extension scope)
  | .ghost (scope := .(oldScope)) fn => .ghost (fn.extend extension scope)
  | .drop (scope := .(oldScope)) fn => .drop (fn.extend extension scope)
termination_by structural related

theorem Covered.extend {address}
    (related : @Covered oldScope before raw address)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @Covered newScope after target address :=
  match related with
  | .defn (scope := .(oldScope)) hc hi hu hd ho body => .defn (extension.source hc) hi hu (extension.declaration hd) ho (body.extend extension scope)
  | .defnProj (scope := .(oldScope)) hc hi hm hu hd hmdecl ho body =>
      .defnProj (extension.source hc) hi (extension.resolveMut hm) hu
        (extension.declaration hd) (extension.declaration hmdecl) ho (body.extend extension scope)
  | .externDefn (scope := .(oldScope)) hc hi hu ha hd => .externDefn (extension.source hc) hi hu (extension.externArity ha) (extension.declaration hd)
  | .externDefnProj (scope := .(oldScope)) hc hi hm hu ha hd hmdecl ho =>
      .externDefnProj (extension.source hc) hi (extension.resolveMut hm) hu
        (extension.externArity ha) (extension.declaration hd) (extension.declaration hmdecl) ho
  | .externAxio (scope := .(oldScope)) hc hi ha hd => .externAxio (extension.source hc) hi (extension.externArity ha) (extension.declaration hd)
  | .ctor (scope := .(oldScope)) hc hi hs hd => .ctor (extension.source hc) hi (extension.ctorShape hs) (extension.declaration hd)
  | .tyf (scope := .(oldScope)) hc hi hd => .tyf (extension.source hc) hi (extension.declaration hd)
  | .quot (scope := .(oldScope)) hc hi hq hd ho => .quot (extension.source hc) hi (extension.quotientKind hq) (extension.declaration hd) ho
  | .recrP (scope := .(oldScope)) hc hi hm hx hd member =>
      .recrP (extension.source hc) hi (extension.resolveMut hm) hx
        (extension.declaration hd) (member.extend extension scope)
termination_by structural related

theorem RecMember.extend {block index recursor}
    (related : @RecMember oldScope before raw block index recursor)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @RecMember newScope after target block index recursor :=
  match related with
  | .mk (scope := .(oldScope)) hm params hd rules => by
      apply RecMember.mk (extension.resolveMut hm) params
      · simpa only [extension.natBlock] using extension.declaration hd
      · exact rules.extend extension scope
termination_by structural related

theorem RulesRel.extend {block index recursor refs muts rules output}
    (related : @RulesRel oldScope before raw block index recursor refs muts rules output)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @RulesRel newScope after target block index recursor refs muts rules output :=
  match related with
  | .nil (scope := .(oldScope)) => .nil
  | .cons (scope := .(oldScope)) fields peeled body rest =>
      .cons fields peeled (body.extend extension scope) (rest.extend extension scope)
termination_by structural related

end

theorem MemberRel.extend {key} (related : @MemberRel oldScope before raw key)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) : @MemberRel newScope after target key := by
  cases related with
  | defn hm hu hd ho body => exact .defn (extension.resolveMut hm) hu (extension.declaration hd) ho (body.extend extension scope)
  | externDefn hm hu ha hd => exact .externDefn (extension.resolveMut hm) hu (extension.externArity ha) (extension.declaration hd)
  | recr member => exact .recr (member.extend extension scope)

theorem MemberCoverage.extend {keys}
    (related : @MemberCoverage oldScope before raw keys)
    (extension : ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) :
    @MemberCoverage newScope after target keys := by
  induction related with
  | nil strict => exact .nil (extension.strict strict)
  | cons member _ ih => exact .cons (member.extend extension scope) ih

end

end Compilatrix.Sim

namespace Compilatrix.EraseValidator

def CoverageDB.extend {oldScope newScope : Sim.MemberScope}
    {before after : Ixon.Eval.EvalCtx} {raw target : IxIR0.Ctx}
    (db : @CoverageDB oldScope before raw)
    (extension : Sim.ContextExtension before raw after target)
    (scope : oldScope.plan ⊆ newScope.plan) : @CoverageDB newScope after target :=
  db.map fun entry =>
    ⟨@CoveredEntry.address oldScope before raw entry,
      Sim.Covered.extend (@CoveredEntry.covered oldScope before raw entry)
        extension scope⟩

end Compilatrix.EraseValidator
