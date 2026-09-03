import Ix.Tc.Verify.Inductive.GeneratedRecursorSemantics
import Ix.Tc.Verify.Whnf

/-!
# Generated recursor telescope closure

`buildRecType` accumulates parameter, motive, minor, index, and major domains
under their live local contexts, builds the return body in the complete
context, and finally closes the array from right to left.  This module proves
that last production stage independently of how the individual domains were
obtained.

The proof has two deliberately separate parts:

* `closeK`/`closeV` are the exact Ix and Lean4Lean reverse closures;
* `TelescopeS` records each domain at the context in which production built
  it, rather than assuming a relation for the already-closed result.

The execution theorem below also requires finite support for every concrete
intern request.  Thus hash-consing cannot silently replace a generated forall
with a colliding expression.
-/

namespace Ix.Tc

open Lean4Lean (VEnv VExpr VInductDecl VLevel VLocalDecl)

namespace GeneratedRecursorTypeClosure

/-- Exact pure result of production's right-to-left forall closure. -/
def closeK (domains : Array (KExpr .anon)) : Nat → KExpr .anon → KExpr .anon
  | 0, body => body
  | remaining + 1, body =>
      closeK domains remaining
        (.mkAll RecM.anonN RecM.anonBi domains[remaining]! body)

/-- Lean4Lean-side closure with the same array positions and order. -/
def closeV (domains : Array VExpr) : Nat → VExpr → VExpr
  | 0, body => body
  | remaining + 1, body =>
      closeV domains remaining (.forallE domains[remaining]! body)

/-- The flattened target domain list used by Lean4Lean's canonical mixed
recursor type. -/
def canonicalMajorDomain {source : VInductDecl}
    (generation : source.GenerationChecked) : VExpr :=
  let constructors := generation.block.ctorPairs.length
  let indices := generation.idxTel.length
  VExpr.appN
    (.const generation.block.sourceType.name
      generation.sourceLevels)
    (VExpr.bvarRevRange (indices + constructors + 1) source.nparams ++
      VExpr.bvarRevRange 0 indices)

/-- The target recursor telescope, flattened in production construction
order: parameters, motive, minors, indices, and major premise. -/
def canonicalDomainList {source : VInductDecl}
    (generation : source.GenerationChecked) : List VExpr :=
  generation.paramsTel ++
    [generation.motiveType] ++
    generation.minorTypes ++
    VExpr.liftTelN (generation.block.ctorPairs.length + 1)
      generation.idxTel 0 ++
    [canonicalMajorDomain generation]

def canonicalDomains {source : VInductDecl}
    (generation : source.GenerationChecked) : Array VExpr :=
  (canonicalDomainList generation).toArray

/-- The target body after every canonical recursor binder has been opened. -/
def canonicalBody {source : VInductDecl}
    (generation : source.GenerationChecked) : VExpr :=
  let constructors := generation.block.ctorPairs.length
  let indices := generation.idxTel.length
  .app
    (VExpr.appN (.bvar (indices + constructors + 1))
      (VExpr.bvarRevRange 1 indices))
    (.bvar 0)

/-- Reverse array closure agrees with `forallN` over the selected prefix. -/
theorem closeV_eq_forallN_take (domains : Array VExpr) (count : Nat)
    (body : VExpr) (hcount : count ≤ domains.size) :
    closeV domains count body =
      VExpr.forallN (domains.toList.take count) body := by
  induction count generalizing body with
  | zero => rfl
  | succ count ih =>
      have hindex : count < domains.size := by omega
      rw [closeV, ih _ (by omega), List.take_add_one,
        Array.getElem?_toList, Array.getElem?_eq_getElem hindex]
      simp only [Option.toList_some, VExpr.forallN_append, VExpr.forallN,
        getElem!_def, hindex, Array.getElem?_eq_getElem]

/-- Closing the whole canonical flattened telescope is exactly Lean4Lean's
public mixed recursor type, not merely a definitionally equal variant. -/
theorem closeV_canonical {source : VInductDecl}
    (generation : source.GenerationChecked) :
    closeV (canonicalDomains generation)
        (canonicalDomains generation).size (canonicalBody generation) =
      generation.recType := by
  rw [closeV_eq_forallN_take _ _ _ (Nat.le_refl _)]
  change VExpr.forallN
      ((canonicalDomainList generation).take
        (canonicalDomainList generation).length)
      (canonicalBody generation) = generation.recType
  rw [List.take_length]
  simp [canonicalDomainList, canonicalMajorDomain, canonicalBody,
    VInductDecl.GenerationChecked.recType,
    VExpr.forallN_append, VExpr.forallN]

/-- Translation context after the first `count` outer domains have been
opened.  The newest binder is the head of `KVLCtx`, matching `TrKExprS`. -/
def opened (base : KVLCtx) (domains : Array VExpr) : Nat → KVLCtx
  | 0 => base
  | count + 1 =>
      (none, VLocalDecl.vlam domains[count]!) :: opened base domains count

/-- The translation context opened by the production builder is exactly the
reverse of the already-built target prefix. -/
theorem opened_toCtx (base : KVLCtx) (domains : Array VExpr) (count : Nat)
    (hcount : count ≤ domains.size) :
    (opened base domains count).toCtx =
      (domains.toList.take count).reverse ++ base.toCtx := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hindex : count < domains.size := by omega
      rw [opened]
      change domains[count]! :: (opened base domains count).toCtx = _
      rw [ih (by omega), List.take_add_one,
        Array.getElem?_toList, Array.getElem?_eq_getElem hindex]
      simp only [Option.toList_some, getElem!_def, hindex,
        Array.getElem?_eq_getElem, List.reverse_append, List.reverse_singleton,
        List.cons_append, List.nil_append]

/-- Inversion for a well-formed iterated forall.  Lean4Lean provides the
constructor theorem `IsType.forallN`; the converse is what lets the production
builder consume the canonical result type one open domain at a time. -/
theorem isType_forallN_inv
    {env : VEnv} {uvars : Nat} {ctx domains : List VExpr} {body : VExpr}
    (henv : env.Ordered)
    (h : env.IsType uvars ctx (VExpr.forallN domains body)) :
    env.OnTel uvars ctx domains ∧
      env.IsType uvars (domains.reverse ++ ctx) body := by
  induction domains generalizing ctx with
  | nil => exact ⟨trivial, h⟩
  | cons domain domains ih =>
      obtain ⟨hdomain, hrest⟩ :=
        Lean4Lean.VEnv.IsType.forallE_inv henv h
      obtain ⟨htelescope, hbody⟩ := ih hrest
      exact ⟨⟨hdomain, htelescope⟩,
        by simpa [List.reverse_cons, List.append_assoc] using hbody⟩

/-- Every entry of a well-formed telescope is a type in the context generated
by the entries strictly before it. -/
theorem onTel_isType_getElem
    {env : VEnv} {uvars : Nat} {ctx domains : List VExpr}
    (h : env.OnTel uvars ctx domains) (index : Nat)
    (hindex : index < domains.length) :
    env.IsType uvars ((domains.take index).reverse ++ ctx)
      domains[index] := by
  induction domains generalizing ctx index with
  | nil => contradiction
  | cons domain domains ih =>
      rcases h with ⟨hdomain, hrest⟩
      cases index with
      | zero => simpa using hdomain
      | succ index =>
          have htail : index < domains.length := by simpa using hindex
          simpa [List.take, List.reverse_cons, List.append_assoc] using
            ih hrest index htail

/-- Lean4Lean's semantic generation invariant decomposes into precisely the
flattened target telescope and open body used by the production builder. -/
theorem canonical_onTel_and_bodyType
    {source : VInductDecl} {generation : source.GenerationChecked}
    {env : VEnv}
    (hgeneration : VInductDecl.GenerationEnv generation env) :
    env.OnTel generation.recursor.uvars []
        (canonicalDomainList generation) ∧
      env.IsType generation.recursor.uvars
        (canonicalDomainList generation).reverse
        (canonicalBody generation) := by
  have hfull := hgeneration.recType_isType
  rw [← closeV_canonical generation] at hfull
  rw [closeV_eq_forallN_take _ _ _ (Nat.le_refl _)] at hfull
  change env.IsType generation.recursor.uvars []
      (VExpr.forallN
        ((canonicalDomainList generation).take
          (canonicalDomainList generation).length)
        (canonicalBody generation)) at hfull
  rw [List.take_length] at hfull
  simpa using isType_forallN_inv hgeneration.ord hfull

/-- Target-side typing of one canonical domain at its exact construction
context. -/
theorem canonical_domainType
    {source : VInductDecl} {generation : source.GenerationChecked}
    {env : VEnv}
    (hgeneration : VInductDecl.GenerationEnv generation env)
    (index : Nat) (hindex : index < (canonicalDomains generation).size) :
    env.IsType generation.recursor.uvars
      (opened [] (canonicalDomains generation) index).toCtx
      (canonicalDomains generation)[index]! := by
  have hlist : index < (canonicalDomainList generation).length := by
    simpa [canonicalDomains] using hindex
  have hentry := onTel_isType_getElem
    (canonical_onTel_and_bodyType hgeneration).1 index hlist
  rw [opened_toCtx [] (canonicalDomains generation) index (by omega)]
  simpa [canonicalDomains, KVLCtx.toCtx, getElem!_def, hlist] using hentry

/-- Target-side typing of the canonical return body under the complete
flattened recursor telescope. -/
theorem canonical_bodyType
    {source : VInductDecl} {generation : source.GenerationChecked}
    {env : VEnv}
    (hgeneration : VInductDecl.GenerationEnv generation env) :
    env.IsType generation.recursor.uvars
      (opened [] (canonicalDomains generation)
        (canonicalDomains generation).size).toCtx
      (canonicalBody generation) := by
  rw [opened_toCtx [] (canonicalDomains generation)
    (canonicalDomains generation).size (Nat.le_refl _)]
  simpa [canonicalDomains, KVLCtx.toCtx] using
    (canonical_onTel_and_bodyType hgeneration).2

/-- Operation-shaped correspondence for a generated dependent telescope.

`domainAt i` is stated in the context containing exactly the preceding
domains.  The body is stated under the complete prefix selected by `count`.
No field mentions either already-closed expression. -/
structure TelescopeS (env : VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (base : KVLCtx) (ixDomains : Array (KExpr .anon))
    (targetDomains : Array VExpr) (count : Nat)
    (ixBody : KExpr .anon) (targetBody : VExpr) : Prop where
  ixBound : count ≤ ixDomains.size
  targetBound : count ≤ targetDomains.size
  domainType : ∀ (index : Nat), index < count →
    env.IsType uvars (opened base targetDomains index).toCtx
      targetDomains[index]!
  domainAt : ∀ (index : Nat), index < count →
    TrKExprS env uvars nameOf trProj
      (opened base targetDomains index)
      ixDomains[index]! targetDomains[index]!
  bodyType : env.IsType uvars (opened base targetDomains count).toCtx
    targetBody
  body : TrKExprS env uvars nameOf trProj
    (opened base targetDomains count) ixBody targetBody

namespace TelescopeS

/-- Construct the operation-shaped telescope from only the Ix-to-target
relations produced by the live builder. All target typing fields are recovered
from Lean4Lean's generation invariant. -/
theorem of_canonical
    {source : VInductDecl} {generation : source.GenerationChecked}
    {env : VEnv}
    (hgeneration : VInductDecl.GenerationEnv generation env)
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {ixDomains : Array (KExpr .anon)} {ixBody : KExpr .anon}
    (hsize : ixDomains.size = (canonicalDomains generation).size)
    (hdomain : ∀ (index : Nat), index < ixDomains.size →
      TrKExprS env generation.recursor.uvars nameOf trProj
        (opened [] (canonicalDomains generation) index)
        ixDomains[index]! (canonicalDomains generation)[index]!)
    (hbody : TrKExprS env generation.recursor.uvars nameOf trProj
      (opened [] (canonicalDomains generation) ixDomains.size)
      ixBody (canonicalBody generation)) :
    TelescopeS env generation.recursor.uvars nameOf trProj [] ixDomains
      (canonicalDomains generation) ixDomains.size ixBody
      (canonicalBody generation) where
  ixBound := Nat.le_refl _
  targetBound := by omega
  domainType := fun index hindex =>
    canonical_domainType hgeneration index (by omega)
  domainAt := hdomain
  bodyType := by
    rw [hsize]
    exact canonical_bodyType hgeneration
  body := hbody

/-- Closing an operation-shaped telescope yields exact structural
translation of the two closed terms. -/
theorem close
    {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {base : KVLCtx} {ixDomains : Array (KExpr .anon)}
    {targetDomains : Array VExpr} {count : Nat}
    {ixBody : KExpr .anon} {targetBody : VExpr}
    (h : TelescopeS env uvars nameOf trProj base ixDomains targetDomains
      count ixBody targetBody) :
    TrKExprS env uvars nameOf trProj base
      (closeK ixDomains count ixBody)
      (closeV targetDomains count targetBody) := by
  induction count generalizing ixBody targetBody with
  | zero =>
      simpa [closeK, closeV, opened] using h.body
  | succ count ih =>
      have hixBound := h.ixBound
      have htargetBound := h.targetBound
      have hix : count < ixDomains.size := by omega
      have htarget : count < targetDomains.size := by omega
      let ixDomain := ixDomains[count]!
      let targetDomain := targetDomains[count]!
      let ixBody' := KExpr.mkAll RecM.anonN RecM.anonBi ixDomain ixBody
      let targetBody' := VExpr.forallE targetDomain targetBody
      have hdomainType :
          env.IsType uvars (opened base targetDomains count).toCtx
            targetDomain := h.domainType count (by omega)
      have hdomain :
          TrKExprS env uvars nameOf trProj
            (opened base targetDomains count) ixDomain targetDomain :=
        h.domainAt count (by omega)
      have hbodyType :
          env.IsType uvars
            (targetDomain :: (opened base targetDomains count).toCtx)
            targetBody := by
        simpa [opened, targetDomain, KVLCtx.toCtx] using h.bodyType
      have hbody :
          TrKExprS env uvars nameOf trProj
            ((none, VLocalDecl.vlam targetDomain) ::
              opened base targetDomains count)
            ixBody targetBody := by
        simpa [opened, targetDomain] using h.body
      have hclosedBody :
          TrKExprS env uvars nameOf trProj
            (opened base targetDomains count) ixBody' targetBody' := by
        exact .all hdomainType hbodyType hdomain hbody
      have hclosedBodyType :
          env.IsType uvars (opened base targetDomains count).toCtx
            targetBody' :=
        Lean4Lean.VEnv.IsType.forallE hdomainType hbodyType
      have hprefix : TelescopeS env uvars nameOf trProj base ixDomains
          targetDomains count ixBody' targetBody' :=
        { ixBound := by omega
          targetBound := by omega
          domainType := fun index hindex => h.domainType index (by omega)
          domainAt := fun index hindex => h.domainAt index (by omega)
          bodyType := hclosedBodyType
          body := hclosedBody }
      simpa [closeK, closeV, ixBody', targetBody', ixDomain,
        targetDomain] using ih hprefix

end TelescopeS

/-! ## Exact execution of the production closure -/

/-- Every concrete forall node requested by the remaining production closure
belongs to the finite run support. -/
def RequestsSupported (support : RunSupport)
    (domains : Array (KExpr .anon)) : Nat → KExpr .anon → Prop
  | 0, _ => True
  | remaining + 1, body =>
      let requested := KExpr.mkAll RecM.anonN RecM.anonBi
        domains[remaining]! body
      support requested ∧ RequestsSupported support domains remaining requested

/-- The explicit closure returns `closeK` exactly and retains a coherent,
covered intern table.  In particular, address collisions cannot change a
generated binder while preserving successful control flow. -/
theorem run_exact
    {support : RunSupport} (hcollision : support.CollisionFree)
    {saved : Nat} {domains : Array (KExpr .anon)} {count : Nat}
    {body : KExpr .anon} (hsupported : RequestsSupported support domains count body)
    (methods : Methods .anon) (initial : TcState .anon)
    (hintern : initial.env.intern.WF)
    (hcover : support.CoversIntern initial.env.intern) :
    ∃ final,
      (RecM.closeGeneratedRecursorForalls saved domains count body).run
          methods initial = .ok (closeK domains count body) final ∧
      final.env.intern.WF ∧ support.CoversIntern final.env.intern := by
  induction count generalizing body initial with
  | zero =>
      let final := { initial with
        lctx := initial.lctx.truncate saved }
      refine ⟨final, ?_, ?_, ?_⟩
      · rfl
      · exact hintern
      · exact hcover
  | succ count ih =>
      simp only [RequestsSupported] at hsupported
      let requested := KExpr.mkAll RecM.anonN RecM.anonBi
        domains[count]! body
      let popped := { initial with
        lctx := initial.lctx.truncate (initial.lctx.size - 1) }
      have hspec := TcM.internExpr_support_spec hcollision hsupported.1
        popped.env.intern hintern hcover
      have hrequested :
          (popped.env.intern.internExpr requested).1 = requested := by
        simpa [requested, popped] using hspec.1
      let afterIntern := { popped with env := { popped.env with
        intern := (popped.env.intern.internExpr requested).2 } }
      have hinternAfter : afterIntern.env.intern.WF := by
        simpa [afterIntern, popped] using hspec.2.1
      have hcoverAfter : support.CoversIntern afterIntern.env.intern := by
        simpa [afterIntern, popped] using hspec.2.2
      obtain ⟨final, hrun, hfinalIntern, hfinalCover⟩ :=
        ih hsupported.2 afterIntern hinternAfter hcoverAfter
      refine ⟨final, ?_, hfinalIntern, hfinalCover⟩
      simp only [RecM.closeGeneratedRecursorForalls, ReaderT.run_bind]
      change EStateM.bind (modify fun s : TcState .anon => { s with
        lctx := s.lctx.truncate (s.lctx.size - 1) }) _ initial = _
      simp only [modify, EStateM.bind]
      change EStateM.bind (TcM.intern requested) _ popped = _
      simp only [TcM.intern, TcM.runIntern, internExprM, hrequested,
        EStateM.bind]
      exact hrun

/-- Combining the exact production run with the operation-shaped telescope
proof yields the final structural translation returned by the real helper. -/
theorem run_translation
    {support : RunSupport} (hcollision : support.CollisionFree)
    {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {base : KVLCtx} {ixDomains : Array (KExpr .anon)}
    {targetDomains : Array VExpr} {count : Nat}
    {ixBody result : KExpr .anon} {targetBody : VExpr}
    {saved : Nat} {methods : Methods .anon}
    {initial final : TcState .anon}
    (hsupported : RequestsSupported support ixDomains count ixBody)
    (hintern : initial.env.intern.WF)
    (hcover : support.CoversIntern initial.env.intern)
    (run :
      (RecM.closeGeneratedRecursorForalls saved ixDomains count ixBody).run
        methods initial = .ok result final)
    (htelescope : TelescopeS env uvars nameOf trProj base ixDomains
      targetDomains count ixBody targetBody) :
    TrKExprS env uvars nameOf trProj base result
      (closeV targetDomains count targetBody) := by
  obtain ⟨exactFinal, hexact, _, _⟩ :=
    run_exact hcollision hsupported methods initial hintern hcover
  rw [run] at hexact
  cases hexact
  exact htelescope.close

/-- A complete production closure over the canonical flattened domains
establishes `CanonicalTypeS` for the returned generated header.  This is the
composition point consumed by the forthcoming `buildRecType` body proof. -/
theorem run_canonicalType
    {support : RunSupport} (hcollision : support.CollisionFree)
    {source : VInductDecl} (generation : source.GenerationChecked)
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {ixDomains : Array (KExpr .anon)}
    {ixBody : KExpr .anon} {saved : Nat} {methods : Methods .anon}
    {initial final : TcState .anon}
    {generated : GeneratedRecursor .anon}
    (hsize : ixDomains.size = (canonicalDomains generation).size)
    (hsupported : RequestsSupported support ixDomains ixDomains.size ixBody)
    (hintern : initial.env.intern.WF)
    (hcover : support.CoversIntern initial.env.intern)
    (run :
      (RecM.closeGeneratedRecursorForalls saved ixDomains ixDomains.size
        ixBody).run methods initial = .ok generated.ty final)
    (htelescope : TelescopeS env generation.recursor.uvars nameOf trProj []
      ixDomains (canonicalDomains generation) ixDomains.size ixBody
      (canonicalBody generation)) :
    GeneratedRecursorSemantics.CanonicalTypeS env nameOf trProj generation
      generated := by
  have translated := run_translation hcollision hsupported hintern hcover run
    htelescope
  rw [hsize, closeV_canonical generation] at translated
  exact translated

/-! ## Production `buildRecType` composition -/

/-- Every successful `buildRecType` execution factors through the exact live
domain/body result and then the verified closure helper. No result expression
or intermediate state is supplied by the caller. -/
theorem buildRecType_decompose
    (di : Nat)
    (indInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m)) (univOffset : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : KExpr m)
    (run :
      (RecM.buildRecType di indInfos blockInds flat motiveTypes
        univOffset).run methods initial = .ok result final) :
    ∃ built afterBody,
      (RecM.buildGeneratedRecursorTypeBody di indInfos blockInds flat
        motiveTypes univOffset).run methods initial = .ok built afterBody ∧
      (RecM.closeGeneratedRecursorForalls built.saved built.domains
        built.domains.size built.body).run methods afterBody =
          .ok result final := by
  unfold RecM.buildRecType at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind
      ((RecM.buildGeneratedRecursorTypeBody di indInfos blockInds flat
        motiveTypes univOffset).run methods) _ initial = .ok result final
    at run
  unfold EStateM.bind at run
  cases bodyRun :
      (RecM.buildGeneratedRecursorTypeBody di indInfos blockInds flat
        motiveTypes univOffset).run methods initial with
  | error err afterBody =>
      rw [bodyRun] at run
      contradiction
  | ok built afterBody =>
      rw [bodyRun] at run
      exact ⟨built, afterBody, rfl, run⟩

/-- The exact postcondition still owed by the domain/body constructor. It is
operation-shaped: each open domain and the open return body are related at
their construction context, and finite support covers the subsequent concrete
closure requests. It does not assume a relation for the closed result. -/
structure CanonicalBodyS (support : RunSupport) (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    {source : VInductDecl} (generation : source.GenerationChecked)
    (built : RecM.GeneratedRecursorTypeBody .anon)
    (afterBody : TcState .anon) : Prop where
  size : built.domains.size = (canonicalDomains generation).size
  requests : RequestsSupported support built.domains built.domains.size
    built.body
  intern : afterBody.env.intern.WF
  cover : support.CoversIntern afterBody.env.intern
  telescope : TelescopeS env generation.recursor.uvars nameOf trProj []
    built.domains (canonicalDomains generation) built.domains.size built.body
    (canonicalBody generation)

/-- Once the actual domain/body run establishes its operation-shaped
postcondition, the real `buildRecType` execution returns a structurally
canonical Lean4Lean recursor type. This theorem closes all control-flow and
hash-consing obligations after that body boundary. -/
theorem buildRecType_canonical_of_body
    {support : RunSupport} (hcollision : support.CollisionFree)
    {source : VInductDecl} (generation : source.GenerationChecked)
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel}
    (di : Nat)
    (indInfos : Array
      (KId .anon × UInt64 × UInt64 × Array (KId .anon) × KExpr .anon))
    (blockInds : Array (KId .anon))
    (flat : Array (FlatBlockMember .anon))
    (motiveTypes : Array (KExpr .anon)) (univOffset : UInt64)
    (methods : Methods .anon) (initial final : TcState .anon)
    (generated : GeneratedRecursor .anon)
    (run :
      (RecM.buildRecType di indInfos blockInds flat motiveTypes
        univOffset).run methods initial = .ok generated.ty final)
    (bodyCanonical : ∀ built afterBody,
      (RecM.buildGeneratedRecursorTypeBody di indInfos blockInds flat
        motiveTypes univOffset).run methods initial = .ok built afterBody →
      CanonicalBodyS support env nameOf trProj generation built afterBody) :
    GeneratedRecursorSemantics.CanonicalTypeS env nameOf trProj generation
      generated := by
  obtain ⟨built, afterBody, bodyRun, closeRun⟩ :=
    buildRecType_decompose di indInfos blockInds flat motiveTypes univOffset
      methods initial final generated.ty run
  have hbody := bodyCanonical built afterBody bodyRun
  exact run_canonicalType hcollision generation hbody.size hbody.requests
    hbody.intern hbody.cover closeRun hbody.telescope

end GeneratedRecursorTypeClosure

end Ix.Tc
