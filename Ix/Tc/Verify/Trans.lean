import Ix.Tc.Verify.Subst
import Ix.Tc.Verify.VLCtx
import Lean4Lean.Verify.Typing.Expr

/-!
# `TrKExpr` — the KExpr ↔ VExpr translation relation (M2)

The Ix.Tc restatement of lean4lean's `TrExprS`, rule-for-rule where the
source languages agree, with the divergences owned deliberately
(roadmap rule 1):

- **Universes are total.** Anon-mode `KUniv` parameters are already de
  Bruijn indices, so M1's `KUniv.toVLevel` is a total function; where
  upstream threads `VLevel.ofLevel Us u = some u'` partiality (name
  lookup), our rules carry the explicit bound `(toVLevel u).WF uvars`.
- **Constants resolve by address.** An anon `KId` is a bare content
  address; the `nameOf : Address → Option Lean.Name` parameter abstracts
  the KEnv-side resolution that M3's `TrKEnv` will provide. The rule
  then mirrors upstream: the resolved name must be a declared `env`
  constant with matching universe arity.
- **Literals are first-class.** `KExpr` has `.nat`/`.str` constructors,
  so the owned rules relate them DIRECTLY to the Theory-side encodings
  (`VExpr.natLit`, `VExpr.trLiteral`) rather than recursively
  translating a `toConstructor` expansion as upstream's `lit` rule
  does; the `VEnv.ContainsLits` side conditions are kept so the later
  typing lemmas can invoke `VEnv.HasPrimitives`.
- **Projection is parameterized.** Upstream's `TrProj` is a literal
  `sorry` at `Verify/Typing/Expr.lean:67`; we own the rule but not yet
  the semantics, so the relation abstracts over
  `trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop`.
  Every lemma proven against the abstract parameter holds for whatever
  definition the inductive layer (M8) supplies; the struct name
  resolves from the `prj` node's `KId` through `nameOf`.
- **No `mdata` rule.** Anon `KExpr` has no mdata constructor (metadata
  lives in `ExprInfo`); instead the relation is metadata-blind by
  theorem (`TrKExpr.eraseMeta`), stated over a generic mode.
- **`letE` inlines.** As upstream: the translation of a `letE` is the
  translation of its body in a `vlet`-extended context — `find?`
  substitutes let values at use sites, and the result `VExpr` has no
  `letE` (the type has no such constructor).

Reused from the dep (VExpr-only content, fvar/Expr-agnostic):
`VLocalDecl.WF`, `VEnv.ContainsLits`, `VExpr.natLit`/`trLiteral`, and
eventually `VEnv.HasPrimitives`.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLevel VLocalDecl VEnv VConstant)

/-- Typing-level context well-formedness, mirroring upstream `VLCtx.WF`:
    fvar-structural freshness plus per-entry `VLocalDecl.WF` (types are
    types, let values are typed) against the tail's bare context. -/
def KVLCtx.WF (env : VEnv) (U : Nat) : KVLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : KVLCtx) =>
    KVLCtx.WF env U Δ ∧
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars) ∧
    Lean4Lean.VLocalDecl.WF env U Δ.toCtx d

theorem KVLCtx.WF.fvwf {env : VEnv} {U : Nat} :
    ∀ {Δ : KVLCtx}, KVLCtx.WF env U Δ → Δ.FVWF
  | [], h => h
  | _ :: _, ⟨h1, h2, _⟩ => ⟨h1.fvwf, h2⟩

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- Structural translation of a kernel expression into the Theory's
    `VExpr`, against a translation context `Δ`. Mode-generic: metadata
    fields are ignored (see `TrKExpr.eraseMeta`). -/
inductive TrKExpr {m : Mode} : KVLCtx → KExpr m → VExpr → Prop
  | var {Δ : KVLCtx} {i : UInt64} {nm : m.F Name} {md : ExprInfo m}
      {e A : VExpr} :
    Δ.find? (.inl i.toNat) = some (e, A) →
    TrKExpr Δ (.var i nm md) e
  | fvar {Δ : KVLCtx} {fv : FVarId} {nm : m.F Name} {md : ExprInfo m}
      {e A : VExpr} :
    Δ.find? (.inr fv) = some (e, A) →
    TrKExpr Δ (.fvar fv nm md) e
  | sort {Δ : KVLCtx} {u : KUniv m} {md : ExprInfo m} :
    (KUniv.toVLevel u).WF uvars →
    TrKExpr Δ (.sort u md) (.sort u.toVLevel)
  | const {Δ : KVLCtx} {id : KId m} {us : Array (KUniv m)}
      {md : ExprInfo m} {c : Lean.Name} {ci : VConstant} :
    nameOf id.addr = some c →
    env.constants c = some ci →
    (∀ u ∈ us, (KUniv.toVLevel u).WF uvars) →
    us.size = ci.uvars →
    TrKExpr Δ (.const id us md) (.const c (us.toList.map KUniv.toVLevel))
  | app {Δ : KVLCtx} {f a : KExpr m} {md : ExprInfo m}
      {f' a' A B : VExpr} :
    env.HasType uvars Δ.toCtx f' (.forallE A B) →
    env.HasType uvars Δ.toCtx a' A →
    TrKExpr Δ f f' → TrKExpr Δ a a' →
    TrKExpr Δ (.app f a md) (.app f' a')
  | lam {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr} :
    env.IsType uvars Δ.toCtx ty' →
    TrKExpr Δ ty ty' →
    TrKExpr ((none, .vlam ty') :: Δ) body body' →
    TrKExpr Δ (.lam nm bi ty body md) (.lam ty' body')
  | all {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr} :
    env.IsType uvars Δ.toCtx ty' →
    env.IsType uvars (ty' :: Δ.toCtx) body' →
    TrKExpr Δ ty ty' →
    TrKExpr ((none, .vlam ty') :: Δ) body body' →
    TrKExpr Δ (.all nm bi ty body md) (.forallE ty' body')
  | letE {Δ : KVLCtx} {nm : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {ty' val' body' : VExpr} :
    env.HasType uvars Δ.toCtx val' ty' →
    TrKExpr Δ ty ty' → TrKExpr Δ val val' →
    TrKExpr ((none, .vlet ty' val') :: Δ) body body' →
    TrKExpr Δ (.letE nm ty val body nd md) body'
  | prj {Δ : KVLCtx} {sid : KId m} {field : UInt64} {val : KExpr m}
      {md : ExprInfo m} {sName : Lean.Name} {e' e'' : VExpr} :
    nameOf sid.addr = some sName →
    TrKExpr Δ val e' →
    trProj Δ.toCtx sName field.toNat e' e'' →
    TrKExpr Δ (.prj sid field val md) e''
  | nat {Δ : KVLCtx} {n : Nat} {blob : Address} {md : ExprInfo m} :
    env.ContainsLits (.natVal n) →
    TrKExpr Δ (.nat n blob md) (.natLit n)
  | str {Δ : KVLCtx} {s : String} {blob : Address} {md : ExprInfo m} :
    env.ContainsLits (.strVal s) →
    TrKExpr Δ (.str s blob md) (.trLiteral (.strVal s))

/-- The translation is metadata-blind: erasing to the anon twin
    translates to the SAME `VExpr`. (With `KExpr.eraseMeta_anon` this
    also means anon statements subsume meta ones — the v1 checker's
    scope.) -/
theorem TrKExpr.eraseMeta {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (h : TrKExpr env uvars nameOf trProj Δ e e') :
    TrKExpr env uvars nameOf trProj Δ e.eraseMeta e' := by
  induction h with
  | var h =>
    rw [KExpr.eraseMeta]
    exact .var h
  | fvar h =>
    rw [KExpr.eraseMeta]
    exact .fvar h
  | @sort Δ u md h =>
    rw [KExpr.eraseMeta, show KUniv.toVLevel u = KUniv.toVLevel u.eraseMeta
      from (KUniv.toVLevel_eraseMeta u).symm]
    exact .sort (by rw [KUniv.toVLevel_eraseMeta]; exact h)
  | @const Δ id us md c ci h1 h2 h3 h4 =>
    rw [KExpr.eraseMeta, show us.toList.map KUniv.toVLevel
        = (us.map KUniv.eraseMeta).toList.map KUniv.toVLevel by
      rw [Array.toList_map, List.map_map,
        show KUniv.toVLevel ∘ KUniv.eraseMeta (m := m) = KUniv.toVLevel
          from funext fun u => KUniv.toVLevel_eraseMeta u]]
    exact .const h1 h2
      (fun u hu => by
        obtain ⟨v, hv, rfl⟩ := Array.mem_map.mp hu
        rw [KUniv.toVLevel_eraseMeta]
        exact h3 v hv)
      (by rw [Array.size_map]; exact h4)
  | app hf ha htf hta ihf iha =>
    rw [KExpr.eraseMeta]
    exact .app hf ha ihf iha
  | lam hty htty htbody ihty ihbody =>
    rw [KExpr.eraseMeta]
    exact .lam hty ihty ihbody
  | all hty hbody htty htbody ihty ihbody =>
    rw [KExpr.eraseMeta]
    exact .all hty hbody ihty ihbody
  | letE hval htty htval htbody ihty ihval ihbody =>
    rw [KExpr.eraseMeta]
    exact .letE hval ihty ihval ihbody
  | prj h1 htval htp ihval =>
    rw [KExpr.eraseMeta]
    exact .prj h1 ihval htp
  | nat h =>
    rw [KExpr.eraseMeta]
    exact .nat h
  | str h =>
    rw [KExpr.eraseMeta]
    exact .str h

end Ix.Tc
