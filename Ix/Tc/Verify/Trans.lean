import Ix.Tc.Verify.Subst
import Ix.Tc.Verify.VLCtx
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Lemmas

/-!
# `TrKExprS` — the KExpr ↔ VExpr translation relation (M2)

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
  theorem (`TrKExprS.eraseMeta`), stated over a generic mode.
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
    fields are ignored (see `TrKExprS.eraseMeta`). -/
inductive TrKExprS {m : Mode} : KVLCtx → KExpr m → VExpr → Prop
  | var {Δ : KVLCtx} {i : UInt64} {nm : m.F Name} {md : ExprInfo m}
      {e A : VExpr} :
    Δ.find? (.inl i.toNat) = some (e, A) →
    TrKExprS Δ (.var i nm md) e
  | fvar {Δ : KVLCtx} {fv : FVarId} {nm : m.F Name} {md : ExprInfo m}
      {e A : VExpr} :
    Δ.find? (.inr fv) = some (e, A) →
    TrKExprS Δ (.fvar fv nm md) e
  | sort {Δ : KVLCtx} {u : KUniv m} {md : ExprInfo m} :
    (KUniv.toVLevel u).WF uvars →
    TrKExprS Δ (.sort u md) (.sort u.toVLevel)
  | const {Δ : KVLCtx} {id : KId m} {us : Array (KUniv m)}
      {md : ExprInfo m} {c : Lean.Name} {ci : VConstant} :
    nameOf id.addr = some c →
    env.constants c = some ci →
    (∀ u ∈ us, (KUniv.toVLevel u).WF uvars) →
    us.size = ci.uvars →
    TrKExprS Δ (.const id us md) (.const c (us.toList.map KUniv.toVLevel))
  | app {Δ : KVLCtx} {f a : KExpr m} {md : ExprInfo m}
      {f' a' A B : VExpr} :
    env.HasType uvars Δ.toCtx f' (.forallE A B) →
    env.HasType uvars Δ.toCtx a' A →
    TrKExprS Δ f f' → TrKExprS Δ a a' →
    TrKExprS Δ (.app f a md) (.app f' a')
  | lam {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr} :
    env.IsType uvars Δ.toCtx ty' →
    TrKExprS Δ ty ty' →
    TrKExprS ((none, .vlam ty') :: Δ) body body' →
    TrKExprS Δ (.lam nm bi ty body md) (.lam ty' body')
  | all {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr} :
    env.IsType uvars Δ.toCtx ty' →
    env.IsType uvars (ty' :: Δ.toCtx) body' →
    TrKExprS Δ ty ty' →
    TrKExprS ((none, .vlam ty') :: Δ) body body' →
    TrKExprS Δ (.all nm bi ty body md) (.forallE ty' body')
  | letE {Δ : KVLCtx} {nm : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {ty' val' body' : VExpr} :
    env.HasType uvars Δ.toCtx val' ty' →
    TrKExprS Δ ty ty' → TrKExprS Δ val val' →
    TrKExprS ((none, .vlet ty' val') :: Δ) body body' →
    TrKExprS Δ (.letE nm ty val body nd md) body'
  | prj {Δ : KVLCtx} {sid : KId m} {field : UInt64} {val : KExpr m}
      {md : ExprInfo m} {sName : Lean.Name} {e' e'' : VExpr} :
    nameOf sid.addr = some sName →
    TrKExprS Δ val e' →
    trProj Δ.toCtx sName field.toNat e' e'' →
    TrKExprS Δ (.prj sid field val md) e''
  | nat {Δ : KVLCtx} {n : Nat} {blob : Address} {md : ExprInfo m} :
    env.ContainsLits (.natVal n) →
    TrKExprS Δ (.nat n blob md) (.natLit n)
  | str {Δ : KVLCtx} {s : String} {blob : Address} {md : ExprInfo m} :
    env.ContainsLits (.strVal s) →
    TrKExprS Δ (.str s blob md) (.trLiteral (.strVal s))

/-- The translation is metadata-blind: erasing to the anon twin
    translates to the SAME `VExpr`. (With `KExpr.eraseMeta_anon` this
    also means anon statements subsume meta ones — the v1 checker's
    scope.) -/
theorem TrKExprS.eraseMeta {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (h : TrKExprS env uvars nameOf trProj Δ e e') :
    TrKExprS env uvars nameOf trProj Δ e.eraseMeta e' := by
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

/-! ### Weakening: `liftSpec` corresponds to `VExpr.liftN`

Mirror of upstream `VLCtx.BVLift`/`TrExprS.weakBV`. The four-index
split is the crux: `dn`/`dk` count context ENTRIES (KExpr de Bruijn
indices see every binder, lets included — exactly `liftSpec`'s
`shift`/`cutoff`), while `n`/`k` are the inserted DEPTH sums (`vlet`s
are depth-0 on the `VExpr` side — exactly `VExpr.liftN`'s amounts).

The master is stated at anon over the walker's `UInt64` arguments with
a `Nat` bridge; the single bound `Δ'.bvars + e.size < UInt64.size`
covers both the rebuilt-index no-wrap (via `find?_inl_lt` +
`KBVLift.bvars_eq` + `dk_le_bvars`) and the binder-descent
`cutoff + 1`. -/

namespace KVLCtx

@[simp] theorem liftVar_zero (v : Nat ⊕ FVarId) : liftVar 0 0 v = v := by
  cases v <;> simp [liftVar]

/-- `Δ'` is `Δ` with `dn` de Bruijn entries inserted at entry-position
    `dk`; the `VExpr` side lifts by the inserted depth sum `n` at
    position `k`. -/
inductive KBVLift : KVLCtx → KVLCtx → Nat → Nat → Nat → Nat → Prop
  | refl {Δ : KVLCtx} : KBVLift Δ Δ 0 0 0 0
  | skip {Δ Δ' : KVLCtx} {dn n : Nat} (d : VLocalDecl) :
    KBVLift Δ Δ' dn 0 n 0 →
    KBVLift Δ ((none, d) :: Δ') (dn + 1) 0 (n + d.depth) 0
  | cons {Δ Δ' : KVLCtx} {dn dk n k : Nat} (d : VLocalDecl) :
    KBVLift Δ Δ' dn dk n k →
    KBVLift ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') dn (dk + 1) n
      (k + d.depth)

theorem KBVLift.toCtx {Δ Δ' : KVLCtx} {dn dk n k : Nat}
    (W : KBVLift Δ Δ' dn dk n k) :
    Lean4Lean.Ctx.LiftN n k Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .zero []
  | @skip _ Δ' _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A =>
      generalize hΓ' : KVLCtx.toCtx Δ' = Γ' at ih
      let .zero As eq := ih
      simp [KVLCtx.toCtx, hΓ']
      exact .zero (A :: As) (eq ▸ rfl)
  | cons d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

theorem KBVLift.bvars_eq {Δ Δ' : KVLCtx} {dn dk n k : Nat}
    (W : KBVLift Δ Δ' dn dk n k) : Δ'.bvars = Δ.bvars + dn := by
  induction W with
  | refl => rfl
  | skip d _ ih => simp [KVLCtx.bvars, ih]; omega
  | cons d _ ih => simp [KVLCtx.bvars, ih]; omega

theorem KBVLift.dk_le_bvars {Δ Δ' : KVLCtx} {dn dk n k : Nat}
    (W : KBVLift Δ Δ' dn dk n k) : dk ≤ Δ'.bvars := by
  induction W with
  | refl => exact Nat.zero_le _
  | skip d _ ih => exact Nat.zero_le _
  | cons d _ ih => simp [KVLCtx.bvars]; omega

/-- A successful de Bruijn lookup is bounded by the entry count. -/
theorem find?_inl_lt : ∀ {Δ : KVLCtx} {j : Nat} {x : VExpr × VExpr},
    find? Δ (.inl j) = some x → j < Δ.bvars
  | [], _, _, h => by simp [find?] at h
  | (none, d) :: Δ, 0, _, _ => by simp [bvars]
  | (none, d) :: Δ, j+1, x, h => by
    simp only [find?, next, Option.bind_eq_bind] at h
    have : ∃ y, find? Δ (.inl j) = some y := by
      cases hf : find? Δ (.inl j) with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some y => exact ⟨y, rfl⟩
    obtain ⟨y, hy⟩ := this
    have := find?_inl_lt hy
    simp [bvars]
    omega
  | (some fv, d) :: Δ, j, x, h => by
    simp only [find?, next, Option.bind_eq_bind] at h
    have : ∃ y, find? Δ (.inl j) = some y := by
      cases hf : find? Δ (.inl j) with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some y => exact ⟨y, rfl⟩
    obtain ⟨y, hy⟩ := this
    have := find?_inl_lt hy
    simp [bvars]
    omega

/-- Lookup transport across an insertion — upstream `BVLift.find?`. -/
protected theorem KBVLift.find? {Δ Δ' : KVLCtx} {dn dk n k : Nat}
    {v : Nat ⊕ FVarId} {e A : VExpr}
    (W : KBVLift Δ Δ' dn dk n k) (H : find? Δ v = some (e, A)) :
    find? Δ' (liftVar dn dk v) = some (e.liftN n k, A.liftN n k) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | @skip _ Δ' _ _ d _ ih =>
    obtain v | fv := v <;> simp [find?, liftVar, next] <;>
      exact ⟨_, _, ih H, by simp [Lean4Lean.VExpr.liftN_liftN]⟩
  | cons d _ ih =>
    obtain (_ | v) | fv := v <;> simp [liftVar] <;>
      [ (simp [find?, next] at H ⊢; simp [← H]);
        split <;> (
          rename_i h
          simp [Nat.add_right_comm _ 1, find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          have := ih H
          simp [liftVar, h] at this
          refine ⟨_, _, this, ?_⟩);
        ( simp [find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          refine ⟨_, _, ih H, ?_⟩ )] <;>
      open Lean4Lean.VLocalDecl in
      cases d <;>
        simp [Lean4Lean.VExpr.lift_liftN', liftN, value, type, depth,
          Lean4Lean.VExpr.liftN]

end KVLCtx

/-- Closed literal encodings are `liftN`-invariant. -/
private theorem liftN_natLit (v n k : Nat) :
    (Lean4Lean.VExpr.natLit v).liftN n k = Lean4Lean.VExpr.natLit v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    show Lean4Lean.VExpr.app _ _ = _
    rw [show ((Lean4Lean.VExpr.natLit v).liftN n k)
        = Lean4Lean.VExpr.natLit v from ih]
    rfl

private theorem liftN_listCharLit (s : List Char) (n k : Nat) :
    (Lean4Lean.VExpr.listCharLit s).liftN n k
      = Lean4Lean.VExpr.listCharLit s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    show Lean4Lean.VExpr.app (Lean4Lean.VExpr.app _ (Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.natLit c.toNat).liftN n k)))
      ((Lean4Lean.VExpr.listCharLit s).liftN n k) = _
    rw [liftN_natLit, ih]
    rfl

private theorem liftN_trLiteral (l : Lean.Literal) (n k : Nat) :
    (Lean4Lean.VExpr.trLiteral l).liftN n k
      = Lean4Lean.VExpr.trLiteral l := by
  cases l with
  | natVal v => exact liftN_natLit v n k
  | strVal s =>
    show Lean4Lean.VExpr.app _ ((Lean4Lean.VExpr.listCharLit _).liftN n k) = _
    rw [liftN_listCharLit]
    rfl

/-- **Weakening** — `liftSpec` tracks the Theory's `VExpr.liftN` through
    the translation. Upstream `TrExprS.weakBV`, restated over the
    walker's `UInt64` arguments; `htp` is the trProj-weakening the
    abstract projection parameter must satisfy (upstream `TrProj.weakN`'s
    shape). -/
theorem TrKExprS.weakBV {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' → trProj Γ s i e e' →
      trProj Γ' s i (e.liftN n k) (e'.liftN n k))
    {Δ : KVLCtx} {e : KExpr .anon} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ e e') :
    ∀ {Δ' : KVLCtx} {dn dk n k : Nat} {shift cutoff : UInt64},
      KVLCtx.KBVLift Δ Δ' dn dk n k →
      shift.toNat = dn → cutoff.toNat = dk →
      Δ'.bvars + e.size < UInt64.size →
      TrKExprS env uvars nameOf trProj Δ'
        (KExpr.liftSpec e shift cutoff) (e'.liftN n k) := by
  induction H with
  | @var Δ i nm md e A h =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hW := W.find? h
    have hlt : i.toNat < Δ.bvars := KVLCtx.find?_inl_lt h
    have hbv : Δ'.bvars = Δ.bvars + dn := W.bvars_eq
    rw [KExpr.liftSpec]
    by_cases hge : i ≥ cutoff
    · have hnl : ¬ (i.toNat < dk) := by
        have := UInt64.le_iff_toNat_le.mp hge
        omega
      rw [if_pos hge, KExpr.mkVar_shape]
      refine .var (A := A.liftN n k) ?_
      have htn : (i + shift).toNat = i.toNat + dn := by
        rw [UInt64.toNat_add, hshift]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [htn]
      simpa [KVLCtx.liftVar, hnl] using hW
    · have hl : i.toNat < dk := by
        have : ¬ (cutoff.toNat ≤ i.toNat) := fun hh =>
          hge (UInt64.le_iff_toNat_le.mpr hh)
        omega
      rw [if_neg hge]
      refine .var (A := A.liftN n k) ?_
      simpa [KVLCtx.liftVar, hl] using hW
  | @fvar Δ fv nm md e A h =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hW := W.find? h
    exact .fvar (A := A.liftN n k) (by simpa [KVLCtx.liftVar] using hW)
  | @sort Δ u md h =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    exact .sort h
  | @const Δ id us md c ci h1 h2 h3 h4 =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    exact .const h1 h2 h3 h4
  | @app Δ f a md f' a' A B h1 h2 htf hta ihf iha =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hbig' : Δ'.bvars + (f.size + a.size + 1) < UInt64.size := hbig
    rw [KExpr.liftSpec, KExpr.mkApp_shape]
    exact .app (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx)
      (ihf W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (iha W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
  | @lam Δ nm bi ty body md ty' body' h1 htty htbody ihty ihbody =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hbig' : Δ'.bvars + (ty.size + body.size + 1) < UInt64.size := hbig
    have hdk : dk ≤ Δ'.bvars := W.dk_le_bvars
    have hc1 : (cutoff + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hcutoff]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.liftSpec, KExpr.mkLam_shape]
    exact .lam (h1.weakN henv W.toCtx)
      (ihty W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.cons (.vlam ty')) hshift hc1
        (by show Δ'.bvars + 1 + body.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @all Δ nm bi ty body md ty' body' h1 h2 htty htbody ihty ihbody =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hbig' : Δ'.bvars + (ty.size + body.size + 1) < UInt64.size := hbig
    have hdk : dk ≤ Δ'.bvars := W.dk_le_bvars
    have hc1 : (cutoff + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hcutoff]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.liftSpec, KExpr.mkAll_shape]
    exact .all (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx.succ)
      (ihty W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.cons (.vlam ty')) hshift hc1
        (by show Δ'.bvars + 1 + body.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @letE Δ nm ty val body nd md ty' val' body' h1 htty htval htbody
      ihty ihval ihbody =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hbig' :
        Δ'.bvars + (ty.size + val.size + body.size + 1) < UInt64.size :=
      hbig
    have hdk : dk ≤ Δ'.bvars := W.dk_le_bvars
    have hc1 : (cutoff + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hcutoff]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.liftSpec, KExpr.mkLet_shape]
    exact .letE (h1.weakN henv W.toCtx)
      (ihty W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihval W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.cons (.vlet ty' val')) hshift hc1
        (by show Δ'.bvars + 1 + body.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @prj Δ sid field val md sName e' e'' h1 htval htrp ihval =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    have hbig' : Δ'.bvars + (val.size + 1) < UInt64.size := hbig
    rw [KExpr.liftSpec, KExpr.mkPrj_shape]
    exact .prj h1
      (ihval W hshift hcutoff (Nat.lt_of_le_of_lt (by omega) hbig'))
      (htp W.toCtx htrp)
  | @nat Δ v blob md h =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    rw [show (Lean4Lean.VExpr.natLit v).liftN n k
        = Lean4Lean.VExpr.natLit v from liftN_natLit v n k]
    exact .nat h
  | @str Δ s blob md h =>
    intro Δ' dn dk n k shift cutoff W hshift hcutoff hbig
    rw [show (Lean4Lean.VExpr.trLiteral (.strVal s)).liftN n k
        = Lean4Lean.VExpr.trLiteral (.strVal s) from
      liftN_trLiteral (.strVal s) n k]
    exact .str h

/-! ### Instantiation: `substSpec` corresponds to `VExpr.inst`

Mirror of upstream `VLCtx.InstN`/`TrExprS.instN`, with one structural
simplification our formulation affords: upstream's variable transport
accumulates the substituted argument's lift through per-stage
single-entry weakenings, but `substSpec`'s hit arm produces
`liftSpec arg depth 0` in ONE shot — so the hit discharges with a
single `TrKExprS.weakBV` application through the `KInstN → KBVLift`
bridge (`toKBVLift`), and the remaining branches are plain `find?`
transports. -/

namespace KVLCtx

variable (Δ₀ : KVLCtx) (e₀ A₀ : VExpr) in
/-- `Δ₁` is the context still carrying the `vlam A₀` being substituted
    at entry-position `dk`; `Δ` is the result after instantiating it
    with `e₀`; `k` is the VExpr-side position. -/
inductive KInstN : Nat → Nat → KVLCtx → KVLCtx → Prop
  | zero : KInstN 0 0 ((none, .vlam A₀) :: Δ₀) Δ₀
  | succ {dk k : Nat} {Γ Γ' : KVLCtx} {d : VLocalDecl} :
    KInstN dk k Γ Γ' →
    KInstN (dk + 1) (k + d.depth) ((none, d) :: Γ)
      ((none, d.inst e₀ k) :: Γ')

private theorem depth_inst (d : VLocalDecl) (e₀ : VExpr) (k : Nat) :
    (d.inst e₀ k).depth = d.depth := by
  cases d <;> rfl

protected theorem KInstN.toCtx {Δ₀ : KVLCtx} {e₀ A₀ : VExpr}
    {dk k : Nat} {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Lean4Lean.Ctx.InstN Δ₀.toCtx e₀ A₀ k Δ₁.toCtx Δ.toCtx := by
  induction W with
  | zero => exact .zero
  | @succ dk k Γ Γ' d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

/-- The instantiated tail extends the base context by pure insertions —
    the bridge that lets the hit case reuse `TrKExprS.weakBV`. -/
theorem KInstN.toKBVLift {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    KBVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ dk k Γ Γ' d _ ih =>
    have := KBVLift.skip (d.inst e₀ k) ih
    rwa [depth_inst] at this

theorem KInstN.dk_le_bvars {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) : dk ≤ Δ.bvars := by
  induction W with
  | zero => exact Nat.zero_le _
  | succ _ ih =>
    simp [KVLCtx.bvars]
    omega

/-- `liftN` by an entry's depth commutes with `inst` above it. -/
private theorem liftN_depth_inst (d : VLocalDecl) (f e₀ : VExpr)
    (k : Nat) :
    (f.liftN d.depth).inst e₀ (k + d.depth)
      = (f.inst e₀ k).liftN d.depth := by
  cases d with
  | vlam A =>
    show (f.liftN 1).inst e₀ (k + 1) = (f.inst e₀ k).liftN 1
    exact (Lean4Lean.VExpr.lift_instN_lo f e₀).symm
  | vlet A v =>
    show (f.liftN 0).inst e₀ (k + 0) = (f.inst e₀ k).liftN 0
    simp

/-- The hit: the entry at `dk` is the substituted `vlam`, whose stored
    value instantiates to the argument lifted to the reference site. -/
theorem KInstN.find?_hit {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    ∀ {e' A : VExpr}, find? Δ₁ (.inl dk) = some (e', A) →
      e'.inst e₀ k = e₀.liftN k := by
  induction W with
  | zero =>
    intro e' A H
    simp [find?, next] at H
    obtain ⟨rfl, rfl⟩ := H
    rfl
  | @succ dk k Γ Γ' d _ ih =>
    intro e' A H
    simp [find?, next] at H
    obtain ⟨e, A', H, rfl, rfl⟩ := H
    rw [liftN_depth_inst, ih H, Lean4Lean.VExpr.liftN_liftN]

/-- Below the substitution site: indices are untouched and values
    instantiate pointwise. -/
theorem KInstN.find?_lt {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    ∀ {j : Nat} {e' A : VExpr}, j < dk →
      find? Δ₁ (.inl j) = some (e', A) →
      find? Δ (.inl j) = some (e'.inst e₀ k, A.inst e₀ k) := by
  induction W with
  | zero => omega
  | @succ dk k Γ Γ' d _ ih =>
    intro j e' A hj H
    match j with
    | 0 =>
      simp [find?, next] at H ⊢
      obtain ⟨rfl, rfl⟩ := H
      constructor <;>
        · cases d <;>
            simp [Lean4Lean.VLocalDecl.inst, Lean4Lean.VLocalDecl.value,
              Lean4Lean.VLocalDecl.type, Lean4Lean.VLocalDecl.depth,
              Lean4Lean.VExpr.inst, Lean4Lean.VExpr.instVar,
              Lean4Lean.VExpr.lift_instN_lo]
    | j + 1 =>
      simp [find?, next] at H ⊢
      obtain ⟨e, A', H, rfl, rfl⟩ := H
      refine ⟨_, _, ih (by omega) H, ?_, ?_⟩ <;>
        rw [liftN_depth_inst, depth_inst]

/-- Above the substitution site: indices shift down by one. -/
theorem KInstN.find?_gt {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    ∀ {j : Nat} {e' A : VExpr}, dk < j →
      find? Δ₁ (.inl j) = some (e', A) →
      find? Δ (.inl (j - 1)) = some (e'.inst e₀ k, A.inst e₀ k) := by
  induction W with
  | zero =>
    intro j e' A hj H
    match j, hj with
    | j + 1, _ =>
      simp [find?, next] at H
      obtain ⟨e, A', H, rfl, rfl⟩ := H
      simp only [Nat.add_sub_cancel]
      rw [show Lean4Lean.VLocalDecl.depth (.vlam A₀) = 1 from rfl,
        Lean4Lean.VExpr.inst_liftN, Lean4Lean.VExpr.inst_liftN]
      exact H
  | @succ dk k Γ Γ' d _ ih =>
    intro j e' A hj H
    match j, hj with
    | j' + 1, _ =>
      simp [find?, next] at H
      obtain ⟨e, A', H, rfl, rfl⟩ := H
      have hj' : dk < j' := by omega
      obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
      have := ih hj' H
      simp only [Nat.add_sub_cancel] at this ⊢
      simp [find?, next]
      refine ⟨_, _, this, ?_, ?_⟩ <;>
        rw [liftN_depth_inst, depth_inst]

/-- Fvar lookups are position-independent: values instantiate
    pointwise. -/
theorem KInstN.find?_fvar {Δ₀ : KVLCtx} {e₀ A₀ : VExpr} {dk k : Nat}
    {Δ₁ Δ : KVLCtx} (W : KInstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    ∀ {fv : FVarId} {e' A : VExpr},
      find? Δ₁ (.inr fv) = some (e', A) →
      find? Δ (.inr fv) = some (e'.inst e₀ k, A.inst e₀ k) := by
  induction W with
  | zero =>
    intro fv e' A H
    simp [find?, next] at H
    obtain ⟨e, A', H, rfl, rfl⟩ := H
    rw [show Lean4Lean.VLocalDecl.depth (.vlam A₀) = 1 from rfl,
      Lean4Lean.VExpr.inst_liftN, Lean4Lean.VExpr.inst_liftN]
    exact H
  | @succ dk k Γ Γ' d _ ih =>
    intro fv e' A H
    simp [find?, next] at H ⊢
    obtain ⟨e, A', H, rfl, rfl⟩ := H
    refine ⟨_, _, ih H, ?_, ?_⟩ <;>
      rw [liftN_depth_inst, depth_inst]

end KVLCtx

/-- Closed literal encodings are `inst`-invariant. -/
private theorem inst_natLit (v : Nat) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.natLit v).inst e₀ k = Lean4Lean.VExpr.natLit v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    show Lean4Lean.VExpr.app _ _ = _
    rw [show ((Lean4Lean.VExpr.natLit v).inst e₀ k)
        = Lean4Lean.VExpr.natLit v from ih]
    rfl

private theorem inst_listCharLit (s : List Char) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.listCharLit s).inst e₀ k
      = Lean4Lean.VExpr.listCharLit s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    show Lean4Lean.VExpr.app (Lean4Lean.VExpr.app _ (Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.natLit c.toNat).inst e₀ k)))
      ((Lean4Lean.VExpr.listCharLit s).inst e₀ k) = _
    rw [inst_natLit, ih]
    rfl

private theorem inst_trLiteral (l : Lean.Literal) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.trLiteral l).inst e₀ k
      = Lean4Lean.VExpr.trLiteral l := by
  cases l with
  | natVal v => exact inst_natLit v e₀ k
  | strVal s =>
    show Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.listCharLit _).inst e₀ k) = _
    rw [inst_listCharLit]
    rfl

/-- **Instantiation** — `substSpec` tracks the Theory's `VExpr.inst`
    through the translation. Upstream `TrExprS.instN`; `htp`/`htpI` are
    the weakening/instantiation closure the abstract projection
    parameter must satisfy (upstream's `TrProj.weakN`/`TrProj.instN`,
    both sorried there). -/
theorem TrKExprS.instN {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' → trProj Γ s i e e' →
      trProj Γ' s i (e.liftN n k) (e'.liftN n k))
    (htpI : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
      {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → trProj Γ₁ s i e e' →
      trProj Γ s i (e.inst e₀ k) (e'.inst e₀ k))
    {Δ₀ : KVLCtx} {arg : KExpr .anon} {e₀' A₀ : VExpr}
    (h₀ : TrKExprS env uvars nameOf trProj Δ₀ arg e₀')
    (t₀ : env.HasType uvars Δ₀.toCtx e₀' A₀)
    {Δ₁ : KVLCtx} {body : KExpr .anon} {body' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ₁ body body') :
    ∀ {Δ : KVLCtx} {dk k : Nat} {depth : UInt64},
      KVLCtx.KInstN Δ₀ e₀' A₀ dk k Δ₁ Δ →
      depth.toNat = dk →
      Δ.bvars + body.size + arg.size < UInt64.size →
      TrKExprS env uvars nameOf trProj Δ
        (KExpr.substSpec body arg depth) (body'.inst e₀' k) := by
  induction H with
  | @var Δ₁' i nm md e A h =>
    intro Δ dk k depth W hdepth hbig
    rw [KExpr.substSpec]
    by_cases heq : (i == depth) = true
    · have hik : i.toNat = dk := by rw [eq_of_beq heq]; exact hdepth
      rw [if_pos heq]
      rw [show e.inst e₀' k = e₀'.liftN k from
        W.find?_hit (by rw [← hik]; exact h)]
      exact TrKExprS.weakBV henv htp h₀ W.toKBVLift hdepth rfl
        (Nat.lt_of_le_of_lt (by omega) hbig)
    · by_cases hgt : i > depth
      · have hik : dk < i.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp hgt
          omega
        rw [if_neg heq, if_pos hgt, KExpr.mkVar_shape]
        refine .var (A := A.inst e₀' k) ?_
        have h1i : (1 : UInt64) ≤ i :=
          UInt64.le_iff_toNat_le.mpr (by
            rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
        rw [UInt64.toNat_sub_of_le i 1 h1i,
          show (1 : UInt64).toNat = 1 from rfl]
        exact W.find?_gt hik h
      · have hik : i.toNat < dk := by
          have hne : i.toNat ≠ depth.toNat := fun hh =>
            heq (beq_iff_eq.mpr (UInt64.toNat_inj.mp hh))
          have hnlt : ¬ (depth.toNat < i.toNat) := fun hh =>
            hgt (UInt64.lt_iff_toNat_lt.mpr hh)
          omega
        rw [if_neg heq, if_neg hgt]
        exact .var (A := A.inst e₀' k) (W.find?_lt hik h)
  | @fvar Δ₁' fv nm md e A h =>
    intro Δ dk k depth W hdepth hbig
    exact .fvar (A := A.inst e₀' k) (W.find?_fvar h)
  | @sort Δ₁' u md h =>
    intro Δ dk k depth W hdepth hbig
    exact .sort h
  | @const Δ₁' id us md c ci h1 h2 h3 h4 =>
    intro Δ dk k depth W hdepth hbig
    exact .const h1 h2 h3 h4
  | @app Δ₁' f a md f' a' A B h1 h2 htf hta ihf iha =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : Δ.bvars + (f.size + a.size + 1) + arg.size
        < UInt64.size := hbig
    rw [KExpr.substSpec, KExpr.mkApp_shape]
    exact .app (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx t₀)
      (ihf W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (iha W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
  | @lam Δ₁' nm bi ty body md ty' body' h1 htty htbody ihty ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : Δ.bvars + (ty.size + body.size + 1) + arg.size
        < UInt64.size := hbig
    have hdk : dk ≤ Δ.bvars := W.dk_le_bvars
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkLam_shape]
    exact .lam (h1.instN henv W.toCtx t₀)
      (ihty W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.succ (d := .vlam ty')) hc1
        (by show Δ.bvars + 1 + body.size + arg.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @all Δ₁' nm bi ty body md ty' body' h1 h2 htty htbody ihty ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : Δ.bvars + (ty.size + body.size + 1) + arg.size
        < UInt64.size := hbig
    have hdk : dk ≤ Δ.bvars := W.dk_le_bvars
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkAll_shape]
    exact .all (h1.instN henv W.toCtx t₀)
      (h2.instN henv W.toCtx.succ t₀)
      (ihty W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.succ (d := .vlam ty')) hc1
        (by show Δ.bvars + 1 + body.size + arg.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @letE Δ₁' nm ty val body nd md ty' val' body' h1 htty htval htbody
      ihty ihval ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' :
        Δ.bvars + (ty.size + val.size + body.size + 1) + arg.size
          < UInt64.size := hbig
    have hdk : dk ≤ Δ.bvars := W.dk_le_bvars
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkLet_shape]
    exact .letE (h1.instN henv W.toCtx t₀)
      (ihty W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihval W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (ihbody (W.succ (d := .vlet ty' val')) hc1
        (by show Δ.bvars + 1 + body.size + arg.size < UInt64.size
            exact Nat.lt_of_le_of_lt (by omega) hbig'))
  | @prj Δ₁' sid field val md sName e' e'' h1 htval htrp ihval =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : Δ.bvars + (val.size + 1) + arg.size < UInt64.size :=
      hbig
    rw [KExpr.substSpec, KExpr.mkPrj_shape]
    exact .prj h1
      (ihval W hdepth (Nat.lt_of_le_of_lt (by omega) hbig'))
      (htpI W.toCtx htrp)
  | @nat Δ₁' v blob md h =>
    intro Δ dk k depth W hdepth hbig
    rw [show (Lean4Lean.VExpr.natLit v).inst e₀' k
        = Lean4Lean.VExpr.natLit v from inst_natLit v e₀' k]
    exact .nat h
  | @str Δ₁' s blob md h =>
    intro Δ dk k depth W hdepth hbig
    rw [show (Lean4Lean.VExpr.trLiteral (.strVal s)).inst e₀' k
        = Lean4Lean.VExpr.trLiteral (.strVal s) from
      inst_trLiteral (.strVal s) e₀' k]
    exact .str h

/-- **Beta step at the API level**: substituting under one `vlam`.
    Upstream `TrExprS.inst`. -/
theorem TrKExprS.inst {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' → trProj Γ s i e e' →
      trProj Γ' s i (e.liftN n k) (e'.liftN n k))
    (htpI : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
      {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → trProj Γ₁ s i e e' →
      trProj Γ s i (e.inst e₀ k) (e'.inst e₀ k))
    {Δ : KVLCtx} {arg body : KExpr .anon} {e₀' A₀ body' : VExpr}
    (t₀ : env.HasType uvars Δ.toCtx e₀' A₀)
    (H : TrKExprS env uvars nameOf trProj ((none, .vlam A₀) :: Δ) body body')
    (h₀ : TrKExprS env uvars nameOf trProj Δ arg e₀')
    (hbig : Δ.bvars + body.size + arg.size < UInt64.size) :
    TrKExprS env uvars nameOf trProj Δ
      (KExpr.substSpec body arg 0) (body'.inst e₀') :=
  TrKExprS.instN henv htp htpI h₀ t₀ H .zero rfl hbig

/-! ### Context typing kit (upstream `VLCtx.WF` lemma transfers) -/

/-- `VLocalDecl.WF.hasType` re-keyed: the resolved (value, type) pair of
    the head entry is typed in the extended bare context. -/
theorem KVLCtx.vlocalDecl_wf_hasType {env : VEnv} {U : Nat} {Δ : KVLCtx}
    {ofv} : ∀ {d}, VLocalDecl.WF env U Δ.toCtx d →
    env.HasType U (KVLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

/-- `VLocalDecl.is_liftN` re-keyed: consing an entry lifts the bare
    context by the entry's depth. -/
theorem KVLCtx.is_liftN {Δ : KVLCtx} {ofv} :
    ∀ {d}, Lean4Lean.Ctx.LiftN (VLocalDecl.depth d) 0 Δ.toCtx
      (KVLCtx.toCtx ((ofv, d) :: Δ))
  | .vlam _ => .one
  | .vlet .. => .zero []

/-- `VLCtx.WF.find?_wf` re-keyed: a successful variable resolution is
    typed (the value against the type, both lifted to the use site). -/
theorem KVLCtx.WF.find?_wf {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Δ : KVLCtx}, KVLCtx.WF env U Δ → ∀ {v} {e A : VExpr},
      Δ.find? v = some (e, A) → env.HasType U Δ.toCtx e A
  | [], _, _, _, _, H => nomatch H
  | (_, _) :: _, hΔ, _, _, _, H => by
    unfold KVLCtx.find? at H
    split at H
    · cases H
      exact KVLCtx.vlocalDecl_wf_hasType hΔ.2.2
    · simp at H
      obtain ⟨e'', A'', H, rfl, rfl⟩ := H
      exact (KVLCtx.WF.find?_wf henv hΔ.1 H).weakN henv KVLCtx.is_liftN

/-- `VLCtx.WF.toCtx` re-keyed: the bare context of a well-formed
    translation context is `OnCtx`-well-formed. -/
theorem KVLCtx.WF.toCtx {env : VEnv} {U : Nat} :
    ∀ {Δ : KVLCtx}, KVLCtx.WF env U Δ →
      Lean4Lean.OnCtx Δ.toCtx (env.IsType U)
  | [], _ => ⟨⟩
  | (_, .vlam _) :: _, ⟨hΔ, _, hA⟩ => ⟨hΔ.toCtx, hA⟩
  | (_, .vlet ..) :: _, ⟨hΔ, _, _⟩ => hΔ.toCtx

/-- Upstream idiom (Verify/Typing/Lemmas.lean:216): context WF coerces
    to the bare-context `OnCtx` whenever a Theory lemma wants it. -/
instance {env : VEnv} {U : Nat} {Δ : KVLCtx} :
    Coe (KVLCtx.WF env U Δ) (Lean4Lean.OnCtx Δ.toCtx (env.IsType U)) :=
  ⟨KVLCtx.WF.toCtx⟩

/-- A term well-formed in the empty context is well-formed anywhere
    (closed-term weakening; the WF witness type is allowed to lift). -/
private theorem wf_weak0 {env : VEnv} (henv : env.Ordered) {U : Nat}
    {e : VExpr} (h : VExpr.WF env U [] e) (Γ : List VExpr) :
    VExpr.WF env U Γ e := by
  obtain ⟨A, hA⟩ := h
  have W : Lean4Lean.Ctx.LiftN Γ.length 0 [] (Γ ++ []) := .zero Γ rfl
  rw [List.append_nil] at W
  have h2 := hA.weakN henv W
  have hce : e.ClosedN 0 := (hA.closedN' henv.closed trivial).1
  rw [hce.liftN_eq (Nat.le_refl 0)] at h2
  exact ⟨_, h2⟩

/-! ### Well-typedness and the defeq quotient -/

/-- Every structural translate is well-typed (upstream `TrExprS.wf`).
    Two owned divergences surface as hypotheses: the literal rules are
    DIRECT (no `toConstructor` sub-derivation), so the typing of the
    closed literal encodings enters as `hlit` (M8's primitive-env
    invariant discharges it); the abstract `trProj` carries its own
    WF-closure `htpwf` (upstream `TrProj.wf` is itself sorry). -/
theorem TrKExprS.wf {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htpwf : ∀ {Γ s i e e'}, trProj Γ s i e e' →
      VExpr.WF env uvars Γ e → VExpr.WF env uvars Γ e')
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ e e')
    (hΔ : KVLCtx.WF env uvars Δ) :
    VExpr.WF env uvars Δ.toCtx e' := by
  induction H with
  | var h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | sort h1 => exact ⟨_, VEnv.HasType.sort h1⟩
  | @const _ _ us _ _ ci h1 h2 h3 h4 =>
    refine ⟨_, VEnv.HasType.const h2 ?_ ?_⟩
    · intro l hl
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      exact h3 u (by simpa using hu)
    · simpa using h4
  | app h1 h2 => exact ⟨_, h1.app h2⟩
  | @lam Δ' nm bi ty body md ty' body' h1 h2 h3 ihty ihbody =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ihbody ⟨hΔ, nofun, h1⟩
    exact ⟨_, h1'.lam h2'⟩
  | @all Δ' nm bi ty body md ty' body' h1 h2 h3 h4 ihty ihbody =>
    obtain ⟨_, h1'⟩ := h1
    obtain ⟨_, h2'⟩ := h2
    exact ⟨_, h1'.forallE h2'⟩
  | @letE Δ' nm ty val body nd md ty' val' body' h1 h2 h3 h4 ihty ihval
      ihbody =>
    exact ihbody ⟨hΔ, nofun, h1⟩
  | @prj Δ' sid field val md sName e1 e2 h1 h2 h3 ihval =>
    exact htpwf h3 (ihval hΔ)
  | nat h1 => exact wf_weak0 henv (hlit _ h1) _
  | str h1 => exact wf_weak0 henv (hlit _ h1) _

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- Defeq-quotiented translation (upstream `TrExpr`): some structural
    translate, defeq to the target. The home of the M5/M6 congruence
    API — needed already for `instL`, whose level simplifications are
    only `≈`-sound. -/
def TrKExpr {m : Mode} (Δ : KVLCtx) (e : KExpr m) (e' : VExpr) : Prop :=
  ∃ e₂, TrKExprS env uvars nameOf trProj Δ e e₂ ∧
    env.IsDefEqU uvars Δ.toCtx e₂ e'

/-- Embed the structural relation into the quotient (upstream
    `TrExprS.trExpr`) — the reflexive defeq is exactly well-typedness. -/
theorem TrKExprS.trKExpr {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htpwf : ∀ {Γ s i e e'}, trProj Γ s i e e' →
      VExpr.WF env uvars Γ e → VExpr.WF env uvars Γ e')
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ e e')
    (hΔ : KVLCtx.WF env uvars Δ) :
    TrKExpr env uvars nameOf trProj Δ e e' :=
  ⟨_, H, H.wf henv hlit htpwf hΔ⟩

theorem TrKExpr.wf {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExpr env uvars nameOf trProj Δ e e') :
    VExpr.WF env uvars Δ.toCtx e' :=
  let ⟨_, _, _, h⟩ := H
  ⟨_, h.hasType.2⟩

/-! ### `instL` transport for the translation context

Upstream `VLCtx.instL` lemma transfers, re-keyed (Lemmas.lean:524-547):
universe instantiation of a context commutes with `toCtx`, `fvars`,
`find?`, and preserves `WF` (re-basing the parameter count). -/

namespace KVLCtx

@[simp] theorem instL_fvars {ls : List VLevel} :
    ∀ {Δ : KVLCtx}, (Δ.instL ls).fvars = Δ.fvars
  | [] => rfl
  | (none, _) :: (Δ : KVLCtx) => by
    show fvars ((none, _) :: Δ.instL ls) = _
    simp [instL_fvars (Δ := Δ)]
  | (some fv, _) :: (Δ : KVLCtx) => by
    show fvars ((some fv, _) :: Δ.instL ls) = _
    simp [instL_fvars (Δ := Δ)]

@[simp] theorem instL_toCtx {ls : List VLevel} :
    ∀ {Δ : KVLCtx}, (Δ.instL ls).toCtx = Δ.toCtx.map (·.instL ls)
  | [] => rfl
  | (ofv, .vlam ty) :: (Δ : KVLCtx) => by
    show KVLCtx.toCtx ((ofv, (VLocalDecl.vlam ty).instL ls) :: Δ.instL ls)
        = _
    rw [VLocalDecl.instL]
    show ty.instL ls :: (Δ.instL ls).toCtx = _
    rw [instL_toCtx (Δ := Δ)]
    rfl
  | (ofv, .vlet ty v) :: (Δ : KVLCtx) => by
    show KVLCtx.toCtx ((ofv, (VLocalDecl.vlet ty v).instL ls) :: Δ.instL ls)
        = _
    rw [VLocalDecl.instL]
    show (Δ.instL ls).toCtx = _
    rw [instL_toCtx (Δ := Δ)]
    rfl

theorem find?_instL {ls : List VLevel} :
    ∀ {Δ : KVLCtx} {v} {e A : VExpr}, Δ.find? v = some (e, A) →
      (Δ.instL ls).find? v = some (e.instL ls, A.instL ls)
  | [], _, _, _, h => nomatch h
  | (ofv, d) :: (Δ : KVLCtx), v, e, A, h => by
    show KVLCtx.find? ((ofv, d.instL ls) :: Δ.instL ls) v = _
    unfold KVLCtx.find? at h ⊢
    split at h
    · cases h
      cases d <;>
        simp [VLocalDecl.instL, VLocalDecl.value, VLocalDecl.type,
          VExpr.instL]
    · simp at h ⊢
      obtain ⟨e'', A'', h, rfl, rfl⟩ := h
      refine ⟨_, _, find?_instL h, ?_, ?_⟩ <;>
        cases d <;>
          simp [VLocalDecl.instL, VLocalDecl.depth, VExpr.instL_liftN]

protected theorem WF.instL {env : VEnv} {U : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) :
    ∀ {Δ : KVLCtx}, KVLCtx.WF env ls.length Δ →
      KVLCtx.WF env U (Δ.instL ls)
  | [], _ => trivial
  | (ofv, d) :: (Δ : KVLCtx), ⟨h1, h2, h3⟩ => by
    refine ⟨WF.instL hls h1, ?_, ?_⟩
    · intro fv deps h
      have := h2 fv deps h
      simpa using this
    · have := VLocalDecl.WF.instL (d := d) hls h3
      rw [instL_toCtx]
      exact this

/-! ### Defeq contexts (upstream `VLCtx.IsDefEq`, re-keyed)

Pairwise-defeq translation contexts — the transport vocabulary for
`TrKExprS.uniq`/`defeqDFC` (which the binder-case congruence lemmas
need: quotient slack in a binder type shifts the context the body's
structural witness lives in). `VLocalDecl.IsDefEq` and its lemmas are
`VExpr`-level and import directly from the dep. -/

variable (env : VEnv) (U : Nat) in
inductive IsDefEq : KVLCtx → KVLCtx → Prop
  | nil : IsDefEq [] []
  | cons {Δ₁ Δ₂ : KVLCtx} {ofv} {d₁ d₂ : VLocalDecl} :
    IsDefEq Δ₁ Δ₂ →
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars) →
    Lean4Lean.VLocalDecl.IsDefEq env U Δ₁.toCtx d₁ d₂ →
    IsDefEq ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem IsDefEq.refl {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Δ : KVLCtx}, KVLCtx.WF env U Δ → IsDefEq env U Δ Δ
  | [], _ => .nil
  | (_, _) :: _, ⟨h1, h2, h3⟩ =>
    .cons (IsDefEq.refl henv h1) h2
      (Lean4Lean.VLocalDecl.IsDefEq.refl henv h1.toCtx h3)

theorem IsDefEq.defeqCtx {env : VEnv} {U : Nat} {Δ₁ Δ₂ : KVLCtx} :
    IsDefEq env U Δ₁ Δ₂ →
      VEnv.IsDefEqCtx env U [] Δ₁.toCtx Δ₂.toCtx
  | .nil => .zero
  | .cons h1 _ (.vlam h2) => .succ h1.defeqCtx h2
  | .cons h1 _ (.vlet ..) => h1.defeqCtx

theorem IsDefEq.fvars_eq {env : VEnv} {U : Nat} {Δ₁ Δ₂ : KVLCtx} :
    IsDefEq env U Δ₁ Δ₂ → Δ₁.fvars = Δ₂.fvars
  | .nil => rfl
  | .cons (ofv := none) h1 _ _ => by
    simp only [KVLCtx.fvars_cons_none]
    exact h1.fvars_eq
  | .cons (ofv := some fv) h1 _ _ => by
    simp only [KVLCtx.fvars_cons_some]
    rw [h1.fvars_eq]

theorem IsDefEq.wf {env : VEnv} {U : Nat} {Δ₁ Δ₂ : KVLCtx} :
    IsDefEq env U Δ₁ Δ₂ → KVLCtx.WF env U Δ₁
  | .nil => trivial
  | .cons h1 h2 h3 => ⟨h1.wf, h2, h3.wf⟩

theorem IsDefEq.symm {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Δ₁ Δ₂ : KVLCtx}, IsDefEq env U Δ₁ Δ₂ → IsDefEq env U Δ₂ Δ₁
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 h3 =>
    .cons (h1.symm henv) (h1.fvars_eq ▸ h2)
      (h3.symm.defeqDFC henv h1.defeqCtx)

theorem IsDefEq.find?_uniq {env : VEnv} {U : Nat} (henv : VEnv.WF env) :
    ∀ {Δ₁ Δ₂ : KVLCtx} {v} {e₁ A₁ e₂ A₂ : VExpr},
      IsDefEq env U Δ₁ Δ₂ →
      Δ₁.find? v = some (e₁, A₁) → Δ₂.find? v = some (e₂, A₂) →
      env.IsDefEqU U Δ₁.toCtx A₁ A₂ ∧ env.IsDefEq U Δ₁.toCtx e₁ e₂ A₁ := by
  intro Δ₁ Δ₂ v e₁ A₁ e₂ A₂ hΔ H1 H2
  match hΔ with
  | .cons hΔ h1 h2 =>
    match h2 with
    | .vlam (type₁ := B₁) (type₂ := B₂) h2 =>
      revert H1 H2
      unfold KVLCtx.find?
      split
      · rintro ⟨⟩ ⟨⟩
        exact ⟨⟨_, h2.weak henv⟩, .bvar .zero⟩
      · simp
        rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
        obtain ⟨h3, h4⟩ := find?_uniq henv hΔ H1' H2'
        exact ⟨h3.weakN henv .one, h4.weak henv⟩
    | .vlet h3 h4 =>
      revert H1 H2
      unfold KVLCtx.find?
      split
      · rintro ⟨⟩ ⟨⟩
        exact ⟨⟨_, h4⟩, h3⟩
      · simp
        rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
        simpa [Lean4Lean.VLocalDecl.depth] using find?_uniq henv hΔ H1' H2'

/-- Transport of `find?`-success along a context defeq (upstream
`VLCtx.IsDefEq.find?_defeqDFC`): a variable resolvable in `Δ₁` is
resolvable in `Δ₂` (with possibly different value/type — related by
`find?_uniq`). -/
theorem IsDefEq.find?_defeqDFC {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : KVLCtx} {v} {e₁ A₁ : VExpr},
      IsDefEq env U Δ₁ Δ₂ →
      Δ₁.find? v = some (e₁, A₁) →
      ∃ e₂ A₂, Δ₂.find? v = some (e₂, A₂) := by
  intro Δ₁ Δ₂ v e₁ A₁ hΔ H
  match hΔ with
  | .cons hΔ h1 h2 =>
    revert H
    unfold KVLCtx.find?
    split
    · exact fun _ => ⟨_, _, rfl⟩
    · simp
      rintro e A H rfl rfl
      obtain ⟨_, _, H⟩ := find?_defeqDFC hΔ H
      exact ⟨_, _, _, _, H, rfl, rfl⟩

end KVLCtx

/-! ### Uniqueness up to defeq, and context-defeq transport

Upstream `TrExprS.uniq`/`TrExprS.defeqDFC` — the two big inductions the
congruence API rides on. From here on the abstract `trProj`'s closure
properties travel as one `TrProjOK` bundle (upstream threads them
individually, each a sorry for its concrete `TrProj`; M8 discharges the
bundle once against the real projection rule). Our `sort`/`const` and
literal cases are SIMPLER than upstream: the total level translation
makes the two targets syntactically equal, so self-defeq suffices — no
`ofLevel` confluence needed. -/

/-- Closure properties of the abstract projection translation. Fields
    mirror upstream `TrProj.weakN/instN/wf/uniq/defeqDFC/instL` (all
    sorried upstream). `weakN`/`instN` restate the `htp`/`htpI`
    hypotheses of `TrKExprS.weakBV`/`instN` verbatim. -/
structure TrProjOK (env : VEnv) (uvars : Nat)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) :
    Prop where
  weakN : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
    {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' → trProj Γ s i e e' →
    trProj Γ' s i (e.liftN n k) (e'.liftN n k)
  instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
    {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → trProj Γ₁ s i e e' →
    trProj Γ s i (e.inst e₀ k) (e'.inst e₀ k)
  wf : ∀ {Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    trProj Γ s i e e' → VExpr.WF env uvars Γ e → VExpr.WF env uvars Γ e'
  uniq : ∀ {Γ₁ Γ₂ : List VExpr} {s : Lean.Name} {i : Nat}
    {e₁ e₂ e₁' e₂' : VExpr},
    VEnv.IsDefEqCtx env uvars [] Γ₁ Γ₂ →
    trProj Γ₁ s i e₁ e₁' → trProj Γ₂ s i e₂ e₂' →
    env.IsDefEqU uvars Γ₁ e₁ e₂ → env.IsDefEqU uvars Γ₁ e₁' e₂'
  defeqDFC : ∀ {Γ₁ Γ₂ : List VExpr} {s : Lean.Name} {i : Nat}
    {e₁ e₂ e' : VExpr},
    VEnv.IsDefEqCtx env uvars [] Γ₁ Γ₂ →
    env.IsDefEqU uvars Γ₁ e₁ e₂ → trProj Γ₁ s i e₁ e' →
    ∃ e₂', trProj Γ₂ s i e₂ e₂'
  instL : ∀ {U' : Nat} {ls : List VLevel} {Γ : List VExpr}
    {s : Lean.Name} {i : Nat} {e e' : VExpr},
    (∀ l ∈ ls, l.WF U') → trProj Γ s i e e' →
    trProj (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls)

/-- Uniqueness of structural translation up to defeq (upstream
    `TrExprS.uniq`): two translates of the same `KExpr` in
    pairwise-defeq contexts are definitionally equal. -/
theorem TrKExprS.uniq {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ₁ Δ₂ : KVLCtx} {e : KExpr m} {e₁ e₂ : VExpr}
    (hΔ : KVLCtx.IsDefEq env uvars Δ₁ Δ₂)
    (H1 : TrKExprS env uvars nameOf trProj Δ₁ e e₁)
    (H2 : TrKExprS env uvars nameOf trProj Δ₂ e e₂) :
    env.IsDefEqU uvars Δ₁.toCtx e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | var l1 =>
    let .var r1 := H2
    exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 =>
    let .fvar r1 := H2
    exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 =>
    let .sort _ := H2
    exact ⟨_, VEnv.HasType.sort l1⟩
  | @const _ _ us _ _ ci l1 l2 l3 l4 =>
    let .const r1 _ _ _ := H2
    cases l1.symm.trans r1
    refine ⟨_, VEnv.HasType.const l2 ?_ ?_⟩
    · intro l hl
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      exact l3 u (by simpa using hu)
    · simpa using l4
  | app l1 l2 _ _ ih3 ih4 =>
    let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    have ⟨_, l1'⟩ := l1
    let .lam _ r2 r3 := H2
    have hA := ih2 hΔ r2 |>.of_l henv hΔ.wf.toCtx l1'
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) r3
    exact ⟨_, .lamDF hA hb⟩
  | all l1 l2 _ _ ih3 ih4 =>
    have ⟨_, l1'⟩ := l1
    have ⟨_, l2'⟩ := l2
    let .all _ _ r3 r4 := H2
    have hA := ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) r4
      |>.of_l (Γ := _ :: _) henv ⟨hΔ.wf.toCtx, l1⟩ l2'
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    have hΓ := hΔ.wf.toCtx
    let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) r4
    exact .vlet (ih3 hΔ r3 |>.of_l henv hΓ l1)
      (ih2 hΔ r2 |>.of_l henv hΓ hb)
  | prj l1 _ l3 ih =>
    let .prj r1 r2 r3 := H2
    cases l1.symm.trans r1
    exact htp.uniq hΔ.defeqCtx l3 r3 (ih hΔ r2)
  | nat l1 =>
    let .nat _ := H2
    exact wf_weak0 henv.ordered (hlit _ l1) _
  | str l1 =>
    let .str _ := H2
    exact wf_weak0 henv.ordered (hlit _ l1) _

/-- Quotient-level uniqueness (upstream `TrExpr.uniq`). -/
theorem TrKExpr.uniq {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ₁ Δ₂ : KVLCtx} {e : KExpr m} {e₁ e₂ : VExpr}
    (hΔ : KVLCtx.IsDefEq env uvars Δ₁ Δ₂)
    (H1 : TrKExpr env uvars nameOf trProj Δ₁ e e₁)
    (H2 : TrKExpr env uvars nameOf trProj Δ₂ e e₂) :
    env.IsDefEqU uvars Δ₁.toCtx e₁ e₂ := by
  let ⟨_, H1, eq1⟩ := H1
  let ⟨_, H2, eq2⟩ := H2
  exact eq1.symm.trans henv hΔ.wf <|
    (H1.uniq henv hlit htp hΔ H2).trans henv hΔ.wf <|
    eq2.defeqDFC henv (hΔ.defeqCtx.symm henv)

/-- Structural translation transports along a context defeq (upstream
    `TrExprS.defeqDFC`): retranslate in the defeq context. -/
theorem TrKExprS.defeqDFC {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ₁ Δ₂ : KVLCtx} {e : KExpr m} {e₁ : VExpr}
    (hΔ : KVLCtx.IsDefEq env uvars Δ₁ Δ₂)
    (H : TrKExprS env uvars nameOf trProj Δ₁ e e₁) :
    ∃ e₂, TrKExprS env uvars nameOf trProj Δ₂ e e₂ := by
  induction H generalizing Δ₂ with
  | var h1 =>
    have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1
    exact ⟨_, .var h1⟩
  | fvar h1 =>
    have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1
    exact ⟨_, .fvar h1⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 h4 => exact ⟨_, .const h1 h2 h3 h4⟩
  | app h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h3'⟩ := ih3 hΔ
    let ⟨_, h4'⟩ := ih4 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf
      (h3'.uniq henv hlit htp (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ.symm henv).wf
      (h4'.uniq henv hlit htp (hΔ.symm henv) h4).symm
    exact ⟨_, .app h1 h2 h3' h4'⟩
  | lam h1 h2 h3 ih2 ih3 =>
    have ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := ih2 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf
      (h2'.uniq henv hlit htp (hΔ.symm henv) h2).symm
    have ht := (h2.uniq henv hlit htp hΔ h2').of_l henv hΔ.wf h1'
    let ⟨_, h3'⟩ := ih3 (hΔ.cons nofun <| .vlam ht)
    exact ⟨_, .lam h1 h2' h3'⟩
  | all h1 h2 h3 h4 ih3 ih4 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := h2
    let ⟨_, h3'⟩ := ih3 hΔ
    have ht := (h3.uniq henv hlit htp hΔ h3').of_l henv hΔ.wf h1'
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlam ht)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv (hΔ.defeqCtx.succ ht)
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf
      (h3'.uniq henv hlit htp (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ'.symm henv).wf
      (h4'.uniq henv hlit htp (hΔ'.symm henv) h4).symm
    exact ⟨_, .all h1 h2 h3' h4'⟩
  | letE h1 h2 h3 h4 ih2 ih3 ih4 =>
    let ⟨_, h2'⟩ := ih2 hΔ
    let ⟨_, h3'⟩ := ih3 hΔ
    have ⟨_, h0⟩ := h1.isType henv hΔ.wf
    have t0 := (h2.uniq henv hlit htp hΔ h2').of_l henv hΔ.wf h0
    have t1 := (h3.uniq henv hlit htp hΔ h3').of_l henv hΔ.wf h1
    have t2 := (h2'.uniq henv hlit htp (hΔ.symm henv) h2).symm
    have t3 := (h3'.uniq henv hlit htp (hΔ.symm henv) h3).symm
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlet t1 t0)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h0 := h0.defeqDFC henv hΔ.defeqCtx
    have h0 := h0.defeqU_l henv (hΔ.symm henv).wf t2
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf t3
    have h1 := h1.defeqU_r henv (hΔ.symm henv).wf t2
    exact ⟨_, .letE h1 h2' h3' h4'⟩
  | prj h1 h2 h3 ih =>
    let ⟨_, h2'⟩ := ih hΔ
    let ⟨_, h3'⟩ := htp.defeqDFC hΔ.defeqCtx
      (h2.uniq henv hlit htp hΔ h2') h3
    exact ⟨_, .prj h1 h2' h3'⟩
  | nat h1 => exact ⟨_, .nat h1⟩
  | str h1 => exact ⟨_, .str h1⟩

/-- `defeqDFC` into the quotient (upstream `TrExprS.defeqDFC'`): the
    retranslation is defeq to the original. -/
theorem TrKExprS.defeqDFC' {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ₁ Δ₂ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (hΔ : KVLCtx.IsDefEq env uvars Δ₁ Δ₂)
    (H : TrKExprS env uvars nameOf trProj Δ₁ e e') :
    TrKExpr env uvars nameOf trProj Δ₂ e e' := by
  let ⟨_, H'⟩ := H.defeqDFC henv hlit htp hΔ
  exact ⟨_, H', H'.uniq henv hlit htp (hΔ.symm henv) H⟩

/-! ### The quotient congruence API (upstream `TrExpr.*`)

Rebuild a quotient translate from quotient translates of the pieces.
The binder cases pay the toll the two inductions above were built for:
quotient slack in the binder type shifts the context the body's
structural witness lives in, so the witness is re-based with
`defeqDFC` and reconciled with `uniq`. No congruence lemmas for
`var`/`fvar`/`sort`/`const`/`nat`/`str` — leaves go through the
structural intro + `TrKExprS.trKExpr`. -/

/-- Widen the quotient along a defeq (upstream `TrExpr.defeq`). -/
theorem TrKExpr.defeq {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e₁ e₂ : VExpr}
    (hΔ : Lean4Lean.OnCtx Δ.toCtx (env.IsType uvars))
    (h1 : TrKExpr env uvars nameOf trProj Δ e e₁)
    (h2 : env.IsDefEqU uvars Δ.toCtx e₁ e₂) :
    TrKExpr env uvars nameOf trProj Δ e e₂ :=
  let ⟨_, H, h1⟩ := h1
  ⟨_, H, h1.trans henv hΔ h2⟩

/-- Application congruence (upstream `TrExpr.app`). -/
theorem TrKExpr.app {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    {m : Mode} {Δ : KVLCtx} {f a : KExpr m} {md : ExprInfo m}
    {f' a' A B : VExpr}
    (hΔ : Lean4Lean.OnCtx Δ.toCtx (env.IsType uvars))
    (h1 : env.HasType uvars Δ.toCtx f' (.forallE A B))
    (h2 : env.HasType uvars Δ.toCtx a' A)
    (h3 : TrKExpr env uvars nameOf trProj Δ f f')
    (h4 : TrKExpr env uvars nameOf trProj Δ a a') :
    TrKExpr env uvars nameOf trProj Δ (.app f a md) (.app f' a') :=
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, h4⟩ := h4
  have h3 := h3.of_r henv hΔ h1
  have h4 := h4.of_r henv hΔ h2
  ⟨_, .app h3.hasType.1 h4.hasType.1 s3 s4, _, h3.appDF h4⟩

/-- Lambda congruence (upstream `TrExpr.lam`). -/
theorem TrKExpr.lam {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr}
    (hΔ : KVLCtx.WF env uvars Δ)
    (h1 : env.IsType uvars Δ.toCtx ty')
    (h2 : TrKExpr env uvars nameOf trProj Δ ty ty')
    (h3 : TrKExpr env uvars nameOf trProj ((none, .vlam ty') :: Δ)
      body body') :
    TrKExpr env uvars nameOf trProj Δ (.lam nm bi ty body md)
      (.lam ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, _, h3⟩ := h3
  have hty := h2.symm.of_l henv hΔ h1
  have hΔΔ := KVLCtx.IsDefEq.cons (KVLCtx.IsDefEq.refl henv hΔ)
    (ofv := none) nofun (.vlam hty)
  let ⟨_, s3'⟩ := s3.defeqDFC henv hlit htp hΔΔ
  let ⟨_, h3'⟩ := s3.uniq henv hlit htp hΔΔ s3'
  ⟨_, .lam ⟨_, hty.hasType.2⟩ s2 s3', _,
    .symm <| .lamDF hty <| h3.symm.trans_l henv hΔΔ.wf.toCtx h3'⟩

/-- Pi congruence (upstream `TrExpr.forallE`; our ctor is `all`). -/
theorem TrKExpr.all {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ : KVLCtx} {nm : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m} {ty' body' : VExpr}
    (hΔ : KVLCtx.WF env uvars Δ)
    (h1 : env.IsType uvars Δ.toCtx ty')
    (h2 : env.IsType uvars (ty' :: Δ.toCtx) body')
    (h3 : TrKExpr env uvars nameOf trProj Δ ty ty')
    (h4 : TrKExpr env uvars nameOf trProj ((none, .vlam ty') :: Δ)
      body body') :
    TrKExpr env uvars nameOf trProj Δ (.all nm bi ty body md)
      (.forallE ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have hty := h3.symm.of_l henv hΔ h1
  have hΔΔ := KVLCtx.IsDefEq.cons (KVLCtx.IsDefEq.refl henv hΔ)
    (ofv := none) nofun (.vlam hty)
  let ⟨_, s4'⟩ := s4.defeqDFC henv hlit htp hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hlit htp hΔΔ s4'
  have h4 := h4.trans_r henv hΔΔ.wf h2 |>.symm.trans_l henv hΔΔ.wf h4'
  have h5 := h4.hasType.2.defeq_l henv hty
  ⟨_, .all ⟨_, hty.hasType.2⟩ ⟨_, h5⟩ s3 s4', _,
    .symm <| .forallEDF hty h4⟩

/-- Let congruence (upstream `TrExpr.letE`). -/
theorem TrKExpr.letE {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ : KVLCtx} {nm : m.F Name} {ty val body : KExpr m}
    {nd : Bool} {md : ExprInfo m} {ty' val' body' : VExpr}
    (hΔ : KVLCtx.WF env uvars Δ)
    (h1 : env.HasType uvars Δ.toCtx val' ty')
    (h2 : TrKExpr env uvars nameOf trProj Δ ty ty')
    (h3 : TrKExpr env uvars nameOf trProj Δ val val')
    (h4 : TrKExpr env uvars nameOf trProj ((none, .vlet ty' val') :: Δ)
      body body') :
    TrKExpr env uvars nameOf trProj Δ (.letE nm ty val body nd md)
      body' :=
  have ⟨_, h0⟩ := h1.isType henv hΔ
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have h1' := h1.defeqU_r henv hΔ h2.symm |>.defeqU_l henv hΔ h3.symm
  have h2' := h2.symm.of_l henv hΔ h0
  have h3' := h3.symm.of_l henv hΔ h1
  have hΔΔ := KVLCtx.IsDefEq.cons (KVLCtx.IsDefEq.refl henv hΔ)
    (ofv := none) nofun (.vlet h3' h2')
  let ⟨_, s4'⟩ := s4.defeqDFC henv hlit htp hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hlit htp hΔΔ s4'
  ⟨_, .letE h1' s2 s3 s4', _, h4'.symm.trans_l henv hΔ h4⟩

/-- Projection congruence (upstream `TrExpr.proj`, plus our
    address-resolution premise). -/
theorem TrKExpr.prj {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {Δ : KVLCtx} {sid : KId m} {field : UInt64}
    {val : KExpr m} {md : ExprInfo m} {sName : Lean.Name} {e' e'' : VExpr}
    (hΔ : KVLCtx.WF env uvars Δ)
    (h1 : nameOf sid.addr = some sName)
    (H : TrKExpr env uvars nameOf trProj Δ val e')
    (H2 : trProj Δ.toCtx sName field.toNat e' e'') :
    TrKExpr env uvars nameOf trProj Δ (.prj sid field val md) e'' :=
  let ⟨_, s2, h2⟩ := H
  have hΓ := (KVLCtx.IsDefEq.refl henv hΔ).defeqCtx
  have ⟨_, H2'⟩ := htp.defeqDFC hΓ h2.symm H2
  ⟨_, .prj h1 s2 H2', htp.uniq hΓ H2' H2 h2⟩

end Ix.Tc
