import Ix.Tc.Verify.Subst
import Ix.Tc.Verify.VLCtx
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Lemmas

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
theorem TrKExpr.weakBV {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' → trProj Γ s i e e' →
      trProj Γ' s i (e.liftN n k) (e'.liftN n k))
    {Δ : KVLCtx} {e : KExpr .anon} {e' : VExpr}
    (H : TrKExpr env uvars nameOf trProj Δ e e') :
    ∀ {Δ' : KVLCtx} {dn dk n k : Nat} {shift cutoff : UInt64},
      KVLCtx.KBVLift Δ Δ' dn dk n k →
      shift.toNat = dn → cutoff.toNat = dk →
      Δ'.bvars + e.size < UInt64.size →
      TrKExpr env uvars nameOf trProj Δ'
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
single `TrKExpr.weakBV` application through the `KInstN → KBVLift`
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
    the bridge that lets the hit case reuse `TrKExpr.weakBV`. -/
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
theorem TrKExpr.instN {env : Lean4Lean.VEnv} {uvars : Nat}
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
    (h₀ : TrKExpr env uvars nameOf trProj Δ₀ arg e₀')
    (t₀ : env.HasType uvars Δ₀.toCtx e₀' A₀)
    {Δ₁ : KVLCtx} {body : KExpr .anon} {body' : VExpr}
    (H : TrKExpr env uvars nameOf trProj Δ₁ body body') :
    ∀ {Δ : KVLCtx} {dk k : Nat} {depth : UInt64},
      KVLCtx.KInstN Δ₀ e₀' A₀ dk k Δ₁ Δ →
      depth.toNat = dk →
      Δ.bvars + body.size + arg.size < UInt64.size →
      TrKExpr env uvars nameOf trProj Δ
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
      exact TrKExpr.weakBV henv htp h₀ W.toKBVLift hdepth rfl
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
theorem TrKExpr.inst {env : Lean4Lean.VEnv} {uvars : Nat}
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
    (H : TrKExpr env uvars nameOf trProj ((none, .vlam A₀) :: Δ) body body')
    (h₀ : TrKExpr env uvars nameOf trProj Δ arg e₀')
    (hbig : Δ.bvars + body.size + arg.size < UInt64.size) :
    TrKExpr env uvars nameOf trProj Δ
      (KExpr.substSpec body arg 0) (body'.inst e₀') :=
  TrKExpr.instN henv htp htpI h₀ t₀ H .zero rfl hbig

end Ix.Tc
