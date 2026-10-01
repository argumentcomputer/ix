module

public import ConLeche.Model.Annot.BitExtend
public import ConLeche.Verify.ProjSlots

public section

/-!
# `denoteMeta` across a tower-entry cons (task #175 wiring, W4c S6)

`denoteMeta_envExtend_mono` refutes a table head outright: its `hproj`
premise says the extension adds no entry at all, because a `.proj T i`
node with *no* entry reads by the pair fallback and would move under
an entry at `(T, i)`.  The direct install conses exactly such entries,
so its transport needs the refinement below: the extension may add
**one** family's slots `(T, i)`, and the subject has no `.proj T i`
node (`Expr.NoProjAt`, `Verify/ProjSlots.lean`, whose two dischargers
cover every stored expression).  Every other clause is
`denoteMeta_envExtend_mono`'s verbatim.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **The monotone crossing, tower-slot refined**: a successful prefix
reading of a subject with no `.proj T i` node is reproduced at an
extension whose only new tower slot is `(T, i)`. -/
theorem denoteMeta_envExtend_mono_at {env₀ env : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    {T : Name}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (j : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn j = none → env.findProj? sn j = some entry →
      sn = T) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e → (∀ j, Expr.NoProjAt T j e) →
      ∀ {ea : AnnotTerm}, denoteMeta acval env₀ φ d e = some ea →
        denoteMeta acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (j : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn j = some entry →
      env.findProj? sn j = some entry := by
    intro sn j entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₀) with
  | case1 d u => intro _ _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case2 d idx ty => intro _ _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteMeta, hf] at h
    rw [denoteMeta, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc _ ea h
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_forallE] at hc
    have hnp' := fun j => Expr.noProjAt_forallE.mp (hnp j)
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : ∀ j, Expr.NoProjAt T j (body.instantiate1 (.fvar d ty)) :=
      fun j => Expr.NoProjAt.instantiate1 (Expr.noProjAt_fvar.mpr (hnp' j).1) _ _ (hnp' j).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    rw [denoteMeta, ihty hc.1 (fun j => (hnp' j).1) hta, ihbody hcb hnpb hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_lam] at hc
    have hnp' := fun j => Expr.noProjAt_lam.mp (hnp j)
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : ∀ j, Expr.NoProjAt T j (body.instantiate1 (.fvar d ty)) :=
      fun j => Expr.NoProjAt.instantiate1 (Expr.noProjAt_fvar.mpr (hnp' j).1) _ _ (hnp' j).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    rw [denoteMeta, ihty hc.1 (fun j => (hnp' j).1) hta, ihbody hcb hnpb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc hnp ea h
    rw [constsBound_app] at hc
    have hnp' := fun j => Expr.noProjAt_app.mp (hnp j)
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    rw [denoteMeta, ihf hc.1 (fun j => (hnp' j).1) hfa, iha hc.2 (fun j => (hnp' j).2) haa]
    rfl
  | case9 d ty val body =>
    intro _ _ ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn j e ihe =>
    intro hc hnp ea h
    rw [constsBound_proj] at hc
    have hnp' := fun j' => Expr.noProjAt_proj.mp (hnp j')
    have hnpe : ∀ j', Expr.NoProjAt T j' e := fun j' => (hnp' j').2
    have hsnT : sn ≠ T := fun hsn => (hnp' j).1 ⟨hsn, rfl⟩
    obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · -- a table entry at the prefix persists unchanged
      rw [denoteMeta, ihe hc hnpe hea', hmono sn j entry hfp0]
      rfl
    · -- the table-free path: the slots the extension may have added
      -- are `T`'s, and the subject has no node there
      rw [denoteMeta, ihe hc hnpe hea']
      cases hfp : env.findProj? sn j with
      | none => exact hdec
      | some entry =>
        exact absurd (hproj sn j entry hnt0 hfp) hsnT
  | case11 d n hsup =>
    intro _ _ ea h
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-- A table cons adds exactly its own structure's slots: any lookup
new at the extension is the head's (task #175 S1). -/
theorem findProj?_cons_tower {env : Env} {tbl₀ : ConLeche.ProjTable} :
    ∀ (sn : Name) (j : Nat) (entry : ConLeche.ProjEntry),
      env.findProj? sn j = none →
      Env.findProj? ⟨.projInfo tbl₀ :: env.consts⟩ sn j = some entry →
      sn = tbl₀.structName := by
  intro sn j entry h0 h1
  by_cases hn : (ConLeche.ConstantInfo.projInfo tbl₀).name = ConLeche.projTableName sn
  · exact (ConLeche.projTableName_inj hn).symm
  · rw [ConLeche.Env.findProj?_cons_ne hn, h0] at h1
    exact nomatch h1

end ConLeche.Model
