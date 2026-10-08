import Ix.CompileCert.Opt.ExpansionOrigin

/-!
Universe scope of the actual independent source export.
No successful image/rewrite predicate is assumed to supply source export,
ingestion correspondence, referenced-spine arity or semantic conversion.
The original compiler endpoints and their domains are unchanged.
-/

namespace Ix.CompileCert.Opt.SourceScope

def LevelOccurs (k : Lean.Name) : Lean.Level → Prop
  | .param name => name = k
  | .succ u => LevelOccurs k u
  | .max u v | .imax u v => LevelOccurs k u ∨ LevelOccurs k v
  | _ => False

def ExprOccurs (k : Lean.Name) : Lean.Expr → Prop
  | .sort u => LevelOccurs k u
  | .const _ us => ∃ u ∈ us, LevelOccurs k u
  | .app f a => ExprOccurs k f ∨ ExprOccurs k a
  | .lam _ t b _ | .forallE _ t b _ => ExprOccurs k t ∨ ExprOccurs k b
  | .letE _ t v b _ => ExprOccurs k t ∨ ExprOccurs k v ∨ ExprOccurs k b
  | .proj _ _ e | .mdata _ e => ExprOccurs k e
  | _ => False

theorem exportUniv_scope {ps : List Lean.Name} {u : Lean.Level} {wire : Ixon.Univ}
    (exported : exportUniv ps u = .ok wire) {k : Lean.Name}
    (occurs : LevelOccurs k u) : k ∈ ps := by
  induction u generalizing wire with
  | zero | mvar => cases occurs
  | succ u ih =>
    simp only [exportUniv] at exported
    obtain ⟨inner, hi, _⟩ := except_bind_ok exported
    exact ih hi occurs
  | max u v ihu ihv =>
    simp only [exportUniv] at exported
    obtain ⟨left, hl, exported⟩ := except_bind_ok exported
    obtain ⟨right, hr, _⟩ := except_bind_ok exported
    exact occurs.elim (ihu hl) (ihv hr)
  | imax u v ihu ihv =>
    simp only [exportUniv] at exported
    obtain ⟨left, hl, exported⟩ := except_bind_ok exported
    obtain ⟨right, hr, _⟩ := except_bind_ok exported
    exact occurs.elim (ihu hl) (ihv hr)
  | param name =>
    have hk : name = k := occurs
    subst k
    cases hi : ps.idxOf? name with
    | none => simp [exportUniv, hi] at exported
    | some i =>
      have found : (ps.idxOf? name).isSome := by simp [hi]
      exact List.isSome_idxOf?.mp found

theorem exportSourceLevel_scope {ps : List Lean.Name} {u : Lean.Level}
    {out : Kernel.Level} (exported : exportSourceLevel ps u = .ok out)
    {k : Lean.Name} (occurs : LevelOccurs k u) : k ∈ ps := by
  unfold exportSourceLevel at exported
  obtain ⟨wire, hw, _⟩ := except_bind_ok exported
  exact exportUniv_scope hw occurs

theorem source_levels_scope {ps : List Lean.Name} {us : List Lean.Level}
    {out : List Kernel.Level} (exported : us.mapM (exportSourceLevel ps) = .ok out)
    {k : Lean.Name} {u : Lean.Level} (member : u ∈ us) (occurs : LevelOccurs k u) :
    k ∈ ps := by
  induction us generalizing out with
  | nil => cases member
  | cons a rest ih =>
    rw [List.mapM_cons] at exported
    obtain ⟨a', ha, exported⟩ := except_bind_ok exported
    obtain ⟨rest', hr, _⟩ := except_bind_ok exported
    rcases List.mem_cons.mp member with same | tail
    · subst u
      exact exportSourceLevel_scope ha occurs
    · exact ih hr tail

/-- The original source expression's complete universe scope, including every
constant level argument, binder annotation, let component and metadata body. -/
theorem exportSourceExpr_scope {ps : List Lean.Name} {e : Lean.Expr}
    {out : Kernel.Expr} (exported : exportSourceExpr ps e = .ok out)
    {k : Lean.Name} (occurs : ExprOccurs k e) : k ∈ ps := by
  induction e generalizing out with
  | sort u =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨u', hu, _⟩ := except_bind_ok exported
    exact exportSourceLevel_scope hu occurs
  | const name us =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨name', _, exported⟩ := except_bind_ok exported
    obtain ⟨us', hu, _⟩ := except_bind_ok exported
    obtain ⟨u, member, occurs⟩ := occurs
    exact source_levels_scope hu member occurs
  | app f a ihf iha =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨f', hf, exported⟩ := except_bind_ok exported
    obtain ⟨a', ha, _⟩ := except_bind_ok exported
    exact occurs.elim (ihf hf) (iha ha)
  | lam name t b info iht ihb =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨t', ht, exported⟩ := except_bind_ok exported
    obtain ⟨b', hb, _⟩ := except_bind_ok exported
    exact occurs.elim (iht ht) (ihb hb)
  | forallE name t b info iht ihb =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨t', ht, exported⟩ := except_bind_ok exported
    obtain ⟨b', hb, _⟩ := except_bind_ok exported
    exact occurs.elim (iht ht) (ihb hb)
  | letE name t v b nd iht ihv ihb =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨t', ht, exported⟩ := except_bind_ok exported
    obtain ⟨v', hv, exported⟩ := except_bind_ok exported
    obtain ⟨b', hb, _⟩ := except_bind_ok exported
    exact occurs.elim (iht ht) (fun h => h.elim (ihv hv) (ihb hb))
  | proj name index e ih =>
    simp only [exportSourceExpr, exportExprWith] at exported
    obtain ⟨name', _, exported⟩ := except_bind_ok exported
    obtain ⟨e', he, _⟩ := except_bind_ok exported
    exact ih he occurs
  | mdata data e ih => exact ih exported occurs
  | bvar | fvar | mvar | lit => cases occurs

/-- Reuse the existing exact source-header/value export theorem; safety and
duplicate-telescope guards remain those of exportSourceEntry itself. -/
theorem exportSourceEntry_defn_scope {source : Lean.DefinitionVal}
    {header : Kernel.ConstantVal} {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (exported : exportSourceEntry (.defnInfo source) = .ok (.defn header body hint))
    {k : Lean.Name} :
    (ExprOccurs k source.type → k ∈ source.levelParams) ∧
      (ExprOccurs k source.value → k ∈ source.levelParams) := by
  obtain ⟨headerImage, valueImage, _⟩ := exportSourceEntry_defn exported
  exact ⟨exportSourceExpr_scope headerImage.2.2, exportSourceExpr_scope valueImage⟩

/-- A theorem's body is checked source syntax; this does not introduce a
transparent semantic unfolding rule for theorem or proof values. -/
theorem exportSourceEntry_thm_scope {source : Lean.TheoremVal}
    {header : Kernel.ConstantVal} {body : Kernel.Expr}
    (exported : exportSourceEntry (.thmInfo source) = .ok (.thm header body))
    {k : Lean.Name} :
    (ExprOccurs k source.type → k ∈ source.levelParams) ∧
      (ExprOccurs k source.value → k ∈ source.levelParams) := by
  obtain ⟨headerImage, valueImage⟩ := exportSourceEntry_thm exported
  exact ⟨exportSourceExpr_scope headerImage.2.2, exportSourceExpr_scope valueImage⟩

end Ix.CompileCert.Opt.SourceScope
