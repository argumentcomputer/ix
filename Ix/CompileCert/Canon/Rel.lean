import Ix.CompileCert.Canon.Const

/-!
# M7 L1: comparisons under two contexts

`compareExpr` reads its context only through `compareRef` (and the level rule, address map
and external mode, which the contexts compared here share). Any relation between results
that the comparator's combinators preserve (`ResRel`) therefore holds between the
comparisons under two contexts as soon as it holds between their reference leaves
(`compareExpr_rel`, `compareDef_rel`, `ctorP_rel`, `indP_rel`, `compareRecr_rel`,
`constP_rel`). Two instances:

* `StrongRel`: a strong result is the same under every context with the same in-block names
  (design document §3.2, "Strength"; §3.4 C3: caching strong results across rounds is sound).
  `constP_strong`.
* `EqRel`: an `eq` result is kept by a context that identifies at least the class indices
  the first one does (design document §3.3 (b): the coarser round's map factors through a
  finer consistent partition's). `constP_eq_mono`.

The per-tag equations of `compareExpr` (`cE_bvar` … `cE_proj`, `cE_contract`) are stated
here once.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind Rec ConstructorVal RecursorVal RecursorRule)

/-! ## Per-tag equations of `compareExpr` -/

section eqns
variable (c : CmpCtx) (xl yl : List Name)

theorem cE_bvar (i j : Nat) (h h' : Address) :
    compareExpr c xl yl (.bvar i h) (.bvar j h') = .ok ⟨true, compare i j⟩ := by
  rw [compareExpr.eq_def]; rfl

theorem cE_sort (u v : Level) (h h' : Address) :
    compareExpr c xl yl (.sort u h) (.sort v h') = compareLevel c.levels xl yl u v := by
  rw [compareExpr.eq_def]

theorem cE_const (xn yn : Name) (us vs : Array Level) (h h' : Address) :
    compareExpr c xl yl (.const xn us h) (.const yn vs h') =
      lexIf (compareLevels c.levels xl yl us.toList vs.toList) (compareRef c xn yn) := by
  rw [compareExpr.eq_def]; rfl

theorem cE_app (f a g b : Expr) (h h' : Address) :
    compareExpr c xl yl (.app f a h) (.app g b h') =
      SOrder.cmpM (compareExpr c xl yl f g) (compareExpr c xl yl a b) := by
  rw [compareExpr.eq_def]

theorem cE_lam (n n' : Name) (t b t' b' : Expr) (bi bi' : Lean.BinderInfo) (h h' : Address) :
    compareExpr c xl yl (.lam n t b bi h) (.lam n' t' b' bi' h') =
      SOrder.cmpM (compareExpr c xl yl t t') (compareExpr c xl yl b b') := by
  rw [compareExpr.eq_def]

theorem cE_forallE (n n' : Name) (t b t' b' : Expr) (bi bi' : Lean.BinderInfo) (h h' : Address) :
    compareExpr c xl yl (.forallE n t b bi h) (.forallE n' t' b' bi' h') =
      SOrder.cmpM (compareExpr c xl yl t t') (compareExpr c xl yl b b') := by
  rw [compareExpr.eq_def]

theorem cE_letE (n n' : Name) (t v b t' v' b' : Expr) (nd nd' : Bool) (h h' : Address) :
    compareExpr c xl yl (.letE n t v b nd h) (.letE n' t' v' b' nd' h') =
      SOrder.cmpM (compareExpr c xl yl t t')
        (SOrder.cmpM (compareExpr c xl yl v v')
          (SOrder.cmpM (compareExpr c xl yl b b') (pure ⟨true, compare nd nd'⟩))) := by
  rw [compareExpr.eq_def]

theorem cE_lit (a b : Lean.Literal) (h h' : Address) :
    compareExpr c xl yl (.lit a h) (.lit b h') = .ok ⟨true, compare a b⟩ := by
  rw [compareExpr.eq_def]; rfl

theorem cE_proj (xn yn : Name) (i j : Nat) (s s' : Expr) (h h' : Address) :
    compareExpr c xl yl (.proj xn i s h) (.proj yn j s' h') =
      SOrder.cmpM (compareRef c xn yn)
        (SOrder.cmpM (pure ⟨true, compare i j⟩) (compareExpr c xl yl s s')) := by
  rw [compareExpr.eq_def]

end eqns

/-! ## Relations the combinators preserve -/

/-- A relation between comparison results that is reflexive, holds from any failure, and is
preserved by the lexicographic combinators (`lexIf` with a first part common to both sides,
as in the code: the level arguments, the inductive header and the contract key do not read
the class indices). -/
structure ResRel (R : Except String SOrder → Except String SOrder → Prop) : Prop where
  refl : ∀ r, R r r
  err : ∀ e r', R (.error e) r'
  cmpM : ∀ {a a' b b'}, R a a' → R b b' → R (SOrder.cmpM a b) (SOrder.cmpM a' b')
  lexIf : ∀ {a b b'}, R b b' → R (lexIf a b) (lexIf a b')

theorem ResRel.zipCtx {R} (hR : ResRel R) {γ β : Type} {F G : γ × β → γ × β → Except String SOrder}
    (h : ∀ a b, R (F a b) (G a b)) (a b : γ × List β) : R (zipCtx F a b) (zipCtx G a b) := by
  obtain ⟨g, xs⟩ := a
  obtain ⟨g', ys⟩ := b
  induction xs generalizing ys with
  | nil => cases ys <;> exact hR.refl _
  | cons x xs ih =>
    cases ys with
    | nil => exact hR.refl _
    | cons y ys =>
      simp only [Canon.zipCtx, zipM_cons] at ih ⊢
      exact hR.cmpM (h _ _) (ih ys)

theorem compareExpr_rel {R} (hR : ResRel R) (c c' : CmpCtx) (hlv : c.levels = c'.levels)
    (href : ∀ x y, R (compareRef c x y) (compareRef c' x y)) (xl yl : List Name) :
    ∀ x y, R (compareExpr c xl yl x y) (compareExpr c' xl yl x y) := by
  suffices h : ∀ n x y, exprSize x + exprSize y < n →
      R (compareExpr c xl yl x y) (compareExpr c' xl yl x y) from
    fun x y => h _ x y (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y hs
    cases ex : ehd x with
    | none =>
      cases e : compareExpr c xl yl x y with
      | error err => exact hR.err _ _
      | ok r => exact absurd e (compareExpr_bad c xl yl x y (.inl ex) r)
    | some hx =>
      cases ey : ehd y with
      | none =>
        cases e : compareExpr c xl yl x y with
        | error err => exact hR.err _ _
        | ok r => exact absurd e (compareExpr_bad c xl yl x y (.inr ey) r)
      | some hy =>
        rw [compareExpr_strip c xl yl x y ex ey, compareExpr_strip c' xl yl x y ex ey]
        obtain ⟨hnx, hsx⟩ := ehd_spec ex
        obtain ⟨hny, hsy⟩ := ehd_spec ey
        have hs' : exprSize hx + exprSize hy < n + 1 := by omega
        by_cases ht : etag hx = etag hy
        · clear ex ey hsx hsy hs
          by_cases hm : ∃ dx x' h1 dy y' h2, hx = .mdata dx x' h1 ∧ hy = .mdata dy y' h2
          · obtain ⟨dx, x', h1, dy, y', h2, rfl, rfl⟩ := hm
            simp only [HN] at hnx hny
            rw [cE_contract c xl yl hnx hny, cE_contract c' xl yl hnx hny]
            simp only [exprSize_mdata] at hs'
            cases SemanticContract.read dx with
            | error e => exact hR.err _ _
            | ok kx =>
              cases SemanticContract.read dy with
              | error e => exact hR.err _ _
              | ok ky =>
                simp only [bind, Except.bind]
                exact hR.lexIf (ih x' y' (by omega))
          · cases hx <;> cases hy <;> simp only [etag] at ht <;> (try omega) <;>
              (try (simp only [HN] at hnx; done)) <;> (try (simp only [HN] at hny; done)) <;>
              (try simp only [exprSize_app, exprSize_lam, exprSize_forallE, exprSize_letE,
                exprSize_proj, exprSize_mdata] at hs') <;>
              first
                | (exfalso; exact hm ⟨_, _, _, _, _, _, rfl, rfl⟩)
                | (rw [cE_bvar, cE_bvar]; exact hR.refl _)
                | (rw [cE_sort, cE_sort, hlv]; exact hR.refl _)
                | (rw [cE_const, cE_const, hlv]; exact hR.lexIf (href _ _))
                | (rw [cE_app, cE_app]; exact hR.cmpM (ih _ _ (by omega)) (ih _ _ (by omega)))
                | (rw [cE_lam, cE_lam]; exact hR.cmpM (ih _ _ (by omega)) (ih _ _ (by omega)))
                | (rw [cE_forallE, cE_forallE]
                   exact hR.cmpM (ih _ _ (by omega)) (ih _ _ (by omega)))
                | (rw [cE_letE, cE_letE]
                   exact hR.cmpM (ih _ _ (by omega))
                     (hR.cmpM (ih _ _ (by omega)) (hR.cmpM (ih _ _ (by omega)) (hR.refl _))))
                | (rw [cE_lit, cE_lit]; exact hR.refl _)
                | (rw [cE_proj, cE_proj]
                   exact hR.cmpM (href _ _) (hR.cmpM (hR.refl _) (ih _ _ (by omega))))
        · rw [compareExpr_diff c xl yl hnx hny ht, compareExpr_diff c' xl yl hnx hny ht]
          exact hR.refl _

section consts
variable {R : Except String SOrder → Except String SOrder → Prop} (hR : ResRel R)
  (c c' : CmpCtx) (hlv : c.levels = c'.levels)
  (href : ∀ x y, R (compareRef c x y) (compareRef c' x y))
include hR hlv href

theorem compareDef_rel (x y : Def) : R (compareDef c x y) (compareDef c' x y) :=
  hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (compareExpr_rel hR c c' hlv href _ _ _ _) (compareExpr_rel hR c c' hlv href _ _ _ _)))

theorem ctorP_rel (xl yl : List Name) (x y : ConstructorVal) :
    R (ctorP c xl yl x y) (ctorP c' xl yl x y) :=
  hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (hR.refl _) (compareExpr_rel hR c c' hlv href _ _ _ _))))

theorem indP_rel (x y : Ind) : R (indP c x y) (indP c' x y) :=
  hR.lexIf (hR.cmpM (compareExpr_rel hR c c' hlv href _ _ _ _)
    (hR.zipCtx (fun a b => ctorP_rel hR c c' hlv href a.1 b.1 a.2 b.2) _ _))

theorem compareRecr_rel (x y : RecursorVal) : R (compareRecr c x y) (compareRecr c' x y) :=
  hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
      (hR.cmpM (compareExpr_rel hR c c' hlv href _ _ _ _)
        (hR.zipCtx (F := ruleC c) (G := ruleC c') (fun _ _ => hR.cmpM (hR.refl _)
          (compareExpr_rel hR c c' hlv href _ _ _ _)) (x.cnst.levelParams.toList, x.rules.toList)
          (y.cnst.levelParams.toList, y.rules.toList))))))))

theorem constP_rel (x y : MutConst) : R (constP c x y) (constP c' x y) := by
  cases x <;> cases y <;> simp only [constP]
  · exact compareDef_rel hR c c' hlv href _ _
  all_goals first
    | exact indP_rel hR c c' hlv href _ _
    | exact compareRecr_rel hR c c' hlv href _ _
    | exact hR.refl _

end consts

/-! ## Strength: strong results do not depend on the class indices -/

/-- A strong result is kept. -/
def StrongRel (r r' : Except String SOrder) : Prop := ∀ o, r = .ok ⟨true, o⟩ → r' = .ok ⟨true, o⟩

theorem strongRel : ResRel StrongRel where
  refl _ _ h := h
  err _ _ _ h := by cases h
  cmpM {a a' b b'} ha hb o h := by
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, y, hy, he⟩)⟩ := cmpM_ok.1 h
    · subst he
      exact cmpM_ok.2 ⟨_, ha _ hx, .inl ⟨hne, rfl⟩⟩
    · obtain ⟨sx, ox⟩ := x; obtain ⟨sy, oy⟩ := y
      simp only at heq; subst heq
      simp only [SOrder.mk.injEq] at he
      obtain ⟨hs, rfl⟩ := he
      cases sx <;> cases sy <;>
        first
          | exact absurd hs (by decide)
          | exact cmpM_ok.2 ⟨_, ha _ hx, .inr ⟨rfl, _, hb _ hy, rfl⟩⟩
  lexIf {a b b'} hb o h := by
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, hy⟩)⟩ := lexIf_ok.1 h
    · exact lexIf_ok.2 ⟨x, hx, .inl ⟨hne, he⟩⟩
    · exact lexIf_ok.2 ⟨x, hx, .inr ⟨heq, hb _ hy⟩⟩

/-- Two contexts with the same rule data and the same in-block names (the class indices may
differ): the contexts of the rounds of one refinement. -/
structure SameDom (c c' : CmpCtx) : Prop where
  levels : c.levels = c'.levels
  mode : c.mode = c'.mode
  addr : c.addr? = c'.addr?
  dom : ∀ n : Name, (c.mutCtx[n]?).isSome = (c'.mutCtx[n]?).isSome

theorem compareRef_strong {c c' : CmpCtx} (h : SameDom c c') (x y : Name) :
    StrongRel (compareRef c x y) (compareRef c' x y) := by
  intro o e
  cases hb : (x == y)
  · have dx := h.dom x
    have dy := h.dom y
    cases hx : c.mutCtx[x]? <;> cases hy : c.mutCtx[y]? <;>
      cases hx' : c'.mutCtx[x]? <;> cases hy' : c'.mutCtx[y]? <;>
      simp only [hx, hy, hx', hy', Option.isSome_none, Option.isSome_some, reduceCtorEq] at dx dy
    · rw [compareRef_out_out c hb hx hy] at e
      rw [compareRef_out_out c' hb hx' hy']
      unfold compareExternal at e ⊢
      rw [← h.mode, ← h.addr]; exact e
    · rw [compareRef_out_in c hb hx hy] at e; rw [compareRef_out_in c' hb hx' hy']; exact e
    · rw [compareRef_in_out c hb hx hy] at e; rw [compareRef_in_out c' hb hx' hy']; exact e
    · rw [compareRef_in_in c hb hx hy] at e; cases e
  · rw [compareRef_beq c hb] at e; rw [compareRef_beq c' hb]; exact e

/-- **Strength** (design document §3.2; §3.4 C3). A strong comparison of two constants is the
same under every context with the same in-block names: strong results may be cached across
the rounds of a refinement. -/
theorem constP_strong {c c' : CmpCtx} (h : SameDom c c') (x y : MutConst) (o : Ordering)
    (e : constP c x y = .ok ⟨true, o⟩) : constP c' x y = .ok ⟨true, o⟩ :=
  constP_rel strongRel c c' h.levels (compareRef_strong h) x y o e

theorem ctorP_strong {c c' : CmpCtx} (h : SameDom c c') (xl yl : List Name)
    (x y : ConstructorVal) (o : Ordering) (e : ctorP c xl yl x y = .ok ⟨true, o⟩) :
    ctorP c' xl yl x y = .ok ⟨true, o⟩ :=
  ctorP_rel strongRel c c' h.levels (compareRef_strong h) xl yl x y o e

/-! ## Equality is kept by a coarser identification -/

/-- An `eq` result is kept. -/
def EqRel (r r' : Except String SOrder) : Prop :=
  (∃ s, r = .ok ⟨s, .eq⟩) → ∃ s, r' = .ok ⟨s, .eq⟩

theorem eqRel : ResRel EqRel where
  refl _ h := h
  err _ _ h := by obtain ⟨s, h⟩ := h; cases h
  cmpM {a a' b b'} ha hb := by
    rintro ⟨s, h⟩
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, y, hy, he⟩)⟩ := cmpM_ok.1 h
    · subst he; exact absurd rfl hne
    · obtain ⟨sx, ox⟩ := x; obtain ⟨sy, oy⟩ := y
      simp only at heq; subst heq
      simp only [SOrder.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨s1, h1⟩ := ha ⟨sx, hx⟩
      obtain ⟨s2, h2⟩ := hb ⟨sy, hy⟩
      exact ⟨_, cmpM_ok.2 ⟨_, h1, .inr ⟨rfl, _, h2, rfl⟩⟩⟩
  lexIf {a b b'} hb := by
    rintro ⟨s, h⟩
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, hy⟩)⟩ := lexIf_ok.1 h
    · subst he; exact absurd rfl hne
    · obtain ⟨s2, h2⟩ := hb ⟨s, hy⟩
      exact ⟨s2, lexIf_ok.2 ⟨x, hx, .inr ⟨heq, h2⟩⟩⟩

/-- `c'` identifies at least the in-block names `c` identifies (same names in the block, same
rule data). -/
structure Coarser (c c' : CmpCtx) : Prop extends SameDom c c' where
  merge : ∀ (x y : Name) (nx ny : Nat), c.mutCtx[x]? = some nx → c.mutCtx[y]? = some ny → nx = ny →
    c'.mutCtx[x]? = c'.mutCtx[y]?

theorem compareRef_eq_mono {c c' : CmpCtx} (h : Coarser c c') (x y : Name) :
    EqRel (compareRef c x y) (compareRef c' x y) := by
  rintro ⟨s, e⟩
  cases hb : (x == y)
  · have dx := h.dom x
    have dy := h.dom y
    cases hx : c.mutCtx[x]? <;> cases hy : c.mutCtx[y]? <;>
      cases hx' : c'.mutCtx[x]? <;> cases hy' : c'.mutCtx[y]? <;>
      simp only [hx, hy, hx', hy', Option.isSome_none, Option.isSome_some, reduceCtorEq] at dx dy
    · rw [compareRef_out_out c hb hx hy] at e
      rw [compareRef_out_out c' hb hx' hy']
      unfold compareExternal at e ⊢
      rw [← h.mode, ← h.addr]; exact ⟨s, e⟩
    · rw [compareRef_out_in c hb hx hy] at e; cases e
    · rw [compareRef_in_out c hb hx hy] at e; cases e
    · rename_i nx ny nx' ny'
      rw [compareRef_in_in c hb hx hy] at e
      simp only [Except.ok.injEq, SOrder.mk.injEq] at e
      have := h.merge x y nx ny hx hy (Nat.compare_eq_eq.1 e.2)
      rw [hx', hy'] at this; cases this
      rw [compareRef_in_in c' hb hx' hy']
      exact ⟨false, by simp⟩
  · rw [compareRef_beq c' hb]; exact ⟨true, rfl⟩

/-- **Monotonicity of equality** (design document §3.3 (b)). Two constants equal under a
context stay equal under any coarser one. -/
theorem constP_eq_mono {c c' : CmpCtx} (h : Coarser c c') (x y : MutConst) {s}
    (e : constP c x y = .ok ⟨s, .eq⟩) : ∃ s', constP c' x y = .ok ⟨s', .eq⟩ :=
  constP_rel eqRel c c' h.levels (compareRef_eq_mono h) x y ⟨s, e⟩

end Ix.CompileCert.Canon
