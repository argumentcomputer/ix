import Ix.CompileCert.Canon.Simulate

/-!
# M7 L1, comparisons under a renaming of the constants

`ERen σ S e e'`: `e'` is `e` with every constant and projection-structure name `n` (each
satisfying `S`) replaced by `σ n`, binder names, binder infos and the cached hashes arbitrary
(the comparator reads none of them). `compareExpr_ren`: the comparison of two renamed
expressions under `c'` is related to the comparison of the originals under `c` by any relation
the comparator's combinators preserve (`ResRel2`) as soon as the reference comparisons are.
The same for the constants (`constP_ren`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Expr MutConst ConstructorVal RecursorVal RecursorRule)

/-- `e'` is `e` with the constant names renamed by `σ`. -/
inductive ERen (σ : Name → Name) (S : Name → Prop) : Expr → Expr → Prop
  | bvar (i : Nat) (h h' : Address) : ERen σ S (.bvar i h) (.bvar i h')
  | fvar (n : Name) (h h' : Address) : ERen σ S (.fvar n h) (.fvar n h')
  | mvar (n : Name) (h h' : Address) : ERen σ S (.mvar n h) (.mvar n h')
  | sort (u : Ix.Level) (h h' : Address) : ERen σ S (.sort u h) (.sort u h')
  | const (n : Name) (us : Array Ix.Level) (h h' : Address) :
      S n → ERen σ S (.const n us h) (.const (σ n) us h')
  | app {f a f' a' : Expr} (h h' : Address) :
      ERen σ S f f' → ERen σ S a a' → ERen σ S (.app f a h) (.app f' a' h')
  | lam {t b t' b' : Expr} (n n' : Name) (bi bi' : Lean.BinderInfo) (h h' : Address) :
      ERen σ S t t' → ERen σ S b b' → ERen σ S (.lam n t b bi h) (.lam n' t' b' bi' h')
  | forallE {t b t' b' : Expr} (n n' : Name) (bi bi' : Lean.BinderInfo) (h h' : Address) :
      ERen σ S t t' → ERen σ S b b' → ERen σ S (.forallE n t b bi h) (.forallE n' t' b' bi' h')
  | letE {t v b t' v' b' : Expr} (n n' : Name) (nd nd' : Bool) (h h' : Address) :
      ERen σ S t t' → ERen σ S v v' → ERen σ S b b' →
        ERen σ S (.letE n t v b nd h) (.letE n' t' v' b' nd' h')
  | lit (l : Lean.Literal) (h h' : Address) : ERen σ S (.lit l h) (.lit l h')
  | mdata {x x' : Expr} (d : Array (Name × Ix.DataValue)) (h h' : Address) :
      ERen σ S x x' → ERen σ S (.mdata d x h) (.mdata d x' h')
  | proj {s s' : Expr} (n : Name) (i : Nat) (h h' : Address) :
      S n → ERen σ S s s' → ERen σ S (.proj n i s h) (.proj (σ n) i s' h')

section
variable {σ : Name → Name} {S : Name → Prop}

theorem ERen.size {x x' : Expr} (r : ERen σ S x x') : exprSize x' = exprSize x := by
  induction r <;> simp only [exprSize] <;> omega

theorem ERen.etag {x x' : Expr} (r : ERen σ S x x') : etag x' = etag x := by
  cases r <;> rfl

theorem ERen.hn {x x' : Expr} (r : ERen σ S x x') : HN x → HN x' := by
  cases r <;> simp only [HN] <;> exact id

theorem ehd_ren {x x' : Expr} (r : ERen σ S x x') :
    (ehd x = none ∧ ehd x' = none) ∨
      ∃ hx hx', ehd x = some hx ∧ ehd x' = some hx' ∧ ERen σ S hx hx' := by
  induction r with
  | mdata d h h' r ih =>
    cases hm : SemanticContract.hasMetadata d
    · simp only [ehd, hm, Bool.false_eq_true, ↓reduceIte]; exact ih
    · exact .inr ⟨_, _, by simp only [ehd, hm, ↓reduceIte], by simp only [ehd, hm, ↓reduceIte],
        .mdata d h h' r⟩
  | fvar n h h' => exact .inl ⟨by simp only [ehd], by simp only [ehd]⟩
  | mvar n h h' => exact .inl ⟨by simp only [ehd], by simp only [ehd]⟩
  | bvar i h h' => exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .bvar i h h'⟩
  | sort u h h' => exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .sort u h h'⟩
  | const n us h h' hs => exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .const n us h h' hs⟩
  | app h h' r1 r2 => exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .app h h' r1 r2⟩
  | lam n n' bi bi' h h' r1 r2 =>
    exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .lam n n' bi bi' h h' r1 r2⟩
  | forallE n n' bi bi' h h' r1 r2 =>
    exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .forallE n n' bi bi' h h' r1 r2⟩
  | letE n n' nd nd' h h' r1 r2 r3 =>
    exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .letE n n' nd nd' h h' r1 r2 r3⟩
  | lit l h h' => exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .lit l h h'⟩
  | proj n i h h' hs r =>
    exact .inr ⟨_, _, by simp only [ehd], by simp only [ehd], .proj n i h h' hs r⟩

end

/-- Relations between results that the comparator's combinators preserve, failures related only
to failures. -/
structure ResRel2 (R : Except String SOrder → Except String SOrder → Prop) : Prop where
  refl : ∀ r, R r r
  err : ∀ e e', R (.error e) (.error e')
  cmpM : ∀ {a a' b b'}, R a a' → R b b' → R (SOrder.cmpM a b) (SOrder.cmpM a' b')
  lexIf : ∀ {a b b'}, R b b' → R (lexIf a b) (lexIf a b')

theorem contract_rel {R} (hR : ResRel2 R) (dx dy : Array (Name × Ix.DataValue))
    {A B : Except String SOrder} (hab : R A B) :
    R (do
        let cx ← SemanticContract.read dx
        let cy ← SemanticContract.read dy
        lexIf (pure ⟨true, compare cx.orderKey cy.orderKey⟩) A)
      (do
        let cx ← SemanticContract.read dx
        let cy ← SemanticContract.read dy
        lexIf (pure ⟨true, compare cx.orderKey cy.orderKey⟩) B) := by
  cases SemanticContract.read dx with
  | error e => exact hR.err _ _
  | ok kx =>
    cases SemanticContract.read dy with
    | error e => exact hR.err _ _
    | ok ky =>
      simp only [bind, Except.bind]
      exact hR.lexIf hab

/-- **Comparison of renamed expressions.** -/
theorem compareExpr_ren {R} (hR : ResRel2 R) (c c' : CmpCtx) (hlv : c.levels = c'.levels)
    {σ : Name → Name} {S : Name → Prop}
    (href : ∀ x y, S x → S y → R (compareRef c x y) (compareRef c' (σ x) (σ y))) (xl yl : List Name) :
    ∀ x y x' y', ERen σ S x x' → ERen σ S y y' →
      R (compareExpr c xl yl x y) (compareExpr c' xl yl x' y') := by
  suffices h : ∀ n x y x' y', exprSize x + exprSize y < n → ERen σ S x x' → ERen σ S y y' →
      R (compareExpr c xl yl x y) (compareExpr c' xl yl x' y') from
    fun x y x' y' rx ry => h _ x y x' y' (Nat.lt_succ_self _) rx ry
  intro n
  induction n with
  | zero => intro x y _ _ h; omega
  | succ n ih =>
    intro x y x' y' hs rx ry
    have bad : ∀ r r' : Except String SOrder, (∀ v, r ≠ .ok v) → (∀ v, r' ≠ .ok v) → R r r' := by
      intro r r' h1 h2
      cases r with
      | ok v => exact absurd rfl (h1 v)
      | error e =>
        cases r' with
        | ok v => exact absurd rfl (h2 v)
        | error e' => exact hR.err _ _
    rcases ehd_ren rx with ⟨ex, ex'⟩ | ⟨hx, hx', ex, ex', rhx⟩
    · exact bad _ _ (compareExpr_bad c xl yl x y (.inl ex)) (compareExpr_bad c' xl yl x' y' (.inl ex'))
    rcases ehd_ren ry with ⟨ey, ey'⟩ | ⟨hy, hy', ey, ey', rhy⟩
    · exact bad _ _ (compareExpr_bad c xl yl x y (.inr ey)) (compareExpr_bad c' xl yl x' y' (.inr ey'))
    rw [compareExpr_strip c xl yl x y ex ey, compareExpr_strip c' xl yl x' y' ex' ey']
    obtain ⟨hnx, hsx⟩ := ehd_spec ex
    obtain ⟨hny, hsy⟩ := ehd_spec ey
    have hnx' : HN hx' := rhx.hn hnx
    have hny' : HN hy' := rhy.hn hny
    have hs' : exprSize hx + exprSize hy < n + 1 := by omega
    by_cases ht : etag hx = etag hy
    · clear ex ey ex' ey' hsx hsy hs rx ry
      cases rhx <;> cases rhy <;> simp only [etag] at ht <;> (try omega) <;>
        (try (simp only [HN] at hnx; done)) <;> (try (simp only [HN] at hny; done)) <;>
        (try simp only [exprSize_app, exprSize_lam, exprSize_forallE, exprSize_letE,
          exprSize_proj, exprSize_mdata] at hs') <;>
        first
          | (rw [cE_bvar, cE_bvar]; exact hR.refl _)
          | (rw [cE_sort, cE_sort, hlv]; exact hR.refl _)
          | (rw [cE_const, cE_const, hlv]; exact hR.lexIf (href _ _ ‹_› ‹_›))
          | (rw [cE_app, cE_app]
             exact hR.cmpM (ih _ _ _ _ (by omega) ‹_› ‹_›) (ih _ _ _ _ (by omega) ‹_› ‹_›))
          | (rw [cE_lam, cE_lam]
             exact hR.cmpM (ih _ _ _ _ (by omega) ‹_› ‹_›) (ih _ _ _ _ (by omega) ‹_› ‹_›))
          | (rw [cE_forallE, cE_forallE]
             exact hR.cmpM (ih _ _ _ _ (by omega) ‹_› ‹_›) (ih _ _ _ _ (by omega) ‹_› ‹_›))
          | (rw [cE_letE, cE_letE]
             exact hR.cmpM (ih _ _ _ _ (by omega) ‹_› ‹_›)
               (hR.cmpM (ih _ _ _ _ (by omega) ‹_› ‹_›) (ih _ _ _ _ (by omega) ‹_› ‹_›)))
          | (rw [cE_lit, cE_lit]; exact hR.refl _)
          | (rw [cE_proj, cE_proj]
             exact hR.cmpM (href _ _ ‹_› ‹_›) (hR.cmpM (hR.refl _) (ih _ _ _ _ (by omega) ‹_› ‹_›)))
          | (simp only [HN] at hnx hny
             rw [cE_contract c xl yl hnx hny, cE_contract c' xl yl hnx hny]
             exact contract_rel hR _ _ (ih _ _ _ _ (by omega) ‹_› ‹_›))
    · have ht' : etag hx' ≠ etag hy' := by rw [rhx.etag, rhy.etag]; exact ht
      rw [compareExpr_diff c xl yl hnx hny ht, compareExpr_diff c' xl yl hnx' hny' ht', rhx.etag,
        rhy.etag]
      exact hR.refl _

/-! ## Constants -/

/-- Two lists related pointwise. -/
inductive LRel {α β : Type} (Rel : α → β → Prop) : List α → List β → Prop
  | nil : LRel Rel [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : Rel a b → LRel Rel as bs →
      LRel Rel (a :: as) (b :: bs)

theorem LRel.length {α β : Type} {Rel : α → β → Prop} {l : List α} {l' : List β} (h : LRel Rel l l') :
    l'.length = l.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ResRel2.zipCtx₂ {R} (hR : ResRel2 R) {γ β β' : Type}
    {F : γ × β → γ × β → Except String SOrder} {G : γ × β' → γ × β' → Except String SOrder}
    {Rel : β → β' → Prop} (g₁ g₂ : γ)
    (h : ∀ a b a' b', Rel a a' → Rel b b' → R (F (g₁, a) (g₂, b)) (G (g₁, a') (g₂, b'))) :
    ∀ {xs ys : List β} {xs' ys' : List β'}, LRel Rel xs xs' → LRel Rel ys ys' →
      R (zipCtx F (g₁, xs) (g₂, ys)) (zipCtx G (g₁, xs') (g₂, ys'))
  | _, _, _, _, .nil, .nil => hR.refl _
  | _, _, _, _, .nil, .cons _ _ => hR.refl _
  | _, _, _, _, .cons _ _, .nil => hR.refl _
  | _, _, _, _, .cons ha hx, .cons hb hy => by
    simp only [Canon.zipCtx, zipM_cons]
    exact hR.cmpM (h _ _ _ _ ha hb) (ResRel2.zipCtx₂ hR g₁ g₂ h hx hy)

section
variable (σ : Name → Name) (S : Name → Prop)

structure DefRen (x y : Ix.Def) : Prop where
  name : y.name = σ x.name
  kind : y.kind = x.kind
  lps : y.levelParams = x.levelParams
  type : ERen σ S x.type y.type
  value : ERen σ S x.value y.value

structure CtorRen (x y : ConstructorVal) : Prop where
  name : y.cnst.name = σ x.cnst.name
  lps : y.cnst.levelParams.size = x.cnst.levelParams.size
  cidx : y.cidx = x.cidx
  numParams : y.numParams = x.numParams
  numFields : y.numFields = x.numFields
  type : ERen σ S x.cnst.type y.cnst.type

structure IndRen (x y : Ix.Ind) : Prop where
  name : y.name = σ x.name
  lps : y.levelParams = x.levelParams
  numParams : y.numParams = x.numParams
  numIndices : y.numIndices = x.numIndices
  type : ERen σ S x.type y.type
  ctors : LRel (CtorRen σ S) x.ctors.toList y.ctors.toList

structure RuleRen (x y : RecursorRule) : Prop where
  nfields : y.nfields = x.nfields
  rhs : ERen σ S x.rhs y.rhs

structure RecRen (x y : RecursorVal) : Prop where
  name : y.cnst.name = σ x.cnst.name
  lps : y.cnst.levelParams = x.cnst.levelParams
  numParams : y.numParams = x.numParams
  numIndices : y.numIndices = x.numIndices
  numMotives : y.numMotives = x.numMotives
  numMinors : y.numMinors = x.numMinors
  k : y.k = x.k
  type : ERen σ S x.cnst.type y.cnst.type
  rules : LRel (RuleRen σ S) x.rules.toList y.rules.toList

/-- `y` is the member `x` renamed by `σ`: its own name, its constructors' names and every
constant it mentions. -/
def MRen : MutConst → MutConst → Prop
  | .defn x, .defn y => DefRen σ S x y
  | .indc x, .indc y => IndRen σ S x y
  | .recr x, .recr y => RecRen σ S x y
  | _, _ => False

end

section consts
variable {R : Except String SOrder → Except String SOrder → Prop} (hR : ResRel2 R)
  (c c' : CmpCtx) (hlv : c.levels = c'.levels) {σ : Name → Name} {S : Name → Prop}
  (href : ∀ x y, S x → S y → R (compareRef c x y) (compareRef c' (σ x) (σ y)))
include hR hlv href

theorem compareDef_ren {x y x' y' : Ix.Def} (hx : DefRen σ S x x') (hy : DefRen σ S y y') :
    R (compareDef c x y) (compareDef c' x' y') := by
  unfold compareDef
  rw [hx.kind, hy.kind, hx.lps, hy.lps]
  exact hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ hx.type hy.type)
      (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ hx.value hy.value)))

theorem ctorP_ren (xl yl : List Name) {x y x' y' : ConstructorVal} (hx : CtorRen σ S x x')
    (hy : CtorRen σ S y y') : R (ctorP c xl yl x y) (ctorP c' xl yl x' y') := by
  unfold ctorP
  rw [hx.lps, hy.lps, hx.cidx, hy.cidx, hx.numParams, hy.numParams, hx.numFields, hy.numFields]
  exact hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (hR.refl _) (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ hx.type hy.type))))

theorem indP_ren {x y x' y' : Ix.Ind} (hx : IndRen σ S x x') (hy : IndRen σ S y y') :
    R (indP c x y) (indP c' x' y') := by
  have hdr : indHdr x' y' = indHdr x y := by
    have e1 : x'.ctors.size = x.ctors.size := by
      rw [← Array.length_toList, ← Array.length_toList]; exact hx.ctors.length
    have e2 : y'.ctors.size = y.ctors.size := by
      rw [← Array.length_toList, ← Array.length_toList]; exact hy.ctors.length
    unfold indHdr
    rw [hx.lps, hy.lps, hx.numParams, hy.numParams, hx.numIndices, hy.numIndices, e1, e2]
  unfold indP
  rw [hdr, hx.lps, hy.lps]
  exact hR.lexIf (hR.cmpM (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ hx.type hy.type)
    (hR.zipCtx₂ (F := ctorC c) (G := ctorC c') x.levelParams.toList y.levelParams.toList
      (fun a b a' b' ha hb => ctorP_ren hR c c' hlv href _ _ ha hb) hx.ctors hy.ctors))

theorem compareRecr_ren {x y x' y' : RecursorVal} (hx : RecRen σ S x x') (hy : RecRen σ S y y') :
    R (compareRecr c x y) (compareRecr c' x' y') := by
  unfold compareRecr
  rw [hx.lps, hy.lps, hx.numParams, hy.numParams, hx.numIndices, hy.numIndices, hx.numMotives,
    hy.numMotives, hx.numMinors, hy.numMinors, hx.k, hy.k]
  exact hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
    (hR.cmpM (hR.refl _) (hR.cmpM (hR.refl _)
      (hR.cmpM (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ hx.type hy.type)
        (hR.zipCtx₂ (F := ruleC c) (G := ruleC c') x.cnst.levelParams.toList y.cnst.levelParams.toList
          (fun a b a' b' ha hb => by
            show R (compareRule c _ _ a b) (compareRule c' _ _ a' b')
            unfold compareRule
            rw [ha.nfields, hb.nfields]
            exact hR.cmpM (hR.refl _) (compareExpr_ren hR c c' hlv href _ _ _ _ _ _ ha.rhs hb.rhs))
          hx.rules hy.rules)))))))

/-- **Comparison of renamed members.** -/
theorem constP_ren {x y x' y' : MutConst} (hx : MRen σ S x x') (hy : MRen σ S y y') :
    R (constP c x y) (constP c' x' y') := by
  cases x <;> cases x' <;> simp only [MRen] at hx <;> cases y <;> cases y' <;>
    simp only [MRen] at hy <;> simp only [constP]
  · exact compareDef_ren hR c c' hlv href hx hy
  · exact hR.refl _
  · exact hR.refl _
  · exact hR.refl _
  · exact indP_ren hR c c' hlv href hx hy
  · exact hR.refl _
  · exact hR.refl _
  · exact hR.refl _
  · exact compareRecr_ren hR c c' hlv href hx hy

end consts

/-! ## Orders of results -/

/-- The same order (strength aside), failures alike. -/
def OrdIff (r r' : Except String SOrder) : Prop :=
  ∀ o, (∃ s, r = .ok ⟨s, o⟩) ↔ (∃ s, r' = .ok ⟨s, o⟩)

theorem cmpM_ord_to {a a' b b' : Except String SOrder}
    (ha : ∀ o, (∃ s, a = .ok ⟨s, o⟩) → ∃ s, a' = .ok ⟨s, o⟩)
    (hb : ∀ o, (∃ s, b = .ok ⟨s, o⟩) → ∃ s, b' = .ok ⟨s, o⟩) (o : Ordering) :
    (∃ s, SOrder.cmpM a b = .ok ⟨s, o⟩) → ∃ s, SOrder.cmpM a' b' = .ok ⟨s, o⟩ := by
  rintro ⟨s, h⟩
  obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, y, hy, he⟩)⟩ := cmpM_ok.1 h
  · subst he
    obtain ⟨s', ha'⟩ := ha o ⟨s, hx⟩
    exact ⟨s', cmpM_ok.2 ⟨_, ha', .inl ⟨hne, rfl⟩⟩⟩
  · obtain ⟨sx, ox⟩ := x; obtain ⟨sy, oy⟩ := y
    simp only at heq; subst heq
    simp only [SOrder.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
    obtain ⟨s1, ha'⟩ := ha .eq ⟨sx, hx⟩
    obtain ⟨s2, hb'⟩ := hb _ ⟨sy, hy⟩
    exact ⟨_, cmpM_ok.2 ⟨_, ha', .inr ⟨rfl, _, hb', rfl⟩⟩⟩

theorem lexIf_ord_to {a b b' : Except String SOrder}
    (hb : ∀ o, (∃ s, b = .ok ⟨s, o⟩) → ∃ s, b' = .ok ⟨s, o⟩) (o : Ordering) :
    (∃ s, lexIf a b = .ok ⟨s, o⟩) → ∃ s, lexIf a b' = .ok ⟨s, o⟩ := by
  rintro ⟨s, h⟩
  obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, hy⟩)⟩ := lexIf_ok.1 h
  · exact ⟨s, lexIf_ok.2 ⟨x, hx, .inl ⟨hne, he⟩⟩⟩
  · obtain ⟨s', hb'⟩ := hb o ⟨s, hy⟩
    exact ⟨s', lexIf_ok.2 ⟨x, hx, .inr ⟨heq, hb'⟩⟩⟩

theorem ordIff : ResRel2 OrdIff := by
  refine ⟨fun _ _ => Iff.rfl, fun _ _ _ => ⟨fun ⟨_, h⟩ => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩, ?_, ?_⟩
  · intro a a' b b' ha hb o
    exact ⟨cmpM_ord_to (fun o => (ha o).1) (fun o => (hb o).1) o,
      cmpM_ord_to (fun o => (ha o).2) (fun o => (hb o).2) o⟩
  · intro a b b' hb o
    exact ⟨lexIf_ord_to (fun o => (hb o).1) o, lexIf_ord_to (fun o => (hb o).2) o⟩

theorem map_ord_ok {r : Except String SOrder} {o : Ordering} :
    r.map (·.ord) = .ok o ↔ ∃ s, r = .ok ⟨s, o⟩ := by
  cases r with
  | error e =>
    constructor
    · intro h; cases h
    · rintro ⟨s, h⟩; cases h
  | ok v =>
    constructor
    · intro h
      have h' : v.ord = o := by simpa only [Except.map, Except.ok.injEq] using h
      exact ⟨v.strong, by rw [← h']⟩
    · rintro ⟨s, h⟩; cases h; rfl

theorem constOrd_to {r : Rules} {a₁ a₂ : Name → Option Address} {m₁ m₂ : MutCtx}
    {x y x' y' : MutConst}
    (h : ∀ mode o, (∃ s, constP (ctxOf r a₁ mode m₁) x y = .ok ⟨s, o⟩) →
      ∃ s, constP (ctxOf r a₂ mode m₂) x' y' = .ok ⟨s, o⟩) (o : Ordering) :
    constOrd r a₁ m₁ x y = .ok o → constOrd r a₂ m₂ x' y' = .ok o := by
  unfold constOrd
  cases r.tieBreak with
  | inline => intro hh; exact map_ord_ok.2 (h _ o (map_ord_ok.1 hh))
  | blind => intro hh; exact map_ord_ok.2 (h _ o (map_ord_ok.1 hh))
  | byAddress =>
    intro hh
    obtain ⟨b, hb, hh⟩ := except_bind_ok.1 hh
    rw [map_ord_ok.2 (h _ b (map_ord_ok.1 hb))]
    simp only [bind, Except.bind]
    by_cases hbe : (b != .eq) = true
    · simp only [hbe, ↓reduceIte] at hh ⊢; exact hh
    · simp only [hbe, Bool.false_eq_true, ↓reduceIte] at hh ⊢
      exact map_ord_ok.2 (h _ o (map_ord_ok.1 hh))

/-- **The round's comparison reads only the order of the constant comparisons.** -/
theorem constOrd_iff {r : Rules} {a₁ a₂ : Name → Option Address} {m₁ m₂ : MutCtx}
    {x y x' y' : MutConst}
    (h : ∀ mode, OrdIff (constP (ctxOf r a₁ mode m₁) x y) (constP (ctxOf r a₂ mode m₂) x' y'))
    (o : Ordering) : constOrd r a₁ m₁ x y = .ok o ↔ constOrd r a₂ m₂ x' y' = .ok o :=
  ⟨constOrd_to (fun mode o => (h mode o).1) o, constOrd_to (fun mode o => (h mode o).2) o⟩

/-! ## Renaming the members -/

theorem lrel_names {σ : Name → Name} {S : Name → Prop} {l l' : List ConstructorVal}
    (h : LRel (CtorRen σ S) l l') : l'.map (·.cnst.name) = (l.map (·.cnst.name)).map σ := by
  induction h with
  | nil => rfl
  | cons hc _ ih => simp only [List.map_cons, ih, hc.name]

theorem lrel_getElem? {α β : Type} {Rel : α → β → Prop} {l : List α} {l' : List β}
    (h : LRel Rel l l') : ∀ {k : Nat} {a : α}, l[k]? = some a → ∃ b, l'[k]? = some b ∧ Rel a b := by
  induction h with
  | nil => intro k a hk; simp only [List.getElem?_nil, reduceCtorEq] at hk
  | cons hab _ ih =>
    intro k a hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ⊢; subst hk
      exact ⟨_, rfl, hab⟩
    | succ k => simp only [List.getElem?_cons_succ] at hk ⊢; exact ih hk

section
variable {σ : Name → Name} {S : Name → Prop}

theorem keysOf_ren {a b : MutConst} (h : MRen σ S a b) : keysOf b = (keysOf a).map σ := by
  cases a <;> cases b <;> simp only [MRen] at h
  · simp only [keysOf, MutConst.name, MutConst.ctors, h.name, List.map_cons]; rfl
  · simp only [keysOf, MutConst.name, MutConst.ctors, h.name, List.map_cons, lrel_names h.ctors,
      List.map_map]
  · simp only [keysOf, MutConst.name, MutConst.ctors, h.name, List.map_cons]; rfl

theorem ctors_size_ren {a b : MutConst} (h : MRen σ S a b) : b.ctors.size = a.ctors.size := by
  cases a <;> cases b <;> simp only [MRen] at h
  · rfl
  · simp only [MutConst.ctors]
    rw [← Array.length_toList, ← Array.length_toList]; exact h.ctors.length
  · rfl

theorem ctor_ren {a b : MutConst} (h : MRen σ S a b) {k : Nat} {c : ConstructorVal}
    (hc : a.ctors[k]? = some c) : ∃ c', b.ctors[k]? = some c' ∧ c'.cnst.name = σ c.cnst.name := by
  cases a <;> cases b <;> simp only [MRen] at h
  · simp only [MutConst.ctors, Array.getElem?_empty, reduceCtorEq] at hc
  · simp only [MutConst.ctors] at hc ⊢
    rw [← Array.getElem?_toList] at hc ⊢
    obtain ⟨c', hc', hr⟩ := lrel_getElem? h.ctors hc
    exact ⟨c', hc', hr.name⟩
  · simp only [MutConst.ctors, Array.getElem?_empty, reduceCtorEq] at hc

end

section rename
variable {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst} {xs : List MutConst}
  (hmr : ∀ a ∈ xs, MRen σ S a (φ a)) (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
  (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))

theorem filter_true' : ∀ (l : List MutConst), l.filter (fun _ => true) = l
  | [] => rfl
  | a :: l => show a :: l.filter _ = a :: l by rw [filter_true' l]

theorem restrictC_true (C : List MutConst) : restrictC (fun _ => true) φ C = C.map φ := by
  unfold restrictC; rw [filter_true']

theorem restrictP_true (P : List (List MutConst)) :
    restrictP (fun _ => true) φ P = P.map (List.map φ) := by
  unfold restrictP
  congr 1
  funext C
  exact restrictC_true C

include hmr in
theorem keys_map_ren : ∀ (l : List MutConst), (∀ a ∈ l, a ∈ xs) →
    (l.map φ).flatMap keysOf = (l.flatMap keysOf).map σ
  | [], _ => rfl
  | a :: l, hl => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append,
      keysOf_ren (hmr a (hl a (List.mem_cons_self ..))),
      keys_map_ren l (fun b hb => hl b (List.mem_cons_of_mem _ hb))]

include hmr hS hinj in
theorem keysDistinct_ren {l : List MutConst} (hl : ∀ a ∈ l, a ∈ xs) (hk : KeysDistinct l) :
    KeysDistinct (l.map φ) := by
  unfold KeysDistinct at *
  rw [keys_map_ren hmr l hl, List.pairwise_map]
  refine hk.imp_of_mem fun {x y} hx hy e => ?_
  have sx : S x := by
    obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.1 hx; exact hS a (hl a ha) x hxa
  have sy : S y := by
    obtain ⟨a, ha, hya⟩ := List.mem_flatMap.1 hy; exact hS a (hl a ha) y hya
  rw [hinj x y sx sy]; exact e

theorem maxC_map (C : List MutConst) (hsz : ∀ m ∈ C, (φ m).ctors.size = m.ctors.size) :
    maxC (C.map φ) = maxC C := by
  unfold maxC
  rw [List.foldl_map]
  suffices h : ∀ (l : List MutConst) (acc : Nat), (∀ m ∈ l, (φ m).ctors.size = m.ctors.size) →
      l.foldl (fun mx m => max mx (φ m).ctors.size) acc = l.foldl (fun mx m => max mx m.ctors.size) acc from
    h C 0 hsz
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro acc h
    simp only [List.foldl_cons]
    rw [h a (List.mem_cons_self ..)]
    exact ih _ (fun m hm => h m (List.mem_cons_of_mem _ hm))


theorem offs_map : ∀ (P : List (List MutConst)), (∀ C ∈ P, ∀ m ∈ C, (φ m).ctors.size = m.ctors.size) →
    ∀ (j : Nat), offs (P.map (List.map φ)) j = offs P j := by
  intro P
  induction P with
  | nil => intro _ j; simp [offs, sumMaxC]
  | cons C P ih =>
    intro hsz j
    cases j with
    | zero => rw [offs_zero, offs_zero]
    | succ j =>
      rw [List.map_cons, offs_cons_succ, offs_cons_succ,
        ih (fun D hD => hsz D (List.mem_cons_of_mem _ hD)) j, maxC_map C (hsz C (List.mem_cons_self ..))]

end rename

theorem name_ren {σ : Name → Name} {S : Name → Prop} {a b : MutConst} (h : MRen σ S a b) :
    b.name = σ a.name := by
  cases a <;> cases b <;> simp only [MRen] at h
  · exact h.name
  · exact h.name
  · exact h.name

theorem any_map_ren {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y)) {x : Name} (hx : S x) :
    ∀ (l : List Name), (∀ k ∈ l, S k) → (l.map σ).any (· == σ x) = l.any (· == x)
  | [], _ => rfl
  | k :: l, hl => by
    simp only [List.map_cons, List.any_cons, hinj k x (hl k (List.mem_cons_self ..)) hx,
      any_map_ren hinj hx l (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))]

section rename2
variable {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst} {xs : List MutConst}
  (hmr : ∀ a ∈ xs, MRen σ S a (φ a)) (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
  (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
  (hext : ∀ x, S x → (∀ k ∈ xs.flatMap keysOf, (k == x) = false) → σ x = x)
  (hk : KeysDistinct xs)

include hmr hS hinj hk in
/-- **The context of the renamed partition** answers for a renamed name as the original
context does for the name. -/
theorem ctx_ren {P : List (List MutConst)} (hP : P.flatten.Perm xs) {x : Name} (hx : S x) :
    (MutConst.ctx (P.map (List.map φ)))[σ x]? = (MutConst.ctx P)[x]? := by
  have hkP : KeysDistinct P.flatten := hk.perm hP.symm
  have hinP : ∀ a ∈ P.flatten, a ∈ xs := fun a ha => hP.mem_iff.1 ha
  have hflat : (P.map (List.map φ)).flatten = P.flatten.map φ := List.map_flatten.symm
  have hkQ : KeysDistinct (P.map (List.map φ)).flatten := by
    rw [hflat]; exact keysDistinct_ren hmr hS hinj hinP hkP
  have hSkeys : ∀ k ∈ P.flatten.flatMap keysOf, S k := fun k hk' => by
    obtain ⟨a, ha, hka⟩ := List.mem_flatMap.1 hk'; exact hS a (hinP a ha) k hka
  cases hv : (MutConst.ctx P)[x]? with
  | some v =>
    obtain ⟨j, C, m, hC, hm, hxv⟩ := ctx_val hkP hv
    have hQ : (P.map (List.map φ))[j]? = some (C.map φ) := by rw [List.getElem?_map, hC]; rfl
    have hmQ : φ m ∈ C.map φ := List.mem_map_of_mem hm
    have hCP : C ∈ P := List.mem_of_getElem? hC
    have hmx : m ∈ xs := hinP m (List.mem_flatten.2 ⟨C, hCP, hm⟩)
    rcases hxv with ⟨hxe, rfl⟩ | ⟨k, c, hc, hxe, rfl⟩
    · have hSm : S m.name := hS m hmx m.name (List.mem_cons_self ..)
      have e : (σ m.name == σ x) = true := by rw [hinj _ _ hSm hx]; exact hxe
      rw [← mutCtx_getElem?_congr _ e, ← name_ren (hmr m hmx)]
      exact ctx_member hkQ hQ hmQ
    · obtain ⟨c', hc', hname'⟩ := ctor_ren (hmr m hmx) hc
      have hcm : c.cnst.name ∈ keysOf m := by
        unfold keysOf
        refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, ?_, rfl⟩)
        rw [← Array.getElem?_toList] at hc
        exact List.mem_of_getElem? hc
      have e : (σ c.cnst.name == σ x) = true := by rw [hinj _ _ (hS m hmx _ hcm) hx]; exact hxe
      rw [← mutCtx_getElem?_congr _ e, ← hname', ctx_ctor hkQ hQ hmQ hc', List.length_map,
        offs_map P (fun D hD m' hm' => ctors_size_ren (hmr m' (hinP m' (List.mem_flatten.2 ⟨D, hD, hm'⟩))))]
  | none =>
    have d := ctx_dom P x
    rw [hv] at d
    have dQ := ctx_dom (P.map (List.map φ)) (σ x)
    rw [hflat, keys_map_ren hmr _ hinP, any_map_ren hinj hx _ hSkeys, ← d] at dQ
    cases hw : (MutConst.ctx (P.map (List.map φ)))[σ x]? with
    | none => rfl
    | some _ => rw [hw] at dQ; cases dQ

include hmr hS hinj hext hk in
/-- **Reference comparisons are unchanged by the renaming.** -/
theorem compareRef_ren {P : List (List MutConst)} (hP : P.flatten.Perm xs) (r : Rules)
    (addr? : Name → Option Address) (mode : ExtMode) {x y : Name} (hx : S x) (hy : S y) :
    compareRef (ctxOf r addr? mode (MutConst.ctx (P.map (List.map φ)))) (σ x) (σ y) =
      compareRef (ctxOf r addr? mode (MutConst.ctx P)) x y := by
  have ex := ctx_ren hmr hS hinj hk hP hx
  have ey := ctx_ren hmr hS hinj hk hP hy
  have fix : ∀ z, S z → (MutConst.ctx P)[z]? = none → σ z = z := by
    intro z hz hn
    apply hext z hz
    intro k hk'
    have d := ctx_dom P z
    rw [hn] at d
    have hk'' : k ∈ P.flatten.flatMap keysOf :=
      (List.Perm.flatMap_right keysOf hP).mem_iff.2 hk'
    cases e : (k == z)
    · rfl
    · have : (P.flatten.flatMap keysOf).any (· == z) = true := List.any_eq_true.2 ⟨k, hk'', e⟩
      rw [← d] at this; cases this
  cases hb : (x == y)
  · have hb' : (σ x == σ y) = false := by rw [hinj x y hx hy, hb]
    cases hx' : (MutConst.ctx P)[x]? <;> cases hy' : (MutConst.ctx P)[y]?
    · rw [compareRef_out_out _ hb' (ex.trans hx') (ey.trans hy'), compareRef_out_out _ hb hx' hy',
        fix x hx hx', fix y hy hy']
      rfl
    · rw [compareRef_out_in _ hb' (ex.trans hx') (ey.trans hy'), compareRef_out_in _ hb hx' hy']
    · rw [compareRef_in_out _ hb' (ex.trans hx') (ey.trans hy'), compareRef_in_out _ hb hx' hy']
    · rw [compareRef_in_in _ hb' (ex.trans hx') (ey.trans hy'), compareRef_in_in _ hb hx' hy']
  · have hb' : (σ x == σ y) = true := by rw [hinj x y hx hy, hb]
    rw [compareRef_beq _ hb', compareRef_beq _ hb]

include hmr hS hinj hext hk in
/-- The comparisons agree on renamed members, at every partition. -/
theorem constOrd_ren {P : List (List MutConst)} (hP : P.flatten.Perm xs) (r : Rules)
    (addr? : Name → Option Address) {a b : MutConst} (ha : a ∈ xs) (hb : b ∈ xs) (o : Ordering) :
    constOrd r addr? (MutConst.ctx P) a b = .ok o ↔
      constOrd r addr? (MutConst.ctx (P.map (List.map φ))) (φ a) (φ b) = .ok o :=
  constOrd_iff (fun mode => constP_ren ordIff (ctxOf r addr? mode (MutConst.ctx P))
    (ctxOf r addr? mode (MutConst.ctx (P.map (List.map φ)))) rfl (fun x y hx hy => by
    rw [compareRef_ren hmr hS hinj hext hk hP r addr? mode hx hy]; exact ordIff.refl _)
    (hmr a ha) (hmr b hb)) o

end rename2

/-- **Renaming** (Def 4.3, renaming): members renamed by a renaming `σ` that is injective (under
`==`) on the names involved and fixes the external ones, presented in any order, have the same
classes in the same order, each class the renamed members of the original class. Only the
representatives can change (they are chosen by name). -/
theorem sortClasses_rename {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {xs ys : List MutConst}
    (hk : KeysDistinct xs) {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst}
    (hmr : ∀ a ∈ xs, MRen σ S a (φ a)) (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (hext : ∀ x, S x → (∀ k ∈ xs.flatMap keysOf, (k == x) = false) → σ x = x)
    (hys : (xs.map φ).Perm ys) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? xs = .ok (F, stats)) :
    ∃ G stats', sortClasses rules addr? ys = .ok (G, stats') ∧ SetEq (F.map (List.map φ)) G := by
  have e₁ := sortClasses_eq hpf hA hk
  rw [h] at e₁
  have hF : sortClassesP rules addr? xs = .ok F := e₁.symm
  obtain ⟨hFp, -, -⟩ := sortClassesP_coarsest rules hA hk hF
  have hkm : KeysDistinct (xs.map φ) := keysDistinct_ren hmr hS hinj (fun a ha => ha) hk
  obtain ⟨G, hG, e⟩ := sortClassesP_sim (keep := fun _ => true) (φ := φ) (xs := xs) (ys := ys) hA hA hk
    (by rw [restrictC_true]; exact hkm) (by rw [restrictC_true]; exact hys) hF
    (fun D hD => by
      obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil D (hFp.2 D hD)
      exact ⟨m, hm, rfl⟩)
    (fun P hP _ a ha b hb _ _ o => by
      rw [restrictP_true]; exact constOrd_ren hmr hS hinj hext hk hP.1 rules addr? ha hb o)
  rw [restrictP_true] at e
  have e₂ := sortClasses_eq hpf hA (hkm.perm hys)
  rw [hG] at e₂
  cases h₂ : sortClasses rules addr? ys with
  | error err => rw [h₂] at e₂; cases e₂
  | ok v =>
    rw [h₂] at e₂
    simp only [Except.map, Except.ok.injEq] at e₂
    refine ⟨v.1, v.2, rfl, ?_⟩
    rw [e₂]; exact e

end Ix.CompileCert.Canon
