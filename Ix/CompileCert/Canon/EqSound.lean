import Ix.CompileCert.Canon.Coarsest

/-! # Pass 1's comparator: what `eq` means

CS-01's new part (the port inventory's "comparator `.eq` soundness"): when
the comparator answers `eq`, the two sides are equal up to exactly the
identifications it makes. `ExprEq c xl yl x y` is that relation on
expressions: binder names and binder information ignored, non-semantic
`mdata` stripped, semantic contracts by their order key, levels equal after
`toUniv` (parameters by position in each side's own list) and `canonUniv`,
references identified by `RefEq` (the same name under `==`, the same class
index, or two external names at one compiled address), and everything else
literally (`bvar` indices, literals, projection indices, a `let`'s nonDep
bit). `ConstMatch` lifts it to constants: the same kind, the same scalar
keys (so, for inductives, the same constructor positions) and related
expressions.

* `compareExpr_eq_sound`: `compareExpr c xl yl x y = .ok ⟨s, .eq⟩` gives
  `ExprEq c xl yl x y`;
* `constP_eq_sound`, `constOrd_eq_sound`: an `eq` constant comparison gives
  `ConstMatch`;
* `sortClasses_match`: two members of one class of `sortClasses` match under
  the classes' own context (from `sortClasses_coarsest`'s consistency).

No faithfulness is needed: soundness reads only the comparator's own
answers. -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind ConstructorVal RecursorVal RecursorRule MutCtx)

/-! ## The relations -/

/-- Two references the comparator identifies at context `c`. -/
def RefEq (c : CmpCtx) (x y : Name) : Prop :=
  (x == y) = true ∨ (∃ n, c.mutCtx[x]? = some n ∧ c.mutCtx[y]? = some n) ∨
    (c.mutCtx[x]? = none ∧ c.mutCtx[y]? = none ∧ ∃ a, c.addr? x = some a ∧ c.addr? y = some a)

/-- Two levels the comparator identifies: both lower to universes with one
`canonUniv` form. -/
def LevelEq (xl yl : List Name) (u v : Level) : Prop :=
  ∃ a b, toUniv xl u = .ok a ∧ toUniv yl v = .ok b ∧ Ixon.canonUniv a = Ixon.canonUniv b

/-- Two expressions the comparator identifies. -/
inductive ExprEq (c : CmpCtx) (xl yl : List Name) : Expr → Expr → Prop
  | mdataL {d x y h} : SemanticContract.hasMetadata d = false → ExprEq c xl yl x y →
      ExprEq c xl yl (.mdata d x h) y
  | mdataR {d x y h} : SemanticContract.hasMetadata d = false → ExprEq c xl yl x y →
      ExprEq c xl yl x (.mdata d y h)
  | contract {dx dy x y hx hy kx ky} : SemanticContract.hasMetadata dx = true →
      SemanticContract.hasMetadata dy = true → SemanticContract.read dx = .ok kx →
      SemanticContract.read dy = .ok ky → kx.orderKey = ky.orderKey → ExprEq c xl yl x y →
      ExprEq c xl yl (.mdata dx x hx) (.mdata dy y hy)
  | bvar {i h h'} : ExprEq c xl yl (.bvar i h) (.bvar i h')
  | sort {u v h h'} : LevelEq xl yl u v → ExprEq c xl yl (.sort u h) (.sort v h')
  | const {xn yn us vs h h'} : List.Forall₂ (LevelEq xl yl) us.toList vs.toList → RefEq c xn yn →
      ExprEq c xl yl (.const xn us h) (.const yn vs h')
  | app {f a g b h h'} : ExprEq c xl yl f g → ExprEq c xl yl a b →
      ExprEq c xl yl (.app f a h) (.app g b h')
  | lam {n n' t b t' b' bi bi' h h'} : ExprEq c xl yl t t' → ExprEq c xl yl b b' →
      ExprEq c xl yl (.lam n t b bi h) (.lam n' t' b' bi' h')
  | forallE {n n' t b t' b' bi bi' h h'} : ExprEq c xl yl t t' → ExprEq c xl yl b b' →
      ExprEq c xl yl (.forallE n t b bi h) (.forallE n' t' b' bi' h')
  | letE {n n' t v b t' v' b' nd h h'} : ExprEq c xl yl t t' → ExprEq c xl yl v v' →
      ExprEq c xl yl b b' → ExprEq c xl yl (.letE n t v b nd h) (.letE n' t' v' b' nd h')
  | lit {l h h'} : ExprEq c xl yl (.lit l h) (.lit l h')
  | proj {xn yn i s s' h h'} : RefEq c xn yn → ExprEq c xl yl s s' →
      ExprEq c xl yl (.proj xn i s h) (.proj yn i s' h')

/-! ## Reading `eq` off the combinators -/

theorem cmpM_eq_parts {ε : Type} {l r : Except ε SOrder} {s : Bool}
    (h : SOrder.cmpM l r = .ok ⟨s, .eq⟩) : (∃ s₁, l = .ok ⟨s₁, .eq⟩) ∧ ∃ s₂, r = .ok ⟨s₂, .eq⟩ := by
  obtain ⟨⟨s₁, o⟩, hl, branch⟩ := cmpM_ok.mp h
  rcases branch with ⟨different, same⟩ | ⟨equal, ⟨⟨s₂, o₂⟩, hr, same⟩⟩
  · exact absurd (congrArg SOrder.ord same).symm different
  · change o = .eq at equal
    have := congrArg SOrder.ord same
    change Ordering.eq = o₂ at this
    subst equal; subst this
    exact ⟨⟨s₁, hl⟩, ⟨s₂, hr⟩⟩

theorem lexIf_eq_parts {ε : Type} {l r : Except ε SOrder} {s : Bool}
    (h : lexIf l r = .ok ⟨s, .eq⟩) : (∃ s₁, l = .ok ⟨s₁, .eq⟩) ∧ r = .ok ⟨s, .eq⟩ := by
  obtain ⟨⟨s₁, o⟩, hl, branch⟩ := lexIf_ok.mp h
  rcases branch with ⟨different, same⟩ | ⟨equal, hr⟩
  · exact absurd (congrArg SOrder.ord same).symm different
  · change o = .eq at equal
    subst equal
    exact ⟨⟨s₁, hl⟩, hr⟩

theorem pure_eq_nat {ε : Type} {a b : Nat} {t s : Bool}
    (h : (pure ⟨t, compare a b⟩ : Except ε SOrder) = .ok ⟨s, .eq⟩) : a = b := by
  simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h
  exact Nat.compare_eq_eq.1 h.2

theorem zipM_eq {ε β : Type} {f : β → β → Except ε SOrder} :
    ∀ {xs ys : List β} {s : Bool}, SOrder.zipM f xs ys = .ok ⟨s, .eq⟩ →
      List.Forall₂ (fun x y => ∃ s, f x y = .ok ⟨s, .eq⟩) xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp [SOrder.zipM, pure, Except.pure] at h
  | _ :: _, [], _, h => by simp [SOrder.zipM, pure, Except.pure] at h
  | x :: xs, y :: ys, _, h => by
    rw [zipM_cons] at h
    obtain ⟨hd, ⟨s₂, tl⟩⟩ := cmpM_eq_parts h
    exact .cons hd (zipM_eq tl)

theorem literal_compare_eq {a b : Lean.Literal} (h : compare a b = .eq) : a = b := by
  cases a <;> cases b
  · rw [literal_compare_natVal] at h; rw [Nat.compare_eq_eq.1 h]
  · cases h
  · cases h
  · rw [literal_compare_strVal] at h; rw [Std.LawfulEqCmp.eq_of_compare h]

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons r t => .cons (h _ _ r) (forall₂_imp h t)

theorem defKind_compare_eq {a b : Ix.DefKind} (h : compare a b = .eq) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem bool_compare_eq {a b : Bool} (h : compare a b = .eq) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-! ## Leaves -/

theorem compareLevel_eq_sound {xl yl : List Name} {u v : Level} {s : Bool}
    (h : compareLevel xl yl u v = .ok ⟨s, .eq⟩) : LevelEq xl yl u v := by
  unfold compareLevel at h
  cases hu : toUniv xl u <;> cases hv : toUniv yl v <;>
    simp only [hu, hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq,
      reduceCtorEq] at h
  rename_i a b
  exact ⟨a, b, hu, hv, compareUniv_eq_iff.1 h.2⟩

theorem compareLevels_eq_sound {xl yl : List Name} {us vs : List Level} {s : Bool}
    (h : compareLevels xl yl us vs = .ok ⟨s, .eq⟩) : List.Forall₂ (LevelEq xl yl) us vs :=
  forall₂_imp (fun _ _ ⟨_, e⟩ => compareLevel_eq_sound e) (zipM_eq h)

theorem compareRef_eq_sound {c : CmpCtx} {x y : Name} {s : Bool}
    (h : compareRef c x y = .ok ⟨s, .eq⟩) : RefEq c x y := by
  cases hb : (x == y)
  · cases hx : c.mutCtx[x]? <;> cases hy : c.mutCtx[y]?
    · rw [compareRef_out_out c hb hx hy] at h
      unfold compareExternal at h
      cases ax : c.addr? x <;> cases ay : c.addr? y <;>
        simp only [ax, ay, pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, reduceCtorEq] at h
      rename_i a b
      exact .inr (.inr ⟨hx, hy, a, ax, by rw [ay, address_compare_eq_iff.1 h.2]⟩)
    · rw [compareRef_out_in c hb hx hy] at h; cases h
    · rw [compareRef_in_out c hb hx hy] at h; cases h
    · rw [compareRef_in_in c hb hx hy] at h
      simp only [Except.ok.injEq, SOrder.mk.injEq] at h
      rename_i nx ny
      exact .inr (.inl ⟨nx, hx, by rw [hy, Nat.compare_eq_eq.1 h.2]⟩)
  · exact .inl hb

/-! ## Expressions -/

theorem exprEq_strip_left {c : CmpCtx} {xl yl : List Name} :
    ∀ {x hx : Expr}, ehd x = some hx → ∀ {y : Expr}, ExprEq c xl yl hx y → ExprEq c xl yl x y
  | .mdata d x' hh, hx, ex, y, h => by
    unfold ehd at ex
    split at ex
    · cases ex; exact h
    · rename_i hd
      exact .mdataL (by simpa using hd) (exprEq_strip_left (x := x') ex h)
  | .mvar .., _, ex, _, _ | .fvar .., _, ex, _, _ => by simp [ehd] at ex
  | .bvar .., _, ex, _, h | .sort .., _, ex, _, h | .const .., _, ex, _, h | .app .., _, ex, _, h
  | .lam .., _, ex, _, h | .forallE .., _, ex, _, h | .letE .., _, ex, _, h | .lit .., _, ex, _, h
  | .proj .., _, ex, _, h => by
    simp only [ehd, Option.some.injEq] at ex; subst ex; exact h

theorem exprEq_strip_right {c : CmpCtx} {xl yl : List Name} {x : Expr} :
    ∀ {y hy : Expr}, ehd y = some hy → ExprEq c xl yl x hy → ExprEq c xl yl x y
  | .mdata d y' hh, hy, ey, h => by
    unfold ehd at ey
    split at ey
    · cases ey; exact h
    · rename_i hd
      exact .mdataR (by simpa using hd) (exprEq_strip_right (y := y') ey h)
  | .mvar .., _, ey, _ | .fvar .., _, ey, _ => by simp [ehd] at ey
  | .bvar .., _, ey, h | .sort .., _, ey, h | .const .., _, ey, h | .app .., _, ey, h
  | .lam .., _, ey, h | .forallE .., _, ey, h | .letE .., _, ey, h | .lit .., _, ey, h
  | .proj .., _, ey, h => by
    simp only [ehd, Option.some.injEq] at ey; subst ey; exact h

/-- **`eq` soundness for expressions**: an `eq` answer of `compareExpr`
relates the two sides by `ExprEq`. -/
theorem compareExpr_eq_sound (c : CmpCtx) (xl yl : List Name) :
    ∀ n (x y : Expr), exprSize x + exprSize y < n → ∀ {s : Bool},
      compareExpr c xl yl x y = .ok ⟨s, .eq⟩ → ExprEq c xl yl x y := by
  intro n
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y hs s h
    cases ex : ehd x with
    | none => exact absurd h (compareExpr_bad c xl yl x y (.inl ex) _)
    | some hx =>
      cases ey : ehd y with
      | none => exact absurd h (compareExpr_bad c xl yl x y (.inr ey) _)
      | some hy =>
        rw [compareExpr_strip c xl yl x y ex ey] at h
        obtain ⟨hnx, hsx⟩ := ehd_spec ex
        obtain ⟨hny, hsy⟩ := ehd_spec ey
        refine exprEq_strip_left ex (exprEq_strip_right ey ?_)
        have hs' : exprSize hx + exprSize hy < n + 1 := by omega
        clear ex ey hsx hsy hs
        have ht : etag hx = etag hy := by
          refine Classical.byContradiction fun ht => ?_
          rw [compareExpr_diff c xl yl hnx hny ht] at h
          simp only [Except.ok.injEq, SOrder.mk.injEq] at h
          exact ht (Nat.compare_eq_eq.1 h.2)
        cases hx <;> cases hy <;> simp only [etag] at ht <;> (try omega) <;>
          (try (simp only [HN] at hnx; done)) <;> (try (simp only [HN] at hny; done)) <;>
          (try simp only [exprSize_app, exprSize_lam, exprSize_forallE, exprSize_letE,
            exprSize_proj, exprSize_mdata] at hs')
        · -- bvar
          rw [cE_bvar] at h
          simp only [Except.ok.injEq, SOrder.mk.injEq] at h
          rw [Nat.compare_eq_eq.1 h.2]; exact .bvar
        · -- sort
          rw [cE_sort] at h; exact .sort (compareLevel_eq_sound h)
        · -- const
          rw [cE_const] at h
          obtain ⟨⟨_, hl⟩, hr⟩ := lexIf_eq_parts h
          exact .const (compareLevels_eq_sound hl) (compareRef_eq_sound hr)
        · -- app
          rw [cE_app] at h
          obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := cmpM_eq_parts h
          exact .app (ih _ _ (by omega) h1) (ih _ _ (by omega) h2)
        · -- lam
          rw [cE_lam] at h
          obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := cmpM_eq_parts h
          exact .lam (ih _ _ (by omega) h1) (ih _ _ (by omega) h2)
        · -- forallE
          rw [cE_forallE] at h
          obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := cmpM_eq_parts h
          exact .forallE (ih _ _ (by omega) h1) (ih _ _ (by omega) h2)
        · -- letE
          rw [cE_letE] at h
          obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := cmpM_eq_parts h
          obtain ⟨⟨_, h2⟩, ⟨_, h3⟩⟩ := cmpM_eq_parts h2
          obtain ⟨⟨_, h3⟩, ⟨_, h4⟩⟩ := cmpM_eq_parts h3
          simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h4
          rw [bool_compare_eq h4.2]
          exact .letE (ih _ _ (by omega) h1) (ih _ _ (by omega) h2) (ih _ _ (by omega) h3)
        · -- lit
          rw [cE_lit] at h
          simp only [Except.ok.injEq, SOrder.mk.injEq] at h
          rw [literal_compare_eq h.2]; exact .lit
        · -- contract frames
          rename_i dx x' hx' dy y' hy'
          simp only [HN] at hnx hny
          rw [cE_contract c xl yl hnx hny] at h
          cases rx : SemanticContract.read dx with
          | error e => simp [rx, bind, Except.bind, Except.mapError] at h
          | ok kx =>
            cases ry : SemanticContract.read dy with
            | error e => simp [rx, ry, bind, Except.bind, Except.mapError] at h
            | ok ky =>
              simp only [rx, ry, bind, Except.bind, Except.mapError] at h
              obtain ⟨⟨_, hk⟩, hb⟩ := lexIf_eq_parts h
              exact .contract hnx hny rx ry (pure_eq_nat hk) (ih _ _ (by omega) hb)
        · -- proj
          rw [cE_proj] at h
          obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := cmpM_eq_parts h
          obtain ⟨⟨_, h2⟩, ⟨_, h3⟩⟩ := cmpM_eq_parts h2
          rw [pure_eq_nat h2]
          exact .proj (compareRef_eq_sound h1) (ih _ _ (by omega) h3)

/-! ## Constants -/

/-- Two definitions the comparator identifies. -/
structure DefMatch (c : CmpCtx) (x y : Def) : Prop where
  kind : x.kind = y.kind
  levels : x.levelParams.size = y.levelParams.size
  type : ExprEq c x.levelParams.toList y.levelParams.toList x.type y.type
  value : ExprEq c x.levelParams.toList y.levelParams.toList x.value y.value

/-- Two constructors the comparator identifies. -/
structure CtorMatch (c : CmpCtx) (xl yl : List Name) (x y : ConstructorVal) : Prop where
  levels : x.cnst.levelParams.size = y.cnst.levelParams.size
  cidx : x.cidx = y.cidx
  numParams : x.numParams = y.numParams
  numFields : x.numFields = y.numFields
  type : ExprEq c xl yl x.cnst.type y.cnst.type

/-- Two inductives the comparator identifies. -/
structure IndMatch (c : CmpCtx) (x y : Ind) : Prop where
  levels : x.levelParams.size = y.levelParams.size
  numParams : x.numParams = y.numParams
  numIndices : x.numIndices = y.numIndices
  ctorCount : x.ctors.size = y.ctors.size
  type : ExprEq c x.levelParams.toList y.levelParams.toList x.type y.type
  ctors : List.Forall₂ (CtorMatch c x.levelParams.toList y.levelParams.toList) x.ctors.toList y.ctors.toList

/-- Two recursor rules the comparator identifies. -/
structure RuleMatch (c : CmpCtx) (xl yl : List Name) (x y : RecursorRule) : Prop where
  nfields : x.nfields = y.nfields
  rhs : ExprEq c xl yl x.rhs y.rhs

/-- Two recursors the comparator identifies. -/
structure RecMatch (c : CmpCtx) (x y : RecursorVal) : Prop where
  levels : x.cnst.levelParams.size = y.cnst.levelParams.size
  numParams : x.numParams = y.numParams
  numIndices : x.numIndices = y.numIndices
  numMotives : x.numMotives = y.numMotives
  numMinors : x.numMinors = y.numMinors
  k : x.k = y.k
  type : ExprEq c x.cnst.levelParams.toList y.cnst.levelParams.toList x.cnst.type y.cnst.type
  rules : List.Forall₂ (RuleMatch c x.cnst.levelParams.toList y.cnst.levelParams.toList)
    x.rules.toList y.rules.toList

/-- Two constants the comparator identifies: one kind, matching per kind. -/
def ConstMatch (c : CmpCtx) : MutConst → MutConst → Prop
  | .defn x, .defn y => DefMatch c x y
  | .indc x, .indc y => IndMatch c x y
  | .recr x, .recr y => RecMatch c x y
  | _, _ => False

theorem ctorKeys_eq_sound {c : CmpCtx} {xl yl : List Name} {x y : ConstructorVal} {s : Bool}
    (h : compareCtorKeys c xl yl x y = .ok ⟨s, .eq⟩) : CtorMatch c xl yl x y := by
  unfold compareCtorKeys at h
  obtain ⟨⟨_, h1⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h2⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h3⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h4⟩, ⟨_, h5⟩⟩ := cmpM_eq_parts h
  exact ⟨pure_eq_nat h1, pure_eq_nat h2, pure_eq_nat h3, pure_eq_nat h4,
    compareExpr_eq_sound c xl yl _ _ _ (Nat.lt_succ_self _) h5⟩

theorem compareDef_eq_sound {c : CmpCtx} {x y : Def} {s : Bool}
    (h : compareDef c x y = .ok ⟨s, .eq⟩) : DefMatch c x y := by
  unfold compareDef at h
  obtain ⟨⟨_, h1⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h2⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h3⟩, ⟨_, h4⟩⟩ := cmpM_eq_parts h
  simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h1
  exact ⟨defKind_compare_eq h1.2, pure_eq_nat h2,
    compareExpr_eq_sound c _ _ _ _ _ (Nat.lt_succ_self _) h3,
    compareExpr_eq_sound c _ _ _ _ _ (Nat.lt_succ_self _) h4⟩

theorem indP_eq_sound {c : CmpCtx} {x y : Ind} {s : Bool}
    (h : indP c x y = .ok ⟨s, .eq⟩) : IndMatch c x y := by
  unfold indP at h
  obtain ⟨⟨_, hh⟩, h⟩ := lexIf_eq_parts h
  rw [indHeader_eq] at hh
  simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, Ordering.then_eq_eq,
    Nat.compare_eq_eq] at hh
  obtain ⟨⟨_, ht⟩, ⟨_, hc⟩⟩ := cmpM_eq_parts h
  exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2,
    compareExpr_eq_sound c _ _ _ _ _ (Nat.lt_succ_self _) ht,
    forall₂_imp (fun _ _ ⟨_, e⟩ => ctorKeys_eq_sound e) (zipM_eq hc)⟩

theorem compareRecr_eq_sound {c : CmpCtx} {x y : RecursorVal} {s : Bool}
    (h : compareRecr c x y = .ok ⟨s, .eq⟩) : RecMatch c x y := by
  unfold compareRecr at h
  obtain ⟨⟨_, h1⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h2⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h3⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h4⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h5⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h6⟩, ⟨_, h⟩⟩ := cmpM_eq_parts h
  obtain ⟨⟨_, h7⟩, ⟨_, h8⟩⟩ := cmpM_eq_parts h
  simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h6
  exact ⟨pure_eq_nat h1, pure_eq_nat h2, pure_eq_nat h3, pure_eq_nat h4, pure_eq_nat h5,
    bool_compare_eq h6.2, compareExpr_eq_sound c _ _ _ _ _ (Nat.lt_succ_self _) h7,
    forall₂_imp (fun _ _ ⟨_, e⟩ => by
      unfold compareRule at e
      obtain ⟨⟨_, e1⟩, ⟨_, e2⟩⟩ := cmpM_eq_parts e
      exact ⟨pure_eq_nat e1, compareExpr_eq_sound c _ _ _ _ _ (Nat.lt_succ_self _) e2⟩) (zipM_eq h8)⟩

/-- **`eq` soundness for constants.** -/
theorem constP_eq_sound {c : CmpCtx} {x y : MutConst} {s : Bool}
    (h : constP c x y = .ok ⟨s, .eq⟩) : ConstMatch c x y := by
  cases x <;> cases y <;> simp only [constP, ConstMatch] at h ⊢
  all_goals first
    | exact compareDef_eq_sound h
    | exact indP_eq_sound h
    | exact compareRecr_eq_sound h
    | (simp only [kindTag, pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h
       exact absurd (Nat.compare_eq_eq.1 h.2) (by decide))

theorem constOrd_eq_sound {addr? : Name → Option Address} {ctx : MutCtx} {x y : MutConst}
    (h : constOrd addr? ctx x y = .ok .eq) : ConstMatch (ctxOf addr? ctx) x y := by
  unfold constOrd at h
  cases hc : constP (ctxOf addr? ctx) x y with
  | error e => rw [hc] at h; cases h
  | ok r =>
    rw [hc] at h
    obtain ⟨s, o⟩ := r
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    exact constP_eq_sound hc

/-- **Two distinct members of one class match** under the classes' own
context. -/
theorem sortClasses_match (rules : Rules) {addr? : Name → Option Address} {N : Name → Prop}
    (hN : Faithful N) {sources : List MutConst} (hin : ∀ m ∈ sources, ConstIn N m)
    (hk : KeysDistinct sources) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? sources = .ok (F, stats)) :
    ∀ C ∈ F, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → ConstMatch (ctxOf addr? (MutConst.ctx F)) a b :=
  fun C hC a ha b hb hab =>
    constOrd_eq_sound ((sortClasses_coarsest rules hN hin hk h).2.1 C hC a ha b hb hab)

end Ix.CompileCert.Canon
