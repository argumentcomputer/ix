module

public import ConLeche.Verify.Level
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern): its constructors are `public` but the module is
not `@[expose]`d, so a `cases`-then-`rfl` proof about a datum cannot
see the reduct.  `import all` gives that view HERE only; nothing this
module exports depends on it. -/
import ConLeche.Kernel.PropWhen
import all ConLeche.Kernel.PropWhen

public section

/-!
# The zero-ness datum against `Level` (task #161)

`ConLeche/Kernel/PropWhen.lean` owns the datum: its representation, its
API, and every law about the datum *alone* (the readout algebra,
`eq_iff_holds` — equality decides zero-ness agreement — and the
`inter`/`bindZ` algebra).  This file is a *consumer* of that API; it
proves what the datum alone cannot say, namely how it relates to
`Level`:

* **Soundness of the readout** — `zeronessOf_sound`:
  `(zeronessOf l).holds φ = (eval φ l == 0)`.
* **The substitution pushforward** — `zeronessOf_subst`:
  `zeronessOf (subst ks vs l) = substPW ks vs (zeronessOf l)`, an
  *equality* of data (`bindZ` distributes over `inter`).
* **The instantiation laws** — `substPW_self` (identity at a
  declaration's own parameters, unconditional: the datum is canonical
  by construction since task #194, so `bindZ` at the unit is the
  identity as an equality, `PropWhen.bindZ_unit`) and `substPW_comp`
  (composition, under the same parameter-definedness hypothesis the
  level side has — `PropWhen.paramsDefined`, folded into
  `Expr.allLevelParamsDefined`), `substPW_paramsDefined`,
  `zeronessOf_paramsDefined`, and the semantic reading
  `holds_substPW`.

Nothing here unfolds the datum's representation: every step goes
through the exported `casesZ` view and the `_never`/`_ifAllZero`
equations.
-/

namespace ConLeche.PropWhen

/-! ## Soundness of the readout -/

private theorem beq_zero_and (x y : Nat) :
    ((x == 0) && (y == 0)) = (Max.max x y == 0) := by
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all <;> omega

theorem zeronessOf_sound (φ : Name → Nat) :
    ∀ l : Level, (Level.zeronessOf l).holds φ = (Level.eval φ l == 0)
  | .zero => by simp [Level.zeronessOf, Level.eval]
  | .succ l => by simp [Level.zeronessOf, Level.eval]
  | .param n => by simp [Level.zeronessOf, Level.eval]
  | .max a b => by
    rw [Level.zeronessOf, holds_inter, zeronessOf_sound φ a,
      zeronessOf_sound φ b, beq_zero_and]
    rfl
  | .imax a b => by
    rw [Level.zeronessOf, zeronessOf_sound φ b]
    show _ = ((if Level.eval φ b = 0 then 0
      else Max.max (Level.eval φ a) (Level.eval φ b)) == 0)
    by_cases hb : Level.eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (Level.eval φ a) (Level.eval φ b) = 0 := by
        omega
      have h1 : (Level.eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (Level.eval φ a) (Level.eval φ b) == 0) = false :=
        by simpa using hm
      rw [h1, if_neg hb, h2]

/-- An intersection is unsatisfiable exactly when one side is. -/
theorem isNever_inter (a b : PropWhen) :
    (a.inter b).isNever = (a.isNever || b.isNever) := by
  cases a with
  | never => simp
  | ifAllZero ps =>
    cases b with
    | never => simp
    | ifAllZero qs => simp

end ConLeche.PropWhen

namespace ConLeche.Level

open ConLeche.PropWhen

/-- The substitution pushforward, as a syntactic equation: reading
zero-ness commutes with level-parameter substitution. -/
theorem zeronessOf_subst (ks : List Name) (vs : List Level) :
    ∀ l : Level,
      zeronessOf (subst ks vs l) = substPW ks vs (zeronessOf l)
  | .zero => rfl
  | .succ l => rfl
  | .param n => rfl
  | .max a b => by
    show (zeronessOf (subst ks vs a)).inter (zeronessOf (subst ks vs b))
      = substPW ks vs ((zeronessOf a).inter (zeronessOf b))
    rw [zeronessOf_subst ks vs a, zeronessOf_subst ks vs b]
    exact (bindZ_inter _ _ _).symm
  | .imax a b => by
    show zeronessOf (subst ks vs b) = _
    exact zeronessOf_subst ks vs b

/-- **The syntactic never-zero test IS the datum's unsatisfiability**:
`isNeverZero` and `zeronessOf` are the same case analysis, one
answering "no valuation makes this zero" and the other reading off
which valuations do. -/
theorem isNeverZero_eq_isNever :
    ∀ l : Level, l.isNeverZero = (zeronessOf l).isNever
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .max a b => by
    rw [Level.isNeverZero, zeronessOf, isNever_inter,
      isNeverZero_eq_isNever a, isNeverZero_eq_isNever b]
  | .imax _ b => by
    rw [Level.isNeverZero, zeronessOf, isNeverZero_eq_isNever b]

/-- `subst.go` at the identity substitution. -/
theorem subst_go_self (ks : List Name) (n : Name) :
    subst.go ks (ks.map Level.param) n = .param n := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    show (if k = n then Level.param k else subst.go ks (ks.map .param) n)
      = _
    by_cases h : k = n
    · simp [h]
    · simp [h, ih]

/-- Instantiating a datum at the declaration's own parameters is the
identity — unconditionally.  Amendment 2 (task #161 P1) found this
law false for a *normalizing* `substPW` on a *non-canonical* datum;
since task #194 every datum is canonical by construction, so there is
no such datum and the law is an equality again (`PropWhen.bindZ_unit`
is its datum half). -/
theorem substPW_self (ks : List Name) (pw : PropWhen) :
    substPW ks (ks.map Level.param) pw = pw := by
  show pw.bindZ _ = pw
  have : pw.bindZ (fun n => zeronessOf (subst.go ks (ks.map .param) n))
      = pw.bindZ (fun n => .ifAllZero [n]) := by
    cases pw with
    | never => rfl
    | ifAllZero ps =>
      rw [bindZ_ifAllZero, bindZ_ifAllZero]
      exact bindZ_congr_names fun n _ => by rw [subst_go_self]; rfl
  rw [this, bindZ_unit]

/-- `subst.go` under a mapped replacement list: a parameter resolved
within the pairing factors through the outer substitution. -/
theorem subst_go_map (σ : Level → Level) :
    ∀ (ps : List Name) (vs : List Level) (n : Name),
      n ∈ ps → vs.length = ps.length →
      subst.go ps (vs.map σ) n = σ (subst.go ps vs n)
  | [], _, n, hn, _ => by simp at hn
  | p :: ps, [], n, _, hl => by simp at hl
  | p :: ps, v :: vs, n, hn, hl => by
    show (if p = n then σ v else subst.go ps (vs.map σ) n) = _
    by_cases h : p = n
    · simp [h, subst.go]
    · have hn' : n ∈ ps := by
        cases hn with
        | head => exact absurd rfl h
        | tail _ h' => exact h'
      have hl' : vs.length = ps.length := by simpa using hl
      simp only [h, if_false]
      rw [subst_go_map σ ps vs n hn' hl']
      show _ = σ (if p = n then v else subst.go ps vs n)
      simp [h]

/-- Composition of datum instantiations, under the same
parameter-definedness the level side's `subst_subst` has: parameters
of the datum are covered by the inner substitution. -/
theorem substPW_comp {ks : List Name} {us : List Level}
    {ps : List Name} {vs : List Level} {pw : PropWhen}
    (hl : vs.length = ps.length)
    (hdef : pw.paramsDefined ps = true) :
    substPW ks us (substPW ps vs pw) =
      substPW ps (vs.map (Level.subst ks us)) pw := by
  cases pw with
  | never => rfl
  | ifAllZero pws =>
    rw [show substPW ps vs (PropWhen.ifAllZero pws)
          = bindZ.go (fun n => zeronessOf (subst.go ps vs n)) pws from
        bindZ_ifAllZero _ _,
      show substPW ps (vs.map (Level.subst ks us)) (PropWhen.ifAllZero pws)
          = bindZ.go
              (fun n => zeronessOf (subst.go ps (vs.map (Level.subst ks us)) n))
              pws from bindZ_ifAllZero _ _]
    show (bindZ.go (fun n => zeronessOf (subst.go ps vs n)) pws).bindZ _
      = bindZ.go (fun n => zeronessOf (subst.go ps (vs.map _) n)) pws
    simp only [PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at hdef
    induction pws with
    | nil => rfl
    | cons n rest ih =>
      show (PropWhen.inter _ _).bindZ _ = PropWhen.inter _ _
      rw [bindZ_inter]
      rw [ih fun m hm => hdef m (by simp [hm])]
      congr 1
      show substPW ks us (zeronessOf (subst.go ps vs n))
        = zeronessOf (subst.go ps (vs.map (subst ks us)) n)
      rw [← zeronessOf_subst ks us (subst.go ps vs n),
        subst_go_map (Level.subst ks us) ps vs n
          (by simpa [List.contains_iff_mem] using hdef n (by simp)) hl]

/-- The parameter footprint of a readout is the level's. -/
theorem zeronessOf_paramsDefined {ps' : List Name} :
    ∀ {l : Level}, l.allParamsDefined ps' = true →
      (zeronessOf l).paramsDefined ps' = true
  | .zero, _ => rfl
  | .succ _, _ => rfl
  | .param n, h => by
    simpa [zeronessOf, allParamsDefined] using h
  | .max a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    exact PropWhen.paramsDefined_inter_of
      (zeronessOf_paramsDefined h.1) (zeronessOf_paramsDefined h.2)
  | .imax a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    show (zeronessOf b).paramsDefined ps' = true
    exact zeronessOf_paramsDefined h.2

/-- A parameter resolved within the pairing lands in the replacement
list. -/
theorem subst_go_mem :
    ∀ {ks : List Name} {us : List Level} {n : Name},
      n ∈ ks → us.length = ks.length → subst.go ks us n ∈ us
  | [], _, n, hn, _ => by simp at hn
  | _ :: _, [], n, _, hl => by simp at hl
  | k :: ks, u :: us, n, hn, hl => by
    show (if k = n then u else subst.go ks us n) ∈ u :: us
    by_cases h : k = n
    · simp [h]
    · have hn' : n ∈ ks := by
        cases hn with
        | head => exact absurd rfl h
        | tail _ h' => exact h'
      simp only [h, if_false]
      exact List.mem_cons_of_mem u (subst_go_mem hn' (by simpa using hl))

/-- The pushforward keeps datum parameters within the bound of the
substituted levels — the datum half of
`Level.allParamsDefined_subst`. -/
theorem substPW_paramsDefined {ks : List Name} {us : List Level}
    {ps' : List Name} (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {pw : PropWhen}, pw.paramsDefined ks = true →
      (substPW ks us pw).paramsDefined ps' = true := by
  intro pw h
  cases pw with
  | never => rfl
  | ifAllZero pws =>
    rw [show substPW ks us (PropWhen.ifAllZero pws)
          = bindZ.go (fun n => zeronessOf (subst.go ks us n)) pws from
        bindZ_ifAllZero _ _]
    simp only [PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at h
    induction pws with
    | nil => rfl
    | cons n rest ih =>
      show (PropWhen.inter _ _).paramsDefined ps' = true
      exact PropWhen.paramsDefined_inter_of
        (zeronessOf_paramsDefined (hus _ (subst_go_mem
          (by simpa [List.contains_iff_mem] using h n (by simp)) hl)))
        (ih fun m hm => h m (by simp [hm]))

/-- **The pushforward's semantic reading** (task #161 P3): the
instantiated datum's bit at `φ` is the datum's bit at the composed
valuation `Level.substFn φ ks vs` — the same composed valuation
`denoteAnnot`'s constant clause uses.  The `denoteMeta` level crossing rides
this where the canonical lane needed the open checker metatheorems
(`SortOfEInstLevels`/`LamSortEInstLevels`,
`ConLeche/SetR/Interp/Steps/Levels.lean`). -/
theorem holds_substPW (φ : Name → Nat) (ks : List Name)
    (vs : List Level) : ∀ pw : PropWhen,
    (substPW ks vs pw).holds φ = pw.holds (substFn φ ks vs) := by
  intro pw
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    rw [show substPW ks vs (PropWhen.ifAllZero ps)
          = PropWhen.bindZ.go (fun n => zeronessOf (subst.go ks vs n)) ps from
        bindZ_ifAllZero _ _,
      holds_bindZ_go, PropWhen.holds_ifAllZero]
    induction ps with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons, ih]
      rw [zeronessOf_sound, eval_subst_go]

end ConLeche.Level
