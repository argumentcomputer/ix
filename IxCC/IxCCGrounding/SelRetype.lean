import IxCCGrounding.GradedHead

/-!
# `autoParam`/`optParam` binders in an `eqn` function's type (`IxCCGrounding.SelRetype`, step Ap)

`eqnShape` asks the function's stored type to be `∀ Ds, R` over the theorem's own binder domains.
`Std.Legacy.Range.forIn'.loop` (every `for` loop) has a binder `autoParam.{0} (j ≤ …) stx` where its
equation theorem binds the bare `j ≤ …`. The two domains denote alike by δ (`defn_value` at
`autoParam`, whose value is `λ α stx. α`) and β twice, each argument's membership in its λ's domain
from `graded` at the function type's node (`beta_peel`, step 1b). So the agreement needs `graded`:
without its memberships the function's domain can be empty (a graph-regime λ applied off its
domain gives `∅`), while the equation body's λ ranges over the selected argument. **Ap belongs to
the family over six of #678's fields only**; the older families keep refusing these equations.

**Transport, not a new shape.** No landed definition changes (`EqnShape`, `RunPair`, `GroundFacts`,
`groundCheck` keep text and meaning). The check reads `selEnv`: the kernel's reading with each `eqn`
function's stored type replaced by its selector-free form `∀ Ds, R` when the two agree binder by
binder up to **selector domains** (`SelDom`: equal, or `D.{vs} b₀ … b_{k-1}` with `D` a stored
definition whose value is `λ x₀ … x_{k-1}. x_j`, every λ's datum `never`, and `b_j` the theorem's
domain; `autoParam` and `optParam` are such, with `j = 0`; no role pin). Every model of the reading
with `defn_value` and `graded` is a model of `selEnv` with the same `cval`, the same denotations and
the six fields (`model_selRetype`, `laws678_selRetype`, `gradedLaw_selRetype`), so the root theorem
of 1b applied to `selEnv` gives the conclusion for the reading (`rootSound_678AGp_of_check`). The
check's new reading of `eqnShape` is `eqnShape` on `selEnv`.

**One repair of the approved statements.** As first approved, `selEnv` retyped every constant of a
target's name, the target having been checked against the first such constant's type only (`find?`
reads the first), and `selRetype_selEnv` was false on a reading with two constants of one name
(`selEnv_unrepaired_refuted` below). `selEnv` retypes a constant only if the agreement holds of that
constant's own type.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w'

/-- `λ x₀ … x_{k-1}. x_j`, every λ's datum `never`: `some (k, j)` (`k` counts the λs peeled). -/
def selIdx : Nat → KExpr → Option (Nat × Nat)
  | k, .lam _ b m => if m.pw = PropWhen.never then selIdx (k + 1) b else none
  | k, .bvar i => if i < k then some (k, k - 1 - i) else none
  | _, _ => none

/-- **A selector domain**: the function's domain `a` against the theorem's `b`. -/
def SelDom (env : KEnv) (a b : KExpr) : Prop :=
  a = b ∨ ∃ (D : KKey) (vs : List Level) (cv : ConstantVal .anon) (val : KExpr)
    (hint : ReducibilityHint) (k j : Nat),
    a.getAppFn = .const D vs ∧ env.find? D = some (.defnInfo cv val hint) ∧
    vs.length = cv.levelParams.length ∧ selIdx 0 val = some (k, j) ∧
    a.getAppArgs.length = k ∧ a.getAppArgs[j]? = some b

/-- **Two telescopes agree up to selector domains**: binder by binder the same datum and
`SelDom` domains, then the same term. -/
inductive SelTele (env : KEnv) : KExpr → KExpr → Prop
  | refl {T : KExpr} : SelTele env T T
  | pi {d d' b b' : KExpr} {m : BinderMeta} :
      SelDom env d d' → SelTele env b b' → SelTele env (.forallE d b m) (.forallE d' b' m)

def selDomB (tab : KTab) (a b : KExpr) : Bool :=
  a == b ||
  match a.getAppFn with
  | .const D vs =>
    match tab[D]? with
    | some (.defnInfo cv val _) =>
      vs.length == cv.levelParams.length &&
      match selIdx 0 val with
      | some (k, j) => a.getAppArgs.length == k && a.getAppArgs[j]? == some b
      | none => false
    | _ => false
  | _ => false

def selTeleB (tab : KTab) : KExpr → KExpr → Bool
  | .forallE d b m, .forallE d' b' m' =>
    (d == d' && b == b' && m == m') || (m == m' && selDomB tab d d' && selTeleB tab b b')
  | T, T' => T == T'

theorem selDom_of_check {env : KEnv} {a b : KExpr} (h : selDomB (KTab.of env) a b = true) :
    SelDom env a b := by
  unfold selDomB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inl h
  · right
    split at h
    · rename_i D vs hfn
      rw [KTab.get_of] at h
      split at h
      · rename_i cv val hint hD
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hl, h2⟩ := h
        split at h2
        · rename_i k j hsel
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          exact ⟨D, vs, cv, val, hint, k, j, hfn, hD, hl, hsel, h2.1, h2.2⟩
        · cases h2
      · cases h
    · cases h

theorem selTele_of_check {env : KEnv} :
    ∀ (T T' : KExpr), selTeleB (KTab.of env) T T' = true → SelTele env T T' := by
  intro T
  induction T with
  | forallE d b m _ ihb =>
    intro T' h
    cases T' with
    | forallE d' b' m' =>
      simp only [selTeleB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, hd⟩, hb⟩
      · exact .refl
      · exact .pi (selDom_of_check hd) (ihb b' hb)
    | _ => simp [selTeleB] at h
  | _ =>
    intro T' h
    simp only [selTeleB, beq_iff_eq] at h
    subst h
    exact .refl

/-- A selector's value peels to the selected variable, every datum `never`. -/
theorem selIdx_peel : ∀ (val : KExpr) (k k' j : Nat), selIdx k val = some (k', j) →
    k ≤ k' ∧ j < k' ∧ ∃ lds, lamPeel (k' - k) val = some (lds, .bvar (k' - 1 - j)) ∧
      ∀ pw ∈ lds, pw = PropWhen.never := by
  intro val
  induction val with
  | lam d b m _ ihb =>
    intro k k' j h
    simp only [selIdx] at h
    split at h
    · rename_i hm
      obtain ⟨h1, h2, lds, hp, hn⟩ := ihb (k + 1) k' j h
      refine ⟨by omega, h2, m.pw :: lds, ?_, ?_⟩
      · have e : k' - k = (k' - (k + 1)) + 1 := by omega
        rw [e]
        simp [lamPeel, hp]
      · intro pw hpw
        rcases List.mem_cons.mp hpw with rfl | hpw
        · exact hm
        · exact hn pw hpw
    · cases h
  | bvar i =>
    intro k k' j h
    simp only [selIdx] at h
    split at h
    · rename_i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, by omega, [], ?_, by simp⟩
      have e : k - 1 - (k - 1 - i) = i := by omega
      rw [e, Nat.sub_self]
      rfl
    · cases h
  | _ => intro k k' j h; simp [selIdx] at h

section Agree

variable {V : Type w'} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **A selector domain denotes its selected argument** (laws: `defn_value` at the selector,
`graded` of its value and of the domain's node for the arguments' memberships). -/
theorem selDom_den (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {a b : KExpr} {X : V} (h : SelDom env a b)
    (hg : GradedBy (Denotes M.cval env φ) ρ a) (hX : Denotes M.cval env φ ρ a X) :
    Denotes M.cval env φ ρ b X ∧ GradedBy (Denotes M.cval env φ) ρ b := by
  rcases h with rfl | ⟨D, vs, cv, val, hint, k, j, hfn, hD, -, hsel, hk, hj⟩
  · exact ⟨hX, hg⟩
  · obtain ⟨-, hjk, lds, hp, hn⟩ := selIdx_peel val 0 k j hsel
    rw [Nat.sub_zero] at hp
    have hae : Expr.mkAppN (.const D vs) a.getAppArgs = a := by
      rw [← hfn]; exact mkAppN_getApp a
    rw [← hae] at hX hg
    have hgp := gradedBy_mkAppN _ hg
    obtain ⟨G0, Ys, hG0, hYs, rfl⟩ := (den_mkAppN _).mp hX
    have hG0e : G0 = M.cval D (Level.substFn φ cv.levelParams vs) := by
      cases hG0 with
      | const hf _ => rw [hD] at hf; cases hf; rfl
    have hname : cv.name = D := find_name hD
    have hval := hδ cv val hint (find_mem hD) (Level.substFn φ cv.levelParams vs) ρ
    rw [hname] at hval
    have hgval := (hgr _ (find_mem hD) (Level.substFn φ cv.levelParams vs) ρ).2 cv val hint rfl
    have hSY := spineMem_of_graded M _ hg hG0 hYs
    have hlenY : Ys.length = k := (denotesList_length hYs).trans hk
    obtain ⟨hbody, -⟩ := beta_peel M k val _ lds ρ G0 Ys hp
      (fun pw hpw => by rw [hn pw hpw]; simp) hlenY (by rw [hG0e]; exact hval) hgval hSY
    rw [den_bvar, ← hlenY, pushAll_rev Ys ρ j (by omega)] at hbody
    obtain ⟨v, hv, hvd⟩ := denotesList_get hYs hj
    rw [List.getElem?_eq_getElem (by omega)] at hv
    have hv' := Option.some.inj hv
    refine ⟨?_, hgp.2 b (List.mem_of_getElem? hj)⟩
    rw [hbody, hv']
    exact hvd

/-- **A graded telescope denotes as its selector-free form, which is graded too.** -/
theorem selTele_den (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {φ : LevelParam → Nat} :
    ∀ {T T' : KExpr}, SelTele env T T' → ∀ (ρ : BVarIdx → V) (X : V),
      GradedBy (Denotes M.cval env φ) ρ T → Denotes M.cval env φ ρ T X →
      Denotes M.cval env φ ρ T' X ∧ GradedBy (Denotes M.cval env φ) ρ T' := by
  intro T T' h
  induction h with
  | refl => intro ρ X hg hX; exact ⟨hX, hg⟩
  | @pi d d' b b' m hd _ ih =>
    intro ρ X hg hX
    obtain ⟨Ad, Bf, hAd, hBf, hP, rfl⟩ := den_pi.mp hX
    simp only [GradedBy] at hg
    obtain ⟨hgd, hgb⟩ := hg
    obtain ⟨hAd', hgd'⟩ := selDom_den M hδ hgr hd hgd hAd
    have hb : ∀ x, x ∈ˢ Ad → Denotes M.cval env φ (push x ρ) b' (Bf x) ∧
        GradedBy (Denotes M.cval env φ) (push x ρ) b' :=
      fun x hx => ih (push x ρ) (Bf x) (hgb Ad hAd x hx) (hBf x hx)
    refine ⟨Denotes.pi hAd' (fun x hx => (hb x hx).1) hP, ?_⟩
    simp only [GradedBy]
    refine ⟨hgd', fun A hA x hx => ?_⟩
    rw [Denotes_functional hA hAd'] at hx
    exact (hb x hx).2

end Agree

/-! ## Retyping the reading -/

/-- A definition's type replaced (other constants unchanged). -/
def retypeCI : ConstantInfo .anon → KExpr → ConstantInfo .anon
  | .defnInfo cv v h, T' => .defnInfo { cv with type := T' } v h
  | ci, _ => ci

/-- One constant of the reading against its retyping. -/
def SelRetype1 (env : KEnv) (ci ci' : ConstantInfo .anon) : Prop :=
  ci' = ci ∨ ∃ (cv : ConstantVal .anon) (v : KExpr) (h : ReducibilityHint) (T' : KExpr),
    ci = .defnInfo cv v h ∧ ci' = .defnInfo { cv with type := T' } v h ∧ SelTele env cv.type T'

/-- Two constant lists, entry by entry a retyping. -/
inductive SelRetypeL (env : KEnv) : List (ConstantInfo .anon) → List (ConstantInfo .anon) → Prop
  | nil : SelRetypeL env [] []
  | cons {ci ci' : ConstantInfo .anon} {cs cs' : List (ConstantInfo .anon)} :
      SelRetype1 env ci ci' → SelRetypeL env cs cs' → SelRetypeL env (ci :: cs) (ci' :: cs')

/-- **`env'` is the reading with some definitions' types replaced by selector-free forms.** -/
def SelRetype (env env' : KEnv) : Prop := SelRetypeL env env.consts env'.consts

/-- **The reading the check reads**: each `eqn` function of `Sl` whose stored type agrees with
`∀ Ds, R` (the theorem's domains, its own data and result) up to selector domains, retyped so; a
constant of a target's name is retyped only if the agreement holds of its own type (the repair: a
reading may hold two constants of one name, and `find?` reads the first). -/
def selEnv (p : Program) (env : KEnv) (κ : CId → KKey) (Sl : List CId) : KEnv :=
  let tab := KTab.of env
  let targets : List (KKey × KExpr) := Sl.filterMap fun c =>
    match p.table.resolveOf c with
    | some (.eqn thm _) =>
      match eqnData? env (κ c) (κ thm), tab[κ c]? with
      | some d, some ci =>
        let T' := piTele (d.Ds.zipWith (fun b m => (b.1, m)) d.ms) d.R
        if selTeleB tab ci.toConstantVal.type T' then some (κ c, T') else none
      | _, _ => none
    | _ => none
  { consts := env.consts.map fun ci =>
      match targets.find? (·.1 == ci.name) with
      | some (_, T') => if selTeleB tab ci.toConstantVal.type T' then retypeCI ci T' else ci
      | none => ci }

theorem selRetypeL_map {env : KEnv} {f : ConstantInfo .anon → ConstantInfo .anon} :
    ∀ (cs : List (ConstantInfo .anon)), (∀ ci ∈ cs, SelRetype1 env ci (f ci)) →
      SelRetypeL env cs (cs.map f)
  | [], _ => .nil
  | ci :: cs, h => .cons (h ci (by simp)) (selRetypeL_map cs fun c hc => h c (by simp [hc]))

theorem selRetype_selEnv (p : Program) (env : KEnv) (κ : CId → KKey) (Sl : List CId) :
    SelRetype env (selEnv p env κ Sl) := by
  unfold SelRetype selEnv
  apply selRetypeL_map
  intro ci _
  dsimp only
  split
  · split
    · rename_i T' _ hsel
      cases ci with
      | defnInfo cv v h => exact .inr ⟨cv, v, h, T', rfl, rfl, selTele_of_check _ _ hsel⟩
      | _ => exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-! ## What a retyping keeps -/

theorem SelRetype1.name {env : KEnv} {ci ci' : ConstantInfo .anon} (h : SelRetype1 env ci ci') :
    ci'.name = ci.name := by
  rcases h with rfl | ⟨cv, v, hh, T', rfl, rfl, -⟩ <;> rfl

theorem SelRetype1.levelParams {env : KEnv} {ci ci' : ConstantInfo .anon}
    (h : SelRetype1 env ci ci') :
    ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams := by
  rcases h with rfl | ⟨cv, v, hh, T', rfl, rfl, -⟩ <;> rfl

/-- A retyping leaves every constant that is not a definition as it is (on either side). -/
theorem SelRetype1.eq_of_not_defn {env : KEnv} {ci ci' : ConstantInfo .anon}
    (h : SelRetype1 env ci ci') (hn : ∀ cv v hh, ci' ≠ .defnInfo cv v hh) : ci' = ci := by
  rcases h with rfl | ⟨cv, v, hh, T', rfl, rfl, -⟩
  · rfl
  · exact absurd rfl (hn _ v hh)

theorem find?_retype {env : KEnv} {n : KKey} :
    ∀ {cs cs' : List (ConstantInfo .anon)}, SelRetypeL env cs cs' →
      (cs.find? (·.name == n) = none ∧ cs'.find? (·.name == n) = none) ∨
      ∃ ci ci', cs.find? (·.name == n) = some ci ∧ cs'.find? (·.name == n) = some ci' ∧
        SelRetype1 env ci ci'
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, @SelRetypeL.cons _ ci ci' cs cs' h1 hs => by
    have hn := h1.name
    cases hb : (ci.name == n)
    · have hb' : (ci'.name == n) = false := by rw [hn]; exact hb
      simp only [List.find?_cons, hb, hb']
      exact find?_retype hs
    · have hb' : (ci'.name == n) = true := by rw [hn]; exact hb
      simp only [List.find?_cons, hb, hb']
      exact .inr ⟨_, _, rfl, rfl, h1⟩

section Keeps

variable {env env' : KEnv}

theorem find?_back (h : SelRetype env env') {n : KKey} {ci' : ConstantInfo .anon}
    (hf : env'.find? n = some ci') : ∃ ci, env.find? n = some ci ∧ SelRetype1 env ci ci' := by
  rcases find?_retype (n := n) h with ⟨-, h2⟩ | ⟨ci, ci'', h1, h2, h3⟩
  · simp only [Env.find?] at hf; rw [hf] at h2; cases h2
  · simp only [Env.find?] at hf; rw [hf] at h2; cases h2
    exact ⟨ci, h1, h3⟩

theorem find?_fwd (h : SelRetype env env') {n : KKey} {ci : ConstantInfo .anon}
    (hf : env.find? n = some ci) : ∃ ci', env'.find? n = some ci' ∧ SelRetype1 env ci ci' := by
  rcases find?_retype (n := n) h with ⟨h1, -⟩ | ⟨ci', ci'', h1, h2, h3⟩
  · simp only [Env.find?] at hf; rw [hf] at h1; cases h1
  · simp only [Env.find?] at hf; rw [hf] at h1; cases h1
    exact ⟨ci'', h2, h3⟩

/-- A constant that is not a definition is found alike in the reading and its retyping. -/
theorem find?_nondefn (h : SelRetype env env') {n : KKey} {ci : ConstantInfo .anon}
    (hn : ∀ cv v hh, ci ≠ .defnInfo cv v hh) : env'.find? n = some ci ↔ env.find? n = some ci := by
  constructor
  · intro hf
    obtain ⟨ci0, h1, h2⟩ := find?_back h hf
    rw [← h2.eq_of_not_defn hn] at h1
    exact h1
  · intro hf
    obtain ⟨ci', h1, h2⟩ := find?_fwd h hf
    rcases h2 with rfl | ⟨cv, v, hh, T', rfl, -, -⟩
    · exact h1
    · exact absurd rfl (hn cv v hh)

theorem findProj?_selRetype (h : SelRetype env env') (T : KKey) (i : Nat) :
    env'.findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  rcases find?_retype (n := projTableName T) h with ⟨h1, h2⟩ | ⟨ci, ci', h1, h2, h3⟩
  · simp only [Env.find?] at h1 h2 ⊢; rw [h1, h2]
  · simp only [Env.find?] at h1 h2 ⊢
    rw [h1, h2]
    rcases h3 with rfl | ⟨cv, v, hh, T', rfl, rfl, -⟩ <;> rfl

theorem mem_retype : ∀ {cs cs' : List (ConstantInfo .anon)}, SelRetypeL env cs cs' →
    ∀ {c' : ConstantInfo .anon}, c' ∈ cs' → ∃ c ∈ cs, SelRetype1 env c c'
  | _, _, .nil, _, hc => by simp at hc
  | _, _, .cons h1 hs, _, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self .., h1⟩
    · obtain ⟨c, hc1, hc2⟩ := mem_retype hs hc
      exact ⟨c, List.mem_cons_of_mem _ hc1, hc2⟩

end Keeps

section Transport

variable {V : Type w'} [Ix.Kernel.SetTheory V] {env env' : KEnv}

/-- `Denotes` over one environment gives `Denotes` over another that finds every constant with
the same level parameters and has the same projection tables. -/
theorem denotes_transfer {cval : KKey → (LevelParam → Nat) → V} {env₁ env₂ : KEnv}
    {φ : LevelParam → Nat}
    (hf : ∀ n ci₁, env₁.find? n = some ci₁ → ∃ ci₂, env₂.find? n = some ci₂ ∧
      ci₂.toConstantVal.levelParams = ci₁.toConstantVal.levelParams)
    (hp : ∀ T i, env₁.findProj? T i = env₂.findProj? T i) :
    ∀ {ρ : BVarIdx → V} {e : KExpr} {X : V}, Denotes cval env₁ φ ρ e X →
      Denotes cval env₂ φ ρ e X := by
  intro ρ e X h
  induction h with
  | bvar => exact .bvar
  | sort => exact .sort
  | @const ρ n us ci hfind hlen =>
    obtain ⟨ci₂, h2, hl⟩ := hf n ci hfind
    have := Denotes.const (cval := cval) (env := env₂) (φ := φ) (ρ := ρ) (us := us) h2
      (by rw [hl]; exact hlen)
    rwa [hl] at this
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ hP ihA ihF => exact .lam ihA ihF hP
  | pi _ _ hP ihA ihB => exact .pi ihA ihB hP
  | proj_table ht _ ih => exact .proj_table (by rw [← hp]; exact ht) ih
  | proj_fst ht _ ih => exact .proj_fst (by rw [← hp]; exact ht) ih
  | proj_snd ht _ ih => exact .proj_snd (by rw [← hp]; exact ht) ih
  | natLit _ ih => exact .natLit ih
  | strLit _ ih => exact .strLit ih

/-- **A retyping changes no denotation** (names, level parameters and projection tables kept). -/
theorem denotes_selRetype (h : SelRetype env env') (cval : KKey → (LevelParam → Nat) → V)
    (φ : LevelParam → Nat) : Denotes cval env' φ = Denotes cval env φ := by
  funext ρ e X
  apply propext
  constructor
  · exact denotes_transfer (fun n ci' hf => by
      obtain ⟨ci, h1, h2⟩ := find?_back h hf
      exact ⟨ci, h1, h2.levelParams.symm⟩) (fun T i => findProj?_selRetype h T i)
  · exact denotes_transfer (fun n ci hf => by
      obtain ⟨ci', h1, h2⟩ := find?_fwd h hf
      exact ⟨ci', h1, h2.levelParams⟩) (fun T i => (findProj?_selRetype h T i).symm)

theorem denotes_selRetype' (h : SelRetype env env') (cval : KKey → (LevelParam → Nat) → V) :
    Denotes cval env' = Denotes cval env :=
  funext fun φ => denotes_selRetype h cval φ

theorem fits_selRetype (h : SelRetype env env') (cval : KKey → (LevelParam → Nat) → V) :
    Fits cval env' = Fits cval env := by
  have hD := denotes_selRetype' (V := V) h cval
  funext φ ρ T xs σ R
  apply propext
  constructor
  · intro hf
    induction hf with
    | nil => exact .nil
    | cons hA hx _ ih => exact .cons (by rw [← hD]; exact hA) hx ih
  · intro hf
    induction hf with
    | nil => exact .nil
    | cons hA hx _ ih => exact .cons (by rw [hD]; exact hA) hx ih

theorem denotesList_selRetype (h : SelRetype env env') (cval : KKey → (LevelParam → Nat) → V) :
    DenotesList cval env' = DenotesList cval env := by
  have hD := denotes_selRetype' (V := V) h cval
  funext φ ρ es vs
  apply propext
  constructor
  · intro hl
    induction hl with
    | nil => exact .nil
    | cons he _ ih => exact .cons (by rw [← hD]; exact he) ih
  · intro hl
    induction hl with
    | nil => exact .nil
    | cons he _ ih => exact .cons (by rw [hD]; exact he) ih

/-- **A model of the reading with δ and `graded` is a model of the retyping, with the same `cval`**
(its `mem` at a retyped constant by `selTele_den`). -/
theorem model_selRetype (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    (h : SelRetype env env') : ∃ M' : Model V env', M'.cval = M.cval := by
  have hD := denotes_selRetype' (V := V) h M.cval
  refine ⟨{ cval := M.cval, mem := ?_, false_empty := ?_, eq_equality := ?_ }, rfl⟩
  · intro c hc φ ρ
    rw [hD]
    obtain ⟨c0, hc0, hr⟩ := mem_retype h hc
    rcases hr with rfl | ⟨cv, v, hh, T', rfl, rfl, hs⟩
    · exact M.mem c hc0 φ ρ
    · obtain ⟨T, hT, hm⟩ := M.mem _ hc0 φ ρ
      have hg := (hgr _ hc0 φ ρ).1
      exact ⟨T, (selTele_den M hδ hgr hs ρ T hg hT).1, hm⟩
  · intro φ ρ F hF
    rw [hD] at hF
    exact M.false_empty φ ρ F hF
  · intro u φ ρ E A a b hE hA ha hb
    rw [hD] at hE
    exact M.eq_equality u φ ρ E A a b hE hA ha hb

/-- **#678's five fields carry over** (each reads constants a retyping keeps, or a definition's
value and name, which it keeps). -/
theorem laws678_selRetype {M : Model V env} (hL : Laws678 M) (h : SelRetype env env')
    {M' : Model V env'} (hc : M'.cval = M.cval) : Laws678 M' := by
  have hD := denotes_selRetype' (V := V) h M.cval
  have hF := fits_selRetype (V := V) h M.cval
  have hDL := denotesList_selRetype (V := V) h M.cval
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cv value hint hmem φ ρ
    rw [hc, hD]
    obtain ⟨c0, hc0, hr⟩ := mem_retype h hmem
    rcases hr with hr | ⟨cv0, v0, hh0, T', rfl, he, -⟩
    · rw [← hr] at hc0
      exact hL.defn_value cv value hint hc0 φ ρ
    · cases he
      exact hL.defn_value cv0 value hint hc0 φ ρ
  · intro r cv mI rP rules rl hr hrl
    have hr0 := (find?_nondefn h (fun _ _ _ => by simp)).mp hr
    have H := hL.iota_rule r cv mI rP rules rl hr0 hrl
    intro cvC nP nF hC
    have hC0 := (find?_nondefn h (fun _ _ _ => by simp)).mp hC
    rw [hc, hD, hF, hDL]
    exact H cvC nP nF hC0
  · intro T i entry cvT capsT hp hT
    rw [findProj?_selRetype h] at hp
    have hT0 := (find?_nondefn h (fun _ _ _ => by simp)).mp hT
    obtain ⟨h1, h2, cvC, hC, h3, h4, h5⟩ := hL.proj_law T i entry cvT capsT hp hT0
    refine ⟨h1, h2, cvC, (find?_nondefn h (fun _ _ _ => by simp)).mpr hC, h3, h4, ?_⟩
    rw [hc, hD, hF]
    exact h5
  · obtain ⟨l1, l2, l3⟩ := hL.lit_ops
    refine ⟨?_, ?_, ?_⟩
    · intro cv v hint hf φ ρ a X
      obtain ⟨ci, hf0, hr⟩ := find?_back h hf
      rw [hc, hD]
      rcases hr with rfl | ⟨cv0, v0, hh0, T', rfl, he, -⟩
      · exact l1 cv v hint hf0 φ ρ a X
      · cases he
        exact l1 cv0 v hint hf0 φ ρ a X
    · intro c f hcf cv v hint hf φ ρ a b X
      obtain ⟨ci, hf0, hr⟩ := find?_back h hf
      rw [hc, hD]
      rcases hr with rfl | ⟨cv0, v0, hh0, T', rfl, he, -⟩
      · exact l2 c f hcf cv v hint hf0 φ ρ a b X
      · cases he
        exact l2 c f hcf cv0 v hint hf0 φ ρ a b X
    · intro c f hcf cv v hint hf φ ρ a b X
      obtain ⟨ci, hf0, hr⟩ := find?_back h hf
      rw [hc, hD]
      rcases hr with rfl | ⟨cv0, v0, hh0, T', rfl, he, -⟩
      · exact l3 c f hcf cv v hint hf0 φ ρ a b X
      · cases he
        exact l3 c f hcf cv0 v hint hf0 φ ρ a b X
  · intro n ci' hf φ₁ φ₂ hφ
    obtain ⟨ci, hf0, hr⟩ := find?_back h hf
    rw [hc]
    exact hL.cval_params n ci hf0 φ₁ φ₂ (by rw [← hr.levelParams]; exact hφ)

/-- **`graded` carries over** (a retyped constant's type by `selTele_den`). -/
theorem gradedLaw_selRetype {M : Model V env} (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    (h : SelRetype env env') : GradedLaw M.cval env' := by
  have hD := denotes_selRetype' (V := V) h M.cval
  intro c hc φ ρ
  rw [hD]
  obtain ⟨c0, hc0, hr⟩ := mem_retype h hc
  rcases hr with rfl | ⟨cv, v, hh, T', rfl, rfl, hs⟩
  · exact hgr c hc0 φ ρ
  · obtain ⟨T, hT, -⟩ := M.mem _ hc0 φ ρ
    have hg := hgr _ hc0 φ ρ
    refine ⟨(selTele_den M hδ hgr hs ρ T hg.1 hT).2, ?_⟩
    intro cv' value hint he
    cases he
    exact hg.2 cv v hh rfl

end Transport

/-! ## The root theorem -/

section RootAp

variable {V : Type w'} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **`rootSound_678AG` with `autoParam`/`optParam` binders in `eqn` functions**: every check on
`selEnv`, the conclusion for the reading. -/
theorem rootSound_678AGp_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTag p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hL.defnValue hgr hS
  have hden := denotes_selRetype hS M.cval φ
  have h := rootSound_678AG_of_check (M := M') (laws678_selRetype hL hS hc)
    (hc ▸ gradedLaw_selRetype hL.defnValue hgr hS) hchk hnc hld hinst hhr hR hA hrun hrb hRT hO
    φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at h
  exact h

end RootAp

/-! ## The approved statement's counterexample, checked

A reading with two definitions of one name `K` (the second of type `Sort 0`, the first of type
`Sort 1`): with an `eqn` entry `c ↦ thm`, `κ c = K`, `thm : Eq T lhs rhs`, the target the approved
`selEnv` computed is `(K, Sort 1)` (checked against the first constant's type, `find?`'s), and it
retyped both constants to it: `SelRetype` fails at the second. The repaired map checks each
constant's own type and keeps `SelRetype`. -/

section Counterexample

/-- The two definitions of one name. -/
def cexEnv : KEnv :=
  { consts := [.defnInfo { name := natName, levelParams := [], type := .sort (.succ .zero) }
      (.sort .zero) .opaque,
    .defnInfo { name := natName, levelParams := [], type := .sort .zero } (.sort .zero) .opaque] }

/-- The approved `selEnv`'s map at the target `(natName, Sort 1)`: every constant of the name. -/
def cexUnrepaired : KEnv :=
  { consts := cexEnv.consts.map fun ci =>
      if ci.name == natName then retypeCI ci (.sort (.succ .zero)) else ci }

/-- The repaired map at the same target. -/
def cexRepaired : KEnv :=
  { consts := cexEnv.consts.map fun ci =>
      if ci.name == natName then
        (if selTeleB (KTab.of cexEnv) ci.toConstantVal.type (.sort (.succ .zero))
          then retypeCI ci (.sort (.succ .zero)) else ci)
      else ci }

theorem selEnv_unrepaired_refuted : ¬ SelRetype cexEnv cexUnrepaired := by
  intro h
  simp only [SelRetype, cexUnrepaired, cexEnv, List.map_cons, List.map_nil] at h
  cases h with
  | cons _ hs =>
    cases hs with
    | cons h1 _ =>
      simp only [SelRetype1] at h1
      rcases h1 with h1 | ⟨cv, v, hh, T', h2, h3, h4⟩
      · simp [retypeCI, ConstantInfo.name, ConstantInfo.toConstantVal] at h1
      · cases h2
        cases h4
        simp [retypeCI, ConstantInfo.name, ConstantInfo.toConstantVal] at h3

theorem selEnv_repaired_ok : SelRetype cexEnv cexRepaired := by
  simp only [SelRetype, cexRepaired]
  apply selRetypeL_map
  intro ci _
  split
  · split
    · rename_i hsel
      cases ci with
      | defnInfo cv v hh => exact .inr ⟨cv, v, hh, _, rfl, rfl, selTele_of_check _ _ hsel⟩
      | _ => exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

end Counterexample

end IxCC.Grounding
