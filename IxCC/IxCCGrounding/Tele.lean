import IxCCGrounding.Subst
import IxCCGrounding.Support

/-!
# Telescopes in a model (`IxCCGrounding.Tele`)

Lemmas about `∀`- and `λ`-telescopes (`piTele`, `lamTele`), application spines (`mkAppN`) and
runs of bound variables (`bvarsFrom`), in any model:

* `Fits` through a telescope binds its arguments (`fits_piTele`), splits at any point
  (`fits_append`, `fits_trans`), and moves to another telescope whose domains denote the same sets
  (`fits_transport`);
* **β through a `λ`-telescope** (`lamTele_app`) at arguments that fit the matching `∀`-telescope;
* **a `λ`-telescope lies in a `∀`-telescope** (`lamTele_mem`) when their domains denote the same
  sets, their binder data agree and the body lands in the codomain;
* **a member of a `∀`-telescope in the graph regime applies along a chain** (`appChain_of_fits`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-! ## Syntax -/

theorem piTele_append : ∀ (bs1 bs2 : List (KExpr × BinderMeta)) (C : KExpr),
    piTele (bs1 ++ bs2) C = piTele bs1 (piTele bs2 C)
  | [], _, _ => rfl
  | (A, m) :: bs1, bs2, C => by simp [piTele, piTele_append bs1 bs2 C]

theorem lamTele_append : ∀ (bs1 bs2 : List (KExpr × BinderMeta)) (C : KExpr),
    lamTele (bs1 ++ bs2) C = lamTele bs1 (lamTele bs2 C)
  | [], _, _ => rfl
  | (A, m) :: bs1, bs2, C => by simp [lamTele, lamTele_append bs1 bs2 C]

theorem liftTele_length (k : Nat) : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)),
    (liftTele k c bs).length = bs.length
  | _, [] => rfl
  | c, _ :: bs => by simp [liftTele, liftTele_length k (c + 1) bs]

theorem liftTele_metas (k : Nat) : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)),
    (liftTele k c bs).map (·.2) = bs.map (·.2)
  | _, [] => rfl
  | c, _ :: bs => by simp [liftTele, liftTele_metas k (c + 1) bs]

theorem liftTele_get (k : Nat) : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)) (p : Nat),
    (liftTele k c bs)[p]?.map (·.1) = bs[p]?.map fun b => b.1.liftLooseBVars k (c + p)
  | _, [], _ => rfl
  | c, _ :: bs, 0 => by simp [liftTele]
  | c, _ :: bs, p + 1 => by
    simp only [liftTele, List.getElem?_cons_succ]
    rw [liftTele_get k (c + 1) bs p, show c + 1 + p = c + (p + 1) by omega]

theorem liftTele_append (k c : Nat) : ∀ (bs1 bs2 : List (KExpr × BinderMeta)),
    liftTele k c (bs1 ++ bs2) = liftTele k c bs1 ++ liftTele k (c + bs1.length) bs2 := by
  intro bs1
  induction bs1 generalizing c with
  | nil => intro bs2; simp [liftTele]
  | cons b bs1 ih =>
    intro bs2
    simp only [List.cons_append, liftTele, ih, List.length_cons]
    rw [show c + 1 + bs1.length = c + (bs1.length + 1) by omega]

theorem lift_piTele (k : Nat) : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)) (C : KExpr),
    (piTele bs C).liftLooseBVars k c = piTele (liftTele k c bs) (C.liftLooseBVars k (c + bs.length))
  | c, [], C => by simp [piTele, liftTele]
  | c, (A, m) :: bs, C => by
    simp only [piTele, Expr.liftLooseBVars, liftTele, lift_piTele k (c + 1) bs C, List.length_cons]
    rw [show c + 1 + bs.length = c + (bs.length + 1) by omega]

theorem lift_mkAppN (k c : Nat) : ∀ (args : List KExpr) (f : KExpr),
    (Expr.mkAppN f args).liftLooseBVars k c =
      Expr.mkAppN (f.liftLooseBVars k c) (args.map (·.liftLooseBVars k c))
  | [], _ => rfl
  | a :: args, f => by
    simp only [Expr.mkAppN, List.map_cons]
    rw [lift_mkAppN k c args (.app f a)]
    rfl

theorem getAppFn_mkAppN : ∀ (args : List KExpr) (f : KExpr),
    (Expr.mkAppN f args).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: args, f => by rw [Expr.mkAppN, getAppFn_mkAppN args]; rfl

theorem getAppArgs_mkAppN : ∀ (args : List KExpr) (f : KExpr),
    (Expr.mkAppN f args).getAppArgs = f.getAppArgs ++ args
  | [], _ => by simp [Expr.mkAppN]
  | a :: args, f => by
    rw [Expr.mkAppN, getAppArgs_mkAppN args]
    simp [Expr.getAppArgs]

theorem bvarsFrom_succ (k n : Nat) :
    bvarsFrom k (n + 1) = (.bvar (k + n) : KExpr) :: bvarsFrom k n := by
  simp [bvarsFrom, List.range_succ]

theorem bvarsFrom_length (k n : Nat) : (bvarsFrom k n).length = n := by simp [bvarsFrom]

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}
  {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

/-! ## Application spines and runs of variables -/

theorem den_mkAppN : ∀ (args : List KExpr) {ρ : BVarIdx → V} {f : KExpr} {X : V},
    Denotes cval env φ ρ (Expr.mkAppN f args) X ↔
      ∃ F Ys, Denotes cval env φ ρ f F ∧ DenotesList cval env φ ρ args Ys ∧ X = Ys.foldl app F
  | [], ρ, f, X => by
    simp only [Expr.mkAppN]
    constructor
    · intro h; exact ⟨X, [], h, .nil, rfl⟩
    · rintro ⟨F, Ys, hF, hY, rfl⟩; cases hY; exact hF
  | a :: args, ρ, f, X => by
    simp only [Expr.mkAppN]
    rw [den_mkAppN args]
    constructor
    · rintro ⟨F', Ys, hF', hYs, rfl⟩
      obtain ⟨F, A, hF, hA, rfl⟩ := den_app.mp hF'
      exact ⟨F, A :: Ys, hF, .cons hA hYs, rfl⟩
    · rintro ⟨F, Ys, hF, hYs, rfl⟩
      cases hYs with
      | cons hA hYs => exact ⟨_, _, .app hF hA, hYs, rfl⟩

theorem denotesList_append {ρ : BVarIdx → V} : ∀ {es1 es2 : List KExpr} {vs1 vs2 : List V},
    DenotesList cval env φ ρ es1 vs1 → DenotesList cval env φ ρ es2 vs2 →
      DenotesList cval env φ ρ (es1 ++ es2) (vs1 ++ vs2)
  | [], _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, h1, h2 => by
    cases h1 with
    | cons h h1 => exact .cons h (denotesList_append h1 h2)

theorem denotesList_length {ρ : BVarIdx → V} : ∀ {es : List KExpr} {vs : List V},
    DenotesList cval env φ ρ es vs → vs.length = es.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by cases h with | cons _ h => simp [denotesList_length h]

theorem denotesList_functional {ρ : BVarIdx → V} : ∀ {es : List KExpr} {vs ws : List V},
    DenotesList cval env φ ρ es vs → DenotesList cval env φ ρ es ws → vs = ws
  | [], _, _, h1, h2 => by cases h1; cases h2; rfl
  | _ :: _, _, _, h1, h2 => by
    cases h1 with
    | cons a h1 =>
      cases h2 with
      | cons b h2 => rw [Denotes_functional a b, denotesList_functional h1 h2]

/-- **A run of variables denotes the block of sets it points at**: in the environment `a, ys, zs`,
the `ys.length` variables above the innermost `zs.length` denote `ys`, outermost first. -/
theorem den_bvarsFrom (ρ : BVarIdx → V) (zs : List V) : ∀ (ys a : List V),
    DenotesList cval env φ (pushAll (a ++ ys ++ zs) ρ) (bvarsFrom zs.length ys.length) ys
  | [], _ => by simp [bvarsFrom]; exact .nil
  | y :: ys, a => by
    rw [List.length_cons, bvarsFrom_succ]
    refine .cons ?_ ?_
    · have e : a ++ y :: ys ++ zs = a ++ y :: (ys ++ zs) := by simp
      rw [e, show zs.length + ys.length = (ys ++ zs).length by simp; omega]
      have h := Denotes.bvar (cval := cval) (env := env) (φ := φ)
        (ρ := pushAll (a ++ y :: (ys ++ zs)) ρ) (i := (ys ++ zs).length)
      rwa [pushAll_at] at h
    · have e : a ++ y :: ys ++ zs = (a ++ [y]) ++ ys ++ zs := by simp
      rw [e]
      exact den_bvarsFrom ρ zs ys (a ++ [y])

theorem den_bvar_at {a c : List V} {y : V} {ρ : BVarIdx → V} :
    Denotes cval env φ (pushAll (a ++ y :: c) ρ) (.bvar c.length) y := by
  have h := Denotes.bvar (cval := cval) (env := env) (φ := φ)
    (ρ := pushAll (a ++ y :: c) ρ) (i := c.length)
  rwa [pushAll_at] at h

omit [Ix.Kernel.SetTheory V] in
/-- Within the bound sets, the environment below them does not matter. -/
theorem pushAll_lt {xs : List V} {E E' : BVarIdx → V} {i : Nat} (h : i < xs.length) :
    pushAll xs E i = pushAll xs E' i := by
  simp only [pushAll, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h)]
  rfl

omit [Ix.Kernel.SetTheory V] in
/-- Two environments differing only in a block of as many sets agree outside the block. -/
theorem pushAll_agree {a b b' c : List V} {ρ : BVarIdx → V} (hb : b.length = b'.length) {i : Nat}
    (hi : i < c.length ∨ c.length + b.length ≤ i) :
    pushAll (a ++ b ++ c) ρ i = pushAll (a ++ b' ++ c) ρ i := by
  rw [pushAll_append, pushAll_append (a ++ b')]
  rcases hi with hi | hi
  · exact pushAll_lt hi
  · obtain ⟨d, rfl⟩ : ∃ d, i = d + c.length := ⟨i - c.length, by omega⟩
    rw [pushAll_offset, pushAll_offset, pushAll_append, pushAll_append]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + b.length := ⟨d - b.length, by omega⟩
    rw [pushAll_offset, hb, pushAll_offset]

/-- A twice-lifted term, read under a block of as many sets as the two lifts insert, denotes what
the term denotes without the block. -/
theorem den_lift2 {ps junk xs : List V} {ρ : BVarIdx → V} {A : KExpr} {j k' : Nat}
    (hj : junk.length = j + 1 + k') {X : V} :
    Denotes cval env φ (pushAll (ps ++ junk ++ xs) ρ)
        ((A.liftLooseBVars (j + 1) xs.length).liftLooseBVars k' (j + xs.length)) X ↔
      Denotes cval env φ (pushAll (ps ++ xs) ρ) A X := by
  rw [den_lift, den_lift, skipEnv_skipEnv _ (by omega) (by omega), ← hj, skipEnv_pushAll]

theorem denotesList_append_inv {ρ : BVarIdx → V} : ∀ {es1 es2 : List KExpr} {vs : List V},
    DenotesList cval env φ ρ (es1 ++ es2) vs →
      ∃ vs1 vs2, vs = vs1 ++ vs2 ∧ DenotesList cval env φ ρ es1 vs1 ∧
        DenotesList cval env φ ρ es2 vs2
  | [], _, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | e :: es1, es2, _, h => by
    cases h with
    | cons he h' =>
      obtain ⟨vs1, vs2, rfl, h1, h2⟩ := denotesList_append_inv (es1 := es1) h'
      exact ⟨_ :: vs1, vs2, rfl, .cons he h1, h2⟩

/-! ## `Fits` through telescopes -/

theorem fits_nil_inv {ρ σ : BVarIdx → V} {T R : KExpr} {xs : List V}
    (h : Fits cval env φ ρ T xs σ R) (hx : xs = []) : σ = ρ ∧ R = T := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ => cases hx

theorem fits_append {ρ σ : BVarIdx → V} {T R : KExpr} {xs ys : List V}
    (h : Fits cval env φ ρ T (xs ++ ys) σ R) :
    ∃ σ1 R1, Fits cval env φ ρ T xs σ1 R1 ∧ Fits cval env φ σ1 R1 ys σ R := by
  induction xs generalizing ρ T with
  | nil => exact ⟨ρ, T, .nil, h⟩
  | cons x xs ih =>
    rw [List.cons_append] at h
    cases h with
    | cons hA hx h' =>
      obtain ⟨σ1, R1, h1, h2⟩ := ih h'
      exact ⟨σ1, R1, .cons hA hx h1, h2⟩

theorem fits_trans {ρ σ1 σ : BVarIdx → V} {T R1 R : KExpr} {xs ys : List V}
    (h1 : Fits cval env φ ρ T xs σ1 R1) (h2 : Fits cval env φ σ1 R1 ys σ R) :
    Fits cval env φ ρ T (xs ++ ys) σ R := by
  induction h1 with
  | nil => exact h2
  | cons hA hx _ ih => exact .cons hA hx (ih h2)

/-- **`Fits` through a telescope** binds the arguments, leaves the rest of the telescope, and does
not look at the codomain. -/
theorem fits_piTele : ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {ρ σ : BVarIdx → V}
    {R : KExpr} {xs : List V}, Fits cval env φ ρ (piTele bs C) xs σ R → xs.length ≤ bs.length →
      σ = pushAll xs ρ ∧ R = piTele (bs.drop xs.length) C ∧
        ∀ C', Fits cval env φ ρ (piTele bs C') xs σ (piTele (bs.drop xs.length) C')
  | bs, C, ρ, σ, R, [], h, _ => by
    obtain ⟨h1, h2⟩ := fits_nil_inv h rfl
    subst h1 h2
    exact ⟨(pushAll_nil _).symm, rfl, fun _ => .nil⟩
  | [], _, _, _, _, _ :: _, _, hl => by simp at hl
  | (A, m) :: bs, C, ρ, σ, R, x :: xs, h, hl => by
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      obtain ⟨e1, e2, h3⟩ := fits_piTele bs C h' (by simp at hl; omega)
      refine ⟨by rw [e1, pushAll_cons], by simpa using e2, fun C' => ?_⟩
      show Fits cval env φ ρ (.forallE A (piTele bs C') m) (x :: xs) σ (piTele (bs.drop xs.length) C')
      exact .cons hA hx (h3 C')

/-- The domain at each argument, from `Fits` through a telescope. -/
theorem fits_get : ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {ρ σ : BVarIdx → V}
    {R : KExpr} {xs : List V}, Fits cval env φ ρ (piTele bs C) xs σ R →
    ∀ (p : Nat) (h1 : p < xs.length) (h2 : p < bs.length),
      ∃ X, Denotes cval env φ (pushAll (xs.take p) ρ) bs[p].1 X ∧ xs[p] ∈ˢ X
  | [], _, _, _, _, _, _, _, _, h2 => by simp at h2
  | _ :: _, _, _, _, _, [], _, _, h1, _ => by simp at h1
  | (A, m) :: bs, C, ρ, σ, R, x :: xs, h, p, h1, h2 => by
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      cases p with
      | zero => exact ⟨_, by simpa [pushAll_nil] using hA, hx⟩
      | succ p =>
        obtain ⟨X, hX, hm⟩ := fits_get bs C h' p (by simp at h1; omega) (by simp at h2; omega)
        exact ⟨X, by simpa [List.take_succ_cons, pushAll_cons] using hX, by simpa using hm⟩

/-- `Fits` through a telescope from the domain at each argument. -/
theorem fits_of_forall : ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {ρ : BVarIdx → V}
    {xs : List V}, xs.length = bs.length →
    (∀ (p : Nat) (h1 : p < xs.length) (h2 : p < bs.length),
      ∃ X, Denotes cval env φ (pushAll (xs.take p) ρ) bs[p].1 X ∧ xs[p] ∈ˢ X) →
    Fits cval env φ ρ (piTele bs C) xs (pushAll xs ρ) C
  | [], _, ρ, [], _, _ => by rw [pushAll_nil]; exact .nil
  | [], _, _, _ :: _, hl, _ => by simp at hl
  | _ :: _, _, _, [], hl, _ => by simp at hl
  | (A, m) :: bs, C, ρ, x :: xs, hl, h => by
    obtain ⟨X, hX, hm⟩ := h 0 (by simp) (by simp)
    have hrest := fits_of_forall bs C (ρ := push x ρ) (xs := xs) (by simpa using hl)
      fun p h1 h2 => by
        obtain ⟨Y, hY, hy⟩ := h (p + 1) (by simp; omega) (by simp; omega)
        exact ⟨Y, by simpa [List.take_succ_cons, pushAll_cons] using hY, by simpa using hy⟩
    rw [pushAll_cons]
    exact .cons (by simpa [pushAll_nil] using hX) (by simpa using hm) hrest

/-- `Fits` of the arguments in the first binders, from `Fits` of all of them. -/
theorem fits_prefix {bs : List (KExpr × BinderMeta)} {C : KExpr} {ρ σ : BVarIdx → V}
    {R : KExpr} {xs ys : List V} (h : Fits cval env φ ρ (piTele bs C) (xs ++ ys) σ R)
    (hl : xs.length ≤ bs.length) :
    Fits cval env φ ρ (piTele bs C) xs (pushAll xs ρ) (piTele (bs.drop xs.length) C) := by
  obtain ⟨σ1, R1, h1, _⟩ := fits_append h
  obtain ⟨e1, e2, _⟩ := fits_piTele bs C h1 hl
  subst e1 e2
  exact h1

/-- The domain correspondence between two telescopes: at every prefix of bound sets, each domain
of `bsP` read in `EP` denotes what the matching domain of `bsL` denotes in `EL`. -/
def TeleCorr (cval : KKey → (LevelParam → Nat) → V) (env : KEnv) (φ : LevelParam → Nat)
    (EL EP : BVarIdx → V) (bsL bsP : List (KExpr × BinderMeta)) : Prop :=
  ∀ (ys : List V) (AL AP : KExpr), bsL[ys.length]?.map (·.1) = some AL →
    bsP[ys.length]?.map (·.1) = some AP →
    ∀ X, Denotes cval env φ (pushAll ys EP) AP X → Denotes cval env φ (pushAll ys EL) AL X

theorem teleCorr_tail {EL EP : BVarIdx → V} {bL bP : KExpr × BinderMeta}
    {bsL bsP : List (KExpr × BinderMeta)} (h : TeleCorr cval env φ EL EP (bL :: bsL) (bP :: bsP))
    (x : V) : TeleCorr cval env φ (push x EL) (push x EP) bsL bsP := by
  intro ys AL AP hL hP X hX
  have := h (x :: ys) AL AP (by simpa using hL) (by simpa using hP) X (by rwa [pushAll_cons])
  rwa [pushAll_cons] at this

theorem teleCorr_head {EL EP : BVarIdx → V} {bL bP : KExpr × BinderMeta}
    {bsL bsP : List (KExpr × BinderMeta)} (h : TeleCorr cval env φ EL EP (bL :: bsL) (bP :: bsP))
    {X : V} (hX : Denotes cval env φ EP bP.1 X) : Denotes cval env φ EL bL.1 X := by
  have := h [] bL.1 bP.1 rfl rfl X (by rwa [pushAll_nil])
  rwa [pushAll_nil] at this

/-- **`Fits` moves to a telescope whose domains denote the same sets.** -/
theorem fits_transport : ∀ (bsL bsP : List (KExpr × BinderMeta)) (CL CP : KExpr)
    {EL EP σ : BVarIdx → V} {R : KExpr} {xs : List V},
    bsL.length = bsP.length → TeleCorr cval env φ EL EP bsL bsP →
    Fits cval env φ EP (piTele bsP CP) xs σ R → xs.length ≤ bsP.length →
      Fits cval env φ EL (piTele bsL CL) xs (pushAll xs EL) (piTele (bsL.drop xs.length) CL)
  | bsL, _, CL, _, EL, _, _, _, [], _, _, _, _ => by rw [pushAll_nil]; exact .nil
  | [], _, _, _, _, _, _, _, _ :: _, hlen, _, _, hl => by simp at hlen; simp [← hlen] at hl
  | _ :: _, [], _, _, _, _, _, _, _ :: _, hlen, _, _, _ => by simp at hlen
  | bL :: bsL, bP :: bsP, CL, CP, EL, EP, σ, R, x :: xs, hlen, hc, h, hl => by
    obtain ⟨AP, mP⟩ := bP
    obtain ⟨AL, mL⟩ := bL
    have h0 : Fits cval env φ EP (.forallE AP (piTele bsP CP) mP) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      have h2 := fits_transport bsL bsP CL CP (by simpa using hlen) (teleCorr_tail hc x) h'
        (by simp at hl; omega)
      rw [pushAll_cons]
      exact .cons (teleCorr_head hc hA) hx (by simpa using h2)

/-- **β through a `λ`-telescope**, at arguments that fit a `∀`-telescope over the same domains. -/
theorem lamTele_app : ∀ (bs : List (KExpr × BinderMeta)) (b C : KExpr) {ρ σ : BVarIdx → V}
    {F : V} {R : KExpr} {xs : List V}, Denotes cval env φ ρ (lamTele bs b) F →
    Fits cval env φ ρ (piTele bs C) xs σ R → xs.length = bs.length →
      ∃ Y, Denotes cval env φ (pushAll xs ρ) b Y ∧ xs.foldl app F = Y
  | [], b, C, ρ, σ, F, R, [], hF, _, _ => ⟨F, by rwa [pushAll_nil], rfl⟩
  | [], _, _, _, _, _, _, _ :: _, _, _, hl => by simp at hl
  | _ :: _, _, _, _, _, _, _, [], _, _, hl => by simp at hl
  | (A, m) :: bs, b, C, ρ, σ, F, R, x :: xs, hF, h, hl => by
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      obtain ⟨Y1, hY1, e1⟩ := app_den_lam hF hA hx
      obtain ⟨Y, hY, e⟩ := lamTele_app bs b C hY1 h' (by simpa using hl)
      exact ⟨Y, by rwa [pushAll_cons], by rw [List.foldl_cons, e1, e]⟩

/-- **A `λ`-telescope lies in a `∀`-telescope** whose domains denote the same sets (read in
their own environments), whose binder data agree, and into whose codomain the body lands at
every arguments that fit. In regime `0` at a binder the body is the proof point, since it lies in
a truth value. -/
theorem lamTele_mem : ∀ (bsL bsP : List (KExpr × BinderMeta)) (b C : KExpr)
    {EL EP : BVarIdx → V} {P : V},
    bsL.map (·.2) = bsP.map (·.2) → TeleCorr cval env φ EL EP bsL bsP →
    Denotes cval env φ EP (piTele bsP C) P →
    (∀ (xs : List V) (σ : BVarIdx → V) (R : KExpr), Fits cval env φ EP (piTele bsP C) xs σ R →
      xs.length = bsP.length → ∃ Y, Denotes cval env φ (pushAll xs EL) b Y ∧
        ∀ CC, Denotes cval env φ (pushAll xs EP) C CC → Y ∈ˢ CC) →
    ∃ L, Denotes cval env φ EL (lamTele bsL b) L ∧ L ∈ˢ P
  | [], [], b, C, EL, EP, P, _, _, hP, hb => by
    obtain ⟨Y, hY, hm⟩ := hb [] EP C .nil rfl
    rw [pushAll_nil] at hY hm
    exact ⟨Y, hY, hm P hP⟩
  | [], _ :: _, _, _, _, _, _, hm, _, _, _ => by simp at hm
  | _ :: _, [], _, _, _, _, _, hm, _, _, _ => by simp at hm
  | (AL, mL) :: bsL, (AP, mP) :: bsP, b, C, EL, EP, P, hm, hc, hP, hb => by
    classical
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨rfl, hm⟩ := hm
    obtain ⟨AA, B, hAA, hB, h0, rfl⟩ := den_pi.mp hP
    have hAL : Denotes cval env φ EL AL AA := teleCorr_head hc hAA
    have hIH : ∀ x, x ∈ˢ AA → ∃ L, Denotes cval env φ (push x EL) (lamTele bsL b) L ∧ L ∈ˢ B x :=
      fun x hx => lamTele_mem bsL bsP b C hm (teleCorr_tail hc x) (hB x hx)
        fun xs σ R hf hl => by
          obtain ⟨Y, hY, hY'⟩ := hb (x :: xs) σ R (.cons hAA hx hf) (by simpa using hl)
          exact ⟨Y, by rwa [pushAll_cons] at hY, fun CC hCC => hY' CC (by rwa [pushAll_cons])⟩
    let F : V → V := fun x => if h : x ∈ˢ AA then Classical.choose (hIH x h) else x
    have hF : ∀ x, x ∈ˢ AA → Denotes cval env φ (push x EL) (lamTele bsL b) (F x) ∧ F x ∈ˢ B x :=
      fun x hx => by
        simp only [F, hx, ↓reduceDIte]
        exact Classical.choose_spec (hIH x hx)
    refine ⟨lamR (regime φ mL.pw) AA F, ?_, lamR_mem fun x hx => (hF x hx).2⟩
    refine .lam hAL (fun x hx => (hF x hx).1) fun hr x hx => ?_
    have hu := h0 hr x hx
    rw [univ_zero] at hu
    exact eq_pt_of_mem_univZero hu (hF x hx).2

/-- **A member of a `∀`-telescope in the graph regime applies along a chain** to arguments that
fit it. -/
theorem appChain_of_fits : ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {E σ : BVarIdx → V}
    {P X : V} {R : KExpr} {ys : List V},
    Denotes cval env φ E (piTele bs C) P → X ∈ˢ P →
    Fits cval env φ E (piTele bs C) ys σ R → ys.length ≤ bs.length →
    (∀ b ∈ bs, regime φ b.2.pw ≠ 0) → AppChain X ys
  | _, _, _, _, _, _, _, [], _, _, _, _, _ => .nil
  | [], _, _, _, _, _, _, _ :: _, _, _, _, hl, _ => by simp at hl
  | (A, m) :: bs, C, E, σ, P, X, R, y :: ys, hP, hX, h, hl, hr => by
    obtain ⟨AA, B, hAA, hB, _, rfl⟩ := den_pi.mp hP
    have h0 : Fits cval env φ E (.forallE A (piTele bs C) m) (y :: ys) σ R := h
    cases h0 with
    | cons hA hy h' =>
      obtain rfl := Denotes_functional hA hAA
      have hv : regime φ m.pw ≠ 0 := hr (A, m) (by simp)
      exact .cons hv hX hy (appChain_of_fits bs C (hB y hy) (app_mem_piR_pos hv hX hy) h'
        (by simp at hl; omega) fun b hb => hr b (by simp [hb]))

end IxCC.Grounding
