module

public import IxC.Kernel.Model.Open.Core
public import IxC.Kernel.Model.Open.Lists
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.Inductives.StructRec

@[expose] public section

/-!
# The rules' soundness over the public `Model`: telescope certificates

* **`Certs`' motive** `CertsS`: the values of a certified spine fit the telescope the way the
  kernel's walk reads it (`WalkFits`): each value is a member of what its binder's domain
  denotes, the domains instantiated with the spine's arguments in turn. A licensed walk
  skips a `never` slot; the motive takes the licence in the sets (`SpineOk`: a member of the
  telescope's denotation, applied along the values, applies each function to a member of
  its domain), which a graded spine supplies (`spineOk_of_graded`).
* **From the walk to the laws' reading.** The laws of `Model` read a telescope as `Denotes`
  reads a binder, by pushing the values (`Fits`). Where the telescope has a binder for every
  argument (`stripPis`), the walk is such a fit: `WalkFits.fitsO` at open terms (`FitsO`,
  with `FitsO.instantiate1` relating the instantiated telescope to the pushed one) and
  `WalkFits.fits` at a closed telescope (a stored type at its levels).
* **`EtaProjCerts`' motive** `EtaProjCertsS`: each listed projection function is stored, at
  the family's level parameters, with enough binders, and `CertsS` holds of its spine.
* **The stored telescopes have their binders** (`StoredArities`): a unit-like or η-capable
  family's type has a binder for each parameter its flag counts, and a recursor with a
  firing rule one for each argument and the major premise. The kernel checks both when it
  stores the constant; the fold's invariant holds them (`EnvModel.storedArities`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Lists of readings -/

theorem DenList.length_eq {σ : Nat → V} :
    ∀ {es : List (Expr md)} {vs : List V}, DenList M φ σ es vs → es.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

/-! ## The walk and its licence -/

/-- **A head applied along values applies functions on their domains**: at each step the
function so far is a member of some product, and the next value a member of its domain. -/
def SpineOk : V → List V → Prop
  | _, [] => True
  | F, x :: xs =>
    (∃ (r : Nat) (A : V) (B : V → V), F ∈ˢ piR r A B ∧ x ∈ˢ A) ∧ SpineOk (app F x) xs

theorem SpineOk.cons_iff {F x : V} {xs : List V} :
    SpineOk F (x :: xs) ↔
      (∃ (r : Nat) (A : V) (B : V → V), F ∈ˢ piR r A B ∧ x ∈ˢ A) ∧ SpineOk (app F x) xs :=
  Iff.rfl

/-- **Values fitting a telescope along a spine**, as the kernel's certificate walk reads it:
each value is a member of what its binder's domain denotes, the domains instantiated with
the spine's arguments in turn. -/
inductive WalkFits (M : Model V env) (φ : LevelParam → Nat) (σ : Nat → V) :
    Expr md → List (Expr md) → List V → Prop
  | nil {T : Expr md} : WalkFits M φ σ T [] []
  | cons {ty body a : Expr md} {mb : BinderMeta} {as : List (Expr md)} {A x : V}
      {xs : List V} :
      Den M φ σ ty A → x ∈ˢ A → WalkFits M φ σ (body.instantiate1 a) as xs →
      WalkFits M φ σ (.forallE ty body mb) (a :: as) (x :: xs)

/-- **`Certs`' motive**: framed, graded arguments, denoting `vs`, against a framed, graded
telescope denoting `A`, fit it along the walk; a licensed walk also takes a member of `A`
that applies along `vs` on its domains. -/
def CertsS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (lic : Bool) (T : Expr md)
    (args : List (Expr md)) : Prop :=
  Frame d T → (∀ x ∈ args, Frame d x) → ∀ σ, Ctx M φ σ T → (∀ x ∈ args, Ctx M φ σ x) →
    ∀ A, Den M φ σ T A → Gr M φ σ T → ∀ vs, DenList M φ σ args vs →
      (∀ x ∈ args, Gr M φ σ x) → (lic = true → ∃ F, F ∈ˢ A ∧ SpineOk F vs) →
        WalkFits M φ σ T args vs

theorem Certs.nil_sound {d : Nat} {lic : Bool} {T : Expr md} : CertsS M φ d lic T [] := by
  intro _ _ σ _ _ A _ _ vs hvs _ _
  cases hvs
  exact .nil

/-- **One slot of the walk, once the argument is in the domain**: the two `Certs` rules
differ only in how they find it there. -/
theorem certs_step {d : Nat} {lic : Bool} {ty body arg : Expr md} {mb : BinderMeta}
    {rest : List (Expr md)} (hrest : CertsS M φ d lic (body.instantiate1 arg) rest)
    (hfT : Frame d (.forallE ty body mb)) (hargs : ∀ x ∈ arg :: rest, Frame d x)
    {σ : Nat → V} (hCT : Ctx M φ σ (.forallE ty body mb))
    (hCargs : ∀ x ∈ arg :: rest, Ctx M φ σ x) {Ad : V} {B : V → V} (hAd : Den M φ σ ty Ad)
    (hB : ∀ x, x ∈ˢ Ad → DenotesO M.cval env φ σ (push x ρ₀) body (B x))
    (hP : regime φ mb.pw = 0 → ∀ x, x ∈ˢ Ad → B x ∈ˢ univ 0)
    (hgT : Gr M φ σ (.forallE ty body mb)) {x : V} {xs : List V} (hx : Den M φ σ arg x)
    (hxs : DenList M φ σ rest xs) (hgargs : ∀ y ∈ arg :: rest, Gr M φ σ y)
    (hlic : lic = true → ∃ F, F ∈ˢ piR (regime φ mb.pw) Ad B ∧ SpineOk F (x :: xs))
    (hxA : x ∈ˢ Ad) :
    WalkFits M φ σ (.forallE ty body mb) (arg :: rest) (x :: xs) := by
  have hpb := Frame.pi_parts hfT
  have hfarg := hargs arg List.mem_cons_self
  have hgarg := hgargs arg List.mem_cons_self
  obtain ⟨hfr', hsub⟩ := hpb.subst hfarg
  have haall := Den.all hx hfarg.2.1
  obtain ⟨-, hgb⟩ := Gr.pi_iff.1 hgT
  refine .cons hAd hxA (hrest hfr' (fun y hy => hargs y (List.mem_cons_of_mem _ hy)) σ ?_
    (fun y hy => hCargs y (List.mem_cons_of_mem _ hy)) (B x)
    ((DenotesO.instantiate1_zero haall body ρ₀ _).2 (hB x hxA))
    ((GradedBy.instantiate1_zeroO haall (Gr.all hgarg hfarg.2.1) body ρ₀).2 (hgb _ hAd _ hxA))
    xs hxs (fun y hy => hgargs y (List.mem_cons_of_mem _ hy)) ?_)
  · intro l hl
    rcases hsub l hl with hl | hl
    · exact hCT l (by simp [Expr.fvarLeaves, hl])
    · exact hCargs arg List.mem_cons_self l hl
  · intro hl
    obtain ⟨F, hF, hok⟩ := hlic hl
    exact ⟨app F x, app_mem_piR hF hxA (by rw [← univ_zero]; exact hP),
      (SpineOk.cons_iff.1 hok).2⟩

/-- **The licensed slot**: at a `never` binder the telescope's member is a graph, and the
licence's own product for it fixes the same domain, which holds the argument. -/
theorem Certs.skip_sound {d : Nat} {lic : Bool} {ty body arg : Expr md} {mb : BinderMeta}
    {rest : List (Expr md)} (hl : lic = true) (hnev : mb.pw.isNever = true)
    (hrest : CertsS M φ d lic (body.instantiate1 arg) rest) :
    CertsS M φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT hargs σ hCT hCargs A hA hgT vs hvs hgargs hlic
  cases hvs with
  | cons hx hxs =>
    cases hA with
    | pi hAd hB hP =>
      obtain ⟨F, hF, hok⟩ := hlic hl
      obtain ⟨⟨r, A', B', hF', hxA'⟩, -⟩ := SpineOk.cons_iff.1 hok
      have hreg := regime_ne_zero_of_isNever hnev φ
      have hr' : r ≠ 0 := by
        intro h0
        subst h0
        have hpt := eq_pt_of_mem_piR_zero hF'
        rw [hpt] at hF
        exact not_pt_mem_piR_pos hreg hF
      have hAA := piR_dom_unique hreg hr' hF hF'
      exact certs_step hrest hfT hargs hCT hCargs hAd hB hP hgT hx hxs hgargs hlic
        (by rw [hAA]; exact hxA')

/-- **The certified slot**: the argument's type is the domain. -/
theorem Certs.cert_sound {d : Nat} {lic : Bool} {ty body arg ta : Expr md} {mb : BinderMeta}
    {rest : List (Expr md)} (hta : InferIOS M φ d arg ta) (hd : DefEqS M φ d ta ty)
    (hrest : CertsS M φ d lic (body.instantiate1 arg) rest) :
    CertsS M φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT hargs σ hCT hCargs A hA hgT vs hvs hgargs hlic
  cases hvs with
  | cons hx hxs =>
    cases hA with
    | pi hAd hB hP =>
      have hpb := Frame.pi_parts hfT
      have hfarg := hargs _ List.mem_cons_self
      have hCarg := hCargs _ List.mem_cons_self
      have hCty : Ctx M φ σ ty := hCT.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
      obtain ⟨hgty, -⟩ := Gr.pi_iff.1 hgT
      obtain ⟨hfta, hsubta, k⟩ := hta hfarg
      obtain ⟨T', hT', hgT', hxT'⟩ := k σ hCarg _ hx (hgargs _ List.mem_cons_self)
      obtain rfl := hd hfta hpb.ty σ (hCarg.of_subset hsubta) hCty _ _ hT' hAd hgT' hgty
      exact certs_step hrest hfT hargs hCT hCargs hAd hB hP hgT hx hxs hgargs hlic hxT'

/-! ## The licence from a graded spine -/

/-- A spine's grading grades its head. -/
theorem Gr.mkAppN_head {σ : Nat → V} :
    ∀ {as : List (Expr md)} {g : Expr md}, Gr M φ σ (Expr.mkAppN g as) → Gr M φ σ g
  | [], _, h => h
  | b :: bs, g, h => (Gr.app_iff.1 (Gr.mkAppN_head (as := bs) (g := .app g b) h)).1

/-- **A graded spine applies its head on the domains**, the licence a licensed walk takes. -/
theorem spineOk_of_graded {σ : Nat → V} :
    ∀ {args : List (Expr md)} {f : Expr md} {F : V} {vs : List V},
      Gr M φ σ (Expr.mkAppN f args) → Den M φ σ f F → DenList M φ σ args vs → SpineOk F vs
  | [], _, _, _, _, _, hvs => by cases hvs; exact True.intro
  | a :: as, f, F, _, hg, hF, hvs => by
    cases hvs with
    | cons hx hxs =>
      have hga : Gr M φ σ (.app f a) := Gr.mkAppN_head (as := as) hg
      obtain ⟨-, -, r, A, F', X, B, hF', hX', hm, hxA, -⟩ := Gr.app_iff.1 hga
      obtain rfl := DenotesO.functional hF' hF
      obtain rfl := DenotesO.functional hX' hx
      exact SpineOk.cons_iff.2 ⟨⟨r, A, B, hm, hxA⟩,
        spineOk_of_graded (args := as) (f := .app f a) hg (.app hF' hX') hxs⟩

/-! ## From the walk to `Fits` -/

/-- **`Fits` at open terms**: the domains read by `DenotesO` at the free-variable
assignment `σ`. -/
inductive FitsO (M : Model V env) (φ : LevelParam → Nat) (σ : Nat → V) :
    (BVarIdx → V) → Expr md → List V → (BVarIdx → V) → Expr md → Prop
  | nil {ρ : BVarIdx → V} {T : Expr md} : FitsO M φ σ ρ T [] ρ T
  | cons {ρ ρ' : BVarIdx → V} {A B R : Expr md} {m : BinderMeta} {X x : V} {xs : List V} :
      DenotesO M.cval env φ σ ρ A X → x ∈ˢ X → FitsO M φ σ (push x ρ) B xs ρ' R →
      FitsO M φ σ ρ (.forallE A B m) (x :: xs) ρ' R

/-- A fit of a telescope with no free variable is the laws' `Fits`. -/
theorem FitsO.to_fits {σ : Nat → V} {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : FitsO M φ σ ρ T xs ρ' R) (hT : T.hasFvar = false) : Fits M.cval env φ ρ T xs ρ' R := by
  induction h with
  | nil => exact .nil
  | cons hA hx _ ih =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hT
    exact .cons (hA.to_denotes hT.1) hx (ih hT.2)

/-- **A fit of an instantiated telescope is a fit of the telescope with the value inserted**,
at a telescope with a binder for every value; the residuals correspond. -/
theorem FitsO.instantiate1 {σ : Nat → V} {a : Expr md} {x : V}
    (ha : ∀ ρ, DenotesO M.cval env φ σ ρ a x) :
    ∀ (xs : List V) (T : Expr md) (k : Nat) (ρ ρ' : BVarIdx → V) (R' : Expr md),
      (T.stripPis xs.length).isSome = true →
      FitsO M φ σ ρ (T.instantiate1 a k) xs ρ' R' →
      ∃ R, FitsO M φ σ (insertAt k x ρ) T xs (insertAt (k + xs.length) x ρ') R ∧
        R' = R.instantiate1 a (k + xs.length) := by
  intro xs
  induction xs with
  | nil =>
    intro T k ρ ρ' R' _ h
    cases h
    exact ⟨T, .nil, rfl⟩
  | cons y ys ih =>
    intro T k ρ ρ' R' hs h
    rw [List.length_cons] at hs
    revert h
    match T, hs with
    | .forallE A B m, hs =>
      intro h
      simp only [Expr.stripPis, Option.isSome_map] at hs
      simp only [Expr.instantiate1] at h
      cases h with
      | cons hA hy hrest =>
        obtain ⟨R, hfit, hR⟩ := ih B (k + 1) (push y ρ) ρ' R' hs hrest
        rw [← push_insertAt] at hfit
        have hk : k + (y :: ys).length = k + 1 + ys.length := by simp; omega
        rw [hk]
        exact ⟨R, .cons ((DenotesO.instantiate1 ha A k ρ _).1 hA) hy hfit, hR⟩

/-- **The walk is a fit**, at a telescope with a binder for every argument and arguments with
no loose bound variable. -/
theorem WalkFits.fitsO {σ : Nat → V} {T : Expr md} {args : List (Expr md)} {vs : List V}
    (h : WalkFits M φ σ T args vs) :
    DenList M φ σ args vs → (∀ x ∈ args, x.looseBVarsBounded 0 = true) →
      (T.stripPis args.length).isSome = true → ∃ ρ' R, FitsO M φ σ ρ₀ T vs ρ' R := by
  induction h with
  | nil => exact fun _ _ _ => ⟨ρ₀, _, .nil⟩
  | @cons ty body a mb as A x xs hA hx _ ih =>
    intro hd hb hs
    cases hd with
    | cons hax hds =>
      rw [List.length_cons] at hs
      simp only [Expr.stripPis, Option.isSome_map] at hs
      obtain ⟨ρ', R', hfit⟩ := ih hds (fun y hy => hb y (List.mem_cons_of_mem _ hy))
        (Ix.Kernel.Expr.stripPis_instantiate1_isSome (v := a) as.length 0 hs)
      obtain ⟨R, hfit', -⟩ := FitsO.instantiate1 (Den.all hax (hb a List.mem_cons_self)) xs
        body 0 ρ₀ ρ' R' (by rw [← hds.length_eq]; exact hs) hfit
      rw [insertAt_zero] at hfit'
      exact ⟨_, R, .cons hA hx hfit'⟩

/-- **The walk along a closed telescope is the laws' `Fits`.** -/
theorem WalkFits.fits {σ : Nat → V} {T : Expr md} {args : List (Expr md)} {vs : List V}
    (h : WalkFits M φ σ T args vs) (hd : DenList M φ σ args vs)
    (hb : ∀ x ∈ args, x.looseBVarsBounded 0 = true)
    (hs : (T.stripPis args.length).isSome = true) (hT : T.hasFvar = false) :
    ∃ ρ' R, Fits M.cval env φ ρ₀ T vs ρ' R := by
  obtain ⟨ρ', R, hfit⟩ := h.fitsO hd hb hs
  exact ⟨ρ', R, hfit.to_fits hT⟩

/-! ## `EtaProjCerts` -/

/-- **`EtaProjCerts`' motive**: each listed slot's projection function is stored as a
recursor at the family's level parameters, with a binder for every argument, and its
spine satisfies `CertsS`. -/
def EtaProjCertsS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (T : Key md)
    (us' : List Level) (targs : List (Expr md)) (b : Expr md) (lpsT : List LevelParam)
    (idxs : List Nat) : Prop :=
  ∀ i ∈ idxs, ∃ (cvp : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
    env.find? (projFnName T i) = some (.recInfo cvp mI rP rules) ∧ cvp.levelParams = lpsT ∧
    (cvp.type.stripPis (targs.length + 1)).isSome = true ∧
    CertsS M φ d false (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b])

theorem EtaProjCerts.nil_sound {d : Nat} {T : Key md} {us' : List Level}
    {targs : List (Expr md)} {b : Expr md} {lpsT : List LevelParam} :
    EtaProjCertsS M φ d T us' targs b lpsT [] :=
  fun _ hi => nomatch hi

theorem EtaProjCerts.cons_sound {d : Nat} {T : Key md} {us' : List Level}
    {targs : List (Expr md)} {b : Expr md} {lpsT : List LevelParam} {i : Nat}
    {rest : List Nat} {cvp : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env.find? (projFnName T i) = some (.recInfo cvp mI rP rules))
    (hlps : cvp.levelParams = lpsT)
    (hstrip : (cvp.type.stripPis (targs.length + 1)).isSome = true)
    (hcerts : CertsS M φ d false
      (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b]))
    (hrest : EtaProjCertsS M φ d T us' targs b lpsT rest) :
    EtaProjCertsS M φ d T us' targs b lpsT (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ⟨cvp, mI, rP, rules, hf, hlps, hstrip, hcerts⟩
  · exact hrest j hj'

/-! ## Spines -/

/-- **A spine's denotation** is its head's applied along its arguments'. -/
theorem Den.mkAppN_inv {σ : Nat → V} :
    ∀ {as : List (Expr md)} {f : Expr md} {W : V}, Den M φ σ (Expr.mkAppN f as) W →
      ∃ F vs, Den M φ σ f F ∧ DenList M φ σ as vs ∧ W = vs.foldl app F
  | [], _, _, h => ⟨_, [], h, .nil, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨F', vs, hF', hvs, rfl⟩ := Den.mkAppN_inv (as := as) (f := .app f a) h
    cases hF' with
    | app hF hX => exact ⟨_, _ :: vs, hF, .cons hX hvs, rfl⟩

/-- A spine's grading grades its arguments. -/
theorem Gr.mkAppN_args {σ : Nat → V} :
    ∀ {as : List (Expr md)} {g : Expr md}, Gr M φ σ (Expr.mkAppN g as) → ∀ x ∈ as, Gr M φ σ x
  | [], _, _ => fun _ hx => nomatch hx
  | b :: bs, g, h => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (Gr.app_iff.1 (Gr.mkAppN_head (as := bs) (g := .app g b) h)).2.1
    · exact Gr.mkAppN_args (as := bs) (g := .app g b) h x hx

theorem Frame.getAppArgs {d : Nat} {e : Expr md} (h : Frame d e) :
    ∀ x ∈ e.getAppArgs, Frame d x :=
  fun x hx => ⟨h.1.getAppArgs x hx, looseBVarsBounded_getAppArgs h.2.1 x hx,
    fun l hl => h.2.2 l (fvarLeaves_getAppArgs hx l hl)⟩

theorem Ctx.getAppArgs {σ : Nat → V} {e : Expr md} (h : Ctx M φ σ e) :
    ∀ x ∈ e.getAppArgs, Ctx M φ σ x :=
  fun _ hx => h.of_subset (fvarLeaves_getAppArgs hx)

/-- A term is its head applied to its arguments. -/
theorem eq_mkAppN_of_getAppFn {e : Expr md} {n : Key md} {us : List Level}
    (h : e.getAppFn = .const n us) : e = Expr.mkAppN (.const n us) e.getAppArgs := by
  rw [← h]; exact (Expr.mkAppN_getApp e).symm

/-! ## Stored telescopes -/

/-- A telescope stripped to a `∀` strips one binder further. -/
theorem stripPis_succ_isSome {k : Nat} {e : Expr md} {pre : List (Expr md × BinderMeta)}
    {dom body : Expr md} {bm : BinderMeta} (h : e.stripPis k = some (pre, .forallE dom body bm)) :
    (e.stripPis (k + 1)).isSome = true := by
  rw [Ix.Kernel.stripPis_append k (m := 1) h
    (show (Expr.forallE dom body bm).stripPis 1 = some ([(dom, bm)], body) from rfl)]
  rfl

/-- **The stored telescopes the laws read have their binders**: a unit-like or η-capable
family's type has a binder for each parameter its flag counts, and a recursor with a firing
rule has one for each argument and the major premise. The kernel checks both when it stores
the constant: the capability arities (`EnvWF.indCaps`), and a firing rule's shape
(`Expr.recRulePlain`, or a nested rule's certified shape). -/
def StoredArities (env : Env md) : Prop :=
  (∀ (T : Key md) (cvT : ConstantVal md) (caps : IndCaps md),
    env.find? T = some (.indInfo cvT caps) →
      (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
      (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true)) ∧
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
    env.find? r = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.fire ≠ .inert →
      (cv.type.stripPis (mI + 1)).isSome = true

/-- An environment whose lookups are the environment's keeps the arities. -/
theorem StoredArities.of_find {env env' : Env md} (h : StoredArities env)
    (hf : ∀ n ci, env'.find? n = some ci → env.find? n = some ci) : StoredArities env' :=
  ⟨fun T cvT caps hT => h.1 T cvT caps (hf _ _ hT),
    fun r cv mI rP rules hr => h.2 r cv mI rP rules (hf _ _ hr)⟩

/-- **The fold's invariant holds the arities.** -/
theorem EnvModel.storedArities {V : Type w} [SetTheory V] {env : Env md}
    (m : Ix.Kernel.Model.EnvModel V env) : StoredArities env := by
  refine ⟨fun T cvT caps hf => m.wf.indCaps hf, fun r cv mI rP rules hf rl hrl hfire => ?_⟩
  obtain ⟨⟨cvj, -, hplain, -, -⟩, -, -⟩ := m.rec_ctors r cv mI rP rules hf rl hrl
  cases hfr : rl.fire with
  | inert => exact absurd hfr hfire
  | plain =>
    obtain ⟨pre, dom, body, bm, -, hs, -⟩ := recRulePlain_shapeT (hplain hfr)
    exact stripPis_succ_isSome hs
  | nested lvls pins =>
    obtain ⟨-, -, -, -, -, h6, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
    obtain ⟨pre, dom, body, bm, -, hs, -⟩ :=
      ((h6 cv mI rP rules rfl rl hrl).2.2.2.2 lvls pins hfr).2.2.2
    exact stripPis_succ_isSome hs

end Ix.Kernel.Open
