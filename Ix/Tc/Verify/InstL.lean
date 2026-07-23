import Ix.Tc.Verify.Trans
import Ix.Tc.Verify.InstUniv

/-!
# Universe instantiation tracks `VExpr.instL` through the translation

The expression side of the M2→M3 seam: `KExpr.instUnivSpec` (the pure
spec of the production walker `TcM.instUnivInner`, Verify/InstUniv.lean)
corresponds to the Theory's `VExpr.instL` — into the defeq QUOTIENT
`TrKExpr`, because `substUniv` rebuilds levels with the simplifying
smart constructors, which are only `≈`-sound (`substUniv_toVLevel`).
Upstream analog: `TrExprS.instL` (Verify/Typing/Lemmas.lean:1482); our
`sort`/`const` cases ride `substUniv_toVLevel`/`substUniv_wf` instead
of the `substParams_wf` `ofLevel` machinery, and the literal cases are
direct (`instL`-invariance of the closed encodings).

The collision-freedom and no-wrap side conditions quantify over
`KExpr.LevelReach` — the levels of `e` together with everything
`substUniv` can compare while rewriting them (`SubstUnivReach`
per level).
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLevel VEnv)

/-! ### Level occurrences and the reach set -/

/-- The levels of an expression: `sort` payloads and `const` level
    arguments, through all subterms. -/
inductive KExpr.HasLevel {m : Mode} : KExpr m → KUniv m → Prop
  | sort {u : KUniv m} {md : ExprInfo m} : HasLevel (.sort u md) u
  | const {id : KId m} {us : Array (KUniv m)} {md : ExprInfo m}
      {u : KUniv m} :
    u ∈ us → HasLevel (.const id us md) u
  | app_f {f a : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel f u → HasLevel (.app f a md) u
  | app_a {f a : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel a u → HasLevel (.app f a md) u
  | lam_ty {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.lam n bi ty body md) u
  | lam_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.lam n bi ty body md) u
  | all_ty {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.all n bi ty body md) u
  | all_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.all n bi ty body md) u
  | letE_ty {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.letE n ty val body nd md) u
  | letE_val {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel val u → HasLevel (.letE n ty val body nd md) u
  | letE_body {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.letE n ty val body nd md) u
  | prj {id : KId m} {field : UInt64} {val : KExpr m} {md : ExprInfo m}
      {u : KUniv m} :
    HasLevel val u → HasLevel (.prj id field val md) u

/-- Level-side reach set of the instantiation walk on `e`: everything
    `substUniv us` can address-compare while rewriting `e`'s levels.
    Finite and spec-determined (union of `SubstUnivReach` over the
    levels of `e`) — never closed under constructors. -/
def KExpr.LevelReach {m : Mode} (us : Array (KUniv m)) (e : KExpr m)
    (x : KUniv m) : Prop :=
  ∃ u, KExpr.HasLevel e u ∧ KUniv.SubstUnivReach us u x

namespace KExpr.LevelReach

variable {m : Mode} {us : Array (KUniv m)} {x : KUniv m}

theorem app_f {f a : KExpr m} {md : ExprInfo m}
    (h : LevelReach us f x) : LevelReach us (.app f a md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .app_f hu, hr⟩

theorem app_a {f a : KExpr m} {md : ExprInfo m}
    (h : LevelReach us a x) : LevelReach us (.app f a md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .app_a hu, hr⟩

theorem lam_ty {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us ty x) : LevelReach us (.lam n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .lam_ty hu, hr⟩

theorem lam_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us body x) :
    LevelReach us (.lam n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .lam_body hu, hr⟩

theorem all_ty {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us ty x) : LevelReach us (.all n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .all_ty hu, hr⟩

theorem all_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us body x) :
    LevelReach us (.all n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .all_body hu, hr⟩

theorem letE_ty {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us ty x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_ty hu, hr⟩

theorem letE_val {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us val x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_val hu, hr⟩

theorem letE_body {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us body x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_body hu, hr⟩

theorem prj {id : KId m} {field : UInt64} {val : KExpr m}
    {md : ExprInfo m} (h : LevelReach us val x) :
    LevelReach us (.prj id field val md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .prj hu, hr⟩

end KExpr.LevelReach

/-! ### `Except`-valued `mapM` decomposition -/

private theorem list_mapM_ok {ε α β : Type _} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      List.Forall₂ (fun a b => f a = .ok b) l l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rw [List.mapM_nil] at h
    cases h
    exact .nil
  | cons a l ih =>
    intro l' h
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error err => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hml : l.mapM f with
      | error err => rw [hml] at h; cases h
      | ok bs =>
        rw [hml] at h
        cases h
        exact .cons hfa (ih hml)

private theorem array_mapM_ok {ε α β : Type _} {f : α → Except ε β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = .ok ys) :
    List.Forall₂ (fun a b => f a = .ok b) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hml : xs.toList.mapM f with
  | error err => rw [hml] at h; cases h
  | ok l' =>
    rw [hml] at h
    cases h
    simpa using list_mapM_ok hml

private theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; cases hb
  | cons hab _ ih =>
    intro b hb
    cases hb with
    | head => exact ⟨_, List.mem_cons_self, hab⟩
    | tail _ hb =>
      obtain ⟨a, ha, hr⟩ := ih _ hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Per-element `substUniv ≈ inst` over a successful `mapM`, in the
    `Forall₂ (· ≈ ·)` form `constDF` consumes. -/
private theorem forall₂_toVLevel {us : Array (KUniv .anon)} :
    ∀ {l l' : List (KUniv .anon)},
      List.Forall₂ (fun a b => TcM.substUniv a us = .ok b) l l' →
      (∀ u ∈ l, ∀ x y, KUniv.SubstUnivReach us u x →
        KUniv.SubstUnivReach us u y → x.AddrFaithful y) →
      (∀ u ∈ l, ∀ x, KUniv.SubstUnivReach us u x →
        x.size < UInt64.size) →
      List.Forall₂ (· ≈ ·) (l'.map KUniv.toVLevel)
        ((l.map KUniv.toVLevel).map
          (·.inst (us.toList.map KUniv.toVLevel))) := by
  intro l l' h
  induction h with
  | nil => intro _ _; exact .nil
  | @cons a b l l' hab _ ih =>
    intro hcf hsz
    refine .cons ?_ (ih ?_ ?_)
    · exact TcM.substUniv_toVLevel hab
        (hcf a (List.mem_cons_self))
        (hsz a (List.mem_cons_self))
    · exact fun u hu => hcf u (List.mem_cons_of_mem _ hu)
    · exact fun u hu => hsz u (List.mem_cons_of_mem _ hu)

/-! ### Closed literal encodings are `instL`-invariant

(`VExpr.instL_natLit` is upstream; the string encoding's constant
spine carries only the literal level `.zero`, which `inst` fixes.) -/

private theorem instL_listCharLit (s : List Char) (ls : List VLevel) :
    (Lean4Lean.VExpr.listCharLit s).instL ls
      = Lean4Lean.VExpr.listCharLit s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    show Lean4Lean.VExpr.app (Lean4Lean.VExpr.app _ (Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.natLit c.toNat).instL ls)))
      ((Lean4Lean.VExpr.listCharLit s).instL ls) = _
    rw [Lean4Lean.VExpr.instL_natLit, ih]
    rfl

private theorem instL_trLiteral (l : Lean.Literal) (ls : List VLevel) :
    (Lean4Lean.VExpr.trLiteral l).instL ls
      = Lean4Lean.VExpr.trLiteral l := by
  cases l with
  | natVal v => exact Lean4Lean.VExpr.instL_natLit
  | strVal s =>
    show Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.listCharLit _).instL ls) = _
    rw [instL_listCharLit]
    rfl

/-! ### The master -/

/-- Context re-basing for the instantiated context: `WF.instL` keyed by
    the array (`ls.length = us.size` bridged once here). -/
private theorem wf_instL_size {env : VEnv} {us : Array (KUniv .anon)}
    {U' : Nat} (hus : ∀ w ∈ us, (KUniv.toVLevel w).WF U')
    {Δ : KVLCtx} (hΔ : KVLCtx.WF env us.size Δ) :
    KVLCtx.WF env U' (Δ.instL (us.toList.map KUniv.toVLevel)) := by
  refine KVLCtx.WF.instL (fun l hl => ?_) ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
    exact hus w (by simpa using hw)
  · simpa using hΔ

/-- **Universe instantiation** — `instUnivSpec` tracks the Theory's
    `VExpr.instL` through the translation, into the defeq quotient
    (upstream `TrExprS.instL`). `heq` pins the instantiation arity to
    the source parameter count (always true at the `checkConst` call
    site); `hcf`/`hsz` are the level-side collision-freedom and no-wrap
    conditions over the walk's reach set. -/
theorem TrKExprS.instL {env : VEnv} {uvars U' : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env U' [] (VExpr.trLiteral l))
    (htp : TrProjOK env U' trProj)
    {us : Array (KUniv .anon)}
    (hus : ∀ w ∈ us, (KUniv.toVLevel w).WF U')
    (heq : uvars = us.size)
    {Δ : KVLCtx} {e : KExpr .anon} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ e e') :
    ∀ {r : KExpr .anon},
      KVLCtx.WF env uvars Δ →
      KExpr.instUnivSpec e us = .ok r →
      (∀ x y, KExpr.LevelReach us e x → KExpr.LevelReach us e y →
        x.AddrFaithful y) →
      (∀ x, KExpr.LevelReach us e x → x.size < UInt64.size) →
      TrKExpr env U' nameOf trProj
        (Δ.instL (us.toList.map KUniv.toVLevel)) r
        (e'.instL (us.toList.map KUniv.toVLevel)) := by
  subst heq
  have hls' : ∀ l ∈ us.toList.map KUniv.toVLevel, l.WF U' := by
    intro l hl
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
    exact hus w (by simpa using hw)
  induction H with
  | @var Δ i nm md e A l1 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.var i nm md) us
        = .ok (.var i nm md) := rfl
    rw [hb] at hr
    cases hr
    exact (TrKExprS.var (KVLCtx.find?_instL l1)).trKExpr henv.ordered
      hlit htp.wf (wf_instL_size hus hΔ)
  | @fvar Δ fv nm md e A l1 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.fvar fv nm md) us
        = .ok (.fvar fv nm md) := rfl
    rw [hb] at hr
    cases hr
    exact (TrKExprS.fvar (KVLCtx.find?_instL l1)).trKExpr henv.ordered
      hlit htp.wf (wf_instL_size hus hΔ)
  | @sort Δ u md l1 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.sort u md) us
        = (TcM.substUniv u us >>= fun v =>
            pure (KExpr.mkSort v)) := rfl
    cases hs : TcM.substUniv u us with
    | error err => rw [hb, hs] at hr; cases hr
    | ok v =>
      rw [hb, hs] at hr
      cases hr
      rw [KExpr.mkSort_shape]
      exact ⟨_, .sort (TcM.substUniv_wf hus hs), _,
        .sortDF (TcM.substUniv_wf hus hs) (VLevel.WF.inst hls')
          (TcM.substUniv_toVLevel hs
            (fun x y hx hy => hcf x y ⟨u, .sort, hx⟩ ⟨u, .sort, hy⟩)
            (fun x hx => hsz x ⟨u, .sort, hx⟩))⟩
  | @const Δ id curUs md c ci l1 l2 l3 l4 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.const id curUs md) us
        = (curUs.mapM (TcM.substUniv · us) >>= fun vs =>
            pure (KExpr.mkConst id vs)) := rfl
    cases hmus : curUs.mapM (TcM.substUniv · us) with
    | error err => rw [hb, hmus] at hr; cases hr
    | ok vs =>
      rw [hb, hmus] at hr
      cases hr
      rw [KExpr.mkConst_shape]
      have harr := array_mapM_ok hmus
      have hsize : vs.size = curUs.size := by
        rw [← Array.length_toList, ← Array.length_toList]
        exact harr.length_eq.symm
      have hwf : ∀ w ∈ vs, (KUniv.toVLevel w).WF U' := by
        intro w hw
        obtain ⟨a, _, hab⟩ := forall₂_mem_right harr w (by simpa using hw)
        exact TcM.substUniv_wf hus hab
      refine ⟨_, .const l1 l2 hwf (hsize.trans l4), _,
        .constDF l2 ?_ ?_ ?_ ?_⟩
      · intro l hl
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
        exact hwf w (by simpa using hw)
      · intro l hl
        obtain ⟨l0, _, rfl⟩ := List.mem_map.1 hl
        exact VLevel.WF.inst hls'
      · simpa using hsize.trans l4
      · exact forall₂_toVLevel harr
          (fun a ha x y hx hy => hcf x y
            ⟨a, .const (by simpa using ha), hx⟩
            ⟨a, .const (by simpa using ha), hy⟩)
          (fun a ha x hx => hsz x ⟨a, .const (by simpa using ha), hx⟩)
  | @app Δ f a md f' a' A B l1 l2 h3 h4 ih3 ih4 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.app f a md) us
        = (KExpr.instUnivSpec f us >>= fun rf =>
            KExpr.instUnivSpec a us >>= fun ra =>
              pure (KExpr.mkApp rf ra)) := rfl
    cases hsf : KExpr.instUnivSpec f us with
    | error err => rw [hb, hsf] at hr; cases hr
    | ok rf =>
      cases hsa : KExpr.instUnivSpec a us with
      | error err => rw [hb, hsf, hsa] at hr; cases hr
      | ok ra =>
        rw [hb, hsf, hsa] at hr
        cases hr
        rw [KExpr.mkApp_shape]
        have hf' := ih3 hΔ hsf
          (fun x y hx hy => hcf x y hx.app_f hy.app_f)
          (fun x hx => hsz x hx.app_f)
        have ha' := ih4 hΔ hsa
          (fun x y hx hy => hcf x y hx.app_a hy.app_a)
          (fun x hx => hsz x hx.app_a)
        have h1' := l1.instL hls'
        have h2' := l2.instL hls'
        rw [← KVLCtx.instL_toCtx] at h1' h2'
        exact TrKExpr.app henv (wf_instL_size hus hΔ) h1' h2' hf' ha'
  | @lam Δ nm bi ty body md ty' body' l1 h2 h3 ih2 ih3 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.lam nm bi ty body md) us
        = (KExpr.instUnivSpec ty us >>= fun rty =>
            KExpr.instUnivSpec body us >>= fun rbody =>
              pure (KExpr.mkLam nm bi rty rbody)) := rfl
    cases hsty : KExpr.instUnivSpec ty us with
    | error err => rw [hb, hsty] at hr; cases hr
    | ok rty =>
      cases hsbody : KExpr.instUnivSpec body us with
      | error err => rw [hb, hsty, hsbody] at hr; cases hr
      | ok rbody =>
        rw [hb, hsty, hsbody] at hr
        cases hr
        rw [KExpr.mkLam_shape]
        have hty' := ih2 hΔ hsty
          (fun x y hx hy => hcf x y hx.lam_ty hy.lam_ty)
          (fun x hx => hsz x hx.lam_ty)
        have hbody' := ih3 ⟨hΔ, nofun, l1⟩ hsbody
          (fun x y hx hy => hcf x y hx.lam_body hy.lam_body)
          (fun x hx => hsz x hx.lam_body)
        have h1' := l1.instL hls'
        rw [← KVLCtx.instL_toCtx] at h1'
        exact TrKExpr.lam henv hlit htp (wf_instL_size hus hΔ) h1'
          hty' hbody'
  | @all Δ nm bi ty body md ty' body' l1 l2 h3 h4 ih3 ih4 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.all nm bi ty body md) us
        = (KExpr.instUnivSpec ty us >>= fun rty =>
            KExpr.instUnivSpec body us >>= fun rbody =>
              pure (KExpr.mkAll nm bi rty rbody)) := rfl
    cases hsty : KExpr.instUnivSpec ty us with
    | error err => rw [hb, hsty] at hr; cases hr
    | ok rty =>
      cases hsbody : KExpr.instUnivSpec body us with
      | error err => rw [hb, hsty, hsbody] at hr; cases hr
      | ok rbody =>
        rw [hb, hsty, hsbody] at hr
        cases hr
        rw [KExpr.mkAll_shape]
        have hty' := ih3 hΔ hsty
          (fun x y hx hy => hcf x y hx.all_ty hy.all_ty)
          (fun x hx => hsz x hx.all_ty)
        have hbody' := ih4 ⟨hΔ, nofun, l1⟩ hsbody
          (fun x y hx hy => hcf x y hx.all_body hy.all_body)
          (fun x hx => hsz x hx.all_body)
        have h1' := l1.instL hls'
        have h2' := l2.instL hls'
        rw [← KVLCtx.instL_toCtx] at h1'
        rw [List.map_cons, ← KVLCtx.instL_toCtx] at h2'
        exact TrKExpr.all henv hlit htp (wf_instL_size hus hΔ) h1' h2'
          hty' hbody'
  | @letE Δ nm ty val body nd md ty' val' body' l1 h2 h3 h4 ih2 ih3
      ih4 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.letE nm ty val body nd md) us
        = (KExpr.instUnivSpec ty us >>= fun rty =>
            KExpr.instUnivSpec val us >>= fun rval =>
              KExpr.instUnivSpec body us >>= fun rbody =>
                pure (KExpr.mkLet nm rty rval rbody nd)) := rfl
    cases hsty : KExpr.instUnivSpec ty us with
    | error err => rw [hb, hsty] at hr; cases hr
    | ok rty =>
      cases hsval : KExpr.instUnivSpec val us with
      | error err => rw [hb, hsty, hsval] at hr; cases hr
      | ok rval =>
        cases hsbody : KExpr.instUnivSpec body us with
        | error err => rw [hb, hsty, hsval, hsbody] at hr; cases hr
        | ok rbody =>
          rw [hb, hsty, hsval, hsbody] at hr
          cases hr
          rw [KExpr.mkLet_shape]
          have hty' := ih2 hΔ hsty
            (fun x y hx hy => hcf x y hx.letE_ty hy.letE_ty)
            (fun x hx => hsz x hx.letE_ty)
          have hval' := ih3 hΔ hsval
            (fun x y hx hy => hcf x y hx.letE_val hy.letE_val)
            (fun x hx => hsz x hx.letE_val)
          have hbody' := ih4 ⟨hΔ, nofun, l1⟩ hsbody
            (fun x y hx hy => hcf x y hx.letE_body hy.letE_body)
            (fun x hx => hsz x hx.letE_body)
          have h1' := l1.instL hls'
          rw [← KVLCtx.instL_toCtx] at h1'
          exact TrKExpr.letE henv hlit htp (wf_instL_size hus hΔ) h1'
            hty' hval' hbody'
  | @prj Δ sid field val md sName e1 e2 l1 h2 l3 ih =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.prj sid field val md) us
        = (KExpr.instUnivSpec val us >>= fun rval =>
            pure (KExpr.mkPrj sid field rval)) := rfl
    cases hsv : KExpr.instUnivSpec val us with
    | error err => rw [hb, hsv] at hr; cases hr
    | ok rval =>
      rw [hb, hsv] at hr
      cases hr
      rw [KExpr.mkPrj_shape]
      have hval' := ih hΔ hsv
        (fun x y hx hy => hcf x y hx.prj hy.prj)
        (fun x hx => hsz x hx.prj)
      have h3' := htp.instL hls' l3
      rw [← KVLCtx.instL_toCtx] at h3'
      exact TrKExpr.prj henv htp (wf_instL_size hus hΔ) l1 hval' h3'
  | @nat Δ n blob md l1 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.nat n blob md) us
        = .ok (.nat n blob md) := rfl
    rw [hb] at hr
    cases hr
    rw [show (Lean4Lean.VExpr.natLit n).instL
          (us.toList.map KUniv.toVLevel)
        = Lean4Lean.VExpr.natLit n from Lean4Lean.VExpr.instL_natLit]
    exact (TrKExprS.nat l1).trKExpr henv.ordered hlit htp.wf
      (wf_instL_size hus hΔ)
  | @str Δ s blob md l1 =>
    intro r hΔ hr hcf hsz
    have hb : KExpr.instUnivSpec (.str s blob md) us
        = .ok (.str s blob md) := rfl
    rw [hb] at hr
    cases hr
    rw [instL_trLiteral]
    exact (TrKExprS.str l1).trKExpr henv.ordered hlit htp.wf
      (wf_instL_size hus hΔ)

end Ix.Tc
