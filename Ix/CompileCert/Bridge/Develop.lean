import Ix.CompileCert.Bridge.Graded
import Ix.CompileCert.Bridge.Justified

/-!
# M7 X2: the development lemma on the checker's side (the worked instance)

X1 proves that the development (`Ix/Compile/Image/Develop.lean`, its table-free core `hinstP`,
`happP`) is *convertible* to the plain substitution (`develop_conv`), and that inlining an image
is δ followed by the development (`inline_conv`). This module carries that to the checker's model.

1. **The development reduces** (directed form): the β-only development `hinstB`/`happB` (X1's
   core clause for clause, with its η and pair-projection contractions left out: the census found
   neither in any call-site development, `M7-X1-conversion.md` §2, P3b: 0 η, 0 projections)
   **reduces** the plain substitution by β in context (`TRedB`): `developB_red`,
   `instantiateB_red`. So the developed term is not merely convertible to the occurrence but a
   β-reduct of its plain substitution.
2. **The reduction is the checker's**: β-reduction on erased terms is graph-regime β on the
   bridges (`TRedB.bridge`: the reader's binders are `.never`), which is sound on graded readings
   (`RedB.sound`, `Graded.lean`).
3. **The worked instance** (`developB_sem`, `instantiateB_sem`): when the plain substitution's
   bridge is graded, the developed term's bridge denotes the same (and is graded); with the image
   constant's δ-rule, the developed occurrence denotes what the unfolded constant applied to the
   arguments denotes (`inlineB_sem`), and its compiler side is X1's `inline_conv`
   (`inlineB_justified`: `Conv` and the semantics at once).
-/

namespace Ix.CompileCert.Bridge

open Ix (Name Level Expr)
open Ix.CompileCert.Conv (Tm er Env Step Conv Forall2 bind_ok map_ok pure_ok mapM_ok EForall2
  looseRangeP liftP looseRangeP_eq er_liftP)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created)
open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

/-! ## β-reduction on erased terms -/

/-- β in every context, reflexive and transitive. -/
inductive TRedB : Tm → Tm → Prop
  | refl (a : Tm) : TRedB a a
  | trans {a b c : Tm} : TRedB a b → TRedB b c → TRedB a c
  | beta (t b a : Tm) : TRedB (.app (.lam t b) a) (Tm.inst a 0 b)
  | app {f f' a a' : Tm} : TRedB f f' → TRedB a a' → TRedB (.app f a) (.app f' a')
  | lam {t t' b b' : Tm} : TRedB t t' → TRedB b b' → TRedB (.lam t b) (.lam t' b')
  | pi {t t' b b' : Tm} : TRedB t t' → TRedB b b' → TRedB (.pi t b) (.pi t' b')
  | letE {t t' v v' b b' : Tm} : TRedB t t' → TRedB v v' → TRedB b b' →
      TRedB (.letE t v b) (.letE t' v' b')
  | proj (s : Name) (i : Nat) {e e' : Tm} : TRedB e e' → TRedB (.proj s i e) (.proj s i e')

/-- A β-reduction is a conversion (in every environment of rules). -/
theorem TRedB.conv (Γ : Env) {a b : Tm} (h : TRedB a b) : Conv Γ a b := by
  induction h with
  | refl a => exact .refl a
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta t b a => exact .step (.beta t b a)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | proj s i _ ih => exact .proj s i ih

theorem TRedB.appN {f f' : Tm} (hf : TRedB f f') :
    ∀ {as as' : List Tm}, Forall2 TRedB as as' → TRedB (Tm.appN f as) (Tm.appN f' as')
  | [], [], .nil => hf
  | _ :: _, _ :: _, .cons ha hs => by
    simp only [Tm.appN_cons]; exact TRedB.appN (.app hf ha) hs

theorem TRedB.forall2_refl : ∀ (as : List Tm), Forall2 TRedB as as
  | [] => .nil
  | a :: as => .cons (.refl a) (TRedB.forall2_refl as)

/-- β at the head of a spine. -/
theorem TRedB.beta_appN (t b a : Tm) (as : List Tm) :
    TRedB (Tm.appN (.lam t b) (a :: as)) (Tm.appN (Tm.inst a 0 b) as) := by
  rw [Tm.appN_cons]; exact TRedB.appN (.beta t b a) (TRedB.forall2_refl as)

/-! ## The β-only development -/

mutual
/-- X1's `hinstP` without its η and pair-projection contractions. -/
def hinstB : Nat → Expr → Nat → Expr → Except String (Expr × Created)
  | 0, _, _, _ => throw "development: out of fuel"
  | fuel + 1, v, k, e =>
    if looseRangeP e ≤ k then pure (e, .no) else
    match e with
    | .bvar i _ =>
      if i == k then pure (liftP v k 0, .direct)
      else if i > k then pure (Expr.mkBVar (i - 1), .no)
      else pure (e, .no)
    | .app .. => do
      let p := getAppFnArgs e
      let args' ← p.2.toList.mapM fun a => Prod.fst <$> hinstB fuel v k a
      let (h', c) ← hinstB fuel v k p.1
      match c, h' with
      | .no, _ => pure (mkAppN h' args'.toArray, .no)
      | _, .lam .. => do pure ((← happB fuel h' args'), .reduced)
      | c, _ => pure (mkAppN h' args'.toArray, c)
    | .proj s i x _ => do
      let (x', _) ← hinstB fuel v k x
      pure (Expr.mkProj s i x', .no)
    | .lam n t b bi _ => do
      let (t', _) ← hinstB fuel v k t
      let (b', _) ← hinstB fuel v (k + 1) b
      pure (Expr.mkLam n t' b' bi, .no)
    | .forallE n t b bi _ => do
      let (t', _) ← hinstB fuel v k t
      let (b', _) ← hinstB fuel v (k + 1) b
      pure (Expr.mkForallE n t' b' bi, .no)
    | .letE n t x b nd _ => do
      let (t', _) ← hinstB fuel v k t
      let (x', _) ← hinstB fuel v k x
      let (b', _) ← hinstB fuel v (k + 1) b
      pure (Expr.mkLetE n t' x' b' nd, .no)
    | .mdata md x _ => do
      let (x', c) ← hinstB fuel v k x
      pure (Expr.mkMData md x', c)
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => pure (e, .no)

/-- X1's `happP` over `hinstB`. -/
def happB : Nat → Expr → List Expr → Except String Expr
  | 0, _, _ => throw "development: out of fuel"
  | fuel + 1, .lam _ _ b _ _, a :: rest => do
    let (b', _) ← hinstB fuel a 0 b
    happB fuel b' rest
  | _ + 1, f, args => pure (mkAppN f args.toArray)
end

/-- The call-site development, β-only. -/
def instantiateB (f : Expr) (args : Array Expr) : Except String Expr :=
  happB Ix.Compile.Image.defaultFuel f args.toList

theorem hinstB_zero (v : Expr) (k : Nat) (e : Expr) :
    hinstB 0 v k e = .error "development: out of fuel" := by rw [hinstB]; rfl

theorem happB_zero (f : Expr) (args : List Expr) :
    happB 0 f args = .error "development: out of fuel" := by rw [happB]; rfl

theorem happB_succ (fuel : Nat) (f : Expr) (args : List Expr) : happB (fuel + 1) f args =
    match f, args with
    | .lam _ _ b _ _, a :: rest => do
      let (b', _) ← hinstB fuel a 0 b
      happB fuel b' rest
    | f, args => pure (mkAppN f args.toArray) := by
  cases f <;> cases args <;> rfl

theorem forall2_red_of_mapM {fuel : Nat}
    (IH : ∀ v k e r c, hinstB fuel v k e = .ok (r, c) → TRedB (Tm.inst (er v) k (er e)) (er r))
    {v : Expr} {k : Nat} : ∀ {l l' : List Expr},
    EForall2 (fun a b => (Prod.fst <$> hinstB fuel v k a) = .ok b) l l' →
      Forall2 TRedB (l.map fun a => Tm.inst (er v) k (er a)) (l'.map er)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab hs => by
    obtain ⟨⟨b', cb⟩, hb, rfl⟩ := map_ok hab
    exact .cons (IH _ _ _ _ _ hb) (forall2_red_of_mapM IH hs)

/-- **The development reduces the plain substitution** (directed form of X1's `develop_conv`,
β-only). -/
theorem developB_red : ∀ fuel : Nat,
    (∀ v k e r c, hinstB fuel v k e = .ok (r, c) → TRedB (Tm.inst (er v) k (er e)) (er r)) ∧
    (∀ f args r, happB fuel f args = .ok r → TRedB (Tm.appN (er f) (args.map er)) (er r))
  | 0 => ⟨fun v k e r c h => (by rw [hinstB_zero] at h; cases h),
          fun f args r h => (by rw [happB_zero] at h; cases h)⟩
  | fuel + 1 => by
    have IH := developB_red fuel
    refine ⟨fun v k e r c h => ?_, fun f args r h => ?_⟩
    · unfold hinstB at h
      by_cases hr : looseRangeP e ≤ k
      · simp only [hr, ↓reduceIte] at h
        cases pure_ok h
        rw [Tm.inst_of_range_le _ _ _ (by rw [← looseRangeP_eq]; exact hr)]
        exact .refl _
      simp only [hr, ↓reduceIte] at h
      match e, h with
      | .bvar i _, h =>
        by_cases hik : i = k
        · subst hik
          simp only [beq_self_eq_true, ↓reduceIte] at h
          cases pure_ok h
          simp only [er_liftP, er, Tm.inst, ↓reduceIte]; exact .refl _
        · have hik' : (i == k) = false := by simp [hik]
          simp only [hik', Bool.false_eq_true, ↓reduceIte] at h
          by_cases hgt : i > k
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h
            simp only [er, Conv.er_mkBVar, Tm.inst, hik, ↓reduceIte, show k < i from hgt]
            exact .refl _
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h
            simp only [er, Tm.inst, hik, ↓reduceIte, show ¬ k < i from hgt]
            exact .refl _
      | .app f₀ a₀ hh, h =>
        obtain ⟨args', hargs, h⟩ := bind_ok h
        obtain ⟨⟨h', c'⟩, hh', h⟩ := bind_ok h
        have hmap := mapM_ok hargs
        have hrargs := forall2_red_of_mapM IH.1 hmap
        have key : TRedB (Tm.inst (er v) k (er (.app f₀ a₀ hh)))
            (Tm.appN (er h') (args'.map er)) := by
          rw [Conv.er_getAppFnArgs (.app f₀ a₀ hh), Tm.inst_appN, List.map_map]
          exact TRedB.appN (IH.1 _ _ _ _ _ hh') hrargs
        dsimp only at h
        split at h
        · cases pure_ok h
          rw [Conv.er_mkAppN, List.toList_toArray]; exact key
        · obtain ⟨r', hr', h⟩ := bind_ok h
          cases pure_ok h
          exact .trans key (IH.2 _ _ _ hr')
        · cases pure_ok h
          rw [Conv.er_mkAppN, List.toList_toArray]; exact key
      | .proj s i x hh, h =>
        obtain ⟨⟨x', c'⟩, hx, h⟩ := bind_ok h
        cases pure_ok h
        simp only [er, Tm.inst, Conv.er_mkProj]; exact .proj s i (IH.1 _ _ _ _ _ hx)
      | .lam n t b bi hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        simp only [Conv.er_mkLam, er, Tm.inst]; exact .lam (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hb)
      | .forallE n t b bi hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        simp only [Conv.er_mkForallE, er, Tm.inst]; exact .pi (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hb)
      | .letE n t x b nd hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        simp only [Conv.er_mkLetE, er, Tm.inst]
        exact .letE (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hx) (IH.1 _ _ _ _ _ hb)
      | .mdata md x hh, h =>
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        cases pure_ok h
        simp only [Conv.er_mkMData, er]; exact IH.1 _ _ _ _ _ hx
      | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lit .., h =>
        cases pure_ok h; exact .refl _
    · rw [happB_succ] at h
      split at h
      · rename_i b a rest
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        have h1 := IH.2 _ _ _ h
        have h2 := IH.1 _ _ _ _ _ hb
        refine .trans ?_ h1
        simp only [List.map_cons, er]
        exact .trans (TRedB.beta_appN _ _ _ _) (TRedB.appN h2 (TRedB.forall2_refl _))
      · cases pure_ok h
        rw [Conv.er_mkAppN, List.toList_toArray]; exact .refl _

theorem hinstB_red {fuel : Nat} {v : Expr} {k : Nat} {e r : Expr} {c : Created}
    (h : hinstB fuel v k e = .ok (r, c)) : TRedB (Tm.inst (er v) k (er e)) (er r) :=
  (developB_red fuel).1 v k e r c h

/-- **The call-site development reduces the application**. -/
theorem instantiateB_red {f : Expr} {args : Array Expr} {r : Expr}
    (h : instantiateB f args = .ok r) : TRedB (er (mkAppN f args)) (er r) := by
  rw [Conv.er_mkAppN]; exact (developB_red _).2 f args.toList r h

/-! ## β on erased terms is graph-regime β on the bridges -/

section Bridged

variable {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

/-- A β-reduction of supported terms is a graph-regime β-reduction of their bridges, at every
assignment (the reader's binders are `.never`). -/
theorem TRedB.bridge {φ : Kernel.Name → Nat} {a b : Tm} (h : TRedB a b) :
    ∀ {ka : Kernel.Expr}, bridgeT N L a = some ka →
      ∃ kb, bridgeT N L b = some kb ∧ RedB φ ka kb := by
  induction h with
  | refl a => intro ka ha; exact ⟨ka, ha, .refl ka⟩
  | trans _ _ ih1 ih2 =>
    intro ka ha
    obtain ⟨kb, hb, r1⟩ := ih1 ha
    obtain ⟨kc, hc, r2⟩ := ih2 hb
    exact ⟨kc, hc, .trans r1 r2⟩
  | beta t b a =>
    intro ka ha
    obtain ⟨kl, kx, hl, hx, rfl⟩ := bridgeT_app_inv ha
    obtain ⟨kt, kb, ht, hb, rfl⟩ := bridgeT_lam_inv hl
    refine ⟨kb.instantiate1Lift kx 0, ?_, .beta (by simp [regime_never])⟩
    rw [bridgeT_inst hx b 0, hb]; rfl
  | app _ _ ihf iha =>
    intro ka ha
    obtain ⟨kf, kx, hf, hx, rfl⟩ := bridgeT_app_inv ha
    obtain ⟨kf', hf', r1⟩ := ihf hf
    obtain ⟨kx', hx', r2⟩ := iha hx
    exact ⟨_, by simp [bridgeT, hf', hx'], .app r1 r2⟩
  | lam _ _ iht ihb =>
    intro ka ha
    obtain ⟨kt, kb, ht, hb, rfl⟩ := bridgeT_lam_inv ha
    obtain ⟨kt', ht', r1⟩ := iht ht
    obtain ⟨kb', hb', r2⟩ := ihb hb
    exact ⟨_, by simp [bridgeT, ht', hb'], .lam r1 r2⟩
  | pi _ _ iht ihb =>
    intro ka ha
    obtain ⟨kt, kb, ht, hb, rfl⟩ := bridgeT_pi_inv ha
    obtain ⟨kt', ht', r1⟩ := iht ht
    obtain ⟨kb', hb', r2⟩ := ihb hb
    exact ⟨_, by simp [bridgeT, ht', hb'], .pi r1 r2⟩
  | letE _ _ _ iht ihv ihb =>
    intro ka ha
    obtain ⟨kt, kv, kb, ht, hv, hb, rfl⟩ := bridgeT_letE_inv ha
    obtain ⟨kt', ht', r1⟩ := iht ht
    obtain ⟨kv', hv', r2⟩ := ihv hv
    obtain ⟨kb', hb', r3⟩ := ihb hb
    exact ⟨_, by simp [bridgeT, ht', hv', hb'], .letE r1 r2 r3⟩
  | proj s i _ ih =>
    intro ka ha
    obtain ⟨ks, ke, hs, he, rfl⟩ := bridgeT_proj_inv ha
    obtain ⟨ke', he', r1⟩ := ih he
    exact ⟨_, by simp [bridgeT, hs, he'], .proj r1⟩

end Bridged

/-! ## The worked instance -/

section Instance

universe u

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}
  {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

/-- **The development on the checker's side**: when the plain substitution's bridge is graded,
the developed term's bridge exists, denotes the same, and is graded. -/
theorem developB_sem {fuel : Nat} {v : Expr} {k : Nat} {e r : Expr} {c : Created}
    (h : hinstB fuel v k e = .ok (r, c)) {ρ : Nat → V} {kp : Kernel.Expr}
    (hp : bridgeT N L (Tm.inst (er v) k (er e)) = some kp) (g : Graded cval env φ ρ kp) :
    ∃ kr, bridge N L r = some kr ∧ SemEq cval env φ ρ kp kr ∧ Graded cval env φ ρ kr := by
  obtain ⟨kr, hr, red⟩ := (hinstB_red h).bridge (φ := φ) hp
  exact ⟨kr, hr, (red.sound g).1, (red.sound g).2⟩

/-- **The call-site development on the checker's side**: a graded bridged application and its
β-only development denote the same. -/
theorem instantiateB_sem {f : Expr} {args : Array Expr} {r : Expr}
    (h : instantiateB f args = .ok r) {ρ : Nat → V} {ka : Kernel.Expr}
    (ha : bridge N L (mkAppN f args) = some ka) (g : Graded cval env φ ρ ka) :
    ∃ kr, bridge N L r = some kr ∧ SemEq cval env φ ρ ka kr ∧ Graded cval env φ ρ kr := by
  obtain ⟨kr, hr, red⟩ := (instantiateB_red h).bridge (φ := φ) ha
  exact ⟨kr, hr, (red.sound g).1, (red.sound g).2⟩

/-- **The inlined image occurrence denotes what the unfolded constant does** (the worked
instance of the development lemma on the checker's side). The compiler inlines the image constant
`n` at the call site `n.{us} args` as the development `r` of its value; on the checker's side the
occurrence's bridge (the constant applied to the arguments) and `r`'s bridge denote the same,
given: the constant's installed value at the occurrence's levels reads, in the graph regime, like
the bridge of the compiler's instantiated value (`Emitted` per compile, the annotation lemma at a
graph-regime assignment), and the unfolded application's bridge is graded. -/
theorem inlineB_sem (strong : StrongInstalledModel V env) {c : Kernel.Name}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (lookup : env.find? c = some (.defnInfo header value hint)) {ls : List Kernel.Level}
    (arity : ls.length = header.levelParams.length) {ρ : Nat → V}
    {val : Expr} {args : Array Expr} {r : Expr} {kval : Kernel.Expr} {kargs : List Kernel.Expr}
    (hval : bridge N L val = some kval) (hargs : optMap (bridgeT N L) (args.toList.map er) = some kargs)
    (hskel : (value.instantiateLevelParams header.levelParams ls).erasePw = kval)
    (hpos : PosAt φ (value.instantiateLevelParams header.levelParams ls))
    (h : instantiateB val args = .ok r)
    (g : Graded strong.public.cval env φ ρ (Kernel.Expr.mkAppN kval kargs)) :
    ∃ kr, bridge N L r = some kr ∧
      SemEq strong.public.cval env φ ρ (Kernel.Expr.mkAppN (.const c ls) kargs) kr := by
  have hunf : bridge N L (mkAppN val args) = some (Kernel.Expr.mkAppN kval kargs) := by
    unfold bridge; rw [Conv.er_mkAppN]; exact bridgeT_appN _ _ hval hargs
  obtain ⟨kr, hr, sem, -⟩ := instantiateB_sem h hunf g
  refine ⟨kr, hr, SemEq.trans ?_ sem⟩
  -- δ, then the installed value read as the bridge (graph regime)
  have hδ := semEq_delta (φ := φ) (ρ := ρ) strong lookup arity
  obtain ⟨w, hw1, hw2⟩ := hδ
  have hw2' : Denotes strong.public.cval env φ ρ kval w :=
    denotes_of_erasePw_pos (by rw [hskel, bridgeT_erasePw _ hval]) hpos
      (bridgeT_posAt _ hval) hw2
  have hsem : SemEq strong.public.cval env φ ρ (.const c ls) kval := ⟨w, hw1, hw2'⟩
  have hspine : KForall2 (SemEq strong.public.cval env φ ρ) kargs kargs := by
    -- every argument of a graded spine denotes
    have key : ∀ (f : Kernel.Expr) (as : List Kernel.Expr),
        Graded strong.public.cval env φ ρ (Kernel.Expr.mkAppN f as) →
          KForall2 (SemEq strong.public.cval env φ ρ) as as := by
      intro f as
      induction as generalizing f with
      | nil => intro _; exact .nil
      | cons a as ih =>
        intro hg
        have hg' := ih (.app f a) hg
        have ga : Graded strong.public.cval env φ ρ a := by
          clear ih hg'
          have : ∀ (f : Kernel.Expr) (bs : List Kernel.Expr),
              Graded strong.public.cval env φ ρ (Kernel.Expr.mkAppN f bs) →
                Graded strong.public.cval env φ ρ f := by
            intro f bs
            induction bs generalizing f with
            | nil => exact id
            | cons b bs ihb => intro h'; exact (ihb (.app f b) h').1
          exact (this (.app f a) as hg).2.1
        obtain ⟨x, hx⟩ := ga.denotes
        exact .cons (SemEq.refl hx) hg'
    exact key kval kargs g
  exact SemEq.appN hsem hspine

/-- **The worked instance as one justified conversion**: the compiler side is X1's `inline_conv`
(the inlined term is convertible to the occurrence, given the image's δ-rule), the checker side
`inlineB_sem` (the two bridges denote the same). -/
theorem inlineB_justified (strong : StrongInstalledModel V env) (Γ : Env) {n : Name}
    {lps : Array Name} {val : Expr} {us : Array Level} {args : Array Expr} {r : Expr}
    (hδ : Γ.ax (.const n us) (er (Ix.Compile.Canon.substLevels lps us val)))
    (h : instantiateB (Ix.Compile.Canon.substLevels lps us val) args = .ok r)
    {c : Kernel.Name} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} (lookup : env.find? c = some (.defnInfo header value hint))
    {ls : List Kernel.Level} (arity : ls.length = header.levelParams.length) {ρ : Nat → V}
    {kval : Kernel.Expr} {kargs : List Kernel.Expr}
    (hval : bridge N L (Ix.Compile.Canon.substLevels lps us val) = some kval)
    (hargs : optMap (bridgeT N L) (args.toList.map er) = some kargs)
    (hc : N n = some c) (hls : optMap L us.toList = some ls)
    (hskel : (value.instantiateLevelParams header.levelParams ls).erasePw = kval)
    (hpos : PosAt φ (value.instantiateLevelParams header.levelParams ls))
    (g : Graded strong.public.cval env φ ρ (Kernel.Expr.mkAppN kval kargs)) :
    ∃ kr, bridge N L r = some kr ∧
      Justified Γ N L strong.public.cval env φ ρ (er (mkAppN (Expr.mkConst n us) args))
        (Kernel.Expr.mkAppN (.const c ls) kargs) (er r) kr := by
  obtain ⟨kr, hr, sem⟩ := inlineB_sem (N := N) (L := L) strong lookup arity hval hargs hskel hpos h g
  refine ⟨kr, hr, ?_, skel_of_bridgeT hr, ?_, sem⟩
  · apply skel_of_bridgeT
    rw [Conv.er_mkAppN, Conv.er_mkConst]
    exact bridgeT_appN _ _ (by simp [bridgeT, hc, hls]) hargs
  · have hred := instantiateB_red h
    have hconv := hred.conv Γ
    rw [Conv.er_mkAppN] at hconv ⊢
    exact .trans (Conv.appN (.step (.ax hδ)) (Conv.forall₂_refl _)) hconv

end Instance

end Ix.CompileCert.Bridge
