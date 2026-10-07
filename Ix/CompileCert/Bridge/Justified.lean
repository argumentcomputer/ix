import Ix.CompileCert.Bridge.Rules

/-!
# M7 X2: justified conversions, `Conv` and its semantics at once

`Justified Γ N L cval env φ ρ s a s' b` packages one conversion seen from both sides: the compiler
side (`Conv Γ s s'`, X1's relation on erased skeletons) and the checker side (`SemEq … a b`, equal
denotations of the annotated terms), with `a`, `b` annotations of the bridges of `s`, `s'`
(`Skel`). Every constructor of X1's `Conv` has a `Justified` counterpart carrying exactly the
semantic premise its rule needs (`Rules.lean`); so a downstream proof follows its syntactic
derivation step by step and ends with both statements:

* `Justified.refl`, `.symm`, `.trans`; congruences `.app`, `.appN`, `.lam`, `.pi`, `.proj`;
* `Justified.beta` (premise: the argument in the abstraction's domain),
  `.beta_graph` (graph regime: the premise from the application's typing),
  `.eta` (premise: the function in the product over the binder's own domain and regime),
  `.delta` (an installed definition whose instantiated value has the skeleton of the compiler's
  δ-rule right-hand side: `Emitted` plus the level instantiation, supplied per compile or by
  L4), `.ax` for any rule of `Γ` whose semantics is supplied.

`Justified.conv` and `Justified.sem` are the two halves of **conversion soundness**.
-/

namespace Ix.CompileCert.Bridge

open Ix.CompileCert.Conv (Tm er Env Step Conv)
open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

universe u

section Justified

variable {V : Type u} [Kernel.SetTheory V]

variable (Γ : Env) (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level)
  (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env) (φ : Kernel.Name → Nat)

/-- A conversion on the compiler side whose bridged annotations denote the same set. -/
structure Justified (ρ : Nat → V) (s : Tm) (a : Kernel.Expr) (s' : Tm) (b : Kernel.Expr) : Prop where
  skel_left : Skel N L s a
  skel_right : Skel N L s' b
  conv : Conv Γ s s'
  sem : SemEq cval env φ ρ a b

variable {Γ N L cval env φ}

namespace Justified

theorem refl {ρ : Nat → V} {s : Tm} {a : Kernel.Expr} {v : V} (hs : Skel N L s a)
    (ha : Denotes cval env φ ρ a v) : Justified Γ N L cval env φ ρ s a s a :=
  ⟨hs, hs, Conv.refl s, SemEq.refl ha⟩

theorem symm {ρ : Nat → V} {s s' : Tm} {a b : Kernel.Expr}
    (h : Justified Γ N L cval env φ ρ s a s' b) : Justified Γ N L cval env φ ρ s' b s a :=
  ⟨h.skel_right, h.skel_left, Conv.symm h.conv, h.sem.symm⟩

theorem trans {ρ : Nat → V} {s s' s'' : Tm} {a b c : Kernel.Expr}
    (h1 : Justified Γ N L cval env φ ρ s a s' b) (h2 : Justified Γ N L cval env φ ρ s' b s'' c) :
    Justified Γ N L cval env φ ρ s a s'' c :=
  ⟨h1.skel_left, h2.skel_right, Conv.trans h1.conv h2.conv, h1.sem.trans h2.sem⟩

theorem app {ρ : Nat → V} {sf sf' sa sa' : Tm} {f f' a a' : Kernel.Expr}
    (hf : Justified Γ N L cval env φ ρ sf f sf' f') (ha : Justified Γ N L cval env φ ρ sa a sa' a') :
    Justified Γ N L cval env φ ρ (.app sf sa) (.app f a) (.app sf' sa') (.app f' a') :=
  ⟨skel_app.mpr ⟨hf.skel_left, ha.skel_left⟩, skel_app.mpr ⟨hf.skel_right, ha.skel_right⟩,
    Conv.app hf.conv ha.conv, hf.sem.app ha.sem⟩

theorem proj {ρ : Nat → V} {s : Ix.Name} {s₀ : Kernel.Name} {i : Nat} {se se' : Tm}
    {e e' : Kernel.Expr} {X : V} (hs : N s = some s₀)
    (he : Justified Γ N L cval env φ ρ se e se' e') (hd : Denotes cval env φ ρ (.proj s₀ i e) X) :
    Justified Γ N L cval env φ ρ (.proj s i se) (.proj s₀ i e) (.proj s i se') (.proj s₀ i e') :=
  ⟨skel_proj.mpr ⟨hs, he.skel_left⟩, skel_proj.mpr ⟨hs, he.skel_right⟩,
    Conv.proj s i he.conv, he.sem.proj hd⟩

/-- The λ congruence: domains justified, bodies justified on the domain (one compiler-side
conversion for every point), equal regimes. -/
theorem lam {ρ : Nat → V} {st st' sb sb' : Tm} {t t' b b' : Kernel.Expr} {m m' : Kernel.BinderMeta}
    {Λ : V} (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ht : Justified Γ N L cval env φ ρ st t st' t')
    (hsb : Skel N L sb b) (hsb' : Skel N L sb' b') (hcb : Conv Γ sb sb')
    (hb : ∀ A, Denotes cval env φ ρ t A → ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) b b')
    (hm : Kernel.regime φ m.pw = Kernel.regime φ m'.pw) :
    Justified Γ N L cval env φ ρ (.lam st sb) (.lam t b m) (.lam st' sb') (.lam t' b' m') :=
  ⟨skel_lam.mpr ⟨ht.skel_left, hsb⟩, skel_lam.mpr ⟨ht.skel_right, hsb'⟩,
    Conv.lam ht.conv hcb, SemEq.lam hl ht.sem hb hm⟩

/-- The ∀ congruence. -/
theorem pi {ρ : Nat → V} {st st' sb sb' : Tm} {t t' b b' : Kernel.Expr} {m m' : Kernel.BinderMeta}
    {P : V} (hl : Denotes cval env φ ρ (.forallE t b m) P) (ht : Justified Γ N L cval env φ ρ st t st' t')
    (hsb : Skel N L sb b) (hsb' : Skel N L sb' b') (hcb : Conv Γ sb sb')
    (hb : ∀ A, Denotes cval env φ ρ t A → ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) b b')
    (hm : Kernel.regime φ m.pw = Kernel.regime φ m'.pw) :
    Justified Γ N L cval env φ ρ (.pi st sb) (.forallE t b m) (.pi st' sb') (.forallE t' b' m') :=
  ⟨skel_pi.mpr ⟨ht.skel_left, hsb⟩, skel_pi.mpr ⟨ht.skel_right, hsb'⟩,
    Conv.pi ht.conv hcb, SemEq.pi hl ht.sem hb hm⟩

/-- **β**, with the domain premise. -/
theorem beta {ρ : Nat → V} {st sb sa : Tm} {t b a : Kernel.Expr} {m : Kernel.BinderMeta} {Λ X : V}
    (hs : Skel N L (.app (.lam st sb) sa) (.app (.lam t b m) a))
    (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ha : Denotes cval env φ ρ a X)
    (hdom : ∀ A, Denotes cval env φ ρ t A → X ∈ˢ A) :
    Justified Γ N L cval env φ ρ (.app (.lam st sb) sa) (.app (.lam t b m) a)
      (Tm.inst sa 0 sb) (b.instantiate1Lift a 0) := by
  obtain ⟨hl', ha'⟩ := skel_app.mp hs
  obtain ⟨_, hb'⟩ := skel_lam.mp hl'
  exact ⟨hs, Skel.inst ha' hb' 0, Conv.step (.beta st sb sa), semEq_beta hl ha hdom⟩

/-- **β in the graph regime**: the domain premise from the application's typing. -/
theorem beta_graph {ρ : Nat → V} {st sb sa : Tm} {t b a : Kernel.Expr} {m : Kernel.BinderMeta}
    {Λ X A' : V} {B : V → V} {v : Nat}
    (hs : Skel N L (.app (.lam st sb) sa) (.app (.lam t b m) a))
    (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ha : Denotes cval env φ ρ a X)
    (hpos : Kernel.regime φ m.pw ≠ 0) (hv : v ≠ 0) (hmem : Λ ∈ˢ piR v A' B) (hX : X ∈ˢ A') :
    Justified Γ N L cval env φ ρ (.app (.lam st sb) sa) (.app (.lam t b m) a)
      (Tm.inst sa 0 sb) (b.instantiate1Lift a 0) := by
  obtain ⟨hl', ha'⟩ := skel_app.mp hs
  obtain ⟨_, hb'⟩ := skel_lam.mp hl'
  exact ⟨hs, Skel.inst ha' hb' 0, Conv.step (.beta st sb sa),
    semEq_beta_graph hl ha hpos hv hmem hX⟩

/-- **η**, with the membership premise (the compiler side's η-redex is `λ t. g↑ #0`). -/
theorem eta {ρ : Nat → V} {st sg : Tm} {t f : Kernel.Expr} {m : Kernel.BinderMeta} {A F : V}
    {B : V → V} (hst : Skel N L st t) (hsg : Skel N L sg f)
    (ht : Denotes cval env φ ρ t A) (hf : Denotes cval env φ ρ f F)
    (hmem : F ∈ˢ piR (Kernel.regime φ m.pw) A B) :
    Justified Γ N L cval env φ ρ (.lam st (.app (Tm.lift 1 0 sg) (.bvar 0)))
      (.lam t (.app (Kernel.Expr.liftLooseBVars 1 0 f) (.bvar 0)) m) sg f := by
  refine ⟨skel_lam.mpr ⟨hst, skel_app.mpr ⟨hsg.lift 1 0, skel_bvar⟩⟩, hsg, ?_, semEq_eta ht hf hmem⟩
  have hocc : Tm.occ (Tm.lift 1 0 sg) 0 = false := Tm.occ_lift_mid 1 0 0 sg (Nat.le_refl _) (by omega)
  have hstep := Conv.step (Γ := Γ) (Step.eta st (Tm.lift 1 0 sg) hocc)
  rwa [Conv.lower_lift_succ, Tm.lift_zero] at hstep

/-- **δ** of an installed definition: the compiler side's rule `c.{us} ⟶ val[lps := us]` (any rule
of `Γ`), the checker side's installed value at the occurrence's levels, given the skeleton of the
instantiated value (per compile: `Emitted` and the level instantiation; once: L4). -/
theorem delta (strong : StrongInstalledModel V env) {ρ : Nat → V} {sc sr : Tm} {c : Kernel.Name}
    {us : List Kernel.Level} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (hax : Γ.ax sc sr) (hsc : Skel N L sc (.const c us))
    (lookup : env.find? c = some (.defnInfo header value hint))
    (arity : us.length = header.levelParams.length)
    (hsr : Skel N L sr (value.instantiateLevelParams header.levelParams us)) :
    Justified Γ N L strong.public.cval env φ ρ sc (.const c us) sr
      (value.instantiateLevelParams header.levelParams us) :=
  ⟨hsc, hsr, Conv.step (.ax hax), semEq_delta strong lookup arity⟩

/-- Any rule of `Γ` whose semantics is supplied. -/
theorem ax {ρ : Nat → V} {sl sr : Tm} {l r : Kernel.Expr} (hax : Γ.ax sl sr)
    (hsl : Skel N L sl l) (hsr : Skel N L sr r) (hsem : SemEq cval env φ ρ l r) :
    Justified Γ N L cval env φ ρ sl l sr r :=
  ⟨hsl, hsr, Conv.step (.ax hax), hsem⟩

end Justified

/-- **Conversion soundness**, the two halves of a justified conversion: the compiler-side terms
are `Conv`-related and the checker-side annotations of their bridges denote the same set. -/
theorem justified_sound {ρ : Nat → V} {s s' : Tm} {a b : Kernel.Expr}
    (h : Justified Γ N L cval env φ ρ s a s' b) :
    Conv Γ s s' ∧ ∃ v, Denotes cval env φ ρ a v ∧ Denotes cval env φ ρ b v :=
  ⟨h.conv, h.sem⟩

end Justified

end Ix.CompileCert.Bridge
