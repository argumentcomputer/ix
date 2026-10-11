import Ix.CompileCert.Bridge.Justified

/-!
# M7 X2: the pair projections, relative to the model's pair law

X1's projection rule contracts `(PProd.mk α β a b).1 ↦ a` (and `.2`, and `And.intro`), exactly the
redexes the development forms. In the checker's model a projection reads a field of the pair chain
its structure's projection table describes (`Denotes.proj_table`), and that a constructor
application's field *is* the constructor's argument is the model's tower law (`TowerOk` (B),
`IxC/Kernel/Model/Annot/Laws.lean`), stated on the internal annotated reading with grading and
telescope-fit premises. Its public form is `PairLaw`; this module proves the rule from it
(`semEq_proj0`, `semEq_proj1`, `Justified.proj0`, `Justified.proj1`), and `Tower.lean` proves the
law in every strong model from the exported `EnvModelM.tower_ok` (`pairLaw_of_tower`,
`pairLaw_of_fireOk`).
-/

namespace Ix.CompileCert.Bridge

open Ix.CompileCert.Conv (Tm er Env Step Conv pairName pair4)
open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

universe u

section Pair

variable {V : Type u} [Kernel.SetTheory V]

/-- **The model's pair law** for a structure `s` with constructor `c` (at `φ`): projections `0` and
`1` of a constructor application whose four arguments fit the constructor's installed type
telescope read the third and fourth argument. -/
def PairLaw (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (φ : Kernel.Name → Nat) (s c : Kernel.Name) : Prop :=
  ∀ (ρ : Nat → V) (us : List Kernel.Level) (α β a b : Kernel.Expr) (A B X Y : V)
    (cv : Kernel.ConstantVal) (nP nF : Nat) (finalρ : Nat → V) (result : Kernel.Expr),
    env.find? c = some (.ctorInfo cv nP nF) → us.length = cv.levelParams.length →
    Denotes cval env φ ρ α A → Denotes cval env φ ρ β B →
    Denotes cval env φ ρ a X → Denotes cval env φ ρ b Y →
    InstalledTelescope cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us)
      [A, B, X, Y] finalρ result →
    (∃ v, Denotes cval env φ ρ (.proj s 0 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) v) ∧
    (∀ v, Denotes cval env φ ρ (.proj s 0 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) v →
      v = X) ∧
    (∃ v, Denotes cval env φ ρ (.proj s 1 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) v) ∧
    (∀ v, Denotes cval env φ ρ (.proj s 1 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) v →
      v = Y)

variable {cval : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
  {φ : Kernel.Name → Nat}

/-- **Projection `0` of a pair**, under the pair law, at typed components. -/
theorem semEq_proj0 {s c : Kernel.Name} (law : PairLaw cval env φ s c) {ρ : Nat → V}
    {us : List Kernel.Level} {α β a b : Kernel.Expr} {A B X Y : V}
    (hα : Denotes cval env φ ρ α A) (hβ : Denotes cval env φ ρ β B)
    (ha : Denotes cval env φ ρ a X) (hb : Denotes cval env φ ρ b Y) {cv : Kernel.ConstantVal} {nP nF : Nat} {finalρ : Nat → V}
    {result : Kernel.Expr} (hc : env.find? c = some (.ctorInfo cv nP nF)) (harity : us.length = cv.levelParams.length)
    (typed : InstalledTelescope cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us)
      [A, B, X, Y] finalρ result) :
    SemEq cval env φ ρ (.proj s 0 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) a := by
  obtain ⟨⟨v, hv⟩, h0, -, -⟩ := law ρ us α β a b A B X Y cv nP nF finalρ result hc harity hα hβ ha hb typed
  exact ⟨X, h0 v hv ▸ hv, ha⟩

/-- **Projection `1` of a pair**, under the pair law, at typed components. -/
theorem semEq_proj1 {s c : Kernel.Name} (law : PairLaw cval env φ s c) {ρ : Nat → V}
    {us : List Kernel.Level} {α β a b : Kernel.Expr} {A B X Y : V}
    (hα : Denotes cval env φ ρ α A) (hβ : Denotes cval env φ ρ β B)
    (ha : Denotes cval env φ ρ a X) (hb : Denotes cval env φ ρ b Y) {cv : Kernel.ConstantVal} {nP nF : Nat} {finalρ : Nat → V}
    {result : Kernel.Expr} (hc : env.find? c = some (.ctorInfo cv nP nF)) (harity : us.length = cv.levelParams.length)
    (typed : InstalledTelescope cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us)
      [A, B, X, Y] finalρ result) :
    SemEq cval env φ ρ (.proj s 1 (Kernel.Expr.mkAppN (.const c us) [α, β, a, b])) b := by
  obtain ⟨-, -, ⟨v, hv⟩, h1⟩ := law ρ us α β a b A B X Y cv nP nF finalρ result hc harity hα hβ ha hb typed
  exact ⟨Y, h1 v hv ▸ hv, hb⟩

variable {Γ : Env} {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

/-- The bridge of X1's pair redex `s.i (c α β a b)`. -/
theorem skel_pair {s c : Ix.Name} {i : Nat} {us : Array Ix.Level} {α β a b : Tm}
    {s' c' : Kernel.Name} {ls : List Kernel.Level} {kα kβ ka kb : Kernel.Expr}
    (hs : N s = some s') (hc : N c = some c') (hl : optMap L us.toList = some ls)
    (hα : Skel N L α kα) (hβ : Skel N L β kβ) (ha : Skel N L a ka) (hb : Skel N L b kb) :
    Skel N L (.proj s i (pair4 c us α β a b))
      (.proj s' i (Kernel.Expr.mkAppN (.const c' ls) [kα, kβ, ka, kb])) := by
  refine skel_proj.mpr ⟨hs, ?_⟩
  simp only [pair4, Tm.appN, Kernel.Expr.mkAppN]
  exact skel_app.mpr ⟨skel_app.mpr ⟨skel_app.mpr ⟨skel_app.mpr ⟨skel_const.mpr ⟨hc, hl⟩, hα⟩, hβ⟩,
    ha⟩, hb⟩

/-- **X1's projection rule `.1`, justified**: under the pair law, at typed components. -/
theorem Justified.proj0 {ρ : Nat → V} {s c : Ix.Name} {us : Array Ix.Level} {α β a b : Tm}
    {s' c' : Kernel.Name} {ls : List Kernel.Level} {kα kβ ka kb : Kernel.Expr} {A B X Y : V}
    (hp : pairName s c = true) (hs : N s = some s') (hc : N c = some c')
    (hl : optMap L us.toList = some ls)
    (sα : Skel N L α kα) (sβ : Skel N L β kβ) (sa : Skel N L a ka) (sb : Skel N L b kb)
    (law : PairLaw cval env φ s' c')
    (hα : Denotes cval env φ ρ kα A) (hβ : Denotes cval env φ ρ kβ B)
    (ha : Denotes cval env φ ρ ka X) (hb : Denotes cval env φ ρ kb Y) {cv : Kernel.ConstantVal} {nP nF : Nat} {finalρ : Nat → V}
    {result : Kernel.Expr} (hcc : env.find? c' = some (.ctorInfo cv nP nF)) (harity : ls.length = cv.levelParams.length)
    (typed : InstalledTelescope cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams ls)
      [A, B, X, Y] finalρ result) :
    Justified Γ N L cval env φ ρ (.proj s 0 (pair4 c us α β a b))
      (.proj s' 0 (Kernel.Expr.mkAppN (.const c' ls) [kα, kβ, ka, kb])) a ka :=
  ⟨skel_pair hs hc hl sα sβ sa sb, sa, Conv.step (.proj0 s c us α β a b hp),
    semEq_proj0 law hα hβ ha hb hcc harity typed⟩

/-- **X1's projection rule `.2`, justified**: under the pair law, at typed components. -/
theorem Justified.proj1 {ρ : Nat → V} {s c : Ix.Name} {us : Array Ix.Level} {α β a b : Tm}
    {s' c' : Kernel.Name} {ls : List Kernel.Level} {kα kβ ka kb : Kernel.Expr} {A B X Y : V}
    (hp : pairName s c = true) (hs : N s = some s') (hc : N c = some c')
    (hl : optMap L us.toList = some ls)
    (sα : Skel N L α kα) (sβ : Skel N L β kβ) (sa : Skel N L a ka) (sb : Skel N L b kb)
    (law : PairLaw cval env φ s' c')
    (hα : Denotes cval env φ ρ kα A) (hβ : Denotes cval env φ ρ kβ B)
    (ha : Denotes cval env φ ρ ka X) (hb : Denotes cval env φ ρ kb Y) {cv : Kernel.ConstantVal} {nP nF : Nat} {finalρ : Nat → V}
    {result : Kernel.Expr} (hcc : env.find? c' = some (.ctorInfo cv nP nF)) (harity : ls.length = cv.levelParams.length)
    (typed : InstalledTelescope cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams ls)
      [A, B, X, Y] finalρ result) :
    Justified Γ N L cval env φ ρ (.proj s 1 (pair4 c us α β a b))
      (.proj s' 1 (Kernel.Expr.mkAppN (.const c' ls) [kα, kβ, ka, kb])) b kb :=
  ⟨skel_pair hs hc hl sα sβ sa sb, sb, Conv.step (.proj1 s c us α β a b hp),
    semEq_proj1 law hα hβ ha hb hcc harity typed⟩

end Pair

end Ix.CompileCert.Bridge

/-! ## ι, restated

ι is not a rule of X1's `Conv` (the canonical recursors' rules enter as `Γ.ax` schemata, relative to
`IxBlockLaws`); in the checker's model it is the lane's public recursor law
(`PublicRecursorApplication.denotes`, `Installed.lean`), whose conclusion is a semantic equality.
`semEq_iota` states it as one, so that a `Justified.ax` step for an ι schema has its semantics. -/

namespace Ix.CompileCert.Bridge

universe u'

/-- **ι in the model**: a fired rule of an installed recursor, at public typed inputs, relates the
recursor applied to a constructor application with the rule's instantiated right-hand side. -/
theorem semEq_iota {V : Type u'} [Kernel.SetTheory V] {env : Kernel.Env}
    {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {header : Kernel.ConstantVal} {major params : Nat} {rule : Kernel.RecRule}
    {universes : List Kernel.Level}
    (application : PublicRecursorApplication strong levels header major params rule universes)
    (name : Kernel.Name) (rules : List Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (arity : universes.length = header.levelParams.length) :
    SemEq strong.public.cval env levels application.valuation
      (Kernel.Expr.mkAppN (.const name universes)
        (application.argumentExpressions.map (Kernel.Expr.closeN application.depth) ++
          [Kernel.Expr.mkAppN (.const rule.ctor application.constructorUniverses)
            (application.fieldExpressions.map (Kernel.Expr.closeN application.depth))]))
      (Kernel.Expr.mkAppN (rule.rhs.instantiateLevelParams header.levelParams universes)
        ((application.argumentExpressions.map (Kernel.Expr.closeN application.depth)).take params ++
          (application.fieldExpressions.map (Kernel.Expr.closeN application.depth)).drop
            rule.ctorParams)) :=
  application.denotes name rules lookup present fires arity

end Ix.CompileCert.Bridge
