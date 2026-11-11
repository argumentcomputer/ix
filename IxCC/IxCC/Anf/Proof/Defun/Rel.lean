import IxCC.Anf.Defun
import IxCC.Anf.Census
import IxCC.Anf.Proof.Lang

/-! # P8's simulation: the relations

The definitions P8's correctness proof is stated with
(`docs/closures-design.md`, "Proof obligation", says what it proves):

* `Setting`: the source program, P8's output, the closure sources and the
  largest dispatcher arity;
* `Tr`: the translation, relationally, at a value depth: `fn` becomes the
  closure cell of a lifted global whose body is the translated body renamed
  onto its captures, `glob` of a function global its field-less cell, `app`
  a call of a dispatcher, everything else unchanged;
* `DV`: the value relation. It is **structural, with no step index**, as the
  implemented Anf relation is (`Anf.Rel.Structural`): literals and □ relate
  to themselves, constructors pointwise; a closure of a local function, made
  in an environment related pointwise to a target environment, relates to
  the cell of its lifted global, whose fields are the captures' values in
  that target environment followed by the arguments supplied so far (the
  cell keeps only the captures; the relation keeps the whole target
  environment, so that the lifted body, renamed back, runs over an
  environment related pointwise to the source's, by `eval_rename` and
  `capRen_env`); a function global's closure relates to the cell of the
  global's key with those arguments. An ordinary mutual inductive with `DVs`;
* `JRel`: join closures with translated bodies over related environments of
  at least the depth they were made at;
* `FundAt`: the fundamental lemma's statement at a clock bound: an expression
  at value depth `Γ` and its image, in environments related pointwise and of
  at least that depth (every binder pushes exactly its values, so the bound
  holds wherever code runs, and a local function's captures, below `Γ`, are
  in the target environment);
* `ExactArity`, `RefinesOn`: the inputs P8 refines on. A root applied to
  more arguments than it takes applies its result to the rest; when the
  result is a closure the source continues and the target, which holds a
  closure cell, is stuck (`IxCCTests.Anf.Defun`, the over-applied root). A
  root is called with exactly its declared number of parameters
  (`docs/closures-design.md`, "Proof obligation", the decisions of
  2026-11-13 and 2026-11-14), so the step is stated for inputs of exactly
  the Anf root's arity, which the end-to-end theorems get from the source
  root's declared count. The input premise is the predicate `RefinesOn`
  takes and nothing else; `refinesOn_mono` restricts it.

Proved here: on first-order values (no closure inside) `DV` is the identity
(`dv_refl`, `dv_eq`), and related values observe the same (`dv_obs`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Result SimUpTo)

/-- What P8's output fixes for the proof. -/
structure Setting where
  /-- The source program. -/
  P : Program
  /-- P8's output. -/
  Q : Program
  /-- The closure sources (`Defun.sources`). -/
  srcs : List Source
  /-- The dispatchers are those of arities `1 … M`. -/
  M : Nat

/-- The dispatcher of arity `m`. -/
def Setting.dispId (X : Setting) (m : Nat) : GlobalId := Defun.dispId X.P.size m

/-- The captures of a local function at value depth `Γ` with `n` parameters
and translated body `b'`. -/
def capsOf (Γ n : Nat) (b' : Exp) : List Nat := captures Γ (b'.free n)

mutual

/-- `Tr X Γ e e'`: `e'` is P8's image of `e`, at value depth `Γ`. -/
inductive Tr (X : Setting) : Nat → Exp → Exp → Prop
  | bind {Γ : Nat} {c : Ixon.V3.LetContract} {b b' : Bind} {e e' : Exp} :
      TrB X Γ b b' → Tr X (Γ + 1) e e' → Tr X Γ (.bind c b e) (.bind c b' e')
  | join {Γ n : Nat} {r : Bool} {b b' e e' : Exp} :
      Tr X (Γ + n) b b' → Tr X Γ e e' → Tr X Γ (.join n r b e) (.join n r b' e')
  | jump {Γ j : Nat} {as : List Atom} : Tr X Γ (.jump j as) (.jump j as)
  | case {Γ : Nat} {x : Atom} {alts alts' : List Alt} {d d' : Option Exp} :
      TrAlts X Γ alts alts' → TrOpt X Γ d d' → Tr X Γ (.case x alts d) (.case x alts' d')
  | ret {Γ : Nat} {a : Atom} : Tr X Γ (.ret a) (.ret a)
  | tick {Γ : Nat} {e e' : Exp} : Tr X Γ e e' → Tr X Γ (.tick e) (.tick e')
  | trap {Γ : Nat} : Tr X Γ .trap .trap

/-- A right-hand side's image. -/
inductive TrB (X : Setting) : Nat → Bind → Bind → Prop
  | atom {Γ : Nat} {a : Atom} : TrB X Γ (.atom a) (.atom a)
  | con {Γ : Nat} {c : Key.CtorKey} {as : List Atom} : TrB X Γ (.con c as) (.con c as)
  | proj {Γ : Nat} {c : Key.CtorKey} {i : Nat} {x : Atom} : TrB X Γ (.proj c i x) (.proj c i x)
  | prim {Γ : Nat} {p : Lam.Prim} {as : List Atom} : TrB X Γ (.prim p as) (.prim p as)
  | call {Γ : Nat} {g : GlobalId} {as : List Atom} : TrB X Γ (.call g as) (.call g as)
  /-- A CAF's value: unchanged. -/
  | caf {Γ h : Nat} {hd : GDef} : h < X.P.size → X.P.global? h = some hd → hd.ps = [] →
      TrB X Γ (.glob h) (.glob h)
  /-- An absent global below the size: unchanged (stuck on both sides). -/
  | absent {Γ h : Nat} : h < X.P.size → X.P.global? h = none → TrB X Γ (.glob h) (.glob h)
  /-- A function global's value: its field-less closure cell. -/
  | glob {Γ h : Nat} {hd : GDef} : h < X.P.size → X.P.global? h = some hd → hd.ps ≠ [] →
      ({ key := hd.key, id := h, caps := 0, arity := hd.ps.length } : Source) ∈ X.srcs →
      TrB X Γ (.glob h) (.con (.clo hd.key 0) [])
  /-- Applying to no arguments returns the function. -/
  | app0 {Γ : Nat} {f : Atom} : TrB X Γ (.app f []) (.atom f)
  /-- An unknown call: a call of the dispatcher of its arity. -/
  | app {Γ : Nat} {f : Atom} {as : List Atom} : as ≠ [] → as.length ≤ X.M →
      TrB X Γ (.app f as) (.call (X.dispId as.length) (f :: as))
  /-- A local function: the cell of its lifted global, holding its captures. -/
  | fn {Γ : Nat} {ps : List Ixon.V3.BinderContract} {b b' : Exp} {s : Source} {gd : GDef} :
      ps ≠ [] → Tr X (Γ + ps.length) b b' → (∀ x ∈ b'.free ps.length, x < Γ) →
      s ∈ X.srcs → s.caps = (capsOf Γ ps.length b').length → s.arity = ps.length →
      X.Q.global? s.id = some gd → gd.ps.length = s.caps + ps.length →
      gd.body = Exp.renameVars (capRen (capsOf Γ ps.length b') ps.length) 0 b' →
      TrB X Γ (.fn ps b) (.con (.clo s.key 0) ((capsOf Γ ps.length b').map .var))

inductive TrAlts (X : Setting) : Nat → List Alt → List Alt → Prop
  | nil {Γ : Nat} : TrAlts X Γ [] []
  | cons {Γ n : Nat} {k : Key.CtorKey} {b b' : Exp} {as as' : List Alt} :
      Tr X (Γ + n) b b' → TrAlts X Γ as as' → TrAlts X Γ (.mk k n b :: as) (.mk k n b' :: as')

inductive TrOpt (X : Setting) : Nat → Option Exp → Option Exp → Prop
  | none {Γ : Nat} : TrOpt X Γ none none
  | some {Γ : Nat} {e e' : Exp} : Tr X Γ e e' → TrOpt X Γ (some e) (some e')

end

mutual

/-- Source and target values (see the module note). -/
inductive DV (X : Setting) : Val → Val → Prop
  | lit {l : Lam.Lit} : DV X (.lit l) (.lit l)
  | box : DV X .box .box
  | con {c : Key.CtorKey} {vs ws : List Val} : DVs X vs ws → DV X (.con c vs) (.con c ws)
  /-- A local function's closure, made at value depth `Γ` in an environment
  `ρ` related to the target's `ρ'`, with `got` supplied: the cell of its
  lifted global holds the captures' values in `ρ'`, then the arguments. -/
  | lam {ρ ρ' : List Val} {n Γ : Nat} {b b' : Exp} {got got' : List Val} {s : Source} {gd : GDef} :
      s ∈ X.srcs → s.arity = n → got.length < n → Tr X (Γ + n) b b' → (∀ x ∈ b'.free n, x < Γ) →
      s.caps = (capsOf Γ n b').length → X.Q.global? s.id = some gd → gd.ps.length = s.caps + n →
      gd.body = Exp.renameVars (capRen (capsOf Γ n b') n) 0 b' → Γ ≤ ρ.length →
      DVs X ρ ρ' → DVs X got got' →
      DV X (.clos ρ n b got)
        (.con (.clo s.key got.length) ((capsOf Γ n b').map (fun x => ρ'.getD x .box) ++ got'))
  /-- A function global's closure, with `got` supplied. -/
  | glob {h n : Nat} {hd gd : GDef} {got ws : List Val} :
      X.P.global? h = some hd → hd.ps.length = n →
      ({ key := hd.key, id := h, caps := 0, arity := n } : Source) ∈ X.srcs →
      got.length < n → X.Q.global? h = some gd → gd.ps.length = n → Tr X n hd.body gd.body →
      DVs X got ws → DV X (.clos [] n hd.body got) (.con (.clo hd.key got.length) ws)

inductive DVs (X : Setting) : List Val → List Val → Prop
  | nil : DVs X [] []
  | cons {v w : Val} {vs ws : List Val} : DV X v w → DVs X vs ws → DVs X (v :: vs) (w :: ws)

end

/-- Join closures with translated bodies over related environments of at
least the depth they were made at. -/
inductive JRel (X : Setting) : List JClo → List JClo → Prop
  | nil : JRel X [] []
  | cons {ρ ρ' : List Val} {J0 J0' J J' : List JClo} {Γ n : Nat} {b b' : Exp} {r : Bool} :
      Tr X (Γ + n) b b' → Γ ≤ ρ.length → DVs X ρ ρ' → JRel X J0 J0' → JRel X J J' →
      JRel X (.mk ρ J0 n b r :: J) (.mk ρ' J0' n b' r :: J')

/-- The fundamental lemma of the translation at clock bound `n`: an
expression at value depth `Γ` and its image, in related environments of at
least that depth. -/
def FundAt (X : Setting) (n : Nat) : Prop :=
  ∀ ⦃Γ : Nat⦄ ⦃e e' : Exp⦄ ⦃ρ ρ' : List Val⦄ ⦃J J' : List JClo⦄, Tr X Γ e e' → Γ ≤ ρ.length →
    DVs X ρ ρ' → JRel X J J' →
    SimUpTo (DV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' e')

/-- Inputs that apply a root to exactly as many arguments as it takes. -/
def ExactArity (P : Program) (i : Nat × List Nat) : Prop :=
  ∀ r gd, P.roots[i.1]? = some r → P.global? r = some gd → i.2.length = gd.ps.length

/-- Refinement on the inputs of `D` (`Sem.Refines` on every input). The
inputs are its only premise: nothing below the root-level statement names
them. -/
def RefinesOn {I S T : Type} [Sem.Lang I S] [Sem.Lang I T] (D : I → Prop) (s : S) (t : T) : Prop :=
  ∀ i, D i → Sem.Behaviour.Refines Sem.Lang.ObsEq (Sem.Lang.behaviour s i) (Sem.Lang.behaviour t i)

/-- Refinement on fewer inputs. -/
theorem refinesOn_mono {I S T : Type} [Sem.Lang I S] [Sem.Lang I T] {D E : I → Prop} {s : S} {t : T}
    (hED : ∀ i, E i → D i) (h : RefinesOn D s t) : RefinesOn E s t :=
  fun i hi => h i (hED i hi)

/-! ## First-order values -/

mutual

/-- A value with no closure in it. -/
inductive FOVal : Val → Prop
  | lit {l : Lam.Lit} : FOVal (.lit l)
  | box : FOVal .box
  | con {c : Key.CtorKey} {vs : List Val} : FOVals vs → FOVal (.con c vs)

inductive FOVals : List Val → Prop
  | nil : FOVals []
  | cons {v : Val} {vs : List Val} : FOVal v → FOVals vs → FOVals (v :: vs)

end

variable {X : Setting}

mutual

/-- A first-order value relates to itself. -/
theorem dv_refl : ∀ {v : Val}, FOVal v → DV X v v
  | _, .lit => .lit
  | _, .box => .box
  | _, .con h => .con (dvs_refl h)

theorem dvs_refl : ∀ {vs : List Val}, FOVals vs → DVs X vs vs
  | _, .nil => .nil
  | _, .cons h hs => .cons (dv_refl h) (dvs_refl hs)

end

mutual

/-- A first-order source value relates to itself only: on first-order values
`DV` is equality. -/
theorem dv_eq : ∀ {v w : Val}, DV X v w → FOVal v → w = v
  | _, _, .lit, _ => rfl
  | _, _, .box, _ => rfl
  | _, _, .con h, .con hf => by rw [dvs_eq h hf]
  | _, _, .lam .., hf => nomatch hf
  | _, _, .glob .., hf => nomatch hf

theorem dvs_eq : ∀ {vs ws : List Val}, DVs X vs ws → FOVals vs → ws = vs
  | _, _, .nil, _ => rfl
  | _, _, .cons h hs, .cons hf hfs => by rw [dv_eq h hf, dvs_eq hs hfs]

end

mutual

/-- Related values observe the same: a closure and a closure cell observe
nothing. -/
theorem dv_obs : ∀ {v w : Val}, DV X v w → obsV v = obsV w
  | _, _, .lit => rfl
  | _, _, .box => rfl
  | _, _, .con h => by
    rename_i c _ _
    cases c with
    | src c => simp only [obsV, dvs_obs h]
    | clo f j => rfl
  | _, _, .lam .. => rfl
  | _, _, .glob .. => rfl

theorem dvs_obs : ∀ {vs ws : List Val}, DVs X vs ws → obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [obsList, dv_obs h, dvs_obs hs]

end

end IxCC.Anf.Defun.Proof
