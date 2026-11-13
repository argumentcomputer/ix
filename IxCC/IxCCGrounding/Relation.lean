import IxCCGrounding.Model

/-!
# The relation between SrcEval values and model elements (`IxCCGrounding.Relation`)

**The relation is by provenance** (`RelV`): a literal relates to what the literal denotes; a
constructor value and a partial application to their head's denotation applied to related
arguments that fit the head's stored type (`Fits`); a closure to what its λ denotes in a kernel
environment satisfying the λ's context, the λ running there, the environments related whenever the
λ's domain has a member (since step C's closure-capture shape: the only reader of a closure's
environment is its application, at a member of the domain); `irr t` to what its kept term
denotes; a by-name slot to what its suspended term denotes, the term running there. It is
inductive on the value and mentions no clock.

**Environments are related through a substitution** (`RelEnv φ ρ σ ρk`, since step C): the Src
variable `i` stands for the kernel term `σ[i]` (a λ-bound one for its kernel variable, a `let`-bound
one for its value's copy in the stored ζ-reduct: no `Denotes` rule reads a `let`), and its slot is
related to that term's denotation in `ρk`; a dead `let`'s variable stands for nothing, and its slot
is related to nothing.

**Typing is consumed in one form only** (`SiteOk`): at an application site SrcEval evaluates, the
function denotes a member of a graph-regime product whose domain holds the argument. `Runs`
records it at every such site of a term SrcEval runs, at the levels it runs it; the per-constant
`Runs` facts are derived in `IxCCGrounding.Runs` from the checks and `SitesOk`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- A kernel environment `ρ` satisfies a context `Γ` (innermost first). -/
inductive CtxSat (M : Model V env) (φ : LevelParam → Nat) : List KExpr → (BVarIdx → V) → Prop
  | nil {ρ : BVarIdx → V} : CtxSat M φ [] ρ
  | cons {A : KExpr} {Γ : List KExpr} {ρ : BVarIdx → V} {X : V} :
      CtxSat M φ Γ (fun i => ρ (i + 1)) → Denotes M.cval env φ (fun i => ρ (i + 1)) A X →
      ρ 0 ∈ˢ X → CtxSat M φ (A :: Γ) ρ

/-- `e` denotes in every environment satisfying `Γ`. -/
def DenotesIn (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (e : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∃ X, Denotes M.cval env φ ρ e X

/-- **An application site in the graph regime**: in every environment satisfying `Γ`, the
function denotes a member of a graph-regime product whose domain holds the argument's
denotation. The one form in which typing is consumed. -/
def SiteOk (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (f a : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∃ (F Xa : V) (v : Nat) (A : V) (B : V → V),
    Denotes M.cval env φ ρ f F ∧ Denotes M.cval env φ ρ a Xa ∧ v ≠ 0 ∧ F ∈ˢ piR v A B ∧ Xa ∈ˢ A

/-- **What SrcEval runs**: the Src term `t` at levels `ls` corresponds to the kernel term `e` at `φ`
in context `Γ`, through the substitution `σ` (a Src variable stands for the kernel term `σ` gives it:
a λ-bound one for its kernel variable, a `let`-bound one for its value's copy in the stored ζ-reduct;
a dead `let`'s for nothing); every application site SrcEval may evaluate is `SiteOk`, every skipped
position and type denotes, every constant SrcEval may unfold is at an instance `Ok` admits, and
every relevant `let`'s value runs against its copy. G1 derives it (`runs_of_corr`); it is no longer
a hypothesis of any landed theorem. -/
inductive Runs (M : Model V env) (κ : CId → KKey) (Ok : CId → Levels → Prop) (lps : List Nat)
    (ls : Levels) (φ : LevelParam → Nat) : Sig → List KExpr → Term → KExpr → Prop
  | var {σ : Sig} {Γ : List KExpr} {i : Nat} {e : KExpr} :
      σ[i]? = some (some e) → Runs M κ Ok lps ls φ σ Γ (.var i) e
  | sort {σ : Sig} {Γ : List KExpr} {u : IxCC.Ixon.Univ} {l : Level} : UnivCorr lps u l →
      Runs M κ Ok lps ls φ σ Γ (.sort u) (.sort l)
  | const {σ : Sig} {Γ : List KExpr} {c : CId} {us : List IxCC.Ixon.Univ} {ls' : List Level} :
      TermCorr κ lps (.const c us) (.const (κ c) ls') → Ok c (us.map (IxCC.Src.evalUniv ls)) →
      DenotesIn M φ Γ (.const (κ c) ls') → Runs M κ Ok lps ls φ σ Γ (.const c us) (.const (κ c) ls')
  | natLit {σ : Sig} {Γ : List KExpr} {n : Nat} : DenotesIn M φ Γ (.lit (.natVal n)) →
      Runs M κ Ok lps ls φ σ Γ (.natLit n) (.lit (.natVal n))
  | app {σ : Sig} {Γ : List KExpr} {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel}
      {f' a' : KExpr} :
      Runs M κ Ok lps ls φ σ Γ f f' →
      (r.irrAt ls = false → Runs M κ Ok lps ls φ σ Γ a a') →
      (r.irrAt ls = true → TermCorrS κ lps σ a a' ∧ DenotesIn M φ Γ a') →
      SiteOk M φ Γ f' a' → Runs M κ Ok lps ls φ σ Γ (.app f a m r) (.app f' a')
  | lam {σ : Sig} {Γ : List KExpr} {b : IxCC.Src.Binder} {d body : Term} {d' body' : KExpr}
      {mb : BinderMeta} :
      TermCorrS κ lps σ d d' → Runs M κ Ok lps ls φ (liftσ σ) (d' :: Γ) body body' →
      DenotesIn M φ Γ (.lam d' body' mb) →
      Runs M κ Ok lps ls φ σ Γ (.lam b d body) (.lam d' body' mb)
  | pi {σ : Sig} {Γ : List KExpr} {b : IxCC.Src.Binder} {r : IxCC.Ixon.V3.ValueContract}
      {d c : Term} {d' c' : KExpr} {mb : BinderMeta} :
      TermCorrS κ lps σ (.pi b r d c) (.forallE d' c' mb) → DenotesIn M φ Γ (.forallE d' c' mb) →
      Runs M κ Ok lps ls φ σ Γ (.pi b r d c) (.forallE d' c' mb)
  | proj {σ : Sig} {Γ : List KExpr} {s : CId} {i : Nat} {e : Term} {e' : KExpr} :
      Runs M κ Ok lps ls φ σ Γ e e' → DenotesIn M φ Γ (.proj (κ s) i e') →
      Runs M κ Ok lps ls φ σ Γ (.proj s i e) (.proj (κ s) i e')
  /-- a `let` relevant at `ls`: its value runs against its copy, the body with the variable
  standing for the copy -/
  | letRel {σ : Sig} {Γ : List KExpr} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v b : Term} {e v' : KExpr} :
      r.irrAt ls = false → zcopy b e = some v' → Runs M κ Ok lps ls φ σ Γ v v' →
      Runs M κ Ok lps ls φ (some v' :: σ) Γ b e → Runs M κ Ok lps ls φ σ Γ (.letE c r ty v b) e
  /-- a `let` irrelevant at `ls` (SrcEval binds `irr`): its value corresponds to its copy, which
  denotes -/
  | letIrr {σ : Sig} {Γ : List KExpr} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v b : Term} {e v' : KExpr} :
      r.irrAt ls = true → zcopy b e = some v' → TermCorrS κ lps σ v v' → DenotesIn M φ Γ v' →
      Runs M κ Ok lps ls φ (some v' :: σ) Γ b e → Runs M κ Ok lps ls φ σ Γ (.letE c r ty v b) e
  /-- a dead `let`: nothing is asked of its value, its slot stands for nothing -/
  | letDead {σ : Sig} {Γ : List KExpr} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v b : Term} {e : KExpr} :
      zcopy b e = none → Runs M κ Ok lps ls φ (none :: σ) Γ b e →
      Runs M κ Ok lps ls φ σ Γ (.letE c r ty v b) e
  /-- a `let` whose body is a λ and whose copy `v'` (in the `let`'s context) occurs, lifted, in the
  λ's body with no binder between (the closure-capture shape, step C): where relevant at `ls`, its
  value runs in the λ's context against the lifted copy (the copy need not denote in the `let`'s
  context: the λ's domain may be empty); where irrelevant, it corresponds there to the lifted copy;
  the λ runs with the variable standing for the copy -/
  | letClo {σ : Sig} {Γ : List KExpr} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v : Term} {bz : IxCC.Src.Binder} {d body : Term} {A b' v' : KExpr} {mb : BinderMeta} :
      SubAt0 (v'.liftLooseBVars 1 0) b' →
      (r.irrAt ls = false →
        Runs M κ Ok lps ls φ (σ.map (·.map (Expr.liftLooseBVars 1 0))) (A :: Γ) v
          (v'.liftLooseBVars 1 0)) →
      (r.irrAt ls = true →
        TermCorrS κ lps (σ.map (·.map (Expr.liftLooseBVars 1 0))) v (v'.liftLooseBVars 1 0)) →
      Runs M κ Ok lps ls φ (some v' :: σ) Γ (.lam bz d body) (.lam A b' mb) →
      Runs M κ Ok lps ls φ σ Γ (.letE c r ty v (.lam bz d body)) (.lam A b' mb)

/-- A special head's denotation (the spike's, with recursor heads since G3; no quotient head in
the first fragment): the key's set at the assignment, its stored type the telescope a partial
application's arguments fit. -/
inductive HeadAt (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) :
    IxCC.Src.Head → Levels → (LevelParam → Nat) → KKey → KExpr → Prop
  | ctor {c : CId} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      S c → LvAt φ (lpsOf c) ls → env.find? (κ c) = some ci → Ok c ls →
      HeadAt M κ lpsOf S Ok (.ctor c) ls φ (κ c) ci.toConstantVal.type
  | cases {c : CId} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      S c → LvAt φ (lpsOf c) ls → env.find? (κ c) = some ci → Ok c ls →
      HeadAt M κ lpsOf S Ok (.cases c) ls φ (κ c) ci.toConstantVal.type
  | recr {r : CId} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      S r → LvAt φ (lpsOf r) ls → env.find? (κ r) = some ci →
      HeadAt M κ lpsOf S Ok (.recr r) ls φ (κ r) ci.toConstantVal.type
  | prim {op : IxCC.Src.PrimOp} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      env.find? (primKey op) = some ci → ci.toConstantVal.levelParams = [] →
      op.arity ≤ kPis ci.toConstantVal.type →
      HeadAt M κ lpsOf S Ok (.prim op) ls φ (primKey op) ci.toConstantVal.type


mutual

/-- **The value relation**, by provenance (the spike's; since step C a closure's and an `irr`
value's environment is related through a substitution `σ`). -/
inductive RelV (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : Value → V → Prop
  | lit {n : Nat} {X : V} {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
      Denotes M.cval env φ ρ (litE n) X → RelV M κ lpsOf S Ok (.lit n) X
  | con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} {φ : LevelParam → Nat}
      {cvC : ConstantVal .anon} {np nf : Nat} {Ps Fs : List V} {ρ σ : BVarIdx → V} {R : KExpr} :
      S c → LvAt φ (lpsOf c) ls → env.find? (κ c) = some (.ctorInfo cvC np nf) →
      Ps.length = np → Fs.length = nf →
      RelSlots M κ lpsOf S Ok ps Ps → RelVs M κ lpsOf S Ok fs Fs →
      Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R →
      (lpsOf c = [] ∨ Ok c ls) →
      RelV M κ lpsOf S Ok (.con c ls ps fs) ((Ps ++ Fs).foldl app (M.cval (κ c) φ))
  | clo {b : IxCC.Src.Binder} {dom body : Term} {ρ : IxCC.Src.Env} {ls : Levels}
      {φ : LevelParam → Nat} {lps : List Nat} {Γ : List KExpr} {σ : Sig} {ρk : BVarIdx → V}
      {A B : KExpr} {m : BinderMeta} {X : V} :
      LvAt φ lps ls →
      (∀ (XA x : V), Denotes M.cval env φ ρk A XA → x ∈ˢ XA → RelEnv M κ lpsOf S Ok φ ρ σ ρk) →
      CtxSat M φ Γ ρk →
      Runs M κ Ok lps ls φ σ Γ (.lam b dom body) (.lam A B m) → ConstsIn S (.lam b dom body) →
      Denotes M.cval env φ ρk (.lam A B m) X → RelV M κ lpsOf S Ok (.clo b dom body ρ ls) X
  | pap {h : IxCC.Src.Head} {ls : Levels} {args : List Slot} {φ : LevelParam → Nat} {k : KKey}
      {T : KExpr} {As : List V} {ρ σ : BVarIdx → V} {R : KExpr} :
      HeadAt M κ lpsOf S Ok h ls φ k T → RelSlots M κ lpsOf S Ok args As →
      Fits M.cval env φ ρ T As σ R →
      RelV M κ lpsOf S Ok (.pap h ls args) (As.foldl app (M.cval k φ))
  | irr {t : Term} {ρ : IxCC.Src.Env} {ls : Levels} {φ : LevelParam → Nat} {lps : List Nat}
      {σ : Sig} {ρk : BVarIdx → V} {e : KExpr} {X : V} :
      LvAt φ lps ls → RelEnv M κ lpsOf S Ok φ ρ σ ρk → TermCorrS κ lps σ t e →
      Denotes M.cval env φ ρk e X → RelV M κ lpsOf S Ok (.irr (some t) ρ ls) X
  | irrNone {ρ : IxCC.Src.Env} {ls : Levels} : RelV M κ lpsOf S Ok (.irr none ρ ls) (pt : V)

inductive RelSlot (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : Slot → V → Prop
  | val {v : Value} {X : V} : RelV M κ lpsOf S Ok v X → RelSlot M κ lpsOf S Ok (.val v) X
  | name {t : Term} {ρ : IxCC.Src.Env} {ls : Levels} {φ : LevelParam → Nat} {lps : List Nat}
      {Γ : List KExpr} {σ : Sig} {ρk : BVarIdx → V} {e : KExpr} {X : V} :
      LvAt φ lps ls → RelEnv M κ lpsOf S Ok φ ρ σ ρk → CtxSat M φ Γ ρk →
      Runs M κ Ok lps ls φ σ Γ t e → ConstsIn S t → Denotes M.cval env φ ρk e X →
      RelSlot M κ lpsOf S Ok (.name t ρ ls) X

/-- **The environment relation under a substitution**: a slot whose variable stands for a kernel
term is related to that term's denotation at `φ` in `ρk`; a slot whose variable stands for nothing
(a dead `let`'s) is related to nothing. With `σ = idσ n` it is slot `i` related to `ρk i`. -/
inductive RelEnv (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : (LevelParam → Nat) → IxCC.Src.Env → Sig → (BVarIdx → V) → Prop
  | nil {φ : LevelParam → Nat} {ρk : BVarIdx → V} : RelEnv M κ lpsOf S Ok φ [] [] ρk
  | some {φ : LevelParam → Nat} {s : Slot} {ss : IxCC.Src.Env} {e : KExpr} {σ : Sig}
      {ρk : BVarIdx → V} {X : V} :
      RelSlot M κ lpsOf S Ok s X → Denotes M.cval env φ ρk e X → RelEnv M κ lpsOf S Ok φ ss σ ρk →
      RelEnv M κ lpsOf S Ok φ (s :: ss) (some e :: σ) ρk
  | none {φ : LevelParam → Nat} {s : Slot} {ss : IxCC.Src.Env} {σ : Sig} {ρk : BVarIdx → V} :
      RelEnv M κ lpsOf S Ok φ ss σ ρk → RelEnv M κ lpsOf S Ok φ (s :: ss) (none :: σ) ρk

inductive RelSlots (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : List Slot → List V → Prop
  | nil : RelSlots M κ lpsOf S Ok [] []
  | cons {s : Slot} {ss : List Slot} {X : V} {Xs : List V} :
      RelSlot M κ lpsOf S Ok s X → RelSlots M κ lpsOf S Ok ss Xs →
      RelSlots M κ lpsOf S Ok (s :: ss) (X :: Xs)

inductive RelVs (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : List Value → List V → Prop
  | nil : RelVs M κ lpsOf S Ok [] []
  | cons {v : Value} {vs : List Value} {X : V} {Xs : List V} :
      RelV M κ lpsOf S Ok v X → RelVs M κ lpsOf S Ok vs Xs →
      RelVs M κ lpsOf S Ok (v :: vs) (X :: Xs)

end

end Sem

end IxCC.Grounding
