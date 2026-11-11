import IxCCGrounding.Model

/-!
# The relation between SrcEval values and model elements (`IxCCGrounding.Relation`)

**The relation is by provenance** (`RelV`): a literal relates to what the literal denotes; a
constructor value and a partial application to their head's denotation applied to related
arguments that fit the head's stored type (`Fits`); a closure to what its λ denotes in a related
kernel environment satisfying the λ's context, the λ running there; `irr t` to what its kept term
denotes; a by-name slot to what its suspended term denotes, the term running there. It is
inductive on the value and mentions no clock.

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

/-- **What SrcEval runs** (the spike's `Runs`, unchanged): the Src term `t` at levels `ls`
corresponds to the kernel term `e` at `φ` in context `Γ`, every application site SrcEval may
evaluate is `SiteOk`, every skipped position and type denotes, and every constant SrcEval may
unfold is at an instance `Ok` admits. G1 derives it (`RunsOfSites`); it is no longer a
hypothesis of any landed theorem. -/
inductive Runs (M : Model V env) (κ : CId → KKey) (Ok : CId → Levels → Prop) (lps : List Nat)
    (ls : Levels) (φ : LevelParam → Nat) : List KExpr → Term → KExpr → Prop
  | var {Γ : List KExpr} {i : Nat} : i < Γ.length → Runs M κ Ok lps ls φ Γ (.var i) (.bvar i)
  | sort {Γ : List KExpr} {u : IxCC.Ixon.Univ} {l : Level} : UnivCorr lps u l →
      Runs M κ Ok lps ls φ Γ (.sort u) (.sort l)
  | const {Γ : List KExpr} {c : CId} {us : List IxCC.Ixon.Univ} {ls' : List Level} :
      TermCorr κ lps (.const c us) (.const (κ c) ls') → Ok c (us.map (IxCC.Src.evalUniv ls)) →
      DenotesIn M φ Γ (.const (κ c) ls') → Runs M κ Ok lps ls φ Γ (.const c us) (.const (κ c) ls')
  | natLit {Γ : List KExpr} {n : Nat} : DenotesIn M φ Γ (.lit (.natVal n)) →
      Runs M κ Ok lps ls φ Γ (.natLit n) (.lit (.natVal n))
  | app {Γ : List KExpr} {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel} {f' a' : KExpr} :
      Runs M κ Ok lps ls φ Γ f f' →
      (r.irrAt ls = false → Runs M κ Ok lps ls φ Γ a a') →
      (r.irrAt ls = true → TermCorr κ lps a a' ∧ DenotesIn M φ Γ a') →
      SiteOk M φ Γ f' a' → Runs M κ Ok lps ls φ Γ (.app f a m r) (.app f' a')
  | lam {Γ : List KExpr} {b : IxCC.Src.Binder} {d body : Term} {d' body' : KExpr}
      {mb : BinderMeta} :
      TermCorr κ lps d d' → Runs M κ Ok lps ls φ (d' :: Γ) body body' →
      DenotesIn M φ Γ (.lam d' body' mb) →
      Runs M κ Ok lps ls φ Γ (.lam b d body) (.lam d' body' mb)
  | pi {Γ : List KExpr} {b : IxCC.Src.Binder} {r : IxCC.Ixon.V3.ValueContract} {d c : Term}
      {d' c' : KExpr} {mb : BinderMeta} :
      TermCorr κ lps (.pi b r d c) (.forallE d' c' mb) → DenotesIn M φ Γ (.forallE d' c' mb) →
      Runs M κ Ok lps ls φ Γ (.pi b r d c) (.forallE d' c' mb)
  | proj {Γ : List KExpr} {s : CId} {i : Nat} {e : Term} {e' : KExpr} :
      Runs M κ Ok lps ls φ Γ e e' → DenotesIn M φ Γ (.proj (κ s) i e') →
      Runs M κ Ok lps ls φ Γ (.proj s i e) (.proj (κ s) i e')

/-- A special head's denotation (the spike's, unchanged; no recursor or quotient head in the
first fragment). -/
inductive HeadAt (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop) :
    IxCC.Src.Head → Levels → (LevelParam → Nat) → KKey → KExpr → Prop
  | ctor {c : CId} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      S c → LvAt φ (lpsOf c) ls → env.find? (κ c) = some ci →
      HeadAt M κ lpsOf S (.ctor c) ls φ (κ c) ci.toConstantVal.type
  | cases {c : CId} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      S c → LvAt φ (lpsOf c) ls → env.find? (κ c) = some ci →
      HeadAt M κ lpsOf S (.cases c) ls φ (κ c) ci.toConstantVal.type
  | prim {op : IxCC.Src.PrimOp} {ls : Levels} {φ : LevelParam → Nat} {ci : ConstantInfo .anon} :
      env.find? (primKey op) = some ci → ci.toConstantVal.levelParams = [] →
      op.arity ≤ kPis ci.toConstantVal.type →
      HeadAt M κ lpsOf S (.prim op) ls φ (primKey op) ci.toConstantVal.type

mutual

/-- **The value relation**, by provenance (the spike's, unchanged). -/
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
      RelV M κ lpsOf S Ok (.con c ls ps fs) ((Ps ++ Fs).foldl app (M.cval (κ c) φ))
  | clo {b : IxCC.Src.Binder} {dom body : Term} {ρ : IxCC.Src.Env} {ls : Levels}
      {φ : LevelParam → Nat} {lps : List Nat} {Γ : List KExpr} {ρk : BVarIdx → V}
      {A B : KExpr} {m : BinderMeta} {X : V} :
      LvAt φ lps ls → RelEnv M κ lpsOf S Ok ρ ρk → CtxSat M φ Γ ρk →
      Runs M κ Ok lps ls φ Γ (.lam b dom body) (.lam A B m) → ConstsIn S (.lam b dom body) →
      Denotes M.cval env φ ρk (.lam A B m) X → RelV M κ lpsOf S Ok (.clo b dom body ρ ls) X
  | pap {h : IxCC.Src.Head} {ls : Levels} {args : List Slot} {φ : LevelParam → Nat} {k : KKey}
      {T : KExpr} {As : List V} {ρ σ : BVarIdx → V} {R : KExpr} :
      HeadAt M κ lpsOf S h ls φ k T → RelSlots M κ lpsOf S Ok args As →
      Fits M.cval env φ ρ T As σ R →
      RelV M κ lpsOf S Ok (.pap h ls args) (As.foldl app (M.cval k φ))
  | irr {t : Term} {ρ : IxCC.Src.Env} {ls : Levels} {φ : LevelParam → Nat} {lps : List Nat}
      {ρk : BVarIdx → V} {e : KExpr} {X : V} :
      LvAt φ lps ls → RelEnv M κ lpsOf S Ok ρ ρk → TermCorr κ lps t e →
      Denotes M.cval env φ ρk e X → RelV M κ lpsOf S Ok (.irr (some t) ρ ls) X
  | irrNone {ρ : IxCC.Src.Env} {ls : Levels} : RelV M κ lpsOf S Ok (.irr none ρ ls) (pt : V)

inductive RelSlot (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : Slot → V → Prop
  | val {v : Value} {X : V} : RelV M κ lpsOf S Ok v X → RelSlot M κ lpsOf S Ok (.val v) X
  | name {t : Term} {ρ : IxCC.Src.Env} {ls : Levels} {φ : LevelParam → Nat} {lps : List Nat}
      {Γ : List KExpr} {ρk : BVarIdx → V} {e : KExpr} {X : V} :
      LvAt φ lps ls → RelEnv M κ lpsOf S Ok ρ ρk → CtxSat M φ Γ ρk →
      Runs M κ Ok lps ls φ Γ t e → ConstsIn S t → Denotes M.cval env φ ρk e X →
      RelSlot M κ lpsOf S Ok (.name t ρ ls) X

inductive RelEnv (M : Model V env) (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop)
    (Ok : CId → Levels → Prop) : IxCC.Src.Env → (BVarIdx → V) → Prop
  | nil {ρk : BVarIdx → V} : RelEnv M κ lpsOf S Ok [] ρk
  | cons {s : Slot} {ss : IxCC.Src.Env} {ρk : BVarIdx → V} :
      RelSlot M κ lpsOf S Ok s (ρk 0) → RelEnv M κ lpsOf S Ok ss (fun i => ρk (i + 1)) →
      RelEnv M κ lpsOf S Ok (s :: ss) ρk

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
