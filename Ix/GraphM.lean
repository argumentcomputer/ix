module

public import Ix.Common
public import Ix.Environment
public import Ix.Compile.ExactKey
public import Ix.Compile.Parallel
import Std.Data.HashMap.Lemmas

public section

namespace Ix

/-!
  # GraphM - Build dependency graph from Ix.Environment

  This module builds a reference graph from an already-canonicalized Ix.Environment.
  The canonicalization should be done first (ideally via fast Rust FFI).
-/

/-- The graph walk's visited set: shared expression sub-DAGs already walked in
the current constant, keyed exactly (`Ix.Compile.ExactKey.ExprKey`: complete
structural equality confirms a hit, as in the compiler's caches). A stored hash
is not a content hash on every input, so a key compared by stored hashes alone
could skip another expression's references. -/
structure GraphState where
  exprSeen : Std.HashSet Ix.Compile.ExactKey.ExprKey := {}

def GraphState.init : GraphState := {}

abbrev GraphM := ReaderT Ix.Environment <| StateT GraphState Id

/-- Extract constant references from an `Ix.Expr` into a single accumulator `acc`,
skipping shared sub-DAGs already recorded in `exprSeen`. -/
def graphExprAcc (expr : Ix.Expr) (acc : Set Ix.Name) : GraphM (Set Ix.Name) := do
  if (← get).exprSeen.contains ⟨expr⟩ then
    pure acc
  else
    let refs ← go expr acc
    modifyGet fun stt => (refs, { stt with
      exprSeen := stt.exprSeen.insert ⟨expr⟩
    })
  where
    go : Ix.Expr → Set Ix.Name → GraphM (Set Ix.Name)
    | .mdata _ x _, acc => graphExprAcc x acc
    | .const name _ _, acc => pure (acc.insert name)
    | .app f a _, acc => do
      let acc ← graphExprAcc f acc
      graphExprAcc a acc
    | .lam _ t b _ _, acc => do
      let acc ← graphExprAcc t acc
      graphExprAcc b acc
    | .forallE _ t b _ _, acc => do
      let acc ← graphExprAcc t acc
      graphExprAcc b acc
    | .letE _ t v b _ _, acc => do
      let acc ← graphExprAcc t acc
      let acc ← graphExprAcc v acc
      graphExprAcc b acc
    | .proj typeName _ s _, acc => do
      let acc ← graphExprAcc s acc
      pure (acc.insert typeName)
    | _, acc => pure acc

/-- Extract constant references from an Ix.Expr.
    NOTE: Aligned with Rust's get_expr_references for cross-impl testing. -/
def graphExpr (expr : Ix.Expr) : GraphM (Set Ix.Name) :=
  graphExprAcc expr {}

/-- The recursors of an inductive block, in the family's declared order: `X.rec` for
each member `X` of `all`, then the nested auxiliary recursors `all[0].rec_N`,
`N = 1 … numMotives - all.size`. -/
def recursorFamilyNames (all : Array Ix.Name) (numMotives : Nat) : Array Ix.Name := Id.run do
  let mut out := all.map (Ix.Name.mkStr · "rec")
  if let some head := all[0]? then
    for k in [1:numMotives - all.size + 1] do
      out := out.push (Ix.Name.mkStr head s!"rec_{k}")
  return out

/-- Extract constant references from an Ix.ConstantInfo.
    NOTE: Aligned with Rust's get_constant_info_references for cross-impl testing.

    An inductive refers to the other members of its Lean block (`all`) and a
    recursor to the other recursors of its family (`recursorFamilyNames`): the
    order of a mutual inductive block and of its recursor family is structural,
    so each is compiled as one block, in Lean's order, even when its members are
    not strongly connected through their types. -/
def graphConst: Ix.ConstantInfo -> GraphM (Set Ix.Name)
| .axiomInfo val => graphExpr val.cnst.type
| .defnInfo val => do
  let acc ← graphExprAcc val.cnst.type {}
  graphExprAcc val.value acc
| .thmInfo val => do
  let acc ← graphExprAcc val.cnst.type {}
  graphExprAcc val.value acc
| .opaqueInfo val => do
  let acc ← graphExprAcc val.cnst.type {}
  graphExprAcc val.value acc
| .quotInfo val => graphExpr val.cnst.type
| .inductInfo val => do
  -- Rust: type refs + constructor names (NOT constructor type refs) + block siblings
  let ctorNames : Set Ix.Name := val.ctors.foldl (init := {}) fun s n => s.insert n
  let type <- graphExpr val.cnst.type
  let siblings := val.all.foldl (init := ctorNames) fun s n =>
    if n == val.cnst.name then s else s.insert n
  return .union type siblings
| .ctorInfo val => do
  -- Rust: type refs + induct name
  let typeRefs <- graphExpr val.cnst.type
  return typeRefs.insert val.induct
| .recInfo val => do
  -- Rust: type refs + (ctor names + rhs refs for each rule) + family siblings
  let t <- graphExpr val.cnst.type
  let mut rs := t
  for rule in val.rules do
    rs := rs.insert rule.ctor
    rs <- graphExprAcc rule.rhs rs
  return (recursorFamilyNames val.all val.numMotives).foldl
    (fun s r => if r != val.cnst.name then s.insert r else s) rs

def GraphM.run (env: Ix.Environment) (stt: GraphState) (g: GraphM α)
  : α × GraphState
  := StateT.run (ReaderT.run (Id.run g env)) stt

def GraphM.envSerial (env: Ix.Environment) : Map Ix.Name (Set Ix.Name) := Id.run do
  let mut refs: Map Ix.Name (Set Ix.Name) := {}
  for (name, const) in env.consts do
    let (rs, _) := GraphM.run env .init (graphConst const)
    refs := refs.insert name rs
  return refs

/-! ## The graph does not read the environment

Proof only. The statements' closure relation (`Ix.Cert.refsOf`) runs
`graphConst` under the empty environment, the driver's graph
(`GraphM.envSerial`) under the input; these say the two agree. -/

/-- A graph computation that does not read the environment. -/
private def EnvFree {α : Type} (g : GraphM α) : Prop :=
  ∀ env₁ env₂ : Ix.Environment, g env₁ = g env₂

private theorem EnvFree.pure {α : Type} (a : α) : EnvFree (Pure.pure a : GraphM α) :=
  fun _ _ => rfl

private theorem EnvFree.bind {α β : Type} {g : GraphM α} {f : α → GraphM β} (hg : EnvFree g)
    (hf : ∀ a, EnvFree (f a)) : EnvFree (g >>= f) := by
  intro env₁ env₂
  funext s
  show (g env₁ s >>= fun p => f p.1 env₁ p.2) = (g env₂ s >>= fun p => f p.1 env₂ p.2)
  rw [hg env₁ env₂]
  simp only [hf _ env₁ env₂]

private theorem EnvFree.map {α β : Type} {g : GraphM α} (f : α → β) (hg : EnvFree g) :
    EnvFree (f <$> g) := by
  rw [← bind_pure_comp]
  exact hg.bind fun a => EnvFree.pure (f a)

private theorem EnvFree.seq {α β : Type} {g : GraphM (α → β)} {h : GraphM α} (hg : EnvFree g)
    (hh : EnvFree h) : EnvFree (g <*> h) := by
  rw [seq_eq_bind_map]
  exact hg.bind fun a => hh.map a

private theorem EnvFree.forInList {α σ : Type} (f : α → σ → GraphM (ForInStep σ))
    (hf : ∀ a s, EnvFree (f a s)) : ∀ (l : List α) (init : σ), EnvFree (ForIn.forIn l init f) := by
  intro l
  induction l with
  | nil => intro init; exact EnvFree.pure init
  | cons a l ih =>
    intro init
    rw [List.forIn_cons]
    refine (hf a init).bind fun r => ?_
    cases r with
    | done b => exact EnvFree.pure b
    | yield b => exact ih b

private theorem EnvFree.forInArray {α σ : Type} (f : α → σ → GraphM (ForInStep σ))
    (hf : ∀ a s, EnvFree (f a s)) (xs : Array α) (init : σ) : EnvFree (ForIn.forIn xs init f) := by
  rw [← Array.forIn_toList]
  exact EnvFree.forInList f hf xs.toList init

private theorem graphExprAcc_envFree (e : Ix.Expr) : ∀ acc : Set Ix.Name, EnvFree (graphExprAcc e acc) := by
  induction e with
  | bvar | fvar | mvar | sort | const | lit =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact (EnvFree.pure _).bind fun _ _ _ => rfl
  | app _ _ _ ihf iha =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact ((ihf acc).bind iha).bind fun _ _ _ => rfl
  | lam _ _ _ _ _ iht ihb | forallE _ _ _ _ _ iht ihb =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact ((iht acc).bind ihb).bind fun _ _ _ => rfl
  | letE _ _ _ _ _ _ iht ihv ihb =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact ((iht acc).bind fun acc₁ => (ihv acc₁).bind ihb).bind fun _ _ _ => rfl
  | mdata _ _ _ ih =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact (ih acc).bind fun _ _ _ => rfl
  | proj _ _ _ _ ih =>
    intro acc
    rw [graphExprAcc]
    refine EnvFree.bind (fun _ _ => rfl) fun stt => ?_
    split
    · exact EnvFree.pure _
    · rw [graphExprAcc.go.eq_def]
      exact ((ih acc).bind fun _ => EnvFree.pure _).bind fun _ _ _ => rfl

private theorem graphExpr_envFree (e : Ix.Expr) : EnvFree (graphExpr e) :=
  graphExprAcc_envFree e {}

/-- **`graphExprAcc` does not read the environment it runs in.** -/
theorem graphExprAcc_env (e : Ix.Expr) (acc : Set Ix.Name) (env₁ env₂ : Ix.Environment) (s : GraphState) :
    GraphM.run env₁ s (graphExprAcc e acc) = GraphM.run env₂ s (graphExprAcc e acc) := by
  show (graphExprAcc e acc env₁).run s = (graphExprAcc e acc env₂).run s
  rw [graphExprAcc_envFree e acc env₁ env₂]

/-- **`graphExpr` does not read the environment it runs in.** -/
theorem graphExpr_env (e : Ix.Expr) (env₁ env₂ : Ix.Environment) :
    graphExpr e env₁ = graphExpr e env₂ :=
  graphExpr_envFree e env₁ env₂

/-- **`graphConst` does not read the environment it runs in**: under any two
environments, from one graph state, it returns the same references and state. -/
theorem graphConst_env (ci : Ix.ConstantInfo) (env₁ env₂ : Ix.Environment) (s : GraphState) :
    GraphM.run env₁ s (graphConst ci) = GraphM.run env₂ s (graphConst ci) := by
  have h : EnvFree (graphConst ci) := by
    cases ci with
    | axiomInfo v | quotInfo v => exact graphExpr_envFree _
    | defnInfo v | thmInfo v | opaqueInfo v =>
      exact (graphExprAcc_envFree _ _).bind fun acc => graphExprAcc_envFree _ acc
    | inductInfo v => exact (graphExpr_envFree _).bind fun _ => EnvFree.pure _
    | ctorInfo v => exact (graphExpr_envFree _).bind fun _ => EnvFree.pure _
    | recInfo v =>
      refine (graphExpr_envFree _).bind fun t => ?_
      dsimp only
      refine (EnvFree.forInArray _ (fun rule r => ?_) _ _).bind fun _ => EnvFree.pure _
      exact (graphExprAcc_envFree _ _).bind fun _ => EnvFree.pure _
  show (graphConst ci env₁).run s = (graphConst ci env₂).run s
  rw [h env₁ env₂]

end Ix

end
