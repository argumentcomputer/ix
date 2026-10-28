import Ix.CompileCert.RawRun
import Ix.CompileCert.CacheSound
import Ix.CompileCert.CanonUnivScope
import Ix.LeanIngress.Expr
import Std.Data.HashMap.Lemmas

/-! # The raw universe compiler computes the exact positional lowering

`Ix.CompileM.compileUniv` compiles a source level under the constant's
universe-parameter context `univCtx`, through the block memo `univCache`.
The memo is keyed by `Ix.Compile.ExactKey.UnivKey`, the exact
source level together with its complete parameter context, so a hit is
confirmed structurally; a parameter compiles to its first structural
position in the context (`nameIndex`), refused when it does not fit the
wire's `UInt64` (`checkedTableIndex`).

* **The specification** is `lower params source`, the exact positional
  lowering: first-occurrence parameter lookup and the wire guard, defined
  independently of the compiler and of its success.
* **One invariant**: every memo entry is the exact lowering of its key
  (`UnivCacheExact`, the generic `CacheSound`, R07-13). The empty memo has
  it, and every run keeps it, failing runs included.
* **The compiler computes the specification** from every such state
  (`compileUniv_exact`, `compileUniv_value`): a warm hit and a fresh compile
  give the same universe (`compileUniv_same`). This merges the donor's
  `UniverseMeaning` and `UniverseExact` (R07-12): the exact meaning
  subsumes the representation relation, which admits any slot of a
  duplicated parameter, where `compileUniv` and the ingress take the first.
* **Success**: a level whose parameters all occur in a wire-sized context
  compiles from every state (`compileUniv_returns`, `compileUniv_total`).
* **Meaning**: the source side is Source mode's own reading of the level,
  `Ix.LeanIngress.ingressLevel σ` under a numbering `σ` of the level
  parameters, evaluated with `Ix.Kernel.Level.eval`. Under valuations
  aligned at the slot `nameIndex` gives each parameter, the ingress reading
  of a level has the value of its lowering (`lower_eval`,
  `compileUniv_eval`, `compileUniv_total_eval`); the lowering mentions only
  the context's slots (`lower_occurs`). -/

namespace Ix.CompileCert.UniverseMeaning

open Ix (Name Level)
open Ix.CompileM Ix.Compile.ExactKey
open Ix.Kernel (LevelParam)

/-! ## Parameter positions -/

theorem nameIndex_correct {name : Name} {params : List Name} {index : Nat}
    (found : nameIndex name params = some index) : params[index]? = some name := by
  obtain ⟨bound, same, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact List.getElem?_eq_some_iff.mpr ⟨bound, (nameEq_iff _ _).mp same⟩

theorem nameIndex_lt {name : Name} {params : List Name} {index : Nat}
    (found : nameIndex name params = some index) : index < params.length :=
  (List.findIdx?_eq_some_iff_getElem.mp found).1

theorem nameIndex_exists {params : List Name} {name : Name} (member : name ∈ params) :
    ∃ index, nameIndex name params = some index ∧ index < params.length := by
  cases found : nameIndex name params with
  | none =>
    have absent := List.findIdx?_eq_none_iff.mp found
    have := absent name member
    have yes := (nameEq_iff name name).mpr rfl
    rw [yes] at this
    contradiction
  | some index => exact ⟨index, rfl, nameIndex_lt found⟩

/-! ## The specification -/

/-- Exact positional lowering, including first-occurrence parameter lookup
and the production wire-index bound. It is independent of compiler success. -/
def lower (params : List Name) : Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ level _ => do return .succ (← lower params level)
  | .max left right _ => do return .max (← lower params left) (← lower params right)
  | .imax left right _ => do return .imax (← lower params left) (← lower params right)
  | .param name _ => do
    let index ← nameIndex name params
    if index < UInt64.size then some (.var index.toUInt64) else none
  | .mvar .. => none

/-- A source condition independent of whether compilation succeeds: every
parameter occurs in the context, and there is no metavariable. -/
def Scoped (params : List Name) : Level → Prop
  | .zero _ => True
  | .succ level _ => Scoped params level
  | .max left right _ | .imax left right _ => Scoped params left ∧ Scoped params right
  | .param name _ => name ∈ params
  | .mvar .. => False

/-- A lowering mentions only slots of the context. -/
theorem lower_occurs {params : List Name} {source : Level} {value : Ixon.Univ}
    (lowered : lower params source = some value) :
    ∀ parameter, CanonUnivScope.Occurs parameter value → parameter.toNat < params.length := by
  induction source generalizing value with
  | zero hash =>
    cases Option.some.inj lowered
    intro parameter occurs
    cases occurs
  | succ child hash ih =>
    cases step : lower params child with
    | none => simp [lower, step] at lowered
    | some out =>
      simp only [lower, step, bind, Option.bind, pure] at lowered
      cases Option.some.inj lowered
      exact ih (value := out) step
  | max left right hash leftIH rightIH | imax left right hash leftIH rightIH =>
    cases first : lower params left with
    | none => simp [lower, first] at lowered
    | some leftOut =>
      cases second : lower params right with
      | none => simp [lower, first, second] at lowered
      | some rightOut =>
        simp only [lower, first, second, bind, Option.bind, pure] at lowered
        cases Option.some.inj lowered
        intro parameter occurs
        rcases occurs with inLeft | inRight
        · exact leftIH first parameter inLeft
        · exact rightIH second parameter inRight
  | param name hash =>
    cases found : nameIndex name params with
    | none => simp [lower, found] at lowered
    | some index =>
      by_cases bounded : index < UInt64.size
      · simp only [lower, found, bind, Option.bind, bounded, ↓reduceIte] at lowered
        cases Option.some.inj lowered
        intro parameter occurs
        cases occurs
        rw [UInt64.toNat_ofNat_of_lt' bounded]
        exact nameIndex_lt found
      · simp [lower, found, bounded] at lowered
  | mvar name hash => cases lowered

/-- **The value of a lowering is the value Source mode reads.** Under a
numbering `σ` of the level parameters, the ingress reads `source` as a
level whose value, under every valuation `φ` of positions aligned with the
wire valuation `ρ` at the slot `nameIndex` gives each parameter, is the
value of the lowering. -/
theorem lower_eval (params : List Name) (σ : Name → LevelParam) {source : Level}
    {value : Ixon.Univ} (lowered : lower params source = some value) :
    ∃ level, Ix.LeanIngress.ingressLevel σ source = .ok level ∧
      ∀ (φ : LevelParam → Nat) (ρ : UInt64 → Nat),
        (∀ name index, nameIndex name params = some index → index < UInt64.size →
          φ (σ name) = ρ index.toUInt64) →
        Ix.Kernel.Level.eval φ level = univEval ρ value := by
  induction source generalizing value with
  | zero hash =>
    cases Option.some.inj lowered
    exact ⟨.zero, rfl, fun _ _ _ => rfl⟩
  | succ child hash ih =>
    cases step : lower params child with
    | none => simp [lower, step] at lowered
    | some out =>
      simp only [lower, step, bind, Option.bind, pure] at lowered
      cases Option.some.inj lowered
      obtain ⟨level, read, meaning⟩ := ih step
      refine ⟨.succ level, by rw [Ix.LeanIngress.ingressLevel, read]; rfl, ?_⟩
      intro φ ρ aligned
      simp only [Ix.Kernel.Level.eval, univEval, meaning φ ρ aligned]
  | max left right hash leftIH rightIH =>
    cases first : lower params left with
    | none => simp [lower, first] at lowered
    | some leftOut =>
      cases second : lower params right with
      | none => simp [lower, first, second] at lowered
      | some rightOut =>
        simp only [lower, first, second, bind, Option.bind, pure] at lowered
        cases Option.some.inj lowered
        obtain ⟨leftLevel, leftRead, leftMeaning⟩ := leftIH first
        obtain ⟨rightLevel, rightRead, rightMeaning⟩ := rightIH second
        refine ⟨.max leftLevel rightLevel, by rw [Ix.LeanIngress.ingressLevel, leftRead, rightRead]; rfl, ?_⟩
        intro φ ρ aligned
        simp only [Ix.Kernel.Level.eval, univEval, leftMeaning φ ρ aligned, rightMeaning φ ρ aligned]
  | imax left right hash leftIH rightIH =>
    cases first : lower params left with
    | none => simp [lower, first] at lowered
    | some leftOut =>
      cases second : lower params right with
      | none => simp [lower, first, second] at lowered
      | some rightOut =>
        simp only [lower, first, second, bind, Option.bind, pure] at lowered
        cases Option.some.inj lowered
        obtain ⟨leftLevel, leftRead, leftMeaning⟩ := leftIH first
        obtain ⟨rightLevel, rightRead, rightMeaning⟩ := rightIH second
        refine ⟨.imax leftLevel rightLevel, by rw [Ix.LeanIngress.ingressLevel, leftRead, rightRead]; rfl, ?_⟩
        intro φ ρ aligned
        simp only [Ix.Kernel.Level.eval, univEval, leftMeaning φ ρ aligned, rightMeaning φ ρ aligned]
  | param name hash =>
    cases found : nameIndex name params with
    | none => simp [lower, found] at lowered
    | some index =>
      by_cases bounded : index < UInt64.size
      · simp only [lower, found, bind, Option.bind, bounded, ↓reduceIte] at lowered
        cases Option.some.inj lowered
        refine ⟨.param (σ name), rfl, ?_⟩
        intro φ ρ aligned
        exact aligned name index found bounded
      · simp [lower, found, bounded] at lowered
  | mvar name hash => cases lowered

/-- A scoped level under a wire-sized context has a lowering. -/
theorem lower_some {params : List Name} (bounded : params.length ≤ UInt64.size) {source : Level}
    (scope : Scoped params source) : ∃ value, lower params source = some value := by
  induction source with
  | zero hash => exact ⟨.zero, rfl⟩
  | succ child hash ih =>
    obtain ⟨value, lowered⟩ := ih scope
    exact ⟨.succ value, by simp only [lower, lowered, bind, Option.bind, pure]⟩
  | max left right hash leftIH rightIH =>
    simp only [Scoped] at scope
    obtain ⟨first, leftLowered⟩ := leftIH scope.1
    obtain ⟨second, rightLowered⟩ := rightIH scope.2
    exact ⟨.max first second, by simp only [lower, leftLowered, rightLowered, bind, Option.bind, pure]⟩
  | imax left right hash leftIH rightIH =>
    simp only [Scoped] at scope
    obtain ⟨first, leftLowered⟩ := leftIH scope.1
    obtain ⟨second, rightLowered⟩ := rightIH scope.2
    exact ⟨.imax first second, by simp only [lower, leftLowered, rightLowered, bind, Option.bind, pure]⟩
  | param name hash =>
    obtain ⟨index, found, inside⟩ := nameIndex_exists (params := params) scope
    have fits : index < UInt64.size := Nat.lt_of_lt_of_le inside bounded
    exact ⟨.var index.toUInt64, by simp only [lower, found, bind, Option.bind, fits, ↓reduceIte]⟩
  | mvar name hash => exact scope.elim

/-! ## The memo's meaning -/

/-- Every entry of the universe memo is the exact lowering of its key. -/
def UnivCacheExact (state : BlockState) : Prop :=
  CacheSound (fun (key : UnivKey) value => lower key.params key.level = some value) state.univCache

theorem univCacheExact_empty (state : BlockState) : UnivCacheExact { state with univCache := {} } :=
  CacheSound.empty _

theorem univCacheExact_cacheUniv {state : BlockState} (prior : UnivCacheExact state)
    (key : UnivKey) (value : Ixon.Univ) (exact : lower key.params key.level = some value) :
    UnivCacheExact (state.cacheUniv key value) :=
  CacheSound.insert prior key value exact

/-- The cached completion of a compile step. -/
theorem keeps_finish (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ)
    (exact : lower key.params key.level = some value) :
    Keeps context UnivCacheExact (do
      let result ← Pure.pure value
      modifyBlockState (fun state => state.cacheUniv key result)
      Pure.pure result) (fun result => lower key.params key.level = some result) :=
  Keeps.bind (Keeps.pure exact) (fun result correct =>
    Keeps.bind (Keeps.modify context _ (fun _ prior => univCacheExact_cacheUniv prior key result correct))
      (fun _ _ => Keeps.pure correct))

/-! ## The compiler computes the specification -/

/-- **Every run keeps the memo exact, and a successful one returns the
exact lowering** of the source level under the block's context, warm memo
hits included. -/
theorem compileUniv_exact (source : Level) (context : CompileEnv × BlockEnv) :
    Keeps context UnivCacheExact (compileUniv source)
      (fun value => lower context.2.univCtx source = some value) := by
  induction source <;> rw [compileUniv]
  all_goals
    apply Keeps.bind (Keeps.get context _)
    intro state valid
    apply Keeps.bind (Keeps.readBlock context _)
    intro block same
    subst block
    dsimp only
    split
    · rename_i value found
      exact Keeps.pure (valid _ _ found)
  · exact keeps_finish context _ _ rfl
  · apply Keeps.bind (by assumption)
    intro value good
    exact keeps_finish context _ _ (by simp only [lower, good, bind, Option.bind, pure])
  · apply Keeps.bind (by assumption)
    intro first firstGood
    apply Keeps.bind (by assumption)
    intro second secondGood
    exact keeps_finish context _ _ (by simp only [lower, firstGood, secondGood, bind, Option.bind, pure])
  · apply Keeps.bind (by assumption)
    intro first firstGood
    apply Keeps.bind (by assumption)
    intro second secondGood
    exact keeps_finish context _ _ (by simp only [lower, firstGood, secondGood, bind, Option.bind, pure])
  · rename_i name hash _ _
    split
    · rename_i index found
      exact Keeps.bind (Keeps.checkedIndex context _ "universe parameter" index) (fun value good =>
        keeps_finish context _ _ (by simp only [lower, found, bind, Option.bind, good.1, ↓reduceIte, good.2]))
    · exact Keeps.bind (Keeps.readBlock context _) (fun _ _ => Keeps.throwBind context _ _ _ _)
  · exact Keeps.throwBind context _ _ _ _

theorem compileUniv_value (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (exact : UnivCacheExact before) {value : Ixon.Univ}
    (ran : (rawRun (compileUniv source) context before).1 = .ok value) :
    lower context.2.univCtx source = some value :=
  (compileUniv_exact source context before exact).2 value ran

/-- A warm and a cold compile of the same level give the same universe. -/
theorem compileUniv_same (source : Level) (context : CompileEnv × BlockEnv)
    (first second : BlockState) (firstExact : UnivCacheExact first) (secondExact : UnivCacheExact second)
    {left right : Ixon.Univ}
    (leftRan : (rawRun (compileUniv source) context first).1 = .ok left)
    (rightRan : (rawRun (compileUniv source) context second).1 = .ok right) : left = right :=
  Option.some.inj ((compileUniv_value source context first firstExact leftRan).symm.trans
    (compileUniv_value source context second secondExact rightRan))

/-- **The compiled universe has the source level's value**, as Source mode
reads it (`ingressLevel σ`), under every valuation aligned at the slots
`nameIndex` gives. -/
theorem compileUniv_eval (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (exact : UnivCacheExact before) {value : Ixon.Univ}
    (ran : (rawRun (compileUniv source) context before).1 = .ok value) (σ : Name → LevelParam) :
    ∃ level, Ix.LeanIngress.ingressLevel σ source = .ok level ∧
      ∀ (φ : LevelParam → Nat) (ρ : UInt64 → Nat),
        (∀ name index, nameIndex name context.2.univCtx = some index → index < UInt64.size →
          φ (σ name) = ρ index.toUInt64) →
        Ix.Kernel.Level.eval φ level = univEval ρ value :=
  lower_eval context.2.univCtx σ (compileUniv_value source context before exact ran)

/-! ## Success -/

theorem returns_finish (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ) :
    Returns context (do
      let result ← Pure.pure value
      modifyBlockState (fun state => state.cacheUniv key result)
      Pure.pure result) := by
  intro state
  exact ⟨value, rfl⟩

/-- **A scoped level compiles from every memo state**, under a wire-sized
context. Exactness of the memo is separate (`compileUniv_exact`). -/
theorem compileUniv_returns (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) : Returns context (compileUniv source) := by
  induction source <;> simp only [Scoped] at *
  all_goals try contradiction
  all_goals
    intro state
    rw [compileUniv]
    simp only [rawRun_bind, rawRun_get, rawRun_readBlock]
    split
    · exact ⟨_, rfl⟩
  · exact returns_finish context _ _ state
  · rename_i level hash ih _ _
    exact Returns.bind (ih scope) (fun value => returns_finish context _ (.succ value)) state
  · rename_i left right hash ihLeft ihRight _ _
    exact Returns.bind (ihLeft scope.1) (fun first =>
      Returns.bind (ihRight scope.2) (fun second => returns_finish context _ (.max first second))) state
  · rename_i left right hash ihLeft ihRight _ _
    exact Returns.bind (ihLeft scope.1) (fun first =>
      Returns.bind (ihRight scope.2) (fun second => returns_finish context _ (.imax first second))) state
  · obtain ⟨index, found, bound⟩ := nameIndex_exists scope
    rw [found]
    have fits := Nat.lt_of_lt_of_le bound bounded
    simp only [checkedTableIndex, fits]
    exact returns_finish context _ _ state

theorem compileUniv_total (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) (before : BlockState) (exact : UnivCacheExact before) :
    ∃ value after, rawRun (compileUniv source) context before = (.ok value, after) ∧
      UnivCacheExact after ∧ lower context.2.univCtx source = some value := by
  obtain ⟨value, success⟩ := compileUniv_returns source context bounded scope before
  have checked := compileUniv_exact source context before exact
  exact ⟨value, _, Prod.ext success rfl, checked.1, checked.2 value success⟩

/-- **No success premise**: a scoped level under a wire-sized context
compiles from an empty memo, and its compiled universe has the value Source
mode reads, under every aligned valuation. -/
theorem compileUniv_total_eval (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) (before : BlockState) (σ : Name → LevelParam) :
    ∃ value after level,
      rawRun (compileUniv source) context { before with univCache := {} } = (.ok value, after) ∧
      UnivCacheExact after ∧ Ix.LeanIngress.ingressLevel σ source = .ok level ∧
      ∀ (φ : LevelParam → Nat) (ρ : UInt64 → Nat),
        (∀ name index, nameIndex name context.2.univCtx = some index → index < UInt64.size →
          φ (σ name) = ρ index.toUInt64) →
        Ix.Kernel.Level.eval φ level = univEval ρ value := by
  obtain ⟨value, after, ran, exact, lowered⟩ :=
    compileUniv_total source context bounded scope _ (univCacheExact_empty before)
  obtain ⟨level, read, meaning⟩ := lower_eval context.2.univCtx σ lowered
  exact ⟨value, after, level, ran, exact, read, meaning⟩

end Ix.CompileCert.UniverseMeaning
