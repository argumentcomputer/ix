import Ix.Cert.Statement
import Ix.CompileCert.RawRun

/-! # A block's records are the block compile's

`runBlock` compiles every block from Lean's own declarations. Its records are
those of the block compile, a lone constant's `compileConstantInfo` or
`compileMutualBlock` over the members in Lean's order (`sourceClasses`), run
from the empty block state: the form the reading theorems take.

* `runBlock_compiles`: a block's records are those of `compileBlock` run from
  the empty block state;
* `compileBlock_result`, `compileBlock_records`, `runBlock_records`: and those
  are the block compile's (the member lookups and `MutConst.mkIndc` change no
  state, `mkIndc_preserves`). The block's `Muts` entry is registered after its
  `BlockResult` is computed, which it returns as it is (`Returns`). -/

namespace Ix.Cert.BlockRecords

open Ix.CompileM

/-- A block's records: its block constant, bytes and address, and each
projection's name and constant (not their metadata). -/
def recordsOf (r : BlockResult) :
    Ixon.Constant × ByteArray × Address × Array (Ix.Name × Ixon.Constant) :=
  (r.block, r.blockBytes, r.blockAddr, r.projections.map fun p => (p.1, p.2.1))

/-- **A block compiles as `compileBlock`**, from the empty block state. -/
theorem runBlock_compiles {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name}
    {r : BlockResult} {cache : BlockState}
    (h : runBlock cenv all lo = .ok (r, cache)) :
    CompileM.run cenv { all, current := lo, mutCtx := default, univCtx := [] } {}
      (compileBlock lo all) = .ok (r, cache) := h

/-! ## What `compileBlock` returns -/

open Ix.CompileCert (rawRun rawRun_pure bind_ok)

/-- Every successful run of `m` returns a value with `P`. -/
def Returns {α : Type} (P : α → Prop) (m : CompileM α) : Prop :=
  ∀ ctx s x s', rawRun m ctx s = (.ok x, s') → P x

theorem Returns.pure {α : Type} {P : α → Prop} {x : α} (h : P x) : Returns P (pure x) := by
  intro ctx s y s' ran
  rw [rawRun_pure] at ran
  cases ran
  exact h

theorem Returns.bind {α β : Type} {P : α → Prop} {m : CompileM β} {k : β → CompileM α}
    (h : ∀ b, Returns P (k b)) : Returns P (m >>= k) := by
  intro ctx s x s' ran
  obtain ⟨b, mid, -, ran⟩ := bind_ok ran
  exact h b ctx mid x s' ran

theorem Returns.ite {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {a b : CompileM α}
    (ha : Returns P a) (hb : Returns P b) : Returns P (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem Returns.dite {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {a : c → CompileM α}
    {b : ¬c → CompileM α} (ha : ∀ h, Returns P (a h)) (hb : ∀ h, Returns P (b h)) :
    Returns P (if h : c then a h else b h) := by
  split
  · exact ha _
  · exact hb _

/-- A trace's value is its continuation's. -/
theorem Returns.dbgTrace {α : Type} {P : α → Prop} {msg : String} {k : Unit → CompileM α}
    (h : Returns P (k ())) : Returns P (dbgTrace msg k) := h

/-- One step of a walk through a `do` block for `Returns P`: a bind (whose
first action is never looked into), an `if`, a trace, a `return` (its value
then shown to have `P`), or a match on a local. Each lemma is applied at
reducible transparency, so no step unfolds the block's own definitions or the
monad's (a `let` or `have` is substituted by the unifier, a join point's
application beta-reduced): the walk's cost grows with the number of steps,
not with what they call, and a bind, `let` or `if` added to the block needs
no change to it. -/
macro "returns_step" : tactic => `(tactic| first
  | ((with_reducible apply Returns.bind); intro _)
  | (with_reducible apply Returns.ite)
  | ((with_reducible apply Returns.dite) <;> intro _)
  | (with_reducible apply Returns.dbgTrace)
  | ((with_reducible apply Returns.pure); rfl)
  | split)

theorem Returns.elim {α : Type} {P : α → Prop} {m : CompileM α} (hm : Returns P m)
    {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {x : α} : rawRun m ctx s = (.ok x, s') → P x :=
  hm ctx s x s'

theorem rawRun_ite {α : Type} {c : Prop} [Decidable c] {a b : CompileM α} {ctx : CompileEnv × BlockEnv}
    {s : BlockState} {r : Except CompileError α × BlockState}
    (h : rawRun (if c then a else b) ctx s = r) : rawRun a ctx s = r ∨ rawRun b ctx s = r := by
  by_cases hc : c
  · exact .inl (by simpa [hc] using h)
  · exact .inr (by simpa [hc] using h)


/-! ## The members' loop changes no state -/

open Ix.CompileCert (Preserves Preserves.bind Preserves.pure Preserves.throw Preserves.readCompile
  Preserves.forIn_list)

theorem findConst_preserves (n : Ix.Name) : Preserves id (findConst n) := by
  unfold findConst
  refine Preserves.bind (Preserves.readCompile id) fun env => ?_
  split
  · exact Preserves.pure id _
  · exact Preserves.throw id _

theorem collectMutConstConstructors_preserves :
    ∀ (names : List Ix.Name) (acc : Array ConstructorVal), Preserves id (collectMutConstConstructors names acc)
  | [], acc => Preserves.pure id acc
  | n :: rest, acc => by
    unfold collectMutConstConstructors
    refine Preserves.bind (findConst_preserves n) fun c => ?_
    split
    · exact collectMutConstConstructors_preserves rest _
    · exact Preserves.throw id _

theorem mkIndc_preserves (val : InductiveVal) : Preserves id (MutConst.mkIndc val) := by
  unfold MutConst.mkIndc
  exact Preserves.bind (collectMutConstConstructors_preserves _ _) fun _ => Preserves.pure id _

/-- **The block `compileBlock` returns is the block compile's**: a
lone non-inductive constant's `compileConstantInfo`, or the mutual block
`compileMutualBlock` compiled from the members in Lean's order
(`sourceClasses`), up to the class order it records (the `Muts` entry is
registered after it and returns it as it is). -/
theorem compileBlock_result {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {s s' : BlockState} {r : BlockResult}
    (h : rawRun (compileBlock lo all) ctx s = (.ok r, s')) :
    ∃ const s₁, rawRun (findConst lo) ctx s = (.ok const, s₁) ∧
      ((∃ s₂, rawRun (compileConstantInfo const) ctx s₁ = (.ok r, s₂)) ∨
        ∃ cs s₂ out s₄, rawRun (forIn all #[] fun n (acc : Array Ix.MutConst) => do
            match ← findConst n with
            | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
            | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
            | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
            | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
            | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
            | _ => pure (ForInStep.yield acc)) ctx s₁ = (.ok cs, s₂) ∧
          rawRun (compileMutualBlock (sourceClasses cs)) ctx s₂ = (.ok out, s₄) ∧
          recordsOf r = recordsOf out) := by
  unfold compileBlock at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  refine ⟨const, s₁, hc, ?_⟩
  rcases rawRun_ite h with h | h
  · left
    exact ⟨_, h⟩
  · right
    obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
    obtain ⟨out, s₄, hout, h⟩ := bind_ok h
    refine ⟨cs, s₂, out, s₄, hcs, hout, ?_⟩
    revert h
    refine Returns.elim
      (P := fun (x : BlockResult) =>
        recordsOf x = recordsOf out) ?_
    repeat returns_step


theorem findConst_ok {n : Ix.Name} {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {c : Ix.ConstantInfo}
    (ran : rawRun (findConst n) ctx s = (.ok c, s')) : ctx.1.env.get? n = some c := by
  simp only [findConst, Ix.CompileCert.rawRun_bind, Ix.CompileCert.rawRun_read] at ran
  cases found : ctx.1.env.get? n with
  | none => rw [found] at ran; cases ran
  | some c' => rw [found] at ran; cases ran; rfl

theorem forIn_set_state {γ : Type} {all : Ix.Set Ix.Name} {init : γ} {body : Ix.Name → γ → CompileM (ForInStep γ)}
    {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {x : Except CompileError γ}
    (h : rawRun (forIn all init body) ctx s = (x, s')) (keeps : ∀ n acc, Preserves id (body n acc)) :
    s' = s := by
  have key := Preserves.forIn_list all.toList init body keeps ctx s
  rw [← Std.HashSet.forIn_eq_forIn_toList, h] at key
  exact key

/-- **`compileBlock_result` from the state it starts in**: the
member lookups and the members' loop change no state, so the block compile
(a lone constant's, or `compileMutualBlock` over the members in Lean's order)
runs from the state `compileBlock` starts from, the empty one in
`runBlock`. -/
theorem compileBlock_records {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {s s' : BlockState} {r : BlockResult}
    (h : rawRun (compileBlock lo all) ctx s = (.ok r, s')) :
    ∃ const, ctx.1.env.get? lo = some const ∧
      ((∃ s₂, rawRun (compileConstantInfo const) ctx s = (.ok r, s₂)) ∨
        ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s₄ : BlockState),
          rawRun (compileMutualBlock (sourceClasses cs)) ctx s = (.ok out, s₄) ∧
          recordsOf r = recordsOf out) := by
  obtain ⟨const, s₁, hc, rest⟩ := compileBlock_result h
  have h₁ : s₁ = s := by
    have := findConst_preserves lo ctx s
    rw [hc] at this
    exact this
  subst h₁
  refine ⟨const, findConst_ok hc, ?_⟩
  rcases rest with single | ⟨cs, s₂, out, s₄, hcs, hout, same⟩
  · exact .inl single
  · have h₂ : s₂ = s₁ := forIn_set_state hcs fun n acc => by
      refine Preserves.bind (findConst_preserves n) fun c => ?_
      split
      · exact Preserves.bind (mkIndc_preserves _) fun _ => Preserves.pure id _
      all_goals exact Preserves.pure id _
    subst h₂
    exact .inr ⟨cs, out, s₄, hout, same⟩

/-- **A block publishes the block compile's records**: the records
`runBlock` returns are those of the lone constant's
`compileConstantInfo`, or of `compileMutualBlock` over the members in Lean's
order (`sourceClasses`), each run from the empty block state in the block's
environment. -/
theorem runBlock_records {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name}
    {r : BlockResult} {cache : BlockState}
    (h : runBlock cenv all lo = .ok (r, cache)) :
    ∃ const, cenv.env.get? lo = some const ∧
      ((∃ (r' : BlockResult) (s₂ : BlockState), rawRun (compileConstantInfo const)
          (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok r', s₂) ∧
          recordsOf r = recordsOf r') ∨
        ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s₄ : BlockState),
          rawRun (compileMutualBlock (sourceClasses cs))
            (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok out, s₄) ∧
          recordsOf r = recordsOf out) := by
  obtain ⟨const, found, rest⟩ :=
    compileBlock_records (Ix.CompileCert.run_success (runBlock_compiles h))
  refine ⟨const, found, ?_⟩
  rcases rest with ⟨s₂, single⟩ | ⟨cs, out, s₄, block, same⟩
  · exact .inl ⟨r, s₂, single, rfl⟩
  · exact .inr ⟨cs, out, s₄, block, same⟩

end Ix.Cert.BlockRecords
