module
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.BytecodeEval
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Proofs.LowerShared
public import Ix.Aiur.Proofs.ConcreteEvalInversion

public section

namespace Aiur

open Concrete

instance : DecidableEq Local
  | .str s₁, .str s₂ =>
    if h : s₁ = s₂ then isTrue (h ▸ rfl) else isFalse fun h' => h (by cases h'; rfl)
  | .idx n₁, .idx n₂ =>
    if h : n₁ = n₂ then isTrue (h ▸ rfl) else isFalse fun h' => h (by cases h'; rfl)
  | .str _, .idx _ => isFalse fun h => by cases h
  | .idx _, .str _ => isFalse fun h => by cases h

private theorem Local.beq_implies_eq {a b : Local} (h : (a == b) = true) : a = b := by
  cases a <;> cases b
  all_goals
    first
      | (rename_i x y
         have hbool : (x == y) = true := h
         have hxy : x = y := eq_of_beq hbool
         exact congrArg _ hxy)
      | (exact absurd h (by intro hbool; cases hbool))

private theorem Local.eq_implies_beq (a : Local) : (a == a) = true := by
  cases a <;> (rename_i x; exact (BEq.rfl : (x == x) = true))

private instance : LawfulBEq Local where
  eq_of_beq := Local.beq_implies_eq
  rfl := Local.eq_implies_beq _

private instance : EquivBEq Local := inferInstance

private instance : LawfulHashable Local where
  hash_eq a b h := by have := Local.beq_implies_eq h; subst this; rfl

/-- The local simulation relation between a source binding environment and the
bytecode value map. -/
@[expose]
def boundFlat
    (decls : Source.Decls) (funcIdx : Global → Option Nat)
    (env : Concrete.Eval.Bindings)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (map : Array G) : Prop :=
  ∀ x v, (x, v) ∈ env →
    ∃ idxs, bindings[x]? = some idxs ∧
      ∀ i : Fin idxs.size, map[idxs[i]]? = some ((flattenValue decls funcIdx v)[i]?.getD 0)

/-- Width-tracking invariant: every binding in `env` maps under `bindings`
to an idx array whose size matches the flattened value size.

This is the width half of the full `CompileInv`/simulation relation
(value-level equality is the other half). It is exactly the piece of
information the `.var` / `.letVar` arms of `toIndex_preservation_core`
need in order to discharge the `idxs.size = flattenValue.size`
conclusion; `boundFlat … #[]` on its own does NOT supply it because the
empty bytecode map vacuously satisfies the pointwise equation for any
`idxs.size = 0`, regardless of the flattened width of `v`. -/
@[expose]
def sizeInv
    (decls : Source.Decls) (funcIdx : Global → Option Nat)
    (env : Concrete.Eval.Bindings)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx)) : Prop :=
  ∀ x v, (x, v) ∈ env →
    ∃ idxs, bindings[x]? = some idxs ∧
      idxs.size = (flattenValue decls funcIdx v).size










/-- `expectIdx` reduces to `.ok idxs[0]` whenever `toIndex` produces a width-1
result. Used to discharge the `.add`/`.sub`/`.mul`/`.eqZero`/`.load`/`.ioRead`/
`.ioSetInfo`/u8/u32 arms uniformly. -/
private theorem expectIdx_run_of_widthOne
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Concrete.Term) (st₀ : CompilerState)
    (h : WidthOne layoutMap term) :
    ∃ i st', (expectIdx layoutMap bindings term).run st₀ = .ok i st' := by
  obtain ⟨idxs, st', hrun, hsz⟩ := h bindings st₀
  unfold expectIdx
  rw [compileM_bind_ok st₀ _ _ st' hrun]
  simp only [hsz, dite_true]
  refine ⟨idxs[0], st', ?_⟩
  exact compileM_pure_run st' _









/-- CompileM-side fold-progress for the body of `buildArgs`. Given that every
`t ∈ xs.map (·.1)` lowers successfully, the accumulator-append fold succeeds.
Stated polymorphically in `P` so callers can instantiate with `args.attach`
(`P = (· ∈ args)`). -/
private theorem buildArgs_fold_ok_aux
    {layoutMap : LayoutMap}
    {bindings : Std.HashMap Local (Array Bytecode.ValIdx)}
    {P : Concrete.Term → Prop}
    (xs : List (Subtype P))
    (hxs : ∀ t ∈ xs.map (·.1), ∀ st, ∃ idxs st',
      (toIndex layoutMap bindings t).run st = .ok idxs st')
    (init : Array Bytecode.ValIdx) (st : CompilerState) :
    ∃ idxs st', (xs.foldlM (init := init)
      (fun acc ⟨arg, _⟩ => do
        pure (acc.append (← toIndex layoutMap bindings arg))) : CompileM _).run st
      = .ok idxs st' := by
  induction xs generalizing init st with
  | nil =>
    refine ⟨init, st, ?_⟩
    simp [List.foldlM_nil, pure, EStateM.pure, EStateM.run]
  | cons x rest ih =>
    have hxmem : x.1 ∈ (x :: rest).map (·.1) := List.mem_cons_self
    obtain ⟨idxs_x, st₁, hx⟩ := hxs x.1 hxmem st
    have hrest : ∀ t ∈ rest.map (·.1), ∀ st, ∃ idxs st',
        (toIndex layoutMap bindings t).run st = .ok idxs st' :=
      fun t ht st => hxs t (List.mem_cons_of_mem _ ht) st
    obtain ⟨idxs', st', hrest_run⟩ := ih hrest (init.append idxs_x) st₁
    refine ⟨idxs', st', ?_⟩
    simp only [List.foldlM_cons]
    have hstep : ((do let y ← toIndex layoutMap bindings x.1; pure (init.append y))
        : CompileM _).run st = .ok (init.append idxs_x) st₁ := by
      rw [compileM_bind_ok st _ _ st₁ hx]
      exact compileM_pure_run st₁ _
    rw [compileM_bind_ok st _ _ st₁ hstep]
    exact hrest_run









end Aiur

end -- public section
