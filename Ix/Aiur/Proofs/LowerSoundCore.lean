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

instance : LawfulBEq Local where
  eq_of_beq := Local.beq_implies_eq
  rfl := Local.eq_implies_beq _

instance : EquivBEq Local := inferInstance

instance : LawfulHashable Local where
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

/-- Extending `sizeInv` with a new binding. -/
theorem sizeInv_insert
    (decls : Source.Decls) (funcIdx : Global → Option Nat)
    (env : Concrete.Eval.Bindings)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (l : Local) (v : Value) (idxs : Array Bytecode.ValIdx)
    (hinv : sizeInv decls funcIdx env bindings)
    (hsize : idxs.size = (flattenValue decls funcIdx v).size)
    (hfresh : ∀ w, (l, w) ∉ env) :
    sizeInv decls funcIdx ((l, v) :: env) (bindings.insert l idxs) := by
  intro x v' hmem
  rcases List.mem_cons.mp hmem with h_head | h_tail
  · have hx : x = l := congrArg Prod.fst h_head
    have hv' : v' = v := congrArg Prod.snd h_head
    subst hx; subst hv'
    refine ⟨idxs, ?_, hsize⟩
    rw [Std.HashMap.getElem?_insert]
    simp
  · obtain ⟨idxs_x, hlook, hsz⟩ := hinv x v' h_tail
    refine ⟨idxs_x, ?_, hsz⟩
    rw [Std.HashMap.getElem?_insert]
    by_cases hxl : (l == x) = true
    · have hxl' : l = x := Local.beq_implies_eq hxl
      subst hxl'
      exact absurd h_tail (hfresh v')
    · have hxl_false : (l == x) = false := Bool.not_eq_true _ |>.mp hxl
      simp [hxl_false, hlook]

/-- Extending `boundFlat` with a new binding. Requires a per-index witness
`hpt` connecting `idxs`, `v`, and `map` — without it the statement is
unprovable (the new head has no anchor in `map`). -/
theorem boundFlat_insert
    (decls : Source.Decls) (funcIdx : Global → Option Nat)
    (env : Concrete.Eval.Bindings)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (map : Array G)
    (l : Local) (v : Value) (idxs : Array Bytecode.ValIdx)
    (hbf : boundFlat decls funcIdx env bindings map)
    (hfresh : ∀ w, (l, w) ∉ env)
    (hpt : ∀ i : Fin idxs.size,
        map[idxs[i]]? = some ((flattenValue decls funcIdx v)[i]?.getD 0)) :
    boundFlat decls funcIdx ((l, v) :: env) (bindings.insert l idxs) map := by
  intro x v' hmem
  rcases List.mem_cons.mp hmem with h_head | h_tail
  · have hx : x = l := congrArg Prod.fst h_head
    have hv' : v' = v := congrArg Prod.snd h_head
    subst hx; subst hv'
    refine ⟨idxs, ?_, hpt⟩
    rw [Std.HashMap.getElem?_insert]
    simp
  · obtain ⟨idxs_x, hlook, hpt'⟩ := hbf x v' h_tail
    refine ⟨idxs_x, ?_, hpt'⟩
    rw [Std.HashMap.getElem?_insert]
    by_cases hxl : (l == x) = true
    · have hxl' : l = x := Local.beq_implies_eq hxl
      subst hxl'
      exact absurd h_tail (hfresh v')
    · have hxl_false : (l == x) = false := Bool.not_eq_true _ |>.mp hxl
      simp [hxl_false, hlook]

/-- Progress for the straight-line subset: `toIndex` succeeds on every
`IsCore`-admitted term. -/
theorem toIndex_progress_core
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Concrete.Term) (st₀ : CompilerState)
    (h : IsCore layoutMap term) :
    ∃ idxs st, (toIndex layoutMap bindings term).run st₀ = .ok idxs st := by
  induction h generalizing bindings st₀ with
  | @unit t e =>
    refine ⟨#[], st₀, ?_⟩
    unfold toIndex
    exact compileM_pure_run st₀ #[]
  | @var t e l =>
    refine ⟨bindings[l]?.getD #[], st₀, ?_⟩
    unfold toIndex
    exact compileM_pure_run st₀ _
  | @field t e g =>
    refine ⟨Array.range' st₀.valIdx 1,
            { st₀ with valIdx := st₀.valIdx + 1,
                       ops := st₀.ops.push (.const g),
                       degrees := pushOpDegree st₀.degrees (.const g) 1 }, ?_⟩
    unfold toIndex
    exact pushOp_run st₀ (.const g) 1
  | @ref t e g hlayout =>
    rcases hlayout with ⟨fl, hfl⟩ | ⟨cl, hcl⟩
    · refine ⟨Array.range' st₀.valIdx 1,
              { st₀ with valIdx := st₀.valIdx + 1,
                         ops := st₀.ops.push (.const (.ofNat fl.index)),
                         degrees := pushOpDegree st₀.degrees (.const (.ofNat fl.index)) 1 }, ?_⟩
      unfold toIndex
      rw [hfl]
      exact pushOp_run st₀ (.const (.ofNat fl.index)) 1
    · let paddingOp : Bytecode.Op := .const (.ofNat cl.index)
      let st₁ : CompilerState :=
        { st₀ with valIdx := st₀.valIdx + 1,
                   ops := st₀.ops.push paddingOp,
                   degrees := pushOpDegree st₀.degrees paddingOp 1 }
      have hunfold : (toIndex layoutMap bindings (.ref t e g)).run st₀
        = ((do
              let index ← pushOp paddingOp
              if index.size < cl.size then
                let padding := (← pushOp paddingOp)[0]!
                pure (index ++ Array.replicate (cl.size - index.size) padding)
              else
                pure index) : CompileM _).run st₀ := by
        show (toIndex layoutMap bindings (.ref t e g)) st₀ = _
        unfold toIndex
        rw [hcl]
        rfl
      rw [hunfold]
      have hpush₁ : (pushOp paddingOp : CompileM _).run st₀ = .ok (Array.range' st₀.valIdx 1) st₁ :=
        pushOp_run st₀ paddingOp 1
      rw [compileM_bind_ok st₀ (pushOp paddingOp) _ st₁ hpush₁]
      by_cases hsz : (Array.range' st₀.valIdx 1).size < cl.size
      · simp only [hsz, if_true]
        let st₂ : CompilerState :=
          { st₁ with valIdx := st₁.valIdx + 1,
                     ops := st₁.ops.push paddingOp,
                     degrees := pushOpDegree st₁.degrees paddingOp 1 }
        have hpush₂ : (pushOp paddingOp : CompileM _).run st₁ = .ok (Array.range' st₁.valIdx 1) st₂ :=
          pushOp_run st₁ paddingOp 1
        rw [compileM_bind_ok st₁ (pushOp paddingOp) _ st₂ hpush₂]
        refine ⟨Array.range' st₀.valIdx 1
                ++ Array.replicate (cl.size - (Array.range' st₀.valIdx 1).size) (Array.range' st₁.valIdx 1)[0]!,
                st₂, ?_⟩
        exact compileM_pure_run st₂ _
      · simp only [hsz, if_false]
        exact ⟨Array.range' st₀.valIdx 1, st₁, compileM_pure_run st₁ _⟩
  | @letVar t e l v b _hv _hb ihv ihb =>
    obtain ⟨idxs_v, st₁, hv⟩ := ihv bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hv]
    exact ihb (bindings.insert l idxs_v) st₁
  | @letWild t e v b _hv _hb ihv ihb =>
    obtain ⟨idxs_v, st₁, hv⟩ := ihv bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hv]
    exact ihb bindings st₁
  | @ptrVal t e a _ha iha =>
    unfold toIndex
    exact iha bindings st₀
  | @assertEq t e a b r _ha _hb _hr iha ihb ihr =>
    obtain ⟨idxs_a, st₁, ha⟩ := iha bindings st₀
    obtain ⟨idxs_b, st₂, hb⟩ := ihb bindings st₁
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    rw [compileM_bind_ok st₁ _ _ st₂ hb]
    let st₃ : CompilerState :=
      { st₂ with ops := st₂.ops.push (.assertEq idxs_a idxs_b) }
    have hmod := compileM_modify_run st₂
      (fun stt : CompilerState => { stt with ops := stt.ops.push (.assertEq idxs_a idxs_b) })
    rw [compileM_bind_ok st₂ _ _ st₃ hmod]
    exact ihr bindings st₃
  | @debug t e label tOpt r hrecT _hrecR ihtOpt ihr =>
    cases htOpt : tOpt with
    | none =>
      let st₁ : CompilerState :=
        { st₀ with ops := st₀.ops.push (.debug label none) }
      obtain ⟨idxs_r, st₂, hr⟩ := ihr bindings st₁
      refine ⟨idxs_r, st₂, ?_⟩
      have hmod := compileM_modify_run st₀
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label none) })
      unfold toIndex
      have hpure : ((pure none : CompileM (Option (Array Bytecode.ValIdx)))).run st₀ = .ok none st₀ :=
        compileM_pure_run st₀ (none : Option (Array Bytecode.ValIdx))
      rw [compileM_bind_ok st₀ (pure (none : Option (Array Bytecode.ValIdx))) none st₀ hpure]
      rw [compileM_bind_ok st₀ _ () st₁ hmod]
      exact hr
    | some sub =>
      obtain ⟨idxs_t, st₁, ht⟩ := ihtOpt sub htOpt bindings st₀
      let st₂ : CompilerState :=
        { st₁ with ops := st₁.ops.push (.debug label (some idxs_t)) }
      obtain ⟨idxs_r, st₃, hr⟩ := ihr bindings st₂
      refine ⟨idxs_r, st₃, ?_⟩
      have hmod := compileM_modify_run st₁
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label (some idxs_t)) })
      unfold toIndex
      rw [compileM_bind_ok st₀ _ idxs_t st₁ ht]
      rw [compileM_bind_ok st₁ _ (some idxs_t) st₁ (compileM_pure_run st₁ (some idxs_t))]
      rw [compileM_bind_ok st₁ _ () st₂ hmod]
      exact hr

/-! ## Preservation for the straight-line subset of `toIndex`.

**Restated (2026-04-16)** after a parallel-agent audit showed the previous
statement was provably false. Counter-example: with
`env = [(l, .field 3)]` and `bindings = {l ↦ #[]}`, the hypothesis
`boundFlat sourceDecls funcIdx env bindings #[]` is satisfied (the inner
`∀ i : Fin idxs.size` is vacuously true since `idxs.size = 0`), yet the
conclusion on `term = .var l` demands `idxs.size = 1 = flattenValue … (.field 3)`
while `toIndex` returns `idxs.size = 0`.

The strengthened statement adds two hypotheses:
1. `hcore : IsCore layoutMap term` — restricts to the straight-line subset.
2. `hinv : sizeInv sourceDecls funcIdx env bindings` — the width invariant. -/

/-- Width preservation for the `.ref g` arm of `toIndex_preservation_core`.
Hoisted from the case body so the `StructCompatible`-style alignment between
`concDecls.getByKey g` (source of `interp_v`) and `layoutMap[g]?` (source
of `idxs`) can be attacked as a focused lemma.

BLOCKED ON: the statement compares the width of `flattenValue` applied to
the runtime value from `concDecls.getByKey g` to the width of the idx array
produced by `toIndex`'s `.ref` arm. Closing it requires a `StructCompatible`
precondition linking `concDecls`' function/constructor layouts to their
flattened widths. -/
theorem toIndex_preservation_ref_arm
    (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (t : Concrete.Typ) (e : Bool) (g : Global) (env : Concrete.Eval.Bindings)
    (fuel : Nat) (st₀ : CompilerState) (evalSt : Concrete.Eval.EvalState)
    (_hlayout : (∃ fl, layoutMap[g]? = some (.function fl)) ∨
                 (∃ cl, layoutMap[g]? = some (.constructor cl)))
    (interp_v : Value)
    (_hinterp : (Concrete.Eval.interp concDecls fuel env
                  (.ref t e g) evalSt).toOption.map Prod.fst = some interp_v)
    (_hcompat : RefCompat sourceDecls concDecls funcIdx layoutMap g) :
    ∃ idxs st',
      (toIndex layoutMap bindings (.ref t e g)).run st₀ = .ok idxs st' ∧
      idxs.size = (flattenValue sourceDecls funcIdx interp_v).size := by
  obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim _hinterp
  rw [Concrete.Eval.interp_ref] at hok
  rcases _hlayout with ⟨fl, hfl⟩ | ⟨cl, hcl⟩
  · -- Function branch.
    refine ⟨Array.range' st₀.valIdx 1,
            { st₀ with valIdx := st₀.valIdx + 1,
                       ops := st₀.ops.push (.const (.ofNat fl.index)),
                       degrees := pushOpDegree st₀.degrees (.const (.ofNat fl.index)) 1 },
            ?_, ?_⟩
    · unfold toIndex
      rw [hfl]
      exact pushOp_run st₀ (.const (.ofNat fl.index)) 1
    · unfold RefCompat at _hcompat
      simp only [hfl] at _hcompat
      obtain ⟨⟨f, hconc⟩, hfnsize⟩ := _hcompat
      rw [hconc] at hok
      simp only at hok
      have hv : interp_v = .fn g :=
        (congrArg Prod.fst (Except.ok.inj hok)).symm
      subst hv
      rw [hfnsize]
      simp []
  · -- Constructor branch.
    unfold RefCompat at _hcompat
    simp only [hcl] at _hcompat
    obtain ⟨⟨dt, ctor, hconc, hempty⟩, hctorsize, hcl_pos⟩ := _hcompat
    rw [hconc] at hok
    simp only [hempty, if_true] at hok
    have hv : interp_v = .ctor g #[] :=
      (congrArg Prod.fst (Except.ok.inj hok)).symm
    subst hv
    let paddingOp : Bytecode.Op := .const (.ofNat cl.index)
    let st₁ : CompilerState :=
      { st₀ with valIdx := st₀.valIdx + 1,
                 ops := st₀.ops.push paddingOp,
                 degrees := pushOpDegree st₀.degrees paddingOp 1 }
    have hunfold : (toIndex layoutMap bindings (.ref t e g)).run st₀
      = ((do
            let index ← pushOp paddingOp
            if index.size < cl.size then
              let padding := (← pushOp paddingOp)[0]!
              pure (index ++ Array.replicate (cl.size - index.size) padding)
            else
              pure index) : CompileM _).run st₀ := by
      show (toIndex layoutMap bindings (.ref t e g)) st₀ = _
      unfold toIndex
      rw [hcl]
      rfl
    have hpush₁ : (pushOp paddingOp : CompileM _).run st₀ = .ok (Array.range' st₀.valIdx 1) st₁ :=
      pushOp_run st₀ paddingOp 1
    rw [hunfold]
    rw [compileM_bind_ok st₀ (pushOp paddingOp) _ st₁ hpush₁]
    have hrange_size : (Array.range' st₀.valIdx 1).size = 1 := by
      simp []
    by_cases hsz : (Array.range' st₀.valIdx 1).size < cl.size
    · simp only [hsz, if_true]
      let st₂ : CompilerState :=
        { st₁ with valIdx := st₁.valIdx + 1,
                   ops := st₁.ops.push paddingOp,
                   degrees := pushOpDegree st₁.degrees paddingOp 1 }
      have hpush₂ : (pushOp paddingOp : CompileM _).run st₁ = .ok (Array.range' st₁.valIdx 1) st₂ :=
        pushOp_run st₁ paddingOp 1
      rw [compileM_bind_ok st₁ (pushOp paddingOp) _ st₂ hpush₂]
      refine ⟨Array.range' st₀.valIdx 1
              ++ Array.replicate (cl.size - (Array.range' st₀.valIdx 1).size) (Array.range' st₁.valIdx 1)[0]!,
              st₂, compileM_pure_run st₂ _, ?_⟩
      have hidxs_size :
          (Array.range' st₀.valIdx 1
            ++ Array.replicate (cl.size - (Array.range' st₀.valIdx 1).size)
                (Array.range' st₁.valIdx 1)[0]!).size
          = cl.size := by
        simp only [Array.size_append, Array.size_replicate, hrange_size]
        have hsz' : 1 < cl.size := by rw [← hrange_size]; exact hsz
        omega
      rw [hidxs_size]
      exact hctorsize.symm
    · simp only [hsz, if_false]
      refine ⟨Array.range' st₀.valIdx 1, st₁, compileM_pure_run st₁ _, ?_⟩
      rw [hrange_size]
      have hsz' : cl.size ≤ 1 := by
        have := hsz
        rw [hrange_size] at this
        exact Nat.le_of_not_lt this
      have hcl_eq : cl.size = 1 := Nat.le_antisymm hsz' hcl_pos
      rw [← hcl_eq]
      exact hctorsize.symm

/-- SSA-uniqueness inheritance: if every `.letVar` binder in `term` is fresh
w.r.t. `env`, the outer `term` contains a `.letVar _ _ l _ _` sub-term, and
the global `LetVarBinderNeq` invariant rules out `l'' = l` for other
`.letVar`-bound `l''`, then extending `env` with `(l, _)` still satisfies
SSA-freshness for `.letVar` sub-terms of the body. -/
theorem letVar_SSA_extension_inherits
    (layoutMap : LayoutMap)
    (t : Concrete.Typ) (e : Bool) (l : Local) (v b : Concrete.Term)
    (val : Value) (env : Concrete.Eval.Bindings)
    (_hSsaFresh : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local} {v' b' : Concrete.Term},
      IsCore layoutMap (.letVar t' e' l' v' b') →
      ∀ w, (l', w) ∉ env)
    (_houter : IsCore layoutMap (.letVar t e l v b))
    (hBinderNeq : LetVarBinderNeq layoutMap l) :
    ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local} {v'' b'' : Concrete.Term},
    IsCore layoutMap (.letVar t'' e'' l'' v'' b'') →
    ∀ w, (l'', w) ∉ ((l, val) :: env) := by
  intro t'' e'' l'' v'' b'' hinner w hmem
  rw [List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · have heq : l'' = l := by cases hhead; rfl
    exact absurd heq (hBinderNeq hinner)
  · exact absurd htail (_hSsaFresh hinner w)
theorem toIndex_preservation_core
    (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Concrete.Term) (env : Concrete.Eval.Bindings)
    (fuel : Nat) (st₀ : CompilerState) (evalSt : Concrete.Eval.EvalState)
    (hcore : IsCore layoutMap term)
    (hinv : sizeInv sourceDecls funcIdx env bindings)
    -- SSA freshness: every `.letVar` binding in `term` introduces a `Local`
    -- not already in `env`. This mirrors the concretize pass's SSA-form output.
    (hSsaFresh : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local} {v' b' : Concrete.Term},
      IsCore layoutMap (.letVar t' e' l' v' b') →
      ∀ w, (l', w) ∉ env)
    -- Global uniqueness: every `.letVar`-bound `Local` reachable via `IsCore` is
    -- distinct from every other such `Local`. Needed for the `.letVar` arm to
    -- extend `env` with the binder without colliding on inner `.letVar`s.
    (hBinderNeq : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local} {v' b' : Concrete.Term},
      IsCore layoutMap (.letVar t' e' l' v' b') →
      LetVarBinderNeq layoutMap l')
    -- `.ref`-site compatibility: for every `.ref _ _ g` reachable via `IsCore`,
    -- `layoutMap[g]?` and `concDecls.getByKey g` agree on the flat-size witness.
    (hRefCompat : ∀ {t' : Concrete.Typ} {e' : Bool} {g : Global},
      IsCore layoutMap (.ref t' e' g) →
      RefCompat sourceDecls concDecls funcIdx layoutMap g) :
    ∀ (interp_v : Value),
      (Concrete.Eval.interp concDecls fuel env term evalSt).toOption.map Prod.fst
        = some interp_v →
      ∃ idxs st',
        (toIndex layoutMap bindings term).run st₀ = .ok idxs st' ∧
        idxs.size = (flattenValue sourceDecls funcIdx interp_v).size := by
  induction hcore generalizing bindings st₀ env fuel evalSt with
  | @unit t e =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_unit] at hok
    have hv : interp_v = .unit := (congrArg Prod.fst (Except.ok.inj hok)).symm
    subst hv
    refine ⟨#[], st₀, ?_, by unfold flattenValue; rfl⟩
    unfold toIndex; exact compileM_pure_run st₀ #[]
  | @var t e l =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_var] at hok
    refine ⟨bindings[l]?.getD #[], st₀, ?_, ?_⟩
    · unfold toIndex; exact compileM_pure_run st₀ _
    · -- Extract the binding from find?
      generalize hfind : env.find? (fun x => x.1 == l) = found at hok
      match found, hfind, hok with
      | some (nm, vl), hfind, hok =>
        have heq := Except.ok.inj hok
        have hvl : vl = interp_v := congrArg Prod.fst heq
        subst hvl
        have hmem := List.mem_of_find?_eq_some hfind
        have hpred := List.find?_some hfind
        change (nm == l) = true at hpred
        have hnml : nm = l := eq_of_beq hpred
        subst hnml
        obtain ⟨idxs, hlook, hsz⟩ := hinv nm vl hmem
        simp only [hlook, Option.getD_some]
        exact hsz
  | @field t e g =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_field] at hok
    have hv : interp_v = .field g := (congrArg Prod.fst (Except.ok.inj hok)).symm
    subst hv
    refine ⟨Array.range' st₀.valIdx 1,
            { st₀ with valIdx := st₀.valIdx + 1,
                       ops := st₀.ops.push (.const g),
                       degrees := pushOpDegree st₀.degrees (.const g) 1 },
            ?_, ?_⟩
    · unfold toIndex; exact pushOp_run st₀ (.const g) 1
    · unfold flattenValue; simp
  | @ref t e g hlayout =>
    intro interp_v hinterp
    exact toIndex_preservation_ref_arm sourceDecls concDecls funcIdx
      layoutMap bindings t e g env fuel st₀ evalSt hlayout interp_v hinterp
      (hRefCompat (t' := t) (e' := e) (g := g) (IsCore.ref hlayout))
  | @letVar t e l v b hv hb ihv ihb =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_v : Concrete.Eval.interp concDecls fuel env v evalSt = res_v at hok
    match res_v, heval_v, hok with
    | .ok (val, st'), heval_v, hok =>
      simp only [] at hok
      have hinterp_v : (Concrete.Eval.interp concDecls fuel env v evalSt).toOption.map Prod.fst
          = some val := by rw [heval_v]; simp [Except.toOption, Option.map]
      -- Prepare SSA-fresh hypothesis for the inner recursive calls.
      -- Both `v` and `b` are subterms of `.letVar t e l v b`; for IH calls we
      -- need SSA-fresh on sub-letVars in those subterms w.r.t. their env.
      have hSsaFresh_v : ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local}
          {v'' b'' : Concrete.Term},
          IsCore layoutMap (.letVar t'' e'' l'' v'' b'') → ∀ w, (l'', w) ∉ env :=
        fun hc w => hSsaFresh hc w
      obtain ⟨idxs_v, st₁, hrun_v, hsz_v⟩ :=
        ihv (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh_v val hinterp_v
      -- Freshness of `l` in `env` — derived from the outer `hSsaFresh` applied
      -- to the current `.letVar t e l v b` (which `hcore` witnesses is `IsCore`).
      have hfresh : ∀ w, (l, w) ∉ env :=
        hSsaFresh (t' := t) (e' := e) (l' := l) (v' := v) (b' := b)
          (IsCore.letVar hv hb)
      have hinv' := sizeInv_insert sourceDecls funcIdx env bindings l val idxs_v hinv hsz_v hfresh
      -- Get interp result for body
      have hinterp_b : (Concrete.Eval.interp concDecls fuel ((l, val) :: env) b st').toOption.map Prod.fst
          = some interp_v := by
        rw [hok]; exact Concrete.Eval.interp_toOption_intro
      -- SSA-fresh for body's subterms via the hoisted `letVar_SSA_extension_inherits`.
      have hSsaFresh_b : ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local}
          {v'' b'' : Concrete.Term},
          IsCore layoutMap (.letVar t'' e'' l'' v'' b'') →
          ∀ w, (l'', w) ∉ ((l, val) :: env) :=
        letVar_SSA_extension_inherits layoutMap t e l v b val env
          (fun {_ _ _ _ _} hc w => hSsaFresh hc w)
          (IsCore.letVar hv hb)
          (hBinderNeq (t' := t) (e' := e) (l' := l) (v' := v) (b' := b)
            (IsCore.letVar hv hb))
      obtain ⟨idxs_b, st₂, hrun_b, hsz_b⟩ :=
        ihb (bindings := bindings.insert l idxs_v) (st₀ := st₁) (env := (l, val) :: env)
            (fuel := fuel) (evalSt := st') hinv' hSsaFresh_b interp_v hinterp_b
      refine ⟨idxs_b, st₂, ?_, hsz_b⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ _ st₁ hrun_v]
      exact hrun_b
  | @letWild t e v b _hv _hb ihv ihb =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_v : Concrete.Eval.interp concDecls fuel env v evalSt = res_v at hok
    match res_v, heval_v, hok with
    | .ok (val, st'), heval_v, hok =>
      simp only [] at hok
      have hinterp_v : (Concrete.Eval.interp concDecls fuel env v evalSt).toOption.map Prod.fst
          = some val := by rw [heval_v]; simp [Except.toOption, Option.map]
      obtain ⟨idxs_v, st₁, hrun_v, _⟩ :=
        ihv (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel) (evalSt := evalSt) hinv hSsaFresh val hinterp_v
      have hinterp_b : (Concrete.Eval.interp concDecls fuel env b st').toOption.map Prod.fst
          = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
      obtain ⟨idxs_b, st₂, hrun_b, hsz_b⟩ :=
        ihb (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel) (evalSt := st') hinv hSsaFresh interp_v hinterp_b
      refine ⟨idxs_b, st₂, ?_, hsz_b⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ _ st₁ hrun_v]
      exact hrun_b
  | @ptrVal t e a _ha iha =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (.pointer w i, st'), heval_a, hok =>
      simp only [] at hok
      have hval : interp_v = .field (G.ofNat i) := (congrArg Prod.fst (Except.ok.inj hok)).symm
      subst hval
      have hinterp_a : (Concrete.Eval.interp concDecls fuel env a evalSt).toOption.map Prod.fst
          = some (.pointer w i) := by rw [heval_a]; simp [Except.toOption, Option.map]
      obtain ⟨idxs, st₁, hrun, hsz⟩ :=
        iha (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel) (evalSt := evalSt) hinv hSsaFresh _ hinterp_a
      refine ⟨idxs, st₁, ?_, ?_⟩
      · unfold toIndex; exact hrun
      · rw [hsz]; unfold flattenValue; simp
  | @assertEq t e a b r _ha _hb _hr iha ihb ihr =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        -- Split on v1 != v2
        split at hok
        · exact absurd hok (by intro h; cases h)
        · -- v1 == v2, so interp r in st2
          have hinterp_a := Concrete.Eval.interp_toOption_intro (v := v1) (st := st1)
          rw [← heval_a] at hinterp_a
          obtain ⟨idxs_a, st₁, hrun_a, _⟩ :=
            iha (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel) (evalSt := evalSt)
                hinv hSsaFresh v1 hinterp_a
          have hinterp_b := Concrete.Eval.interp_toOption_intro (v := v2) (st := st2)
          rw [← heval_b] at hinterp_b
          obtain ⟨idxs_b, st₂, hrun_b, _⟩ :=
            ihb (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel) (evalSt := st1)
                hinv hSsaFresh v2 hinterp_b
          have hinterp_r : (Concrete.Eval.interp concDecls fuel env r st2).toOption.map Prod.fst
              = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
          let st₃ : CompilerState := { st₂ with ops := st₂.ops.push (.assertEq idxs_a idxs_b) }
          have hmod := compileM_modify_run st₂
            (fun stt : CompilerState => { stt with ops := stt.ops.push (.assertEq idxs_a idxs_b) })
          obtain ⟨idxs_r, st₄, hrun_r, hsz_r⟩ :=
            ihr (bindings := bindings) (st₀ := st₃) (env := env) (fuel := fuel) (evalSt := st2)
                hinv hSsaFresh interp_v hinterp_r
          refine ⟨idxs_r, st₄, ?_, hsz_r⟩
          unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hrun_a]
          rw [compileM_bind_ok st₁ _ _ st₂ hrun_b]
          rw [compileM_bind_ok st₂ _ _ st₃ hmod]
          exact hrun_r
  | @debug t e label tOpt r hrecT _hrecR ihtOpt ihr =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    have hinterp_r : (Concrete.Eval.interp concDecls fuel env r evalSt).toOption.map Prod.fst
        = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
    cases htOpt : tOpt with
    | none =>
      let st₁ : CompilerState := { st₀ with ops := st₀.ops.push (.debug label none) }
      have hmod := compileM_modify_run st₀
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label none) })
      obtain ⟨idxs_r, st₂, hrun_r, hsz_r⟩ :=
        ihr (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel) (evalSt := evalSt)
            hinv hSsaFresh interp_v hinterp_r
      refine ⟨idxs_r, st₂, ?_, hsz_r⟩
      unfold toIndex
      have hpure : ((pure none : CompileM (Option (Array Bytecode.ValIdx)))).run st₀ = .ok none st₀ :=
        compileM_pure_run st₀ none
      rw [compileM_bind_ok st₀ (pure none) none st₀ hpure]
      rw [compileM_bind_ok st₀ _ () st₁ hmod]
      exact hrun_r
    | some sub =>
      have hcoreSub := hrecT sub htOpt
      obtain ⟨idxs_t, st₁, ht⟩ := toIndex_progress_core layoutMap bindings sub st₀ hcoreSub
      let st₂ : CompilerState := { st₁ with ops := st₁.ops.push (.debug label (some idxs_t)) }
      have hmod := compileM_modify_run st₁
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label (some idxs_t)) })
      obtain ⟨idxs_r, st₃, hrun_r, hsz_r⟩ :=
        ihr (bindings := bindings) (st₀ := st₂) (env := env) (fuel := fuel) (evalSt := evalSt)
            hinv hSsaFresh interp_v hinterp_r
      refine ⟨idxs_r, st₃, ?_, hsz_r⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ idxs_t st₁ ht]
      rw [compileM_bind_ok st₁ _ (some idxs_t) st₁ (compileM_pure_run st₁ (some idxs_t))]
      rw [compileM_bind_ok st₁ _ () st₂ hmod]
      exact hrun_r

/-! ## Extension scaffolds for the full `Concrete.Term` shape.

`IsCoreExtended` (in `LowerShared.lean`) carves the `toIndex`-valid subset
covering every `Concrete.Term` constructor `toIndex` may legitimately see
(everything except `.ret` and `.match`, both of which throw). The two lemmas
below mirror the `core` lemmas at the extended predicate and feed the
block-level `Term.compile` proofs in `LowerSoundControl`.

Both are currently sorried with a per-arm BLOCKED breakdown. Each arm's
proof obligation is independently resolvable — see the per-arm notes
inside the sorry body. The `core` arms are inherited via
`IsCore.toExtended` + `toIndex_progress_core`/`toIndex_preservation_core`. -/

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

/-- The `do`-block fragment `let len ← match typSize lm typ with | .error e =>
throw e | .ok n => pure n; cont len` reduces to `cont n` whenever
`typSize lm typ = .ok n`. Used to discharge the `.proj`/`.get`/`.slice`/
`.set` / `.load` arms uniformly — the `match typSize`-on-`Typ` branch shows
up under a `__do_jp` continuation that `simp only [hsize]` doesn't always
close on its own. -/
private theorem compileM_typSize_match_run
    {α : Type} {layoutMap : LayoutMap} {typ : Concrete.Typ} {n : Nat}
    (htyp : typSize layoutMap typ = .ok n)
    (cont : Nat → CompileM α)
    (st₀ : CompilerState) :
    ((do let len ← match typSize layoutMap typ with
          | .error e => throw e
          | .ok len => pure len
         cont len) : CompileM α).run st₀ =
      (cont n).run st₀ := by
  simp only [htyp]
  rfl

/-- Membership transport: every `τ` in `typs.extract 0 i` is in `typs`. -/
private theorem mem_typs_of_mem_extract_prefix
    {typs : Array Concrete.Typ} {i : Nat} {typ : Concrete.Typ}
    (hmem : typ ∈ (typs.extract 0 i).toList) : typ ∈ typs.toList := by
  have hmem_arr : typ ∈ typs.extract 0 i := Array.mem_toList_iff.mp hmem
  rw [Array.mem_iff_getElem] at hmem_arr
  obtain ⟨j, hj, hget⟩ := hmem_arr
  have hsz : (typs.extract 0 i).size = min i typs.size := by
    simp [Array.size_extract]
  have hjsz : j < min i typs.size := hsz ▸ hj
  have hjs : j < typs.size := Nat.lt_of_lt_of_le hjsz (Nat.min_le_right _ _)
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  refine ⟨j, hjs, ?_⟩
  simp only [Array.getElem_extract, Nat.zero_add] at hget
  exact hget

/-- CompileM-side fold-progress for the offset computation inside `.proj`.
Every step is pure (state-unchanged): `match typSize` → `.ok len` → `pure (len + x)`.
The body shape matches the `__do_jp`-desugaring produced by Lean for the
do-block inside `toIndex`'s `.proj` arm — using Lean's auto-inferred binder
names `x`/`y` so `rw` aligns without alpha-renaming. -/
private theorem proj_offset_compileM_fold_ok_aux
    {layoutMap : LayoutMap}
    (xs : List Concrete.Typ)
    (hxs_typ : ∀ τ ∈ xs, ∃ k, typSize layoutMap τ = .ok k)
    (init : Nat) (st : CompilerState) :
    ∃ offset, (xs.foldlM (init := init)
      (fun x y =>
        match typSize layoutMap y with
        | .error e => do let y ← throw e; pure (y + x)
        | .ok len => do let y ← pure len; pure (y + x)) : CompileM Nat).run st
      = .ok offset st := by
  induction xs generalizing init st with
  | nil =>
    refine ⟨init, ?_⟩
    simp [List.foldlM_nil, pure, EStateM.pure, EStateM.run]
  | cons x rest ih =>
    obtain ⟨k, hk⟩ := hxs_typ x (List.mem_cons_self)
    have hrest : ∀ τ ∈ rest, ∃ k, typSize layoutMap τ = .ok k :=
      fun τ hτ => hxs_typ τ (List.mem_cons_of_mem _ hτ)
    obtain ⟨offset', hoffset'⟩ := ih hrest (k + init) st
    refine ⟨offset', ?_⟩
    simp only [List.foldlM_cons, hk]
    have hstep : ((do let y ← (pure k : CompileM Nat); pure (y + init))
        : CompileM Nat).run st = .ok (k + init) st := by
      simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [compileM_bind_ok st _ (k + init) st hstep]
    exact hoffset'

private theorem proj_offset_compileM_fold_ok
    {layoutMap : LayoutMap} (typs : Array Concrete.Typ) (i : Nat)
    (htyp : ∀ τ ∈ typs.toList, ∃ k, typSize layoutMap τ = .ok k)
    (st : CompilerState) :
    ∃ offset, ((typs.extract 0 i).foldlM (init := (0 : Nat))
      (fun x y =>
        match typSize layoutMap y with
        | .error e => do let y ← throw e; pure (y + x)
        | .ok len => do let y ← pure len; pure (y + x)) : CompileM Nat).run st
      = .ok offset st := by
  rw [← Array.foldlM_toList]
  apply proj_offset_compileM_fold_ok_aux
  intro τ hτ
  exact htyp τ (mem_typs_of_mem_extract_prefix hτ)

/-- CompileM-side fold-progress for the body of `.tuple`/`.array`.
Given that every `t ∈ ts` lowers successfully, the accumulator-append fold
also succeeds. -/
private theorem tuple_array_fold_ok_aux
    {layoutMap : LayoutMap}
    {bindings : Std.HashMap Local (Array Bytecode.ValIdx)}
    (xs : List Concrete.Term)
    (hxs : ∀ t ∈ xs, ∀ st, ∃ idxs st',
      (toIndex layoutMap bindings t).run st = .ok idxs st')
    (init : Array Bytecode.ValIdx) (st : CompilerState) :
    ∃ idxs st', (xs.foldlM (init := init)
      (fun acc arg => do
        pure (acc ++ (← toIndex layoutMap bindings arg))) : CompileM _).run st
      = .ok idxs st' := by
  induction xs generalizing init st with
  | nil =>
    refine ⟨init, st, ?_⟩
    simp [List.foldlM_nil, pure, EStateM.pure, EStateM.run]
  | cons x rest ih =>
    obtain ⟨idxs_x, st₁, hx⟩ := hxs x List.mem_cons_self st
    have hrest : ∀ t ∈ rest, ∀ st, ∃ idxs st',
        (toIndex layoutMap bindings t).run st = .ok idxs st' :=
      fun t ht st => hxs t (List.mem_cons_of_mem _ ht) st
    obtain ⟨idxs', st', hrest_run⟩ := ih hrest (init ++ idxs_x) st₁
    refine ⟨idxs', st', ?_⟩
    simp only [List.foldlM_cons]
    have hstep : ((do let y ← toIndex layoutMap bindings x; pure (init ++ y))
        : CompileM _).run st = .ok (init ++ idxs_x) st₁ := by
      rw [compileM_bind_ok st _ _ st₁ hx]
      exact compileM_pure_run st₁ _
    rw [compileM_bind_ok st _ _ st₁ hstep]
    exact hrest_run

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

/-- Progress for the FULL `toIndex`-valid subset. Mirrors
`toIndex_progress_core` with `IsCoreExtended` in place of `IsCore`.

Per-arm closure status:
- inherited core arms (`.unit`/`.var`/`.field`/`.ref`/`.letVar`/`.letWild`/
  `.ptrVal`/`.assertEq`/`.debug`) — **F=0** (closed in this session,
  replaying core arms with extended IH).
- `.letLoad` — **F=0** (closed; uses carried `typSize lm dstTyp = .ok n`).
- `.store` — **F=0** (closed; IH on `a` + `pushOp (.store args)`).
- `.ioGetInfo` — **F=0** (closed; IH on `k` + `pushOp .ioGetInfo`).
- `.ioWrite` — **F=0** (closed; IH on `data`/`ret` + modify).
- `.tuple` / `.array` — **F=0** (closed; `tuple_array_fold_ok_aux` over
  list induction).
- `.get` / `.slice` / `.set` — **F=0** (closed; `compileM_typSize_match_run`
  helper resolves the inner `match typSize` chain).
- `.proj` — **F=0** (closed; via `proj_offset_compileM_fold_ok_aux`
  + explicit `change` to convert do-notation to `>>=`-form bind chain
  + per-position `typs[i]?.getD .unit` size lookup).
- `.add` / `.sub` / `.mul` / `.eqZero` — **F=0** (closed; `WidthOne`
  carriers + `expectIdx_run_of_widthOne` helper).
- `.load` — **F=0** (closed; `WidthOne` carrier + carried `typSize`).
- `.app` — **F=0** (closed; `buildArgs_fold_ok_aux` over `args.attach`).
- `.ioSetInfo` / `.ioRead` — **F=0** (closed via `WidthOne` carriers).
- u8/u32 ops (10 arms) — **F=0** (closed via `WidthOne` carriers).

All arms F=0. -/
theorem toIndex_progress_core_extended
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Concrete.Term) (st₀ : CompilerState)
    (h : IsCoreExtended layoutMap term) :
    ∃ idxs st, (toIndex layoutMap bindings term).run st₀ = .ok idxs st := by
  induction h generalizing bindings st₀ with
  | unit => exact toIndex_progress_core layoutMap bindings _ st₀ .unit
  | var => exact toIndex_progress_core layoutMap bindings _ st₀ .var
  | field => exact toIndex_progress_core layoutMap bindings _ st₀ .field
  | ref hl => exact toIndex_progress_core layoutMap bindings _ st₀ (.ref hl)
  | letVar _ _ ihv ihb =>
    -- IsCoreExtended on subterms; can't directly call core. Inline the
    -- letVar arm body using IH at extended level.
    obtain ⟨idxs_v, st₁, hv⟩ := ihv bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hv]
    exact ihb _ st₁
  | letWild _ _ ihv ihb =>
    obtain ⟨idxs_v, st₁, hv⟩ := ihv bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hv]
    exact ihb bindings st₁
  | ptrVal _ ih =>
    unfold toIndex
    exact ih bindings st₀
  | assertEq _ _ _ ihA ihB ihR =>
    obtain ⟨idxs_a, st₁, ha⟩ := ihA bindings st₀
    obtain ⟨idxs_b, st₂, hb⟩ := ihB bindings st₁
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    rw [compileM_bind_ok st₁ _ _ st₂ hb]
    let st₃ : CompilerState :=
      { st₂ with ops := st₂.ops.push (.assertEq idxs_a idxs_b) }
    have hmod := compileM_modify_run st₂
      (fun stt : CompilerState => { stt with ops := stt.ops.push (.assertEq idxs_a idxs_b) })
    rw [compileM_bind_ok st₂ _ _ st₃ hmod]
    exact ihR bindings st₃
  | @debug t e label tOpt r htOpt _hr ihtOpt ihr =>
    cases htOpt' : tOpt with
    | none =>
      let st₁ : CompilerState :=
        { st₀ with ops := st₀.ops.push (.debug label none) }
      obtain ⟨idxs_r, st₂, hr⟩ := ihr bindings st₁
      refine ⟨idxs_r, st₂, ?_⟩
      have hmod := compileM_modify_run st₀
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label none) })
      unfold toIndex
      have hpure : ((pure none : CompileM (Option (Array Bytecode.ValIdx)))).run st₀ = .ok none st₀ :=
        compileM_pure_run st₀ (none : Option (Array Bytecode.ValIdx))
      rw [compileM_bind_ok st₀ (pure (none : Option (Array Bytecode.ValIdx))) none st₀ hpure]
      rw [compileM_bind_ok st₀ _ () st₁ hmod]
      exact hr
    | some sub =>
      obtain ⟨idxs_t, st₁, ht⟩ := ihtOpt sub htOpt' bindings st₀
      let st₂ : CompilerState :=
        { st₁ with ops := st₁.ops.push (.debug label (some idxs_t)) }
      obtain ⟨idxs_r, st₃, hr⟩ := ihr bindings st₂
      refine ⟨idxs_r, st₃, ?_⟩
      have hmod := compileM_modify_run st₁
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label (some idxs_t)) })
      unfold toIndex
      rw [compileM_bind_ok st₀ _ idxs_t st₁ ht]
      rw [compileM_bind_ok st₁ _ (some idxs_t) st₁ (compileM_pure_run st₁ (some idxs_t))]
      rw [compileM_bind_ok st₁ _ () st₂ hmod]
      exact hr
  | @tuple t e ts _hts ihts =>
    unfold toIndex
    rw [← Array.foldlM_toList]
    apply tuple_array_fold_ok_aux
    intro x hx st
    exact ihts x (Array.mem_toList_iff.mp hx) bindings st
  | @array t e ts _hts ihts =>
    unfold toIndex
    rw [← Array.foldlM_toList]
    apply tuple_array_fold_ok_aux
    intro x hx st
    exact ihts x (Array.mem_toList_iff.mp hx) bindings st
  | @letLoad t e dst dstTyp src bod hsz _hbod ihbod =>
    obtain ⟨n, hsize⟩ := hsz
    unfold toIndex
    -- Reduce the `match typSize`-case under `hsize`.
    simp only [hsize]
    let ptrIdxs := bindings[src]?.getD #[0]
    let loadOp : Bytecode.Op := .load n ptrIdxs[0]!
    let st₁ : CompilerState :=
      { st₀ with valIdx := st₀.valIdx + n,
                 ops := st₀.ops.push loadOp,
                 degrees := pushOpDegree st₀.degrees loadOp n }
    have hpush : (pushOp loadOp n : CompileM _).run st₀ = .ok (Array.range' st₀.valIdx n) st₁ :=
      pushOp_run st₀ loadOp n
    have hpure : (pure n : CompileM Nat).run st₀ = .ok n st₀ := compileM_pure_run st₀ n
    rw [compileM_bind_ok st₀ (pure n) n st₀ hpure]
    rw [compileM_bind_ok st₀ _ _ st₁ hpush]
    exact ihbod (bindings.insert dst (Array.range' st₀.valIdx n)) st₁
  | @proj t e a i _iha htyp ihA =>
    obtain ⟨typs, hatyp, htypsizes⟩ := htyp
    obtain ⟨idxs_a, st₁, ha⟩ := ihA bindings st₀
    unfold toIndex
    simp only [hatyp]
    rw [compileM_bind_ok st₀ _ typs st₀ (compileM_pure_run st₀ typs)]
    -- The offset fold: `(typs.extract 0 i).foldlM ... 0` after `Array.foldlM_toList`.
    rw [← Array.foldlM_toList]
    -- Resolve the offset fold via helper lemma's result.
    obtain ⟨offset, hoffset⟩ :=
      proj_offset_compileM_fold_ok_aux (layoutMap := layoutMap)
        (typs.extract 0 i).toList
        (fun τ hτ => htypsizes τ (mem_typs_of_mem_extract_prefix hτ)) 0 st₀
    -- Compute hith so the second match resolves.
    have hith : ∃ k, typSize layoutMap (typs[i]?.getD .unit) = .ok k := by
      cases hi : typs[i]? with
      | none =>
        refine ⟨0, ?_⟩
        simp only [Option.getD]
        unfold typSize
        rfl
      | some τ =>
        have hmem : τ ∈ typs.toList := by
          rw [Array.mem_toList_iff, Array.mem_iff_getElem]
          have hh := Array.getElem?_eq_some_iff.mp hi
          exact ⟨i, hh.1, hh.2⟩
        simp only [Option.getD]
        exact htypsizes τ hmem
    obtain ⟨iLen, hiLen⟩ := hith
    refine ⟨idxs_a.extract offset (offset + iLen), st₁, ?_⟩
    -- After `unfold toIndex` + `simp [hatyp]` + `compileM_bind_ok` for
    -- `pure typs`, the remaining goal uses `do let offset ← ...` which
    -- elaborates to `Bind.bind` directly (NOT `>>=`). Convert via `change`.
    change ((List.foldlM
        (fun (x : Nat) (y : Concrete.Typ) =>
          match typSize layoutMap y with
          | Except.error e => do let y ← throw e; pure (y + x)
          | Except.ok len => do let y ← pure len; pure (y + x))
        0 (typs.extract 0 i).toList : CompileM Nat) >>= fun offset => do
        let arg ← toIndex layoutMap bindings a
        match typSize layoutMap (typs[i]?.getD .unit) with
        | Except.error e => do let y ← throw e; pure (arg.extract offset (offset + y))
        | Except.ok len => do let y ← pure len; pure (arg.extract offset (offset + y))).run
        st₀ = _
    rw [compileM_bind_ok st₀ _ offset st₀ hoffset]
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    simp only [hiLen]
    rw [compileM_bind_ok st₁ _ iLen st₁ (compileM_pure_run st₁ iLen)]
    exact compileM_pure_run st₁ _
  | @get t e a n _iha htyp ihA =>
    obtain ⟨τ, k, hτ, m, hsize⟩ := htyp
    obtain ⟨idxs_a, st₁, ha⟩ := ihA bindings st₀
    unfold toIndex
    simp only [hτ]
    rw [compileM_bind_ok st₀ _ τ st₀ (compileM_pure_run st₀ τ)]
    simp only [hsize]
    rw [compileM_bind_ok st₀ _ m st₀ (compileM_pure_run st₀ m)]
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    exact ⟨_, _, compileM_pure_run st₁ _⟩
  | @slice t e a i j _iha htyp ihA =>
    obtain ⟨τ, k, hτ, m, hsize⟩ := htyp
    obtain ⟨idxs_a, st₁, ha⟩ := ihA bindings st₀
    unfold toIndex
    simp only [hτ]
    rw [compileM_bind_ok st₀ _ τ st₀ (compileM_pure_run st₀ τ)]
    simp only [hsize]
    rw [compileM_bind_ok st₀ _ m st₀ (compileM_pure_run st₀ m)]
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    exact ⟨_, _, compileM_pure_run st₁ _⟩
  | @set t e a n v _iha _ihv htyp ihA ihV =>
    obtain ⟨τ, k, hτ, m, hsize⟩ := htyp
    obtain ⟨idxs_a, st₁, ha⟩ := ihA bindings st₀
    obtain ⟨idxs_v, st₂, hv⟩ := ihV bindings st₁
    unfold toIndex
    simp only [hτ]
    rw [compileM_bind_ok st₀ _ τ st₀ (compileM_pure_run st₀ τ)]
    simp only [hsize]
    rw [compileM_bind_ok st₀ _ m st₀ (compileM_pure_run st₀ m)]
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    rw [compileM_bind_ok st₁ _ _ st₂ hv]
    exact ⟨_, _, compileM_pure_run st₂ _⟩
  | store _ ih =>
    obtain ⟨idxs_a, st₁, ha⟩ := ih bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ ha]
    exact ⟨_, _, pushOp_run st₁ (.store idxs_a) 1⟩
  | @load t e a _iha hwa htyp _ihA =>
    obtain ⟨τ, hτ, n, hsize⟩ := htyp
    unfold toIndex
    simp only [hτ, hsize]
    obtain ⟨i, st₁, hexp⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    rw [compileM_bind_ok st₀ _ n st₀ (compileM_pure_run st₀ n)]
    rw [compileM_bind_ok st₀ _ _ st₁ hexp]
    exact ⟨_, _, pushOp_run st₁ (.load n i) n⟩
  | @app t e g args u hl _hargs ihargs =>
    have hbuild_step : ∀ t ∈ args.attach.map (·.1), ∀ st, ∃ idxs st',
        (toIndex layoutMap bindings t).run st = .ok idxs st' := by
      intro t ht st
      rw [List.mem_map] at ht
      obtain ⟨⟨a, ha⟩, _, heq⟩ := ht
      subst heq
      exact ihargs a ha bindings st
    unfold toIndex
    rcases hl with ⟨fl, hfl⟩ | ⟨cl, hcl⟩
    · -- Function branch
      rw [hfl]
      simp only []
      -- buildArgs unfolds to args.attach.foldlM
      unfold buildArgs
      obtain ⟨bargs, st₁, hbuild⟩ :=
        buildArgs_fold_ok_aux (P := fun a => a ∈ args)
          args.attach hbuild_step #[] st₀
      rw [compileM_bind_ok st₀ _ _ st₁ hbuild]
      exact ⟨_, _, pushOp_run st₁ (.call fl.index bargs fl.outputSize u) fl.outputSize⟩
    · -- Constructor branch
      rw [hcl]
      simp only []
      let paddingOp : Bytecode.Op := .const (.ofNat cl.index)
      let st₁ : CompilerState :=
        { st₀ with valIdx := st₀.valIdx + 1,
                   ops := st₀.ops.push paddingOp,
                   degrees := pushOpDegree st₀.degrees paddingOp 1 }
      have hpush₁ : (pushOp paddingOp 1 : CompileM _).run st₀ = .ok (Array.range' st₀.valIdx 1) st₁ :=
        pushOp_run st₀ paddingOp 1
      rw [compileM_bind_ok st₀ _ _ st₁ hpush₁]
      unfold buildArgs
      obtain ⟨bargs, st₂, hbuild⟩ :=
        buildArgs_fold_ok_aux (P := fun a => a ∈ args)
          args.attach hbuild_step (Array.range' st₀.valIdx 1) st₁
      rw [compileM_bind_ok st₁ _ _ st₂ hbuild]
      by_cases hsz : bargs.size < cl.size
      · simp only [hsz, if_true]
        let padOp : Bytecode.Op := .const (.ofNat 0)
        let st₃ : CompilerState :=
          { st₂ with valIdx := st₂.valIdx + 1,
                     ops := st₂.ops.push padOp,
                     degrees := pushOpDegree st₂.degrees padOp 1 }
        have hpush₂ : (pushOp padOp 1 : CompileM _).run st₂ = .ok (Array.range' st₂.valIdx 1) st₃ :=
          pushOp_run st₂ padOp 1
        rw [compileM_bind_ok st₂ _ _ st₃ hpush₂]
        exact ⟨_, _, compileM_pure_run st₃ _⟩
      · simp only [hsz, if_false]
        exact ⟨_, _, compileM_pure_run st₂ _⟩
  | @add t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.add ia ib) 1⟩
  | @sub t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.sub ia ib) 1⟩
  | @mul t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.mul ia ib) 1⟩
  | @eqZero t e a _iha hwa _ihA =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    exact ⟨_, _, pushOp_run st₁ (.eqZero ia) 1⟩
  | ioGetInfo _ ih =>
    obtain ⟨idxs_k, st₁, hk⟩ := ih bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hk]
    exact ⟨_, _, pushOp_run st₁ (.ioGetInfo idxs_k) 2⟩
  | @ioSetInfo t e k i l r _ihK _ihI _ihL _ihR hwI hwL ihK _ihI' _ihL' ihR =>
    obtain ⟨idxs_k, st₁, hk⟩ := ihK bindings st₀
    obtain ⟨ii, st₂, hexpI⟩ := expectIdx_run_of_widthOne layoutMap bindings i st₁ hwI
    obtain ⟨il, st₃, hexpL⟩ := expectIdx_run_of_widthOne layoutMap bindings l st₂ hwL
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hk]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpI]
    rw [compileM_bind_ok st₂ _ _ st₃ hexpL]
    let st₄ : CompilerState :=
      { st₃ with ops := st₃.ops.push (.ioSetInfo idxs_k ii il) }
    have hmod := compileM_modify_run st₃
      (fun stt : CompilerState => { stt with ops := stt.ops.push (.ioSetInfo idxs_k ii il) })
    rw [compileM_bind_ok st₃ _ () st₄ hmod]
    exact ihR bindings st₄
  | @ioRead t e i n _ihI hwI _ihI' =>
    obtain ⟨ii, st₁, hexpI⟩ := expectIdx_run_of_widthOne layoutMap bindings i st₀ hwI
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpI]
    exact ⟨_, _, pushOp_run st₁ (.ioRead ii n) n⟩
  | ioWrite _ _ ihD ihR =>
    obtain ⟨idxs_d, st₁, hd⟩ := ihD bindings st₀
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hd]
    let st₂ : CompilerState :=
      { st₁ with ops := st₁.ops.push (.ioWrite idxs_d) }
    have hmod := compileM_modify_run st₁
      (fun stt : CompilerState => { stt with ops := stt.ops.push (.ioWrite idxs_d) })
    rw [compileM_bind_ok st₁ _ () st₂ hmod]
    exact ihR bindings st₂
  | @u8BitDecomposition t e a _iha hwa _ihA =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    exact ⟨_, _, pushOp_run st₁ (.u8BitDecomposition ia) 8⟩
  | @u8ShiftLeft t e a _iha hwa _ihA =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    exact ⟨_, _, pushOp_run st₁ (.u8ShiftLeft ia) 1⟩
  | @u8ShiftRight t e a _iha hwa _ihA =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    exact ⟨_, _, pushOp_run st₁ (.u8ShiftRight ia) 1⟩
  | @u8Xor t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8Xor ia ib) 1⟩
  | @u8Add t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8Add ia ib) 2⟩
  | @u8Sub t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8Sub ia ib) 2⟩
  | @u8And t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8And ia ib) 1⟩
  | @u8Or t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8Or ia ib) 1⟩
  | @u8LessThan t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u8LessThan ia ib) 1⟩
  | @u32LessThan t e a b _iha _ihb hwa hwb _ihA _ihB =>
    obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
    obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
    unfold toIndex
    rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
    rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
    exact ⟨_, _, pushOp_run st₂ (.u32LessThan ia ib) 1⟩

/-! ## Round 5 helpers: `flattenValue` size/structure lemmas. -/

/-- Distribute `flattenValue` width over `Array.attach.flatMap` for an
`#[v] ++ vs` split. Closes the cons step in the `.tuple`/`.array`
fold-preservation. -/
private theorem flattenValue_attach_flatMap_size_cons
    (sourceDecls : Source.Decls) (funcIdx : Global → Option Nat)
    (v : Value) (vs : Array Value) :
    ((#[v] ++ vs).attach.flatMap
      (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w)).size =
    (flattenValue sourceDecls funcIdx v).size +
      (vs.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w)).size := by
  -- Strategy: replace Array.attach with Array.attachWith using a constant predicate,
  -- then both sides have a `flatMap`-with-`Subtype.val`-projection structure.
  -- The key insight: the function `fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w`
  -- doesn't actually depend on the membership proof, so we can treat it as a
  -- composition `flattenValue ∘ Subtype.val` and use `Array.flatMap_attach_eq_flatMap`.
  have helper : ∀ (a : Array Value),
      a.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w) =
      a.flatMap (fun w => flattenValue sourceDecls funcIdx w) := by
    intro a
    apply Array.ext'
    simp [Array.toList_flatMap, Array.toList_attach,
          List.attachWith, List.attach, List.flatMap, List.pmap]
  -- After replacement, the goal becomes:
  --   ((#[v] ++ vs).flatMap flatten).size = (flatten v).size + (vs.flatMap flatten).size.
  rw [helper, helper]
  rw [show (#[v] ++ vs).flatMap (fun w => flattenValue sourceDecls funcIdx w) =
      flattenValue sourceDecls funcIdx v ++ vs.flatMap
        (fun w => flattenValue sourceDecls funcIdx w) from by
    apply Array.ext'
    simp [Array.toList_flatMap, List.flatMap_cons]]
  simp [Array.size_append]

/-- `flattenValue` size-distributivity for `Array.attach.flatMap` over a
list-built array. Used to compute the `.tuple`/`.array` fold size. -/
private theorem flattenValue_attach_flatMap_size_toArray
    (sourceDecls : Source.Decls) (funcIdx : Global → Option Nat)
    (l : List Value) :
    (l.toArray.attach.flatMap
      (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w)).size =
    (l.map (fun v => (flattenValue sourceDecls funcIdx v).size)).sum := by
  -- Direct induction on l. Each cons step uses
  -- `flattenValue_attach_flatMap_size_cons` (which is closed F=0).
  -- Strategy: prove the size equation by reducing both sides to Array form
  -- via plain (non-attach) flatMap. The non-attach equivalent is provable
  -- without motive issues.
  have helper : ∀ (a : Array Value),
      a.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w) =
      a.flatMap (fun w => flattenValue sourceDecls funcIdx w) := by
    intro a
    apply Array.ext'
    simp [Array.toList_flatMap, Array.toList_attach,
          List.attachWith, List.flatMap, List.pmap]
  rw [helper]
  -- Convert to .toList.length form.
  rw [show ∀ (a : Array G), a.size = a.toList.length from fun a => by simp]
  rw [Array.toList_flatMap]
  rw [show l.toArray.toList = l from by simp]
  -- Goal: (List.flatMap _ l).length = sum of map (.size) l.
  induction l with
  | nil => simp
  | cons h t ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    rw [show (flattenValue sourceDecls funcIdx h).toList.length
        = (flattenValue sourceDecls funcIdx h).size from by simp]
    simp [List.map_cons, List.sum_cons]

/-- Fold-preservation helper for `.tuple`/`.array`. Given `evalList ts`
yields per-element values (the `.tuple` interp dispatches to `evalList`
on `ts.toList`), the `toIndex` fold yields an array whose width equals
`(flattenValue (.tuple vs)).size`.

Inductive structure mirrors `tuple_array_fold_ok_aux`. The `hxs` callback
is specialized to a fixed outer `env`/`fuel` since `evalList` threads them
unchanged across elements; this lets the caller discharge `sizeInv` and
`hSsaFresh` for a single env-context. -/
private theorem tuple_array_fold_preservation
    {sourceDecls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    {layoutMap : LayoutMap}
    {bindings : Std.HashMap Local (Array Bytecode.ValIdx)}
    (env : Concrete.Eval.Bindings) (fuel : Nat)
    (xs : List Concrete.Term)
    (hxs : ∀ t ∈ xs, ∀ st₀ evalSt (interp_v : Value),
      (Concrete.Eval.interp concDecls fuel env t evalSt).toOption.map Prod.fst
        = some interp_v →
      ∃ idxs st',
        (toIndex layoutMap bindings t).run st₀ = .ok idxs st' ∧
        idxs.size = (flattenValue sourceDecls funcIdx interp_v).size)
    (evalSt : Concrete.Eval.EvalState)
    (vs : Array Value) (evalSt' : Concrete.Eval.EvalState)
    (heval : Concrete.Eval.evalList concDecls fuel env xs evalSt
      = .ok (vs, evalSt'))
    (init : Array Bytecode.ValIdx) (st₀ : CompilerState) :
    ∃ idxs st',
      (xs.foldlM (init := init)
        (fun acc arg => do
          pure (acc ++ (← toIndex layoutMap bindings arg))) : CompileM _).run st₀
        = .ok idxs st' ∧
      idxs.size = init.size +
        (vs.toList.map
          (fun v => (flattenValue sourceDecls funcIdx v).size)).sum := by
  induction xs generalizing init st₀ evalSt vs evalSt' with
  | nil =>
    -- vs = #[]
    simp only [Concrete.Eval.evalList] at heval
    have hpair : (#[], evalSt) = (vs, evalSt') := Except.ok.inj heval
    have hvs : vs = #[] := (congrArg Prod.fst hpair).symm
    subst hvs
    refine ⟨init, st₀, ?_, ?_⟩
    · simp [List.foldlM_nil, pure, EStateM.pure, EStateM.run]
    · simp
  | cons x rest ih =>
    simp only [Concrete.Eval.evalList] at heval
    generalize hinterp_x : Concrete.Eval.interp concDecls fuel env x evalSt = res_x at heval
    match res_x, hinterp_x, heval with
    | .ok (v_x, st_x), hinterp_x, heval =>
      simp only [] at heval
      generalize hres_rest : Concrete.Eval.evalList concDecls fuel env rest st_x = res_rest at heval
      match res_rest, hres_rest, heval with
      | .ok (vs_rest, st_rest), hres_rest, heval =>
        simp only [] at heval
        have hpair : (#[v_x] ++ vs_rest, st_rest) = (vs, evalSt') :=
          Except.ok.inj heval
        have hvs : vs = #[v_x] ++ vs_rest := (congrArg Prod.fst hpair).symm
        subst hvs
        have hinterp_v_x : (Concrete.Eval.interp concDecls fuel env x evalSt).toOption.map
            Prod.fst = some v_x := by
          rw [hinterp_x]; simp [Except.toOption, Option.map]
        obtain ⟨idxs_x, st₁, hrun_x, hsz_x⟩ :=
          hxs x List.mem_cons_self st₀ evalSt v_x hinterp_v_x
        have hxs_rest : ∀ t ∈ rest, ∀ st₀' evalSt' (interp_v' : Value),
            (Concrete.Eval.interp concDecls fuel env t evalSt').toOption.map Prod.fst
              = some interp_v' →
            ∃ idxs st'',
              (toIndex layoutMap bindings t).run st₀' = .ok idxs st'' ∧
              idxs.size = (flattenValue sourceDecls funcIdx interp_v').size :=
          fun t ht => hxs t (List.mem_cons_of_mem _ ht)
        obtain ⟨idxs_rest, st_final, hrest_run, hrest_sz⟩ :=
          ih hxs_rest st_x vs_rest st_rest hres_rest (init ++ idxs_x) st₁
        refine ⟨idxs_rest, st_final, ?_, ?_⟩
        · simp only [List.foldlM_cons]
          have hstep : ((do let y ← toIndex layoutMap bindings x; pure (init ++ y))
              : CompileM _).run st₀ = .ok (init ++ idxs_x) st₁ := by
            rw [compileM_bind_ok st₀ _ _ st₁ hrun_x]
            exact compileM_pure_run st₁ _
          rw [compileM_bind_ok st₀ _ _ st₁ hstep]
          exact hrest_run
        · -- Width.
          rw [hrest_sz]
          rw [Array.size_append]
          rw [hsz_x]
          -- (#[v_x] ++ vs_rest).toList = v_x :: vs_rest.toList.
          have htoList : (#[v_x] ++ vs_rest).toList = v_x :: vs_rest.toList := by
            simp
          rw [htoList]
          simp [List.map_cons, List.sum_cons]
          omega

/-- Width of `flattenValue (.array xs)` when each entry of `xs` is a `.field`.
For `xs.map .field`, width equals `xs.size`. Used by `.ioRead`. -/
private theorem flattenValue_array_map_field_size
    (sourceDecls : Source.Decls) (funcIdx : Global → Option Nat)
    (xs : Array G) :
    (flattenValue sourceDecls funcIdx (.array (xs.map Value.field))).size = xs.size := by
  unfold flattenValue
  rw [Array.size_flatMap]
  -- Strategy: rewrite using `Array.attach_map` to swap out attach over map,
  -- then `Array.map_map`, then point-wise simplify the inner function to 1.
  have hattach_map :
      (Array.map Value.field xs).attach.map
        (fun (v : { a : Value // a ∈ Array.map Value.field xs}) =>
          (flattenValue sourceDecls funcIdx v.val).size) =
      xs.attach.map (fun (_ : { a : G // a ∈ xs}) => 1) := by
    apply Array.ext (h₁ := by simp [Array.size_map, Array.size_attach])
    intro i hi₁ hi₂
    simp only [Array.getElem_map]
    have hi_xs : i < xs.size := by
      rw [Array.size_map, Array.size_attach] at hi₂
      exact hi₂
    -- LHS: flatten of field `xs[i]` = `#[xs[i]]`, size 1.
    have hattach_get : ((Array.map Value.field xs).attach[i]'(by
          rw [Array.size_attach, Array.size_map]; exact hi_xs)).val
        = Value.field (xs[i]'hi_xs) := by
      simp [Array.getElem_attach, Array.getElem_map]
    rw [hattach_get]
    show (flattenValue sourceDecls funcIdx (Value.field (xs[i]'hi_xs))).size = 1
    unfold flattenValue
    rfl
  rw [hattach_map]
  -- Goal: (xs.attach.map (fun _ => 1)).sum = xs.size.
  show (Array.map (fun (_ : { a : G // a ∈ xs}) => 1) xs.attach).sum = xs.size
  rw [← Array.sum_toList]
  rw [Array.toList_map, Array.toList_attach]
  -- Goal: (List.map (fun _ => 1) (xs.toList.attachWith (· ∈ xs) _)).sum = xs.size.
  show (List.map (fun (_ : { a : G // a ∈ xs}) => 1)
      (List.pmap Subtype.mk xs.toList (fun a ha => Array.mem_toList_iff.mp ha))).sum = xs.size
  rw [List.map_pmap]
  -- Goal: (List.pmap (fun a _ => 1) xs.toList _).sum = xs.size.
  have hsum : ∀ (l : List G) (h : ∀ a ∈ l, a ∈ xs),
      (List.pmap (fun (_ : G) (_ : _ ∈ xs) => 1) l h).sum = l.length := by
    intro l h
    induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.pmap, List.sum_cons]
      rw [ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
      simp [List.length]; omega
  rw [hsum]
  simp

/-- Preservation for the FULL `toIndex`-valid subset. Mirrors
`toIndex_preservation_core` with `IsCoreExtended` in place of `IsCore`.

**Round 6 closure status** (cumulative 30/37 arms F=0):
- 9 core arms (unit/var/field/ref/letVar/letWild/ptrVal/assertEq/debug) — F=0
- arithmetic (add/sub/mul/eqZero) — F=0 (round 4)
- u8/u32: 9 arms — F=0 (round 4)
- u8BitDecomposition — F=0 (round 5)
- IO: ioGetInfo/ioSetInfo/ioWrite — F=0 (round 4)
- IO: ioRead — F=0 (round 5; uses `flattenValue_array_map_field_size`)
- `.store` — F=0 (round 4)
- `.tuple`/`.array` — F=0 (round 6; `tuple_array_fold_preservation` helper
  with fixed-env `hxs` callback + `flattenValue` definitional unfold via
  `show ... = _; rw [flattenValue]` + `flattenValue_attach_flatMap_size_toArray`)
- 6 collection/access (letLoad/proj/get/slice/set/load) — F=1
  BLOCKED ON: typed-Value flat-size invariant + witness producer. The
  compiler-side `toIndex` produces an array of size `typSize layoutMap τ`
  (where `τ` is a sub-Typ), but the value-side `flattenValue` produces
  `(flattenValue v).size` for the projected/extracted/loaded value `v`.
  Bridging requires
  `ValueHasTyp concDecls τ v → (flattenValue v).size = typSize layoutMap τ`
  (LowerShared.lean `flattenValue_size_of_ValueHasTyp`; predicate
  strengthened per audit SD-A — no longer vacuous), plus an
  `interp_preserves_ValueHasTyp`-style witness producer threaded
  through `IsCoreExtended` carriers (the witness is the missing piece).
  This is ~300+ LoC of infrastructure.
- `.app` — F=1; deferred to Phase 4 (FnFreeBody / runFunction equivalence)

Helpers (all F=0):
- `flattenValue_array_map_field_size` — `(flatten (.array (xs.map .field))).size = xs.size`
- `flattenValue_attach_flatMap_size_cons` — append-cons distribution
- `flattenValue_attach_flatMap_size_toArray` — fold-size over `l.toArray.attach.flatMap`
- `tuple_array_fold_preservation` — fold-preservation for tuple/array
  (uses fixed-env `hxs` callback)

The `RefCompat` hypothesis on `.ref` arms generalizes to a
`AppCompat`-shape hypothesis for `.app`. -/
theorem toIndex_preservation_core_extended
    (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (layoutMap : LayoutMap) (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Concrete.Term) (env : Concrete.Eval.Bindings)
    (fuel : Nat) (st₀ : CompilerState) (evalSt : Concrete.Eval.EvalState)
    (hcore : IsCoreExtended layoutMap term)
    (hinv : sizeInv sourceDecls funcIdx env bindings)
    (hSsaFresh : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local}
        {v' b' : Concrete.Term},
      IsCoreExtended layoutMap (.letVar t' e' l' v' b') →
      ∀ w, (l', w) ∉ env)
    (_hBinderNeq : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local}
        {v' b' : Concrete.Term},
      IsCoreExtended layoutMap (.letVar t' e' l' v' b') →
      ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local}
        {v'' b'' : Concrete.Term},
      IsCoreExtended layoutMap (.letVar t'' e'' l'' v'' b'') →
      l'' ≠ l')
    (_hRefCompat : ∀ {t' : Concrete.Typ} {e' : Bool} {g : Global},
      IsCoreExtended layoutMap (.ref t' e' g) →
      RefCompat sourceDecls concDecls funcIdx layoutMap g) :
    ∀ (interp_v : Value),
      (Concrete.Eval.interp concDecls fuel env term evalSt).toOption.map Prod.fst
        = some interp_v →
      ∃ idxs st',
        (toIndex layoutMap bindings term).run st₀ = .ok idxs st' ∧
        idxs.size = (flattenValue sourceDecls funcIdx interp_v).size := by
  induction hcore generalizing bindings st₀ env fuel evalSt with
  | @unit t e =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_unit] at hok
    have hv : interp_v = .unit := (congrArg Prod.fst (Except.ok.inj hok)).symm
    subst hv
    refine ⟨#[], st₀, ?_, by unfold flattenValue; rfl⟩
    unfold toIndex; exact compileM_pure_run st₀ #[]
  | @var t e l =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_var] at hok
    refine ⟨bindings[l]?.getD #[], st₀, ?_, ?_⟩
    · unfold toIndex; exact compileM_pure_run st₀ _
    · generalize hfind : env.find? (fun x => x.1 == l) = found at hok
      match found, hfind, hok with
      | some (nm, vl), hfind, hok =>
        have heq := Except.ok.inj hok
        have hvl : vl = interp_v := congrArg Prod.fst heq
        subst hvl
        have hmem := List.mem_of_find?_eq_some hfind
        have hpred := List.find?_some hfind
        change (nm == l) = true at hpred
        have hnml : nm = l := eq_of_beq hpred
        subst hnml
        obtain ⟨idxs, hlook, hsz⟩ := hinv nm vl hmem
        simp only [hlook, Option.getD_some]
        exact hsz
  | @field t e g =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_field] at hok
    have hv : interp_v = .field g := (congrArg Prod.fst (Except.ok.inj hok)).symm
    subst hv
    refine ⟨Array.range' st₀.valIdx 1,
            { st₀ with valIdx := st₀.valIdx + 1,
                       ops := st₀.ops.push (.const g),
                       degrees := pushOpDegree st₀.degrees (.const g) 1 },
            ?_, ?_⟩
    · unfold toIndex; exact pushOp_run st₀ (.const g) 1
    · unfold flattenValue; simp
  | @ref t e g hlayout =>
    intro interp_v hinterp
    exact toIndex_preservation_ref_arm sourceDecls concDecls funcIdx
      layoutMap bindings t e g env fuel st₀ evalSt hlayout interp_v hinterp
      (_hRefCompat (t' := t) (e' := e) (g := g) (.ref hlayout))
  | @letVar t e l v b _hv _hb ihv ihb =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_v : Concrete.Eval.interp concDecls fuel env v evalSt = res_v at hok
    match res_v, heval_v, hok with
    | .ok (val, st'), heval_v, hok =>
      simp only [] at hok
      have hinterp_v : (Concrete.Eval.interp concDecls fuel env v evalSt).toOption.map Prod.fst
          = some val := by rw [heval_v]; simp [Except.toOption, Option.map]
      obtain ⟨idxs_v, st₁, hrun_v, hsz_v⟩ :=
        ihv (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh val hinterp_v
      have hfresh : ∀ w, (l, w) ∉ env :=
        hSsaFresh (t' := t) (e' := e) (l' := l) (v' := v) (b' := b)
          (.letVar _hv _hb)
      have hinv' := sizeInv_insert sourceDecls funcIdx env bindings l val idxs_v hinv hsz_v hfresh
      have hinterp_b : (Concrete.Eval.interp concDecls fuel ((l, val) :: env) b st').toOption.map Prod.fst
          = some interp_v := by
        rw [hok]; exact Concrete.Eval.interp_toOption_intro
      -- Inline the SSA-extension helper at `IsCoreExtended`. For inner
      -- `.letVar t'' e'' l'' v'' b''`, the binder `l''` differs from `l`
      -- (via `_hBinderNeq`), and the tail freshness comes from
      -- `hSsaFresh hinner w`.
      have hSsaFresh_b : ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local}
          {v'' b'' : Concrete.Term},
          IsCoreExtended layoutMap (.letVar t'' e'' l'' v'' b'') →
          ∀ w, (l'', w) ∉ ((l, val) :: env) := by
        intro t'' e'' l'' v'' b'' hinner w hmem
        rw [List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · have heq : l'' = l := by cases hhead; rfl
          exact absurd heq (_hBinderNeq (t' := t) (e' := e) (l' := l)
            (v' := v) (b' := b) (.letVar _hv _hb) hinner)
        · exact absurd htail (hSsaFresh hinner w)
      obtain ⟨idxs_b, st₂, hrun_b, hsz_b⟩ :=
        ihb (bindings := bindings.insert l idxs_v) (st₀ := st₁)
            (env := (l, val) :: env) (fuel := fuel) (evalSt := st')
            hinv' hSsaFresh_b interp_v hinterp_b
      refine ⟨idxs_b, st₂, ?_, hsz_b⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ _ st₁ hrun_v]
      exact hrun_b
  | @letWild t e v b _hv _hb ihv ihb =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_v : Concrete.Eval.interp concDecls fuel env v evalSt = res_v at hok
    match res_v, heval_v, hok with
    | .ok (val, st'), heval_v, hok =>
      simp only [] at hok
      have hinterp_v : (Concrete.Eval.interp concDecls fuel env v evalSt).toOption.map Prod.fst
          = some val := by rw [heval_v]; simp [Except.toOption, Option.map]
      obtain ⟨idxs_v, st₁, hrun_v, _⟩ :=
        ihv (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh val hinterp_v
      have hinterp_b : (Concrete.Eval.interp concDecls fuel env b st').toOption.map Prod.fst
          = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
      obtain ⟨idxs_b, st₂, hrun_b, hsz_b⟩ :=
        ihb (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel)
            (evalSt := st') hinv hSsaFresh interp_v hinterp_b
      refine ⟨idxs_b, st₂, ?_, hsz_b⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ _ st₁ hrun_v]
      exact hrun_b
  | @ptrVal t e a _ha iha =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (.pointer w i, st'), heval_a, hok =>
      simp only [] at hok
      have hval : interp_v = .field (G.ofNat i) := (congrArg Prod.fst (Except.ok.inj hok)).symm
      subst hval
      have hinterp_a : (Concrete.Eval.interp concDecls fuel env a evalSt).toOption.map Prod.fst
          = some (.pointer w i) := by rw [heval_a]; simp [Except.toOption, Option.map]
      obtain ⟨idxs, st₁, hrun, hsz⟩ :=
        iha (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh _ hinterp_a
      refine ⟨idxs, st₁, ?_, ?_⟩
      · unfold toIndex; exact hrun
      · rw [hsz]; unfold flattenValue; simp
  | @assertEq t e a b r _ha _hb _hr iha ihb ihr =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        split at hok
        · exact absurd hok (by intro h; cases h)
        · have hinterp_a := Concrete.Eval.interp_toOption_intro (v := v1) (st := st1)
          rw [← heval_a] at hinterp_a
          obtain ⟨idxs_a, st₁, hrun_a, _⟩ :=
            iha (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
                (evalSt := evalSt) hinv hSsaFresh v1 hinterp_a
          have hinterp_b := Concrete.Eval.interp_toOption_intro (v := v2) (st := st2)
          rw [← heval_b] at hinterp_b
          obtain ⟨idxs_b, st₂, hrun_b, _⟩ :=
            ihb (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel)
                (evalSt := st1) hinv hSsaFresh v2 hinterp_b
          have hinterp_r : (Concrete.Eval.interp concDecls fuel env r st2).toOption.map Prod.fst
              = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
          let st₃ : CompilerState := { st₂ with ops := st₂.ops.push (.assertEq idxs_a idxs_b) }
          have hmod := compileM_modify_run st₂
            (fun stt : CompilerState => { stt with ops := stt.ops.push (.assertEq idxs_a idxs_b) })
          obtain ⟨idxs_r, st₄, hrun_r, hsz_r⟩ :=
            ihr (bindings := bindings) (st₀ := st₃) (env := env) (fuel := fuel)
                (evalSt := st2) hinv hSsaFresh interp_v hinterp_r
          refine ⟨idxs_r, st₄, ?_, hsz_r⟩
          unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hrun_a]
          rw [compileM_bind_ok st₁ _ _ st₂ hrun_b]
          rw [compileM_bind_ok st₂ _ _ st₃ hmod]
          exact hrun_r
  | @debug t e label tOpt r hrecT _hrecR ihtOpt ihr =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    simp only [Concrete.Eval.interp] at hok
    have hinterp_r : (Concrete.Eval.interp concDecls fuel env r evalSt).toOption.map Prod.fst
        = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
    cases htOpt : tOpt with
    | none =>
      let st₁ : CompilerState := { st₀ with ops := st₀.ops.push (.debug label none) }
      have hmod := compileM_modify_run st₀
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label none) })
      obtain ⟨idxs_r, st₂, hrun_r, hsz_r⟩ :=
        ihr (bindings := bindings) (st₀ := st₁) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh interp_v hinterp_r
      refine ⟨idxs_r, st₂, ?_, hsz_r⟩
      unfold toIndex
      have hpure : ((pure none : CompileM (Option (Array Bytecode.ValIdx)))).run st₀ = .ok none st₀ :=
        compileM_pure_run st₀ none
      rw [compileM_bind_ok st₀ (pure none) none st₀ hpure]
      rw [compileM_bind_ok st₀ _ () st₁ hmod]
      exact hrun_r
    | some sub =>
      have hcoreSub := hrecT sub htOpt
      obtain ⟨idxs_t, st₁, ht⟩ :=
        toIndex_progress_core_extended layoutMap bindings sub st₀ hcoreSub
      let st₂ : CompilerState := { st₁ with ops := st₁.ops.push (.debug label (some idxs_t)) }
      have hmod := compileM_modify_run st₁
        (fun stt : CompilerState => { stt with ops := stt.ops.push (.debug label (some idxs_t)) })
      obtain ⟨idxs_r, st₃, hrun_r, hsz_r⟩ :=
        ihr (bindings := bindings) (st₀ := st₂) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh interp_v hinterp_r
      refine ⟨idxs_r, st₃, ?_, hsz_r⟩
      unfold toIndex
      rw [compileM_bind_ok st₀ _ idxs_t st₁ ht]
      rw [compileM_bind_ok st₁ _ (some idxs_t) st₁ (compileM_pure_run st₁ (some idxs_t))]
      rw [compileM_bind_ok st₁ _ () st₂ hmod]
      exact hrun_r
  | @tuple t e ts _hts ihts =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    -- Use interp_tuple_ok to extract per-element evalList result.
    obtain ⟨vs, hres, hv⟩ :=
      Concrete.Eval.interp_tuple_ok concDecls fuel env t e ts evalSt
        interp_v est hok
    subst hv
    -- Wire to tuple_array_fold_preservation.
    have hxs : ∀ x ∈ ts.toList, ∀ st₀' evalSt' (interp_v' : Value),
        (Concrete.Eval.interp concDecls fuel env x evalSt').toOption.map Prod.fst
          = some interp_v' →
        ∃ idxs st'',
          (toIndex layoutMap bindings x).run st₀' = .ok idxs st'' ∧
          idxs.size = (flattenValue sourceDecls funcIdx interp_v').size :=
      fun x hx st₀' evalSt' interp_v' hinterp' =>
        ihts x (Array.mem_toList_iff.mp hx)
          (bindings := bindings) (st₀ := st₀') (env := env) (fuel := fuel)
          (evalSt := evalSt') hinv hSsaFresh interp_v' hinterp'
    obtain ⟨idxs, st_final, hrun, hsz⟩ :=
      tuple_array_fold_preservation (sourceDecls := sourceDecls)
        (concDecls := concDecls) (funcIdx := funcIdx)
        (layoutMap := layoutMap) (bindings := bindings)
        env fuel ts.toList hxs evalSt vs est hres #[] st₀
    refine ⟨idxs, st_final, ?_, ?_⟩
    · unfold toIndex
      rw [← Array.foldlM_toList]
      exact hrun
    · -- (flattenValue (.tuple vs)).size = sum of per-element flatten.size.
      rw [hsz]
      simp only [Array.size_empty, Nat.zero_add]
      -- Goal: (List.map (fun v => (flatten v).size) vs.toList).sum
      --       = (flattenValue (.tuple vs)).size.
      -- `flattenValue (.tuple vs)` definitionally reduces to
      -- `vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue _ _ v)`, and
      -- `vs = vs.toList.toArray` by Array/List round-trip — so we use
      -- `flattenValue_attach_flatMap_size_toArray`.
      have hvs_eq : vs = vs.toList.toArray := by simp
      have hflat :
          flattenValue sourceDecls funcIdx (Value.tuple vs) =
          vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue sourceDecls funcIdx v) := by
        show flattenValue sourceDecls funcIdx (Value.tuple vs) = _
        rw [flattenValue]
      have hkey :
          (flattenValue sourceDecls funcIdx (Value.tuple vs)).size =
          (vs.toList.map (fun v => (flattenValue sourceDecls funcIdx v).size)).sum := by
        rw [hflat, hvs_eq]
        exact flattenValue_attach_flatMap_size_toArray sourceDecls funcIdx vs.toList
      exact hkey.symm
  | @array t e ts _hts ihts =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    obtain ⟨vs, hres, hv⟩ :=
      Concrete.Eval.interp_array_ok concDecls fuel env t e ts evalSt
        interp_v est hok
    subst hv
    have hxs : ∀ x ∈ ts.toList, ∀ st₀' evalSt' (interp_v' : Value),
        (Concrete.Eval.interp concDecls fuel env x evalSt').toOption.map Prod.fst
          = some interp_v' →
        ∃ idxs st'',
          (toIndex layoutMap bindings x).run st₀' = .ok idxs st'' ∧
          idxs.size = (flattenValue sourceDecls funcIdx interp_v').size :=
      fun x hx st₀' evalSt' interp_v' hinterp' =>
        ihts x (Array.mem_toList_iff.mp hx)
          (bindings := bindings) (st₀ := st₀') (env := env) (fuel := fuel)
          (evalSt := evalSt') hinv hSsaFresh interp_v' hinterp'
    obtain ⟨idxs, st_final, hrun, hsz⟩ :=
      tuple_array_fold_preservation (sourceDecls := sourceDecls)
        (concDecls := concDecls) (funcIdx := funcIdx)
        (layoutMap := layoutMap) (bindings := bindings)
        env fuel ts.toList hxs evalSt vs est hres #[] st₀
    refine ⟨idxs, st_final, ?_, ?_⟩
    · unfold toIndex
      rw [← Array.foldlM_toList]
      exact hrun
    · rw [hsz]
      simp only [Array.size_empty, Nat.zero_add]
      have hvs_eq : vs = vs.toList.toArray := by simp
      have hflat :
          flattenValue sourceDecls funcIdx (Value.array vs) =
          vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue sourceDecls funcIdx v) := by
        show flattenValue sourceDecls funcIdx (Value.array vs) = _
        rw [flattenValue]
      have hkey :
          (flattenValue sourceDecls funcIdx (Value.array vs)).size =
          (vs.toList.map (fun v => (flattenValue sourceDecls funcIdx v).size)).sum := by
        rw [hflat, hvs_eq]
        exact flattenValue_attach_flatMap_size_toArray sourceDecls funcIdx vs.toList
      exact hkey.symm
  | @letLoad t e dst dstTyp src bod _hsz _hbod _ihbod =>
    -- Decomposition: `interp_letLoad` reads memory + runs
    -- `unflattenValue _ gs 0 srcTyp` to produce `stored`, binds
    -- `(dst, stored) :: env` and recurses on `bod`. Compiler pushes
    -- `pushOp (.load size ptrIdxs[0]!) size` and recurses on `bod` with
    -- bindings extended by `(dst, range' valIdx size)`. Closure path:
    --   (s1) Extract `stored` via `interp_letLoad` inversion — bridges
    --        the read-memory → `unflattenValue` chain.
    --   (s2) `unflattenValue_preserves_ValueHasTyp` (NEW aux, BLOCKED)
    --        gives `ValueHasTyp concDecls dstTyp stored`. The aux
    --        composes with `interp_preserves_ValueHasTyp` (LowerShared,
    --        F=1) for the env-extension typing invariant.
    --   (s3) `flattenValue_size_of_ValueHasTyp` (S18) on `stored` →
    --        `(flattenValue stored).size = typSize layoutMap dstTyp`.
    --   (s4) `sizeInv_insert` to extend `sizeInv` with `(dst, idxs)` of
    --        matching width.
    --   (s5) Apply `ihbod` under the extended env/bindings; compose
    --        with the `pushOp .load` step on the compiler side.
    intro interp_v hinterp; sorry
  | @proj t e a i _iha htyp ihA =>
    -- Decomposition: extract `vs` via `interp_proj`, apply IH on `a` to
    -- get `(idxs_a, st₁, hrun_a, hsz_a)`, then close via:
    --   (s1) `interp_preserves_ValueHasTyp` (LowerShared, F=1) to extract
    --        `ValueHasTyp concDecls a.typ (.tuple vs)` — needs prereqs
    --        `RefClosed concDecls` + env-typing on parent signature.
    --   (s2) Destructure the witness's `.tuple` arm to obtain per-index
    --        `ValueHasTyp typs[k] vs[k]`.
    --   (s3) `flattenValue_slice_at_offset` (S19) to bridge:
    --          ∃ offset iLen, typSize lm typs[i] = .ok iLen ∧
    --          (flattenValue vs[i]).size = iLen ∧
    --          (flattenValue (.tuple vs)).extract offset (offset+iLen)
    --            = flattenValue vs[i]
    --   (s4) Compose IH `hrun_a` with the compiler-side toIndex `.proj`
    --        offset-fold, matching the offset/iLen extracted in s3.
    intro interp_v hinterp; sorry
  | @get t e a n _iha htyp ihA =>
    -- Decomposition: extract `vs` via `interp_get`, apply IH on `a` to
    -- get `(idxs_a, st₁, hrun_a, hsz_a)`, then extract typing witness
    -- via `interp_preserves_ValueHasTyp`. Closure path:
    --   (s1) `interp_preserves_ValueHasTyp` (LowerShared, F=1) on `a` →
    --        `ValueHasTyp concDecls a.typ (.array vs)`. Needs prereqs
    --        `RefClosed concDecls` + env-typing on parent sig.
    --   (s2) `htyp` gives `a.typ = .array τ k`; `.array`-arm
    --        destructure → per-index `ValueHasTyp τ vs[n]`.
    --   (s3) `flattenValue_size_of_ValueHasTyp` (S18) on `vs[n]` →
    --        `(flattenValue vs[n]).size = m` (= eltSize).
    --   (s4) `flattenValue_size_of_ValueHasTyp` (S18) `.array` arm
    --        gives `(flattenValue (.array vs)).size = vs.size * m`,
    --        which combined with `_hsz_a` lets us conclude
    --        `(idxs_a.extract (n*m) (n*m + m)).size = m`.
    --   (s5) Compose IH `hrun_a` with the compiler-side `.get` body
    --        (`pure $ arr.extract (n*m) (n*m + m)`).
    intro interp_v hinterp
    obtain ⟨τ, k, hτ, m, _hsize⟩ := htyp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_get] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (.array vs, st1), heval_a, hok =>
      simp only [] at hok
      split at hok
      · rename_i hn_lt
        have heq := Except.ok.inj hok
        have hv : interp_v = vs[n] := (congrArg Prod.fst heq).symm
        subst hv
        have hinterp_a :
            (Concrete.Eval.interp concDecls fuel env a evalSt).toOption.map Prod.fst
              = some (.array vs) := by
          rw [heval_a]; simp [Except.toOption, Option.map]
        obtain ⟨_idxs_a, _st₁, _hrun_a, _hsz_a⟩ :=
          ihA (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
              (evalSt := evalSt) hinv hSsaFresh _ hinterp_a
        -- Consume `interp_preserves_ValueHasTyp` to get the runtime
        -- array typing. Prereqs (RefClosed + env-typing) are sorried
        -- here; threading through the parent sig is the next step.
        have _hRefClosed : Concrete.Decls.RefClosed concDecls := by sorry
        have _hEnv : ∀ l v', (l, v') ∈ env →
            ∃ τ', ValueHasTyp concDecls τ' v' := by sorry
        have _hValueHasTyp_a : ValueHasTyp concDecls a.typ (.array vs) :=
          interp_preserves_ValueHasTyp _hRefClosed _hEnv heval_a
        -- (s2)-(s5) remain blocked: rewrite `a.typ` via `hτ` to
        -- `.array τ k`, destructure the `.array` arm of the witness,
        -- apply S18 twice (once on `.array vs` for `_hsz_a` =
        -- `vs.size*m`, once on `vs[n]` for the per-element width),
        -- and compose with the compiler-side extract.
        sorry
      · exact absurd hok (by intro h; cases h)
  | @slice t e a i j _iha htyp ihA =>
    -- Decomposition: extract `vs` via `interp_slice`, apply IH on `a`
    -- to get `(idxs_a, st₁, hrun_a, hsz_a)`, close via:
    --   (s1) `interp_preserves_ValueHasTyp` (LowerShared, F=1) on `a`
    --        to extract `ValueHasTyp concDecls a.typ (.array vs)` —
    --        needs prereqs `RefClosed concDecls` + env-typing on parent
    --        sig.
    --   (s2) Per-element typing on `vs.extract i j` from the array
    --        witness's per-index witness; new helper `array_extract_
    --        preserves_ValueHasTyp` would package this cleanly.
    --   (s3) `flattenValue_size_of_ValueHasTyp` (S18) on the slice plus
    --        the array case for the source array → bridges to
    --        `(j-i)*m` via uniform-element width.
    --   (s4) Compose IH `hrun_a` with the compiler-side `.slice` body
    --        (`pure $ arr.extract (i*m) (j*m)`).
    intro interp_v hinterp; sorry
  | @set t e a n v _iha _ihv htyp _ihA _ihV =>
    -- Decomposition: `interp_set` returns `.array (vs.set! n val)` for
    -- runtime array `.array vs` and replacement value `val`. Compiler
    -- returns `arr.extract 0 (n*m) ++ val ++ arr.extract ((n+1)*m)`.
    -- Closure path:
    --   (s1) Extract `vs`, `val` via `interp_set` inversion (`val`
    --        first, then `vs`).
    --   (s2) Apply IH on `a` (gives `idxs_a, st₁, hrun_a`) and on `v`
    --        (gives `idxs_v, st₂, hrun_v`).
    --   (s3) `interp_preserves_ValueHasTyp` (LowerShared, F=1) on `a`
    --        gives `ValueHasTyp concDecls (.array τ k) (.array vs)`.
    --   (s4) Same lemma on `v` gives `ValueHasTyp concDecls τ val`.
    --   (s5) `flattenValue_size_of_ValueHasTyp` (S18) on the array →
    --        `(flattenValue (.array vs)).size = k * m`. Same lemma on
    --        `val` → `(flattenValue val).size = m`.
    --   (s6) Bridge `.array (vs.set! n val)` flatten width: with
    --        uniform typing preserved under `.set!` (NEW helper) the
    --        size remains `k*m`.
    --   (s7) Compose with compiler-side
    --        `extract 0 (n*m) ++ val ++ extract ((n+1)*m)` =
    --        `n*m + m + (k-n-1)*m = k*m`.
    intro interp_v hinterp; sorry
  | @store t e a _ha iha =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_store] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      -- Output is `.pointer w idx` where idx comes from storeInsert.
      -- Width: flatten of `.pointer _ _` is `#[.ofNat _]`, size 1.
      have hinterp_a : (Concrete.Eval.interp concDecls fuel env a evalSt).toOption.map Prod.fst
          = some v1 := by rw [heval_a]; simp [Except.toOption, Option.map]
      obtain ⟨idxs_a, st₁, hrun_a, _hsz_a⟩ :=
        iha (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
            (evalSt := evalSt) hinv hSsaFresh v1 hinterp_a
      -- Extract pointer info from hok
      let gs := Concrete.Eval.flattenForStore v1
      let w := gs.size
      have hidx_eq : interp_v = .pointer w (Concrete.Eval.storeInsert st1 gs).2 := by
        have := (congrArg Prod.fst (Except.ok.inj hok)).symm
        simp only at this
        exact this
      rw [hidx_eq]
      refine ⟨Array.range' st₁.valIdx 1,
              { st₁ with valIdx := st₁.valIdx + 1,
                         ops := st₁.ops.push (.store idxs_a),
                         degrees := pushOpDegree st₁.degrees (.store idxs_a) 1 },
              ?_, ?_⟩
      · unfold toIndex
        rw [compileM_bind_ok st₀ _ _ st₁ hrun_a]
        exact pushOp_run st₁ (.store idxs_a) 1
      · unfold flattenValue; simp
  | @load t e a _ha _hwa htyp _ihA =>
    -- Decomposition: `interp_load` produces `unflattenValue _ gs 0 τ`
    -- from the read memory `gs` (where `a.typ = .pointer τ`). Compiler
    -- pushes `pushOp (.load size ptr) size`, `size = typSize lm τ`.
    -- Closure path:
    --   (s1) `interp_preserves_ValueHasTyp` (LowerShared, F=1) on `a`
    --        gives `ValueHasTyp concDecls (.pointer τ) (.pointer w n)`.
    --   (s2) `unflattenValue_preserves_ValueHasTyp` (NEW aux, BLOCKED)
    --        gives `ValueHasTyp concDecls τ (unflattenValue _ gs 0 τ).1`
    --        — the roundtrip-typing certificate.
    --   (s3) `flattenValue_size_of_ValueHasTyp` (S18) on the loaded
    --        value gives `(flattenValue _).size = typSize lm τ`.
    --   (s4) Compose IH on `a` (via `WidthOne` / `expectIdx`) with the
    --        compiler-side `pushOp (.load size ptr) size` step.
    intro interp_v hinterp; sorry
  | @app t e g args u hl _hargs _ihargs =>
    -- BLOCKED ON: deferred to Phase 4. `.app` preservation is the
    -- simultaneous-induction site at `fuel - 1` on `runFunction`-
    -- equivalence; central recursive obligation of the entire Lower
    -- preservation. Depends on the FnFreeBody / runFunction-equivalence
    -- chain (Phase 4 in PLAN.md).
    intro interp_v hinterp; sorry
  | @add t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_add, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (ga + gb) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.add ia ib),
                             degrees := pushOpDegree st₂.degrees (.add ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.add ia ib) 1
          · unfold flattenValue; simp
  | @sub t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_sub, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (ga - gb) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.sub ia ib),
                             degrees := pushOpDegree st₂.degrees (.sub ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.sub ia ib) 1
          · unfold flattenValue; simp
  | @mul t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_mul, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (ga * gb) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.mul ia ib),
                             degrees := pushOpDegree st₂.degrees (.mul ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.mul ia ib) 1
          · unfold flattenValue; simp
  | @eqZero t e a _iha hwa _ihA =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_eqZero] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      match v1, hok with
      | .field ga, hok =>
        have hv : interp_v = .field (if ga.val == 0 then 1 else 0) :=
          (congrArg Prod.fst (Except.ok.inj hok)).symm
        subst hv
        obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
        refine ⟨Array.range' st₁.valIdx 1,
                { st₁ with valIdx := st₁.valIdx + 1,
                           ops := st₁.ops.push (.eqZero ia),
                           degrees := pushOpDegree st₁.degrees (.eqZero ia) 1 },
                ?_, ?_⟩
        · unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
          exact pushOp_run st₁ (.eqZero ia) 1
        · unfold flattenValue; simp
  | @ioGetInfo t e k _hk ihK =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_ioGetInfo] at hok
    generalize heval_k : Concrete.Eval.interp concDecls fuel env k evalSt = res_k at hok
    match res_k, heval_k, hok with
    | .ok (vk, stk), heval_k, hok =>
      match vk, hok with
      | .array vs, hok =>
        simp only at hok
        cases hexp : Concrete.Eval.expectFieldArray vs with
        | none => rw [hexp] at hok; exact absurd hok (by intro h; cases h)
        | some keyGs =>
          rw [hexp] at hok
          simp only at hok
          cases hmap : stk.ioBuffer.map[keyGs]? with
          | none => rw [hmap] at hok; exact absurd hok (by intro h; cases h)
          | some info =>
            rw [hmap] at hok
            simp only at hok
            have hv : interp_v = .tuple
              #[.field (.ofNat info.idx), .field (.ofNat info.len)] :=
              (congrArg Prod.fst (Except.ok.inj hok)).symm
            subst hv
            have hinterp_k : (Concrete.Eval.interp concDecls fuel env k evalSt).toOption.map
                Prod.fst = some (.array vs) := by rw [heval_k]; simp [Except.toOption, Option.map]
            obtain ⟨idxs_k, st₁, hrun_k, _⟩ :=
              ihK (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
                  (evalSt := evalSt) hinv hSsaFresh _ hinterp_k
            refine ⟨Array.range' st₁.valIdx 2,
                    { st₁ with valIdx := st₁.valIdx + 2,
                               ops := st₁.ops.push (.ioGetInfo idxs_k),
                               degrees := pushOpDegree st₁.degrees (.ioGetInfo idxs_k) 2 },
                    ?_, ?_⟩
            · unfold toIndex
              rw [compileM_bind_ok st₀ _ _ st₁ hrun_k]
              exact pushOp_run st₁ (.ioGetInfo idxs_k) 2
            · unfold flattenValue
              simp [Array.attach, Array.attachWith, flattenValue]
  | @ioSetInfo t e k i l r _hk _hi _hl _hr hwI hwL ihK _ihI _ihL ihR =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_ioSetInfo] at hok
    generalize heval_k : Concrete.Eval.interp concDecls fuel env k evalSt = res_k at hok
    match res_k, heval_k, hok with
    | .ok (vk, stk), heval_k, hok =>
      simp only [] at hok
      generalize heval_i : Concrete.Eval.interp concDecls fuel env i stk = res_i at hok
      match res_i, heval_i, hok with
      | .ok (vi, sti), heval_i, hok =>
        simp only [] at hok
        generalize heval_l : Concrete.Eval.interp concDecls fuel env l sti = res_l at hok
        match res_l, heval_l, hok with
        | .ok (vl, stl), heval_l, hok =>
          simp only [] at hok
          match vk, vi, vl, hok with
          | .array vs, .field iG, .field lG, hok =>
            simp only [] at hok
            generalize hexp : Concrete.Eval.expectFieldArray vs = ofa at hok
            match ofa, hexp, hok with
            | some keyGs, hexp, hok =>
              simp only [] at hok
              split at hok
              · exact absurd hok (by intro h; cases h)
              · -- The non-collision branch: state updated, recurse on r.
                have hinterp_k : (Concrete.Eval.interp concDecls fuel env k evalSt).toOption.map
                    Prod.fst = some (.array vs) := by rw [heval_k]; simp [Except.toOption, Option.map]
                obtain ⟨idxs_k, st₁, hrun_k, _⟩ :=
                  ihK (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
                      (evalSt := evalSt) hinv hSsaFresh _ hinterp_k
                obtain ⟨ii, st₂, hexpI⟩ := expectIdx_run_of_widthOne layoutMap bindings i st₁ hwI
                obtain ⟨il, st₃, hexpL⟩ := expectIdx_run_of_widthOne layoutMap bindings l st₂ hwL
                let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
                let newMap := stl.ioBuffer.map.insert keyGs info
                let newBuf : IOBuffer := { stl.ioBuffer with map := newMap }
                let st''_eval : Concrete.Eval.EvalState := { stl with ioBuffer := newBuf }
                have hinterp_r : (Concrete.Eval.interp concDecls fuel env r st''_eval).toOption.map
                    Prod.fst = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
                let st₄ : CompilerState := { st₃ with ops := st₃.ops.push (.ioSetInfo idxs_k ii il) }
                have hmod := compileM_modify_run st₃
                  (fun stt : CompilerState =>
                    { stt with ops := stt.ops.push (.ioSetInfo idxs_k ii il) })
                obtain ⟨idxs_r, st₅, hrun_r, hsz_r⟩ :=
                  ihR (bindings := bindings) (st₀ := st₄) (env := env) (fuel := fuel)
                      (evalSt := st''_eval) hinv hSsaFresh interp_v hinterp_r
                refine ⟨idxs_r, st₅, ?_, hsz_r⟩
                unfold toIndex
                rw [compileM_bind_ok st₀ _ _ st₁ hrun_k]
                rw [compileM_bind_ok st₁ _ _ st₂ hexpI]
                rw [compileM_bind_ok st₂ _ _ st₃ hexpL]
                rw [compileM_bind_ok st₃ _ () st₄ hmod]
                exact hrun_r
  | @ioRead t e i n _hi hwi _ihI =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_ioRead] at hok
    generalize heval_i : Concrete.Eval.interp concDecls fuel env i evalSt = res_i at hok
    match res_i, heval_i, hok with
    | .ok (vi, sti), heval_i, hok =>
      match vi, hok with
      | .field gi, hok =>
        simp only [] at hok
        split at hok
        · exact absurd hok (by intro h; cases h)
        · rename_i hbound
          have hv : interp_v = .array
              (sti.ioBuffer.data.extract gi.val.toNat (gi.val.toNat + n) |>.map .field) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ii, st₁, hexpI⟩ :=
            expectIdx_run_of_widthOne layoutMap bindings i st₀ hwi
          refine ⟨Array.range' st₁.valIdx n,
                  { st₁ with valIdx := st₁.valIdx + n,
                             ops := st₁.ops.push (.ioRead ii n),
                             degrees := pushOpDegree st₁.degrees (.ioRead ii n) n },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpI]
            exact pushOp_run st₁ (.ioRead ii n) n
          · -- LHS: range'.size = n. RHS: flattenValue (.array (extract.map .field)).size.
            -- The extracted array has size n (extract bound), each elem flattens to #[_].
            simp only [Array.size_range']
            -- Width: extract is exactly `n`-wide (since `gi.val.toNat + n
            -- ≤ ioBuffer.data.size` from `hbound`), and each `.field _`
            -- flattens to width 1.
            have hextract_sz :
                (sti.ioBuffer.data.extract gi.val.toNat (gi.val.toNat + n)).size = n := by
              rw [Array.size_extract]
              have hle : gi.val.toNat + n ≤ sti.ioBuffer.data.size := Nat.le_of_not_lt hbound
              omega
            rw [flattenValue_array_map_field_size, hextract_sz]
  | @ioWrite t e d r _hd _hr ihD ihR =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_ioWrite] at hok
    generalize heval_d : Concrete.Eval.interp concDecls fuel env d evalSt = res_d at hok
    match res_d, heval_d, hok with
    | .ok (vd, std), heval_d, hok =>
      simp only [] at hok
      match vd, hok with
      | .array vs, hok =>
        simp only [] at hok
        generalize hexp : Concrete.Eval.expectFieldArray vs = ofa at hok
        match ofa, hexp, hok with
        | some dataGs, hexp, hok =>
          simp only [] at hok
          -- `interp r` from the modified state.
          have hinterp_d : (Concrete.Eval.interp concDecls fuel env d evalSt).toOption.map
              Prod.fst = some (.array vs) := by rw [heval_d]; simp [Except.toOption, Option.map]
          obtain ⟨idxs_d, st₁, hrun_d, _⟩ :=
            ihD (bindings := bindings) (st₀ := st₀) (env := env) (fuel := fuel)
                (evalSt := evalSt) hinv hSsaFresh _ hinterp_d
          let st''_eval : Concrete.Eval.EvalState := { std with ioBuffer :=
            { std.ioBuffer with data := std.ioBuffer.data ++ dataGs } }
          have hinterp_r : (Concrete.Eval.interp concDecls fuel env r st''_eval).toOption.map
              Prod.fst = some interp_v := by rw [hok]; exact Concrete.Eval.interp_toOption_intro
          let st₂ : CompilerState := { st₁ with ops := st₁.ops.push (.ioWrite idxs_d) }
          have hmod := compileM_modify_run st₁
            (fun stt : CompilerState => { stt with ops := stt.ops.push (.ioWrite idxs_d) })
          obtain ⟨idxs_r, st₃, hrun_r, hsz_r⟩ :=
            ihR (bindings := bindings) (st₀ := st₂) (env := env) (fuel := fuel)
                (evalSt := st''_eval) hinv hSsaFresh interp_v hinterp_r
          refine ⟨idxs_r, st₃, ?_, hsz_r⟩
          unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hrun_d]
          rw [compileM_bind_ok st₁ _ () st₂ hmod]
          exact hrun_r
  | @u8BitDecomposition t e a _iha hwa _ihA =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8BitDecomposition] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      match v1, hok with
      | .field ga, hok =>
        have hv : interp_v = .array (Array.ofFn fun (i : Fin 8) =>
          .field (G.ofUInt8 ((ga.val.toUInt8 >>> i.val.toUInt8) &&& 1))) :=
          (congrArg Prod.fst (Except.ok.inj hok)).symm
        subst hv
        obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
        refine ⟨Array.range' st₁.valIdx 8,
                { st₁ with valIdx := st₁.valIdx + 8,
                           ops := st₁.ops.push (.u8BitDecomposition ia),
                           degrees := pushOpDegree st₁.degrees (.u8BitDecomposition ia) 8 },
                ?_, ?_⟩
        · unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
          exact pushOp_run st₁ (.u8BitDecomposition ia) 8
        · -- The value is `.array (Array.ofFn (Fin 8) (.field _))`. Width = 8.
          unfold flattenValue
          simp [Array.attach, Array.attachWith, flattenValue,
                show (Array.ofFn (n := 8) (fun (i : Fin 8) =>
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> i.val.toUInt8) &&& 1)))) =
                  #[Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 0) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 1) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 2) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 3) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 4) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 5) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 6) &&& 1)),
                    Value.field (G.ofUInt8 ((ga.val.toUInt8 >>> 7) &&& 1))] from by
                  apply Array.ext'
                  simp [Array.toList_ofFn, List.ofFn]
                  rfl]
  | @u8ShiftLeft t e a _iha hwa _ihA =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8ShiftLeft] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      match v1, hok with
      | .field ga, hok =>
        have hv : interp_v = .field (G.ofUInt8 (ga.val.toUInt8 <<< 1)) :=
          (congrArg Prod.fst (Except.ok.inj hok)).symm
        subst hv
        obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
        refine ⟨Array.range' st₁.valIdx 1,
                { st₁ with valIdx := st₁.valIdx + 1,
                           ops := st₁.ops.push (.u8ShiftLeft ia),
                           degrees := pushOpDegree st₁.degrees (.u8ShiftLeft ia) 1 },
                ?_, ?_⟩
        · unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
          exact pushOp_run st₁ (.u8ShiftLeft ia) 1
        · unfold flattenValue; simp
  | @u8ShiftRight t e a _iha hwa _ihA =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8ShiftRight] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      match v1, hok with
      | .field ga, hok =>
        have hv : interp_v = .field (G.ofUInt8 (ga.val.toUInt8 >>> 1)) :=
          (congrArg Prod.fst (Except.ok.inj hok)).symm
        subst hv
        obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
        refine ⟨Array.range' st₁.valIdx 1,
                { st₁ with valIdx := st₁.valIdx + 1,
                           ops := st₁.ops.push (.u8ShiftRight ia),
                           degrees := pushOpDegree st₁.degrees (.u8ShiftRight ia) 1 },
                ?_, ?_⟩
        · unfold toIndex
          rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
          exact pushOp_run st₁ (.u8ShiftRight ia) 1
        · unfold flattenValue; simp
  | @u8Xor t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8Xor, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (G.ofUInt8 (ga.val.toUInt8 ^^^ gb.val.toUInt8)) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.u8Xor ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8Xor ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8Xor ia ib) 1
          · unfold flattenValue; simp
  | @u8Add t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8Add, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .tuple
            #[.field (G.ofUInt8 (ga.val.toUInt8.toNat + gb.val.toUInt8.toNat).toUInt8),
              .field (if ga.val.toUInt8.toNat + gb.val.toUInt8.toNat ≥ 256 then 1 else 0)] :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 2,
                  { st₂ with valIdx := st₂.valIdx + 2,
                             ops := st₂.ops.push (.u8Add ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8Add ia ib) 2 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8Add ia ib) 2
          · unfold flattenValue
            simp [Array.attach, Array.attachWith, flattenValue]
  | @u8Sub t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8Sub, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .tuple
            #[.field (G.ofUInt8 (ga.val.toUInt8 - gb.val.toUInt8)),
              .field (if gb.val.toUInt8 > ga.val.toUInt8 then 1 else 0)] :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 2,
                  { st₂ with valIdx := st₂.valIdx + 2,
                             ops := st₂.ops.push (.u8Sub ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8Sub ia ib) 2 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8Sub ia ib) 2
          · unfold flattenValue
            simp [Array.attach, Array.attachWith, flattenValue]
  | @u8And t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8And, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (G.ofUInt8 (ga.val.toUInt8 &&& gb.val.toUInt8)) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.u8And ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8And ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8And ia ib) 1
          · unfold flattenValue; simp
  | @u8Or t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8Or, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v = .field (G.ofUInt8 (ga.val.toUInt8 ||| gb.val.toUInt8)) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.u8Or ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8Or ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8Or ia ib) 1
          · unfold flattenValue; simp
  | @u8LessThan t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u8LessThan, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v =
            .field (if ga.val.toUInt8 < gb.val.toUInt8 then 1 else 0) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.u8LessThan ia ib),
                             degrees := pushOpDegree st₂.degrees (.u8LessThan ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u8LessThan ia ib) 1
          · unfold flattenValue; simp
  | @u32LessThan t e a b _iha _ihb hwa hwb _ihA _ihB =>
    intro interp_v hinterp
    obtain ⟨est, hok⟩ := Concrete.Eval.interp_toOption_elim hinterp
    rw [Concrete.Eval.interp_u32LessThan, Concrete.Eval.evalBinField_unfold] at hok
    generalize heval_a : Concrete.Eval.interp concDecls fuel env a evalSt = res_a at hok
    match res_a, heval_a, hok with
    | .ok (v1, st1), heval_a, hok =>
      simp only [] at hok
      generalize heval_b : Concrete.Eval.interp concDecls fuel env b st1 = res_b at hok
      match res_b, heval_b, hok with
      | .ok (v2, st2), heval_b, hok =>
        simp only [] at hok
        match v1, v2, hok with
        | .field ga, .field gb, hok =>
          have hv : interp_v =
            .field (if ga.val.toUInt32 < gb.val.toUInt32 then 1 else 0) :=
            (congrArg Prod.fst (Except.ok.inj hok)).symm
          subst hv
          obtain ⟨ia, st₁, hexpA⟩ := expectIdx_run_of_widthOne layoutMap bindings a st₀ hwa
          obtain ⟨ib, st₂, hexpB⟩ := expectIdx_run_of_widthOne layoutMap bindings b st₁ hwb
          refine ⟨Array.range' st₂.valIdx 1,
                  { st₂ with valIdx := st₂.valIdx + 1,
                             ops := st₂.ops.push (.u32LessThan ia ib),
                             degrees := pushOpDegree st₂.degrees (.u32LessThan ia ib) 1 },
                  ?_, ?_⟩
          · unfold toIndex
            rw [compileM_bind_ok st₀ _ _ st₁ hexpA]
            rw [compileM_bind_ok st₁ _ _ st₂ hexpB]
            exact pushOp_run st₂ (.u32LessThan ia ib) 1
          · unfold flattenValue; simp

end Aiur

end
