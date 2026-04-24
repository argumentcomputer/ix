# Lean 4 Proof Tactics

Compact patterns. One entry = one tactic. Code blocks unchanged.

## Motive not type correct (dependent rewrites on indexed access)

`arr[i]'hi` + `h` rewrites `arr` → fails. Fixes:
1. Index-erase: reformulate via `∈`, derive indexed via `Array.getElem_mem`.
2. `congrFun heq i` + `.trans`: prove functional eq first, apply pointwise.
3. `show (if h : ...)` to re-expose `dite`, then `rw [dif_pos hi]`.

## `@[expose]` iota pitfalls

`@[expose]` iota-reduces `(t.f).snd` after `intro` into `Decidable.rec`.
- Equation lemma `f = g` BEFORE `intro`; apply via `congrFun`.
- `generalize hd : t.f = d` before `intro`.
- Restate via `.fst`/`.snd` directly, skip `let (a, b) := ...`.
- `simp only [defName]` when `unfold` fails.

## `[i]!` ↔ `[i]'h`

`getElem!_pos arr i h : arr[i]! = arr[i]'h`.

## Array lemma names

- `Array.size_mapIdx` 0-ary.
- `Array.getElem_mem h` (not `mem_of_getElem`).
- `Array.mem_iff_getElem` — `x ∈ arr ↔ ∃ i hi, arr[i]'hi = x`.
- `Array.getElem_push_lt` / `Array.getElem_push`.
- `Array.extract_succ_eq_push` — DOESN'T exist; custom recursion.
- `Array.map_congr` — DOESN'T exist; `Array.ext` + pointwise.

## `Option` contradiction

`some x = none`: `Option.some_ne_none _`. NOT `Option.noConfusion` (expects `Sort u`).

## BEq-false via cases-true/false

```lean
cases heq : (a == b) with
| false => rfl
| true => -- contradiction in this branch
```

## IndexMap key-uniqueness (BEq)

```lean
theorem indexMap_key_unique (m : IndexMap α β) {k₁ k₂ v₁ v₂}
    (h₁ : (k₁, v₁) ∈ m.pairs.toList) (h₂ : (k₂, v₂) ∈ m.pairs.toList)
    (hbeq : (k₁ == k₂) = true) : v₁ = v₂
```
Proof: `List.getElem_of_mem` → i, j; `pairsIndexed`; `Std.HashMap.getElem?_congr hbeq` → indices equal → values equal.

## `omega` pitfalls

- Name `have` with explicit type.
- Don't `unfold X at this` before `omega` (injects `Decidable.rec`).
- Extract `(...).snd ≤ n` directly: `(invariant).2.2`.

## Non-core (no Mathlib)

`set ... with ...` → `let x := ...` + `have hx : x = ... := rfl`.

## `rfl`-equation for `if-then-else`

`@[expose] def f := if cond then a else b` → `f = if cond then a else b` is `rfl`:
```lean
have : f = if cond then a else b := rfl
rw [this]; by_cases hc : cond
· rw [if_pos hc]; ...
· rw [if_neg hc]; ...
```

## Bisimulation foldl

```lean
Array.foldl_induction (motive := fun i s₁ =>
    let s₂ := xs.extract 0 i |>.foldl f₂ init₂
    R s₁ s₂)
```

## Peel one iteration

Inductive step needs typeclass missing on outer type → peel one iteration; inner branches reduce to instance-ful type.

## `foldl_induction` motive HOU

`if b then ... else ...` inside motive fails HOU. Fix: `let x := if ...` inside motive. `decide True/False` → `simp`-based, not `rfl`.

## Helper-lemma generalization

```lean
private theorem helper (n : Nat) (xs : Array α) (h_inv : Inv xs n) :
    Inv (process xs) n := by
  induction structure_param generalizing xs
```

## `Array.attach.foldl` unpacking

Unpack `br.attach.foldl (init:=#[]) (fun acc ⟨(_,b),_⟩ => acc ++ f b)`:
1. `list_foldl_attachWith_eq` → `List.foldl` over `br.toList`.
2. Custom `list_foldl_f_eq_flatMap` → foldl-append to `flatMap toList`.

After: work with `l.flatMap (fun p => (f p.2).toList)`.

## `Array.foldl` backward analysis → list first

For backward key-analysis: convert to `List.foldl` via `Array.foldl_toList` + structural induction. Cleaner than `Array.foldl_induction` with implication motive. Bridge `∈` via `Array.mem_toList_iff.mp`.

Parameterize helper by `step : Acc → β → Acc` and `toKey : β → α` — single generic lemma serves chained folds.

## `generalize` vs `let` inside `Array.foldl_induction`

`let dt' := newDataTypes[i.val]'hi` zeta-reduces; `rw` fails. Fix: `generalize hdt'_eq : (newDataTypes[i.val]'hi) = dt'`.

`set x := ... with h` is Mathlib-only.

## Dual-invariant `Array.foldl_induction`

Fold end-state depending on "prior index matched P?" — pair `∃`-form ("seen, in expected state") + `∀`-form ("not yet, still init"). Extract via `Array.mem_iff_getElem`.

## Nested-inductive `deriving BEq` is opaque

`inductive T | ctor : Array T → T deriving BEq` produces opaque `T.beq`. `LawfulBEq T` unreachable via derived BEq. Fix: manual `T.beq : T → T → Bool` with `where`-bound helpers, terminated by `sizeOf`; `instance : BEq T := ⟨T.beq⟩` + manual `LawfulBEq`.

Mutual inductives: `deriving instance LawfulBEq for T, U` fails ("not supported"). `DecidableEq` same. Manual.

Manual `BEq` for mutual-with-Array gotchas:
- `mutual def f ... termination_by (sizeOf _)` may fail LCNF: `Failed to find LCNF signature for T._sizeOf_inst`.
- WA1: fuel-bounded `def f : Nat → T → T → Bool` w/ entry `T.beq t u := f (sizeOf t + 1) t u`. May still hit LCNF.
- WA2: structural `Depth : T → Nat` via `T.rec`, then use `Depth` as fuel. `T.rec` always emitted.
- ~200-400 LoC for Block/Ctrl-shaped mutual w/ Array nesting. Project-scope.

`induction` tactic fails on nested inductives. Use `@T.rec` w/ one motive per recursively-occurring type. `Array.mk` case: rec gives `(toList : List T) → motive_list toList → motive_array ⟨toList⟩`.

Motive strengthening for nested-array induction: `List` motive carries list-level statement AND elementwise as conjunction. `Array.mk` extracts `.2`; `List.cons` threads both.

## `fun_induction` + `.attach` subtype unification

`fun_induction` uses `y.1`; user helpers use `y.val`. Kernel-defeq, syntactic mismatch in `Array.foldlM`. Workarounds:
1. Match source `do`-shape, not goal's `match`-on-`Except`. `simp only [bind, Except.bind, pure, Except.pure]` on hypothesis BEFORE `rw`.
2. Bridge via `← Array.foldlM_toList` + `simp only [Array.toList_attach]` (Lean 4.29 normalizes `bs.toArray.toList` → `bs`).
3. Remove `.attach` from callee (invasive, sidesteps).

## Dummy-branch trick for size equality

"Branches-foldl sizes equal" without default-arm contribution: query size-eq theorem on `(Ctrl.match v br none)` vs `(Ctrl.match v br' none)`. Strip default via `simpa`.

## `let`-abbreviation for match arms in `Array.append_inj`

`match d with | none => x | some b => x ++ g b` inside sizes-append-inj: alias `x` as `let brFold := x`. Prevents `simp` exploding.

## Mutual recursion w/ size-decreasing membership

Branches-array mutual recursion (IH on `br[i].2`):
- Thread `∀ p ∈ l, sizeOf p.2 < sizeOf br`.
- `Array.sizeOf_lt_of_mem` + `Prod.mk.sizeOf_spec`.
- Termination: `(sizeOf c, 0)` / `(sizeOf b, 1)` lex pair.

## Iota capture on `unfold rewriteCtrl`

`unfold rewriteCtrl` then `cases d1` may fuse `d1` into match. Fix: `cases d1 / cases d2` FIRST, then `simp only [rewriteCtrl]`.

## Adversarial agents

"Falsify" agents surface missing hypotheses. "Prove true" miss holes. Red team + own analysis as prover. Skip blue team.

## Decomposition vs closure

Decomposing sorry into sub-sorries ≠ progress. Prefer closure. Exception: decomposition reveals unprovable/missing-hypothesis → IS progress.

## False-premise theorem detection

Unsatisfiable hypothesis → vacuously true, useless. Symptoms: all proofs via `False.elim`; callers can't discharge. Verify hypothesis provable from upstream BEFORE building atop.

## Consultant agent (after 2 fails)

Launch w/: theorem statement + available lemmas + failed attempts (tactic + error) + specific question. 30-50% useful pointers.

## Do-block: `rw` fails on dependent-motive matches

Goal: `match foldlM ... with | .error => ... | .ok v => ...`. Dependent motive blocks term-level substitution.

Fix: `split` + `cases` on `hbranch.symm.trans h_known`:
```lean
unfold thing
simp only [h_outer_guard, bind, Except.bind, pure, Except.pure]
split
· rename_i err herr
  exfalso
  have : (Except.error err : Except String _) = Except.ok <witness> :=
    herr.symm.trans h_known_ok
  cases this
· rename_i v hfv
  have hveq : v = <witness> := Except.ok.inj (hfv.symm.trans h_known_ok)
  subst hveq
```

`cases` on `.error = .ok` discharges False without `noConfusion`.

## `simp only [h_eq]` under match ≠ `rw [h_eq]`

Outer match: `simp only [h_eq]` often works where `rw [h_eq]` fails (motive inference). Try first before `split + cases`.

## `Fin.getElem_fin` unblocks `arr[j]` vs `arr[↑j]`

Inside `Array.foldl_induction`, `j : Fin as.size`. Motive uses `as[j.val]`. Hypotheses carry `as[↑j].snd`. `rw`/`simp only` fail on syntactic mismatch.

Fix: `simp only [Fin.getElem_fin, hf_eq, hpe, ↓reduceIte]`.

## `pairsCovered` ∀-eq form for clean weakening

Per-element invariant for foldl-induction motive over sum-typed list:
```lean
-- ∀-eq form: weakening = direct projection.
def covered (acc) (kd) : Prop :=
  (∀ f, kd.snd = .A f → P f acc) ∧
  (∀ dt, kd.snd = .B dt → Q dt acc)
```

`covered.weaken`: `obtain ⟨h_a, h_b⟩ := h; refine ⟨..., ...⟩`. Vacuous ctors absent from conjunction; consumer recovers via companion lookup.

## `induction l generalizing acc` regenerates dep hypotheses

`(h : q ∈ acc)` in scope + `induction l generalizing acc`: `h` auto-generalizes too.
```lean
| cons hd tl ih =>
  -- ih : ∀ acc, q ∈ acc → q ∈ tl.foldl f acc
  exact ih (f acc hd) (some_subset_proof acc q h)
```
`ih` takes acc value AND regenerated mem proof.

## Foldl body pointwise-congruence

`foldlM` body in helper vs consumer beta-equiv but syntactic different (do-sugar vs `__do_jp` vs match):
```lean
theorem List.foldlM_congr_body
    {α β : Type _} {m : Type _ → Type _} [Monad m]
    {f g : β → α → m β} (h : ∀ acc x, f acc x = g acc x) :
    ∀ (xs : List α) (init : β), xs.foldlM f init = xs.foldlM g init
```

Proof: induction on `xs`, each step applies `h`. Lives in `Ix/Aiur/Proofs/Lib.lean`.

## `conv_lhs` vs `conv => lhs`

`conv_lhs => ...` may not parse. Use `conv => lhs; ...` or bare `rw`/`simp only`.

## Anonymous-pattern λ vs `let` destructure

`fun (a, b) (c, d) => ...` and `fun acc p => do let (a, b) := acc; ...` beta-equiv but NOT syntactically identical. For `rw`/`simp only` on fold body, match consumer's lambda form. State sub-lemmas anonymous-pattern; destructure inside via `obtain ⟨a, b⟩ := acc`.

## Invariant struct w/ `autoParam`

```lean
structure Foo where
  flag : Bool
  list : List α
  invariant : list = [] ∨ flag = false := by
    first | exact Or.inl rfl | exact Or.inr rfl
```

Anonymous `⟨...⟩` fires autoParam. `mkAppM ``Foo.mk` does NOT — requires all fields. Smart constructors for metaprogramming.

## `grind` limits

Handles: decidable eq, small case-splits, Nat (omega), congruence closure.

Fails: do-notation body unification (`__do_jp` vs match), match-under-binder rewrites, nested fold-body congruence, dependent-motive rewriting. Skip `grind` for these → `split + cases` or `List.foldlM_congr_body`.

## `Nat.strongRecOn` (not `Nat.strong_induction_on`)

```lean
induction n using Nat.strongRecOn with
| ind n ih => ...
```
`ih : ∀ m, m < n → motive m`.

## Nested induction w/ `∀` bind

`have helper : ∀ (b : Nat) (t : T) (v : V), ... := by intro b; induction b with ...`. `induction b` BEFORE `intro t v`, else `ihb` specialized to fixed `t/v`, breaking inner recursion.

```lean
have helper : ∀ b t v, ... := by
  intro b
  induction b with
  | zero => intros; ...
  | succ b' ihb => intro t v ...; exact ihb t' v hyp
```

## `Array.mapM_except_ok` vs `List.mapM_except_ok`

- `List.mapM_except_ok` returns `∃ bs, l.mapM f = .ok bs` (List β).
- `Array.mapM_except_ok` returns `∃ ys : List β, a.mapM f = .ok ys.toArray`.

Mismatch → "List β expected Array β" errors.

## HashSet `contains_insert` + BEq

`HashSet.contains_insert : (m.insert k).contains a = (k == a || m.contains a)`. Case-split:
```lean
rw [Std.HashSet.contains_insert] at hc
rcases Bool.or_eq_true .. |>.mp hc with heq | hin
· have : k = a := LawfulBEq.eq_of_beq heq   -- ORDER: k = a, not a = k
```

## Sig strengthening cascades

Theorem sig too weak → strengthen sig AND update:
1. Upstream: stronger output requirement (sorry if upstream sorried, count unchanged).
2. Downstream: stronger hypothesis. Update callers w/ already-in-scope data.
3. Sibling `_ok` lemmas consuming the prop: check call sites.

`SizeBoundOk cd` from "¬ vis.contains dt.name" to "∀ g' dt', getByKey → ¬ vis.contains dt'.name": callers had stronger form already; only disjointness lemmas needed reshaping.

## Mindset: persistence

1. **Don't over-revert scratch**. Salvage F=0 helpers + skeletons before `rm`.
2. **Syntactic difference ≠ unprovable**. Beta-equal forms unify via `split + cases` on constructor-equality. Don't conclude "impossible" from `grind` failure.
3. **`grind` failure ≠ target verdict**. Fall back to `split + cases` or body-congruence lemma.
4. **Cross-cutting deps ≠ impossible**. Compose modulo sorried upstream — chain progress legitimate.
5. **Universe-fragile tactics**. `Except.noConfusion`/`EStateM.Result.noConfusion` fail w/ `Type _`. `cases h` on equation discharges False without unification drama.
6. **Sig defects = features**. Theorem FALSE-as-stated → fix hypothesis, don't prove weaker.
7. **F>0 agents progress-bearing**. Closed helpers + `.common.md` blocker doc bootstrap next attempt. Revert ONLY the open target.

## Salvaging partial agent output

1. Read agent's `A.lean` for closed helpers.
2. Move closures to main tree (visibility adjustments). Net positive even if top open.
3. Keep `A.lean` + `.notes.md` only if follow-up planned. Else delete.
4. Sig defect / missing upstream → port to PLAN.md or file docstring BEFORE deleting.

## Mathlib-only tactics (avoid)

| Don't | Use |
|---|---|
| `set X := Y with hX` | `let X := Y` + `have hX : X = Y := rfl` |
| `h.elim` on `h : x ∈ ([] : List α)` | `cases h` or `nomatch h` |
| `rcases ... <;> all_goals (...)` Mathlib-pattern | manual per-arm |

## Dangling-file (parallel agents)

Each writer owns one scratch; sees only own errors. Main-thread merger inlines after agents complete. No agent touches another's file or any real file.

Gotcha: scratch imports real proof modules. Main thread editing real file → in-flight agents see foreign errors. Either main works in own scratch OR waits for agents.

## "Processed/remaining split" key_helper (fold invariant)

For `List.foldlM` over `decls.pairs.toList` w/ per-key invariant + needing FULL decls-pairs context:
1. Invariant `P : Typed.Decls → Prop` over accumulator.
2. `List.foldlM_except_invariant` for simple cases.
3. Custom `key_helper` inducting over `remaining`, carrying predicate over `processed` + split `processed ++ remaining = decls.pairs.toList`.
4. Step case: `hsplit'` lets `IndexMap.getByKey_of_mem_pairs` for cross-pair key-uniqueness.

Reusable helper in `Lib.lean`: `IndexMap.pairs_toList_key_pairwise`.

## Sig fix > proving weaker

Theorem FALSE-as-stated → fix sig, thread hypothesis through callers. Examples:
- `concretizeName` not globally injective → `Typed.Decls.ConcretizeUniqueNames`.
- `eval_congr_dedup` arity-mismatch → `WellFormedCallees`.
- `sizeBound_ok_of_rank` vis arg → `SizeBoundVisInv`.

Sig change cascades to top (`compile_progress`/`compile_correct`); `sorry` at most at blocker site, NOT caller bridging.

## Predicate w/ implicit `{cd}` in `have`

```lean
def ConcretizeUniqueNames (tds : Typed.Decls) : Prop :=
  ∀ {cd : Concrete.Decls}, tds.concretize = .ok cd → ...
```

`have hunique := someCall` may fail (eager `{cd}` instantiation). Annotate:
```lean
have hunique : Typed.Decls.ConcretizeUniqueNames typedDecls := someCall
```

## Per-arm induction w/ term-fixed callback

Mutual recursion w/ `_termCompileDelta` callback: quantify only changing params, `term` fixed:
```lean
-- WRONG: ∀ term' defeats termination on recursive call
addCase_delta_arm (_termCompileDelta : ∀ term' bindings' ..., term_compile_delta term' ...)

-- RIGHT: term fixed
addCase_delta_arm (term : Term) (_termCompileDelta : ∀ bindings' ..., term_compile_delta term ...)
```

## `Bytecode.Eval.evalOp.mutual_induct` for evalOp/evalBlock/evalCtrl

3 mutually recursive eval-congruence theorems can't close independently (same-fuel recursion in `.match`). Consolidate via `Bytecode.Eval.evalOp.mutual_induct` w/ 6 coordinated motives. Individual theorems become trivial projections.

Motive shape: `fun ⟨(g, b), _⟩ => (g, rewriteBlock remap b)` elaborates to `match x with | ⟨(g,b), property⟩ => ...`. Match motive form exactly, else `rw`/`simp` fails.

## `cases _db` BEFORE `unfold evalCtrl`

matchContinue arms: `_db : Option Block` creates dep-motive capture under `unfold`. Fix: `cases _db` BEFORE `unfold`. Each branch gets specialized `harm`/`ih_arm` with no dep binding.

## Drain-state invariant pattern

4-level preservation chain:
```lean
def DrainState.<Inv> (tds) (st) : Prop := ...
theorem DrainState.<Inv>.init : <Inv> tds {empty} := ...
theorem concretizeDrainEntry_preserves_<Inv> := ...
-- list_foldlM (via List.foldlM_except_invariant)
-- iter (concretizeDrainIter unfold + ih)
-- top concretizeDrain
```

Examples: `MonoHasDecl`, `MonoValueIsConcretized`, `NewNameShape`. ~200 LoC each, mechanical.

## Three-way mutual for universal-callback termination

Helper takes `∀ term', termCompileDelta term' ...` callback, non-mutual itself → structural termination can't analyze callback at call sites in `foldlM`. Lift helper into same `mutual` block:
```lean
mutual
  theorem term_compile_delta term ... := ...
  theorem addCases_fold_delta patTerms ... := ...  -- recurses on patTerms
  termination_by sizeOf term
```

## `@[expose]` for cross-module def-body

Lean 4 module mode: `public def` makes name visible, body opaque. Downstream can't `unfold`. Add `@[expose]`:
```lean
@[expose] def MyPred (x : T) : Prop := ...
```

Symptom: cite `theorem foo : MyPred x` works, but `show ∀ y, ...` fails on unfold.

## `@[expose]` on simple-body defs unblocks `rfl`-bridges

`def IndexMap.size := m.pairs.size` w/o `@[expose]` is sealed cross-module. `unfold`, `simp [size]`, `rfl`, `attribute [local reducible]` all fail. Add `@[expose]` → `theorem bridge : m.size = m.pairs.size := rfl`.

Symptom: build error on private/sealed body, OR mysterious `rfl` failure on definitionally-equal goal.

## `IndexMap.insert` at existing key = `pairs.set` (in-place)

`Ix/IndexMap.lean:39`: checks `m.indices[a]?`. None → `pairs.push` (size grows). Some idx → `pairs.set idx (a, b)` (size preserved via `Array.size_set`).

Implication: under FullyMono, `concretizeBuild`'s `dtStep`/`fnStep` insert at keys already in srcStep's output → in-place. `concretizeBuild.size = typedDecls.size` regardless of `newDataTypes`/`newFunctions` content.

## `do let x ← M; rest` desugars to `Bind.bind`

NOT `>>=`. Custom `compileM_bind_ok`-style helpers using `>>=` fail to unify w/ `do`-form. Fix: explicit `change ((_ >>= _).run _ = _)` to align. OR write helpers in `Bind.bind` form.

## `unfold flattenValue` aggressively expands per-element match

`flattenValue cd fid (.tuple vs)` unfolds to `vs.attach.flatMap (fun ⟨v, _⟩ => match v with | .field _ => ... | ...)` — match expansion across all `Value` ctors. `rfl`/`change` fail.

Fix: `show flattenValue _ _ (.tuple vs) = _; rw [flattenValue]` for surgical 1-level. Then `flatten_attach_flatMap_size_*` helpers close residual.

## `IsCoreExtended` partial-coverage extension pattern

Extending partial-coverage induction (e.g., `IsCore` covering 9 of 36 `Term` arms) to full:
1. Define `IsCoreExtended` w/ all arms; each new arm carries side-conditions (`typSize lm dstTyp = .ok n`, `arg.typ = .tuple typs`).
2. `IsCore.toExtended` embedding F=0.
3. Original `toIndex_progress_core` becomes `_extended` taking `IsCoreExtended`.
4. **Carrier predicates** (e.g., `WidthOne layoutMap typ`) bundle multi-arm preconditions. Adding to `IsCoreExtended` constructors centralizes prerequisite (unblocks 14 width-1 arms simultaneously).

Used Phase 1 of compile_correct closure: 22/23 progress arms F=0, 30/37 preservation F=0.

## Mutual-induction proof for fuel + structure

Two functions cross-recursing on fuel + structural Typ + DataType:
```lean
mutual

private theorem f_agree (h : ...) :
    ∀ n V V' ty cty,
    P → typFlatSizeBound decls n V ty = ... cd n V' cty
  | 0, ... => by unfold typFlatSizeBound; rfl
  | n+1, V, V', _, _, hM, hVagree => by
      cases hM with
      | unit => unfold; rfl
      | tuple hLen hElems => ... foldl_pw_add helper ...
      | ref => ... case-split visited ... cross-call to g_agree at fuel n ...

private theorem g_agree (h : ...) :
    ∀ n V V' src_dt cd_dt, ... := by
  | 0, ... => by unfold; rfl
  | n+1, ... => by ... map_pw_eq + foldl_max ... recurse via f_agree at n ...

end
```

Termination: structural on `n`. `g_agree (n+1) → f_agree n` decreasing. `f_agree (n+1).{tuple, array}` self-recurse w/ `n` decreasing. `f_agree (n+1).{ref}` cross-call to `g_agree n` decreasing.

Helpers:
- `foldl_add_pointwise_eq` — pointwise-equal Nat folds give equal sums.
- `List.map_pw_eq` — pointwise-equal list maps give equal lists.
- `Array.attach_foldl_pw_add` — same for `Array.attach.foldl`.

## False predicate placeholder (anti-pattern)

`def hasConstrainedCall (_t) (_caller _callee) : Prop := False` is dead-weight: consuming predicate becomes vacuously true. Symptoms:
- `grep` shows predicate consumed nowhere.
- "Real" check described in comment, never implemented.
- Removing the predicate breaks no proof.

Diagnostic: never-referenced placeholder predicate → delete. Its `WellFormed` field is dead-weight.

## Recognize over-restrictive `WellFormed` fields

`FullyMonomorphic t` requires empty `params`. Polymorphic source (e.g. `enum List<T>`) FAILS trivially. If real-world programs in test/example tree don't satisfy `WellFormed t`, sig defect.

Diagnostic:
1. Pick concrete program from test/example tree.
2. Check each `WellFormed` field by hand. Failure → sig defect candidate.
3. Trace usage: load-bearing or proof shortcut?

Real example (2026-04-27): `FullyMonomorphic` excludes IxVM. TEMPORARY tag; multi-week refactor.

## Agent file inconsistency on incomplete dispatch

Agent removes infra mid-session, fails to complete replacement → dangling refs. Build breaks at `Unknown identifier <removed-lemma>` at unrelated-looking lines.

Recovery (preference order):
1. Surgical revert of agent's incomplete edits; salvage F=0.
2. Re-add stub of removed helper as `sorry` + BLOCKED note. Plan follow-up.
3. Wholesale `git checkout HEAD -- <file>`. Last resort.

Option 3 used 2026-04-27 (broken Phase 2 agent in ConcretizeSound). Lost ~3000 LoC session work.

Prevention: agent prompts forbid deleting infra unless replacement complete same session. "Do NOT delete `<lemma>` until you have a passing replacement in scope."

## Background agents + monitor

Long-running (>30 min) → `run_in_background: true`. Monitor:
1. `ls -la <jsonl-file>` → size growth + mtime. Steady growth + recent mtime = healthy.
2. `ScheduleWakeup` 600s+ (10 min) — amortize cache miss.
3. Stale (>3 min mtime, no growth): `TaskStop <agentId>`.

Don't:
- Read JSONL output (overflow).
- Sleep < 270s (cache hot, no info).
- Sleep 300s exactly (cache miss without amortization).
- Run agent >30 min without checkpoint.

## Module struct field cascade

`obtain ⟨a, _, b, _, _, _, _, c⟩ := hwf` matches by FIELD ORDER. Removing struct field misaligns ALL caller destructures. Errors: `rcases` failed, type mismatch.

Fix: update each destructure (`git grep` for `:= hwf`). Pattern applies to ANY anonymous-constructor destructure.

## Preserve pre-unfold alias before `unfold at`

```lean
have hconc_orig := hconc
unfold Typed.Decls.concretize at hconc
-- ... pass hconc_orig to drain-invariant lemmas ...
```

Observed in `concretize_produces_ctorPresent`.

## Sub-sorry stacking vs sig fix (diagnostic)

F>S on single target + decomp "infrastructure-heavy" (10+ sub-lemmas, 50+ LoC each) → theorem **sig-defective**. Construct counterexample:
- Polymorphic `tf.params = [p]` falsifies `concretize_extract_function_at_name`.
- Function value `.ref g` w/ `g ∈ functions` falsifies `runFunction_preserves_FnFree`.
- `concretizeName g args = concretizeName g' args'` w/ rank mismatch falsifies `concretize_preserves_direct_dag`.

Strengthen sig (rule out counterexample) > stack sub-sorries.

## Two-stage drain-invariant decomposition

Target invariant `∀ X, reachable X → st.mono[X]? = some _` too strong for step-wise → decompose:
- (a) `SeenSubsetMono`: `st.seen ⊆ dom(st.mono)` — easy step-wise.
- (b) `ReachableReachedOrPending`: `∀ X, reachable X → X ∈ st.seen ∨ X ∈ st.pending`.

At drain end (pending = []): (b) → `reachable X → X ∈ seen`; combined w/ (a) → `reachable X → X ∈ mono`.

Pattern: existing `NewNameShape`/`MonoValueIsConcretized`/`NewFunctionsFO` infra.

## Deep-arm consolidation under strict-decrease

N arms via `cases t`, M trivial (1-3 lines) + N-M deep (300+ LoC each): do NOT stack N-M sorries. Consolidate N-M into SINGLE top-level sorry. Close M trivial inline; ONE explicit `sorry` w/ BLOCKED-note listing each case + required infra.

## Path A (thread-decidable-hypothesis)

Drain-invariant proof requires hypothesis from project-wide condition (e.g. `FullyMonomorphic`) but not in drain API → sig-strengthen target, thread through 4-level chain, discharge at top-level via `WellFormed` projection.

Cheaper than new `DrainState.<Args>Invariant` chain.

Example: T4 needed `mkParamSubst []` returning identity. Strengthened sig to `(hparamsEmpty : ∀ tf ∈ typedDecls.pairs.map Prod.snd, ... .params = []) →`. Caller discharged via `typedDecls_params_empty_of_fullyMonomorphic hwf.fullyMonomorphic hts`.

## DrainState invariant pattern (NewFunctionsFO)

```lean
def DrainState.NewFunctionsFO (tds) (st) : Prop :=
  ∀ f ∈ st.newFunctions, Concrete.Typ.FirstOrder f.output

theorem DrainState.NewFunctionsFO.init : NewFunctionsFO tds {empty} := ...
theorem concretizeDrainEntry_preserves_NewFunctionsFO := ...
-- list/iter/top (~4 theorems, ~150 LoC)
```

## Pointwise predicate transport through Except-mapM

```lean
theorem List.mem_mapM_ok_forall {α β ε} {f : α → Except ε β} {xs ys}
    (h : xs.mapM f = .ok ys) (hP : ∀ x ∈ xs, ∀ y, f x = .ok y → Q y) :
    ∀ y ∈ ys, Q y
```

`Array` analog same.

## `mem_of_attach_map`

```lean
theorem mem_of_attach_map {arr : Array α} {f : {x // x ∈ arr} → β} {b : β}
    (h : b ∈ arr.attach.map f) :
    ∃ x ∈ arr, ∃ (hx : x ∈ arr), f ⟨x, hx⟩ = b
```

## Strengthen sig to conjunction for state-propagation

Recursive theorem needs state-preservation through recursive calls + sig only one conjunct → strengthen to conjunction:
```lean
-- weak: state not on returns
theorem term_compile_delta ... : BlockCalleesFromLayout layoutMap body

-- strong: state propagates via .1
theorem term_compile_delta ... :
    AllCallsFromLayout layoutMap s'.ops ∧ BlockCalleesFromLayout layoutMap body
```

`(term_compile_delta ...).1` feeds next sibling; `.2` block-callees.

## `cases hrun` substitutes mid-state — compute recursive BEFORE

`cases hrun` rewrites mid-state fresh var (`s3`) to final (`s'`). Recursive-call hypothesis on `s3.ops` → reference lost.

```lean
-- BEFORE cases hrun:
have hcontRes : AllCallsFromLayout s3.ops ∧ BlockCalleesFromLayout body :=
  term_compile_delta bod ... (by ...)
obtain ⟨hops_s3, hbc⟩ := hcontRes
cases hrun  -- hops_s3 auto-updates to s'
```

## B2: `.call` arm of dedup_mutual_congr arity-mismatch

Same defect as `eval_congr_dedup`: `.arityMismatch funIdx` vs `.arityMismatch (remap funIdx)`. `WellFormedCallees t` doesn't help (constrains body callees, not caller-supplied funIdx).

Resolution (b): weaken motives `a = b` → `a = .ok x → b = .ok x` (one-directional). Error payload mismatch irrelevant.

## `let`-destructure vs `rw` (Decidable.rec gotcha)

Body begins `let (tDedup, remap) := t.deduplicate`. Outer `simp only [↓reduceDIte]` unfolds to `Decidable.rec`. Bridge via `let` won't match for `rw`.

Fix: restate explicitly:
```lean
have hbridge : Eval.runFunction (t.deduplicate).1 ((t.deduplicate).2 funIdx) ... = ...
  := by show ...; exact ...
rw [← hbridge]
```

Use `(t.deduplicate).1`/`.2` directly in signatures, avoid `let`-destructure.

## Motive weakening for error-payload mismatch (`.ok`-transport)

Different error payloads on success vs transformed → weaken motives:
```lean
motive_op : Nat → Op → State → Prop :=
  fun fuel op st => ∀ x, evalOp t fuel op st = .ok x → evalOp t' ... = .ok x
```

Error branches vacuous (false premise). Happy path closes via helper composition.

## Sig-fix-induced bridge sorries at callers

Strengthening upstream sig forces each caller to provide new hypothesis. Not in scope → bridge sorry per caller. Sig-fix exemption: net +N where N = caller bridge count. Mark each `-- BLOCKED ON: <exported-lemma-needed>`.

## Unreachable-but-Lean-can't-see arms

`match term with | .letVar _ _ _ (.match ..) bod => arm1 | .letVar _ _ _ val bod => arm3` — arm3 w/ `val = .match ..` IS dead but Lean's elaborator doesn't dedup. Options:
1. Duplicate arm1 into dead case of arm3 (~200 LoC per dead arm).
2. Flat dispatch: `| .letVar _ _ var val bod => cases val with | .match .. => arm1body | _ => arm3body`.
3. `nomatch` if Lean sees unreachability at type level (rare).

## Docstring-before-namespace

Lean 4 rejects `/-- ... -/` immediately followed by `namespace Foo`. Insert dummy decl:
```lean
/-- docstring -/
private def _foobar_docstub : Unit := ()

namespace Foo
```

Or attach docstring to first theorem.

## Vacuous-hypothesis axioms (anti-pattern)

Reject:
- `∀ (_ : Unit), P` or `∃ (_ : Unit), True` — degenerates to unconditional.
- `True`-valued shadow `def Predicate ... : Prop := True` — no-op.
- `∀ g, P g` w/ `g` unconstrained, goal `P specific` — vacuous quantification.

If F=0 cites such axioms, "proof" vacuous. Revert.

## Sub-namespace condensation

Agent closes `T` F=0 via N axioms + helpers. Port:
```lean
namespace TBody
theorem axiom1 <hyps> : ... := by sorry
theorem axiom2 <hyps> : ... := by sorry
theorem helper1 ... := ...
theorem T_body <hyps> : ... := by <use axiom1, axiom2, helper1>
end TBody

theorem T <hyps> : ... := TBody.T_body <hyps>
```

Sorries: +N-1 (axioms vs main body retired). Don't port if circular-import blocker.

## `Lean.Name.str n s ≠ n`

```lean
theorem Name_str_ne_self : ∀ (n : Lean.Name) (s : String),
    Lean.Name.str n s ≠ n
  | .anonymous, _, h => by cases h
  | .str n' s', s, h => by
    injection h with hn hs
    exact Name_str_ne_self n' s' hn  -- sizeOf-decreasing
  | .num n' k, s, h => by cases h
```

`pushNamespace` injectivity:
```lean
theorem pushNamespace_inj_both {g₁ g₂ : Global} {s t : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace t) : g₁ = g₂ ∧ s = t := by
  unfold Global.pushNamespace at h
  have h' := Global.mk.inj h
  injection h' with hn hs
  exact ⟨Global.mk.injEq _ _ |>.mpr ⟨hn⟩ |>.mp rfl, hs⟩
```

## Weakened-pre / strong-post for inner fold

Outer fold has intermediate state breaking full invariant `P` → inner fold helper PRE-condition `P'` = `P` minus unsatisfied clauses; POST = full `P`. Inner-step preservation threads dichotomy: pre-weakened clauses remain (monotonic insert); inner final step re-establishes full `P`.

Cleaner than global-strengthening outer motive.

## Speed up iteration: temporary `#exit` below target theorem

When iterating on a single theorem inside a large file, Lean re-elaborates everything below it on every edit — slow for big files (ConcretizeSound.lean is 14k lines).

Insert `#exit` IMMEDIATELY below the target theorem during iteration:

```lean
theorem foo (...) := by
  ...your proof in progress...

#exit  -- TEMPORARY — remove before commit

theorem bar ...  -- everything below skipped during elaboration
```

Lean stops elaborating at `#exit`. `lake build` of that file finishes seconds instead of minutes. Remove `#exit` before committing or running full build.

## Per-arm match decomposition for large structural inductions

When a per-`Decl`-kind closure is 250-400 LoC, restructure body into a single match with `sorry` per arm:

```lean
theorem foo (d : Decl) (h : ...) : P d := by
  match d, h with
  | .function f, hf => sorry  -- arm 1: BLOCKED on ...
  | .dataType dt, hd => sorry  -- arm 2: BLOCKED on ...
```

Lean folds multiple sorries in one body into a single `uses sorry` warning, so framework progress doesn't inflate counts.

## Universal `tds`/`cd`-key claims are FALSE for polymorphic source

`∀ g f, tds.getByKey g = some (.function f) → f.params = []` is structurally false: a polymorphic non-entry typed function is a counterexample.

Before closing any universal-form sig, audit: does the conclusion hold for ALL keys, or only entry-reachable ones? If only entry-reachable, refactor sig to per-call BEFORE attempting closure.

## `notPolyEntry` ⟹ entry-reachable mono propagates without `FullyMono`

`Source.Function.notPolyEntry : params = [] ∨ entry = false`. Combined with `concretize`'s drain (which monomorphizes the transitive call graph from entry seeds), per-entry monomorphism propagates structurally. Use entry-restricted variants of `_under_fullymono` lemmas; cite `concretize_drain_preserves_StrongNewNameShape`.

## `lake build` "uses sorry" is authoritative

`grep "^[ \t]*sorry$"` overcounts: catches sorries in `/-...-/` block comments (Lean ignores those). Verify via:

```
lake build 2>&1 | grep "uses \`sorry\`" | wc -l
```

## `String.Pos` changed in Lean 4.29

`String.drop : String → Nat → String.Slice` (was `String`). `String.extract` requires `String.Pos.Raw`-typed args, not `Nat`.

```lean
-- Don't:
let rest : String := s.drop "_private.".length  -- type error
-- Do:
let parts := s.splitOn "."  -- back to List String
```

## Strengthened drain-invariant for FullyMono derivations

`DrainState.NewNameShape` carries `dt.name = concretizeName g args` but NOT `args.size = dt_orig.params.length`. Under `FullyMonomorphic`, `args.size = 0` derivable via `typedDecls_(dt_)params_empty`, closing `concretizeName g #[] = g`.

`DrainState.StrongNewNameShape` adds:
- `args.size = orig.params.length` (fn + dt).
- `dt.constructors.map (·.nameHead) = dt_orig.constructors.map (·.nameHead)` (dt-arm).

Preservation chain follows `NewNameShape` verbatim. Close `.dataType` ctor-map preservation: `List.map_map` + `List.map_congr_left` + `rfl`.

Pattern: any FullyMono structural correspondence → strengthened drain invariant w/ same 4-level proof shape.
