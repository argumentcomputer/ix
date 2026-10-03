# The Lean compiler as passes: design document (Phase A)

Status: **draft for the owner's signature (review R1)**. Written 2026-10-02/03 on `jcb/ix-certified`
at `f829b760` (Lean 4.34.1). No compiler file changed between `e9cb732e` (where the planning reports
cite lines) and `f829b760`, so every `file:line` below is valid at both. Nothing was built or run to
write this document.

Lean's elaborator is cited from a Lean **4.34.0** source tree (`src/lean/Lean/...`), the only one
readable when this was written; whether 4.34.1 changed any cited line is **[open]**.

**Status markers** (as in the old plan):
- **[measured]**: an experiment or census recorded it; the input file is cited.
- **[argued]**: a paper argument given here.
- **[open]**: not established.

A fact about code carries a citation and no marker.

**Abbreviations.**
- *Old plan*: `plans/review/auxgen-certify/PLAN.md` (untracked). Its definition numbers (Def 1.x–4.x,
  O1–O17, M.1–M.6) are reused here.
- *Phase A*: `plans/PLAN-A-compiler-design.md` (untracked).
- *CEN*, *PRO*, *ORA*, *MUT*: the census, prototype, oracle and mutual-definition study under
  `plans/review/auxgen-certify/inputs/` (`exp-census-1.md`, `exp-prototype-1.md`, `exp-oracle-1.md`,
  `study-mutual-definitions-1.md`).

Every definition used here is restated, so this document does not depend on those files.

---

## 0. Findings in brief

1. **The comparator is a total preorder at every fixed context, on every input Lean can produce**
   [argued, §3]. The fixed point of the refinement does not depend on the seed order: neither the
   partition nor the order of the classes does. Only the order of members inside a class does, and
   that is metadata [argued].
   - The Lean port has two latent defects that the Rust original does not have. **C1:** comparing
     members of different kinds always returns `lt`. **C2:** the comparison cache is not normalised
     for argument order.
   - Neither is reachable today [argued]. C2 becomes reachable as soon as the seed is made name-free,
     so its fix is part of A2.
   - The order is *defined by the refinement procedure*. A declarative "fixed point of sorting" is not
     unique (§2.3, §3.4 C9).
2. **"Addresses break only full ties" is not what the code does.** External references are compared
   by address at the first position where two members differ, interleaved with the structural
   comparison. Phase A's decision therefore needs a two-key comparator (§2.3, §3.5).
3. **Discovery order** is a FIFO queue over the block's types, each constructor walked pre-order. It
   is not "depth first into new auxiliaries" as the old plan's Def 2.5 says. It is pinned in §2.5.
   - One rule is unverifiable from local sources: how an occurrence of a *sibling* of an external
     mutual inductive is deduplicated [open, §2.5].
4. **Transport of clique proofs is not a pure renaming in any of the three encodings** (§5). They
   use up to four kinds of step:
   - (R) a renaming of the encoding's own constants;
   - (A) a re-association of the packing types, injections, case trees, tuples and projection paths;
   - (S) re-stated obligations wherever a statement mentions the packing (well-founded `proof_N`,
     `partial_fixpoint` monotonicity goals);
   - for `partial_fixpoint`, (G) regeneration of the projection-path monotonicity sub-proofs, whose
     shape depends on the path.

   Every transported term proves the canonical obligation [argued]. Where the conjugation does not
   apply, Lean's own term is a fallback proof:
   - by conversion, for the well-founded obligations;
   - by composition with the re-association isomorphism, for monotonicity;
   - unchanged, for theorem bodies, whose statements never mention the encoding.

   The fallback is recorded as residue.
5. **Lean 4.34's well-founded definitions with a single `Nat` measure use `WellFounded.Nat.fix`.**
   That combinator reduces on closed arguments (`src/lean/Init/WF.lean:470-499`), so the old plan's
   "never meet by conversion, not even on closed arguments" holds only for the `WellFounded.fix`
   route (§5.2).

---

## 1. The pipeline and the convention

### 1.1 The passes

Input: the prepared `List (Lean.Name × Lean.ConstantInfo)` (`Ix/CompileDriver.lean:1194-1226`), plus
read access to `Structural.eqnInfoExt`, `WF.eqnInfoExt` and the `partial_fixpoint` `EqnInfo`.

Output:
- the Ixon v4 environment `E`;
- the side-car: names, hints, metadata, `Named.original`, clique permutations, call-site records.

| # | Pass | Input | Output | Module (to be) |
|---|---|---|---|---|
| P1a | Components | prepared constants | the SCCs of the reference graph (§2.1) | `Ix/Compile/Canon/Graph.lean` |
| P1b | Classes and order | one SCC; the closure's addresses | ordered classes; representative per class (§2.2–2.3) | `Ix/Compile/Canon/{Classes,Order}.lean` |
| P1c | Nested auxiliaries | canonical inductive block | the expanded block in discovery order; evaporation set (§2.5–2.6) | `Ix/Compile/Canon/Nested.lean` |
| P1d | Cliques | `EqnInfo`, `_unsafe_rec`, `partial_fixpoint` data | cliques, specifications, classes, order, `σ` (§2.7) | `Ix/Compile/Canon/Clique.lean` |
| P1e | Name map | P1a–P1d | `N : Lean.Name → canonical position` | `Ix/Compile/Canon/NameMap.lean` |
| P2 | Ix auxiliaries | canonical blocks | `rec`, `rec_N`, `casesOn`, `recOn`, `below*`, `brecOn*` (`.go`, `.eq`, `_N`), `IndPredBelow`; one constant per auxiliary | `Ix/Compile/Pass/Aux.lean` over `Ix/AuxGen/*` |
| P3a | Images | Lean recursors of changed blocks; P1, P2 | `img(r)` (Def 3.3–3.4, §4) | `Ix/Compile/Pass/Image.lean` |
| P3b | Translation and baseline | every other constant | `tr_N`, Def 3.5 images, Def 3.6 baselines, inline call sites (§4.5) | `Ix/Compile/Pass/Translate.lean` |
| P3c | Canonical cliques | changed cliques | the repacked functional, transported proofs, members as projections (§5) | `Ix/Compile/Pass/Clique/{Structural,WF,PartialFixpoint,Transport}.lean` |
| P4+ | Optimisations | baselines | O1–O17, each a module with a side condition | `Ix/Compile/Pass/Opt/O*.lean` |
| P4e | Rewrite engine | P4+ modules | the fixed point (§1.4) | `Ix/Compile/Pass/Engine.lean` |
| P5 | Emission | compiled terms | sharing, serialisation, side-car | `Ix/Compile/Pass/Emit.lean` |
| — | Fold | all of the above | the sequential fold over blocks that defines `compile` (§6) | `Ix/Compile/Fold.lean` |

P1 is written as total pure functions over data types. They have no `partial`, and import nothing
from `Lean` beyond the data types (Phase A §3.1).

### 1.2 The five-part docstring

Every `Ix/Compile/Pass/**` module opens with:

```
/-! # <Pass name>

## Contract
Input invariants, output invariants, stated with the definitions of §2 (components, classes,
canonical order, discovery order, name map N, images, baselines) and the kernel's declaration
language.

## Faithfulness
Definitional pass: the conversion steps (δ of which constants, β, ζ, η, ι, projection of a
constructor) that make each rewritten constant definitionally equal to its baseline.
Proof-justified pass: the equation, the statement Phase B formalises, and its proof sketch
(induction on what, which lemma).

## Canonicity
What the output depends on: canonical data only, or canonical data plus addresses (where), plus
the residue. Why two presentations of one canonical block or clique give equal bytes.

## Side condition and fallback
The decidable condition. What remains when it fails (the baseline) and why that is faithful.

## Residue and evidence
Known non-canonical outputs with their cause code (§7.2). The fixtures, twins, value pins and
census counts that exercise the pass, with their status markers.
-/
```

### 1.3 Worked example: O1, permutation pass-through

```
/-! # O1: recursor of a permuted block

## Contract
Input: a baseline term containing an occurrence `img(T.rec).{u,us} a₁ … a_m` or
`img(T.recOn).{u,us} a₁ … a_m`, where T is a member of a Lean inductive block b whose
canonicalisation is a *pure permutation*:
  - one component;
  - every class a singleton;
  - only the member order and/or the discovery order of nested auxiliaries differ from Lean's.
Let ρ be the Ix recursor of T's class (the recursor block of canon(b), projection at T's canonical
motive index).
Let π be the bijection from Lean motive indices to Ix motive indices: members by the class map,
auxiliaries by the discovery-order map (§2.5).
Let π′ be the induced bijection on minors: Lean minor (i, k) ↦ Ix minor (π i, k), with
constructors by position.
Output: the occurrence is replaced by
    ρ.{u′, us′} ps (ms ∘ π⁻¹) (mins ∘ π′⁻¹) is x a_{n+1} … a_m
where
  - ps, ms, mins, is, x are the first n = np + nm + nmin + ni + 1 arguments in Lean's order;
  - u′, us′ are the canonical levels (`canonUniv`, positional renaming);
  - for `recOn` the Lean argument order (ps ms is x mins) is read accordingly.
The result contains no image reference at this position. The arguments are copied unchanged.

## Faithfulness (definitional)
By Def 3.4 with all classes singletons:
  - no slot is a tuple, so the level is u (step 2) and no slot is lifted (step 3);
  - every Lean induction hypothesis comes from a field that is recursive for ρ: the block is one
    component, so nothing is relocated (step 4.2);
  - so the Ix minor for constructor c of slot π i is `λ fs ihs. lean_minor_{i,k} fs ihs`, with the
    IHs in the same field order. Ix and Lean constructors have the same fields by position.
The development (§4.3) η-contracts it to `lean_minor_{i,k}`, so
    img(T.rec) ≡ λ ps ms mins is x. ρ ps (ms∘π⁻¹) (mins∘π′⁻¹) is x.
The rewrite is one δ-step (img), one β-step (n arguments) and η-steps on the minors. Each is a
conversion the kernel performs, so `Eq.refl : @Eq τ c base(c)` checks, where τ is the translated
Lean type of the rewritten constant c [argued].
For recOn: Def 3.5 makes img(T.recOn) Lean's value over img(T.rec), and the same steps apply.

## Canonicity
Let twin(c) be c's counterpart in the source where b is declared in canonical order. Then twin(c)
mentions T′.rec with its arguments already in canonical order, and its translation is
`ρ ps ms′ mins′ is x …` with ms′ = ms∘π⁻¹ term for term, because the user's motives and minors are
the same terms up to the renaming.
The output depends on: π (a function of the canonical order, §2.3, and of the discovery order,
§2.5); the canonical levels; the arguments.
It does not depend on Lean's member order beyond π.
So two presentations give equal bytes once their arguments are equal after translation [argued].
Addresses enter only through ρ's address, i.e. through the canonical block.

## Side condition and fallback
Decidable: m ≥ n (fully applied), and b is permutation-only (read from P1).
Otherwise the occurrence keeps its baseline reference to the image constant img(T.rec), which is
faithful by Def 3.6 and Prop 3.3.

## Residue and evidence
Residue: none for full applications. Bare or partial occurrences stay faithful only (cause BARE,
§7.2).
Evidence:
  - [measured] ORA (exp-oracle-1.md, DQReord): 53/53 constants of a reordered fixture equal the
    twin's, including the structural functions and the theorem.
  - [measured] CEN (exp-census-1.md:20, Q3): in Mathlib's closure, 6 reordered blocks; 206 `rec`-plan
    call sites; 14 `Ring` definitions and 16 `_f`.
  - [measured] PRO (exp-prototype-1.md, C1): permutation images 2/2, rules 3/3, `rfl` bridges 4/4.
  - Twins gate: every permutation of every fixture block (§3.6).
-/
```

### 1.4 Pass order and the fixed point

**The engine.**
- Passes P1 → P2 → P3 run once per block or clique, in the fold order of §6.
- The optimisation passes run in the engine, separately on every compiled constant:
  - repeat: traverse the term bottom-up (arguments before the head, left to right);
  - at each image occurrence, apply the first pass in the fixed order whose pattern and side
    condition hold;
  - after each rewrite, develop the created redexes (§4.3);
  - stop when no pass applies.
- Whole-unit passes (cliques: O13–O17; helper families: O11a/b) run once per unit, after the
  occurrence passes have finished on the unit's constants.

**Termination** [argued]:
- the measure is the number of image-constant occurrences in the term;
- every occurrence pass removes one, the occurrence it rewrote;
- no pass introduces an image occurrence. The outputs are over Ix constants and the copied
  arguments; O2's relocated calls are Ix recursors, not images;
- the development (§4.3) contracts only redexes created at the rewrite site, so it is finite;
- unit passes run once.

**Confluence of the definitional passes** [argued]:
- O1–O4 and O11a have pairwise disjoint patterns, distinguished by the auxiliary kind and by the
  block's change kind.
- O5 is O1–O4 at universe 0, not a separate pattern. It is implemented as the level rule inside
  O1–O4.
- O6 overlaps O1, O3 and O4: every permuted-block image of theirs is "an Ix auxiliary applied to a
  permutation of its arguments". On the overlap, both rewrites produce the same term.
- Every rewrite is left-linear in its arguments and copies them unchanged, so rewrites at nested
  positions commute.
- One interaction needs the bottom-up order. The development can make a bare occurrence fully
  applied: `(λ g. g p q) (img a)` develops to `img a p q`. The engine re-scans after each
  development, so the result does not depend on which occurrence was examined first.
- So for the definitional passes, the order of the table below is immaterial.

**Order constraints for the other passes** [argued]:
1. Definitional passes first (O1–O6, O11a, O13a/b). They recover today's output on the library call
   sites, and the clique passes need them: a canonical clique is elaborated over the *Ix*
   auxiliaries of canonical blocks (M.6 counts a clique that ranges over a changed block as changed).
2. Clique passes (O14–O16) next. O9 (split, structural recursion with a cross field) is the target of
   O14 over a split block (old plan §3.6), so the two produce the same rewrite and do not conflict.
3. Collapse and split passes last (O7, O8, O10, O11b, O12, O17). Their side conditions compare the
   *compiled* forms of arguments ("arguments identical after compilation"), so every argument must
   already be in normal form. The bottom-up traversal guarantees that.
   - O7 is disjoint from O1 (collapsed versus permuted-only block).
   - O8 is disjoint from O3 (collapsed or lifted member versus permuted or split block).
4. **Demotion** (old plan §3.5, requirement 2): a proof-justified rewrite whose dependent Lean proofs
   need the old shape to unfold is reverted to the baseline. Demotion only removes rewrites and the
   set is finite, so the iteration reaches a fixed point. A demoted constant changes its own bytes
   and the addresses of its users, but no pass decision of a user: users reference it by address
   [argued].

---

## 2. Canonical form, defined

### 2.1 Components (Def 2.1)

- **Graph.** There is an edge `x → y` when the constant `y` occurs in `x`:
  - for an inductive: in its type, plus an edge to each constructor name;
  - for a constructor: in its type, plus an edge to its inductive;
  - for a definition, theorem or opaque: in its type or its value;
  - for a recursor: in its type, plus edges to the rule constructors and to the constants of the
    right-hand sides;
  - a projection `proj S i e` gives an edge to `S` (`Ix/GraphM.lean:26-71`; Rust
    `get_constant_info_references`).
- **Components.** The SCCs of this graph, by Tarjan (`Ix/CondenseM.lean:54-108`).
  - For an inductive block, the inductive → constructor → (constructor-type references) path makes the
    component of `T` exactly the SCC of Def 2.1's member graph: there is an edge `Tᵢ → Tⱼ` when `Tⱼ`
    occurs in the type of `Tᵢ` or of one of its constructors [argued]. Lean declarations cannot
    reference a later declaration, so a member is reachable only from its own block.
  - Recursors are never in a member's component: nothing in the block references them.
- **Kinds.** Lean's mutual declarations are kind-homogeneous: all inductives, or all definitions, of
  one safety. A safe constant cannot reference a `partial` or `unsafe` one. Hence every SCC of Lean
  input is kind-homogeneous and safety-homogeneous [argued]. §3 relies on this.
- **Unaffected by traversal order.** The *set* of members of a component does not depend on the
  traversal order. The SCC *representative* `lo` (the Tarjan root) does
  (`Ix/CondenseM.lean:110-144`), and so does the member iteration order (a `Set`): neither may reach
  the output (§6).
- **Definitions.** Safe structural and well-founded cliques are acyclic after elaboration: each
  member is a non-recursive definition over `brecOn`, `WellFounded.fix` or `Lean.Order.fix` (MUT
  §2). So definition SCCs come only from `partial`/`unsafe` blocks and their `_unsafe_rec`
  companions. Safe cliques are canonicalised on their specifications (§2.7), not on the graph.

### 2.2 Classes (Def 2.2) and the structural key

A partition `P` of a component `K` is **consistent** when any two members in one class are equal
under the **structural key** once every occurrence of a member of `K` is replaced by its class and
every other constant by its address. The **classes** are the coarsest consistent partition.

The key compares, lexicographically, in this order.

**Kind tag:** definition < inductive < recursor.
- Rust implements this (`crates/compile/src/compile.rs:3586-3592, 3618`).
- Lean does not (defect C1, §3.4).

**Definition** (`Ix/CompileM.lean:2153-2158`; `compile.rs:3369-3405`): `DefKind`, universe-parameter
count, type, value. Safety and hints are not compared. Hints are per name in `Named.hints`.

**Inductive** (`Ix/CompileM.lean:2181-2192`; `compile.rs:3468-3530`):
- universe-parameter count, parameter count, index count, constructor count, type;
- then the constructors pairwise (`Ix/CompileM.lean:2162-2178`): universe count, constructor index,
  parameters, fields, type;
- Rust additionally compares `is_rec` and `is_unsafe` first (C6, §3.4).

**Recursor** (`Ix/CompileM.lean:2199-2212`; `compile.rs:3536-3580`): universe count, parameters,
indices, motives, minors, `k`, type, rules (field count, right-hand side).

**Expression** (`Ix/CompileM.lean:2054-2140`; `compile.rs:3232-3365`): a structural walk with the
constructor-tag order mdata(semantic) > … and bvar < sort < const < app < lam < forallE < letE < lit
< proj. Within it:
- binder names and binder info are ignored;
- non-semantic `mdata` is stripped;
- semantic-contract `mdata` compares by `Contract.orderKey` (`Ix/SemanticContract.lean:53`), then by
  its body;
- `bvar` by index;
- levels by `compareLevel`: zero < succ < max < imax < param, with parameters by position in each
  side's own list (`Ix/CompileM.lean:1983-2009`);
- **constants**: level arguments first, then equal names are equal, then
  - two in-block names compare by current class index. This is the **weak** comparison: its
    result is flagged `strong = false`;
  - an in-block name is less than an external one;
  - two externals compare by compiled address (`Ix/CompileM.lean:2085-2104`). An unresolved address
    is an error, never a fallback to the name (`compile.rs:3206-3227`);
- projections compare the structure the same way, then the field index, then the body
  (`Ix/CompileM.lean:2122-2135`).

**Context.** The context is `MutConst.ctx` (`Ix/Mutual.lean:95-121`):
- member ↦ index of its class;
- constructor ↦ `#classes + offset`, with offsets reserved per class by the class's maximum
  constructor count.

Lean blocks never reference their own constructors inside member or constructor types, so
constructor entries never decide a comparison [argued].

**Phase A decision: levels are compared after `canonUniv`.**
- Today `compareLevel` reads syntax, while compilation canonicalises afterwards
  (`Ix/CompileM.lean:417`).
- So two members equal after canonicalisation but spelled differently fall in different classes.
  That is a gap in minimality, and the order between them follows the spelling.
- Comparing `canonUniv u` (`Ix/IxonUniv.lean:379`) with parameters by position makes collapse
  coincide with equality of compiled content [argued].
- This holds whether or not `canonUniv` is complete for level equivalence; completeness is [open]
  and is not needed here.

### 2.3 Canonical order (Def 2.3), as a procedure

**Definition (refinement).** Let `seed` be a total order on the members of `K` (§2.8 fixes it). Then:

```
classes₀ := [K sorted by seed]
classes_{n+1} := concat over C in classes_n (in order) of
                   if |C| = 1 then [C]
                   else groups(sortBy (cmp_{ctx(classes_n)}) C)   -- stable; groups of equal neighbours,
                                                                   -- each group in seed order
stop at the first n with classes_{n+1} = classes_n
```
- The canonical order of `K`'s classes is the final list.
- The representative of a class is its first member in seed order.
- `cmp_ctx` is the key of §2.2 under the context `ctx`.

Today's implementation:
- Lean `sortConsts` (`Ix/CompileM.lean:2246-2353`): the stopping rule is an unchanged class count,
  with fuel `|K| + 1`;
- Rust `sort_consts` (`compile.rs:3723-3790`): the stopping rule is an unchanged class list;
- the two rules agree, because refinement only splits classes and keeps each group in place [argued].

**Not a declarative fixed point.** The order is the *history* of the splits: once two classes are
separated, their relative order is never revisited. In general the final list is not the result of
sorting the final classes by `cmp_{ctx(final)}`. A declarative definition ("an ordered partition
fixed by sorting under its own indices") can have several solutions: two classes whose contents
mention each other symmetrically can be self-consistent in either order. The refinement picks one of
them deterministically. **The canonical order is therefore defined as the output of this procedure**,
and Phase B proves properties of the procedure, not of a declarative characterisation [argued].

**Phase A decision: addresses break only full ties.** Today an external reference compares by address
wherever two members first differ (`Ix/CompileM.lean:2098-2104`), interleaved with structure. So the
order depends on the Ixon format version whenever the first difference is an external constant.

Phase A's key is the lexicographic pair `(k₀, k₁)`:
- `k₀` is the key of §2.2 with **all external references equal** (in-block references still by class
  index);
- `k₁` is today's key.

Properties:
- `k₁`-equality implies `k₀`-equality, so the pair's equality is `k₁`'s and **the partition does not
  change** [argued];
- only the order changes, and only in blocks where `k₀` decides differently from `k₁`.

Census (CEN Q5, `exp-census-1.md:159-169`) [measured]: in Mathlib's closure, 1 of 16 multi-class
member sorts (`Aesop.GoalUnsafe`) and 4 of 33 nested sorts "tie without addresses". Whether that
census measured `k₀`-ties or today's first-difference rule is not stated, so the number of blocks
whose order moves is [open]. A1's census instrumentation must count it.

### 2.4 Member content (Def 2.4; D3/D16)

The canonical declaration of a class is its representative's declaration, changed as follows:
- **universe parameters:** the Lean block's whole list, in order;
- **parameter count:** the block's;
- **result sort:** as declared;
- **references:** to other members of the component by class; to everything else by address.

Elimination universe, `K` target, `isRec`, reflexivity and structure-likeness are computed by the
kernel on the Ix block, never inherited from Lean.

Nothing is pruned. A split member is therefore not the same constant as that member declared alone
when it ignores a block universe or parameter, or when its declared sort is larger than needed (ORA
split cause (a), `UnivSplit` [measured]).

The content does not depend on which member represents the class [argued]. Members of one class are
equal under the key, and every compared datum has a canonical compiled form:
- levels by position, after canonicalisation;
- in-block references by class;
- externals by address;
- binder names and non-semantic `mdata` are metadata.

### 2.5 Nested auxiliaries in discovery order (Def 2.5; D2)

Lean's kernel replaces nested occurrences by auxiliary inductive types in `elim_nested_inductive`
(C++ `src/kernel/inductive.cpp:963-1077`, cited through its ports; the C++ file is not in the local
source tree). Ix ports it twice:
- Lean: `Ix/AuxGen/Nested.lean:485-729`;
- Rust: `crates/compile/src/compile/aux_gen/nested.rs:172-700`.

Both claim to mirror it line by line (`nested.rs:239, 486-487, 1070-1073`).

**Definition (discovery order).** Input:
- members `m₁ … m_n` in a fixed order;
- the block's `np` parameters and levels.

Procedure:
- Let `Q := [m₁, …, m_n]`, a queue of types, and `seen` an empty map from occurrences to
  auxiliaries.
- For `q = 0, 1, …` while `q < |Q|`, for each constructor `c` of `Q[q]` in constructor order:
  1. instantiate the first `np` binders of `c`'s type with the block parameters;
  2. walk the remaining type **pre-order**:
     - application: function, then argument;
     - binder: domain, then body;
     - `let`: type, value, body;
     - `proj`: the body;
     - `mdata`: the body;
     - a node that was replaced is not descended into (`Nested.lean:596-627`; `nested.rs:172-238`);
  3. at a node `e = I As idx` that is an **occurrence**, replace `e` (rules below);
  4. replace `c`'s type by the rewritten type.
- A node is an occurrence when all of the following hold (`Nested.lean:485-516`):
  - `I` is an inductive whose name is not in `Q`;
  - `|As| ≥ np(I)`;
  - some parameter argument mentions a name in `Q`;
  - the parameter arguments, rewritten into block-parameter space, contain no loose bound variable
    and no free variable other than a block parameter. A parameter that depends on a constructor
    field disqualifies the node.
- **Replacing an occurrence:**
  - if `I As` (the key, in block-parameter space) is in `seen`, replace `e` by `seen[I As]` applied
    to the block parameters and `idx`;
  - otherwise, for each `J` in `I.all`, in order: append to `Q` the auxiliary type
    `aux_k := J.{lvls} As`, with `J`'s constructors specialised, result heads renamed to the
    auxiliaries, and `k` a global counter. Record `seen[I As] := aux` of `I`. Replace `e` by `I`'s
    auxiliary (`Nested.lean:526-590`).
- The **discovery order** of the auxiliaries is their order in `Q` after the members. Lean names the
  recursor of the `k`-th as `m₁.rec_k`.

Two consequences:
- An auxiliary's own constructors are walked only when the queue reaches it. Auxiliaries found
  inside auxiliaries therefore come after every auxiliary found from an earlier queue entry.
- The order is breadth-first over types and pre-order within one constructor. **The old plan's
  "depth first into new auxiliaries" (Def 2.5) is incorrect** and is replaced by this definition.

**Discovery order over the canonical block.** Run the definition with:
- `m₁ … m_n` := the class representatives of one component, in canonical order;
- every reference to a non-representative member rewritten to its representative first
  (`aliasToRep`, `Nested.lean:678-696`);
- members of other components counted as external: they are not in `Q`.

Consequences:
- two occurrences `List A` and `List B` with `A ≅ B` become one key, so one auxiliary (merged nested
  auxiliaries);
- an occurrence whose parameters mention only other components is not an occurrence (evaporation,
  §2.6);
- for a block whose canonical order is Lean's `all` order, with no split and no collapse, the
  procedure is Lean's own, so the block is an identity block [argued].

Evidence:
- [measured] CEN:28: every unchanged block's regenerated auxiliaries are α-equal to Lean's, 21,136 of
  21,136 in Mathlib's closure, including nested blocks whose structural order coincided with Lean's.
  This is indirect evidence that the port's source walk reproduces Lean's numbering. The direct gate
  is the oracle on every nested fixture (Phase A §5.3).

**[open] Deduplication of sibling occurrences.**
- Both ports register only the *head* `I As` in `seen`, not the siblings `J As`
  (`Nested.lean:542-546`; `nested.rs:369-373`). The comment says the siblings are "reached through
  the normal queue walk".
- If an auxiliary constructor's field is `J As`, with `J` a sibling of an external mutual `I`, the walk
  finds no `seen` entry and would create a second group.
- Whether Lean's kernel registers every `J` cannot be checked from local sources.
- A2 must settle it with a fixture *before* the migration: a nested occurrence of an external mutual
  pair, e.g. `Tree/Forest` used as `T | mk : Tree T → T`, compared against Lean's `rec_N` count and
  order.

**What changes.** This replaces the structural sort:
- `sortAuxByPartitionRefinement`, `Nested.lean:731-918`;
- Rust `sort_aux_by_partition_refinement`, `nested.rs:681-760`, with an identity-marker constructor
  per auxiliary;
- the kernels' mirrors: `canonical_aux_order`, `crates/kernel/src/inductive.rs:1284-1450`;
  `Ix/Tc/CanonicalCheck.lean`;
- the certified modeller's "largest family first" in `Ix/Kernel/Frontend/InModel/Nested.lean`;
- the certified `BlockOrder` variant.

### 2.6 Evaporation

After a split, Lean's auxiliary for `I As` **evaporates** from component `K` when `As` mentions no
member of `K`. By §2.5 it is then not an occurrence in `K`'s walk.

Its Lean recursor `rec_j` has no Ix counterpart in `K`. Its image eliminates with `elim(t)` of Def
3.3:
- the recursor of another component whose expansion contains `tr_N(t)`;
- else that of a container inside `t`;
- else that of `t`'s head.

Census (`exp-census-1.md:24`) [measured]: no evaporation in Init, Std, Lean, Batteries or Mathlib.

### 2.7 Definition cliques (M.1–M.6)

- **M.1, clique.**
  - For structural and well-founded recursion: `EqnInfo.declNames` (`.../Structural/Eqns.lean`,
    `.../WF/Eqns.lean:18-46`).
  - For a `partial` or `unsafe` block: the block, or its `_unsafe_rec` companions. These are
    canonicalised as SCCs (§2.1) and need no specification.
  - `partial_fixpoint`: its `EqnInfo` (`.../PartialFixpoint/Main.lean:220`).
- **No specification** for theorems or Prop-valued definitions. `EqnInfo` is not registered for them
  (`.../Structural/Main.lean:202-213`; `.../WF/Eqns.lean:41-42`), and `abstractNestedProofs` skips
  theorems (`.../PreDefinition/Basic.lean:120-128`).
- **M.2, specification.** For a member `f`: (kind and safety, universe count, type, method, value,
  pinned choices). The value is `EqnInfo.value`, after nested-proof abstraction for definitions.
  Recursive calls are references to clique members. The pinned choices are:
  - structural: `recArgPos` per function;
  - well-founded: the per-function measure term chosen by `termination_by` or GuessLex.

  GuessLex attaches function-index measures to each function as literals:
  `.func i` becomes `if i = funIdx then 1 else 0` inside *that function's* tuple
  (`.../WF/GuessLex.lean:762-774`). Re-indexing therefore happens automatically when the measure
  travels with its function.
- **M.3, classes and order.** §2.2–2.3 applied to specifications, with "constructors" replaced by
  "value and pinned choices".
  - **Phase A decision proposed (Q8, §8):** the pinned choices compare *last*. A GuessLex or
    `recArgPos` tie-break that differs between presentations then changes the order only when
    everything else ties.
  - Matchers in values are compared by address. Original matchers are content-canonical; only their
    owning name follows elaboration order (`src/lean/Lean/Meta/Match/Match.lean:1074-1122`, per MUT
    §1.6) [measured: MUT, F9 `names.tsv`].
- **M.4, canonical clique.** One representative per class, in canonical order, with member
  references redirected to the representatives.
- **M.5, canonical elaboration.** **Defined as the output of Ix's repacking function** (§5), which is
  the plan's Δ8. Lean's pre-definition pipeline run on the canonical twin is the oracle.
  - Structural: the packing within each type former in canonical order (`Positions.groupAndSort`,
    `.../Structural/Basic.lean:59-66`); fixed parameters from the first canonical member
    (`.../FixedParams.lean:256-299`).
  - Well-founded: `PSum` summands in canonical order, Lean's per-function measures, and re-stated
    decreasing obligations.
  - `partial_fixpoint`: `PProd` factors in canonical order.
  - New constants carry the reserved `_ix` component (D14).
- **M.6, changed clique.** A clique is changed when any of these holds:
  - Lean's clique order differs from the canonical order;
  - a class has two members;
  - the clique ranges over a changed inductive block.

  Lean's clique order is Tarjan's DFS push order from the first member in source order
  (`src/lean/Lean/Util/SCC.lean:69-106`, per MUT §1.1).

### 2.8 The Phase A decisions, with reasons

| Decision | Today | Phase A | Reason |
|---|---|---|---|
| Level comparison | syntactic (`CompileM.lean:1983-2009`) | after `canonUniv`, parameters by position | collapse = equal compiled content; no level-spelling dependence (§2.2) |
| Seed order | blake3 of the name (`Ix/Environment.lean:148-153`; `compile.rs:3734`) | Lean's `all` order restricted to the component; `EqnInfo.declNames` order for cliques | name-free. The seed affects only the order inside a class, i.e. metadata (§3.3) |
| Representative | least name hash (`compile.rs:4318-4330`) | first member of the class in seed order | equal content within a class (§2.4); metadata only; no name dependence. Lean's order is what a user expects as "the" name |
| Address use | first differing external (§2.3) | `(k₀, k₁)`: addresses only on full `k₀`-ties | format-version independence except on full ties |
| Kind tag | Lean: none (C1) | definition < inductive < recursor | antisymmetry on all inputs (§3.4) |
| Cache | Lean: unnormalised (C2) | stored for `(min, max)` with the result reversed when swapped, as in Rust | required once the seed is not name-sorted (§3.4) |
| Nested order | structural sort | discovery order over the canonical block (§2.5) | equals Lean on identity blocks; address-free |
| Packaging | one block per auxiliary kind | one constant per auxiliary (D6) | minimality; 382 + 28 packaging-only differences [measured, CEN:27] |

---

## 3. The comparator is a total preorder

### 3.1 What runs today

| Element | Lean | Rust |
|---|---|---|
| Level order | `compareLevel`, `Ix/CompileM.lean:1983-2009` | `compare_level`, `compile.rs:3153-3205` |
| Expression order | `compareExpr`, `CompileM.lean:2054-2140` (well-founded on `compareExprSize`) | `compare_expr`, `compile.rs:3232-3365` |
| Strength | `SOrder` with `cmp`/`cmpM`/`zipM` (`Ix/SOrder.lean:6-60`) | `SOrd::try_compare`/`try_zip` |
| Kind dispatch | `compareConstBody`, `CompileM.lean:2215-2224` | `compare_const`, `compile.rs:3597-3623` (tag order `:3586-3592`) |
| Cache | `cmpCache : HashMap (Name×Name) Ordering` (`CompileM.lean:156`), key `comparisonCacheKey` (`:2147-2151`), strong results only (`:2163-2177, 2226-2236`) | `cache.cmps`, key `(min,max)` with `reversed` flag (`compile.rs:3442-3459, 3602-3622`) |
| Sort | natural merge sort `sortByM` (`Ix/Common.lean:122-199`) | top-down merge sort `sort_by_compare` (`compile.rs:3667-3721`) |
| Grouping | `groupByM` of adjacent `eqConst` (`Common.lean:211-219`) | `group_by` (`compile.rs:3640-3665`) |
| Refinement | `sortConstsLoop`/`sortConsts` (`CompileM.lean:2315-2342`), groups re-sorted by name (`:2290-2299`) | `sort_consts` loop (`compile.rs:3739-3787`), groups keep the stable order |
| Seed | name-hash order (`CompileM.lean:2272-2286`, `Ix/Environment.lean:148-153`) | `sort_by_key(name)` (`compile.rs:3734`), the same hash order |

Context: `MutConst.ctx` (`Ix/Mutual.lean:109-121`), rebuilt at every round from that round's classes
(`CompileM.lean:2320`; `compile.rs:3744`).

### 3.2 At a fixed context, the key is a total preorder [argued]

Fix a round's context `ctx`. Then `cmp_ctx` is a lexicographic comparison of finite trees, and each
leaf is compared by a total preorder.

**Leaves:**
- binder index: `Nat`;
- level trees under positional parameters: a lexicographic tree order with tag order
  zero < succ < max < imax < param;
- literals: the derived order on literals;
- semantic contracts: `orderKey : Nat`, injective on decodable contracts
  (`Ix/SemanticContract.lean:43-53`);
- constant references: the map `κ(n) = (0, ctx n)` when `n` is in the block, `(1, addr n)` otherwise.
  A total preorder on names; equal names have equal `κ`.

**Inner nodes:**
- a node is first ordered by its tag (the fixed tag order of §2.2);
- equal tags compare their children left to right;
- lists (`zipM`, `try_zip`) compare lexicographically, a shorter list first.

**`mdata`:**
- non-semantic `mdata` is removed before comparison, on either side and in any combination of
  wrapping;
- semantic `mdata` is a node whose tag exceeds every other tag. Lean checks it first:
  `Ix/CompileM.lean:2061-2081`; Rust: `compile.rs:3249-3279`.

A lexicographic product of total preorders is a total preorder. Its equivalence is equality of the
normalised trees under `κ`. Reflexivity, transitivity and totality follow by induction on
`compareExprSize x + compareExprSize y`, the comparator's own termination measure
(`CompileM.lean:2136-2140`).

**The kind dispatch** must be the tag order for this to extend to members: Rust does this; Lean does
not (C1).

**Strength.** A result is *strong* when no leaf read through `ctx`'s indices contributed to it:
- `cmp ⟨true, eq⟩ y = y`;
- `cmp ⟨false, eq⟩ y = ⟨false, y.ord⟩`;
- a first non-equal component is returned with its own strength (`Ix/SOrder.lean:12-25`).

So a strong result is the same under every context of the same block [argued]: the in-block versus
external split is fixed, and only the class indices vary. Caching strong results across rounds is
therefore sound, **provided the cached value is read back in the orientation it was stored in** (C2).

### 3.3 The refinement computes the coarsest consistent partition, and its class order does not depend on the seed [argued]

**(a) Every round splits correctly.** At round `n` the context is fixed, so `cmp_n` is a total
preorder (§3.2). A correct merge sort followed by grouping of adjacent equals then yields exactly the
equivalence classes of `cmp_n` on that class, ordered by `cmp_n`.
- Equal elements are contiguous after sorting.
- Every adjacent output pair of a merge sort was compared directly (by induction over merges), so
  `groupBy`'s comparisons are among the sort's.

**(b) The result is the coarsest partition.** Let `Q` be any consistent partition. Assume `Q` refines
`classes_n`.
- Two `Q`-equivalent members have equal keys under `Q`'s class map.
- `classes_n`'s map factors through `Q`'s, so their keys are equal under `classes_n` too.
- So they stay together in `classes_{n+1}`.

`classes₀ = {K}` is refined by every `Q`, so by induction every `classes_n` is.
- At the fixed point, members of one class are `cmp`-equal under the final context, so the final
  partition is consistent.
- Being refined by every consistent `Q`, it is the coarsest. This is old plan Prop 2.1.

Termination:
- every non-final round increases the class count, which is at most `|K|`;
- so at most `|K|` rounds run, and `|K| + 1` fuel suffices (`CompileM.lean:2310-2314`).

**(c) The class order does not depend on the seed.** By induction on `n`: the ordered list of classes
at round `n`, each class as a *set*, is a function of the content alone.
- Base: `classes₀` is one set.
- Step: the context's index of a member is the position of its *class*, a function of the ordered
  set-list.
  - Constructor offsets depend on the classes' maximum constructor counts, again content.
  - Within one class, `cmp_n` is a total preorder that depends only on content and the context. So
    the ordered list of its equivalence classes does not depend on the input order of the class.
  - The concatenation keeps the old order of the classes.

The seed determines only the order of members *inside* each set: stable sorts preserve input order
among ties. Lean also re-sorts groups by name (`CompileM.lean:2296-2299`); Rust does not
(`compile.rs:3772-3783`). Both therefore keep seed order inside a class, and the Rust comment's worry
about a "name-dependent canonical order" does not arise. Inside a class the order selects only the
representative, which is metadata (§2.4).

Hence the partition and the class order are seed-independent, and the representative is the only
seed-dependent output [argued].

### 3.4 Where transitivity or antisymmetry could fail

| # | Site | Property at risk | Lean | Rust | Reachable on Lean input? | Fix in A2 |
|---|---|---|---|---|---|---|
| C1 | kind dispatch | antisymmetry | `compareConstBody` returns `lt` for **every** pair of different kinds: `.defn _, _`, `.indc _, _` and `.recr _, _` all give `lt` (`CompileM.lean:2215-2224`), so `defn < indc` and `indc < defn` | tag order (`compile.rs:3586-3592, 3618`) | No. SCCs are kind-homogeneous (§2.1) and `MutConst`s are built per SCC (`CompileDriver.lean:82-90`) [argued] | tag order, as Rust |
| C2 | cache orientation | antisymmetry: a cached `lt` read back for the swapped pair | key `(min,max)` by name hash, but the value stored is `ord` of the *call's* orientation, and the read returns it unchanged (`CompileM.lean:2147-2151, 2163-2177, 2226-2236`) | normalised: `stored = reversed ? ord.reverse : ord` and the read is reversed back (`compile.rs:3442-3459, 3602-3622`) | **Not today** [argued]. Every class handed to `sortByM` is in name-hash order. `sortByM` (runs, then merges of adjacent runs) only calls `cmp a b` with `a` earlier in the input (`Common.lean:122-199`), so the call orientation equals the key orientation. `groupByM` calls `eqConst later earlier` (`Common.lean:211-215`), but only on adjacent pairs that the sort already compared (§3.3(a)): a strong pair is a cache hit whose sign `eqConst` ignores, and a weak pair is never stored. The constructor cache (`:2163-2177`) inherits its parent's orientation. **Reachable as soon as the seed is not name-sorted:** a name-free seed makes the call orientation differ from the key orientation | store normalised, as Rust |
| C3 | strength flag | soundness of caching | `SOrder` (`Ix/SOrder.lean:12-60`) | `SOrd` | — sound (§3.2) [argued] | none |
| C4 | syntactic levels | not a preorder failure: minimality, and order follows level spelling | `CompileM.lean:1983-2009` | `compile.rs:3153-3205` | in principle yes; library population unmeasured [open] | compare `canonUniv` forms (§2.2) |
| C5 | address interleaving | not a preorder failure: order depends on the format version beyond full ties | `CompileM.lean:2098-2104, 2129-2133` | `compile.rs:3210-3227, 3344-3356` | yes: 1/16 member and 4/33 nested sorts in Mathlib involve addresses [measured, CEN Q5] | `(k₀, k₁)` (§2.3) |
| C6 | `is_rec`, `is_unsafe` | Lean/Rust parity, not order | absent (`CompileM.lean:2181-2192`) | first keys (`compile.rs:3468-3471`) | No, if both flags are uniform across Lean's block [argued for `isUnsafe`: Lean blocks share safety]. Whether Lean's `InductiveVal.isRec` is block-wide is [open] (the C++ kernel is not in the local tree). A split member keeps Lean's flag in either case | the canonical key compares content only. The Rust catch-up drops both keys, or computes them on the Ix block |
| C7 | constructor indices in `ctx` | none at a fixed context | `Mutual.lean:109-121` | same | constructor references never occur in Lean member or constructor types [argued] | none |
| C8 | semantic `mdata` | totality | orderKey, then body | same | Ix-internal only (source contracts) | none |
| C9 | declarative "fixed point" | uniqueness of the specification | — | — | yes, as a definition (§2.3) | define the order as the procedure |
| C10 | stopping rules | agreement | count unchanged | list unchanged | agree, since refinement only splits [argued] | none |

**Verdict.**
- At every round, the key restricted to one SCC of Lean input is a total preorder, in both
  implementations [argued].
- The fixed point is the coarsest consistent partition. Its class order does not depend on the seed;
  only the representative does [argued].
- C1 and C2 are defects of the Lean port that today's inputs do not reach. Both are fixed in A2's
  migration commit, and neither fix moves a byte: C1 is unreachable, and C2 is unreachable under
  today's seed. The fix for C2 is a precondition of the name-free seed.
- C4 and C5 are not preorder failures. They are the canonical-form changes Phase A already decided,
  and both move addresses. C4 moves them where level spellings differ inside a block; C5 where
  `k₀` and `k₁` order differently.
- Whether the theory needs a further fix is [open] only for C6's flag question. It has no byte effect
  either way.

### 3.5 Phase A's comparator, stated for Phase B

`cmpA_ctx(x, y) := lex(k₀_ctx(x, y), k₁_ctx(x, y))`, where:
- both keys are §3.2's comparison with levels replaced by `canonUniv` forms and the kind tag first;
- `k₀` maps every external constant to one leaf value `(1, ⋆)`;
- `k₁` maps it to `(1, addr)`.

Both keys are total preorders, and a lexicographic pair of total preorders is one [argued]. The strong
flag is computed per key as today. A result is strong iff both components are strong, or the first is
strong and non-equal.

Phase B's L1 statements:
- (i) `cmpA_ctx` is a total preorder for every `ctx`;
- (ii) the refinement terminates and returns the coarsest `cmpA`-consistent partition;
- (iii) the ordered partition is invariant under permutation of the input list;
- (iv) the canonical declaration of a class is invariant under the choice of representative.

### 3.6 The exhaustive test (A1 study; A2 gate)

**Corpus:**
- every fixture block and clique: the whitebox (28) and blackbox (10) reproducers with their
  neighbours, and the ~120-namespace shape matrix;
- every library block with two or more classes (16 member sorts and 33 nested sorts in Mathlib's
  closure [measured, CEN Q5]).

**Legs:**
1. **All permutations.** For every block with `|K| ≤ 7` (5,040 presentations), every permutation of
   its members in Lean's `all`, re-elaborated as Lean source.
2. **Random presentations.** For larger blocks (Cutsat has 12 members), 1,000 random presentations
   per block. Each draws a member permutation and a renaming of members, constructors and binders.
   A presentation may also respell universe levels (`max u v` ↔ `max v u`, `succ (max …)` forms)
   and split its components into separate declarations with the block's universes, parameters and
   sort.
3. **Seed sweep, no recompilation.** On each block's prepared `MutConst` list, run the refinement
   under the identity, reverse, name-hash and ten random seeds. Require identical class lists, as
   sets, in identical order.
4. **Property check per round.** At every round of every run, evaluate `cmpA_ctx` on all ordered pairs
   and triples of the class being refined. Require reflexivity, antisymmetry up to equality, and
   transitivity, with the cache on and off. For `|K| ≤ 12` this costs at most 1,728 triples per round.
5. **Compile and compare.** For legs 1 and 2, compile each presentation and require all of:
   - the Ix block bytes and every Ix auxiliary are identical;
   - `N` sends corresponding names to corresponding canonical positions;
   - every other constant is byte-identical except the entries of the residue fixture (§7.2).
6. **Lean/Rust.** Run the seed sweep on Rust's `sort_consts` through `rs_compile_phases` until the
   catch-up PR; it gates the Rust port of `(k₀, k₁)`.

**Failure policy.** Any failure of leg 3 or leg 4 is a comparator defect and stops A2. A leg 5
difference outside the residue fixture is a canonicity defect of a later pass.

---

## 4. The image construction

For each Lean recursor `r` of a changed block (Def 3.1), Pass 3 builds an **image** `img(r)`: a
closed Ix term with Lean's type `tr_N(type r)` that computes as `r` does. The image is built from the
*types* of the Ix recursors and from the specifications. It uses no reduction, unlike the prototype,
which used `MetaM` (`plans/review/auxgen-certify/exp-prototype/CertProto/Lib.lean`, 516 lines; A3
re-implements it as a generator over kernel terms).

### 4.1 Eliminator choice (Def 3.3)

Let `t` be a Lean motive type: a member or an auxiliary, at parameters `ps`. Then `elim(t)` is the
first Ix recursor whose motive types contain `tr_N(t)` at some slot `j`, taken from these candidate
lists in order:
1. the recursors of the Ix blocks occurring in `tr_N(t)`, nested auxiliaries included;
2. the recursors of the other inductives occurring strictly inside `tr_N(t)`, outermost first;
3. the recursor of `tr_N(t)`'s head.

The prototype's `findElim` (`Lib.lean:184-219`) takes the candidates of list 2 in the order of
`Expr.getUsedConstants`, which is first occurrence in a pre-order walk, at the parameters of the first
occurrence (`T.find?`). A3 uses that exact rule, which makes "outermost first" precise.

The order matters because it makes the choice *consistent*: if `t′` is a recursive field of a
constructor of `t` and `elim(t)` has `t′` among its motive types, then `elim(t′) = elim(t)`
[argued]. Choosing the head first breaks this: `List (Rose B)` would get `List.rec` instead of
`Rose.rec_1`, and the computation rules then fail [measured: PRO correction 1, ablation `C4b-naive`
rejected at `A2.rec_1.iota_node`, plus 4 `.go`, 4 `.eq` and `_sizeOf_3_eq`].

### 4.2 The image of a recursor (Def 3.4)

Fix `r` with parameters `ps`, motives `m₁ … m_M` over Lean motive types `t_i`, minors, indices `is`
and major `x : t_maj`. Let `ρ = elim(t_maj)` have motive slots `1 … K`.

**Step 1: slot classes.** For each slot `j`, `C_j` is the set of Lean motives `i` with
`elim(t_i) = ρ` and `tr_N(t_i)` at slot `j`, listed in Lean's order. The prototype finds it by
comparing *stripped* motive types, with the sort replaced by `Sort 0` (`Lib.lean:125-129, 245-246`).
- Every slot has a non-empty class [argued: Lean's nested expansion is closed under the
  containers' own expansion; measured: PRO, 38/38 images built].
- The prototype throws when a class is empty (`Lib.lean:247-248`); A3 does the same, as an error
  naming the block.

**Step 2: the level.** Let `u` be the universe of Lean's motives (`motiveLevel`, `Lib.lean:131-134`).
- If some `|C_j| ≥ 2` and `u` is not always zero, instantiate `ρ` at `ℓ := max 1 u`, normalised.
  Otherwise `ℓ := u` (`Lib.lean:249-251`).
- **Prop member that gained large elimination:** if `ρ` has an elimination universe and Lean's `r`
  does not, then `u = 0` and `ℓ = 0`. This instantiates `ρ.{0}`.
- If `ρ` eliminates only into Prop while `ℓ ≠ 0`, it is an error (`Lib.lean:255-256`). This never
  happens [argued: splitting and collapsing only remove the conditions that restrict elimination].

**Step 3: packing each slot.**
- *single* (`|C_j| = 1`, and no lift needed): the motive is `m_i`, η-contracted (`Lib.lean:265-271`).
- *tuple* (`|C_j| = k ≥ 2`): the motive is `λ ys. m_{i₁} ys ×' … ×' m_{i_k} ys`, nested to the right.
  - `PProd` is used at level `ℓ`; `And` replaces it exactly when Lean's motives are propositions
    (`PProdN.pack`, `src/lean/Lean/Meta/PProdN.lean:94-114`).
  - [measured: PRO, C3b and C7 at level 0.]
- *lifted* (`|C_j| = 1`, but some other slot is a tuple and `u` is not always zero): the motive is
  `λ ys. PProd.{u,0} (m_i ys) True`, of sort `Sort (max 1 u)` (`Lib.lean:227-238`).
  - Without the lift, `ρ.{max 1 u}` cannot take a `Sort u` motive.
  - [measured: PRO correction 2. Ablation `C8-nolift`: all 3 transports and 70 dependents
    rejected. `PLift` lands in `Type u`, also rejected.]
- **Unwrapping.** `unwrap_p` projects component `p` of a tuple (`PProdN.proj`, primitive `.proj`
  projections: `PProdN.lean:55-79, 123-145`), takes `.1` of a lifted slot, and is the identity on a
  single slot (`Lib.lean:221-225`).

**Step 4: minors.** For each Ix minor of slot `j` and its constructor `c`, with fields `fs` and Ix
hypotheses `ihs`:
1. For each `i ∈ C_j`, take Lean's minor for `(i, c′)`, where `c′` is the Lean constructor that
   corresponds to `c` by position (`Lib.lean:296-300`).
2. Apply it to `fs`, then to one hypothesis per Lean IH binder. For a binder over field `f` with Lean
   motive type `t′`:
   - **if `f` has an Ix hypothesis** (it is recursive for `ρ`): take `unwrap_pos (ih ys)`, where
     `pos` is the position of `t′` in the hypothesis's class (`Lib.lean:311-315`);
   - **otherwise: a relocated hypothesis.** Take the image construction for `t′` applied to `f` and
     its indices: an explicit call of `elim(t′)`, another Ix recursor, with Lean's motives and minors
     (`Lib.lean:316-318`, recursive, under the reflexive binders `ys`). This covers the split case and
     the evaporated case.
3. Pack the results of all `i ∈ C_j` like the motive: `v`, `⟨v₁, …⟩`, or `⟨v, True.intro⟩`
   (`Lib.lean:234-238, 322`). Then η-contract (`Lib.lean:324`).

**Relocation terminates** [argued, old plan Prop 3.1 lemma]. A relocated field's type lies either in
an Ix block strictly below `ρ`'s block in the condensation DAG, or in a container instance finitely
nested in the field type. The prototype's fuel of 64 (`Lib.lean:241, 355`) becomes a structural
recursion on (DAG height, nesting depth) in A3.

**Step 5: the result.**
`img(r) := λ ps ms mins is x. unwrap_{pos(t_maj)} (ρ.{ℓ, us} ps motives′ minors′ is x)`
(`Lib.lean:325-327`), followed by the development of §4.3.
- The prototype applies `Core.betaReduce` to the whole term (`Lib.lean:357`), plus `.eta` on each
  motive and minor.
- The levels `us` are the block's universe arguments, after `canonUniv`. Under D3/D16 the level
  selection σ is the identity.

**Composition.** Def 3.4 computes the image of `τ_order ∘ τ_collapse ∘ τ_split` directly. Nothing
downstream depends on how an image was built: it is checked by its type and its computation rules.

**What is established.** Images are well typed, and Lean's computation rules hold against them:
- old plan Prop 3.1 and Prop 3.2 [argued];
- 38/38 images typed at Lean's type and 62/62 iota rules by `Eq.refl` in Lean's kernel, over 15
  sub-cases: permutation, split with and without a cross field, Prop split and collapse, evaporated
  `List`, `Rose`, collapse, nested collapse, `IndPredBelow`, mixed class, parameters, universes and
  reflexive fields [measured: PRO, `out/results.tsv`].

### 4.3 The development

Substituting an image term creates redexes. "Develop" means: contract exactly the redexes that the
construction or the substitution created, and leave every redex the user wrote. Precisely:

1. **At the image (P3a).**
   - Contract the β-redexes formed by applying the image's own motive and minor λs.
   - Contract the η-redexes `λ ys. m ys` and `λ fs ihs. g fs ihs` that the construction produced.
   - These are a finite set and their residuals, so a complete development, which is finite by the
     finite-developments theorem.
2. **At a call site (P3b, §4.5): hereditary substitution.** The occurrence `img(a) args` with
   `|args| ≥ arity(img a)` is replaced by `body[params := args]`.
   - Wherever a parameter that received a λ-argument occurs at the head of an application inside
     `body`, the created β-redex is contracted, and so on hereditarily.
   - So are projection-of-constructor redexes `(⟨a, b⟩).1 ↦ a` (`PProd`, `And`), and η-redexes,
     created at those positions.
   - Termination [argued]: each hereditary step substitutes at a strictly smaller type, namely a
     motive's or minor's codomain, which is finitely nested in Lean's recursor type.
   - Redexes inside the user's arguments are not touched unless the substitution itself formed
     them.
   - ι-redexes are **not** contracted. `ρ … (c fs)` arising from a user-written `T.rec … (c fs)` is a
     residual of the user's redex.

The development is part of the canonical form, because O1–O6's outputs must equal the twin's terms
[measured: 53/53 on DQReord, a pure permutation, where the rewrite creates no λ-substitution]. A3 must
pin the hereditary rule with fixtures in which the user's motives and minors are λs (they always are
when elaborated from `match` or `induction`) and compare against the twin.

### 4.4 The two prototype corrections

1. **Container rule.** A nested Lean type is eliminated with the outermost block that has it as a
   motive type: canonical blocks first, then containers inside the type, then the head (§4.1). For
   `List (Rose B)`: `Rose.rec_1`, not `List.rec` [measured: PRO correction 1].
2. **Mixed collapse class.** When some slot is a tuple at `max 1 u`, every singleton slot of the same
   eliminator is lifted with `PProd (m x) True` (§4.2, step 3) [measured: PRO correction 2].

A third rule, `And` exactly at Prop motives, was in the design already and was confirmed [measured:
PRO].

### 4.5 Call sites: inline rewrite or image constant

For every occurrence of a Lean auxiliary `a` of a changed block in a compiled constant. `a` ranges
over `rec`, `rec_N`, `recOn`, `casesOn`, `below*`, `brecOn*`, `.go`, `.eq` and `_N`.

- **Fully applied** (at least the image's arity in arguments): **inline**. Replace the occurrence by
  `img(a)`'s body with the arguments substituted, then develop (§4.3). Arguments beyond the arity stay
  applied. Nothing is dropped:
  - every motive and minor Lean supplied appears in the result, permuted, paired or relocated;
  - O7/O10/O12 are the only passes that may later remove duplicates, and only under their side
    conditions.
- **Bare or partial** (`def r := @A.rec`, `List.map A.casesOn`, `@f._mutual`): reference the
  **image constant** `img(a)`.
  - It has Lean's type exactly and is a λ over Lean's telescope, so it *is* the eta adapter. A
    partial application `img(a) a₁ … a_k` is well typed with Lean's type, and no separate adapter
    constant is generated.
  - The alternative, an inline η-expansion `λ ys. inline(a, args ++ ys)`, duplicates the image per
    occurrence and is no more canonical: the type is Lean's, which follows the grouping. It is not
    used (Q11, §8).
  - An image constant referenced after the engine's fixed point is a **residual image**: an ordinary
    constant of `E`, flagged in metadata, with provenance in `Named.original`.
  - Library population: 0 bare or partial applications in Init+Std, Lean, Batteries and Mathlib
    [measured: CEN:33].
- **`casesOn` and `recOn` keep Lean's arity.**
  - The Lean names are images, so their types are Lean's.
  - `casesOn` has one motive and its own constructors' minors, so its image is the Ix `casesOn` of
    the class with the same arguments (O3).
  - `recOn` takes all of Lean's motives, so its image goes through `img(rec)` (Def 3.5).

### 4.6 Lean's other auxiliaries over images (Def 3.5) and the baseline (Def 3.6)

**Def 3.5.** For a Lean auxiliary `a` of a changed block that is a definition or a theorem,
`img(a) := tr_N(value a)` with every reference to an auxiliary `a′` of a changed block replaced by
`img(a′)`. The kinds are `casesOn`, `recOn`, `below`, `below_N`, `brecOn`, `brecOn_N`, `.go` and
`.eq`.
- No regeneration over images is needed: 836/836 of Lean's other auxiliaries, copied verbatim under
  renaming, type-check over the images [measured: PRO claim 2].
- The kinds covered: `casesOn`, `recOn`, `below*`, `brecOn*` with `.go`/`.eq`; matchers, splitters,
  `match_N.eq_N`; `_sparseCasesOn` and `.else_eq`; the `noConfusion` family; `inj`/`injEq`;
  `ctorIdx`/`ctorElim`; the `sizeOf` family; `eq_N`, `eq_def`, `_f`, `_sunfold`, `_unsafe_rec`.
- Two copying details apply. Private splitter names are renamed through `privateToUserName?`
  (`Lib.lean:47`). Mutual `_unsafe_rec` definitions are added together as one `mutualDefnDecl`
  (`Lib.lean:403-410`).

**Lean's `IndPredBelow` families of a changed Prop block** are inductive types, so they have no
closed-term image. They are compiled as blocks by Passes 1–3, are themselves canonicalised, and get
images when changed (old plan §2.9). They are the one non-canonical, non-image kind of constant in
`E`.
- The prototype's single checker reject came from this (PropSplit inside the view: PRO claim 6,
  caveat 1).
- None exist in the measured libraries [measured: CEN:24, 0 Prop members gaining large elimination;
  Mathlib has 0 Prop-valued nested inductives, `polish/nestedprop/README.md`].

**Def 3.6, baseline.** For every other constant `c`, `base(c) := tr_N(c)` with every reference to an
auxiliary of a changed block replaced by its image, inline at full applications (§4.5).
- Theorem statements are translated exactly.
- `base(c)` is well typed whenever Lean's derivation of `c` unfolds no theorem [argued: old plan
  Prop 3.3].
- A derivation that unfolds a theorem has no Ix counterpart. This is a *certification* totality
  failure: the checker rejects or declines. The compiler cannot detect it (A Δ11).

### 4.7 The six ways a split differs from Lean's elaboration, and their Phase A treatment

From ORA, split row [measured], on `SurgSplit`, `DQSplit`, `DQMut`, `EvapClosure`, `NestRoseSplit`,
`PropSplit`, `SurgIdx`, `UnivSplit` and `Grind.Arith.Linear`:

| Cause | What differs | Phase A |
|---|---|---|
| (a) | The split member keeps the block's universe list (`UnivSplit`: `lvls = 1` against `0`) | By design (D3/D16, §2.4). Recorded as faithful but not canonical against a separate declaration with fewer universes; not a residue entry, since Def 4.3 excludes such presentations |
| (b) | `below`/`brecOn` generated for a split member that is no longer recursive | Fixed. Pass 2 decides existence by Lean's conditions on the Ix block (old plan Def 2.7), never by names or by the Lean block |
| (c) | Lean's `noConfusion` takes the enumeration form only for `numTypeFormers == 1 && !isRec` (`src/lean/Lean/MonadEnv.lean:198`, per ORA) | Lean's form compiles by baseline (faithful); O11b rewrites users onto the canonical `noConfusion` (proof-justified) |
| (d) | Lean's mutual `_sizeOf_N` inlines the block recursor, while the separate form goes through the instance | Baseline; O11a if one `rfl` on `Linear.EqCnstr` confirms it is definitional [open] |
| (e) | Leftover reference and sharing-table entries from dropped arguments change addresses | Removed by construction. P3 builds each term afresh and P5 derives the tables from the final term only (`preseedExprTables`, `Ix/CompileM.lean:1672-1690, 1929`) [argued; v4 sharing was rewritten in `1965df06` and this was not re-measured, D §3.2] |
| (f) | Open defects: SurgSplit (wrong IH projection), PropSplit (missing universe), SurgIdx (eta adapter) | Retired with surgery (A3). Images take the IH projection from the slot class (§4.2, step 4), the universe from the level rule (step 2), and partial occurrences from the image constant (§4.5) |

Two neighbouring findings:
- For user structural recursion over a split block, the only term difference is the path into
  `below` (`x_below.2.1` against `.1`) plus the leftover entries [measured: ORA §3, `A.len._f`]. That
  is O9's re-pathing.
- For collapse, functions cannot agree with the twin by rewriting [measured: ORA §3; PRO, B2 table].
  That is O10/O12's territory.

---

## 5. Transport of proof terms

### 5.0 The common frame

**Setting.**
- A changed clique has Lean order `f_0 … f_{n-1}`, which is Tarjan order (M.6).
- The canonical order is given by `σ : Fin n → Fin n`: Lean index `i` goes to canonical position
  `σ i` (M.3).
- Lean's pre-definition pipeline encodes the clique as `Enc_L`. The canonical elaboration (M.5) is
  `Enc_C`: the same encoding run on the canonical order, with Lean's pinned choices.
- **Transport** is a map `Φ_σ` from terms in the image of `Enc_L` to terms of `Enc_C`.

`Φ_σ` is the identity on every subterm the encoding did not generate: user bodies, external
constants, and the per-function data the encoding carries along with each function (measures,
`recArgPos`, arities). It acts by four kinds of step:

| Kind | What it does | Example |
|---|---|---|
| **(R) renaming** | Lean's encoding constants become canonical ones with the `_ix` component | `f₀._mutual ↦ g._ix._mutual`; `_mutual.proof_k ↦ proof′_k`; transformed `match_N ↦` canonical transformed matcher |
| **(A) re-association** | right-nested `PSum`/`PProd` types, their introductions and eliminations are rebuilt for the order `σ` | `PSum a (PSum b c) ↦ PSum b (PSum a c)`; `inr (inl v) ↦ inl v`; case trees with leaves moved; projection paths `.2.1 ↦ .1` |
| **(S) re-statement** | an obligation whose statement mentions the packing becomes the obligation over the canonical packing | `∀ ctx, rel (inj_b ⟨…⟩) (inj_a ⟨…⟩) ↦ ∀ ctx, rel′ (inj′_{σb} ⟨…⟩) (inj′_{σa} ⟨…⟩)` |
| **(G) regeneration** | a sub-proof whose *shape* depends on a projection path is rebuilt by Lean's own deterministic recipe for the new path | the monotonicity proof of `f.2.1` against `f.1` (§5.2) |

**No encoding is a pure renaming.** All three use (A), because the packing nests binary type formers
and a permutation changes the nesting depth of a summand or factor. Well-founded recursion adds (S);
`partial_fixpoint` adds (S) and (G).

**Why `Φ_σ(p)` proves `Φ_σ(T)` when `p : T`** [argued]:
- `Φ_σ` is a homomorphism on term structure, except at encoding-generated constructs.
- At those it maps each construct to the corresponding construct of `Enc_C`: a type former to a type
  former, an introduction to an introduction, an elimination to an elimination.
- So every typing-rule instance in `p`'s derivation maps to an instance of the same rule.
- Every conversion step that involves the encoding maps to the same kind of step: ι of a case tree on
  an injection, projection of a tuple, δ of an encoding constant.
- (G) replaces a sub-proof by another proof of the *mapped* sub-statement.

**Precondition: the grammar.** Every occurrence of an encoding type in `p` must be in a recognised
position: one of the constructs above, or a copy of a statement produced by the encoding. A
recogniser decides this. When it fails, the fallback of each encoding applies, and the constant is a
residue entry with cause `SHAPE` (§7.2).

**Faithfulness never depends on transport.**
- Theorem statements and definition types are translated exactly.
- A transported proof is a proof of the canonical obligation.
- The correspondence between a canonical member and Lean's member is O14–O16's business, not
  transport's.

### 5.1 Well-founded recursion

**Lean's encoding** (4.34.0, `src/lean/Lean/...`):
- **Fixed parameters.** `getFixedParamPerms` (`Elab/PreDefinition/FixedParams.lean:271-301`). The
  fixed parameters appear in the *first* function's order, so the `_mutual` telescope depends on
  which function is first (`:259-263`). Under `σ` this is a permutation of binders, which is O13b
  (definitional).
- **Domain.** `α = PSum D₀ (PSum D₁ … D_{n-1})`, in clique order (`Meta/ArgsPacker.lean:248-253`).
  Each `D_i` is the `PSigma` tuple of `f_i`'s varying arguments (`:64-77`).
- **Injections.** `inj_i v = inr^i (inl v)`, or `inr^{n-1} v` for the last summand
  (`ArgsPacker.lean:270-289`).
- **Motive.** The codomain motive is a `PSum.casesOn` tree over `α` (`mkCodomain`, `:313-344`).
- **The unary function.** `packMutual` (`Elab/PreDefinition/WF/PackMutual.lean:79-104`) builds
  `f₀._mutual` (`:66-73`). Its value is `ArgsPacker.uncurry` of the bodies, a case tree with
  `PSigma.casesOn` per arity, and recursive calls are packed.
- **Relation.** `elabWFRel` builds `wfRel` from the per-function measures. Each measure is a tuple per
  function. GuessLex fills it with `measures[k].fn` and the function-index literals
  (`WF/GuessLex.lean:762-774`). The measures are combined by a case tree over `α`.
- **Fixpoint.** `mkFix` (`WF/Fix.lean:289-319`) builds one of two forms:
  - `WellFounded.Nat.fix α motive measure F` when `wfRel` is `invImage f Nat.lt_wfRel` (`:281-287,
    300-301`);
  - otherwise `WellFounded.fix α motive wfRel.1 (opaqueId wfRel.2) F` (`:302-306`).
- **Case refinement.** `F := λ x F. …`. The packed argument `x` is refined by `processSumCasesOn` and
  `processPSigmaCasesOn` (`:159-203`).
- **Recursive calls.** Each becomes `F arg h` with `h` a goal of type `rel arg x`, the binding domain
  of `F arg`'s type (`:78-87`).
- **Goals.** Goals are grouped per function by `ArgsPacker.unpack` (`:239-248`) and closed by
  `clean_wf` (`src/lean/Init/WFTactics.lean:28-31`) and `decreasing_tactic`, or by the function's
  `decreasing_by` (`Fix.lean:250-279`). Goals with equal types and nested contexts are merged first
  (`assignSubsumed`, `:216-230`).
- **Abstraction.** `addPreDefsFromUnary (cacheProofs := false)` (`WF/Main.lean:82`) runs
  `abstractNestedProofs`, which turns each decreasing proof of a *definition* into a theorem
  `f₀._mutual.proof_k : ∀ ctx, rel y x` (`Elab/PreDefinition/Basic.lean:120-128`). For a theorem,
  abstraction is skipped (`:121-122`) and the proofs stay inline.
- **Members.** `f_i := λ params. f₀._mutual fixed (curryProj … i)` (`WF/PackMutual.lean:127-143`).
- **Equations.** `EqnInfo` records `argsPacker` and `fixedParamPerms` (`WF/Main.lean:86`). Then come
  `_mutual.eq_unfold` and the per-member unfold lemmas (`:88-94`).

**Transport `Φ_σ`:**
- **(R).** `f₀._mutual ↦ g._ix._mutual`, where `g` is the first canonical member.
  `f₀._mutual.proof_k ↦ proof′_k`, numbered in the canonical traversal order; the numbering is
  metadata. References to members go through `N`.
- **(A).**
  - `α ↦ α′`, with `D_i` at summand `σ i`.
  - `inj_i ↦ inj′_{σ i}`.
  - Every `PSum.casesOn` tree over `α` becomes the canonical tree with leaf `i` at position `σ i`. The
    trees are the motive, the body's case split, the measure's case split and `F`'s refinement. The
    motives inside the trees are rebuilt by `mkCodomain`'s rule.
  - `PSigma` parts are per function and are unchanged.
  - The fixed-parameter telescope is reordered to the first canonical member's order.
- **(S).** Each `proof_k : ∀ ctx, wfRel.rel y x` becomes `proof′_k : ∀ ctx′, wfRel′.rel y′ x′`.
  `wfRel′` combines the *same* per-function measures by the canonical case tree (D22: Lean's measure,
  pinned and re-indexed). `y′` and `x′` are the canonical injections of the same tuples.
- **Proof bodies.** The value of `proof′_k` is `Φ_σ(p_k)` when `p_k` passes the grammar check;
  otherwise it is `p_k` **verbatim**.

**Why both are proofs of the re-stated obligation** [argued]. `Φ_σ(T)` and `T` reduce to the same
proposition:
- δ of `invImage`, then the `WellFoundedRelation.rel` projection, then δ of `InvImage`;
- β;
- ι of the case trees on injections, then of `PSigma.casesOn` on `PSigma.mk`.

Both end at `r.rel (m_b c⃗) (m_a a⃗)`, with `r` the same lexicographic instance (GuessLex pads every
tuple to one length). The kernel's definitional-equality check performs exactly these steps, and none
unfolds a theorem, which Ix never does. So `p_k : T` is accepted at `Φ_σ(T)` by conversion.
`Φ_σ(p_k) : Φ_σ(T)` holds by the homomorphism argument of §5.0.

What `p_k` typically contains: the cleanup is a `simp only` over definitions (`clean_wf`), and the
default tactic works on the cleaned goal, which mentions only measures. So the packing typically
occurs in `p_k` only in copies of the goal: `Eq.mpr`/`id` annotations and motives of the rewrites.
Those are recognised by the grammar [argued; the shapes are measured nowhere: open].

**Closed values.**
- On the `Nat.fix` route (single `Nat` measure), `WellFounded.Nat.fix` is a fuel-driven `Nat.rec`
  marked `@[implicit_reducible]` (`src/lean/Init/WF.lean:470-499`). Canonical and Lean members
  therefore agree on closed arguments by evaluation.
- On the `WellFounded.fix` route they never meet by conversion: `fix` goes through `Acc.rec` on a
  proof (`Init/WF.lean:125-137`).
- Either way, open arguments need O15's correspondence: `WellFounded.induction` and `fix_eq`/
  `Nat.fix_eq` once on each side (`Init/WF.lean:139-142, 513-517`) [argued, MUT §4.1].

### 5.2 `partial_fixpoint`

**Lean's encoding** (`Elab/PreDefinition/PartialFixpoint/Main.lean`):
- **Instances.** Per function, `CCPO (∀ x⃗, r_i x⃗)` (or `CompleteLattice` for `inductive_fixpoint`/
  `coinductive_fixpoint`) (`:87-113`).
- **Packing.** `packedType := PProdN.pack 0 types`, in clique order (`:125`), with
  `packedInst := mkPackedPPRodInstance` (`:135`).
- **Functionals.** `F_i := λ f. body_i`, with each recursive call replaced by
  `PProdN.proj n idx t f` applied to the varying arguments (`replaceRecApps`, `:24-30`).
- **Goals.** One per function: `monotone (α := packedType) packedPartialOrderInst type_i inst_i F_i`,
  proved by `solveMono` or by the user's term (`hints[i].term?`) (`:167-186`).
- **Combination.** `PProdN.genMk mkMonoPProd` combines the proofs with `PProd.monotone_mk`, in clique
  order (`:65-75, 187`).
- **Value.** `mkFixOfMonFun packedType packedInst hmono` gives `Lean.Order.fix`
  (`Init/Internal/Order/Basic.lean:452`). It is named `f₀.mutual` (`:189-197`).
- **Members.** `f_i := PProdN.proj n i packedType (f₀.mutual fixed) varying` (`:205-216`).

**The recursive-call sub-proofs.** `solveMonoCall` (`src/lean/Lean/Elab/Tactic/Monotonicity.lean:
84-106`) builds the monotonicity proof of a call `f.p₁….p_k a⃗` *inside out*:
- `monotone_id` for `f`;
- then one `PProd.monotone_fst` or `PProd.monotone_snd` per projection step, instantiated at that
  step's intermediate `PProd` type and instance;
- then one `monotone_apply` per argument.

**Transport `Φ_σ`:**
- **(R).** `f₀.mutual ↦ g._ix.mutual`.
- **(A).**
  - `packedType`, `packedInst` and the `PProd.monotone_mk` tree are rebuilt in canonical order.
  - In each `F_i`, `PProdN.proj n idx ↦ PProdN.proj n (σ idx)`.
  - The members project at `σ i`.
- **(S).** Each goal mentions `packedType` and `F_i`, and becomes the canonical goal.
- **(G).** In each `hmono_i`, the sub-proof for a recursive call through path `π_idx` is replaced by
  `solveMonoCall`'s recipe for the path `π_{σ idx}`.
  - The paths can have different lengths: `.2.1` against `.1`. So the number of `monotone_fst`/
    `monotone_snd` applications changes. This is regeneration, not renaming.
  - The recipe is deterministic and term-level: `whnfUntil` to the `PProd` instance, then lemma
    application. No search runs.
  - Every other part of `hmono_i` (`monotone_const`, the `ite`, `bind` and `match` lemmas of
    `solveMonoStep`) mentions the packing only as the domain and its instance, and is (A).

**Fallback** (user-supplied monotonicity terms, or anything that fails the grammar check):
`hmono′_i := monotone_compose (mono φ) hmono_i`.
- Here `φ : packedType′ → packedType` is the re-association `f′ ↦ ⟨f′.π_{σ 0}, …⟩`.
- `F′_i ≡ F_i ∘ φ` holds by β and projection of a constructor [argued].
- `monotone_compose` is at `Init/Internal/Order/Basic.lean:209` in the 4.33.1 tree that could be read;
  its 4.34 location is [open].
- `mono φ` is a `PProd.monotone_mk` tree over projection-path proofs, built by (G).
- The fallback embeds Lean's `hmono_i`, whose content follows Lean's packing. It is therefore residue
  (cause `SHAPE`), but always a proof.

**Faithfulness of the members** is O16: `Lean.Order.fix` commutes with an order isomorphism of the
product. That lemma is still to be written once, in the checker's theory or as a Lean module [open].

### 5.3 Structural recursion

**Lean's encoding** (`Elab/PreDefinition/Structural/`):
- **Grouping.** `Positions.groupAndSort` groups the functions by the type former of their recursive
  argument (`Main.lean:46`; `Basic.lean:59-66`):
  - the groups are in the inductive's `all` order, nested auxiliaries included;
  - **within a group, the functions are in clique order.**
- **Motives.** One per function (`mkBRecOnMotive`, `BRecOn.lean:213-219`). Each group's motives are
  packed by `PProdN.packLambdas`, giving `P₁ x ×' P₂ x …`, or `PUnit` for an empty group
  (`mkBRecOnConst`, `:243-260`).
- **Functionals.** `mkBRecOnF` with `replaceRecApps` (`BRecOn.lean:125-206`):
  - a recursive call becomes a path into the `below` dictionary, found by `searchPProd` over `.proj
    PProd i` and `.proj And i` (`:25-35, 120-123`);
  - under a `match`, `MatcherApp.addArg? below` creates a **transformed matcher**: a new constant
    whose type carries `below`'s type, and so the packed motives (`:186-201`).
- **`_f`.** Each functional is extracted as an `.abbrev` definition `f._f := λ xs. F_i` (`Main.lean:
  89-107`), whose *type* mentions `T.below` at the packed motives.
- **Packed functionals.** They are packed per group by `PProdN.mkLambdas` (`Main.lean:113-114`).
- **Values.** `f_i := λ ys. PProdN.projM size idx (T.brecOn_k ps packedMotives is x packedFs) rest`
  (`mkBRecOnApp`, `BRecOn.lean:289-300`).
- **Inductive predicates.**
  - The result types are let-bound as `funType_1 … funType_n` in clique order (`withFunTypes`,
    `IndPred.lean:105-120`), and the value is wrapped in them (`BRecOn.lean:300`).
  - "below" matchers are created by `IndPredBelow.mkBelowMatcher` under the function's name
    (`IndPred.lean:84-91, 150-155`).
- **Fixed parameters.** In the first function's order (`FixedParams.lean:259-263`).

**Transport `Φ_σ`.** Only the order *within a type-former group* depends on the clique. Across groups
the order is the inductive's `all` order; when the block itself changed, O4 handles it. Let `σ_k` be
the restriction of `σ` to group `k`.
- **(R).**
  - `f._f ↦ g._ix._f`.
  - Each transformed matcher becomes a canonical transformed matcher, itself transported by (A).
  - Each IndPred "below" matcher becomes a regenerated one.
- **(A).**
  - The packed motive of group `k` is rebuilt in the order `σ_k`, and so is the packed functional
    tuple.
  - The final projection `projM size idx ↦ projM size (σ_k idx)`.
  - In each functional, every path into `below` splits in two. The prefix walks the inductive's
    `below` structure for the recursive field: it does not depend on the clique and is unchanged. The
    suffix is the position inside the group's packed motive: it is re-associated.
  - The `_f` type follows.
  - `let funType_i` is re-ordered. That is ζ-equivalent, i.e. O13a, definitional.
- **No (S) and no (G).** A structural definition carries no separate proof obligation: its
  "decreasing" evidence *is* the `below` path, which is a term.

**The fallback is the baseline.** If a functional uses a packed value outside the grammar (passes a
`below` dictionary to a helper other than a transformed matcher), the whole clique keeps its baseline.
That is faithful.

**The correspondence is not definitional.** The canonical and Lean members are stuck `brecOn`
applications at a variable. It is O14: joint induction with the block's recursor, where the repacking
map on the `below` dictionaries closes each case [argued, old plan §3.5].

### 5.4 Theorems proved by mutual recursion

There are three routes:
- structural over data: the `brecOn` route, with `_f` still added;
- structural over an inductive predicate: the IndPred route;
- well-founded: the theorem `_mutual` itself, with its decreasing proofs inline because
  `abstractNestedProofs` skips theorems (`Basic.lean:121-122`).

For all three, Lean records no `EqnInfo` (§2.7).

**What transport gives.** The transported body is `Φ_σ` of Lean's body, by §5.1 or §5.3. It proves
`tr_N(φ)`, the theorem's translated statement, which never mentions the encoding [argued]. Lean's
own body proves the same statement, so **the fallback for a theorem is its baseline**, always valid.
For theorems, transport matters only for the canonicity of the theorem's address.

**What transport needs.** A canonical order for the theorem clique. Without a specification, only two
sources exist:
- (i) the statements;
- (ii) a **recovered specification**: the inverse of the encoding applied to Lean's bodies. That
  means reading recursive calls back from `F (inj_j ⟨a⃗⟩) h` for well-founded recursion, and from
  `below` paths against the packed motives for structural recursion. The result is checked by
  re-encoding it and comparing with Lean's bytes.

The recommendation (Q6, §8): (i), and then (ii) for statement ties. Fall back to the baseline, with
cause `NOSPEC`, when recovery fails.

**Equation lemmas of definitions** (`eq_N`, `eq_def`, `_mutual.eq_unfold`) have proofs that unfold
Lean's encoding. When a member maps to the canonical form, the old plan's §3.5 requirement 2 applies:
cast along the correspondence, else demote the clique, else a compile error naming the constant. The
equations are realised lazily (MUT §1.2), so which of them exist varies between builds (A Δ13). The
canonicity claim excludes them (§7.1).

### 5.5 Where two presentations can still give different transported terms

These are the residue causes the fixture must be able to record (§7.2).

| Cause | Mechanism | Encoding |
|---|---|---|
| `TACTIC-ASYM` | Lean's proof for presentation `P₁`, transported, differs from Lean's proof for `P₂`, because the tactic's output depends on the order beyond the packing. Candidates: user `decreasing_by` or monotonicity scripts that depend on goal order *across* functions; `simp` traces when the goal still contains packed structure; proof terms mentioning the packed type through generic lemmas (`PSum.inr.injEq`, `sizeOf` of a `PSum`). Goals are grouped per function (`Fix.lean:239-248`) and merged only when their types are equal (`:216-230`), so the default path is symmetric [argued] | WF, `partial_fixpoint`, theorems |
| `SHAPE` | The grammar check fails, so the fallback (verbatim proof, composition with `φ`, or the baseline) carries Lean's packing in its content | all |
| `GUESSLEX` | GuessLex enumerates measure combinations in function order, uniform ones first; function-index measures `.func i` come last, in index order; it takes the first that works (`GuessLex.lean:524-629`). Two presentations may pick different per-function tuples. Pinning (D22) keeps each faithful, but the canonical functionals then differ | WF |
| `RECARG` | Structural `allCombinations` takes the first working combination in clique order (`FindRecArg.lean:228-310`, per MUT §1.2) | structural |
| `ORDER-STMT` | Statements that follow the order: `_mutual.eq_unfold`, `mutual_induct`, `induct`, bare `@f._mutual`. These are faithful only | all |
| `NOSPEC` | A theorem clique whose order cannot be determined (§5.4) | theorems |

The numbering of `proof_N`, `match_N` and `_f` names, and which declaration owns a shared matcher,
are names only. They are metadata, not residue.

### 5.6 What is measured about cliques

Measured:
- Structural cliques with one function per type former are already canonical under reordering
  [measured: ORA, DQReord 53/53 including the theorem; MUT §1.7: `M2_T_cyc_fun__p1`,
  `M2_T_alpha_fun__p1`, `M3_T_ring_fun__p1…p5` with equal address multisets].
- An inductive-predicate structural theorem clique is not canonical today: the "below" matchers
  differ in content, and so do `A.two` and `B.two` [measured: MUT, F9 `M2_P_even_fun` against
  `__p1`]. The data permute the inductives as well, so the two causes are not separated.
- The theorems of a mutual structural pair change address when the definitions are reordered
  [measured: old plan §4.6].
- Population: about 5 order-dependent safe `mutual` definition cliques across all libraries, of which
  about 2–3 would reorder [estimate, MUT §5.1]. Four well-founded `_mutual` in an Init-sized
  environment [measured: MUT §5.1].

Not measured:
- no well-founded or `partial_fixpoint` clique was compiled under permutation;
- no transport was implemented;
- the grammar's coverage of real `proof_k` terms is unmeasured.

Everything in §5.1–5.4 is [argued], and O16's lemma is [open]. A5's first task is the census PD1
(MUT §5.1) and one twin per encoding.

---

## 6. Determinism: the compiler as a function of the closure

### 6.1 Global reads and order dependences today

| # | Site | What it reads or depends on | Output effect |
|---|---|---|---|
| D1 | Wave driver `compileEnvParallelAux` (`Ix/CompileDriver.lean:838-…`) and the sequential `compileEnvAux` | Each wave snapshots the accumulated `CompileEnv`; merges are applied on the main thread. The module doc claims every merge is "insert-once or last-wins-per-name in dependency order" (`CompileDriver.lean:17-22, 653-662`) | "Last-wins" is an order dependence unless the conflicting writes are equal. Nothing checks that they are |
| D2 | Promotion path (`AuxBlockOutcome.promoted`, `CompileDriver.lean:665-689`; `auxBlockOutcome`, `:691-735`; `precompileAuxGenPrereqs`, `:379`) | A block may have been pre-compiled by `precompileAuxGenPrereqs` or by *another block's* aux tail. The promote-remaining loop "runs at merge time against the live env" (`:676, 807-815`; the sequential driver does the same at `:601-610`) | A block's output depends on which other blocks merged first: a cross-block read |
| D3 | `surgeryFree` (`Ix/CompileM.lean:717-723, 1661-1670`) | Chooses between two expression compilers according to whether **any** call-site plan exists anywhere in the environment | Equal output is intended but not proved. A closure compile and a whole compile can take different implementations for the same constant |
| D4 | `nameForAddr` (`Ix/AuxGen/Kernel.lean:731-745`) | A linear scan of a `HashMap` (`nameToNamed`): the first name whose address matches wins, then `nameByHash`, then `env.consts` by name hash | When aliases share an address, which name is used for kernel ingress, and so for display metadata, follows hash-map iteration order. Content is unaffected, since aliases have equal content [argued] |
| D5 | Provisional addresses (`Kernel.lean:62-77`; `Ix/AuxGen/CompileAux.lean:37-46`) | The name hash stands in for the address of a constant compiled after the `AddrMaps` snapshot | Consistent within one bridge kenv. `CompileAux` states that output-visible paths go through the live chain. Whether any path leaks a provisional address into output is [open] |
| D6 | Synthetic primitive names (`Kernel.lean:150-156`) | Primitive `KId`s get synthetic display names. Rust uses real names when the primitive is in the walked closure (B §F7(b)) | Display metadata; a Lean/Rust difference |
| D7 | Kernel intern history (B §F7(a)) | Binder names and which alias a `Const` names are "fixed by whichever constant was interned first". Both compilers mitigate this with a fresh context per block (`CompileDriver.lean:23-27`) | Display metadata |
| D8 | `]!` accesses | 252 sites in `Ix/AuxGen`, `Ix/CompileM.lean` and `Ix/CallSiteSurgery.lean` print and continue with a default where Rust aborts [measured: `grep -c ']!'` over those paths at `f829b760` gives 252, matching B §F7(f)] | A wrong default can reach output silently |
| D9 | SCC iteration (`Ix/CondenseM.lean:110-144`; `CompileDriver.lean:82-90`) | Blocks are keyed by the Tarjan root `lo`; members are iterated in `Set` order | Harmless today, because `sortConsts` re-sorts by name hash. **Must not become the seed** (§2.8) |
| D10 | Seed and representative (`Ix/Environment.lean:148-153`) | Name hash | Representative and metadata (§3.3) |

### 6.2 The definition Phase A adopts

**Definition.** `compile(L) := foldl step ∅ (blocks L)` where:
- `blocks L` lists the components and cliques (§2.1, §2.7) in a **topological order of the
  condensation DAG**, with ties broken by a fixed key. The key may be the Lean name of the block's
  first member in Lean order; by the theorem below, the choice cannot affect the output.
- `step acc B := acc ∪ out(B)`, where
  `out(B) := compileBlock(input(B), {(n, addr n, plan n) | n ∈ closure(B)})`.
  - `input(B)` is the prepared Lean data of `B`'s members. For an inductive block this includes its
    Lean auxiliaries, whose images are compiled with the block.
  - `closure(B)` is the set of constants `B` references, transitively through types, values and
    rules (Def 1.3). The closure carries resolved addresses and, for changed blocks, the plans
    (images, `N`, `σ`).
- `∪` is a disjoint union of per-name maps. A name assigned twice is an **error** unless both
  assignments are equal. Content-keyed tables (blobs, shared subterms) are unioned by content.

**Theorem to state and prove (Phase B L1; A7 gate):** `out(B)` reads nothing outside
`input(B) ∪ closure(B)`. Consequently `compile(L)` is the same for every topological order, every
wave partition and every worker count, and a closure compile of `X` agrees with the whole compile on
every constant in `X`'s closure [argued].

**What the definition removes:**
- **D1, D2:** no promotion, no pre-compilation by another block, no live reads. Every block is
  compiled by its own `step`. An auxiliary of a block is compiled with that block (one constant per
  auxiliary, D6), never by another block's tail.
- **D3:** one expression compiler. The no-plan path is the special case "every plan is the identity",
  stated per block from the block's own closure.
- **D4:** the generators' display metadata is taken from the block's own Lean declarations.
  - Kernel queries run in **anonymous mode** (Phase A §3.2), so the result of a query never supplies
    a name.
  - Ingress through an alias needs *some* name with that address, and all aliases have equal content.
  - Where a name must be recorded, the **canonical alias** is the alias whose defining block comes
    first in the fold order, then the first in canonical position, then the first in seed order.
- **D5:** kernel ingress resolves addresses from the closure only. A constant outside the closure is
  never ingressed, so no provisional address exists.
- **D6:** each primitive's display name is the real Lean name chosen by the canonical alias rule.
  Primitives are recognised by address and shape, never by name.
- **D7:** subsumed by anonymous mode plus metadata from the source declarations.
- **D8:** every `]!` is replaced by total code or by a named error that reports the block.
- **D9, D10:** the seed is Lean's `all` order (§2.8). `lo` and `Set` order are never observed.

**What the wave and speculative drivers must satisfy.** They are optimisations of the fold, gated by
schedule identity: byte-equal output for every driver, every worker count, and closure against whole.
Three conditions together suffice [argued]:
- (i) a worker computes `out(B)` on a snapshot that contains `closure(B)`;
- (ii) merges are the disjoint union of §6.2;
- (iii) no worker reads anything outside its snapshot's closure.

A speculative driver that compiles `B` before its closure is complete must discard the result unless
the closure it read equals the final closure.

---

## 7. What is canonical and what is only faithful; the residue fixture

### 7.1 The table (Phase A §3.4.5, made precise)

"Canonical" means invariant, in bytes, under the presentations of Def 4.3:
- for blocks: member reorder; separate declaration of components with the block's universes,
  parameters and sort; collapse;
- for cliques: permutation, regrouping, renaming, equal members.

| Source constant | Compiled by | Canonical? | Residue cause if not |
|---|---|---|---|
| Ix blocks and every Ix auxiliary | P1, P2 | **yes** [argued; leg 5 of §3.6] | — |
| Anything over an unchanged block or clique | identity translation | **yes** | — |
| `rec`/`recOn`/`casesOn`/`below`/`brecOn` users over a permuted block | O1–O6 | **yes** [measured, ORA DQReord 53/53] | — |
| The same over a split block, including relocated calls | O2, O3 | **yes** [argued; PRO B1/B2 `rfl` for `rec` and `casesOn` users] | — |
| Structural recursion over a split block with a cross field | O9 | **yes** once the reference tables are derived from the final term (§4.7 (e)) [argued] | — |
| `noConfusion` in enumeration form; mutual `_sizeOf` over a split block | O11b; O11a | **yes** | `O11A-PENDING` until the `rfl` is confirmed |
| `rec` users of a collapsed block that do not distinguish members | O7 | **yes** | — |
| `casesOn` and matchers over a collapsed or lifted member | O8 | **yes** | — |
| Two functions over a collapsed pair, equal arms | O10 | **yes** (the twin's single function) | — |
| Two functions over a collapsed pair, different arms | O12 | the shared helper `fg` only | `COLLAPSE-ARMS` (the Lean names `A.f`, `B.g`) |
| A changed structural clique | O13, O14 | **yes** | `RECARG` (an ambiguous recursive argument) |
| A changed well-founded clique | O15 + §5.1 | functional: **yes**. Proofs: yes when transported | `GUESSLEX`, `TACTIC-ASYM`, `SHAPE` |
| A changed `partial_fixpoint` clique | O16 + §5.2 | as above | `TACTIC-ASYM`, `SHAPE` |
| Clique members in one class | O17 | **yes** | — |
| Theorems proved by mutual recursion | §5.4 | statement **yes**; proof when transported | `NOSPEC`, `TACTIC-ASYM`, `SHAPE` |
| Statements following the order (`mutual_induct`, `induct`, `_mutual.eq_unfold`) | baseline | faithful only | `ORDER-STMT` |
| Bare or partial auxiliary occurrences (`def r := @A.rec`, `@f._mutual`) | residual image | faithful only: the type is Lean's | `BARE` |
| Lean `IndPredBelow` families of a changed Prop block | own block (§4.6) | faithful only | `INDPRED-BELOW` |
| Lazily realised equation lemmas (`eq_N`, `eq_def`, `eq_unfold`) | baseline, or demoted | existence varies with the build (A Δ13) | excluded from the claim; `LAZY` if listed |
| A split member against the member declared alone with fewer universes, parameters or a smaller sort | — | not a presentation under Def 4.3 | not recorded |
| Theorem proofs in general | any | not promised (M7) | not recorded unless the theorem is in a clique fixture |

### 7.2 The residue fixture

**Location.** The fixture is tracked at `Tests/Ix/Compile/Residue.lean`, as Lean data, because
tooling is in Lean. The twins gate (Phase A §5.2) reads it.

**Format.**

```lean
inductive ResidueCause where
  | tacticAsym | shape | guessLex | recArg | orderStmt | bare | collapseArms
  | indPredBelow | noSpec | lazy | o11aPending
  deriving Repr, BEq

structure ResidueEvidence where
  addrA       : String          -- hex address under presentation A
  addrB       : String          -- hex address under presentation B
  firstDiff   : String          -- path to the first differing node of the decoded terms, e.g. "value.app.arg.3.proj"
  kernelsA    : Bool × Bool × Bool  -- accepted by Ix.Tc, the Rust kernel, the certified checker
  kernelsB    : Bool × Bool × Bool
  note        : String          -- one line; for TACTIC-ASYM the tactic or lemma responsible

structure ResidueEntry where
  fixture     : Lean.Name       -- the fixture module, e.g. `Tests.Ix.Compile.Fixtures.WFPair`
  presA       : String          -- presentation id, e.g. "orig"
  presB       : String          -- e.g. "perm[1,0]", "regroup:where", "rename"
  constant    : Lean.Name       -- the constant's name in presentation A
  canonical   : String          -- its canonical position (block or clique, class, role)
  cause       : ResidueCause
  evidence    : ResidueEvidence

def residue : List ResidueEntry := [ ... ]
```

**Gate semantics.** The fixture is **exact** in both directions:
- every byte difference between twins must match an entry by `(fixture, presA, presB, constant)`;
- every entry must still match a difference;
- a stale entry fails the gate.

Entries change only in a commit that states the cause.

**Policy.** Recording is the Phase A policy (Q-A5). A `TACTIC-ASYM` or `SHAPE` entry on library code
is reported in the migration's PR text.

---

## 8. Open questions for the owner

Each question comes with the recommendation this document assumes.

**Canonical form and the comparator (decide before A2's migration).**
- **Q1. Addresses only on full ties.** Adopt the two-key comparator `(k₀, k₁)` of §2.3 in A2's
  migration? Today addresses are interleaved with the structural comparison.
  - *Recommend: yes.* It is the stated Phase A decision, the partition is unchanged, and it removes
    format-version dependence except on full ties.
  - Cost: the order of some blocks moves. A1's census must count how many before A2.
- **Q2. Seed and representative.** Seed = Lean's `all` order restricted to the component, and
  `EqnInfo.declNames` order for cliques. Representative = first in seed order.
  - *Recommend: yes.* It is name-free. Only metadata depends on it (§3.3). It names a collapsed class
    by the member the user wrote first.
- **Q3. Fixes C1 (kind tag) and C2 (cache orientation) in the Lean port.**
  - *Recommend: both, in A2's migration commit.* Neither moves a byte. C2 is a precondition of Q2.
- **Q4. `is_rec`/`is_unsafe` in Rust's key (C6).**
  - *Recommend:* the canonical key compares content only. The Rust catch-up drops both keys, or
    computes them on the Ix block. This has no byte effect if the flags are block-wide.
  - One fact must be checked first: is Lean's `InductiveVal.isRec` block-wide? A one-line
    `#eval` on a split fixture answers it [open].
- **Q5. Discovery-order deduplication of a sibling of an external mutual inductive (§2.5).**
  - *Recommend:* a blocking fixture before A2, comparing Lean's `rec_N` count and order on
    `T | mk : Tree T → T` with `Tree/Forest` mutual. Fix both ports if Lean registers every sibling.
- **Q6. Theorem cliques without a specification (§5.4).**
  - *Recommend:* order theorem cliques by statement first, then by the recovered specification. The
    recovery is checked by re-encoding against Lean's bytes. Fall back to the baseline with cause
    `NOSPEC`.
  - A smaller alternative: Phase A leaves theorem cliques at the baseline and records them. That gives
    up theorem-address canonicity for cliques, which the decision log puts in scope.
- **Q7. Well-founded decreasing proofs (§5.1).**
  - *Recommend:* re-state every `proof_k` over the canonical packing. Its value is `Φ_σ(p_k)` when the
    grammar recognises `p_k`, else Lean's `p_k` verbatim, which is accepted by conversion and recorded
    as `SHAPE`. Never re-run a tactic.
- **Q8. Pinned choices compare last in M.3 (§2.7).**
  - *Recommend: yes.* Otherwise a GuessLex or `recArgPos` difference between presentations changes
    the canonical *order* as well as the encoding.
- **Q9. `partial_fixpoint` monotonicity (§5.2).**
  - *Recommend:* regenerate the projection-path sub-proofs with `solveMonoCall`'s recipe. Fall back to
    `monotone_compose (mono φ) hmono_i` for user-supplied terms (`SHAPE`).
  - O16's lemma (fix commutes with a product reordering) is written once as an Ix-supplied Lean
    module in A5.
- **Q10. The development (§4.3).**
  - *Recommend:* hereditary substitution of the image's parameters, contracting the β-, projection-
    and η-redexes formed at the substituted variables, and never ι.
  - Confirm, because it is part of the canonical form of every rewritten call site. A3 pins it with
    twins whose motives and minors are λs.
- **Q11. Bare and partial occurrences (§4.5).**
  - *Recommend:* reference the image constant, which serves as the eta adapter. Do not inline
    η-expansions. Library population: 0 [measured, CEN:33].
- **Q12. Old Def 2.5 wording.**
  - *Recommend:* replace "depth first into new auxiliaries" with the FIFO-queue definition of §2.5.
    Same for `docs/ix_canonicity.md` at A8.

**Phase A §7, answered better now.**
- **Q-A2 (discovery order): confirm,** conditional on Q5.
  - The cost is unchanged: `canonical_aux_order` (`crates/kernel/src/inductive.rs:1284-1450`),
    `Ix/Tc/CanonicalCheck.lean`, the certified modeller's nested adaptation and `BlockOrder` are
    re-recorded.
- **Q-A5 (residue policy): accept and record.** §5 shows the residue is confined to (a) proof internals
  the grammar does not recognise, (b) order-dependent *choices* (`GUESSLEX`, `RECARG`), and (c)
  order-following statements.
  - (a) is measurable per term.
  - (b) is the larger risk, and it is a property of Lean's search, not of transport.
  - Narrow D20 should be revisited only if (a) is frequent on library code.
- **Q-A6 (scope O1–O17): all, in the stated order.**
  - §1.4 shows the passes compose without order conflicts once definitional precedes clique precedes
    collapse/split.
  - O16 alone carries an [open] lemma. If it is not written by A5, O16 is deferred, and
    `partial_fixpoint` cliques keep a transported functional with the baseline correspondence
    unproved, i.e. no optimisation.
- **Q-A9 (generator totality):** add to the list the head-only deduplication of external mutual
  groups (Q5), if the fixture shows it diverges from Lean.

---

## Appendix: what this document could not establish without running anything

- **Lean source version.** The Lean 4.34.1 source tree was not readable; the elaborator was read at
  4.34.0. Some line numbers may differ [open].
- **C6's flag.** Whether `isRec` is block-wide (Q4) [open].
- **Discovery-order deduplication** of siblings of external mutual inductives (Q5) [open].
- **Address moves under `(k₀, k₁)` and `canonUniv` comparison.** Their population is unmeasured
  [open].
- **The grammar's coverage** of real `proof_k` and monotonicity terms, and the frequency of
  `TACTIC-ASYM` [open].
- **Leaks of provisional addresses into output.** Whether any output-visible path reads them (D5)
  [open].
- **O11a's `rfl`** on `Linear.EqCnstr` [open, carried from the old plan].
- **O16's lemma** [open].
- **Cause (e) of §4.7 at v4.** The leftover-table-entry cause has not been re-measured under v4
  sharing [open].
