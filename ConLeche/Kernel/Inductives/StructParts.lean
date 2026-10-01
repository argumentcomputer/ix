module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# The direct install's generators (families, spines, rule bodies)

The syntactic generators every direct install reads and compares
against the stream — the type-former family, constructor spines, rule
bodies, the Π-to-λ rewrites — and `StructParts`, the shape the
in-process modeller reads (`Frontend/InModel/Kit.lean`).  Written for
the simple-structure route (a non-recursive, single-constructor,
index-free inductive installed from the reference checks alone),
deleted at task #210 Part C; the fixpoint route is the one consumer.

This module holds the **pure** recognition layer.  It is a conservative
filter: a block that does not match falls through to the modeled path
unchanged, so a `false` here never costs a verdict.

The checks mirror what the reference kernels do when *adding* an
inductive declaration, restricted to this class (line numbers:
lean4lean `Lean4Lean/Inductive/Add.lean`, a line-by-line port of the
official `src/kernel/inductive/inductive.cpp`; nanoda
`checker/src/inductive.rs`):

* the type former's type is a `∀`-telescope of exactly `numParams`
  binders ending in a `Sort` — `checkInductiveTypes` (`Add.lean:60-116`,
  nanoda `check_inductive_spec_0th`, `inductive.rs:375`); *index-free* means the
  telescope ends there.
* the result level may be anything (task #175 W4c/O4, the user's
  ruling that every supported `.proj` is served directly): a provably
  `Prop` result (`isProp`) selects the squash-regime install — the
  official kernel's `Prop` escape hatch on the field-universe bound
  (`Add.lean:225`), projection entries only for the `Prop`-prefix of
  the fields (a data field of a `Prop` structure is not projectable,
  `infer_proj`'s restriction), K for the fieldless case.
* the constructor's type is a `∀`-telescope whose first `numParams`
  binder domains are the type former's, ending in the type former
  applied to **exactly** those parameters at the declaration's own
  level parameters — `checkConstructors` (`Add.lean:218-223`) and
  `isValidIndAppIdx` (`Add.lean:157-165`, nanoda `is_valid_ind_app`, `inductive.rs:711`).
* no recursive occurrence: every binder domain of the constructor
  resolves already in the *pre-block* environment, which subsumes
  `checkPositivity`/`hasIndOcc` (`Add.lean:184-199`) for this class and
  is exactly what the model construction needs (the type former's value
  is defined from the field types' interpretations in the old
  environment).
* the recursor's type is **exactly** the generated shape
  (`Add.lean:477-483`): params → one motive → one minor → no indices →
  major → `motive t`, with the motive dependent
  (`∀ (t : T p⃗), Sort ℓ`, `Add.lean:326`), the minor the constructor's
  field telescope ending in `motive (C p⃗ f⃗)` (`Add.lean:384-388`), and
  either a fresh elimination level parameter in front
  (`getRecLevelParams`, `Add.lean:416-417`) — the large eliminator
  (`isLargeEliminator`, `Add.lean:257-259`) — or, for a propositional
  structure with a non-`Prop` field, the small eliminator (motive into
  `Prop`, the block's own level parameters).  Both shapes are
  recognised (`StructParts.large`).
* the single rule's right-hand side is
  `λ p⃗ motive minor f⃗, minor f⃗` (`mkRecRules`, `Add.lean:441-447`).

The per-field universe bound (`Add.lean:225-228`,
nanoda `check_ctor`, `inductive.rs:809`) needs inference, and the
recursor is **generated** here (`structRecTy`/`structRecRhs`, task
#175 S2) and compared against the stream's by one closed `isDefEq`;
both live in the monadic `checkStruct`
(`ConLeche/Kernel/Inductives/StructInstall.lean`).

The direct path installs **native tower-backed projection entries**
(`checkStructProj`, task #175 wiring): `.proj T i` nodes are typed by
the entry's stored type and reduced by the structural rule, and the
model reads them by the uniform tower projection.  The capability
record (`structCaps`) claims structure eta (the tower's own law),
unit-likeness for the fieldless case, and K for the fieldless
propositional case.
-/

namespace ConLeche

/-- The type former applied to its parameter variables, `bvar` indices
offset by `o` (the number of binders crossed since the parameters). -/
def structFam (T : Name) (lps : List Name) (nP o : Nat) : Expr :=
  Expr.mkAppN (.const T (lps.map .param))
    ((List.range nP).map fun k => Expr.bvar (o + nP - 1 - k))

/-- The constructor applied to the parameter and field variables, as
spelled inside the recursor's minor premise (parameters sit above the
motive binder). -/
def structCtorSpine (C : Name) (lps : List Name) (nP nF : Nat) : Expr :=
  Expr.mkAppN (.const C (lps.map .param))
    (((List.range nP).map fun i => Expr.bvar (nF + nP - i)) ++
     (List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- The recursor rule's right-hand side body: the minor premise applied
to the field variables. -/
def structRuleBody (nF : Nat) : Expr :=
  Expr.mkAppN (.bvar nF) ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-! ## The generated recursor (task #175 S2: fabricate-and-compare)

The reference kernels *generate* the recursor from the block
(lean4lean `Inductive/Add.lean:326-483`, official
`inductive.cpp`'s `mk_rec_infos`) and store what they generated.  So
does the direct route: the recursor type and its rule are built here,
syntactically, from the **annotated** type former and constructor
types, and the stream's recursor is compared against the generated
type by one closed `isDefEq` (`checkStructRec`).  What is stored is
the generated form — which is what makes its reading syntactic in the
model (`ConLeche/Model/Inductives/StructRecRead.lean`): no pin at an opened
frame is consumed anywhere.

The generators are written over a **list** of constructors (one minor
premise and one rule per constructor) though the recogniser admits
one: the multi-constructor extension changes the recogniser and the
proofs, not the generated shapes.

**Binder infos** are the export's: the former's parameter binders keep
theirs, every generated binder is `.default` (the standard-axiom pins,
`stdAxiomOk`, compare the stored `Iff.rec`/`Nonempty.rec` against the
exported shapes up to names and data but not infos).

**Binder data.**  Every binder the generator introduces or re-emits at
the recursor's own telescope carries the elimination datum
`Level.zeronessOf ℓ`: the codomain of each is `motive t : Sort ℓ`
(through `imax`'s right-argument rule), so this is exactly what the
verified-mode inference validates (`(forall-cod)`, `(lam-cod-*)`) and
what the stream's annotated recursor carries at the same binders (the
defeq sites compare data by `==`; the datum is canonical).  The motive's own
binder `(t : T p⃗)` has codomain `Sort ℓ : Sort (ℓ+1)`, hence `.never`.
The domains are re-emitted verbatim, their inner data untouched. -/

/-- The parameter variables as seen from under `o` extra binders:
`p_k = bvar (o + nP - 1 - k)` — `structFam`'s argument spine. -/
def structPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (o + nP - 1 - k)

/-- The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one. -/
def structElimLevel (elim : Name) (large : Bool) : Level :=
  if large then .param elim else .zero

/-- The constructor applied to the parameter and field variables, as
spelled under `o` binders between the parameters and the fields (the
motive and the earlier minor premises); `structCtorSpine` is the
`o = 1` case (`structCtorSpine_eq_at`). -/
def structCtorSpineAt (C : Name) (lps : List Name) (o nP nF : Nat) : Expr :=
  Expr.mkAppN (.const C (lps.map .param))
    (structPsAt (o + nF) nP ++ (List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- Replace the body under the first `k` `∀`-binders, resetting their
codomain data to `pw` (the domains are kept). -/
def Expr.replacePisPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE ty rest _, b =>
    (replacePisPw pw k rest b).map fun r => .forallE ty r ⟨pw⟩
  | _ + 1, _, _ => none

/-- Convert the first `k` `∀`-binders into `λ`-binders with datum `pw`
over a body (`pisToLams` with the datum supplied instead of the
`.never` placeholder). -/
def Expr.pisToLamsPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE ty rest _, b =>
    (pisToLamsPw pw k rest b).map fun r => .lam ty r ⟨pw⟩
  | _ + 1, _, _ => none

/-! ## The generated recursor at an indexed family (task #175 indexed)

A non-recursive family `T : ∀ p⃗ ı⃗, Sort w` with constructors
`C_k : ∀ p⃗ f⃗, T p⃗ e⃗_k` (the index expressions `e⃗_k` arbitrary terms
over the parameters and the fields) has the recursor

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_k : ∀ f⃗, motive e⃗_k (C_k p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(lean4lean `Inductive/Add.lean:326-483`, official `mk_rec_infos`):
the index binders are the type former's own telescope past the
parameters, re-emitted twice — at the motive (over the parameters
alone) and after the minors (lifted under the motive and the `n`
minors); the minor's conclusion applies the motive to the
constructor's residual index expressions (lifted under the extras)
before the constructor spine.  The rules are `structRecRhs`'s: a
rule binds no index (`rulePrefix = nP + 1 + n`).  At `nIdx = 0` every
generator below is the index-free one above. -/

/-- The family applied to its parameter variables and its index
variables: `e` extra binders sit between the parameters and the
indices (the motive and the minors), `o` binders below the index
frame. -/
def structFamI (T : Name) (lps : List Name) (nP nIdx e o : Nat) : Expr :=
  Expr.mkAppN (.const T (lps.map .param)) (structPsAt (o + e + nIdx) nP ++ structPsAt o nIdx)

/-- A constructor residual's shape at an indexed family: the family
at exactly the parameter variables (`o` binders below the parameter
frame) followed by `nIdx` index expressions. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppArgs.length == nP + nIdx &&
  cbody.getAppArgs.take nP == structPsAt o nP

/-- The motive's type `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the parameters'
frame, over the former's index telescope `itele = ∀ ı⃗, Sort w` (scoped
at the parameters); every binder's codomain is a type former, never a
proposition. -/
def structMotiveTyI (T : Name) (lps : List Name) (nP nIdx : Nat) (ℓ : Level) (itele : Expr) :
    Option Expr :=
  Expr.replacePisPw .never nIdx itele
    (.forallE (structFamI T lps nP nIdx 0 0) (.sort ℓ) ⟨.never⟩)

/-- The pieces of a recognised simple-structure block. -/
structure StructParts where
  /-- the type former -/
  cvT : ConstantVal
  /-- the single constructor -/
  cvC : ConstantVal
  /-- parameter count -/
  nP : Nat
  /-- field count -/
  nF : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the structure's result sort -/
  resSort : Level
  /-- the single rule's right-hand side (as exported) -/
  rhs : Expr
  /-- **large eliminator** (task #175 W4c/O4): the recursor carries a
  fresh elimination level parameter in front and its motive lands in
  `Sort elim`; `false` is the small eliminator (`motive : T p⃗ → Prop`,
  the recursor's level parameters are the block's own) that Lean
  generates for a propositional structure with a non-`Prop` field. -/
  large : Bool
  /-- **propositional result** (task #175 W4c/O4): the result sort is
  provably `Prop` (`Level.isEquiv resSort .zero`).  Selects the
  squash-regime install: no field-universe bound (the official
  kernel's `Prop` escape hatch), entries only for the `Prop`-prefix of
  the fields, K for the fieldless case. -/
  isProp : Bool
  deriving Repr

/-- The *shape* facts the model reads off the stored (annotated)
types — everything that annotation cannot change, checked on both the
raw block (recognition) and the annotated constants (install).

The binder-domain correspondences are deliberately **not** here: the
reference kernels compare the constructor's parameter domains to the
type former's by `isDefEq` (`Add.lean:220-222`) and build the
recursor's telescope from `whnf`-peeled domains (`Add.lean:79-95`), so
a syntactic pin would wrongly reject; `checkStructCtor` pins the
parameter domains definitionally over the opened telescopes, and the
recursor is generated and compared as a whole (`checkStructRec`, task
#175 S2). -/
def structShape (T C : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nF : Nat) (tty cty rty : Expr) : Bool :=
  match tty.stripPis nP, cty.stripPis (nP + nF), rty.stripPis (nP + 3) with
  | some (_, .sort _), some (_, cbody), some (rbs, rbody) =>
    cbody == structFam T lps nP nF &&
    rbody == Expr.app (.bvar 2) (.bvar 0) &&
    (match rbs[nP]? with
     | some (.forallE mmaj (.sort s') _, _) =>
       -- the motive's codomain: `Sort elim` for the large eliminator,
       -- `Prop` for the small one (task #175 W4c/O4)
       (if large then s' == .param elim else s' == .zero) &&
         mmaj == structFam T lps nP 0
     | _ => false) &&
    (match rbs[nP + 1]? with
     | some (mindom, _) =>
       match mindom.stripPis nF with
       | some (_, mbody) =>
         mbody == Expr.app (.bvar nF) (structCtorSpine C lps nP nF)
       | none => false
     | none => false) &&
    (match rbs[nP + 2]? with
     | some (majdom, _) => majdom == structFam T lps nP 2
     | none => false)
  | _, _, _ => false

/-- Recognise a direct simple-structure block (see the module docs).
`none` means "not this class" — the caller falls through to the modeled
path, so this is never an error source. -/
def structPartsCore? (block : List ConstantInfo) : Option StructParts :=
  match block with
  | [.indInfo cvT _, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] =>
    let T := cvT.name
    let C := cvC.name
    let lps := cvT.levelParams
    -- the shape facts common to both eliminator shapes
    if cvR.name == T.str "rec" && cvC.levelParams == lps &&
        reservedBasisNames.contains T == false &&
        reservedBasisNames.contains C == false &&
        reservedBasisNames.contains cvR.name == false &&
        mI == nP + 2 && rP == nP + 2 &&
        rule.ctor == C && rule.nfields == nF &&
        (match rule.rhs.stripLams (nP + 2 + nF) with
         | some (_, rbody) => rbody == structRuleBody nF
         | none => false) then
      match cvT.type.stripPis nP with
      | some (_, .sort s) =>
        let isProp := Level.isEquiv s .zero == some true
        -- the large eliminator: a fresh elimination level parameter in
        -- front of the block's own; else the small eliminator at the
        -- block's own level parameters (task #175 W4c/O4)
        let large? : Option Name :=
          match cvR.levelParams with
          | elim :: relps =>
            if relps == lps && !lps.contains elim &&
                structShape T C lps elim true nP nF cvT.type cvC.type
                  cvR.type then
              some elim
            else none
          | [] => none
        match large? with
        | some elim =>
          some ⟨cvT, cvC, nP, nF, cvR, elim, s, rule.rhs, true, isProp⟩
        | none =>
          if cvR.levelParams == lps &&
              structShape T C lps .anonymous false nP nF cvT.type cvC.type
                cvR.type then
            some ⟨cvT, cvC, nP, nF, cvR, .anonymous, s, rule.rhs, false,
              isProp⟩
          else none
      | _ => none
    else none
  | _ => none

/-- The parameter spine of the generated projection types, spelled at
the frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar
(nP - k)` (the `instPisAtLift` walk lowers each entry once per
substitution step, landing them at `bvar (nP - 1 - k)` under the
subject binder). -/
def structProjPs (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (nP - k)

/-- The `j`-th earlier-field substitute in a **tower entry's**
generated type (task #175 wiring): the first-class node `t.j`
(`.proj T j` of the subject), at `structProjArg`'s frame (subject
`t = bvar 0`).  No `projFnName` chain — each field's entry stands
alone, which is what makes O4's per-field entry branch real. -/
def structProjArgP (T : Name) (j : Nat) : Expr :=
  Expr.proj T j (Expr.bvar 0)

/-- `structProjResid` in the `.proj`-node spelling: the constructor
telescope peeled at the parameters and the first `i` subject
projections, threaded incrementally (step `i → i + 1` is a single
`instantiate1Lift`). -/
def structProjResidP (T : Name) (nP : Nat) (cty : Expr) : Nat → Option Expr
  | 0 => Expr.instPisAtLift (structProjPs nP) cty
  | i + 1 => (structProjResidP T nP cty i).bind
      (Expr.instPisAtLift [structProjArgP T i])

/-- Does `bvar i` occur loose in `e`?  (Not through fvar type
annotations — the generated telescopes are fvar-free.) -/
def Expr.hasLooseBVar : Nat → Expr → Bool
  | i, .bvar j => i == j
  | _, .fvar .. => false
  | _, .sort _ => false
  | _, .const .. => false
  | _, .lit _ => false
  | i, .app f a => hasLooseBVar i f || hasLooseBVar i a
  | i, .lam ty b _ => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .forallE ty b _ => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .letE t v b =>
    hasLooseBVar i t || hasLooseBVar i v || hasLooseBVar (i + 1) b
  | i, .proj _ _ e => hasLooseBVar i e

/-- `hasLooseBVar` with the packed bound's cutoff (task #214, P4): a
node whose loose-bvar bound is at or below `i` has no `bvar i`, so the
walk stops there without descending — `structProjGuards`' O(nF²)
`structUsedLater` calls then touch only the spine of a large
telescope, never its shared instance towers.  Read as `hasLooseBVar`
by `Expr.hasLooseBVarB_eq` (`ConLeche/Verify/Inductives/StructBody.lean`). -/
def Expr.hasLooseBVarB (i : Nat) (e : Expr) : Bool :=
  if e.bvarB ≤ i then false else
  match e with
  | .bvar j => i == j
  | .fvar .. => false
  | .sort _ => false
  | .const .. => false
  | .lit _ => false
  | .app f a => hasLooseBVarB i f || hasLooseBVarB i a
  | .lam ty b _ => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .forallE ty b _ => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .letE t v b =>
    hasLooseBVarB i t || hasLooseBVarB i v || hasLooseBVarB (i + 1) b
  | .proj _ _ e => hasLooseBVarB i e

/-! ### `hasLooseBVarB`, memoized (task #233)

The cutoff above stops the walk where the variable **cannot** occur.
It cannot stop it where a loose variable *above* `i` occurs but `i`
itself does not: `bvarB` is the bound of the largest loose index, so a
node holding `bvar 1` has `bvarB = 2` and the `bvarB ≤ 0` test fails at
every node of a shared tower whose answer is `false` — and with no
`true` to short-circuit the `||` on, each shared node is re-entered
once per path.  A user's stream showed 99.5 % of a run inside this one
function; the depth-60 fixture is `tests/e2e/tower_usedlater.ndjson`
(a three-field structure whose last field's type is a tower over the
FIRST field, asked about the SECOND).

The cutoff and the memo are complementary — this keeps both.  As with
`mentionsConst` below and `instantiate1` (`ConLeche/Kernel/ExprOps.lean`,
task #215), the memoized walk is swapped in by `@[csimp]`:
kernel-checked, no trust point, and the pure definition stays what
every proof consumes (`Expr.hasLooseBVarB_eq`,
`ConLeche/Verify/Inductives/StructBody.lean`, is unchanged).  The memo
is keyed by the *node and the index* — the index shifts under binders,
so a node's answer is not a function of the node alone — and dropped
after each call. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def LooseBVarMemoInv (memo : Std.HashMap (Expr × Nat) Bool) : Prop :=
  ∀ (k : Expr × Nat) (r : Bool), memo[k]? = some r → r = Expr.hasLooseBVarB k.2 k.1

theorem LooseBVarMemoInv.empty : LooseBVarMemoInv {} := by
  intro k r h; simp at h

theorem LooseBVarMemoInv.insert {memo : Std.HashMap (Expr × Nat) Bool}
    (hm : LooseBVarMemoInv memo) {e : Expr} {i : Nat} {r : Bool}
    (heq : r = Expr.hasLooseBVarB i e) :
    LooseBVarMemoInv (memo.insert (e, i) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Record one answer for `(e, i)` in the memo the walk hands back.
Written with projections rather than a destructuring `let` so that the
correctness proof can `split` the walk's own matches. -/
@[inline] def Expr.hasLooseBVarBIns (e : Expr) (i : Nat)
    (r : Bool × Std.HashMap (Expr × Nat) Bool) : Bool × Std.HashMap (Expr × Nat) Bool :=
  (r.1, r.2.insert (e, i) r.1)

/-- Memoized `hasLooseBVarB`. -/
def Expr.hasLooseBVarBGo (memo : Std.HashMap (Expr × Nat) Bool) (i : Nat) (e : Expr) :
    Bool × Std.HashMap (Expr × Nat) Bool :=
  if e.bvarB ≤ i then (false, memo) else
  match e with
  | .bvar j => (i == j, memo)
  | .fvar .. => (false, memo)
  | .sort _ => (false, memo)
  | .const .. => (false, memo)
  | .lit _ => (false, memo)
  | e =>
    match memo[(e, i)]? with
    | some r => (r, memo)
    | none =>
      Expr.hasLooseBVarBIns e i <|
        match e with
        | .app f a =>
          match hasLooseBVarBGo memo i f with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo i a
        | .lam ty b _ =>
          match hasLooseBVarBGo memo i ty with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .forallE ty b _ =>
          match hasLooseBVarBGo memo i ty with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .letE t v b =>
          match hasLooseBVarBGo memo i t with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match hasLooseBVarBGo memo i v with
            | (true, memo) => (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .proj _ _ sub => hasLooseBVarBGo memo i sub
        | _ => (false, memo)

/-- **The memoized walk is `hasLooseBVarB`.** -/
theorem Expr.hasLooseBVarBGo_spec :
    ∀ (e : Expr) (i : Nat) (memo : Std.HashMap (Expr × Nat) Bool), LooseBVarMemoInv memo →
      (hasLooseBVarBGo memo i e).1 = Expr.hasLooseBVarB i e ∧
        LooseBVarMemoInv (hasLooseBVarBGo memo i e).2 := by
  intro e
  induction e with
  | bvar j =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | fvar idx ty _ =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | sort u =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | const n us =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, if_pos hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.app f a)
          = (Expr.hasLooseBVarB i f || Expr.hasLooseBVarB i a) := by
        rw [Expr.hasLooseBVarB, if_neg hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := iha i memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | lam ty b m iht ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, if_pos hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.lam ty b m)
          = (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, if_neg hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihb (i + 1) memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | forallE ty b m iht ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, if_pos hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.forallE ty b m)
          = (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, if_neg hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihb (i + 1) memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | letE t v b iht ihv ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, if_pos hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.letE t v b)
          = (Expr.hasLooseBVarB i t || Expr.hasLooseBVarB i v
              || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, if_neg hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihv i memo₁ h2
          split
          · rename_i memo₂ heq₂
            rw [heq₂] at h3 h4
            exact ⟨by simp [hspec, ← h1, ← h3], h4.insert (by simp [hspec, ← h1, ← h3])⟩
          · rename_i memo₂ heq₂
            rw [heq₂] at h3 h4
            obtain ⟨h5, h6⟩ := ihb (i + 1) memo₂ h4
            exact ⟨by simp [hspec, ← h1, ← h3, h5],
              h6.insert (by simp [hspec, ← h1, ← h3, h5])⟩
  | proj s j sub ih =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, if_pos hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.proj s j sub) = Expr.hasLooseBVarB i sub := by
        rw [Expr.hasLooseBVarB, if_neg hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih i memo hm
        simp only [hasLooseBVarBIns]
        exact ⟨by simp [hspec, h1], h2.insert (by simp [hspec, h1])⟩

/-- The executed `hasLooseBVarB` (one memoized DAG walk). -/
def Expr.hasLooseBVarBFast (i : Nat) (e : Expr) : Bool :=
  (Expr.hasLooseBVarBGo {} i e).1

@[csimp] theorem Expr.hasLooseBVarB_eq_hasLooseBVarBFast :
    @Expr.hasLooseBVarB = @Expr.hasLooseBVarBFast := by
  funext i e
  exact (hasLooseBVarBGo_spec e i {} LooseBVarMemoInv.empty).1.symm

/-- **Field `j` is used by a later field** — the official
`infer_proj`'s `has_loose_bvars(binding_body(r))` at step `j`: the
field's variable occurs in the constructor telescope's remainder after
binder `j` (a later field's domain; the result never mentions a
field). -/
def structUsedLater (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => rest.hasLooseBVarB 0
  | none => false

/-- **The projection guard levels** (task #175 W4c/O4): for field `i`,
its own sort joined with the sorts of the earlier fields that a later
field uses — the level a `.proj T i` use on a `Prop`-declared
structure must instantiate to `Prop` (the official `infer_proj`
restriction, both of its clauses, as one level).  `sorts` are the
fields' sorts in order (`checkStructFieldSorts`). -/
def structProjGuards (cty : Expr) (nP nF : Nat) (sorts : List Level) :
    List Level :=
  (List.range nF).map fun i =>
    (List.range i).foldl
      (fun acc j =>
        if structUsedLater cty nP j then .max acc (sorts.getD j .zero)
        else acc)
      (sorts.getD i .zero)

/-! ### The guard table in one traversal (task #236)

`structProjGuards` asks `structUsedLater cty nP j` once for every PAIR
`j < i < nF`: O(nF²) walks of one telescope for nF distinct answers.
The fast form computes the nF answers first, threading ONE
`hasLooseBVarBGo` memo through them — so a node the walk for field `j`
already answered at index `d` is not re-walked for field `j'` — and
then folds over the recorded answers.  `@[csimp]`, so the pure
definition above stays what `structProjGuards_getD` and the model
stage tables consume. -/

/-- Memoized `structUsedLater`, taking and returning the shared memo. -/
def structUsedLaterGo (memo : Std.HashMap (Expr × Nat) Bool) (cty : Expr) (nP j : Nat) :
    Bool × Std.HashMap (Expr × Nat) Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => Expr.hasLooseBVarBGo memo 0 rest
  | none => (false, memo)

theorem structUsedLaterGo_spec (cty : Expr) (nP j : Nat)
    {memo : Std.HashMap (Expr × Nat) Bool} (hm : LooseBVarMemoInv memo) :
    (structUsedLaterGo memo cty nP j).1 = structUsedLater cty nP j ∧
      LooseBVarMemoInv (structUsedLaterGo memo cty nP j).2 := by
  rw [structUsedLaterGo, structUsedLater]
  split
  · exact Expr.hasLooseBVarBGo_spec _ 0 memo hm
  · exact ⟨rfl, hm⟩

/-- `structUsedLater cty nP j` for `j = base, …, base + n - 1`, in
order, through one shared memo. -/
def structUsedLaterList (cty : Expr) (nP : Nat) :
    Std.HashMap (Expr × Nat) Bool → Nat → Nat → List Bool
  | _, 0, _ => []
  | memo, n + 1, base =>
    let r := structUsedLaterGo memo cty nP base
    r.1 :: structUsedLaterList cty nP r.2 n (base + 1)

theorem structUsedLaterList_spec (cty : Expr) (nP : Nat) :
    ∀ (n : Nat) (memo : Std.HashMap (Expr × Nat) Bool), LooseBVarMemoInv memo →
      ∀ (base t : Nat), t < n →
        (structUsedLaterList cty nP memo n base).getD t false
          = structUsedLater cty nP (base + t) := by
  intro n
  induction n with
  | zero => intro _ _ _ t ht; omega
  | succ n ih =>
    intro memo hm base t ht
    obtain ⟨h1, h2⟩ := structUsedLaterGo_spec cty nP base hm
    rw [structUsedLaterList]
    cases t with
    | zero => simpa using h1
    | succ t =>
      rw [List.getD_cons_succ, ih _ h2 (base + 1) t (by omega)]
      congr 1
      omega

/-- `foldl` respects a pointwise equality of the step functions on the
list's elements. -/
private theorem foldlCongrMem {α β : Type _} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ b ∈ l, ∀ x : α, f x b = g x b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h b (by simp) a]
    exact foldlCongrMem l _ (fun b' hb' => h b' (by simp [hb']))

/-- The executed `structProjGuards`: the `nF` `structUsedLater`
answers first, one shared memo, then the fold. -/
def structProjGuardsFast (cty : Expr) (nP nF : Nat) (sorts : List Level) :
    List Level :=
  let used := structUsedLaterList cty nP {} nF 0
  (List.range nF).map fun i =>
    (List.range i).foldl
      (fun acc j =>
        if used.getD j false then .max acc (sorts.getD j .zero)
        else acc)
      (sorts.getD i .zero)

@[csimp] theorem structProjGuards_eq_structProjGuardsFast :
    @structProjGuards = @structProjGuardsFast := by
  funext cty nP nF sorts
  have hused : ∀ j, j < nF →
      (structUsedLaterList cty nP {} nF 0).getD j false = structUsedLater cty nP j := by
    intro j hj
    simpa using structUsedLaterList_spec cty nP nF {} LooseBVarMemoInv.empty 0 j hj
  simp only [structProjGuards, structProjGuardsFast]
  refine List.map_congr_left ?_
  intro i hi
  refine foldlCongrMem _ _ ?_
  intro j hj x
  rw [hused j (Nat.lt_trans (List.mem_range.mp hj) (List.mem_range.mp hi))]

/-- **The projection bodies of a recognised block** (task #175 S1),
one walk of the constructor telescope: after the parameters are
replaced by the loose variables `structProjPs nP` (parameter `k` at
`bvar (nP - k)`, the subject reserved at `bvar 0`), the fields are
peeled one at a time — field `i`'s domain is body `i`, and the field
is replaced by the subject's projection `.proj T i (bvar 0)` before
the walk continues (`structProjResidP`'s step).  So `bodies[i] =
F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar 0)]`, scoped at `nP + 1`: what
a `.proj T i e` use instantiates in one `instantiateList` along the
subject type's arguments and the subject (`ProjEntry.typeAt`).  The
table holds every field (the official `infer_proj` restriction at a
`Prop`-declared structure is the per-use guard level,
`structProjGuards`); no entry is annotated, inferred or pinned. -/
def structProjBodiesGo (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
    (structProjBodiesGo T k (i + 1) (body.instantiate1Lift (structProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match Expr.instPisAtLift (structProjPs nP) cty with
  | some r => (structProjBodiesGo T nF 0 r).map List.toArray
  | none => none

/-- Does the constant `T` occur in `e`?  A syntactic walk (`fvar`
annotations included; a `.proj` node names its structure). -/
def Expr.mentionsConst (T : Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => n == T
  | .fvar _ ty => ty.mentionsConst T
  | .app f a => f.mentionsConst T || a.mentionsConst T
  | .lam ty b _ | .forallE ty b _ => ty.mentionsConst T || b.mentionsConst T
  | .letE ty v b => ty.mentionsConst T || v.mentionsConst T || b.mentionsConst T
  | .proj s _ e => s == T || e.mentionsConst T

/-! ### `mentionsConst`, memoized (task #210 Part B)

The recogniser's positivity walk asks `mentionsConst` of every field
domain and index argument; on a DAG-shared field type (task #215's
`tower_struct`: a depth-60 doubling tower in a structure field) the
tree walk does not finish.  As with `instantiate1` and `renameConsts`
(`ConLeche/Kernel/ExprOps.lean`, task #215) the memoized walk is
swapped in by `@[csimp]`: kernel-checked, no trust point, the pure
definition stays what every proof consumes.  The memo is keyed by the
node and dropped after each call (the answer depends on `T`). -/

/-- The memo's invariant: every recorded answer is the real one. -/
def MentionsMemoInv (T : Name) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = k.mentionsConst T

theorem MentionsMemoInv.empty {T : Name} : MentionsMemoInv T {} := by
  intro k r h; simp at h

theorem MentionsMemoInv.insert {T : Name} {memo : Std.HashMap Expr Bool}
    (hm : MentionsMemoInv T memo) {e : Expr} {r : Bool} (heq : r = e.mentionsConst T) :
    MentionsMemoInv T (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `mentionsConst`. -/
def Expr.mentionsConstGo (T : Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (n == T, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => mentionsConstGo T memo ty
        | .app f a =>
          let (b₁, memo) := mentionsConstGo T memo f
          let (b₂, memo) := mentionsConstGo T memo a
          (b₁ || b₂, memo)
        | .lam ty body _ =>
          let (b₁, memo) := mentionsConstGo T memo ty
          let (b₂, memo) := mentionsConstGo T memo body
          (b₁ || b₂, memo)
        | .forallE ty body _ =>
          let (b₁, memo) := mentionsConstGo T memo ty
          let (b₂, memo) := mentionsConstGo T memo body
          (b₁ || b₂, memo)
        | .letE ty val body =>
          let (b₁, memo) := mentionsConstGo T memo ty
          let (b₂, memo) := mentionsConstGo T memo val
          let (b₃, memo) := mentionsConstGo T memo body
          (b₁ || b₂ || b₃, memo)
        | .proj s _ sub =>
          let (b, memo) := mentionsConstGo T memo sub
          (s == T || b, memo)
        | e => (e.mentionsConst T, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `mentionsConst`.** -/
theorem Expr.mentionsConstGo_spec {T : Name} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), MentionsMemoInv T memo →
      (mentionsConstGo T memo e).1 = e.mentionsConst T ∧
        MentionsMemoInv T (mentionsConstGo T memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsConst, h1], ?_⟩
      exact h2.insert (by simp [mentionsConst, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsConst, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsConst, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsConst, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [mentionsConst, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [mentionsConst, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [mentionsConstGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsConst, h1], ?_⟩
      exact h2.insert (by simp [mentionsConst, h1])

/-- The executed `mentionsConst` (one memoized DAG walk). -/
def Expr.mentionsConstFast (T : Name) (e : Expr) : Bool :=
  (mentionsConstGo T {} e).1

@[csimp] theorem Expr.mentionsConst_eq_mentionsConstFast :
    @Expr.mentionsConst = @Expr.mentionsConstFast := by
  funext T e
  exact (mentionsConstGo_spec e {} MentionsMemoInv.empty).1.symm

end ConLeche
