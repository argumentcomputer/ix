module

public import ConLeche.Kernel.Inductives.SumInstall
public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# The direct recursive install (pure fueled checker; task #188)

The install stages of a block recognised by `nativeParts?`
(`ConLeche/Kernel/Inductives/NativeParts.lean`).  The former's and the
constructors' stages are the sum route's, verbatim
(`checkSumInd`, `checkSumCtors`): the constructors are
checked at the environment holding the former, with the pre-block
resolution guard pointed at THAT environment so that the recursive
fields `T p⃗` pass it; what the sum route's guard bought — no field
domain mentions the block — is replaced by the positivity
classification, re-checked on the annotated types after the stage
(`nativeFieldsOk`: every field is ordinary, resolving in the
pre-block environment, or exactly the family at the parameters).
The recursor stage generates the type with the inductive-hypothesis
binders (`structRecTyR`), compares it with the stream's by one closed
`isDefEq` (task #175 S2), and generates the rules (`structRecRhsR`);
the rules mention the recursor itself, so they are scope-checked at
the environment holding its constant and NOT inferred — the official
kernel infers no rule either; the P tier grades the generated form
from the leaf's own laws.

Front guards, in the official kernel's order: positivity (a
non-positive occurrence is `.invalid`, an unsupported positive one
`.notImplemented`), the elimination restriction
(`elim_only_at_universe_zero`: a large eliminator on a block whose
sort may be `Prop` is `.invalid` at two or more constructors; at one
constructor it is the subsingleton case, taken with the per-field
criterion at `checkStructFieldSortsI` — the recursive squash regime's
large eliminator, task #202 Stage A2), the constructors' distinct
names.

**The recursor pin is the LAST of the block's checks** (task #220):
everything the stream's recursor RECORD claims — its name, its level
parameters, its argument sums, its rules — is compared at
`checkNativeRec`/`nativeRulesOk`, where a mismatch is `.invalid`,
and none of it is a condition of recognition.  Official never reads the
exported recursor as an input either: `add_inductive` generates one and
the replay compares the record with it structurally
(`checkPostponedRecursors`, `Lean4Checker/Replay.lean` — "Invalid
recursor", "No such recursor").  So a block whose recursor record is a
stub is rejected by its own type and constructors, with official's
message, instead of being declined for a recursor this route was going
to generate anyway.  The index-threaded twins are
`ConLeche/Kernel/Inductives/NativeInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- The capabilities a block on the fixpoint route earns (task #210
Part A): at a STRUCTURE-LIKE block — one constructor, no index, and NO
recursive or reflexive field: official's `is_structure_like` is
`ncnstrs == 1 && nindices == 0 && !is_rec` (kernel/inductive.cpp), and
its `try_eta_struct` / `is_def_eq_unit_like` fire nowhere else —
structure eta at a non-`Prop` sort (the tagged tower's own elimination
law: a member is the constructor at its projections) and
unit-likeness when the constructor has no field (the fibre is then the
one tagged empty tuple); rule K exactly at official's `is_K_target` (a
`Prop` result, one constructor taking only the parameters — at any
index count, as at the sum route's `Eq`); nothing at any other block.
The projection TABLE (`checkNativeTable`) does not depend on this
record: official's `infer_proj` types `.proj` on any one-constructor
index-free family, recursive or not.  At a FIELDLESS constructor the
record claims BOTH unit-likeness and η, as official's `is_structure_like`
does: the recursor's major-premise rescue (`Core.lean`, the
`etaFields = 0` arm — arena `073_typeSingletonRecReduction`) keys on η,
and the η law owed there is the constructor at the parameters
(`FixZeroFieldP.fixFibreEtaLaw0`).  (Granting η at a recursive
structure-like was tried and is UNSOUND IN PRACTICE though sound in
the model: on `ind_nest_via_refl` the tool's nested model over a
reflexive `W1 α = sup (a : α) (f : Nat → W1 α)` made `isDefEq` spin
through η-expansion — official's `!is_rec` is load-bearing.)  On the
sum route's domain (never one constructor without an index) this is
`sumCaps`.  The `is_rec` verdict is a parameter (task #268): the
former is installed before the constructors are classified, so the
install runs at the syntactic reading (`nativeRawRec`) and confirms
it against the classification (`nativeCaps`). -/
def nativeCapsAt (p : InductiveShape) (isRec : Bool) : IndCaps :=
  match p.ctors with
  | [c] =>
    { eta := p.nIdx == 0 && !p.isProp && !isRec
      etaCtor := c.1.name
      etaParams := p.nP
      etaFields := c.2
      unitlike := p.nIdx == 0 && c.2 == 0
      unitParams := p.nP
      ruleK := c.2 == 0 && p.isProp
      sortZ := Level.zeronessOf p.resSort }
  | _ => {}

/-- Official's `is_rec` off the classified kinds: some field is
recursive or reflexive. -/
def nativeIsRec (kinds : List (List RecFieldKind)) : Bool :=
  kinds.any fun ks => ks.any fun k => k == .recursive || k == .reflexive

/-- The block's capability record at its classified kinds
(`nativeCapsAt` at `nativeIsRec`). -/
def nativeCaps (p : NativeParts) : IndCaps :=
  nativeCapsAt p.toInductiveShape (nativeIsRec p.kinds)

/-- **The syntactic reading of `is_rec`** (task #268): does the block
occur in some declared field domain of some constructor?  Official's
`is_rec` is read off the WHNF'd domains (`is_rec_argument`), and the
classification (`classifyFixKinds`) reads it off the normalised
constructors the install stores; the raw occurrence is a SUPERSET
of it (reduction never introduces the block, so a domain free of it
stays free — `normPosDom` keeps such a domain as declared), and a
strict one exactly when a redex over the block reduces away.  It is
the capability record the first pass runs at; the pass's own
classification confirms it (`checkNative`) or the block is passed
again at the classified verdict.  Read only where the record depends
on it — one constructor — as `nativeCapsAt` does. -/
def nativeRawRec (p : NativeParts) : Bool :=
  match p.ctors with
  | [c] =>
    match c.1.type.stripPis (p.nP + c.2) with
    | some (cbs, _) => (cbs.drop p.nP).any fun b => b.1.mentionsConst p.cvT.name
    | none => false
  | _ => false

/-- The fixpoint route stores the family's own result-sort datum: the
former's telescope ends in `Sort p.resSort`, so the record's `sortZ`
is `piResultZ` of the type the install stores (`capsNeverZero_eq`). -/
theorem nativeCaps_sortZ {p : NativeParts} {c : ConstantVal × Nat}
    {e : Expr} (hc : p.ctors = [c]) (he : e.piResult = .sort p.resSort) :
    (nativeCaps p).sortZ = piResultZ e := by
  unfold nativeCaps nativeCapsAt piResultZ
  rw [hc, he]

/-- Does the variable `q` occur as a leaf of `e` (annotations
included, as `fvarLeaves` walks them)? -/
def Expr.mentionsFvar (q : Nat) (e : Expr) : Bool := e.fvarLeaves.any fun l => l.1 == q

/-! ### `mentionsFvar` memoizes

`Expr.fvarLeaves` returns a list that IS tree-sized by construction,
so it cannot be memoized where it stands; the fix belongs to its
consumer.  `mentionsFvar` asks a `Bool` question of it, and that
question memoizes: the answer at a node is a function of the node and
`q` alone, so one hash map keyed by the node — `q` is fixed for the
whole walk, unlike `hasLooseBVarB`'s index — shares the answer across
every path that reaches a shared node.

**There is no cutoff to put in front of it.**  The packed `fvarB`
field is the fvar range of a node's *own* spine and stops at an
`fvar` leaf (`fvarRange (.fvar idx _) = idx + 1`), while `fvarLeaves`
descends hereditarily into the leaf's TYPE ANNOTATION, so
`e.fvarB ≤ q` does not license "`q` does not occur in `e`" — the
range field cannot answer this question at all, and the memo is the
whole remedy.

`tests/e2e/tower_recfield.ndjson` — a recursive structure whose field
after the recursive one is a depth-60 tower over the FIRST field's
variable — is what walks it: `nativeOpenedOk` asks whether the
recursive field's variable occurs in any later field's domain, the
answer is `false`, and nothing short-circuits. -/

/-- `mentionsFvar` at an `fvar` leaf: the index, or its annotation. -/
theorem Expr.mentionsFvar_fvar (q idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).mentionsFvar q = ((idx == q) || ty.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_app (q : Nat) (f a : Expr) :
    (Expr.app f a).mentionsFvar q = (f.mentionsFvar q || a.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_lam (q : Nat) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).mentionsFvar q = (ty.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_forallE (q : Nat) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).mentionsFvar q
      = (ty.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_letE (q : Nat) (t v b : Expr) :
    (Expr.letE t v b).mentionsFvar q
      = (t.mentionsFvar q || v.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves, Bool.or_assoc]

theorem Expr.mentionsFvar_proj (q : Nat) (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).mentionsFvar q = e.mentionsFvar q := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

/-- The memo's invariant: every recorded answer is the real one. -/
def MentionsFvarMemoInv (q : Nat) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (e : Expr) (r : Bool), memo[e]? = some r → r = e.mentionsFvar q

theorem MentionsFvarMemoInv.empty {q : Nat} : MentionsFvarMemoInv q {} := by
  intro e r h; simp at h

theorem MentionsFvarMemoInv.insert {q : Nat} {memo : Std.HashMap Expr Bool}
    (hm : MentionsFvarMemoInv q memo) {e : Expr} {r : Bool}
    (heq : r = e.mentionsFvar q) :
    MentionsFvarMemoInv q (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm e' r' hk

/-- Record one answer for `e` in the memo the walk hands back.
Written with projections rather than a destructuring `let` so that the
correctness proof can `split` the walk's own matches. -/
@[inline] def Expr.mentionsFvarIns (e : Expr)
    (r : Bool × Std.HashMap Expr Bool) : Bool × Std.HashMap Expr Bool :=
  (r.1, r.2.insert e r.1)

/-- Memoized `mentionsFvar`. -/
def Expr.mentionsFvarGo (q : Nat) (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  match e with
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .const .. => (false, memo)
  | .lit _ => (false, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      Expr.mentionsFvarIns e <|
        match e with
        | .fvar idx ty =>
          if idx == q then (true, memo) else mentionsFvarGo q memo ty
        | .app f a =>
          match mentionsFvarGo q memo f with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo a
        | .lam ty b _ =>
          match mentionsFvarGo q memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo b
        | .forallE ty b _ =>
          match mentionsFvarGo q memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo b
        | .letE t v b =>
          match mentionsFvarGo q memo t with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match mentionsFvarGo q memo v with
            | (true, memo) => (true, memo)
            | (false, memo) => mentionsFvarGo q memo b
        | .proj _ _ sub => mentionsFvarGo q memo sub
        | _ => (false, memo)

/-- **The memoized walk is `mentionsFvar`.** -/
theorem Expr.mentionsFvarGo_spec (q : Nat) :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), MentionsFvarMemoInv q memo →
      (mentionsFvarGo q memo e).1 = e.mentionsFvar q ∧
        MentionsFvarMemoInv q (mentionsFvarGo q memo e).2 := by
  intro e
  induction e with
  | bvar j =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | sort u =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | const n us =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | lit l =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | fvar idx ty ih =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · simp only [mentionsFvarIns]
      split
      · rename_i hq
        refine ⟨by simp [mentionsFvar_fvar, hq], hm.insert (by simp [mentionsFvar_fvar, hq])⟩
      · rename_i hq
        obtain ⟨h1, h2⟩ := ih memo hm
        exact ⟨by simp [mentionsFvar_fvar, hq, h1], h2.insert (by simp [mentionsFvar_fvar, hq, h1])⟩
  | app f a ihf iha =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ihf memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_app, ← h1], h2.insert (by simp [mentionsFvar_app, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := iha memo₁ h2
        exact ⟨by simp [mentionsFvar_app, ← h1, h3],
          h4.insert (by simp [mentionsFvar_app, ← h1, h3])⟩
  | lam ty b m iht ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_lam, ← h1], h2.insert (by simp [mentionsFvar_lam, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihb memo₁ h2
        exact ⟨by simp [mentionsFvar_lam, ← h1, h3],
          h4.insert (by simp [mentionsFvar_lam, ← h1, h3])⟩
  | forallE ty b m iht ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_forallE, ← h1],
          h2.insert (by simp [mentionsFvar_forallE, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihb memo₁ h2
        exact ⟨by simp [mentionsFvar_forallE, ← h1, h3],
          h4.insert (by simp [mentionsFvar_forallE, ← h1, h3])⟩
  | letE t v b iht ihv ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_letE, ← h1],
          h2.insert (by simp [mentionsFvar_letE, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihv memo₁ h2
        split
        · rename_i memo₂ heq₂
          rw [heq₂] at h3 h4
          exact ⟨by simp [mentionsFvar_letE, ← h1, ← h3],
            h4.insert (by simp [mentionsFvar_letE, ← h1, ← h3])⟩
        · rename_i memo₂ heq₂
          rw [heq₂] at h3 h4
          obtain ⟨h5, h6⟩ := ihb memo₂ h4
          exact ⟨by simp [mentionsFvar_letE, ← h1, ← h3, h5],
            h6.insert (by simp [mentionsFvar_letE, ← h1, ← h3, h5])⟩
  | proj s j sub ih =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      simp only [mentionsFvarIns]
      exact ⟨by simp [mentionsFvar_proj, h1], h2.insert (by simp [mentionsFvar_proj, h1])⟩

/-- The executed `mentionsFvar` (one memoized DAG walk). -/
def Expr.mentionsFvarFast (q : Nat) (e : Expr) : Bool :=
  (Expr.mentionsFvarGo q {} e).1

@[csimp] theorem Expr.mentionsFvar_eq_mentionsFvarFast :
    @Expr.mentionsFvar = @Expr.mentionsFvarFast := by
  funext q e
  exact (mentionsFvarGo_spec q e {} MentionsFvarMemoInv.empty).1.symm

/-- The kinds the recogniser computed, re-checked on the annotated
constructor type OPENED at variables (`openPisAtFvars`, as the stage
read it): an ordinary field's domain resolves in the pre-block
environment `env₀`; a recursive field's domain is the family at the
opened parameter variables followed by `nIdx` index expressions
resolving in `env₀`, and the variable occurs in no later field's
domain nor in the residual (the model reads those at a frame whose
recursive slots hold an arbitrary member of the family being defined);
the residual's index expressions resolve in `env₀`. -/
def nativeOpenedOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => x.fvarTypeD.constsResolve env₀
        | some x, .recursive =>
          x.fvarTypeD.getAppFn == Expr.const T (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdx &&
          (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive =>
          -- the field's own telescope, OPENED at variables at the field's
          -- depth (as the constructor's was): its domains resolve in
          -- `env₀` (so they are free of the block), its body is the family
          -- at the parameter variables and `nIdx` index expressions
          -- resolving in `env₀` (task #202)
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => a.fvarTypeD.constsResolve env₀) &&
            body.getAppFn == Expr.const T (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdx &&
            (body.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- The kinds, re-checked on every annotated constructor
(`nativeOpenedOk`), one kind list per constructor, one kind per
field. -/
def nativeFieldsOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && nativeOpenedOk env₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => false

/-- The generated rules for constructors `j, j+1, …` (`k` of them),
each scoped at the environment holding the recursor's constant
(`envR`): a rule mentions the recursor and is not inferred. -/
def checkNativeRules (envR : Env) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRules envR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- Stage 3: the recursor, generated and compared — the generated
type has the inductive-hypothesis binders in each minor
(`structRecTyR`); the generated rules are scoped at the environment
holding the recursor's constant. -/
def checkNativeRec (ops : CheckerOps m) (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- THE RECURSOR PIN (task #220), split off the type-and-constructor
  -- gate above and thrown here: official generates the recursor and its
  -- replay compares the exported record with the generated one
  -- structurally, so a record naming something other than the generated
  -- `T.rec` ("No such recursor") or contradicting it in its argument
  -- sums or its rules ("Invalid recursor") is INVALID INPUT
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let envR : Env := ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩
  let rhss ← checkNativeRules envR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- Stage 4 (task #210 Part A): **the projection table** at a
STRUCTURE-LIKE block — one constructor, no index — the direct
structure route's table (`checkStructProjTable`: the fields' bodies
off the annotated constructor type, the guard levels from the
constructors' stage's field sorts) at the TAGGED tower's projection
offset `1` (`ProjTable.off`: the carrier's first pair component is
the constructor tag); nothing at any other block. -/
def checkNativeTable (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (env : Env) : m Env :=
  match ctorsA, sortss with
  | [cA], [sorts] =>
    if p.nIdx == 0 then
      checkStructProjTable p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 env
    else pure env
  | _, _ => pure env

/-- **What one pass over the former and the constructors yields**
(task #268; `E` is the environment representation — `Env` at the pure
install, `FEnv` at the cached driver's mirror): the former's
environment, the annotated former, the record completed with the sort
the former's run read and the kinds the pass classified, the
annotated constructors and their fields' sorts. -/
structure NativePass (E : Type) where
  /-- the environment holding the former, at the record the pass ran at -/
  env₁ : E
  /-- the annotated former -/
  cvTa : ConstantVal
  /-- the completed record: the sort read, the kinds classified -/
  p : NativeParts
  /-- the annotated (normalised) constructors -/
  ctorsA : List (ConstantVal × Nat)
  /-- the fields' sorts, one list per constructor -/
  sortss : List (List Level)

/-- **The fields' kinds, classified at install** (task #210 Part D) on
the stored constructors — their field domains normalised by official's
positivity walk (`normCtorVal`), so the syntactic classification
(`recCtorKinds`) is official's: a non-positive or non-valid occurrence
is INVALID (official's "non positive occurrence", "non valid
occurrence", "invalid return type"), a nested occurrence — the one
positive occurrence the route does not model — a positive decline. -/
def classifyFixKinds (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) : m (List (List RecFieldKind)) := do
  let kinds ← unwrapOr (ctorsA.mapM (recCtorKinds T lps nP nIdx))
    (.notImplemented "direct rec: constructor telescope")
  if kinds.any (fun ks => ks.any (· == .negative)) then
    throw (.invalid "direct rec: non positive or non valid occurrence of the inductive type")
  if kinds.any (fun ks => ks.any (· == .unsupported)) then
    throw (.notImplemented "direct rec: a nested occurrence of the block (not modeled here)")
  pure kinds

/-- **One pass over the former and the constructors** (task #268) at
a given `is_rec` verdict: the former with the capability record at
that verdict (`nativeCapsAt`), the constructors at the former's
environment (normalised, checked; the resolution guard pointed at
that same environment), the kinds classified on THOSE constructors
(`classifyFixKinds`) and the record completed with them.  The last
component says whether the classification confirms the verdict the
pass ran at: `nativeCaps p` is the record the block owes, and it is
the one the former carries exactly then. -/
def checkNativePass (ops : CheckerOps m) (env : Env) (p₀ : NativeParts) (isRec : Bool) :
    m (NativePass Env × Bool) := do
  let (env₁, cvTa, p₁) ← checkSumInd ops env p₀.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)
  let pC := p₀.complete p₁
  let (ctorsA, sortss) ← checkSumCtors ops env₁ env₁ pC.cvT.name pC.cvT.levelParams pC.nP
    pC.nIdx pC.resSort pC.isProp pC.large cvTa pC.ctors
  let kinds ← classifyFixKinds pC.cvT.name pC.cvT.levelParams pC.nP pC.nIdx ctorsA
  let p := pC.withKinds kinds
  pure (⟨env₁, cvTa, p, ctorsA, sortss⟩, nativeCaps p == nativeCapsAt p₁ isRec)

/-- **The install after the pass** (task #268): the elimination
restriction, the index binders' sorts, the kinds re-checked, the
stream's rules against the generated ones, the constructors consed,
the recursor with its rules, and — at a structure-like block — the
projection table (`checkNativeTable`, task #210 Part A). -/
def checkNativeTail (ops : CheckerOps m) (env : Env) (q : NativePass Env) : m Env := do
  let p := q.p
  -- a large eliminator on a block whose sort may be `Prop`: two or more
  -- constructors is `.invalid` (official's `elim_only_at_universe_zero`);
  -- one constructor is the subsingleton case, taken (task #202 Stage
  -- A2) with the per-field criterion at `checkStructFieldSortsI`
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  -- the index binders' universes, exposed for the model's index-tuple
  -- universe: the former's telescope opened at variables, each index
  -- domain's sort inferred (no bound is checked — `isProp` set,
  -- `large` unset — the sorts are read, not compared)
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsI ops q.env₁ true false p.resSort p.nP (tq.1.drop p.nP) []
    p.nIdx
  -- the kinds, re-checked on the stored (normalised) constructors in
  -- the opened form the model reads
  unless nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx q.ctorsA p.kinds do
    throw (.internal "direct rec: field kinds")
  -- the stream's rules are the generated ones (official's replay
  -- compares the exported recursor structurally with its own)
  unless nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      q.ctorsA p.kinds p.rhss p.cvR.type do
    throw (.invalid "direct rec: recursor rules are not the generated ones")
  let env₂ := consSumCtors p.nP q.ctorsA q.env₁
  let (cvRa, rhss) ← checkNativeRec ops env₂ p q.cvTa q.ctorsA
  checkNativeTable p q.ctorsA q.sortss ⟨.recInfo cvRa p.majorIdx p.rulePrefix
    (sumRules env₂.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type
      q.ctorsA rhss) :: env₂.consts⟩

/-- Check and install a **direct recursive block**: the distinct
names, the pass over the former (with the block's capability record)
and the constructors — again where the record's syntactic reading
overshot — and the install after it (`checkNativeTail`). -/
def checkNative (ops : CheckerOps m) (env : Env) (p₀ : NativeParts) : m Env := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  -- THE CAPABILITY RECORD'S VERDICT (task #268; before it, task #210
  -- Part D's provisional pass): the record (`nativeCaps`) needs the
  -- fields' kinds — official's `is_rec` — and the kinds need the
  -- constructors normalised at an environment where the former
  -- resolves, which carries the record.  The pass runs at the
  -- syntactic reading of `is_rec` (`nativeRawRec`), which the
  -- classification of the constructors it stored confirms at every
  -- block but one whose declared field domain mentions the block
  -- under a redex that reduces it away; there the block is passed
  -- again at the classified verdict, which then stands (the second
  -- pass stores the same constructors the first did, so a verdict
  -- that moved again is an internal error, never a decline).
  -- (Official adds the whole block in one step; this is the same
  -- information in one pass, and two where the reading overshot.)
  let (q, settled) ← checkNativePass ops env p₀ (nativeRawRec p₀)
  if settled then checkNativeTail ops env q
  else do
    let (q', settled') ← checkNativePass ops env p₀ (nativeIsRec q.p.kinds)
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkNativeTail ops env q'

end ConLeche
