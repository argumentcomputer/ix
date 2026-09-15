/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqMemo

/-!
# The quick structural DefEq tier under the contracts

Tier 1 of production conversion compares sorts by universe equality and
matching binders by opening both bodies with one common fresh local. This
module proves it sound against the checker invariant with the recursive
conversion callback abstracted by its contract: universe equality is
`univEq_sound` read into the model, and a binder comparison composes the
domain answer, the actual production binder opening, and the body answer into
lambda or dependent-function congruence. Every other constructor pair returns
`false` without touching the state.

The binder case consumes premises the contracts do not yet supply, stated in
`DefEqBinderAssumptions`: typing of the domains and bodies of a typed binder,
agreement of the two root annotations of a binder pair the tier accepts, and
the synthesis origin of the pushed context. Constant-instance and
argument-spine congruence are proved here for the later same-head tiers.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Outcome-directed reasoning through the monad -/

theorem EStateM.bind_cases {ε σ α γ : Type} {action : EStateM ε σ α} {next : α → EStateM ε σ γ}
    {state : σ} {post : EStateM.Result ε σ γ → Prop}
    (ok : ∀ value after, action state = .ok value after → post (next value after))
    (error : ∀ err after, action state = .error err after → post (.error err after)) :
    post ((action >>= next) state) := by
  change post (EStateM.bind action next state)
  unfold EStateM.bind
  cases run : action state with
  | ok value after => exact ok value after run
  | error err after => exact error err after run

/-- Scope cleanup as a pure map on outcomes. -/
def scopedResult {α : Type} (before : TcState .anon) :
    EStateM.Result (TcError .anon) (TcState .anon) α →
      EStateM.Result (TcError .anon) (TcState .anon) α
  | .ok value after => .ok value {after with lctx := after.lctx.truncate before.lctx.size}
  | .error err after => .error err {after with lctx := after.lctx.truncate before.lctx.size}

theorem withLctxScope_run {α : Type} (action : RecM .anon α) (methods : Methods .anon)
    (before : TcState .anon) :
    (RecM.withLctxScope action).run methods before = scopedResult before (action.run methods before) := by
  rw [withLctxScope_eq]
  cases action.run methods before <;> rfl

theorem intern_eq (term : KExpr .anon) (state : TcState .anon) :
    TcM.intern term state = .ok (state.env.intern.internExpr term).1
      {state with env := {state.env with intern := (state.env.intern.internExpr term).2}} := rfl

theorem runIntern_eq {α : Type} (action : InternM .anon α) (state : TcState .anon) :
    TcM.runIntern action state = .ok (action state.env.intern).1
      {state with env := {state.env with intern := (action state.env.intern).2}} := rfl

theorem isDefEqCall_run (left right : KExpr .anon) (methods : Methods .anon) :
    (RecM.isDefEqCall left right).run methods = methods.isDefEq left right := rfl

/-! ### Annotated readings of the compared shapes -/

section Readings

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

private theorem bind_some {α γ : Type _} {action : Option α} {next : α → Option γ} {result : γ}
    (run : action.bind next = some result) :
    ∃ value, action = some value ∧ next value = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem readScopedExpr?_sort_annotated {level : KUniv .anon} {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.sort level info) = some a.erase) :
    a = .sort (readLevel level) := by
  have erased : a.erase = .sort (readLevel level) := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  rfl

theorem readScopedExpr?_const_annotated {id : KId .anon} {levels : Array (KUniv .anon)}
    {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.const id levels info) = some a.erase) :
    ∃ ref, resolve id.addr = some ref ∧ a = .const ref (levels.toList.map readLevel) := by
  rw [readScopedExpr?] at reading
  obtain ⟨ref, resolved, reading⟩ := bind_some reading
  exact ⟨ref, resolved, AExpr.eq_const_of_erase_eq (Option.some.inj reading).symm⟩

theorem readScopedExpr?_lam_annotated {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.lam name bi domain body info) = some a.erase) :
    ∃ (condition : Certified.PropWhen) (A b : AExpr β), a = .lam condition A b ∧
      readScopedExpr? resolve locals domain = some A.erase ∧
      readScopedExpr? resolve locals body 1 = some b.erase := by
  rw [readScopedExpr?] at reading
  obtain ⟨A', domainReads, reading⟩ := bind_some reading
  obtain ⟨b', bodyReads, reading⟩ := bind_some reading
  have erased : a.erase = .lam A' b' := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  exact ⟨_, _, _, rfl, domainReads, bodyReads⟩

theorem readScopedExpr?_all_annotated {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.all name bi domain body info) = some a.erase) :
    ∃ (condition : Certified.PropWhen) (A B : AExpr β), a = .forallE condition A B ∧
      readScopedExpr? resolve locals domain = some A.erase ∧
      readScopedExpr? resolve locals body 1 = some B.erase := by
  rw [readScopedExpr?] at reading
  obtain ⟨A', domainReads, reading⟩ := bind_some reading
  obtain ⟨B', bodyReads, reading⟩ := bind_some reading
  have erased : a.erase = .forallE A' B' := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  exact ⟨_, _, _, rfl, domainReads, bodyReads⟩

end Readings

/-! ### Constant instances with pointwise equal universes -/

section Levels

variable {β : Type u} {entries : Model.Environment β} {context : Model.Context β}

/-- The model has no rule for two instances of one constant at pointwise
equivalent levels; the interpretation depends only on the evaluated levels. -/
theorem ConversionClaim.constLevels {ref : ConstRef β} {left right : List VLevel}
    (levels : ∀ values, left.map (VLevel.eval values) = right.map (VLevel.eval values)) :
    ConversionClaim.{u,v} entries context (.const ref left) (.const ref right) := by
  intro V _ constants _ values env _
  exact congrArg (constants ref) (levels values)

private theorem zip_levels : ∀ (left right : List (KUniv .anon)), left.length = right.length →
    RecM.allDefEqUniversesList (left.zip right) = true →
    (∀ u ∈ left, ∀ v ∈ right, u.AddrFaithful v ∧ u.size < UInt64.size ∧ v.size < UInt64.size) →
    ∀ values, (left.map readLevel).map (VLevel.eval values) =
      (right.map readLevel).map (VLevel.eval values)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, lengths, _, _, _ => absurd lengths (by simp)
  | _ :: _, [], lengths, _, _, _ => absurd lengths (by simp)
  | l :: ls, r :: rs, lengths, accepted, resources, values => by
      simp only [List.zip_cons_cons, RecM.allDefEqUniversesList, Bool.and_eq_true] at accepted
      obtain ⟨faithful, boundL, boundR⟩ :=
        resources l (List.mem_cons_self ..) r (List.mem_cons_self ..)
      have head := Theory.VLevel.equiv_def.mp (univEq_sound faithful boundL boundR accepted.1) values
      have tail := zip_levels ls rs (by simpa using lengths) accepted.2
        (fun u hu v hv => resources u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)) values
      simp only [List.map_cons, head, tail]

/-- The production universe gate of constant-headed comparisons decides
pointwise level equality under faithfulness and size bounds of the levels. -/
theorem sameDefEqUniverses_sound {left right : Array (KUniv .anon)}
    (accepted : RecM.sameDefEqUniverses left right = true)
    (resources : ∀ u ∈ left, ∀ v ∈ right, u.AddrFaithful v ∧ u.size < UInt64.size ∧ v.size < UInt64.size) :
    ∀ values, (left.toList.map readLevel).map (VLevel.eval values) =
      (right.toList.map readLevel).map (VLevel.eval values) := by
  simp only [RecM.sameDefEqUniverses, Bool.and_eq_true, beq_iff_eq] at accepted
  obtain ⟨sizes, pairs⟩ := accepted
  rw [Array.toList_zip] at pairs
  exact zip_levels left.toList right.toList (by simpa using sizes) pairs
    (fun u hu v hv => resources u (by simpa using hu) v (by simpa using hv))

/-- Two readable instances of one constant that pass the universe gate are
convertible. -/
theorem ConversionClaim.constInstances {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {leftId rightId : KId .anon} {leftUs rightUs : Array (KUniv .anon)}
    {leftInfo rightInfo : ExprInfo .anon} {a b : AExpr β}
    (leftReads : readScopedExpr? resolve locals (.const leftId leftUs leftInfo) = some a.erase)
    (rightReads : readScopedExpr? resolve locals (.const rightId rightUs rightInfo) = some b.erase)
    (sameHead : leftId.addr = rightId.addr)
    (accepted : RecM.sameDefEqUniverses leftUs rightUs = true)
    (resources : ∀ u ∈ leftUs, ∀ v ∈ rightUs,
      u.AddrFaithful v ∧ u.size < UInt64.size ∧ v.size < UInt64.size) :
    ConversionClaim.{u,v} entries context a b := by
  obtain ⟨ref, resolved, aEq⟩ := readScopedExpr?_const_annotated leftReads
  obtain ⟨ref', resolved', bEq⟩ := readScopedExpr?_const_annotated rightReads
  rw [sameHead] at resolved
  cases Option.some.inj (resolved.symm.trans resolved')
  subst aEq bEq
  exact ConversionClaim.constLevels (sameDefEqUniverses_sound accepted resources)

end Levels

/-! ### Typing across a converted binder domain -/

section Domains

variable {β : Type u} {entries : Model.Environment β} {context : Model.Context β}

theorem contextValid_pushConverted {V : Type v} [SetTheory V] {constants : Assignment β V}
    {levels : List Nat} {A A' : AExpr β} {env : Nat → V}
    (valid : (context.push A).Valid constants levels env)
    (denoted : WellDenoted constants levels (Valuation.skip 1 0 env) A')
    (same : interp constants levels (Valuation.skip 1 0 env) A =
      interp constants levels (Valuation.skip 1 0 env) A') :
    (context.push A').Valid constants levels env := by
  intro index B found
  cases index with
  | zero =>
      simp only [Model.Context.push, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      have head := valid 0 (A.liftN 1) rfl
      rw [wellDenoted_liftN, interp_liftN] at head ⊢
      exact ⟨denoted, same ▸ head.2⟩
  | succ index =>
      exact valid (index + 1) B
        (by simpa only [Model.Context.push, List.getElem?_cons_succ] using found)

/-- A term typed under the second domain of a binder pair is typed under the
first once the domains are convertible and the second is a type. -/
theorem TypingClaim.pushConverted {A A' term type : AExpr β} {level : VLevel}
    (formed : TypingClaim.{u,v} entries context A' (.sort level))
    (converted : ConversionClaim.{u,v} entries context A A')
    (typed : TypingClaim.{u,v} entries (context.push A') term type) :
    TypingClaim.{u,v} entries (context.push A) term type := by
  intro V _ constants realizes levels env valid
  have tail := context_valid_tail valid
  exact typed V constants realizes levels env
    (contextValid_pushConverted valid (formed V constants realizes levels _ tail).1
      (converted V constants realizes levels _ tail))

end Domains

/-! ### Resources and boundary premises of the quick tier -/

/-- Finite resources of one binder comparison at the state where the left
binder is opened: both bodies are constructed and bounded, and the intern
table, the fresh local, and both instantiation reaches are collision free. -/
structure QuickBinderData (state : TcState .anon) (body1 body2 : KExpr .anon) : Prop where
  constructed1 : body1.Constructed
  constructed2 : body2.Constructed
  bound1 : body1.size + 1 < UInt64.size
  bound2 : body2.size + 1 < UInt64.size
  faithful : KExpr.CollisionFree fun term =>
    state.env.intern.ExprSupport term ∨ term = KExpr.mkFVar ⟨state.env.nextFVarId⟩ () ∨
    KExpr.InstRevReach #[KExpr.mkFVar ⟨state.env.nextFVarId⟩ ()] body1 0 term ∨
    KExpr.InstRevReach #[KExpr.mkFVar ⟨state.env.nextFVarId⟩ ()] body2 0 term

theorem QuickBinderData.left {state : TcState .anon} {body1 body2 : KExpr .anon}
    (data : QuickBinderData state body1 body2) : BinderOpeningData state body1 :=
  ⟨data.constructed1, data.bound1, data.faithful.mono fun _ h =>
    h.elim Or.inl fun h => h.elim (fun equal => .inr (.inl equal)) fun reached =>
      .inr (.inr (.inl reached))⟩

section Premises

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- Premises of the binder case that the contracts do not supply: hereditary
typing of a typed binder's domain and body, agreement of the root annotations
of an accepted binder pair, and the synthesis origin of the pushed context. The
set model interprets annotations, so the agreement is a discipline on the
readings and not a consequence of typing. -/
structure DefEqBinderAssumptions : Prop where
  lamHereditary : ∀ (context : Model.Context β) (condition : Certified.PropWhen)
    (domain body type : AExpr β),
    TypingClaim.{u,v} entries context (.lam condition domain body) type →
    (∃ level, TypingClaim.{u,v} entries context domain (.sort level)) ∧
    (∃ codomain, TypingClaim.{u,v} entries (context.push domain) body codomain)
  piHereditary : ∀ (context : Model.Context β) (condition : Certified.PropWhen)
    (domain body type : AExpr β),
    TypingClaim.{u,v} entries context (.forallE condition domain body) type →
    (∃ level, TypingClaim.{u,v} entries context domain (.sort level)) ∧
    (∃ level, TypingClaim.{u,v} entries (context.push domain) body (.sort level))
  lamAnnotations : ∀ (context : Model.Context β) (left right : Certified.PropWhen)
    (domain domain' body body' : AExpr β),
    (∃ type, TypingClaim.{u,v} entries context (.lam left domain body) type) →
    (∃ type, TypingClaim.{u,v} entries context (.lam right domain' body') type) →
    ConversionClaim.{u,v} entries context domain domain' →
    ConversionClaim.{u,v} entries (context.push domain) body body' → left = right
  piAnnotations : ∀ (context : Model.Context β) (left right : Certified.PropWhen)
    (domain domain' body body' : AExpr β),
    (∃ type, TypingClaim.{u,v} entries context (.forallE left domain body) type) →
    (∃ type, TypingClaim.{u,v} entries context (.forallE right domain' body') type) →
    ConversionClaim.{u,v} entries context domain domain' →
    ConversionClaim.{u,v} entries (context.push domain) body body' → left = right
  binderOrigin : ∀ (context : Model.Context β) (bounds : List VLevel) (domain : AExpr β)
    (level : VLevel),
    Nonempty (SynthesisContext resolve anchor [] [] entries context bounds) →
    TypingClaim.{u,v} entries context domain (.sort level) →
    Nonempty (SynthesisContext resolve anchor [] [] entries (context.push domain) (level :: bounds))

/-- Finite resources of the direct tiers over a support of compared operands,
each an instance of `RunAssumptions`: pairwise address faithfulness, universe
faithfulness and bounds at sorts, and binder-opening data at every invariant
state. -/
structure DefEqTierResources (support : KExpr .anon → Prop) : Prop where
  faithful : ∀ left right, support left → support right → left.AddrFaithful right
  sorts : ∀ (u w : KUniv .anon) (infoU infoW : ExprInfo .anon),
    support (.sort u infoU) → support (.sort w infoW) →
    u.AddrFaithful w ∧ u.size < UInt64.size ∧ w.size < UInt64.size
  lamData : ∀ (state : TcState .anon) (locals : List FVarId) (context : Model.Context β)
    (bounds : List VLevel),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    ∀ (name1 name2 : Mode.anon.F Name) (bi1 bi2 : Mode.anon.F Lean.BinderInfo)
      (ty1 body1 ty2 body2 : KExpr .anon) (info1 info2 : ExprInfo .anon),
      support (.lam name1 bi1 ty1 body1 info1) → support (.lam name2 bi2 ty2 body2 info2) →
      QuickBinderData state body1 body2
  piData : ∀ (state : TcState .anon) (locals : List FVarId) (context : Model.Context β)
    (bounds : List VLevel),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    ∀ (name1 name2 : Mode.anon.F Name) (bi1 bi2 : Mode.anon.F Lean.BinderInfo)
      (ty1 body1 ty2 body2 : KExpr .anon) (info1 info2 : ExprInfo .anon),
      support (.all name1 bi1 ty1 body1 info1) → support (.all name2 bi2 ty2 body2 info2) →
      QuickBinderData state body1 body2

/-- The binder tier's outcome at annotated readings of both domains and
bodies: the answer `true` establishes the domain conversion and the body
conversion under the first domain. -/
def QuickBinderPost (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (A₁ A₂ b₁ b₂ : AExpr β) : EStateM.Result (TcError .anon) (TcState .anon) Bool → Prop
  | .ok true after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ConversionClaim.{u,v} entries context A₁ A₂ ∧
      ConversionClaim.{u,v} entries (context.push A₁) b₁ b₂
  | .ok false after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end Premises

/-! ### The binder tier -/

section Binders

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- Interning one expression preserves the invariant once the updated table is coherent. -/
theorem CheckerInvariant.internStep {state : TcState .anon} {term : KExpr .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (coherent : (state.env.intern.internExpr term).2.WF) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with env := {state.env with intern := (state.env.intern.internExpr term).2}} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl

/-- Running an intern-table action preserves the invariant once the updated table is coherent. -/
theorem CheckerInvariant.runInternStep {α : Type} {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (action : InternM .anon α) (coherent : (action state.env.intern).2.WF) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with env := {state.env with intern := (action state.env.intern).2}} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl

/-- Successful binder opening from a coherent state, with the exact fresh
identifier, the opened body, the updated table's coherence and support, and
the unchanged fields the scope exit needs. -/
theorem openBinder_support {before after : TcState .anon} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {type body opened : KExpr .anon} {fresh : FVarId}
    (data : BinderOpeningData before body) (coherent : before.env.intern.WF)
    (run : TcM.openBinder name bi type body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
    opened = KExpr.instantiateRevSpec body #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()] 0 ∧
    after.env.intern.WF ∧
    (∀ term, after.env.intern.ExprSupport term → before.env.intern.ExprSupport term ∨
      term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ () ∨
      KExpr.InstRevReach #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()] body 0 term) := by
  have nameUnit : name = () := Subsingleton.elim _ _
  have biUnit : bi = () := Subsingleton.elim _ _
  subst nameUnit biUnit
  have interned : (before.env.intern.internExpr
      (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())).1 =
        KExpr.mkFVar ⟨before.env.nextFVarId⟩ () := by
    have faithful := KExpr.keyCollisionFree_anon.mpr
      (data.faithful.mono (fun _ h => h.elim Or.inl (fun equal => .inr (.inl equal))) :
        KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
          term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())
    simpa only [KExpr.eraseMeta_anon] using
      before.env.intern.internExpr_eraseMeta coherent faithful
  have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()])
    data.faithful data.constructed (by simpa using data.bound)
    (fun _ reached => .inr (.inr reached))
    (coherent.internExpr (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()))
    (fun _ member => (InternTable.ExprSupport.of_internExpr member).elim
      Or.inl (fun equal => .inr (.inl equal)))
  rw [openBinder_eq] at run
  split at run
  · simp only [interned] at run
    cases run
    exact ⟨rfl, walk.1, walk.2.1, walk.2.2⟩
  · contradiction

/-- The common-local binder comparison. The domain answer comes from the
recursive contract, the left body is opened by production, the right body is
instantiated with the same local, and the body answer is taken under the
first domain after transporting the right body's typing across the domain
conversion. Scope exit restores the caller's registration on every outcome. -/
theorem quickBinder_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    (frames : MethodsLocalState methods) {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {ty1 body1 ty2 body2 : KExpr .anon}
    {A₁ A₂ b₁ b₂ : AExpr β} {l₁ l₂ : VLevel}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (data : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      QuickBinderData state body1 body2)
    (ty1Reads : readScopedExpr? resolve locals ty1 = some A₁.erase)
    (ty2Reads : readScopedExpr? resolve locals ty2 = some A₂.erase)
    (body1Reads : readScopedExpr? resolve locals body1 1 = some b₁.erase)
    (body2Reads : readScopedExpr? resolve locals body2 1 = some b₂.erase)
    (ty1Typed : TypingClaim.{u,v} entries context A₁ (.sort l₁))
    (ty2Typed : TypingClaim.{u,v} entries context A₂ (.sort l₂))
    (body1Typed : ∃ type, TypingClaim.{u,v} entries (context.push A₁) b₁ type)
    (body2Typed : ∃ type, TypingClaim.{u,v} entries (context.push A₂) b₂ type)
    (pushed : Nonempty (SynthesisContext resolve anchor [] [] entries (context.push A₁) (l₁ :: bounds))) :
    QuickBinderPost.{u,v} resolve anchor entries source catalog locals context bounds A₁ A₂ b₁ b₂
      ((RecM.quickBinder name bi ty1 body1 ty2 body2).run methods before) := by
  have nameUnit : name = () := Subsingleton.elim _ _
  subst nameUnit
  have domains := recursive.isDefEq ty1 ty2 locals context bounds before A₁ A₂ valid ty1Reads
    ⟨_, ty1Typed⟩ ty2Reads ⟨_, ty2Typed⟩
  unfold RecM.quickBinder
  simp only [ReaderT.run_bind, isDefEqCall_run]
  refine EStateM.bind_cases ?_ ?_
  · intro answer middle domainRun
    rw [domainRun] at domains
    cases answer with
    | false =>
        simp only [Bool.not_false, ↓reduceIte]
        exact domains
    | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨valid', domainClaim⟩ := domains
        rw [withLctxScope_run]
        simp only [ReaderT.run_bind, ReaderT.run_monadLift, isDefEqCall_run]
        refine EStateM.bind_cases (post := fun result => QuickBinderPost.{u,v} resolve anchor entries
          source catalog locals context bounds A₁ A₂ b₁ b₂ (scopedResult middle result)) ?_ ?_
        · rintro ⟨opened, fresh⟩ afterOpen openRun
          have binderData := data middle valid'
          have absent := valid'.structural.freshReading valid'.reading
          have openRun' : TcM.openBinder () bi ty1 body1 middle = .ok (opened, fresh) afterOpen :=
            openRun
          have extension := PreservesLocalState.openBinder () bi ty1 body1 middle valid'.structural
          rw [openRun'] at extension
          obtain ⟨freshEq, openedEq, afterWF, afterSupport⟩ :=
            openBinder_support binderData.left valid'.coherent openRun'
          subst freshEq
          have validExt := valid'.openBinder binderData.left ty1Reads pushed openRun'
          have openedReads : readScopedExpr? resolve (⟨middle.env.nextFVarId⟩ :: locals) opened =
              some b₁.erase := by
            rw [openedEq]
            exact readScopedExpr?_instantiateRevSpec absent (by simpa using binderData.bound1) body1Reads
          have keyFaithful : KExpr.KeyCollisionFree fun term =>
              afterOpen.env.intern.ExprSupport term ∨
                term = KExpr.mkFVar ⟨middle.env.nextFVarId⟩ () :=
            KExpr.keyCollisionFree_anon.mpr (binderData.faithful.mono fun term h =>
              h.elim (fun member => (afterSupport term member).elim Or.inl fun h =>
                  h.elim (fun equal => .inr (.inl equal)) fun reached => .inr (.inr (.inl reached)))
                fun equal => .inr (.inl equal))
          have interned : (afterOpen.env.intern.internExpr
              (KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ())).1 =
                KExpr.mkFVar ⟨middle.env.nextFVarId⟩ () := by
            simpa only [KExpr.eraseMeta_anon] using
              afterOpen.env.intern.internExpr_eraseMeta afterWF keyFaithful
          dsimp only
          refine EStateM.bind_cases (post := fun result => QuickBinderPost.{u,v} resolve anchor entries
            source catalog locals context bounds A₁ A₂ b₁ b₂ (scopedResult middle result)) ?_ ?_
          · intro fv afterIntern internRun
            have internRun' : TcM.intern (KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()) afterOpen =
                .ok fv afterIntern := internRun
            rw [intern_eq] at internRun'
            obtain ⟨fvEq, stateEq₁⟩ := EStateM.Result.ok.inj internRun'
            rw [interned] at fvEq
            subst fvEq
            have table₃ := afterWF.internExpr (KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ())
            have internEq : afterIntern.env.intern =
                (afterOpen.env.intern.internExpr (KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ())).2 := by
              rw [← stateEq₁]
            have validIntern : CheckerInvariant.{u,v} resolve anchor entries source catalog
                (⟨middle.env.nextFVarId⟩ :: locals) (context.push A₁) (l₁ :: bounds) afterIntern := by
              rw [← stateEq₁]
              exact validExt.internStep table₃
            have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()])
              binderData.faithful binderData.constructed2 (by simpa using binderData.bound2)
              (fun _ reached => .inr (.inr (.inr reached))) table₃
              (fun term member => (InternTable.ExprSupport.of_internExpr member).elim
                (fun member => (afterSupport term member).elim Or.inl fun h =>
                  h.elim (fun equal => .inr (.inl equal)) fun reached => .inr (.inr (.inl reached)))
                fun equal => .inr (.inl equal))
            rw [← internEq] at walk
            refine EStateM.bind_cases (post := fun result => QuickBinderPost.{u,v} resolve anchor
              entries source catalog locals context bounds A₁ A₂ b₁ b₂ (scopedResult middle result))
              ?_ ?_
            · intro b2Open afterInst instRun
              have instRun' : TcM.runIntern
                  (instantiateRev body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()]) afterIntern =
                  .ok b2Open afterInst := instRun
              rw [runIntern_eq] at instRun'
              obtain ⟨b2OpenEq, stateEq₂⟩ := EStateM.Result.ok.inj instRun'
              rw [walk.1] at b2OpenEq
              subst b2OpenEq
              have b2OpenReads : readScopedExpr? resolve (⟨middle.env.nextFVarId⟩ :: locals)
                  (KExpr.instantiateRevSpec body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()] 0) =
                  some b₂.erase :=
                readScopedExpr?_instantiateRevSpec absent (by simpa using binderData.bound2) body2Reads
              have validInst : CheckerInvariant.{u,v} resolve anchor entries source catalog
                  (⟨middle.env.nextFVarId⟩ :: locals) (context.push A₁) (l₁ :: bounds) afterInst := by
                rw [← stateEq₂]
                exact validIntern.runInternStep _ walk.2.1
              have body2Typed' : ∃ type, TypingClaim.{u,v} entries (context.push A₁) b₂ type :=
                body2Typed.imp fun _ typed => TypingClaim.pushConverted ty2Typed domainClaim typed
              have inner := recursive.isDefEq opened
                (KExpr.instantiateRevSpec body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()] 0)
                (⟨middle.env.nextFVarId⟩ :: locals) (context.push A₁) (l₁ :: bounds) afterInst b₁ b₂
                validInst openedReads body1Typed b2OpenReads body2Typed'
              have innerFrame := frames.isDefEq opened
                (KExpr.instantiateRevSpec body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()] 0)
                afterInst validInst.structural
              have internFrame : LocalStateFrame afterOpen afterInst := by
                subst stateEq₂ stateEq₁
                exact ⟨Nat.le_refl _, .refl _, rfl⟩
              have exit : ∀ final, LocalStateFrame afterInst final →
                  LocalStateExtension middle final :=
                fun final frame => extension.trans (LocalStateExtension.of_frame validExt.structural
                  (internFrame.trans frame))
              cases innerRun : methods.isDefEq opened
                  (KExpr.instantiateRevSpec body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()] 0)
                  afterInst with
              | ok answer final =>
                  rw [innerRun] at inner innerFrame
                  have restored := exit final innerFrame
                  cases answer with
                  | false =>
                      exact valid'.exitScope inner restored.context restored.counter restored.loader
                  | true =>
                      exact ⟨valid'.exitScope inner.1 restored.context restored.counter restored.loader,
                        domainClaim, inner.2⟩
              | error err final =>
                  rw [innerRun] at inner innerFrame
                  have restored := exit final innerFrame
                  exact valid'.exitScope inner restored.context restored.counter restored.loader
            · intro err after instRun
              have instRun' : TcM.runIntern (instantiateRev body2 #[KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()]) _ =
                  .error err after := instRun
              rw [runIntern_eq] at instRun'
              cases instRun'
          · intro err after internRun
            have internRun' : TcM.intern (KExpr.mkFVar ⟨middle.env.nextFVarId⟩ ()) afterOpen =
                .error err after := internRun
            rw [intern_eq] at internRun'
            cases internRun'
        · intro err afterOpen openRun
          have openRun' : TcM.openBinder () bi ty1 body1 middle = .error err afterOpen := openRun
          rw [openBinder_eq] at openRun'
          split at openRun'
          · cases openRun'
          · cases openRun'
            exact valid'.exitScope valid' (.refl _) (Nat.le_refl _) rfl
  · intro err after domainRun
    rw [domainRun] at domains
    exact domains

end Binders

/-! ### The quick tier -/

section Quick

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The exact shape dispatch of the quick tier. -/
theorem quickDefEq_eq (left right : KExpr .anon) (methods : Methods .anon) (before : TcState .anon) :
    (RecM.quickDefEq left right).run methods before =
      match left, right with
      | .sort u1 _, .sort u2 _ => .ok (univEq u1 u2) before
      | .lam name bi ty1 body1 _, .lam _ _ ty2 body2 _ =>
          (RecM.quickBinder name bi ty1 body1 ty2 body2).run methods before
      | .all name bi ty1 body1 _, .all _ _ ty2 body2 _ =>
          (RecM.quickBinder name bi ty1 body1 ty2 body2).run methods before
      | _, _ => .ok false before := by
  unfold RecM.quickDefEq
  cases left <;> cases right <;> rfl

/-- Tier 1: sorts by universe equality, matching binders by the common-local
comparison, and every other shape pair rejected without state change. -/
theorem quickDefEq_sound {methods : Methods .anon} {support : KExpr .anon → Prop}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    (frames : MethodsLocalState methods)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqTierResources.{u,v} resolve anchor entries source catalog support)
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {before : TcState .anon}
    {left right : KExpr .anon} {a b : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftMember : support left) (rightMember : support right)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((RecM.quickDefEq left right).run methods before) := by
  rw [quickDefEq_eq]
  split
  · rename_i u1 info1 u2 info2
    cases accepted : univEq u1 u2
    · exact valid
    · obtain ⟨faithful, boundU, boundV⟩ := resources.sorts u1 u2 info1 info2 leftMember rightMember
      have aEq := readScopedExpr?_sort_annotated leftReads
      have bEq := readScopedExpr?_sort_annotated rightReads
      subst aEq bEq
      exact ⟨valid, ConversionClaim.sort
        (Theory.VLevel.equiv_def.mp (univEq_sound faithful boundU boundV accepted))⟩
  · rename_i name1 bi1 ty1 body1 info1 name2 bi2 ty2 body2 info2
    obtain ⟨p, A₁, b₁, aEq, ty1Reads, body1Reads⟩ := readScopedExpr?_lam_annotated leftReads
    obtain ⟨q, A₂, b₂, bEq, ty2Reads, body2Reads⟩ := readScopedExpr?_lam_annotated rightReads
    subst aEq bEq
    obtain ⟨T₁, aTyped⟩ := leftTyped
    obtain ⟨T₂, bTyped⟩ := rightTyped
    obtain ⟨⟨l₁, ty1Typed⟩, body1Typed⟩ := binders.lamHereditary context p A₁ b₁ T₁ aTyped
    obtain ⟨⟨l₂, ty2Typed⟩, body2Typed⟩ := binders.lamHereditary context q A₂ b₂ T₂ bTyped
    have pushed := binders.binderOrigin context bounds A₁ l₁ valid.origin ty1Typed
    have post := quickBinder_sound (name := name1) (bi := bi1) recursive frames valid
      (fun state valid' => resources.lamData state locals context bounds valid' name1 name2 bi1 bi2
        ty1 body1 ty2 body2 info1 info2 leftMember rightMember)
      ty1Reads ty2Reads body1Reads body2Reads ty1Typed ty2Typed body1Typed body2Typed pushed
    cases run : (RecM.quickBinder name1 bi1 ty1 body1 ty2 body2).run methods before with
    | ok answer after =>
        rw [run] at post
        cases answer with
        | false => exact post
        | true =>
            obtain ⟨valid', domainClaim, bodyClaim⟩ := post
            have same := binders.lamAnnotations context p q A₁ A₂ b₁ b₂ ⟨T₁, aTyped⟩ ⟨T₂, bTyped⟩
              domainClaim bodyClaim
            subst same
            exact ⟨valid', ConversionClaim.lam ty1Typed domainClaim bodyClaim⟩
    | error err after =>
        rw [run] at post
        exact post
  · rename_i name1 bi1 ty1 body1 info1 name2 bi2 ty2 body2 info2
    obtain ⟨p, A₁, B₁, aEq, ty1Reads, body1Reads⟩ := readScopedExpr?_all_annotated leftReads
    obtain ⟨q, A₂, B₂, bEq, ty2Reads, body2Reads⟩ := readScopedExpr?_all_annotated rightReads
    subst aEq bEq
    obtain ⟨T₁, aTyped⟩ := leftTyped
    obtain ⟨T₂, bTyped⟩ := rightTyped
    obtain ⟨⟨l₁, ty1Typed⟩, ⟨s₁, body1Typed⟩⟩ := binders.piHereditary context p A₁ B₁ T₁ aTyped
    obtain ⟨⟨l₂, ty2Typed⟩, ⟨s₂, body2Typed⟩⟩ := binders.piHereditary context q A₂ B₂ T₂ bTyped
    have pushed := binders.binderOrigin context bounds A₁ l₁ valid.origin ty1Typed
    have post := quickBinder_sound (name := name1) (bi := bi1) recursive frames valid
      (fun state valid' => resources.piData state locals context bounds valid' name1 name2 bi1 bi2
        ty1 body1 ty2 body2 info1 info2 leftMember rightMember)
      ty1Reads ty2Reads body1Reads body2Reads ty1Typed ty2Typed ⟨_, body1Typed⟩ ⟨_, body2Typed⟩ pushed
    cases run : (RecM.quickBinder name1 bi1 ty1 body1 ty2 body2).run methods before with
    | ok answer after =>
        rw [run] at post
        cases answer with
        | false => exact post
        | true =>
            obtain ⟨valid', domainClaim, bodyClaim⟩ := post
            have same := binders.piAnnotations context p q A₁ A₂ B₁ B₂ ⟨T₁, aTyped⟩ ⟨T₂, bTyped⟩
              domainClaim bodyClaim
            subst same
            exact ⟨valid', ConversionClaim.forallE ty1Typed domainClaim bodyClaim⟩
    | error err after =>
        rw [run] at post
        exact post
  · exact valid

end Quick

/-! ### Argument spines -/

section Spines

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
  (context : Model.Context β) (bounds : List VLevel)

/-- Typed annotated readings of an argument-pair list, in order. -/
inductive SpineReadings : List (KExpr .anon × KExpr .anon) → List (AExpr β × AExpr β) → Prop
  | nil : SpineReadings [] []
  | cons {left right : KExpr .anon} {a b : AExpr β} {pairs : List (KExpr .anon × KExpr .anon)}
      {terms : List (AExpr β × AExpr β)}
      (leftReads : readScopedExpr? resolve locals left = some a.erase)
      (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
      (rightReads : readScopedExpr? resolve locals right = some b.erase)
      (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type)
      (rest : SpineReadings pairs terms) :
      SpineReadings ((left, right) :: pairs) ((a, b) :: terms)

/-- The spine loop's outcome: `true` establishes every pairwise conversion. -/
def SpineConversionPost (terms : List (AExpr β × AExpr β)) :
    EStateM.Result (TcError .anon) (TcState .anon) Bool → Prop
  | .ok true after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∀ term ∈ terms, ConversionClaim.{u,v} entries context term.1 term.2
  | .ok false after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end Spines

section SpineLemmas

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

theorem allDefEqSpineArgsList_cons (left right : KExpr .anon)
    (rest : List (KExpr .anon × KExpr .anon)) (methods : Methods .anon) (before : TcState .anon) :
    (RecM.allDefEqSpineArgsList ((left, right) :: rest)).run methods before =
      match methods.isDefEq left right before with
      | .error err after => .error err after
      | .ok false after => .ok false after
      | .ok true after => (RecM.allDefEqSpineArgsList rest).run methods after := by
  rw [RecM.allDefEqSpineArgsList]
  simp only [ReaderT.run_bind, isDefEqCall_run]
  change EStateM.bind (methods.isDefEq left right) _ before = _
  unfold EStateM.bind
  cases methods.isDefEq left right before with
  | error err after => rfl
  | ok answer after => cases answer <;> rfl

/-- Left-to-right argument comparison through the recursive contract. -/
theorem allDefEqSpineArgsList_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    {pairs : List (KExpr .anon × KExpr .anon)} {terms : List (AExpr β × AExpr β)}
    (readings : SpineReadings.{u,v} resolve entries locals context pairs terms) :
    ∀ {before : TcState .anon},
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
      SpineConversionPost.{u,v} resolve anchor entries source catalog locals context bounds terms
        ((RecM.allDefEqSpineArgsList pairs).run methods before) := by
  induction readings with
  | nil =>
      intro before valid
      exact ⟨valid, fun _ member => nomatch member⟩
  | @cons left right a b pairs terms leftReads leftTyped rightReads rightTyped _ ih =>
      intro before valid
      rw [allDefEqSpineArgsList_cons]
      have post := recursive.isDefEq left right locals context bounds before a b valid leftReads
        leftTyped rightReads rightTyped
      cases run : methods.isDefEq left right before with
      | error err after =>
          rw [run] at post
          exact post
      | ok answer after =>
          rw [run] at post
          cases answer with
          | false => exact post
          | true =>
              obtain ⟨valid', claim⟩ := post
              have tail := ih valid'
              dsimp only
              cases run' : (RecM.allDefEqSpineArgsList pairs).run methods after with
              | error err final =>
                  rw [run'] at tail
                  exact tail
              | ok answer' final =>
                  rw [run'] at tail
                  cases answer' with
                  | false => exact tail
                  | true =>
                      obtain ⟨valid'', claims⟩ := tail
                      refine ⟨valid'', fun term member => ?_⟩
                      rcases List.mem_cons.mp member with rfl | member
                      · exact claim
                      · exact claims term member

/-- The array entry point is the list loop on the array's elements. -/
theorem allDefEqSpineArgs_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    {pairs : Array (KExpr .anon × KExpr .anon)} {terms : List (AExpr β × AExpr β)}
    (readings : SpineReadings.{u,v} resolve entries locals context pairs.toList terms)
    {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    SpineConversionPost.{u,v} resolve anchor entries source catalog locals context bounds terms
      ((RecM.allDefEqSpineArgs pairs).run methods before) :=
  allDefEqSpineArgsList_sound recursive readings valid

end SpineLemmas

end Ix.Kernel.Consistency
