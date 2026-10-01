module

public import ConLeche.Kernel.Core

public section

/-!
# Environment well-formedness

`EnvWF` collects the syntactic facts the checker establishes for every
accepted constant — closed, level parameters within the declared list,
referenced constants resolving — as an invariant of the environment.  The
delta-unfolding and monotonicity lemmas need it.
-/

namespace ConLeche

/-- The projection-table name shape is injective. -/
theorem projFnName_inj {T T' : Name} {i i' : Nat}
    (h : projFnName T i = projFnName T' i') : T = T' ∧ i = i' := by
  simp only [projFnName, Name.num.injEq, Name.str.injEq] at h
  exact ⟨h.1.1, h.2⟩

/-- The projection-table name shape is injective (task #175 S1). -/
theorem projTableName_inj {T T' : Name} (h : projTableName T = projTableName T') :
    T = T' := by
  simp only [projTableName, Name.num.injEq, Name.str.injEq] at h
  exact h.1.1

/-- Unfold a successful projection-table lookup to the stored table:
the structure's table is stored, the index is in range, and the entry
is the table's view at it (task #175 S1). -/
theorem Env.findProj?_some {env : Env} {T : Name} {i : Nat}
    {entry : ProjEntry} (h : env.findProj? T i = some entry) :
    ∃ tbl : ProjTable, env.find? (projTableName T) = some (.projInfo tbl) ∧
      i < tbl.numFields ∧ entry = tbl.entry i := by
  unfold Env.findProj? at h
  split at h
  next tbl heq =>
    split at h
    · next hi => exact ⟨tbl, heq, hi, (Option.some.inj h).symm⟩
    · exact nomatch h
  next => exact nomatch h

/-- The lookup at a stored table, in range. -/
theorem Env.findProj?_of_table {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.find? (projTableName T) = some (.projInfo tbl)) {i : Nat}
    (hi : i < tbl.numFields) : env.findProj? T i = some (tbl.entry i) := by
  unfold Env.findProj?
  rw [h]
  exact if_pos hi

/-- No table stored, no entry. -/
theorem Env.findProj?_none_of_fresh {env : Env} {T : Name}
    (h : env.find? (projTableName T) = none) (i : Nat) : env.findProj? T i = none := by
  unfold Env.findProj?
  rw [h]

/-- **The stored table's projection offset** of structure `T` (task
#210 Part A; `0` when no table is stored): what every entry of the
table carries (`Env.findProj?_off`). -/
def Env.projOff (env : Env) (T : Name) : Nat :=
  match env.find? (projTableName T) with
  | some (.projInfo tbl) => tbl.off
  | _ => 0

theorem Env.findProj?_off {env : Env} {T : Name} {i : Nat} {e : ProjEntry}
    (hi : env.findProj? T i = some e) : e.off = env.projOff T := by
  obtain ⟨tbl, hf, -, rfl⟩ := Env.findProj?_some hi
  unfold Env.projOff
  rw [hf]
  rfl

/-- Two entries of one structure's table carry the same projection
offset (task #210 Part A): both are views of the one stored table. -/
theorem Env.findProj?_off_eq {env : Env} {T : Name} {i j : Nat} {e e' : ProjEntry}
    (hi : env.findProj? T i = some e) (hj : env.findProj? T j = some e') : e.off = e'.off := by
  obtain ⟨tbl, hf, -, rfl⟩ := Env.findProj?_some hi
  obtain ⟨tbl', hf', -, rfl⟩ := Env.findProj?_some hj
  obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hf.symm.trans hf'))
  rfl

/-- A stored table's view fixes the entry's data. -/
@[simp] theorem ProjTable.entry_structName (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).structName = tbl.structName := rfl
@[simp] theorem ProjTable.entry_idx (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).idx = i := rfl
@[simp] theorem ProjTable.entry_levelParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).levelParams = tbl.levelParams := rfl
@[simp] theorem ProjTable.entry_numParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).numParams = tbl.numParams := rfl
@[simp] theorem ProjTable.entry_ctor (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).ctor = tbl.ctor := rfl
@[simp] theorem ProjTable.entry_numFields (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).numFields = tbl.numFields := rfl
@[simp] theorem ProjTable.entry_body (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).body = tbl.bodies.getD i default := rfl
@[simp] theorem ProjTable.entry_fieldSort (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).fieldSort = tbl.guards.getD i .zero := rfl
@[simp] theorem ProjTable.entry_structSort (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).structSort = tbl.structSort := rfl
@[simp] theorem ProjTable.entry_off (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).off = tbl.off := rfl
/-- **The capability arities**: an inductive stored with the unit-like
or the η capability has the `∀`-telescope its capability record's
parameter count names.  A property of the stored declaration alone —
established ONCE at the block's install (the native route pins the
former's telescope before storing it, `checkSumInd`'s
`stripPis (nP + nIdx)`; on the modeled route the capability theorems
pin the model former's telescope and the stored type is the model's
under the block renaming, `indCapsWF_of_pins`; the basis blocks' types
are literal) and consumed by the structure-η and unit-like rows
(`CapsRows`) from the invariant, where `structEtaCertWith` and
`structUnitCert` used to re-check it per call ("invariants over
runtime gates"). -/
@[expose] def IndCapsWF (c : ConstantInfo) : Prop :=
  ∀ cv caps, c = .indInfo cv caps →
    (caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true) ∧
    (caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true)

/-- `IndCapsWF` at an inductive, from the two arity facts. -/
theorem IndCapsWF.of_caps {cv : ConstantVal} {caps : IndCaps}
    (hu : caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true)
    (he : caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true) :
    IndCapsWF (.indInfo cv caps) := by
  intro cv' caps' heq
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj heq
  exact ⟨hu, he⟩

/-- A `stripPis` at a larger count strips at a smaller one. -/
theorem stripPis_isSome_of_le :
    ∀ {k n : Nat} {e : Expr}, k ≤ n → (e.stripPis n).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro n e _ _; simp [Expr.stripPis]
  | succ k ih =>
    intro n e hle h
    match n, hle with
    | n + 1, hle =>
      match e, h with
      | .forallE d bo m, h =>
        simp only [Expr.stripPis, Option.isSome_map] at h ⊢
        exact ih (by omega) h

/-- Syntactic well-formedness of one stored constant w.r.t. `env`. -/
@[expose] def ConstWF (env : Env) (c : ConstantInfo) : Prop :=
  c.toConstantVal.type.hasFvar = false ∧
  c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
  c.toConstantVal.type.constsResolve env = true ∧
  c.toConstantVal.type.looseBVarsBounded 0 = true ∧
  (∀ cv value hint, c = .defnInfo cv value hint →
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true ∧
    value.looseBVarsBounded 0 = true) ∧
  (∀ cv mI rP rules, c = .recInfo cv mI rP rules →
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      -- a certified nested rule's stored instantiations are
      -- syntactically well-formed in the recursor's rule-prefix
      -- context, and the recursor type's major-premise domain applies
      -- the constructor family to exactly their liftings past the
      -- index binders followed by the index variables in order
      -- (validated once at install, `nestedRuleShape`)
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        rP ≤ mI ∧
        (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined cv.levelParams = true ∧
          pin.constsResolve env = true ∧
          pin.looseBVarsBounded rP = true) ∧
        ∃ pre dom body bm D,
          cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
              (List.range (mI - rP)).map
                (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
  -- (a theorem's stored value carries NO clause: a theorem is opaque
  -- to reduction and stored by its statement — the value is the
  -- record's own, unread by the kernel and by the invariant)
  -- a projection table's bodies (task #175 S1): closed with respect to
  -- free variables, level parameters within the structure's list,
  -- resolving, and scoped at the parameters and the subject; there
  -- are exactly `numFields` of them
  (∀ tbl, c = .projInfo tbl →
    tbl.bodies.size = tbl.numFields ∧
    ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
      b.hasFvar = false ∧
      b.allLevelParamsDefined tbl.levelParams = true ∧
      b.constsResolve env = true ∧
      b.looseBVarsBounded (tbl.numParams + 1) = true) ∧
  -- the capability arities (environment-independent)
  IndCapsWF c

/-- Every stored constant is syntactically well-formed. -/
@[expose] def EnvWF (env : Env) : Prop := ∀ c ∈ env.consts, ConstWF env c

/-- The capability arities of a stored inductive, off `EnvWF`. -/
theorem EnvWF.indCaps {env : Env} (henv : EnvWF env) {T : Name}
    {cv : ConstantVal} {caps : IndCaps}
    (h : env.find? T = some (.indInfo cv caps)) :
    (caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true) ∧
    (caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true) :=
  (henv _ (List.mem_of_find?_eq_some h)).2.2.2.2.2.2.2 cv caps rfl

/-- `find?` on a cons. -/
theorem Env.find?_cons {c : ConstantInfo} {env : Env} {n : Name} :
    Env.find? ⟨c :: env.consts⟩ n = if c.name = n then some c else env.find? n := by
  simp only [Env.find?, List.find?]
  split
  · next h => simp_all
  · next h => simp_all

/-- A cons finds its own head. -/
theorem Env.find?_cons_self (c : ConstantInfo) (env : Env) :
    Env.find? ⟨c :: env.consts⟩ c.name = some c := by
  rw [Env.find?_cons, if_pos rfl]

/-- A cons of a *fresh* head does not find anything new. -/
theorem Env.find?_cons_of_fresh {c : ConstantInfo} {env : Env}
    {n : Name} {ci : ConstantInfo} (hfresh : env.find? c.name = none)
    (h : env.find? n = some ci) :
    Env.find? ⟨c :: env.consts⟩ n = some ci := by
  rw [Env.find?_cons]
  split
  · next heq => rw [heq, h] at hfresh; exact nomatch hfresh
  · exact h

/-- Extending the environment with a fresh constant does not change
successful lookups. -/
theorem Env.find?_cons_of_isSome {c : ConstantInfo} {env : Env} {n : Name}
    (hfresh : env.find? c.name = none) (h : (env.find? n).isSome = true) :
    Env.find? ⟨c :: env.consts⟩ n = env.find? n := by
  rw [Env.find?_cons]
  split
  · next heq => rw [← heq] at h; rw [hfresh] at h; simp at h
  · rfl

/-- A cons at another name does not change a table lookup. -/
theorem Env.findProj?_cons_ne {env : Env} {c₀ : ConstantInfo} {T : Name}
    (hn : c₀.name ≠ projTableName T) (i : Nat) :
    Env.findProj? ⟨c₀ :: env.consts⟩ T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [Env.find?_cons, if_neg hn]

/-- Resolution depends on the environment only through which names it
finds: every name found in `env` being found in `env'` carries
resolution over. -/
theorem Expr.constsResolve_of_find {env env' : Env}
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ {e : Expr}, e.constsResolve env = true → e.constsResolve env' = true := by
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

/-- Resolution is monotone under environment extension. -/
theorem Expr.constsResolve_mono {c : ConstantInfo} {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨c :: env.consts⟩ = true :=
  Expr.constsResolve_of_find fun n h => by
    rw [Env.find?_cons]
    split <;> simp_all

/-- Resolution survives binder opening. -/
theorem Expr.constsResolve_instantiate1 {env : Env} {d : Nat} {ty : Expr}
    (hty : ty.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 (.fvar d ty) k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · simpa [Expr.constsResolve] using hty
    · split <;> simp [Expr.constsResolve]

/-- Level instantiation does not change which constants occur. -/
theorem Expr.constsResolve_instantiateLevelParams {env : Env} (ks : List Name)
    (us : List Level) :
    ∀ {e : Expr}, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- No name equals its own string extension. -/
theorem Name.str_ne (n : Name) (s : String) : n.str s ≠ n := by
  intro h
  have h1 : sizeOf (Name.str n s) = sizeOf n := congrArg sizeOf h
  simp at h1
  omega

/-- No name equals its own two-step string extension. -/
theorem Name.str_str_ne (n : Name) (s₁ s₂ : String) :
    (n.str s₁).str s₂ ≠ n := by
  intro h
  have h1 : sizeOf ((Name.str (Name.str n s₁) s₂)) = sizeOf n :=
    congrArg sizeOf h
  simp at h1
  omega

/-- Resolution only reads whether names are stored. -/
theorem Expr.constsResolve_congr {env₁ env₂ : Env}
    (henv : ∀ n, (env₁.find? n).isSome = (env₂.find? n).isSome) :
    ∀ (e : Expr), e.constsResolve env₁ = e.constsResolve env₂ := by
  intro e
  induction e with
  | lit l => cases l <;> simp_all [Expr.constsResolve]
  | _ => simp_all [Expr.constsResolve]

/-- Telescope domains of a resolving type resolve. -/
theorem Expr.constsResolve_stripPis {env : Env} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) → e.constsResolve env = true →
      (∀ b ∈ bs, (b.1).constsResolve env = true) ∧
      body.constsResolve env = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h hres
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun b hb => absurd hb (List.not_mem_nil), hres⟩
  | succ k ih =>
    intro e bs body h hres
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs', body'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.constsResolve, Bool.and_eq_true] at hres
        obtain ⟨hd, hrest⟩ := ih hs hres.2
        refine ⟨?_, hrest⟩
        intro bnd hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hres.1
        · exact hd bnd hb

/-- `stripPis` commutes with constant renaming. -/
theorem Expr.stripPis_renameConsts {f : Name → Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) →
      (e.renameConsts f).stripPis k =
        some (bs.map (fun b => ((b.1).renameConsts f, b.2)),
          body.renameConsts f) := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expr.stripPis]
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs', body'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show ((Expr.forallE ty b m).renameConsts f).stripPis (k + 1) = _
        rw [show (Expr.forallE ty b m).renameConsts f =
          .forallE (ty.renameConsts f) (b.renameConsts f) m from rfl]
        simp only [Expr.stripPis, ih hs, Option.map_some, List.map_cons]

/-- A `∀`-telescope pin of a renamed expression is one of the
expression itself (renaming touches no binder structure). -/
theorem Expr.stripPis_isSome_of_renameConsts {f : Name → Name} :
    ∀ (k : Nat) {e : Expr},
      ((e.renameConsts f).stripPis k).isSome = true →
      (e.stripPis k).isSome = true
  | 0, _, _ => rfl
  | k + 1, e, h => by
    cases e with
    | forallE ty b m =>
      rw [show (Expr.forallE ty b m).renameConsts f =
        .forallE (ty.renameConsts f) (b.renameConsts f) m from rfl] at h
      simp only [Expr.stripPis, Option.isSome_map] at h ⊢
      exact Expr.stripPis_isSome_of_renameConsts k h
    | _ => simp [Expr.renameConsts, Expr.stripPis] at h

/-- Renaming maps that agree on every stored name rename a resolving
expression identically. -/
theorem Expr.renameConsts_congr_resolve {env : Env} {f g : Name → Name}
    (hfg : ∀ n, (env.find? n).isSome = true → f n = g n) :
    ∀ (e : Expr), e.constsResolve env = true →
      e.renameConsts f = e.renameConsts g := by
  intro e
  induction e <;> intro h <;>
    simp_all [Expr.constsResolve, Expr.renameConsts]
  all_goals first
  | (rename_i n _; exact hfg n h)
  | (rename_i s _ _ h'; exact hfg s h'.1)
  | (rename_i s _ _; exact hfg s h.1)

/-- Extending with a fresh, well-formed constant preserves `EnvWF`. -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env}
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts⟩ c) : EnvWF ⟨c :: env.consts⟩ := by
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hmem
  · exact hc
  · obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := henv c' hmem
    refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value hint heq =>
      let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_,
      fun tbl heq =>
        let ⟨g0, g⟩ := h8 tbl heq
        ⟨g0, fun i b hb =>
          let ⟨g1, g2, g3, g4⟩ := g i b hb
          ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩⟩, h9⟩
    intro cv mI rP rules heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
    refine ⟨g1, g2, Expr.constsResolve_mono g3, g4, ?_⟩
    intro lvls pins hfr
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
    exact ⟨n1, n2, fun pin hpin =>
      let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      ⟨p1, p2, Expr.constsResolve_mono p3, p4⟩, n4⟩

/-- Resolution is monotone under lookup-preserving extension. -/
theorem Expr.constsResolve_le {envA envB : Env}
    (hf : ∀ n, (envA.find? n).isSome = true →
      (envB.find? n).isSome = true) :
    ∀ {e : Expr}, e.constsResolve envA = true →
      e.constsResolve envB = true := by
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

end ConLeche
