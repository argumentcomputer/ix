import Ix.IxVM.RecordSections
import Ix.Compile.BinderData
import Ix.IxVM.Consistency.StatementRel
import Ix.IxVM.Consistency.ReadsKeys
import Ix.IxVM.Consistency.TableValid
import Ix.Cert.CompileCorrectProof
import IxCK.Kernel.Ixon.Reader
import IxCK.Kernel.Ixon.RoleTableInj
import IxCK.Kernel.Verify.Rename.Basic
import IxCK.Kernel.Verify.Rename.ExprOps
import IxCK.Kernel.Verify.Rename.Pins

/-!
# Binder-data section preservation bridge (`RecordSections` ↔ `ReadsIn` / `readRecord` / `compileCorrect`)

`Ix.Cert.ReaderStreamsTrace.compileCorrect` certifies the pure compiler (`Ix.Cert.compileReport`),
whose records carry bare/pre-section binder data, whereas `Ix.Compile.BinderData` (`stripSection`,
`sectionOf`, `rewriteRecord`, `renameTable`, `readdress`) and `IxVM.RecordSections` (`sectionsOf`,
`withSection`) attach canonical `PropWhen` binder-data sections (`Ixon.Constant.binders`) and
re-address records bottom-up.

This module closes the semantic bridge between pre-section and post-section records:

1. **Single-record binder-section erasure invariance** (`memberReader_withBinders`,
   `exprReader_withBinders`, `inLogic_withBinders`, `readRecord_withBinders`,
   `readRecordBare_withBinders`):
   Replacing `c.binders` on any non-projection record (or preserving `binders = #[]` on projection
   records) leaves `Ix.Kernel.Reader.MemberReader.read`, `IxVM.Consistency.exprReader`,
   `IxVM.Consistency.InLogic`, `Ix.Kernel.Reader.readRecord`, and
   `Ix.Kernel.Reader.readRecordBare` completely invariant. In particular,
   `IxVM.RecordSections.withSection` preserves `readRecord`, `readRecordBare`, `InLogic`,
   `exprReader`, and `ReadsIn` (`withSection_readRecord`, `withSection_readsIn`).

2. **Role-table and store-level re-addressing preservation (`attachSections_readsIn`)**:
   Under any injective address renaming `rename : Address → Address` and a store transformation
   `SectionedStore` attaching arbitrary binder sections to non-projection records via
   `Ix.Compile.BinderData.rewriteRecord` while re-addressing projections and `renameTable rename t`:
   * `renameTable_check`: well-formedness (`RoleTable.check = .ok ()`) is preserved;
   * `keyOf_renameTable`: `keyOf (renameTable rename t) (rename a) = (keyOf t a).map rename`;
   * `exprReader_rewriteRecord_ok`: expression decoding commutes with `Expr.mapKeys rename`;
   * `attachSections_readsIn`: `ReadsIn t store₁ blob₁ a ci` implies
     `ReadsIn (renameTable rename t) store₂ blob₂ (rename a) (ci.mapKeys rename)`;
   * `attachSections_readsIn_sameAddr`: when `rename = id`, `ReadsIn` is preserved as an exact
     biconditional (`↔`).

3. **Composition with `compileCorrect` and `CircuitComposed`**:
   * `readsIn_mono` and `sectioned_readsIn_agree_of_compat`: any `ReadsIn` witness over a
     circuit-loaded store compatible with the sectioned view agrees up to `SameReading` with
     `ci.mapKeys rename` for every bare reading `Reads t ixe a ci`;
   * `compileCorrect_sectioned_circuitComposed_bridge`: composes
     `Ix.Cert.ReaderStreamsTrace.compileCorrect` with `IxVM.Consistency.CircuitComposed` over a
     `SectionedStore` view, linking every bare compiled constant's reading to the circuit-verified
     sectioned reading up to `rename` and `SameReading`, while preserving non-provability of
     `False` (`mapKeys_type_eq_false_iff`).
-/

namespace Ix.Cert.RecordSectionsBridge

open Ix.Kernel (Mode Key LevelParam Role RoleTable)
open Ix.Kernel.Reader (Ctx ECx MemberReader ReadM Store State Read convUniv convExpr
  readRecord readRecordBare)
open IxVM.Consistency (InLogic ReadsIn Reads ReadsRecord DefnReads AxiomReads QuotReads IndReads
  CtorReads RecReads RuleReads MemberAt IndKeyAt SameReading keyOf keyOf_cases keyOf_inj
  readCtx exprReader soloSelf blockSelf constructorProjection memberAddr
  ctorAddr familyKey majorKey binderDom lastBinderDom headKey inertKey quotSlot
  readCtx_keyAt roles_nodup_of_admitBinding recordOf storeOver blobOver LoadedBy
  CircuitComposed ComposedWith ConsistentReadOver TableShape AllBound InScopeTyping ClaimSeeds
  committedFootprint SelfHashed GenuineCollision hashed_mono circuitSound_mono)
open IxVM.Refinement (View Digest packDigest Hashed CircuitSound)
open Ix.Compile.BinderData (rewriteRecord renameTable stripSection)
open Aiur.Generic.SourceSemantics (Call)

/-! ## 1. Helper predicates on record kinds -/

/-- Whether an `Ixon.ConstantInfo` is a projection record (`iPrj`, `cPrj`, `rPrj`, `dPrj`). -/
def isProjectionInfo : Ixon.ConstantInfo → Bool
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ => true
  | _ => false

/-- Replacing `c.binders` leaves `InLogic` unchanged. -/
theorem inLogic_withBinders (c : Ixon.Constant) (bs : Array Ixon.BinderBlock) :
    InLogic { c with binders := bs } ↔ InLogic c := Iff.rfl

/-- `rewriteRecord` preserves `InLogic` for every record. -/
theorem inLogic_rewriteRecord (rename : Address → Address) (c : Ixon.Constant)
    (bs : Array Ixon.BinderBlock) :
    InLogic (rewriteRecord rename c bs) ↔ InLogic c := by
  unfold InLogic rewriteRecord
  cases c.info <;> simp

/-- `rewriteRecord` on a `memberProjection` with empty binder section yields the renamed
`memberProjection`. -/
@[simp] theorem rewriteRecord_memberProjection (rename : Address → Address) (B : Address)
    (i : Nat) (m : Ixon.MutConst) :
    rewriteRecord rename (IxVM.Consistency.memberProjection B i m) #[] =
      IxVM.Consistency.memberProjection (rename B) i m := by
  cases m <;> simp [rewriteRecord, IxVM.Consistency.memberProjection]

/-- `rewriteRecord` on a `constructorProjection` with empty binder section yields the renamed
`constructorProjection`. -/
@[simp] theorem rewriteRecord_constructorProjection (rename : Address → Address) (B : Address)
    (i j : Nat) :
    rewriteRecord rename (constructorProjection B i j) #[] =
      constructorProjection (rename B) i j := by
  simp [rewriteRecord, constructorProjection]

/-! ## 2. Single-record binder-section erasure invariance -/

private theorem convExpr_congr {md : Mode} {e₁ e₂ : ECx md}
    (huniv : e₁.univs = e₂.univs)
    (hkey : ∀ i, e₁.keyAt i = e₂.keyAt i)
    (hblob : ∀ i, e₁.blobAt i = e₂.blobAt i)
    (hself : ∀ i, e₁.self i = e₂.self i)
    (tbl : Array (ReadM (Ix.Kernel.Expr md))) (x : Ixon.Expr) :
    convExpr e₁ tbl x = convExpr e₂ tbl x := by
  have hlevel : ∀ i, e₁.level i = e₂.level i := fun i => by
    unfold ECx.level; rw [huniv]
  have hlevels : ∀ us, e₁.levels us = e₂.levels us := fun us => by
    unfold ECx.levels
    congr 1; funext i; exact hlevel i
  have hnat : ∀ i, e₁.natAt i = e₂.natAt i := fun i => by
    unfold ECx.natAt; rw [hblob i]
  induction x with
  | var _ => rfl
  | sort i => simp only [convExpr, hlevel i]
  | ref i us => simp only [convExpr, hkey i, hlevels us]
  | recur i us => simp only [convExpr, hself i.toNat, hlevels us]
  | prj i f v ih => simp only [convExpr, hkey i, ih]
  | str i => simp only [convExpr, hblob i]
  | nat i => simp only [convExpr, hnat i]
  | app f a ihf iha => simp only [convExpr, ihf, iha]
  | lam t b iht ihb => simp only [convExpr, iht, ihb]
  | all t b iht ihb => simp only [convExpr, iht, ihb]
  | letE nd _ t v b iht ihv ihb => simp only [convExpr, iht, ihv, ihb]
  | share _ => rfl

private theorem foldl_sharing_congr {md : Mode} {e₁ e₂ : ECx md}
    (huniv : e₁.univs = e₂.univs)
    (hkey : ∀ i, e₁.keyAt i = e₂.keyAt i)
    (hblob : ∀ i, e₁.blobAt i = e₂.blobAt i)
    (hself : ∀ i, e₁.self i = e₂.self i) :
    ∀ (entries : List Ixon.Expr) (tbl : Array (ReadM (Ix.Kernel.Expr md))),
      entries.foldl (fun acc entry => acc.push (convExpr e₁ acc entry)) tbl =
      entries.foldl (fun acc entry => acc.push (convExpr e₂ acc entry)) tbl
  | [], _ => rfl
  | entry :: rest, tbl => by
    simp only [List.foldl_cons]
    rw [convExpr_congr huniv hkey hblob hself tbl entry]
    exact foldl_sharing_congr huniv hkey hblob hself rest _

private theorem mk'_tbl_eq_foldl {md : Mode} (cx : Ctx md) (src : Ixon.Constant)
    (param : Nat → LevelParam) (self : Nat → Option (ReadM (Key md))) :
    (MemberReader.mk' cx src param self).tbl =
      src.sharing.toList.foldl
        (fun acc entry => acc.push (convExpr ⟨cx, src, src.univs.map (convUniv param), self⟩ acc entry))
        #[] := by
  unfold MemberReader.mk'
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
  rfl

/-- **`MemberReader.read` is invariant under replacing `src.binders`.** -/
theorem memberReader_withBinders {md : Mode} (cx : Ctx md) (src : Ixon.Constant)
    (bs : Array Ixon.BinderBlock) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (Key md))) (x : Ixon.Expr) :
    (MemberReader.mk' cx { src with binders := bs } param self).read x =
      (MemberReader.mk' cx src param self).read x := by
  let e₁ : ECx md := ⟨cx, { src with binders := bs }, src.univs.map (convUniv param), self⟩
  let e₂ : ECx md := ⟨cx, src, src.univs.map (convUniv param), self⟩
  have hkey : ∀ i, e₁.keyAt i = e₂.keyAt i := fun _ => rfl
  have hblob : ∀ i, e₁.blobAt i = e₂.blobAt i := fun _ => rfl
  have htbl : (MemberReader.mk' cx { src with binders := bs } param self).tbl =
      (MemberReader.mk' cx src param self).tbl := by
    rw [mk'_tbl_eq_foldl, mk'_tbl_eq_foldl]
    exact foldl_sharing_congr (e₁ := e₁) (e₂ := e₂) rfl hkey hblob (fun _ => rfl)
      src.sharing.toList #[]
  unfold MemberReader.read
  change convExpr e₁ (MemberReader.mk' cx { src with binders := bs } param self).tbl x =
    convExpr e₂ (MemberReader.mk' cx src param self).tbl x
  rw [htbl]
  exact convExpr_congr (e₁ := e₁) (e₂ := e₂) rfl hkey hblob (fun _ => rfl) _ x

/-- **`exprReader` is invariant under replacing `src.binders`.** -/
theorem exprReader_withBinders (t : RoleTable) (blob : Address → Option ByteArray)
    (src : Ixon.Constant) (bs : Array Ixon.BinderBlock) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (Key .anon))) (x : Ixon.Expr) :
    (exprReader t blob { src with binders := bs } param self).read x =
      (exprReader t blob src param self).read x :=
  memberReader_withBinders (readCtx t blob) src bs param self x

private theorem recurDeps_withBinders (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (d : Ixon.Definition) :
    Ix.Kernel.Reader.recurDeps { c with binders := bs } d = Ix.Kernel.Reader.recurDeps c d := rfl

private theorem readDefinition_congr {md : Mode} (cx : Ctx md) (st : State md)
    (heights : Key md → Nat) (ref : Ix.Kernel.ConstRef Address) (lps : List LevelParam)
    {m₁ m₂ : MemberReader md} (hm : ∀ x, m₁.read x = m₂.read x) (d : Ixon.Definition) :
    Ix.Kernel.Reader.readDefinition cx st heights ref lps m₁ d =
      Ix.Kernel.Reader.readDefinition cx st heights ref lps m₂ d := by
  unfold Ix.Kernel.Reader.readDefinition
  simp only [hm]

private theorem readInductive_withBinders {md : Mode} (cx : Ctx md) (st : State md)
    (owner : Address) (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (ms : Array Ixon.MutConst) :
    Ix.Kernel.Reader.readInductive cx st owner { c with binders := bs } ms =
      Ix.Kernel.Reader.readInductive cx st owner c ms := by
  unfold Ix.Kernel.Reader.readInductive
  simp only [memberReader_withBinders]

private theorem readInductiveBare_withBinders {md : Mode} (cx : Ctx md)
    (owner : Address) (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (ms : Array Ixon.MutConst) :
    Ix.Kernel.Reader.readInductiveBare cx owner { c with binders := bs } ms =
      Ix.Kernel.Reader.readInductiveBare cx owner c ms := by
  unfold Ix.Kernel.Reader.readInductiveBare
  simp only [memberReader_withBinders]

/-- **`Ix.Kernel.Reader.readRecord` is invariant under attaching or replacing binder data**
on every non-projection record (and on projection records when `bs = c.binders`). -/
theorem readRecord_withBinders {md : Mode} (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (hprj : isProjectionInfo c.info = true → bs = c.binders) :
    readRecord cx st owner { c with binders := bs } = readRecord cx st owner c := by
  cases c with
  | mk info sharing refs univs binders =>
    have hm : ∀ param self x,
        (MemberReader.mk' cx ⟨info, sharing, refs, univs, bs⟩ param self).read x =
          (MemberReader.mk' cx ⟨info, sharing, refs, univs, binders⟩ param self).read x :=
      fun param self x => memberReader_withBinders cx ⟨info, sharing, refs, univs, binders⟩ bs param self x
    unfold readRecord
    cases info with
    | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
      have hbs : bs = binders := hprj rfl
      subst hbs
      rfl
    | defn d =>
      simp only [readDefinition_congr cx st _ _ _ (hm id _)]
    | recr _ => rfl
    | axio a =>
      simp only [hm]
    | quot q =>
      simp only [hm]
    | muts ms =>
      have hri := readInductive_withBinders cx st owner ⟨.muts ms, sharing, refs, univs, binders⟩ bs ms
      have hrd : Ix.Kernel.Reader.recurDeps ⟨.muts ms, sharing, refs, univs, bs⟩ =
          Ix.Kernel.Reader.recurDeps ⟨.muts ms, sharing, refs, univs, binders⟩ := rfl
      simp only [hri, hrd, readDefinition_congr cx st _ _ _ (hm id _)]

/-- **`Ix.Kernel.Reader.readRecordBare` is invariant under attaching or replacing binder data**
on every non-projection record (and on projection records when `bs = c.binders`). -/
theorem readRecordBare_withBinders {md : Mode} (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (hprj : isProjectionInfo c.info = true → bs = c.binders) :
    readRecordBare cx st owner { c with binders := bs } = readRecordBare cx st owner c := by
  have hrr := readRecord_withBinders cx st owner c bs hprj
  cases c with
  | mk info sharing refs univs binders =>
    unfold readRecordBare
    cases info with
    | muts ms =>
      have hbi := readInductiveBare_withBinders cx owner ⟨.muts ms, sharing, refs, univs, binders⟩ bs ms
      dsimp only
      split
      · simp only [hbi]
      · exact hrr
    | _ => exact hrr

/-! ## 3. Properties of `Ix.Compile.BinderData.stripSection` and `IxVM.RecordSections.withSection` -/

/-- Stripping a canonical projection record (empty sharing and binder tables) returns the empty
binder section. -/
theorem stripSection_projection_empty (c : Ixon.Constant)
    (hprj : isProjectionInfo c.info = true) (hshare : c.sharing = #[]) (hempty : c.binders = #[]) :
    stripSection c = .ok #[] := by
  cases c with
  | mk info sharing refs univs binders =>
    simp only at hprj hshare hempty
    subst hshare; subst hempty
    unfold stripSection Ix.Compile.BinderData.hasBinderModes Ix.CompileM.undecidedSection
    cases info <;> simp [isProjectionInfo] at hprj
    all_goals
      simp [Ixon.ConstantInfo.binderRoots, Ixon.binderfulEntries, Id.run, pure, Except.pure]
      rfl

/-- `IxVM.RecordSections.withSection` modifies ONLY the `binders` field of `c`, leaving
`info`, `sharing`, `refs`, and `univs` untouched. -/
theorem withSection_eq_withBinders (env : Ixon.Env) (c c' : Ixon.Constant) (taint : Bool)
    (h : IxVM.RecordSections.withSection env c taint = .ok c') :
    ∃ bs : Array Ixon.BinderBlock, c' = { c with binders := bs } := by
  unfold IxVM.RecordSections.withSection at h
  cases hs : stripSection c with
  | error e => simp [hs, bind, Except.bind] at h
  | ok stripped =>
    simp only [hs, bind, Except.bind] at h
    cases hc : IxVM.RecordSections.chosenOf env with
    | error e => simp [hc] at h
    | ok chosen =>
      simp only [hc] at h
      split at h
      · cases h
      · rename_i sections _
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨sections.getD _ #[], h.symm⟩

/-- `IxVM.RecordSections.withSection` preserves `Ix.Kernel.Reader.readRecord` on every
non-projection record. -/
theorem withSection_readRecord {md : Mode} (env : Ixon.Env) (cx : Ctx md) (st : State md)
    (owner : Address) (c c' : Ixon.Constant) (taint : Bool)
    (hnonprj : isProjectionInfo c.info = false)
    (h : IxVM.RecordSections.withSection env c taint = .ok c') :
    readRecord cx st owner c' = readRecord cx st owner c := by
  obtain ⟨bs, rfl⟩ := withSection_eq_withBinders env c c' taint h
  exact readRecord_withBinders cx st owner c bs (fun hp => by rw [hnonprj] at hp; cases hp)

/-- `IxVM.RecordSections.withSection` preserves `Ix.Kernel.Reader.readRecordBare` on every
non-projection record. -/
theorem withSection_readRecordBare {md : Mode} (env : Ixon.Env) (cx : Ctx md) (st : State md)
    (owner : Address) (c c' : Ixon.Constant) (taint : Bool)
    (hnonprj : isProjectionInfo c.info = false)
    (h : IxVM.RecordSections.withSection env c taint = .ok c') :
    readRecordBare cx st owner c' = readRecordBare cx st owner c := by
  obtain ⟨bs, rfl⟩ := withSection_eq_withBinders env c c' taint h
  exact readRecordBare_withBinders cx st owner c bs (fun hp => by rw [hnonprj] at hp; cases hp)

/-! ## 4. Role-table well-formedness and key preservation under `renameTable` -/

private theorem foldl_firstRepeatStep_map (rename : Address → Address)
    (hinj : Function.Injective rename) :
    ∀ (l pre : List Address) (s s' : Std.HashSet Address),
      (∀ x, s.contains x = true ↔ x ∈ pre) →
      (∀ y, s'.contains y = true ↔ y ∈ pre.map rename) →
      ((l.map rename).foldl RoleTable.firstRepeatStep (none, s')).1 =
        (l.foldl RoleTable.firstRepeatStep (none, s)).1.map rename
  | [], _, _, _, _, _ => rfl
  | x :: rest, pre, s, s', hs, hs' => by
    simp only [List.map_cons, List.foldl_cons]
    have hmem : (rename x ∈ pre.map rename) ↔ (x ∈ pre) := by
      constructor
      · intro h
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp h
        exact hinj heq ▸ hy
      · intro h
        exact List.mem_map.mpr ⟨x, h, rfl⟩
    by_cases hx : s.contains x = true
    · have hx' : s'.contains (rename x) = true := (hs' (rename x)).mpr (hmem.mpr ((hs x).mp hx))
      simp only [RoleTable.firstRepeatStep, hx, hx', ↓reduceIte,
        RoleTable.foldl_firstRepeatStep_some, Option.map_some]
    · have hx' : s'.contains (rename x) = false := by
        cases hc : s'.contains (rename x) with
        | false => rfl
        | true => exact absurd ((hs x).mpr (hmem.mp ((hs' (rename x)).mp hc))) hx
      simp only [RoleTable.firstRepeatStep, hx, hx', Bool.false_eq_true, ↓reduceIte]
      have hs1 : ∀ z, (s.insert x).contains z = true ↔ z ∈ x :: pre := by
        intro z
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs z, beq_iff_eq, List.mem_cons]
        exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
          fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩
      have hs1' : ∀ y, (s'.insert (rename x)).contains y = true ↔ y ∈ (x :: pre).map rename := by
        intro y
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs' y, beq_iff_eq, List.map_cons,
          List.mem_cons]
        exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
          fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩
      exact foldl_firstRepeatStep_map rename hinj rest (x :: pre) (s.insert x)
        (s'.insert (rename x)) hs1 hs1'

/-- `RoleTable.firstRepeat` commutes with mapping an injective address renaming. -/
theorem firstRepeat_map (rename : Address → Address) (hinj : Function.Injective rename)
    (as : List Address) :
    Ix.Kernel.RoleTable.firstRepeat (as.map rename) =
      (Ix.Kernel.RoleTable.firstRepeat as).map rename := by
  rw [RoleTable.firstRepeat_eq, RoleTable.firstRepeat_eq]
  exact foldl_firstRepeatStep_map rename hinj as [] {} {} (by simp) (by simp)

private theorem forIn_map_eq {α β σ : Type} {f : α → β}
    (body₁ : β → σ → Except String (ForInStep σ))
    (body₂ : α → σ → Except String (ForInStep σ))
    (h : ∀ x s, body₁ (f x) s = body₂ x s) :
    ∀ (l : List α) (s : σ), forIn (l.map f) s body₁ = forIn l s body₂
  | [], _ => rfl
  | x :: xs, s => by
    simp only [List.map_cons, List.forIn_cons, h x s, bind, Except.bind]
    cases body₂ x s with
    | error e => rfl
    | ok step =>
      cases step with
      | done b => rfl
      | yield b => exact forIn_map_eq body₁ body₂ h xs b

/-- **Renaming a well-formed role table by an injective map preserves `RoleTable.check = .ok ()`.** -/
theorem renameTable_check {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address} (hinj : Function.Injective rename) :
    (renameTable rename t).check = .ok () := by
  have h1 : (renameTable rename t).version = t.version := rfl
  have h2 : (renameTable rename t).bound.toList.map (·.1) = t.bound.toList.map (·.1) := by
    simp [renameTable]
  have h3 : (renameTable rename t).bound.toList.map (·.2) =
      (t.bound.toList.map (·.2)).map rename := by
    simp [renameTable, List.map_map, Function.comp_def]
  have h4 : (renameTable rename t).evidence.toList.map (·.1) = t.evidence.toList.map (·.1) := by
    simp [renameTable]
  have hall : ∀ (f : Ix.Kernel.Evidence Address → Ix.Kernel.Evidence Address)
      (es : Array (Ix.Kernel.Evidence Address)) (kinds : List (Option Bool)),
      (∀ e k, (f e).allowedBy k = e.allowedBy k) →
      ((es.map f).toList.zip kinds).all (fun x => x.1.allowedBy x.2) =
      (es.toList.zip kinds).all (fun x => x.1.allowedBy x.2) := by
    intro f es kinds hfa
    simp only [Array.toList_map]
    generalize es.toList = xs
    induction xs generalizing kinds with
    | nil => rfl
    | cons e rest ih =>
      cases kinds with
      | nil => rfl
      | cons k ks =>
        simp only [List.map_cons, List.zip_cons_cons, List.all_cons, hfa, ih ks]
  unfold RoleTable.check at hc ⊢
  rw [h1, h2, h3, firstRepeat_map rename hinj, h4]
  by_cases hv : (t.version == Ix.Kernel.specVersion) = true
  · by_cases hnd1 : (t.bound.toList.map (·.1)).Nodup
    · cases hfr : RoleTable.firstRepeat (t.bound.toList.map (·.2)) with
      | some a =>
        simp [hv, hnd1, hfr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hc
      | none =>
        simp only [hv, hnd1, hfr, Option.map_none, ↓reduceIte] at hc ⊢
        simp only [renameTable, ← Array.forIn_toList, Array.toList_map] at hc ⊢
        rw [forIn_map_eq _ _ (fun _ _ => rfl)]
        have hbind : ∀ {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β},
            (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := fun {ε α β x f b} => by
          cases x <;> simp [bind, Except.bind]
        obtain ⟨u1, hL1, hc2⟩ := hbind.mp hc
        rw [hbind]
        refine ⟨u1, hL1, ?_⟩
        by_cases hnd2 : (t.evidence.toList.map (·.1)).Nodup
        · simp only [hnd2, ↓reduceIte] at hc2 ⊢
          obtain ⟨u2, hL2, hc3⟩ := hbind.mp hc2
          rw [hbind]
          refine ⟨u2, ?_, hc3⟩
          rw [← hL2]
          refine forIn_map_eq _ _ (fun ⟨r, es⟩ s => ?_) t.evidence.toList PUnit.unit
          simp only [Array.size_map]
          rw [hall]
          intro e k; cases e <;> rfl
        · simp [hnd2, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hc2
    · simp [hv, hnd1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hc
  · simp [hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hc

private theorem find?_map_rename {rename : Address → Address} (hinj : Function.Injective rename)
    (bs : List (Role × Address)) (a : Address) :
    (bs.map fun (r, x) => (r, rename x)).find? (·.2 == rename a) =
      (bs.find? (·.2 == a)).map (fun (r, x) => (r, rename x)) := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.find?_cons]
    have hbeq : (rename p.2 == rename a) = (p.2 == a) := by
      cases h : (p.2 == a) with
      | true =>
        have heq : p.2 = a := beq_iff_eq.mp h
        simp [heq]
      | false =>
        cases h' : (rename p.2 == rename a) with
        | false => rfl
        | true =>
          have heq : p.2 = a := hinj (beq_iff_eq.mp h')
          simp [heq] at h
    rw [hbeq]
    cases (p.2 == a) with
    | true => rfl
    | false => exact ih

/-- **`keyOf` commutes with `renameTable`** for every injective address renaming. -/
theorem keyOf_renameTable (t : RoleTable) {rename : Address → Address}
    (hinj : Function.Injective rename) (a : Address) :
    keyOf (renameTable rename t) (rename a) = (keyOf t a).map rename := by
  unfold keyOf renameTable
  simp only [← Array.find?_toList, Array.toList_map]
  rw [find?_map_rename hinj t.bound.toList a]
  cases t.bound.toList.find? (·.2 == a) with
  | none => rfl
  | some p => rfl

/-- `inertKey` is invariant under key renaming. -/
@[simp] theorem inertKey_map (rename : Address → Address) (k : Key .anon) :
    inertKey (k.map rename) = inertKey k := by
  cases k <;> rfl

/-! ## 5. Expression-reader commutation under `rewriteRecord` and monotonicity -/

/-- Pointwise success relation between two expression-reading outcomes under `rename`. -/
private def ReadResRel (rename : Address → Address) (r₁ r₂ : ReadM (Ix.Kernel.Expr .anon)) : Prop :=
  ∀ e, r₁ = .ok e → r₂ = .ok (e.mapKeys rename)

/-- Pointwise success relation between two converted sharing tables under `rename`. -/
private def TblRel (rename : Address → Address) (tbl₁ tbl₂ : Array (ReadM (Ix.Kernel.Expr .anon))) : Prop :=
  tbl₁.size = tbl₂.size ∧
    ∀ (i : Nat) (h₁ : i < tbl₁.size) (h₂ : i < tbl₂.size),
      ReadResRel rename tbl₁[i] tbl₂[i]

private theorem tblRel_getElem? {rename : Address → Address}
    {tbl₁ tbl₂ : Array (ReadM (Ix.Kernel.Expr .anon))} (h : TblRel rename tbl₁ tbl₂) (i : Nat)
    {r₁ : ReadM (Ix.Kernel.Expr .anon)} (hget : tbl₁[i]? = some r₁) :
    ∃ r₂, tbl₂[i]? = some r₂ ∧ ReadResRel rename r₁ r₂ := by
  have hi₁ : i < tbl₁.size := (Array.getElem?_eq_some_iff.mp hget).1
  have hr₁ : tbl₁[i] = r₁ := (Array.getElem?_eq_some_iff.mp hget).2
  have hi₂ : i < tbl₂.size := h.1 ▸ hi₁
  refine ⟨tbl₂[i], Array.getElem?_eq_getElem hi₂, ?_⟩
  rw [← hr₁]
  exact h.2 i hi₁ hi₂

private theorem tblRel_push {rename : Address → Address}
    {tbl₁ tbl₂ : Array (ReadM (Ix.Kernel.Expr .anon))} (h : TblRel rename tbl₁ tbl₂)
    {r₁ r₂ : ReadM (Ix.Kernel.Expr .anon)} (hr : ReadResRel rename r₁ r₂) :
    TblRel rename (tbl₁.push r₁) (tbl₂.push r₂) := by
  have hsz : tbl₁.size = tbl₂.size := h.1
  refine ⟨by simp [hsz], fun i h₁ h₂ => ?_⟩
  simp only [Array.size_push] at h₁ h₂
  by_cases hlt : i < tbl₁.size
  · have hlt₂ : i < tbl₂.size := hsz ▸ hlt
    rw [Array.getElem_push_lt hlt, Array.getElem_push_lt hlt₂]
    exact h.2 i hlt hlt₂
  · have hi₁ : i = tbl₁.size := by omega
    have hi₂ : i = tbl₂.size := by omega
    subst hi₁
    rw [Array.getElem_push_eq]
    have heq : (tbl₂.push r₂)[tbl₁.size] = (tbl₂.push r₂)[tbl₂.size] := by simp [hsz]
    rw [heq, Array.getElem_push_eq]
    exact hr

private theorem convExpr_mapKeys_ok {rename : Address → Address}
    {e₁ e₂ : ECx .anon}
    (huniv : e₂.univs = e₁.univs)
    (hkey : ∀ i k, e₁.keyAt i = .ok k → e₂.keyAt i = .ok (k.map rename))
    (hblob : ∀ i b, e₁.blobAt i = .ok b → e₂.blobAt i = .ok b)
    (hself : ∀ i r₁ k, e₁.self i = some r₁ → r₁ = .ok k →
      ∃ r₂, e₂.self i = some r₂ ∧ r₂ = .ok (k.map rename))
    {tbl₁ tbl₂ : Array (ReadM (Ix.Kernel.Expr .anon))} (htbl : TblRel rename tbl₁ tbl₂)
    (x : Ixon.Expr) :
    ReadResRel rename (convExpr e₁ tbl₁ x) (convExpr e₂ tbl₂ x) := by
  have hlevel : ∀ i, e₂.level i = e₁.level i := fun i => by
    unfold ECx.level; rw [huniv]
  have hlevels : ∀ us, e₂.levels us = e₁.levels us := fun us => by
    unfold ECx.levels; congr 1; funext i; exact hlevel i
  have hnat : ∀ i n, e₁.natAt i = .ok n → e₂.natAt i = .ok n := fun i n hn => by
    unfold ECx.natAt at hn ⊢
    cases hb : e₁.blobAt i with
    | error _ => simp [hb, bind, Except.bind] at hn
    | ok bs =>
      rw [hb] at hn
      rw [hblob i bs hb]
      exact hn
  induction x with
  | var i =>
    intro e he
    simp only [convExpr, pure, Except.pure, Except.ok.injEq, Ix.Kernel.Expr.mkBvar_eq] at he ⊢
    rw [← he]; rfl
  | sort i =>
    intro e he
    simp only [convExpr, hlevel i] at he ⊢
    cases hl : e₁.level i with
    | error _ => simp [hl, bind, Except.bind] at he
    | ok l =>
      simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
      rw [← he]; rfl
  | ref i us =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hk : e₁.keyAt i with
    | error _ => simp [hk, bind, Except.bind] at he
    | ok k =>
      rw [hk] at he
      rw [hkey i k hk, hlevels us]
      cases hl : e₁.levels us with
      | error _ => simp [hl, bind, Except.bind] at he
      | ok ls =>
        simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | recur i us =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hs : e₁.self i.toNat with
    | none => simp [hs, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at he
    | some r₁ =>
      rw [hs] at he
      cases hr₁ : r₁ with
      | error _ => simp [hr₁, bind, Except.bind] at he
      | ok k =>
        obtain ⟨r₂, hs₂, hr₂⟩ := hself i.toNat r₁ k hs hr₁
        rw [hs₂, hr₂, hlevels us]
        rw [hr₁] at he
        cases hl : e₁.levels us with
        | error _ => simp [hl, bind, Except.bind] at he
        | ok ls =>
          simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
          rw [← he]; rfl
  | prj i f v ih =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hk : e₁.keyAt i with
    | error _ => simp [hk, bind, Except.bind] at he
    | ok k =>
      rw [hk] at he
      rw [hkey i k hk]
      cases hv : convExpr e₁ tbl₁ v with
      | error _ => simp [hv, bind, Except.bind] at he
      | ok ev =>
        rw [hv] at he
        rw [ih ev hv]
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | str i =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hb : e₁.blobAt i with
    | error _ => simp [hb, bind, Except.bind] at he
    | ok bs =>
      rw [hb] at he
      rw [hblob i bs hb]
      cases hs : String.fromUTF8? bs with
      | none => simp [hs, bind, Except.bind, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at he
      | some s =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | nat i =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hn : e₁.natAt i with
    | error _ => simp [hn, bind, Except.bind] at he
    | ok n =>
      rw [hn] at he
      rw [hnat i n hn]
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
      rw [← he]; rfl
  | app f a ihf iha =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hf : convExpr e₁ tbl₁ f with
    | error _ => simp [hf, bind, Except.bind] at he
    | ok ef =>
      rw [hf] at he
      cases ha : convExpr e₁ tbl₁ a with
      | error _ => simp [ha, bind, Except.bind] at he
      | ok ea =>
        rw [ha] at he
        rw [ihf ef hf, iha ea ha]
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | lam t b iht ihb =>
    intro e he
    simp only [convExpr] at he ⊢
    cases ht : convExpr e₁ tbl₁ t with
    | error _ => simp [ht, bind, Except.bind] at he
    | ok et =>
      rw [ht] at he
      cases hb : convExpr e₁ tbl₁ b with
      | error _ => simp [hb, bind, Except.bind] at he
      | ok eb =>
        rw [hb] at he
        rw [iht et ht, ihb eb hb]
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | all t b iht ihb =>
    intro e he
    simp only [convExpr] at he ⊢
    cases ht : convExpr e₁ tbl₁ t with
    | error _ => simp [ht, bind, Except.bind] at he
    | ok et =>
      rw [ht] at he
      cases hb : convExpr e₁ tbl₁ b with
      | error _ => simp [hb, bind, Except.bind] at he
      | ok eb =>
        rw [hb] at he
        rw [iht et ht, ihb eb hb]
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
        rw [← he]; rfl
  | letE nd _ t v b iht ihv ihb =>
    intro e he
    simp only [convExpr] at he ⊢
    cases ht : convExpr e₁ tbl₁ t with
    | error _ => simp [ht, bind, Except.bind] at he
    | ok et =>
      rw [ht] at he
      cases hv : convExpr e₁ tbl₁ v with
      | error _ => simp [hv, bind, Except.bind] at he
      | ok ev =>
        rw [hv] at he
        cases hb : convExpr e₁ tbl₁ b with
        | error _ => simp [hb, bind, Except.bind] at he
        | ok eb =>
          rw [hb] at he
          rw [iht et ht, ihv ev hv, ihb eb hb]
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ⊢
          rw [← he]; rfl
  | share i =>
    intro e he
    simp only [convExpr] at he ⊢
    cases hg : tbl₁[i.toNat]? with
    | none => simp [hg, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at he
    | some r₁ =>
      rw [hg] at he
      obtain ⟨r₂, hg₂, hr⟩ := tblRel_getElem? htbl i.toNat hg
      rw [hg₂]
      exact hr e he

private theorem foldl_sharing_mapKeys_ok {rename : Address → Address}
    {e₁ e₂ : ECx .anon}
    (huniv : e₂.univs = e₁.univs)
    (hkey : ∀ i k, e₁.keyAt i = .ok k → e₂.keyAt i = .ok (k.map rename))
    (hblob : ∀ i b, e₁.blobAt i = .ok b → e₂.blobAt i = .ok b)
    (hself : ∀ i r₁ k, e₁.self i = some r₁ → r₁ = .ok k →
      ∃ r₂, e₂.self i = some r₂ ∧ r₂ = .ok (k.map rename)) :
    ∀ (entries : List Ixon.Expr) (tbl₁ tbl₂ : Array (ReadM (Ix.Kernel.Expr .anon))),
      TblRel rename tbl₁ tbl₂ →
      TblRel rename
        (entries.foldl (fun acc entry => acc.push (convExpr e₁ acc entry)) tbl₁)
        (entries.foldl (fun acc entry => acc.push (convExpr e₂ acc entry)) tbl₂)
  | [], _, _, htbl => htbl
  | entry :: rest, _, _, htbl =>
    foldl_sharing_mapKeys_ok huniv hkey hblob hself rest _ _
      (tblRel_push htbl (convExpr_mapKeys_ok huniv hkey hblob hself htbl entry))

private theorem key_map_id (k : Key .anon) : k.map id = k := Ix.Kernel.Key.map_id k
private theorem expr_mapKeys_id (e : Ix.Kernel.Expr .anon) : e.mapKeys id = e := Ix.Kernel.Expr.mapKeys_id e
private theorem constInfo_mapKeys_id (ci : Ix.Kernel.ConstantInfo .anon) : ci.mapKeys id = ci :=
  Ix.Kernel.ConstantInfo.mapKeys_id ci

/-- **`exprReader` commutes with `rewriteRecord` and `renameTable` on successful reads.** -/
theorem exprReader_rewriteRecord_ok {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address} (hinj : Function.Injective rename)
    {blob₁ blob₂ : Address → Option ByteArray}
    (hblob : ∀ a b, blob₁ a = some b → blob₂ (rename a) = some b)
    (c : Ixon.Constant) (bs : Array Ixon.BinderBlock)
    (param : Nat → LevelParam)
    (self₁ self₂ : Nat → Option (ReadM (Key .anon)))
    (hself : ∀ i r₁ k, self₁ i = some r₁ → r₁ = .ok k →
      ∃ r₂, self₂ i = some r₂ ∧ r₂ = .ok (k.map rename))
    {x : Ixon.Expr} {e : Ix.Kernel.Expr .anon}
    (hread : (exprReader t blob₁ c param self₁).read x = .ok e) :
    (exprReader (renameTable rename t) blob₂ (rewriteRecord rename c bs) param self₂).read x =
      .ok (e.mapKeys rename) := by
  have hc' : (renameTable rename t).check = .ok () := renameTable_check hc hinj
  let c' := rewriteRecord rename c bs
  let e₁ : ECx .anon := ⟨readCtx t blob₁, c, c.univs.map (convUniv param), self₁⟩
  let e₂ : ECx .anon := ⟨readCtx (renameTable rename t) blob₂, c', c'.univs.map (convUniv param), self₂⟩
  have hkey : ∀ i k, e₁.keyAt i = .ok k → e₂.keyAt i = .ok (k.map rename) := fun i k hk => by
    unfold ECx.keyAt at hk ⊢
    dsimp only [e₁, e₂, c', rewriteRecord] at hk ⊢
    rw [Array.getElem?_map]
    cases hr : c.refs[i.toNat]? with
    | none =>
      rw [hr] at hk
      simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hk
    | some a =>
      simp only [hr, readCtx_keyAt hc] at hk
      obtain rfl : keyOf t a = k := Except.ok.inj hk
      simp only [Option.map_some, readCtx_keyAt hc', keyOf_renameTable t hinj]
  have hblobAt : ∀ i b, e₁.blobAt i = .ok b → e₂.blobAt i = .ok b := fun i b hb => by
    unfold ECx.blobAt at hb ⊢
    dsimp only [e₁, e₂, c', rewriteRecord, readCtx] at hb ⊢
    rw [Array.getElem?_map]
    cases hr : c.refs[i.toNat]? with
    | none =>
      rw [hr] at hb
      simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hb
    | some a =>
      simp only [hr] at hb
      cases hba : blob₁ a with
      | none =>
        rw [hba] at hb
        simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hb
      | some bs =>
        rw [hba] at hb
        obtain rfl : bs = b := Except.ok.inj hb
        simp only [Option.map_some, hblob a bs hba, pure, Except.pure]
  have htbl0 : TblRel rename (#[] : Array (ReadM (Ix.Kernel.Expr .anon))) #[] :=
    ⟨rfl, fun _ h₁ _ => by simp at h₁⟩
  have htbl : TblRel rename
      (exprReader t blob₁ c param self₁).tbl
      (exprReader (renameTable rename t) blob₂ c' param self₂).tbl := by
    unfold exprReader
    rw [mk'_tbl_eq_foldl, mk'_tbl_eq_foldl]
    exact foldl_sharing_mapKeys_ok (e₁ := e₁) (e₂ := e₂) rfl hkey hblobAt hself c.sharing.toList #[] #[] htbl0
  exact convExpr_mapKeys_ok (e₁ := e₁) (e₂ := e₂) rfl hkey hblobAt hself htbl x e hread

/-- `exprReader` is monotone in the blob map (without requiring `t.check`). -/
theorem exprReader_blob_mono {t : RoleTable} {blob₁ blob₂ : Address → Option ByteArray}
    (hblob : ∀ a b, blob₁ a = some b → blob₂ a = some b)
    (c : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (Key .anon)))
    {x : Ixon.Expr} {e : Ix.Kernel.Expr .anon}
    (hread : (exprReader t blob₁ c param self).read x = .ok e) :
    (exprReader t blob₂ c param self).read x = .ok e := by
  let e₁ : ECx .anon := ⟨readCtx t blob₁, c, c.univs.map (convUniv param), self⟩
  let e₂ : ECx .anon := ⟨readCtx t blob₂, c, c.univs.map (convUniv param), self⟩
  have hkey : ∀ i k, e₁.keyAt i = .ok k → e₂.keyAt i = .ok (k.map id) := fun i k hk => by
    have heq : e₂.keyAt i = e₁.keyAt i := rfl
    rw [heq, hk, key_map_id]
  have hblobAt : ∀ i b, e₁.blobAt i = .ok b → e₂.blobAt i = .ok b := fun i b hb => by
    unfold ECx.blobAt at hb ⊢
    dsimp only [e₁, e₂, readCtx] at hb ⊢
    cases hr : c.refs[i.toNat]? with
    | none => rw [hr] at hb; simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hb
    | some a =>
      simp only [hr] at hb
      cases hba : blob₁ a with
      | none => rw [hba] at hb; simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hb
      | some bs =>
        rw [hba] at hb
        obtain rfl : bs = b := Except.ok.inj hb
        simp only [hblob a bs hba, pure, Except.pure]
  have hself : ∀ i r₁ k, e₁.self i = some r₁ → r₁ = .ok k →
      ∃ r₂, e₂.self i = some r₂ ∧ r₂ = .ok (k.map id) := fun i r₁ k hs hr =>
    ⟨r₁, hs, by rw [key_map_id]; exact hr⟩
  have htbl0 : TblRel id (#[] : Array (ReadM (Ix.Kernel.Expr .anon))) #[] :=
    ⟨rfl, fun _ h₁ _ => by simp at h₁⟩
  have htbl : TblRel id (exprReader t blob₁ c param self).tbl (exprReader t blob₂ c param self).tbl := by
    unfold exprReader
    rw [mk'_tbl_eq_foldl, mk'_tbl_eq_foldl]
    exact foldl_sharing_mapKeys_ok (e₁ := e₁) (e₂ := e₂) rfl hkey hblobAt hself c.sharing.toList #[] #[] htbl0
  have hres := convExpr_mapKeys_ok (e₁ := e₁) (e₂ := e₂) rfl hkey hblobAt hself htbl x e hread
  rwa [expr_mapKeys_id] at hres

/-! ## 6. Store-level section attachment and `attachSections_readsIn` -/

/-- **A store `store₂` obtained by attaching binder-data sections to `store₁` and re-addressing
records by `rename`** (the exact mathematical relation between pre-section `compileReport` records
and post-section `Ix.Compile.BinderData.readdress` / `IxVM.RecordSections` records):
* `rename` is injective on addresses;
* every non-projection record `c` stored at `a` in `store₁` is stored at `rename a` in `store₂`
  as `rewriteRecord rename c bs` for some binder-data section `bs`;
* every projection record `memberProjection B i m` (resp. `constructorProjection B i j`) stored
  at `memberAddr B i m` (resp. `ctorAddr B i j`) in `store₁` is re-addressed to
  `memberAddr (rename B) i m = rename (memberAddr B i m)` (resp.
  `ctorAddr (rename B) i j = rename (ctorAddr B i j)`) with empty tables (`#[]` binders);
* every blob at `x` in `blob₁` is preserved at `rename x` in `blob₂` (in practice `rename` fixes
  blob addresses and `blob₂ = blob₁`). -/
structure SectionedStore (rename : Address → Address) (store₁ store₂ : Store)
    (blob₁ blob₂ : Address → Option ByteArray) : Prop where
  inj : Function.Injective rename
  nonPrj : ∀ a c, store₁ a = some c → isProjectionInfo c.info = false →
    ∃ bs, store₂ (rename a) = some (rewriteRecord rename c bs)
  memberPrj : ∀ B i m,
    store₁ (memberAddr B i m) = some (IxVM.Consistency.memberProjection B i m) →
    rename (memberAddr B i m) = memberAddr (rename B) i m ∧
    store₂ (memberAddr (rename B) i m) = some (IxVM.Consistency.memberProjection (rename B) i m)
  ctorPrj : ∀ B i j,
    store₁ (ctorAddr B i j) = some (constructorProjection B i j) →
    rename (ctorAddr B i j) = ctorAddr (rename B) i j ∧
    store₂ (ctorAddr (rename B) i j) = some (constructorProjection (rename B) i j)
  ctorAddrEq : ∀ B cb ms i ind j,
    store₁ B = some cb → cb.info = .muts ms → ms[i]? = some (.indc ind) → j < ind.ctors.size →
    rename (ctorAddr B i j) = ctorAddr (rename B) i j
  memberAddrEq : ∀ B cb ms i m,
    store₁ B = some cb → cb.info = .muts ms → ms[i]? = some m →
    rename (memberAddr B i m) = memberAddr (rename B) i m
  blobs : ∀ a b, blob₁ a = some b → blob₂ (rename a) = some b

private theorem lastBinderDom_mapKeys (rename : Address → Address) (e : Ix.Kernel.Expr .anon) :
    lastBinderDom (e.mapKeys rename) = (lastBinderDom e).map (Ix.Kernel.Expr.mapKeys rename) := by
  induction e with
  | forallE d b _ _ ihb =>
    cases b with
    | forallE d' b' _ =>
      simp only [Ix.Kernel.Expr.mapKeys, lastBinderDom] at ihb ⊢
      exact ihb
    | _ => rfl
  | _ => rfl

private theorem headKey_mapKeys (rename : Address → Address) (e : Ix.Kernel.Expr .anon) :
    headKey (e.mapKeys rename) = (headKey e).map (Key.map rename) := by
  unfold headKey
  rw [← Ix.Kernel.Expr.mapKeys_getAppFn]
  cases e.getAppFn <;> rfl

private theorem binderDom_mapKeys (rename : Address → Address) (n : Nat) (ty : Ix.Kernel.Expr .anon) :
    binderDom n (ty.mapKeys rename) = (binderDom n ty).map (Ix.Kernel.Expr.mapKeys rename) := by
  unfold binderDom
  rw [Ix.Kernel.Expr.stripPis_mapKeys]
  cases ty.stripPis n with
  | none => rfl
  | some q =>
    rcases q with ⟨bs, body⟩
    cases body <;> rfl

private theorem familyKey_mapKeys (rename : Address → Address) (rc : Ixon.Recursor)
    (ty : Ix.Kernel.Expr .anon) :
    familyKey rc (ty.mapKeys rename) = (familyKey rc ty).map (Key.map rename) := by
  unfold familyKey
  rw [binderDom_mapKeys]
  cases binderDom rc.params.toNat ty with
  | none => rfl
  | some m =>
    simp only [Option.map_some, Option.bind_some, lastBinderDom_mapKeys]
    cases lastBinderDom m with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, headKey_mapKeys]

private theorem majorKey_mapKeys (rename : Address → Address) (rc : Ixon.Recursor)
    (ty : Ix.Kernel.Expr .anon) :
    majorKey rc (ty.mapKeys rename) = (majorKey rc ty).map (Key.map rename) := by
  unfold majorKey
  rw [binderDom_mapKeys]
  cases binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty with
  | none => rfl
  | some d => simp only [Option.map_some, Option.bind_some, headKey_mapKeys]

private theorem quotDeclsA_mapKeys_fixed (rename : Address → Address) {slot : Nat}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (h : (Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon))[slot]? = some ci) :
    ci.mapKeys rename = ci := by
  have hd := @Ix.Kernel.declsA_mapKeys .anon .anon rename .quotK
  have hget : ((Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon)).map
      (Ix.Kernel.ConstantInfo.mapKeys rename))[slot]? =
      (Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon))[slot]? := by
    exact congrArg (fun l => l[slot]?) hd
  rw [List.getElem?_map, h, Option.map_some] at hget
  exact Option.some.inj hget

private theorem soloSelf_rel (t : RoleTable) {rename : Address → Address}
    (hinj : Function.Injective rename) (a : Address) :
    ∀ i r₁ k, soloSelf t a i = some r₁ → r₁ = .ok k →
      ∃ r₂, soloSelf (renameTable rename t) (rename a) i = some r₂ ∧ r₂ = .ok (k.map rename) := by
  intro i r₁ k hs hr
  unfold soloSelf at hs ⊢
  cases h : (i == 0) with
  | false => simp [h] at hs
  | true =>
    simp only [h, ↓reduceIte, Option.some.injEq] at hs ⊢
    subst hs
    obtain rfl : keyOf t a = k := Except.ok.inj hr
    exact ⟨pure (keyOf (renameTable rename t) (rename a)), rfl,
      by simp [pure, Except.pure, keyOf_renameTable t hinj]⟩

private theorem blockSelf_rel (t : RoleTable) {rename : Address → Address}
    {store₁ store₂ : Store} {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {B : Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hsB : store₁ B = some cb) (hiB : cb.info = .muts ms) :
    ∀ i r₁ k, blockSelf t B ms i = some r₁ → r₁ = .ok k →
      ∃ r₂, blockSelf (renameTable rename t) (rename B) ms i = some r₂ ∧
        r₂ = .ok (k.map rename) := by
  intro i r₁ k hs hr
  unfold blockSelf at hs ⊢
  cases hm : ms[i]? with
  | none => simp [hm] at hs
  | some m =>
    simp only [hm, Option.map_some, Option.some.injEq] at hs ⊢
    subst hs
    obtain rfl : keyOf t (memberAddr B i m) = k := Except.ok.inj hr
    refine ⟨pure (keyOf (renameTable rename t) (memberAddr (rename B) i m)), rfl, ?_⟩
    rw [← hsec.memberAddrEq B cb ms i m hsB hiB hm]
    simp [pure, Except.pure, keyOf_renameTable t hsec.inj]

private theorem memberAt_sectioned {rename : Address → Address}
    {store₁ store₂ : Store} {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {a : Address} {c : Ixon.Constant} {B : Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (hsa : store₁ a = some c) (hm : MemberAt store₁ a c B cb ms i m) :
    ∃ bs, store₂ (rename a) = some (IxVM.Consistency.memberProjection (rename B) i m) ∧
      rename a = memberAddr (rename B) i m ∧
      MemberAt store₂ (rename a) (IxVM.Consistency.memberProjection (rename B) i m) (rename B)
        (rewriteRecord rename cb bs) ms i m := by
  obtain ⟨hsB, hiB, hms, rfl, rfl, hlog⟩ := hm
  obtain ⟨bs, hcb₂⟩ := hsec.nonPrj B cb hsB (by simp [isProjectionInfo, hiB])
  obtain ⟨haddr, hprj₂⟩ := hsec.memberPrj B i m hsa
  refine ⟨bs, ?_, haddr, ?_⟩
  · rw [haddr]; exact hprj₂
  · refine ⟨hcb₂, ?_, hms, rfl, haddr, (inLogic_rewriteRecord rename cb bs).mpr hlog⟩
    simp [rewriteRecord, hiB]

private theorem indKeyAt_sectioned {t : RoleTable} {rename : Address → Address}
    {store₁ store₂ : Store} {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {k : Key .anon} {B : Address} {i : Nat} {ind : Ixon.Inductive}
    (h : IndKeyAt t store₁ k B i ind) :
    IndKeyAt (renameTable rename t) store₂ (k.map rename) (rename B) i ind := by
  obtain ⟨a, c, p, cb, ms, rfl, hsa, hinfo, rfl, rfl, hm⟩ := h
  obtain ⟨bs, hsa₂, haddr₂, hm₂⟩ := memberAt_sectioned hsec hsa hm
  refine ⟨rename a, IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.indc ind),
    { p with block := rename p.block }, rewriteRecord rename cb bs, ms,
    (keyOf_renameTable t hsec.inj a).symm, hsa₂, ?_, rfl, rfl, hm₂⟩
  simp [IxVM.Consistency.memberProjection, UInt64.ofNat_toNat]

private theorem ruleReads_sectioned {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address} {store₁ store₂ : Store}
    {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {src : Ixon.Constant} (bs : Array Ixon.BinderBlock)
    {ps : List LevelParam}
    {self₁ self₂ : Nat → Option (ReadM (Key .anon))}
    (hself : ∀ i r₁ k, self₁ i = some r₁ → r₁ = .ok k →
      ∃ r₂, self₂ i = some r₂ ∧ r₂ = .ok (k.map rename))
    {Bm : Address} {cbM : Ixon.Constant} {msM : Array Ixon.MutConst}
    {im : Nat} {indM : Ixon.Inductive}
    (hsBm : store₁ Bm = some cbM) (hiBm : cbM.info = .muts msM)
    (hmsBm : msM[im]? = some (.indc indM)) :
    ∀ {rzip : List (Ixon.RecursorRule × Nat)} {rules : List (Ix.Kernel.RecRule .anon)},
      (∀ ru ∈ rzip, ru.2 < indM.ctors.size) →
      List.Forall₂
        (RuleReads t (exprReader t blob₁ src (Ix.Kernel.Reader.recParam ps) self₁) Bm im)
        rzip rules →
      List.Forall₂
        (RuleReads (renameTable rename t)
          (exprReader (renameTable rename t) blob₂ (rewriteRecord rename src bs)
            (Ix.Kernel.Reader.recParam ps) self₂) (rename Bm) im)
        rzip (rules.map (Ix.Kernel.RecRule.mapKeys rename))
  | [], [], _, .nil => .nil
  | ru :: rus, rl :: rls, hidxBound, .cons h1 hrest => by
    refine List.Forall₂.cons ?_
      (ruleReads_sectioned hc hsec bs hself hsBm hiBm hmsBm
        (fun x hx => hidxBound x (List.mem_cons_of_mem _ hx)) hrest)
    obtain ⟨rhs, hrhs, rfl⟩ := h1
    have hrhs' := exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs src bs
      (Ix.Kernel.Reader.recParam ps) self₁ self₂ hself hrhs
    refine ⟨rhs.mapKeys rename, hrhs', ?_⟩
    have hlt : ru.2 < indM.ctors.size := hidxBound ru List.mem_cons_self
    have hctorEq := hsec.ctorAddrEq Bm cbM msM im indM ru.2 hsBm hiBm hmsBm hlt
    simp only [Ix.Kernel.RecRule.mapKeys, Ix.Kernel.RecRuleFire.mapKeys, ← hctorEq,
      keyOf_renameTable t hsec.inj]

private theorem recReads_sectioned {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address} {store₁ store₂ : Store}
    {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {src : Ixon.Constant} (bs : Array Ixon.BinderBlock)
    {self₁ self₂ : Nat → Option (ReadM (Key .anon))}
    (hself : ∀ i r₁ k, self₁ i = some r₁ → r₁ = .ok k →
      ∃ r₂, self₂ i = some r₂ ∧ r₂ = .ok (k.map rename))
    {name : Key .anon} {rc : Ixon.Recursor} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hr : RecReads t store₁ blob₁ src self₁ name rc ci₀) :
    RecReads (renameTable rename t) store₂ blob₂ (rewriteRecord rename src bs) self₂
      (name.map rename) rc (ci₀.mapKeys rename) := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules,
    hP, hF, hIF, hM, hIM, hps, hty, hsize, hrules, rfl⟩ := hr
  have hP' := exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs src bs id self₁ self₂ hself hP
  have hty' := exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs src bs
    (Ix.Kernel.Reader.recParam ps) self₁ self₂ hself hty
  have hIF' := indKeyAt_sectioned hsec hIF
  have hIM' := indKeyAt_sectioned hsec hIM
  obtain ⟨_, _, _, cbM, msM, _, _, _, _, _, hsBm, hiBm, hmsBm, -⟩ := hIM
  have hidxBound : ∀ ru ∈ rc.rules.toList.zipIdx, ru.2 < indM.ctors.size := by
    intro ru hru
    have hlen : ru.2 < rc.rules.toList.length := by
      have := List.mem_zipIdx hru
      omega
    simpa [hsize] using hlen
  have hrules' := ruleReads_sectioned hc hsec bs hself hsBm hiBm hmsBm hidxBound hrules
  exact ⟨tyP.mapKeys rename, ty.mapKeys rename, kF.map rename, kM.map rename, rename B, rename Bm,
    i, im, ind, indM, ps, rules.map (Ix.Kernel.RecRule.mapKeys rename),
    hP', by rw [familyKey_mapKeys, hF]; rfl, hIF',
    by rw [majorKey_mapKeys, hM]; rfl, hIM',
    hps, hty', hsize, hrules', rfl⟩

/-- **`attachSections_readsIn`**: attaching binder-data sections and bottom-up re-addressing via
`SectionedStore` preserves the semantic reading relation `ReadsIn` across every constant kind
(definitions, theorems, opaques, axioms, quotients, recursors, inductive types, constructors, and
projections), transforming every read constant by `ConstantInfo.mapKeys rename`. -/
theorem attachSections_readsIn {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address} {store₁ store₂ : Store}
    {blob₁ blob₂ : Address → Option ByteArray}
    (hsec : SectionedStore rename store₁ store₂ blob₁ blob₂)
    {a : Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : ReadsIn t store₁ blob₁ a ci) :
    ReadsIn (renameTable rename t) store₂ blob₂ (rename a) (ci.mapKeys rename) := by
  obtain ⟨c, hsa, hrec⟩ := h
  unfold ReadsRecord at hrec
  cases hinfo : c.info with
  | defn d =>
    rw [hinfo] at hrec
    obtain ⟨hlog, ty, val, hty, hval, hshape⟩ := hrec
    obtain ⟨bs, hsa₂⟩ := hsec.nonPrj a c hsa (by simp [isProjectionInfo, hinfo])
    refine ⟨rewriteRecord rename c bs, hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (rewriteRecord rename c bs).info = .defn d := by simp [rewriteRecord, hinfo]
    rw [hinfo₂]
    refine ⟨(inLogic_rewriteRecord rename c bs).mpr hlog, ty.mapKeys rename, val.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs c bs id _ _ (soloSelf_rel t hsec.inj a) hty,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs c bs id _ _ (soloSelf_rel t hsec.inj a) hval,
      ?_⟩
    rw [keyOf_renameTable t hsec.inj]
    cases hk : d.kind with
    | defn =>
      rw [hk] at hshape
      obtain ⟨hint, rfl⟩ := hshape
      exact ⟨hint, rfl⟩
    | thm =>
      rw [hk] at hshape
      subst hshape; rfl
    | opaq =>
      rw [hk] at hshape
      subst hshape; rfl
  | axio ax =>
    rw [hinfo] at hrec
    obtain ⟨hlog, hinert, ty, hty, rfl⟩ := hrec
    obtain ⟨bs, hsa₂⟩ := hsec.nonPrj a c hsa (by simp [isProjectionInfo, hinfo])
    refine ⟨rewriteRecord rename c bs, hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (rewriteRecord rename c bs).info = .axio ax := by simp [rewriteRecord, hinfo]
    rw [hinfo₂]
    refine ⟨(inLogic_rewriteRecord rename c bs).mpr hlog, ?_, ty.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs c bs id _ _ (fun _ _ _ hs => by cases hs) hty,
      ?_⟩
    · rw [keyOf_renameTable t hsec.inj, inertKey_map]; exact hinert
    · rw [keyOf_renameTable t hsec.inj]; rfl
  | quot q =>
    rw [hinfo] at hrec
    obtain ⟨ty, hty, hpin, hslot⟩ := hrec
    obtain ⟨bs, hsa₂⟩ := hsec.nonPrj a c hsa (by simp [isProjectionInfo, hinfo])
    refine ⟨rewriteRecord rename c bs, hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (rewriteRecord rename c bs).info = .quot q := by simp [rewriteRecord, hinfo]
    rw [hinfo₂]
    have hinjOn : @Ix.Kernel.InjOn .anon .anon rename (Ix.Kernel.KeyScope.ofId (fun _ => True)) := by
      intro _ _ _ _ e; exact hsec.inj e
    have hgoodKey : ∀ k : Key .anon, k.Good (Ix.Kernel.KeyScope.ofId (fun _ => True)) := fun k => by
      induction k with
      | id _ => trivial
      | role _ => trivial
      | aux _ _ ih => exact ih
    have hgoodExpr : ∀ e : Ix.Kernel.Expr .anon, e.Good (Ix.Kernel.KeyScope.ofId (fun _ => True)) := fun e => by
      induction e with
      | bvar _ | sort _ => trivial
      | fvar _ _ ih => exact ih
      | const k _ => exact hgoodKey k
      | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
      | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
      | lit l => cases l <;> simp
      | proj k _ _ ih => exact ⟨hgoodKey k, ih⟩
    have hpin' : Ix.Kernel.quotPinHit (quotSlot q.kind)
        ⟨(keyOf t a).map rename, List.range q.lvls.toNat, ty.mapKeys (md' := .anon) rename⟩ = true := by
      have hren := Ix.Kernel.quotPinHit_ren hinjOn (Ix.Kernel.KeyScope.ofId_pre _) (quotSlot q.kind)
        (cv := ⟨keyOf t a, List.range q.lvls.toNat, ty⟩) ⟨hgoodKey _, hgoodExpr _⟩
      simpa [Ix.Kernel.ConstantVal.mapKeys, hpin] using hren
    refine ⟨ty.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs c bs id _ _ (fun _ _ _ hs => by cases hs) hty,
      by rw [keyOf_renameTable t hsec.inj]; exact hpin',
      by rw [quotDeclsA_mapKeys_fixed rename hslot]; exact hslot⟩
  | recr rc =>
    rw [hinfo] at hrec
    obtain ⟨hlog, hrr⟩ := hrec
    obtain ⟨bs, hsa₂⟩ := hsec.nonPrj a c hsa (by simp [isProjectionInfo, hinfo])
    refine ⟨rewriteRecord rename c bs, hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (rewriteRecord rename c bs).info = .recr rc := by simp [rewriteRecord, hinfo]
    rw [hinfo₂]
    refine ⟨(inLogic_rewriteRecord rename c bs).mpr hlog, ?_⟩
    rw [keyOf_renameTable t hsec.inj]
    exact recReads_sectioned hc hsec bs (soloSelf_rel t hsec.inj a) hrr
  | dPrj p =>
    rw [hinfo] at hrec
    obtain ⟨cb, ms, d, hm, ty, val, hty, hval, hshape⟩ := hrec
    obtain ⟨bs, hsa₂, -, hm₂⟩ := memberAt_sectioned hsec hsa hm
    refine ⟨IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.defn d), hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.defn d)).info =
        .dPrj { p with block := rename p.block } := by
      simp [IxVM.Consistency.memberProjection, UInt64.ofNat_toNat]
    rw [hinfo₂]
    refine ⟨rewriteRecord rename cb bs, ms, d, hm₂, ty.mapKeys rename, val.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs cb bs id _ _
        (blockSelf_rel t hsec hm.1 hm.2.1) hty,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs cb bs id _ _
        (blockSelf_rel t hsec hm.1 hm.2.1) hval, ?_⟩
    rw [keyOf_renameTable t hsec.inj]
    cases hk : d.kind with
    | defn =>
      rw [hk] at hshape
      obtain ⟨hint, rfl⟩ := hshape
      exact ⟨hint, rfl⟩
    | thm =>
      rw [hk] at hshape
      subst hshape; rfl
    | opaq =>
      rw [hk] at hshape
      subst hshape; rfl
  | iPrj p =>
    rw [hinfo] at hrec
    obtain ⟨cb, ms, ind, hm, ty, caps, hty, rfl⟩ := hrec
    obtain ⟨bs, hsa₂, -, hm₂⟩ := memberAt_sectioned hsec hsa hm
    refine ⟨IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.indc ind), hsa₂, ?_⟩
    unfold ReadsRecord
    have hinfo₂ : (IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.indc ind)).info =
        .iPrj { p with block := rename p.block } := by
      simp [IxVM.Consistency.memberProjection, UInt64.ofNat_toNat]
    rw [hinfo₂]
    refine ⟨rewriteRecord rename cb bs, ms, ind, hm₂, ty.mapKeys rename, caps.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs cb bs id _ _
        (blockSelf_rel t hsec hm.1 hm.2.1) hty, ?_⟩
    rw [keyOf_renameTable t hsec.inj]; rfl
  | cPrj p =>
    rw [hinfo] at hrec
    obtain ⟨cb, ms, ind, ct, hsB, hiB, hms, hct, hcidx, rfl, rfl, hlog, ty, hty, rfl⟩ := hrec
    obtain ⟨bs, hcb₂⟩ := hsec.nonPrj p.block cb hsB (by simp [isProjectionInfo, hiB])
    obtain ⟨haddr, hsa₂⟩ := hsec.ctorPrj p.block p.idx.toNat p.cidx.toNat hsa
    refine ⟨constructorProjection (rename p.block) p.idx.toNat p.cidx.toNat,
      by rw [haddr]; exact hsa₂, ?_⟩
    dsimp only [ReadsRecord, constructorProjection]
    rw [show p.idx.toNat.toUInt64 = p.idx from UInt64.ofNat_toNat,
      show p.cidx.toNat.toUInt64 = p.cidx from UInt64.ofNat_toNat]
    refine ⟨rewriteRecord rename cb bs, ms, ind, ct, hcb₂, by simp only [rewriteRecord, hiB],
      hms, hct, hcidx, by simp only [UInt64.ofNat_toNat], haddr,
      (inLogic_rewriteRecord rename cb bs).mpr hlog,
      ty.mapKeys rename,
      exprReader_rewriteRecord_ok hc hsec.inj hsec.blobs cb bs id _ _
        (blockSelf_rel t hsec hsB hiB) hty, ?_⟩
    rw [keyOf_renameTable t hsec.inj]; rfl
  | rPrj p =>
    rw [hinfo] at hrec
    obtain ⟨cb, ms, rc, hm, hrr⟩ := hrec
    obtain ⟨bs, hsa₂, -, hm₂⟩ := memberAt_sectioned hsec hsa hm
    refine ⟨IxVM.Consistency.memberProjection (rename p.block) p.idx.toNat (.recr rc), hsa₂, ?_⟩
    dsimp only [ReadsRecord, IxVM.Consistency.memberProjection]
    rw [show p.idx.toNat.toUInt64 = p.idx from UInt64.ofNat_toNat]
    refine ⟨rewriteRecord rename cb bs, ms, rc,
      by simpa only [IxVM.Consistency.memberProjection, UInt64.ofNat_toNat] using hm₂, ?_⟩
    rw [keyOf_renameTable t hsec.inj]
    exact recReads_sectioned hc hsec bs (blockSelf_rel t hsec hm.1 hm.2.1) hrr
  | muts _ =>
    rw [hinfo] at hrec
    exact False.elim hrec

private theorem rewriteRecord_id_eq_withBinders (c : Ixon.Constant) (bs : Array Ixon.BinderBlock) :
    rewriteRecord id c bs = { c with binders := bs } := by
  unfold rewriteRecord
  cases c.info <;> simp

private theorem renameTable_id (t : RoleTable) : renameTable id t = t := by
  cases t with
  | mk ver bound ev =>
    unfold renameTable
    congr 1
    · simp
    · apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.getElem_map]
        cases h : ev[i] with
        | mk r es =>
          congr 1
          apply Array.ext
          · simp
          · intro j hj₁ hj₂
            simp only [Array.getElem_map]
            cases es[j] <;> rfl

/-- **In-place binder-section attachment/stripping (`rename = id`) preserves `ReadsIn` as an exact
biconditional**: replacing `c.binders` on non-projection records while leaving projection records
and blobs intact neither adds nor removes any semantic reading. -/
theorem attachSections_readsIn_sameAddr {t : RoleTable} (hc : t.check = .ok ())
    {store₁ store₂ : Store} {blob : Address → Option ByteArray}
    (hnonPrj₁ : ∀ a c, store₁ a = some c → isProjectionInfo c.info = false →
      ∃ bs, store₂ a = some { c with binders := bs })
    (hnonPrj₂ : ∀ a c, store₂ a = some c → isProjectionInfo c.info = false →
      ∃ bs, store₁ a = some { c with binders := bs })
    (hprj : ∀ a c, isProjectionInfo c.info = true → (store₁ a = some c ↔ store₂ a = some c))
    (a : Address) (ci : Ix.Kernel.ConstantInfo .anon) :
    ReadsIn t store₁ blob a ci ↔ ReadsIn t store₂ blob a ci := by
  have hfwd : SectionedStore id store₁ store₂ blob blob := {
    inj := fun _ _ h => h
    nonPrj := fun x c hx hnp => by
      obtain ⟨bs, hx₂⟩ := hnonPrj₁ x c hx hnp
      exact ⟨bs, by simpa [rewriteRecord_id_eq_withBinders] using hx₂⟩
    memberPrj := fun B i m hm =>
      ⟨rfl, (hprj _ _ (by cases m <;> rfl)).mp hm⟩
    ctorPrj := fun B i j hm =>
      ⟨rfl, (hprj _ _ rfl).mp hm⟩
    ctorAddrEq := fun _ _ _ _ _ _ _ _ _ _ => rfl
    memberAddrEq := fun _ _ _ _ _ _ _ _ => rfl
    blobs := fun _ _ h => h
  }
  have hbwd : SectionedStore id store₂ store₁ blob blob := {
    inj := fun _ _ h => h
    nonPrj := fun x c hx hnp => by
      obtain ⟨bs, hx₁⟩ := hnonPrj₂ x c hx hnp
      exact ⟨bs, by simpa [rewriteRecord_id_eq_withBinders] using hx₁⟩
    memberPrj := fun B i m hm =>
      ⟨rfl, (hprj _ _ (by cases m <;> rfl)).mpr hm⟩
    ctorPrj := fun B i j hm =>
      ⟨rfl, (hprj _ _ rfl).mpr hm⟩
    ctorAddrEq := fun _ _ _ _ _ _ _ _ _ _ => rfl
    memberAddrEq := fun _ _ _ _ _ _ _ _ => rfl
    blobs := fun _ _ h => h
  }
  constructor
  · intro h
    have h' := attachSections_readsIn hc hfwd h
    rw [renameTable_id, constInfo_mapKeys_id] at h'
    exact h'
  · intro h
    have h' := attachSections_readsIn hc hbwd h
    rw [renameTable_id, constInfo_mapKeys_id] at h'
    exact h'

/-- Updating a single non-projection record in a store using `IxVM.RecordSections.withSection`
preserves `ReadsIn` across the entire store (for every address `x` and constant `ci`). -/
theorem withSection_readsIn {t : RoleTable} (hc : t.check = .ok ())
    {store : Store} {blob : Address → Option ByteArray}
    {env : Ixon.Env} {a : Address} {c c' : Ixon.Constant} {taint : Bool}
    (hsa : store a = some c) (hnonprj : isProjectionInfo c.info = false)
    (hws : IxVM.RecordSections.withSection env c taint = .ok c')
    (x : Address) (ci : Ix.Kernel.ConstantInfo .anon) :
    ReadsIn t store blob x ci ↔
      ReadsIn t (fun y => if y == a then some c' else store y) blob x ci := by
  obtain ⟨bs, rfl⟩ := withSection_eq_withBinders env c c' taint hws
  refine attachSections_readsIn_sameAddr hc ?_ ?_ ?_ x ci
  · intro y cy hsy hnp
    by_cases hy : y = a
    · subst hy
      rw [hsa] at hsy
      obtain rfl := Option.some.inj hsy
      exact ⟨bs, by simp⟩
    · have hne : (y == a) = false := beq_false_of_ne hy
      exact ⟨cy.binders, by simp [hne, hsy]⟩
  · intro y cy hsy hnp
    by_cases hy : y = a
    · subst hy
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hsy
      subst hsy
      exact ⟨c.binders, hsa⟩
    · have hne : (y == a) = false := beq_false_of_ne hy
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hsy
      exact ⟨cy.binders, hsy⟩
  · intro y cy hprj
    by_cases hy : y = a
    · subst hy
      simp only [beq_self_eq_true, ↓reduceIte, hsa, Option.some.injEq]
      constructor
      · rintro rfl; rw [hnonprj] at hprj; cases hprj
      · rintro rfl; change isProjectionInfo c.info = true at hprj; rw [hnonprj] at hprj; cases hprj
    · have hne : (y == a) = false := beq_false_of_ne hy
      simp [hne]

/-! ## 7. Monotonicity, compatibility, and `compileCorrect` ↔ `CircuitComposed` sectioned bridge -/

/-- `ReadsIn` is monotone in both the record store and the blob map. -/
theorem readsIn_mono {t : RoleTable} {store₁ store₂ : Store}
    {blob₁ blob₂ : Address → Option ByteArray}
    (hs : ∀ x c, store₁ x = some c → store₂ x = some c)
    (hb : ∀ x b, blob₁ x = some b → blob₂ x = some b)
    {a : Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : ReadsIn t store₁ blob₁ a ci) :
    ReadsIn t store₂ blob₂ a ci := by
  obtain ⟨c, hsa, hrec⟩ := h
  refine ⟨c, hs a c hsa, ?_⟩
  unfold ReadsRecord at hrec ⊢
  have hmem : ∀ {x c B cb ms i m}, MemberAt store₁ x c B cb ms i m →
      MemberAt store₂ x c B cb ms i m := fun ⟨h1, h2⟩ => ⟨hs _ _ h1, h2⟩
  have hind : ∀ {k B i ind}, IndKeyAt t store₁ k B i ind → IndKeyAt t store₂ k B i ind :=
    fun ⟨x, cx, p, cb, ms, h1, h2, h3, h4, h5, h6⟩ =>
      ⟨x, cx, p, cb, ms, h1, hs _ _ h2, h3, h4, h5, hmem h6⟩
  have hrecR : ∀ {src self name rc ci₀},
      RecReads t store₁ blob₁ src self name rc ci₀ →
      RecReads t store₂ blob₂ src self name rc ci₀ := by
    intro src self name rc ci₀
      ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, hP, hF, hIF, hM, hIM, hps, hty, hsize, hrules, hci⟩
    refine ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules,
      exprReader_blob_mono hb _ _ _ hP, hF, hind hIF, hM, hind hIM, hps,
      exprReader_blob_mono hb _ _ _ hty, hsize, ?_, hci⟩
    exact hrules.imp fun _ _ ⟨rhs, hrhs, heq⟩ => ⟨rhs, exprReader_blob_mono hb _ _ _ hrhs, heq⟩
  cases hinfo : c.info with
  | defn d =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨hlog, ty, val, hty, hval, hsh⟩ := hrec
    exact ⟨hlog, ty, val, exprReader_blob_mono hb _ _ _ hty, exprReader_blob_mono hb _ _ _ hval, hsh⟩
  | axio ax =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨hlog, hin, ty, hty, heq⟩ := hrec
    exact ⟨hlog, hin, ty, exprReader_blob_mono hb _ _ _ hty, heq⟩
  | quot q =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨ty, hty, hp, hq⟩ := hrec
    exact ⟨ty, exprReader_blob_mono hb _ _ _ hty, hp, hq⟩
  | recr rc =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    exact ⟨hrec.1, hrecR hrec.2⟩
  | dPrj p =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨cb, ms, d, hm, ty, val, hty, hval, hsh⟩ := hrec
    exact ⟨cb, ms, d, hmem hm, ty, val, exprReader_blob_mono hb _ _ _ hty,
      exprReader_blob_mono hb _ _ _ hval, hsh⟩
  | iPrj p =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨cb, ms, ind, hm, ty, caps, hty, heq⟩ := hrec
    exact ⟨cb, ms, ind, hmem hm, ty, caps, exprReader_blob_mono hb _ _ _ hty, heq⟩
  | cPrj p =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, ty, hty, heq⟩ := hrec
    exact ⟨cb, ms, ind, ct, hs _ _ h1, h2, h3, h4, h5, h6, h7, h8, ty,
      exprReader_blob_mono hb _ _ _ hty, heq⟩
  | rPrj p =>
    rw [hinfo] at hrec; dsimp only at hrec ⊢
    obtain ⟨cb, ms, rc, hm, hrr⟩ := hrec
    exact ⟨cb, ms, rc, hmem hm, hrecR hrr⟩
  | muts _ =>
    rw [hinfo] at hrec
    exact False.elim hrec

/-- Two compatible `(store, blob)` pairs under a role-unique table assign `SameReading` to any
common constant address. -/
theorem readsIn_agree_of_compat {t : RoleTable}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {store₁ store₂ : Store} {blob₁ blob₂ : Address → Option ByteArray}
    (hs : ∀ x c₁ c₂, store₁ x = some c₁ → store₂ x = some c₂ → c₁ = c₂)
    (hb : ∀ x b₁ b₂, blob₁ x = some b₁ → blob₂ x = some b₂ → b₁ = b₂)
    {a : Address} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : ReadsIn t store₁ blob₁ a ci₁) (h₂ : ReadsIn t store₂ blob₂ a ci₂) :
    SameReading ci₁ ci₂ := by
  let mergedStore : Store := fun x => (store₁ x).orElse fun _ => store₂ x
  let mergedBlob : Address → Option ByteArray := fun x => (blob₁ x).orElse fun _ => blob₂ x
  have hs₁ : ∀ x c, store₁ x = some c → mergedStore x = some c := fun x c hx => by
    simp [mergedStore, hx]
  have hs₂ : ∀ x c, store₂ x = some c → mergedStore x = some c := fun x c hx => by
    cases h1 : store₁ x with
    | none => simp [mergedStore, h1, hx]
    | some c₁ => simp [mergedStore, h1, hs x c₁ c h1 hx]
  have hb₁ : ∀ x b, blob₁ x = some b → mergedBlob x = some b := fun x b hx => by
    simp [mergedBlob, hx]
  have hb₂ : ∀ x b, blob₂ x = some b → mergedBlob x = some b := fun x b hx => by
    cases h1 : blob₁ x with
    | none => simp [mergedBlob, h1, hx]
    | some b₁ => simp [mergedBlob, h1, hb x b₁ b h1 hx]
  exact ReadsIn.functional hroles (readsIn_mono hs₁ hb₁ h₁) (readsIn_mono hs₂ hb₂ h₂)

/-- **Sectioned compatibility theorem**: if `storeSec` / `blobSec` is a `SectionedStore rename`
of `(storeBare, blobBare)` under well-formed table `t`, and a circuit-loaded store
`(storeCirc, blobCirc)` agrees with `(storeSec, blobSec)` on overlapping addresses, then any
bare reading `ReadsIn t storeBare blobBare a ciBare` agrees up to `SameReading` with any
circuit reading `ReadsIn (renameTable rename t) storeCirc blobCirc (rename a) ciCirc` via
`ciBare.mapKeys rename`. -/
theorem sectioned_readsIn_agree_of_compat {t : RoleTable} (hc : t.check = .ok ())
    {rename : Address → Address}
    {storeBare storeSec storeCirc : Store}
    {blobBare blobSec blobCirc : Address → Option ByteArray}
    (hsec : SectionedStore rename storeBare storeSec blobBare blobSec)
    (hs : ∀ x c₁ c₂, storeCirc x = some c₁ → storeSec x = some c₂ → c₁ = c₂)
    (hb : ∀ x b₁ b₂, blobCirc x = some b₁ → blobSec x = some b₂ → b₁ = b₂)
    {a : Address} {ciBare ciCirc : Ix.Kernel.ConstantInfo .anon}
    (hBare : ReadsIn t storeBare blobBare a ciBare)
    (hCirc : ReadsIn (renameTable rename t) storeCirc blobCirc (rename a) ciCirc) :
    SameReading ciCirc (ciBare.mapKeys rename) := by
  have hroles' : ((renameTable rename t).bound.toList.map (·.1)).Nodup :=
    (RoleTable.check_nodup (renameTable_check hc hsec.inj)).1
  exact readsIn_agree_of_compat hroles' hs hb hCirc (attachSections_readsIn hc hsec hBare)

/-- Renaming keys preserves having type `False` (`Ix.Kernel.falseName` is a role key). -/
theorem mapKeys_type_eq_false_iff (rename : Address → Address) (ci : Ix.Kernel.ConstantInfo .anon) :
    (ci.mapKeys (md' := .anon) rename).toConstantVal.type = .const Ix.Kernel.falseName [] ↔
      ci.toConstantVal.type = .const Ix.Kernel.falseName [] := by
  rw [Ix.Kernel.ConstantInfo.mapKeys_toConstantVal]
  change (ci.toConstantVal.type).mapKeys (md' := .anon) rename = .const (.role .false) [] ↔
    ci.toConstantVal.type = .const (.role .false) []
  cases h : ci.toConstantVal.type with
  | const k us =>
    simp only [Ix.Kernel.Expr.mapKeys, Ix.Kernel.Expr.const.injEq]
    cases k <;> simp
  | _ => simp [Ix.Kernel.Expr.mapKeys]

private theorem noCollision_sectioned_agrees {V : View} {extra : List ByteArray}
    {callsA callsB : List (Call IxVM.F)} {E₀ R : Ixon.Env}
    {tb : ByteArray} {a : Address} {binding : Ix.Kernel.Admission.Binding}
    {t t' : RoleTable}
    (hV : SelfHashed V)
    (hNoCol : ¬ GenuineCollision V extra (callsA ++ callsB))
    (hLoadA : LoadedBy callsA E₀) (hLoadB : LoadedBy callsB R)
    (hHashedTb : Hashed callsB tb)
    (hAdmitTb : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t')
    (hViewBind : V.env.roleBinding = some ⟨binding.address, binding.bytes⟩)
    (hBindAddr : binding.address = a)
    (hAdmitBind : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t) :
    tb = binding.bytes ∧ t' = t ∧
      (∀ x c₁ c₂, storeOver E₀ R x = some c₁ → recordOf V.env x = some c₂ → c₁ = c₂) ∧
      (∀ x b₁ b₂, blobOver E₀ R x = some b₁ → V.env.blobs.get? x = some b₂ → b₁ = b₂) := by
  have hcA : ∀ c ∈ callsA, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inl h)
  have hcB : ∀ c ∈ callsB, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inr h)
  have hBytesEq : ∀ {held bytes : ByteArray},
      V.Preimage (Address.blake3Pure held) held →
      Hashed (callsA ++ callsB) bytes →
      Address.blake3Pure bytes = Address.blake3Pure held →
      bytes = held := fun {held bytes} hpre hh heq =>
    Classical.byContradiction fun hne =>
      hNoCol (Or.inl ⟨held, bytes, Or.inl hpre, hh, hne, heq⟩)
  have hHashBind : Address.blake3Pure binding.bytes = a :=
    (hV.2.2 ⟨binding.address, binding.bytes⟩ hViewBind).trans hBindAddr
  have hHashTb : Address.blake3Pure tb = a := by
    have ha := ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ _).mp hAdmitTb).authentic
    simpa [Address.admissionHash_eq] using ha
  have hPreBind : V.Preimage (Address.blake3Pure binding.bytes) binding.bytes :=
    Or.inr (Or.inr (Or.inl ⟨⟨binding.address, binding.bytes⟩, hViewBind,
      (hV.2.2 ⟨binding.address, binding.bytes⟩ hViewBind).symm, rfl⟩))
  have hTbEq : tb = binding.bytes :=
    hBytesEq hPreBind (hashed_mono hcB hHashedTb) (hHashTb.trans hHashBind.symm)
  have hTableEq : t' = t := by
    have hbStruct : ({ address := a, bytes := tb } : Ix.Kernel.Admission.Binding) = binding := by
      cases binding with
      | mk addr bs => simp only at hBindAddr hTbEq; subst hBindAddr; subst hTbEq; rfl
    rw [hbStruct] at hAdmitTb
    rw [hAdmitBind] at hAdmitTb
    exact (Except.ok.inj hAdmitTb).symm
  have hRecAgree : ∀ {E : Ixon.Env}, LoadedBy (callsA ++ callsB) E →
      ∀ x c₁ c₂, recordOf E x = some c₁ → recordOf V.env x = some c₂ → c₁ = c₂ := by
    intro E hLoad x c₁ c₂ h1 h2
    unfold recordOf at h1 h2
    cases hE : E.consts.get? x with
    | none => rw [hE] at h1; cases h1
    | some lc₁ =>
      cases hVe : V.env.consts.get? x with
      | none => rw [hVe] at h2; cases h2
      | some lc₂ =>
        simp only [hE, Option.bind_some] at h1
        simp only [hVe, Option.bind_some] at h2
        have hHash1 := hLoad.1 x lc₁ hE
        have hHash2 := hV.1 x lc₂ hVe
        have hPre : V.Preimage (Address.blake3Pure lc₂.rawBytes) lc₂.rawBytes :=
          Or.inl ⟨lc₂, hHash2.symm ▸ hVe, rfl⟩
        have hRawEq : lc₁.rawBytes = lc₂.rawBytes :=
          hBytesEq hPre hHash1.1 (hHash1.2.trans hHash2.symm)
        rw [hRawEq] at h1
        exact Option.some.inj (h1.symm.trans h2)
  have hBlobAgreeEnv : ∀ {E : Ixon.Env}, LoadedBy (callsA ++ callsB) E →
      ∀ x b₁ b₂, E.blobs.get? x = some b₁ → V.env.blobs.get? x = some b₂ → b₁ = b₂ := by
    intro E hLoad x b₁ b₂ h1 h2
    have hHash1 := hLoad.2 x b₁ h1
    have hHash2 := hV.2.1 x b₂ h2
    have hPre : V.Preimage (Address.blake3Pure b₂) b₂ :=
      Or.inr (Or.inl (hHash2.symm ▸ h2))
    exact hBytesEq hPre hHash1.1 (hHash1.2.trans hHash2.symm)
  have hLoadA' : LoadedBy (callsA ++ callsB) E₀ :=
    ⟨fun x lc h => ⟨hashed_mono hcA (hLoadA.1 x lc h).1, (hLoadA.1 x lc h).2⟩,
     fun x b h => ⟨hashed_mono hcA (hLoadA.2 x b h).1, (hLoadA.2 x b h).2⟩⟩
  have hLoadB' : LoadedBy (callsA ++ callsB) R :=
    ⟨fun x lc h => ⟨hashed_mono hcB (hLoadB.1 x lc h).1, (hLoadB.1 x lc h).2⟩,
     fun x b h => ⟨hashed_mono hcB (hLoadB.2 x b h).1, (hLoadB.2 x b h).2⟩⟩
  refine ⟨hTbEq, hTableEq, fun x c₁ c₂ h1 h2 => ?_, fun x b₁ b₂ h1 h2 => ?_⟩
  · unfold storeOver at h1
    cases hE : recordOf E₀ x with
    | some c =>
      simp only [hE, Option.orElse_some, Option.some.injEq] at h1
      subst h1; exact hRecAgree hLoadA' x c c₂ hE h2
    | none =>
      simp only [hE, Option.orElse_none] at h1
      exact hRecAgree hLoadB' x c₁ c₂ h1 h2
  · unfold blobOver at h1
    cases hE : E₀.blobs.get? x with
    | some b =>
      simp only [hE, Option.orElse_some, Option.some.injEq] at h1
      subst h1; exact hBlobAgreeEnv hLoadA' x b b₂ hE h2
    | none =>
      simp only [hE, Option.orElse_none] at h1
      exact hBlobAgreeEnv hLoadB' x b₁ b₂ h1 h2

universe u

/-- **End-to-end `compileCorrect` + `RecordSections` + `CircuitComposed` bridge**:
given a bare Lean closure compiled by `Ix.Cert.compileReport` (satisfying the `CompileCorrect`
hypotheses under `defaultTable = .ok t`) and a post-compile sectioned environment `ixeSec`
related to `ixe` by `SectionedStore rename (recordOf ixe) (recordOf ixeSec) ixe.blobs.get? ixeSec.blobs.get?`,
with admitted sectioned binding `bindingSec` admitting `renameTable rename t` and `SelfHashed`
view `V = ⟨{ ixeSec with roleBinding := some ⟨bindingSec.address, bindingSec.bytes⟩ }, trees⟩`:

Given `CircuitComposed`, for any accepted IxVM binding proof for `bindingSec.address` and accepted
in-scope typing proof under `bindingSec.address`, either the runs exhibited a `GenuineCollision`
against `V`, the claim bytes, and the committed footprint, **or**:
1. `Published ixe sub` and `IxonCommutesCovering ixe sub t envQ` hold from `compileCorrect`;
2. the circuit binding run hashed `bindingSec.bytes` and admitted `renameTable rename t` with a
   valid `TableShape` on all 77 groups, and `ConsistentReadOver` holds on the typing claim's seeds;
3. every bare reading `Reads t ixe a ciBare` transports to a sectioned reading
   `Reads (renameTable rename t) ixeSec (rename a) (ciBare.mapKeys rename)` and agrees up to
   `SameReading` with every `ReadsIn` witness over `(storeOver E₀ R, blobOver E₀ R)` loaded by
   the circuit! -/
theorem compileCorrect_sectioned_circuitComposed_bridge
    (hCircuit : CircuitComposed.{u})
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe ixeSec : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable}
    {envQ : Ix.Kernel.Env .source} {rename : Address → Address}
    {bindingSec : Ix.Kernel.Admission.Binding}
    (htable : Ix.Kernel.Reader.defaultTable = .ok t)
    (hsource : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (hcomp : Ix.Cert.compileReport env = .ok (ixe, failures))
    (hnofail : Ix.Cert.NoFailure failures sub)
    (hpubRoles : Ix.Cert.PublishedRolesBound t ixe)
    (hpubAgree : Ix.Cert.PublishedAgree ixe)
    (hevAgrees : Ix.Cert.EvidenceCheck.EvidenceAgrees t ixe)
    (hroleEv : Ix.Cert.RoleClosure.RoleEvidenceChecks)
    (hsec : SectionedStore rename (recordOf ixe) (recordOf ixeSec)
      (fun x => ixe.blobs.get? x) (fun x => ixeSec.blobs.get? x))
    (hAdmitSec : Ix.Kernel.Admission.admitBinding Address.admissionHash bindingSec =
      .ok (renameTable rename t)) :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec : Address),
          Ix.Claim.de bytesB = .ok (.binding spec bindingSec.address) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Ix.Claim), Ix.Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = bindingSec.address →
              ∀ (trees : List Ix.AssumptionTree) (seeds : List Address),
                let V : View :=
                  ⟨{ ixeSec with roleBinding := some ⟨bindingSec.address, bindingSec.bytes⟩ }, trees⟩
                SelfHashed V → ClaimSeeds cA V seeds →
                  GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                    (Ix.Cert.Published ixe sub ∧
                      Ix.Cert.IxonCommutesCovering.{u} ixe sub t envQ ∧
                      ∃ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
                        Hashed callsB bindingSec.bytes ∧
                        AllBound (renameTable rename t) ∧ LoadedBy callsB R ∧
                        TableShape.{u} (renameTable rename t) (fun _ => True) R envT ∧
                        ConsistentReadOver.{u} callsA (renameTable rename t) R envT seeds ∧
                        (∀ a ciBare, Reads t ixe a ciBare →
                          Reads (renameTable rename t) ixeSec (rename a) (ciBare.mapKeys rename)) ∧
                        (∀ E₀, LoadedBy callsA E₀ →
                          ∀ a ciBare ciCirc,
                            Reads t ixe a ciBare →
                            ReadsIn (renameTable rename t) (storeOver E₀ R) (blobOver E₀ R)
                              (rename a) ciCirc →
                            SameReading ciCirc (ciBare.mapKeys rename))) := by
  obtain ⟨hPub, hComm⟩ := Ix.Cert.ReaderStreamsTrace.compileCorrect.{u}
    env roots sub ixe failures t envQ htable hsource hcomp hnofail
    hpubRoles hpubAgree hevAgrees hroleEv
  have hcheck : t.check = .ok () := Ix.Cert.defaultTable_check htable
  intro idB specB compiledB physicalB cfgB certB bitsB planB wfB romB validB lenB dB
    wiresB outputB resultB signedB rootB erasedB notinB rowsB rowsLenB memoB decB decOutB
  obtain ⟨vB, hpB, callsB, hobsB, hromB, hA⟩ :=
    @hCircuit idB specB compiledB physicalB cfgB certB bitsB planB wfB romB validB lenB dB
      wiresB outputB resultB signedB rootB erasedB notinB rowsB rowsLenB memoB decB decOutB
  refine ⟨vB, hpB, callsB, hobsB, hromB, ?_⟩
  intro idA specA compiledA physicalA cfgA certA bitsA planA wfA romA validA lenA dA
    wiresA outputA resultA signedA rootA erasedA notinA rowsA rowsLenA memoA decA decOutA
  obtain ⟨vA, hpA, callsA, hobsA, hromA, hSpec⟩ :=
    @hA idA specA compiledA physicalA cfgA certA bitsA planA wfA romA validA lenA dA
      wiresA outputA resultA signedA rootA erasedA notinA rowsA rowsLenA memoA decA decOutA
  refine ⟨vA, hpA, callsA, hobsA, hromA, ?_⟩
  intro bytesB spec deB dgB bytesA cA deA dgA hsc ctx hctx hba trees seeds V hV hseeds
  by_cases hCol : GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB)
  · exact Or.inl hCol
  · rcases hSpec.selfHashed deB dgB deA dgA hsc hctx hba hseeds hV with
        hCol' | ⟨tb, t', R, envT, htb, hadm', hall, hloadB, hshape, hcons⟩
    · exact Or.inl hCol'
    · right
      have ⟨E₀_wit, _, hLoadA_wit, _⟩ := hcons
      obtain ⟨htbEq, htEq, -, -⟩ :=
        noCollision_sectioned_agrees hV hCol hLoadA_wit hloadB htb hadm' rfl rfl hAdmitSec
      subst htbEq
      subst htEq
      refine ⟨hPub, hComm, R, envT, htb, hall, hloadB, hshape, hcons,
        fun a ciBare hBare => attachSections_readsIn hcheck hsec hBare,
        fun E₀ hLoadA a ciBare ciCirc hBare hCirc => ?_⟩
      obtain ⟨-, -, hStoreAgree, hBlobAgree⟩ :=
        noCollision_sectioned_agrees hV hCol hLoadA hloadB htb hadm' rfl rfl hAdmitSec
      exact sectioned_readsIn_agree_of_compat hcheck hsec hStoreAgree hBlobAgree hBare hCirc

end Ix.Cert.RecordSectionsBridge

/-! ## 8. Standard-axiom audits (zero `sorry`, zero `native_decide`, zero `bv_decide`) -/

/--
info: 'Ix.Cert.RecordSectionsBridge.memberReader_withBinders' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.memberReader_withBinders

/--
info: 'Ix.Cert.RecordSectionsBridge.readRecord_withBinders' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.readRecord_withBinders

/--
info: 'Ix.Cert.RecordSectionsBridge.withSection_readRecord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.withSection_readRecord

/--
info: 'Ix.Cert.RecordSectionsBridge.withSection_readsIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.withSection_readsIn

/--
info: 'Ix.Cert.RecordSectionsBridge.renameTable_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.renameTable_check

/--
info: 'Ix.Cert.RecordSectionsBridge.attachSections_readsIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.attachSections_readsIn

/--
info: 'Ix.Cert.RecordSectionsBridge.attachSections_readsIn_sameAddr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.attachSections_readsIn_sameAddr

/--
info: 'Ix.Cert.RecordSectionsBridge.sectioned_readsIn_agree_of_compat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.sectioned_readsIn_agree_of_compat

/--
info: 'Ix.Cert.RecordSectionsBridge.compileCorrect_sectioned_circuitComposed_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.RecordSectionsBridge.compileCorrect_sectioned_circuitComposed_bridge
