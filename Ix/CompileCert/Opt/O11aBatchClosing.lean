import Ix.CompileCert.Opt.O11aReconstruction

/-!
The final batched lambda reconstruction agrees with sequential singleton
closing on the scope actually built by O11a. SOURCE-ONLY / UNCOMPILED.
Structural name distinctness is proved from actual allocator reservations;
it is not a new premise on a public compiler caller. Dependent domains,
arbitrary open bodies, cached fields and instance callback outcomes are kept.
No cross-branch conversion or original O11aFaithful endpoint is asserted.
-/

namespace Ix.CompileCert.Opt.O11aBatchClosing

open Ix (Name Level Expr RecursorVal)
open Ix.AuxGen (FreshFVars LocalDecl SourceRecTarget mkLambda)
open Ix.Compile.Canon (NameTable keyName)
open Ix.CompileCert.Conv
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.FreshFVarsProof
open Ix.CompileCert.Opt.FreshTelescope
open Ix.CompileCert.Opt.O11aFields
open Ix.CompileCert.Opt.O11aSourceBounds
open Ix.CompileCert.Opt.O11aReaderGrowth
open Ix.CompileCert.Opt.O11aReconstruction

/-- Pure structural scope condition, built by appending a new key. It makes
no assertion about any expression's abstraction or conversion. -/
inductive FreshDecls : Array LocalDecl → Prop
  | empty : FreshDecls #[]
  | push {decls : Array LocalDecl} (valid : FreshDecls decls) (decl : LocalDecl)
      (fresh : ∀ old ∈ decls, keyName old.fvarName ≠ keyName decl.fvarName) :
      FreshDecls (decls.push decl)

private theorem declarationTable_list (decls : Array LocalDecl) :
    declarationTable decls = decls.toList.zipIdx.foldl
      (fun table (decl, index) => table.insert decl.fvarName index) {} := by
  unfold declarationTable
  rewrite [← Array.forIn_toList, Array.toList_zipIdx, List.forIn_pure_yield_eq_foldl]
  rfl

theorem declarationTable_push (decls : Array LocalDecl) (decl : LocalDecl) :
    declarationTable (decls.push decl) =
      (declarationTable decls).insert decl.fvarName decls.size := by
  rw [declarationTable_list, declarationTable_list]
  simp [List.zipIdx_append, List.foldl_append]

theorem declarationTable_bound (decls : Array LocalDecl) (valid : FreshDecls decls) :
    ∀ name index, (declarationTable decls).get? name = some index → index < decls.size := by
  induction valid with
  | empty =>
      intro name index hit
      change none = some index at hit
      cases hit
  | @push decls valid decl fresh ih =>
      intro name index hit
      rw [declarationTable_push, NameTable.get?_insert] at hit
      split at hit
      · cases hit
        simpa only [Array.size_push] using Nat.lt_succ_self decls.size
      · have bound := ih name index hit
        simpa only [Array.size_push] using Nat.lt.step bound

theorem declarationTable_absent (decls : Array LocalDecl) (valid : FreshDecls decls)
    (name : Name) (fresh : ∀ old ∈ decls, keyName old.fvarName ≠ keyName name) :
    (declarationTable decls).get? name = none := by
  revert fresh
  induction valid with
  | empty => exact fun _ => rfl
  | @push decls valid decl distinct ih =>
      intro fresh
      have oldFresh : ∀ old ∈ decls, keyName old.fvarName ≠ keyName name :=
        fun old member => fresh old (Array.mem_push_of_mem decl member)
      have lastFresh := fresh decl Array.mem_push_self
      rw [declarationTable_push, NameTable.get?_insert]
      simp only [lastFresh, ↓reduceIte, ih oldFresh]

/-- Inserting a fresh key at position k cannot change a domain whose scope
ends at or before k. This preserves the actual dependent-domain convention. -/
theorem babs_insert_inactive (table : NameTable Nat) (name : Name) (position scope : Nat)
    (absent : table.get? name = none) (inactive : scope ≤ position)
    (body : Tm) (depth : Nat) :
    babs (table.insert name position).get? scope depth body = babs table.get? scope depth body := by
  induction body generalizing depth with
  | fvar query =>
      by_cases same : keyName name = keyName query
      · have old : table.get? query = none := by
          unfold NameTable.get? at absent ⊢
          rw [← same]
          exact absent
        simp [babs, NameTable.get?_insert, same, old, Nat.not_lt_of_ge inactive]
      · simp [babs, NameTable.get?_insert, same]
  | app f a ihf iha => simp only [babs, ihf depth, iha depth]
  | lam domain body ihd ihb => simp only [babs, ihd depth, ihb (depth + 1)]
  | pi domain body ihd ihb => simp only [babs, ihd depth, ihb (depth + 1)]
  | letE domain value body ihd ihv ihb =>
      simp only [babs, ihd depth, ihv depth, ihb (depth + 1)]
  | proj owner index body ih => exact congrArg (Tm.proj owner index) (ih depth)
  | _ => rfl

/-- Batch closing at k+1 equals closing the last binder and then the previous
k binders one level deeper. The bound is a table-index fact, not a body-domain
or closed-input premise. -/
theorem babs_insert_last (table : NameTable Nat) (name : Name) (scope : Nat)
    (bounded : ∀ query index, table.get? query = some index → index < scope)
    (body : Tm) (depth : Nat) :
    babs (table.insert name scope).get? (scope + 1) depth body =
      babs table.get? scope (depth + 1)
        (babs (singletonTable name).get? 1 depth body) := by
  induction body generalizing depth with
  | fvar query =>
      by_cases same : keyName name = keyName query
      · simp [babs, NameTable.get?_insert, singletonTable_get, same]
      · simp only [babs, NameTable.get?_insert, singletonTable_get, same, ↓reduceIte]
        cases hit : table.get? query with
        | none => rfl
        | some index =>
            have below := bounded query index hit
            have belowNext : index < scope + 1 := by omega
            simp only [below, belowNext, ↓reduceIte]
            congr 1
            omega
  | bvar index =>
      by_cases above : depth ≤ index
      · have shifted : depth + 1 ≤ index + 1 := by omega
        simp only [babs, above, shifted, ↓reduceIte]
        congr 1
        omega
      · have below : ¬ depth + 1 ≤ index := by omega
        simp only [babs, above, below, ↓reduceIte]
  | app f a ihf iha => simp only [babs, ihf depth, iha depth]
  | lam domain body ihd ihb => simp only [babs, ihd depth, ihb (depth + 1)]
  | pi domain body ihd ihb => simp only [babs, ihd depth, ihb (depth + 1)]
  | letE domain value body ihd ihv ihb =>
      simp only [babs, ihd depth, ihv depth, ihb (depth + 1)]
  | proj owner index body ih => exact congrArg (Tm.proj owner index) (ih depth)
  | _ => rfl

private def wrapErased (table : NameTable Nat) (body : Tm) (entry : LocalDecl × Nat) : Tm :=
  .lam (babs table.get? entry.2 0 (er entry.1.domain)) body

private theorem erasedLambda_fold (body : Tm) (decls : Array LocalDecl) :
    erasedLambda body decls = decls.toList.zipIdx.reverse.foldl
      (wrapErased (declarationTable decls))
      (babs (declarationTable decls).get? decls.size 0 body) := by
  by_cases empty : decls.size = 0
  · have equal := Array.eq_empty_of_size_eq_zero empty
    subst decls
    simp [erasedLambda, babs_zero]
  · have nonempty : (decls.size == 0) = false := by simpa using empty
    unfold erasedLambda
    rw [nonempty]
    change forIn (m := Id) decls.zipIdx.reverse
      (babs (declarationTable decls).get? decls.size 0 body)
      (fun entry result => pure (.yield (wrapErased (declarationTable decls) result entry))) = _
    rewrite [← Array.forIn_toList, Array.toList_reverse, Array.toList_zipIdx,
      List.forIn_pure_yield_eq_foldl]
    rfl

private theorem wrap_fold_insert (table : NameTable Nat) (name : Name) (position : Nat)
    (absent : table.get? name = none) :
    ∀ (entries : List (LocalDecl × Nat)) (body : Tm),
      (∀ entry ∈ entries, entry.2 ≤ position) →
      entries.foldl (wrapErased (table.insert name position)) body =
        entries.foldl (wrapErased table) body
  | [], _, _ => rfl
  | entry :: rest, body, bounded => by
      rw [List.foldl_cons, List.foldl_cons]
      have same : wrapErased (table.insert name position) body entry = wrapErased table body entry := by
        unfold wrapErased
        rw [babs_insert_inactive table name position entry.2 absent (bounded entry (.head _))]
      rw [same]
      exact wrap_fold_insert table name position absent rest _
        (fun entry member => bounded entry (.tail _ member))

/-- Exact append law for the actual batch reconstruction under the structural
condition supplied later by the real binder loop. -/
theorem erasedLambda_push (decls : Array LocalDecl) (valid : FreshDecls decls)
    (decl : LocalDecl)
    (fresh : ∀ old ∈ decls, keyName old.fvarName ≠ keyName decl.fvarName) (body : Tm) :
    erasedLambda body (decls.push decl) = erasedLambda
      (.lam (er decl.domain) (babs (singletonTable decl.fvarName).get? 1 0 body)) decls := by
  have absent := declarationTable_absent decls valid decl.fvarName fresh
  have bounded := declarationTable_bound decls valid
  have rows : (decls.push decl).toList.zipIdx.reverse =
      (decl, decls.size) :: decls.toList.zipIdx.reverse := by
    simp [List.zipIdx_append]
  rw [erasedLambda_fold, rows, List.foldl_cons, erasedLambda_fold]
  simp only [Array.size_push, declarationTable_push]
  have initial : wrapErased ((declarationTable decls).insert decl.fvarName decls.size)
      (babs ((declarationTable decls).insert decl.fvarName decls.size).get?
        (decls.size + 1) 0 body) (decl, decls.size) =
      babs (declarationTable decls).get? decls.size 0
        (.lam (er decl.domain) (babs (singletonTable decl.fvarName).get? 1 0 body)) := by
    unfold wrapErased
    rewrite [babs_insert_inactive _ _ _ _ absent (Nat.le_refl _),
      babs_insert_last _ _ _ bounded]
    rfl
  rw [initial]
  apply wrap_fold_insert _ _ _ absent
  intro entry member
  have bound := List.snd_lt_add_of_mem_zipIdx (List.mem_reverse.1 member)
  simpa only [Nat.zero_add, Array.length_toList] using Nat.le_of_lt bound

theorem mkLambda_push_er (decls : Array LocalDecl) (valid : FreshDecls decls)
    (decl : LocalDecl)
    (fresh : ∀ old ∈ decls, keyName old.fvarName ≠ keyName decl.fvarName) (body : Expr) :
    er (mkLambda body (decls.push decl)) = er (mkLambda (mkLambda body #[decl]) decls) := by
  calc
    er (mkLambda body (decls.push decl)) = erasedLambda (er body) (decls.push decl) :=
      er_mkLambda _ _
    _ = erasedLambda (.lam (er decl.domain)
        (babs (singletonTable decl.fvarName).get? 1 0 (er body))) decls :=
      erasedLambda_push decls valid decl fresh (er body)
    _ = erasedLambda (er (mkLambda body #[decl])) decls := by
      rw [mkLambda_singleton, er_mkLam, er_batchAbstractNames]
    _ = er (mkLambda (mkLambda body #[decl]) decls) := (er_mkLambda _ _).symm

theorem mkLambda_eq_closeDecls (decls : Array LocalDecl) (valid : FreshDecls decls)
    (body : Expr) : er (mkLambda body decls) = er (closeDecls decls.toList body) := by
  induction valid generalizing body with
  | empty => rfl
  | @push decls valid decl fresh ih =>
      rewrite [mkLambda_push_er decls valid decl fresh body, ih,
        Array.toList_push, closeDecls_append]
      rfl

/-- Only structural scope data: distinct keys and their actual reservations. -/
def ScopeInv (state : BinderState) : Prop :=
  FreshDecls state.2.2.1 ∧
    ∀ decl ∈ state.2.2.1, keyName decl.fvarName ∈ state.1.used

private theorem scope_push (supply : FreshFVars) (decls : Array LocalDecl)
    (valid : FreshDecls decls)
    (reserved : ∀ decl ∈ decls, keyName decl.fvarName ∈ supply.used)
    (name : Name) (domain : Expr) (info : Lean.BinderInfo) (index : Nat) :
    let decl : LocalDecl := {
      fvarName := (supply.fresh "o11a" index).1.1,
      binderName := name, domain := domain, info := info }
    FreshDecls (decls.push decl) ∧
      ∀ item ∈ decls.push decl, keyName item.fvarName ∈ (supply.fresh "o11a" index).2.used := by
  dsimp only
  constructor
  · apply FreshDecls.push valid
    intro old member same
    apply fresh_not_mem supply "o11a" index
    rw [← same]
    exact reserved old member
  · intro item member
    rcases Array.mem_push.1 member with old | equal
    · exact fresh_grows supply "o11a" index _ (reserved item old)
    · subst item
      exact fresh_reserved supply "o11a" index

/-- Both retaining branches extend the structural scope with an actually
fresh key; the cross branch still grows the supply and retains the old scope. -/
theorem binderStep_scope (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) (index : Nat)
    (state : BinderState) (step : ForInStep BinderState) (valid : ScopeInv state)
    (run : binderStepWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread index state = .ok step) :
    ∃ next, step = .yield next ∧ ScopeInv next := by
  rcases state with ⟨supply, cur, decls, fields⟩
  rcases valid with ⟨distinct, reserved⟩
  unfold binderStepWith at run
  obtain ⟨parts, _, run⟩ := except_bind_ok.1 run
  rcases parts with ⟨name, domain, body, info⟩
  have appended := scope_push supply decls distinct reserved name domain info index
  dsimp only at run
  split at run
  · cases run
    exact ⟨_, rfl, appended⟩
  · split at run
    · cases run
      exact ⟨_, rfl, appended⟩
    · obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨answer, _, run⟩ := except_bind_ok.1 run
      rcases answer with ⟨inst, level⟩
      obtain ⟨field, _, run⟩ := except_bind_ok.1 run
      cases run
      exact ⟨_, rfl, distinct,
        fun decl member => fresh_grows supply "o11a" index _ (reserved decl member)⟩

/-- The actual full loop supplies the cross-binder condition internally,
including successful dropped-IH branches and arbitrary callback answers. -/
theorem binderLoop_scope (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) : ScopeInv out := by
  unfold binderLoopWith at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  refine Ix.CompileCert.Canon.forIn_except_list _ (fun _ state => ScopeInv state)
    ?_ _ [] _ out ?_ run
  · intro preRun index state step valid succeeded
    exact binderStep_scope inst? rv inBlock recFields telescope numFields j unread
      index state step valid succeeded
  · refine ⟨FreshDecls.empty, ?_⟩
    intro decl member
    simp at member

/-- The batch-to-sequential bridge has no extra scope or freshness premise
on an actual loop caller. Its only hypothesis is the actual successful run. -/
theorem binderLoop_batch_eq_sequential
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) :
    er (mkLambda out.2.1 out.2.2.1) = er (closeDecls out.2.2.1.toList out.2.1) :=
  mkLambda_eq_closeDecls out.2.2.1
    (binderLoop_scope inst? rv inBlock recFields telescope numFields j unread
      count supply minor out run).1 out.2.1

/-- Source preparation discharges protection, and actual allocation supplies
the distinct scope. Closing a retained field prefix by the real final batched
mkLambda therefore recovers the raw minor's erasure, including open inputs. -/
theorem prepared_field_prefix_batch_close (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) (minorTy : Expr)
    (numFields index : Nat) (unread : String) (prepared : TargetState)
    (minor : Expr) (read : mins[index]? = some minor)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (inBlock : Array Bool) (count : Nat) (out : BinderState)
    (fieldsOnly : count ≤ numFields) :
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
      (initialSupply rv ps ms mins)
    prepareFields minorTy numFields aux.2 (actualTargetRead rv ps env aux.1) unread =
        .ok prepared →
      binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
        numFields index unread count prepared.1 minor = .ok out →
      Protects out.1 out.2.1 ∧ er (mkLambda out.2.1 out.2.2.1) = er minor := by
  dsimp only
  intro prepareRun loopRun
  obtain ⟨covered, sequential⟩ := prepared_field_prefix_close rv levels ps ms mins env minorTy
    numFields index unread prepared minor read inst? inBlock count out fieldsOnly prepareRun loopRun
  exact ⟨covered, (binderLoop_batch_eq_sequential inst? rv inBlock prepared.2
    (ps ++ ms ++ mins) numFields index unread count prepared.1 minor out loopRun).trans sequential⟩

/-- The actual public helper's final output uses a scope for which batched
and sequential closing agree, even when cross binders were dropped. -/
theorem sizeOfMinorWith_batch_eq_sequential (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (levels : Array Level)
    (ps ms mins : Array Expr) (index : Nat) (output : Expr)
    (run : sizeOfMinorWith env inst? rv inBlock levels ps ms mins index = .ok (some output)) :
    ∃ opened : BinderState,
      output = mkLambda opened.2.1 opened.2.2.1 ∧ ScopeInv opened ∧
      er output = er (closeDecls opened.2.2.1.toList opened.2.1) := by
  obtain ⟨_, ctor, _, prepared, minor, opened, _, _, _,
    _, loopRun, _, _, outputEq⟩ :=
    sizeOfMinorWith_success_fields env inst? rv inBlock levels ps ms mins index output run
  have scope := binderLoop_scope inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
    ctor.numFields index _ _ prepared.1 minor opened loopRun
  refine ⟨opened, outputEq, scope, ?_⟩
  rw [outputEq]
  exact mkLambda_eq_closeDecls _ scope.1 _

end Ix.CompileCert.Opt.O11aBatchClosing
