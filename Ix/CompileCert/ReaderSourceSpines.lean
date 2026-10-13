import Ix.CompileCert.ReaderSpines

/-! Recover syntactic spine facts from the actual unshared expression reader.
These facts connect source/reader expression correspondence to recursor
analysis without assuming that recursor discovery already succeeded. -/

namespace Ix.CompileCert.ReaderSourceSpines

open Ix Kernel.Reader

def Outer (reader : ECx) : Ixon.Expr → Kernel.Expr → Prop
  | .var index, .bvar target => index.toNat = target
  | .all _ _ type body, .forallE targetType targetBody binder =>
    convExpr reader #[] type = .ok targetType ∧ convExpr reader #[] body = .ok targetBody ∧ binder = ⟨.never⟩
  | .app function argument, .app targetFunction targetArgument =>
    convExpr reader #[] function = .ok targetFunction ∧ convExpr reader #[] argument = .ok targetArgument
  | .ref index _, .const name _ => ∃ ref, reader.refAt index = .ok ref ∧ name = reader.cx.nameOf ref
  | .recur index _, .const name _ => reader.self index.toNat = some name
  | .sort _, .sort _ | .lam .., .lam .. | .letE .., .letE .. | .prj .., .proj .. => True
  | .nat _, .lit (.natVal _) | .str _, .lit (.strVal _) => True
  | _, _ => False

/-- Successful reading without a sharing table retains the outer constructor
and supplies the actual child reads and reference lookup for spine traversal. -/
theorem read_outer (reader : ECx) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target) : Outer reader expression target := by
  cases expression with
  | var index =>
    simp only [convExpr, Kernel.Expr.mkBvar_eq, pure, Except.pure, Except.ok.injEq] at read
    cases read
    rfl
  | sort index =>
    obtain ⟨level, _, returned⟩ := Sharing.Verify.except_bind_eq_ok read
    cases Except.ok.inj returned
    trivial
  | ref index levels =>
    obtain ⟨ref, found, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨universes, _, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact ⟨ref, found, rfl⟩
  | recur index levels =>
    simp only [convExpr] at read
    cases found : reader.self index.toNat with
    | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at read
    | some name =>
      simp only [found] at read
      obtain ⟨universes, _, returned⟩ := Sharing.Verify.except_bind_eq_ok read
      cases Except.ok.inj returned
      exact found
  | prj index field value =>
    obtain ⟨ref, _, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨value, _, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | str index =>
    obtain ⟨bytes, _, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    cases found : String.fromUTF8? bytes with
    | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at rest
    | some value =>
      simp only [found] at rest
      cases Except.ok.inj rest
      trivial
  | nat index =>
    obtain ⟨bytes, _, returned⟩ := Sharing.Verify.except_bind_eq_ok read
    cases Except.ok.inj returned
    trivial
  | app function argument =>
    obtain ⟨targetFunction, first, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetArgument, second, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact ⟨first, second⟩
  | lam contract type body =>
    obtain ⟨targetType, _, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetBody, _, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | all contract binder type body =>
    obtain ⟨targetType, first, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetBody, second, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact ⟨first, second, rfl⟩
  | letE contract type value body =>
    obtain ⟨targetType, _, rest⟩ := Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetValue, _, rest⟩ := Sharing.Verify.except_bind_eq_ok rest
    obtain ⟨targetBody, _, returned⟩ := Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | share index => simp [convExpr, malformed, throw, throwThe, MonadExceptOf.throw] at read

theorem read_forall (reader : ECx) (expression : Ixon.Expr) (type body : Kernel.Expr) (binder : Kernel.BinderMeta)
    (read : convExpr reader #[] expression = .ok (.forallE type body binder)) :
    ∃ contract metadata rawType rawBody, expression = .all contract metadata rawType rawBody ∧
      convExpr reader #[] rawType = .ok type ∧ convExpr reader #[] rawBody = .ok body ∧ binder = ⟨.never⟩ := by
  have shape := read_outer reader expression _ read
  cases expression <;> simp only [Outer] at shape
  exact ⟨_, _, _, _, rfl, shape⟩

theorem read_app (reader : ECx) (expression : Ixon.Expr) (function argument : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok (.app function argument)) :
    ∃ rawFunction rawArgument, expression = .app rawFunction rawArgument ∧
      convExpr reader #[] rawFunction = .ok function ∧ convExpr reader #[] rawArgument = .ok argument := by
  have shape := read_outer reader expression _ read
  cases expression <;> simp only [Outer] at shape
  exact ⟨_, _, rfl, shape⟩

theorem read_bvar (reader : ECx) (expression : Ixon.Expr) (index : Nat)
    (read : convExpr reader #[] expression = .ok (.bvar index)) :
    ∃ raw, expression = .var raw ∧ raw.toNat = index := by
  have shape := read_outer reader expression _ read
  cases expression <;> simp only [Outer] at shape
  exact ⟨_, rfl, shape⟩

def BinderRead (reader : ECx) (raw : Ixon.Expr) (target : Kernel.Expr × Kernel.BinderMeta) : Prop :=
  convExpr reader #[] raw = .ok target.1 ∧ target.2 = ⟨.never⟩

/-- A telescope in the already-related kernel expression is present in the
unshared Ixon syntax, with corresponding domain and residual-body reads. -/
theorem read_stripAll (reader : ECx) (empty : reader.src.sharing = #[])
    (count : Nat) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target)
    (binders : List (Kernel.Expr × Kernel.BinderMeta)) (body : Kernel.Expr)
    (parsed : target.stripPis count = some (binders, body)) :
    ∃ types residual, stripAll reader.src count expression = some (types, residual) ∧
      List.Forall₂ (BinderRead reader) types binders ∧ convExpr reader #[] residual = .ok body := by
  induction count generalizing expression target binders body with
  | zero =>
    cases Option.some.inj parsed
    exact ⟨[], expression, rfl, .nil, read⟩
  | succ count ih =>
    cases target with
    | forallE type tail binder =>
      obtain ⟨contract, metadata, rawType, rawBody, rawEq, typeRead, bodyRead, binderEq⟩ :=
        read_forall reader expression type tail binder read
      subst expression
      cases tailParsed : tail.stripPis count with
      | none => simp [Kernel.Expr.stripPis, tailParsed] at parsed
      | some result =>
        rcases result with ⟨rest, result⟩
        have same : ((type, binder) :: rest, result) = (binders, body) := by
          simpa [Kernel.Expr.stripPis, tailParsed] using parsed
        cases same
        obtain ⟨types, residual, stripped, meanings, bodyRead⟩ := ih rawBody tail bodyRead rest body tailParsed
        exact ⟨rawType :: types, residual,
          by simp [stripAll, ReaderSpines.unshare_empty reader.src empty, stripped],
          .cons ⟨typeRead, binderEq⟩ meanings, bodyRead⟩
    | _ => simp [Kernel.Expr.stripPis] at parsed

def kernelAppDepth : Kernel.Expr → Nat
  | .app function _ => kernelAppDepth function + 1
  | _ => 0

theorem read_appDepth (reader : ECx) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target) :
    ReaderSpines.appDepth expression = kernelAppDepth target := by
  induction expression generalizing target with
  | app function argument ihf iha =>
    have shape := read_outer reader (.app function argument) target read
    cases target <;> simp only [Outer] at shape
    exact congrArg (· + 1) (ihf _ shape.1)
  | _ =>
    have shape := read_outer reader _ target read
    cases target <;> simp only [Outer, ReaderSpines.appDepth, kernelAppDepth] at shape ⊢

/-- With enough application fuel, the actual unshared head walk reads to
the head of the corresponding kernel expression. -/
theorem read_appHead (reader : ECx) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : Kernel.Expr) (read : convExpr reader #[] expression = .ok target)
    (enough : kernelAppDepth target < fuel) :
    convExpr reader #[] (appHead reader.src fuel expression) = .ok target.getAppFn := by
  induction fuel generalizing expression target with
  | zero => omega
  | succ fuel ih =>
    have shape := read_outer reader expression target read
    cases expression with
    | app function argument =>
      cases target <;> simp only [Outer] at shape
      simp only [kernelAppDepth] at enough
      simpa only [appHead, ReaderSpines.unshare_empty reader.src empty, Kernel.Expr.getAppFn] using
        ih function _ shape.1 (by omega)
    | _ =>
      cases target <;> simp only [Outer] at shape
      all_goals simpa only [appHead, ReaderSpines.unshare_empty reader.src empty, Kernel.Expr.getAppFn] using read

theorem read_variable_head (reader : ECx) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : Kernel.Expr) (read : convExpr reader #[] expression = .ok target)
    (enough : kernelAppDepth target < fuel) (index : Nat) (head : target.getAppFn = .bvar index) :
    ∃ raw, appHead reader.src fuel expression = .var raw ∧ raw.toNat = index := by
  have headRead := read_appHead reader empty fuel expression target read enough
  rw [head] at headRead
  exact read_bvar reader _ index headRead

def sourceAppDepth : Ix.Expr → Nat
  | .app function _ _ => sourceAppDepth function + 1
  | .mdata _ body _ => sourceAppDepth body
  | _ => 0

theorem related_appDepth (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target) :
    kernelAppDepth target = sourceAppDepth source := by
  induction related <;> simp_all [kernelAppDepth, sourceAppDepth]

/-- The fuel bound for the raw emitted application spine is a bound on the
actual source syntax, erasing source metadata nodes. -/
theorem source_appDepth (reader : ECx) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (related : ExpressionState.Related names sourceParams params source target) :
    ReaderSpines.appDepth expression = sourceAppDepth source :=
  (read_appDepth reader expression target read).trans (related_appDepth names sourceParams params source target related)

def sourceHead : Ix.Expr → Ix.Expr
  | .app function _ _ => sourceHead function
  | .mdata _ body _ => sourceHead body
  | expression => expression

theorem related_head (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target) :
    ExpressionState.Related names sourceParams params (sourceHead source) target.getAppFn := by
  induction related with
  | app _ _ _ ihf _ => exact ihf
  | mdata _ _ _ ih => exact ih
  | _ => constructor <;> assumption

theorem related_variable_head (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target)
    (index : Nat) (hash : Address) (head : sourceHead source = .bvar index hash) :
    target.getAppFn = .bvar index := by
  have headRelated := related_head names sourceParams params source target related
  rw [head] at headRelated
  generalize result : target.getAppFn = value at headRelated ⊢
  cases headRelated
  rfl

/-- A source motive-variable head is reflected by the actual unshared Ixon
walk; the numerical result index is preserved exactly. -/
theorem source_variable_head (reader : ECx) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : Kernel.Expr) (read : convExpr reader #[] expression = .ok target)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (related : ExpressionState.Related names sourceParams params source target)
    (enough : sourceAppDepth source < fuel) (index : Nat) (hash : Address)
    (head : sourceHead source = .bvar index hash) :
    ∃ raw, appHead reader.src fuel expression = .var raw ∧ raw.toNat = index :=
  read_variable_head reader empty fuel expression target read
    (by rw [related_appDepth names sourceParams params source target related]; exact enough) index
    (related_variable_head names sourceParams params source target related index hash head)

theorem refAt_resolves (reader : ECx) (index : UInt64) (ref : Kernel.ConstRef Address)
    (read : reader.refAt index = .ok ref) :
    ∃ address, reader.src.refs[index.toNat]? = some address ∧ resolve reader.cx.store address = some ref := by
  unfold ECx.refAt at read
  cases found : reader.src.refs[index.toNat]? with
  | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at read
  | some address =>
    simp only [found] at read
    cases resolved : resolve reader.cx.store address with
    | none => simp [resolved, malformed, throw, throwThe, MonadExceptOf.throw] at read
    | some actual =>
      simp only [resolved, pure, Except.pure, Except.ok.injEq] at read
      subst actual
      exact ⟨address, rfl, resolved⟩

/-- Alignment of the reader's self names with anonymous self-member lookup.
External heads use the reader's actual address-table resolution directly. -/
def SelfAligned (reader : ECx) (owner : Address) : Prop :=
  ∀ (index : UInt64) name, reader.self index.toNat = some name →
    ∃ ref, ReaderSpines.selfRef reader.src owner index = some ref ∧ reader.cx.nameOf ref = name

theorem read_constant_head (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target) (enough : kernelAppDepth target < spineFuel)
    (name : Kernel.Name) (levels : List Kernel.Level) (head : target.getAppFn = .const name levels) :
    ∃ ref, headRef reader.cx.store owner reader.src expression = some ref ∧ reader.cx.nameOf ref = name := by
  have headRead := read_appHead reader empty spineFuel expression target read enough
  rw [head] at headRead
  have shape := read_outer reader (appHead reader.src spineFuel expression) _ headRead
  cases found : appHead reader.src spineFuel expression <;> simp only [found, Outer] at shape
  · rename_i index universes
    obtain ⟨ref, read, named⟩ := shape
    obtain ⟨address, stored, resolved⟩ := refAt_resolves reader index ref read
    exact ⟨ref, by simp [headRef, found, stored, resolved], named.symm⟩
  · rename_i index universes
    obtain ⟨ref, resolved, named⟩ := self index name shape
    refine ⟨ref, ?_, named⟩
    unfold headRef
    rw [found]
    cases kind : reader.src.info <;> simpa only [ReaderSpines.selfRef, kind] using resolved

def sourceStrip (count : Nat) (expression : Ix.Expr) : Option (List Ix.Expr × Ix.Expr) :=
  match count, expression with
  | 0, expression => some ([], expression)
  | count + 1, .mdata _ body _ => sourceStrip (count + 1) body
  | count + 1, .forallE _ type body _ _ => (sourceStrip count body).map fun (types, residual) => (type :: types, residual)
  | _ + 1, _ => none
termination_by structural expression

theorem sourceStrip_zero (expression : Ix.Expr) : sourceStrip 0 expression = some ([], expression) := by
  cases expression <;> rfl

theorem related_strip (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target)
    (count : Nat) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) :
    ∃ binders residual, target.stripPis count = some (binders, residual) ∧
      List.Forall₂ (fun source binder => ExpressionState.Related names sourceParams params source binder.1) types binders ∧
      ExpressionState.Related names sourceParams params body residual := by
  induction count generalizing source target types body with
  | zero =>
    rw [sourceStrip_zero] at parsed
    cases Option.some.inj parsed
    exact ⟨[], target, rfl, .nil, related⟩
  | succ count ih =>
    induction related generalizing types body with
    | @all sourceType sourceBody targetType targetBody name info hash typeRel bodyRel _ _ =>
      cases tail : sourceStrip count sourceBody with
      | none => simp [sourceStrip, tail] at parsed
      | some result =>
        rcases result with ⟨rest, result⟩
        have same : (sourceType :: rest, result) = (types, body) := by simpa [sourceStrip, tail] using parsed
        cases same
        obtain ⟨binders, residual, stripped, meanings, bodyMeaning⟩ := ih sourceBody targetBody bodyRel rest body tail
        exact ⟨(targetType, ⟨.never⟩) :: binders, residual, by simp [Kernel.Expr.stripPis, stripped],
          .cons typeRel meanings, bodyMeaning⟩
    | mdata data hash bodyRel ihBody => exact ihBody types body parsed
    | _ => simp [sourceStrip] at parsed

def SourceRead (reader : ECx) (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (raw : Ixon.Expr) : Prop :=
  ∃ target, ExpressionState.Related names sourceParams params source target ∧ convExpr reader #[] raw = .ok target

/-- The source telescope alone determines the emitted unshared telescope;
every domain and residual body retains its original expression relation. -/
theorem source_stripAll (reader : ECx) (empty : reader.src.sharing = #[])
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (expression : Ixon.Expr) (meaning : SourceRead reader names sourceParams params source expression)
    (count : Nat) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) :
    ∃ rawTypes residual, stripAll reader.src count expression = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names sourceParams params) types rawTypes ∧
      SourceRead reader names sourceParams params body residual := by
  obtain ⟨target, related, read⟩ := meaning
  obtain ⟨binders, bodyValue, targetParsed, typeMeanings, bodyMeaning⟩ :=
    related_strip names sourceParams params source target related count types body parsed
  obtain ⟨rawTypes, residual, rawParsed, typeReads, bodyRead⟩ :=
    read_stripAll reader empty count expression target read binders bodyValue targetParsed
  refine ⟨rawTypes, residual, rawParsed, ?_, bodyValue, bodyMeaning, bodyRead⟩
  exact Sharing.Verify.CanonicalMeaning.pairs_match_right
    (fun source binder raw relation reading => ⟨binder.1, relation, reading.1⟩) typeMeanings typeReads

/-- The result-variable walk of an emitted recursor type follows the actual
source telescope and source application head, with no index-success premise. -/
theorem source_telescope_variable (reader : ECx) (empty : reader.src.sharing = #[])
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (expression : Ixon.Expr) (meaning : SourceRead reader names sourceParams params source expression)
    (count : Nat) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body))
    (enough : sourceAppDepth body < spineFuel) (index : Nat) (hash : Address)
    (head : sourceHead body = .bvar index hash) :
    ∃ rawTypes residual rawIndex,
      stripAll reader.src count expression = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names sourceParams params) types rawTypes ∧
      appHead reader.src spineFuel residual = .var rawIndex ∧ rawIndex.toNat = index := by
  obtain ⟨rawTypes, residual, rawParsed, typeMeanings, bodyValue, bodyMeaning, bodyRead⟩ :=
    source_stripAll reader empty names sourceParams params source expression meaning count types body parsed
  obtain ⟨rawIndex, headFound, sameIndex⟩ := source_variable_head reader empty spineFuel residual bodyValue bodyRead
    names sourceParams params body bodyMeaning enough index hash head
  exact ⟨rawTypes, residual, rawIndex, rawParsed, typeMeanings, headFound, sameIndex⟩

theorem related_constant_head (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Ix.Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target)
    (name : Name) (levels : Array Level) (hash : Address) (head : sourceHead source = .const name levels hash) :
    ∃ targetName targetLevels, target.getAppFn = .const targetName targetLevels ∧ names name targetName := by
  have headRelated := related_head names sourceParams params source target related
  rw [head] at headRelated
  generalize result : target.getAppFn = value at headRelated ⊢
  cases headRelated with
  | const _ _ _ mapped _ => exact ⟨_, _, rfl, mapped⟩

theorem source_constant_head (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (related : ExpressionState.Related names sourceParams params source target)
    (enough : sourceAppDepth source < spineFuel) (name : Name) (levels : Array Level) (hash : Address)
    (head : sourceHead source = .const name levels hash) :
    ∃ ref, headRef reader.cx.store owner reader.src expression = some ref ∧ names name (reader.cx.nameOf ref) := by
  obtain ⟨targetName, targetLevels, targetHead, mapped⟩ :=
    related_constant_head names sourceParams params source target related name levels hash head
  obtain ⟨ref, found, named⟩ := read_constant_head reader empty owner self expression target read
    (by rw [related_appDepth names sourceParams params source target related]; exact enough) targetName targetLevels targetHead
  exact ⟨ref, found, by simpa only [named] using mapped⟩

theorem recursor_sourceRead (reader : MemberReader) (table : reader.tbl = #[])
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : RecursorVal) (target : Ixon.Recursor)
    (related : RecursorEmission.Related reader names sourceParams params source target) :
    SourceRead reader.ecx names sourceParams params source.cnst.type target.typ := by
  obtain ⟨type, meaning, read⟩ := related.type
  exact ⟨type, meaning, by simpa only [MemberReader.read, table] using read⟩

def sourceDepth (source : RecursorVal) : Nat :=
  source.numParams + source.numMotives + source.numMinors + source.numIndices + 1

theorem recursor_depth (reader : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (source : RecursorVal) (target : Ixon.Recursor)
    (related : RecursorEmission.Related reader names sourceParams params source target) :
    ReaderSpines.depth target = sourceDepth source := by
  simp only [ReaderSpines.depth, sourceDepth, related.parameters, related.motives, related.minors, related.indices]

theorem recursor_telescope_variable (reader : MemberReader) (empty : reader.ecx.src.sharing = #[])
    (table : reader.tbl = #[]) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (source : RecursorVal) (target : Ixon.Recursor)
    (related : RecursorEmission.Related reader names sourceParams params source target)
    (types : List Ix.Expr) (body : Ix.Expr) (parsed : sourceStrip (sourceDepth source) source.cnst.type = some (types, body))
    (enough : sourceAppDepth body < spineFuel) (index : Nat) (hash : Address)
    (head : sourceHead body = .bvar index hash) :
    ∃ rawTypes residual rawIndex,
      stripAll reader.ecx.src (ReaderSpines.depth target) target.typ = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader.ecx names sourceParams params) types rawTypes ∧
      appHead reader.ecx.src spineFuel residual = .var rawIndex ∧ rawIndex.toNat = index := by
  rw [recursor_depth reader names sourceParams params source target related]
  exact source_telescope_variable reader.ecx empty names sourceParams params source.cnst.type target.typ
    (recursor_sourceRead reader table names sourceParams params source target related)
    (sourceDepth source) types body parsed enough index hash head

open Ix.CompileM Ix.CompileCert.HeadWriterFrame in
/-- Actual payload compilation supplies the unshared reading and exact
header depth. The result-variable walk is derived from source syntax. -/
theorem compiled_telescope_variable (reader : Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = source.cnst.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileRecursor source) context before = (.ok output, after))
    (types : List Ix.Expr) (body : Ix.Expr) (parsed : sourceStrip (sourceDepth source) source.cnst.type = some (types, body))
    (enough : sourceAppDepth body < spineFuel) (index : Nat) (hash : Address)
    (head : sourceHead body = .bvar index hash) :
    let member := ExpressionRead.blockReader reader base (paramOf params) self after
    ∃ rawTypes residual rawIndex,
      stripAll member.ecx.src (ReaderSpines.depth output.1) output.1.typ = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead member.ecx names source.cnst.levelParams.toList params) types rawTypes ∧
      appHead member.ecx.src spineFuel residual = .var rawIndex ∧ rawIndex.toNat = index := by
  have compiled := RecursorEmission.compile_correct reader base self names params bindings context source arity
    aligned external selfSound before after output ready ran
  apply recursor_telescope_variable _ _ _ names source.cnst.levelParams.toList params source output.1
    compiled.2.2.1 types body parsed enough index hash head
  · rfl
  · rfl

def NonForall : Ixon.Expr → Prop
  | .all .. => False
  | _ => True

def SourceNonForall : Ix.Expr → Prop
  | .forallE .. => False
  | .mdata _ body _ => SourceNonForall body
  | _ => True

theorem related_nonForall (reader : ECx) (expression : Ixon.Expr) (target : Kernel.Expr)
    (read : convExpr reader #[] expression = .ok target)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (related : ExpressionState.Related names sourceParams params source target)
    (last : SourceNonForall source) : NonForall expression := by
  have shape := read_outer reader expression target read
  induction related with
  | mdata _ _ _ ih => exact ih read last shape
  | all _ _ _ _ _ _ _ => exact False.elim last
  | _ => cases expression <;> simp only [Outer, NonForall] at shape ⊢

theorem full_of_strip (constant : Ixon.Constant) (empty : constant.sharing = #[])
    (count fuel : Nat) (enough : count < fuel) (expression : Ixon.Expr)
    (types : List Ixon.Expr) (body : Ixon.Expr) (last : NonForall body)
    (parsed : stripAll constant count expression = some (types, body)) :
    stripAllFull constant fuel expression = (types, body) := by
  induction count generalizing fuel expression types body with
  | zero =>
    cases Option.some.inj parsed
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [stripAllFull, ReaderSpines.unshare_empty constant empty]
      cases expression <;> simp only [NonForall] at last <;> rfl
  | succ count ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [stripAll, ReaderSpines.unshare_empty constant empty] at parsed
      cases expression with
      | all contract binder type tail =>
        cases tailParsed : stripAll constant count tail with
        | none => simp [tailParsed] at parsed
        | some result =>
          rcases result with ⟨rest, residual⟩
          have same : (type :: rest, residual) = (types, body) := by simpa [tailParsed] using parsed
          cases same
          have full := ih fuel (by omega) tail rest body last tailParsed
          simp only [stripAllFull, ReaderSpines.unshare_empty constant empty, full]
      | _ => cases parsed

/-- A complete source telescope determines the real fuel-bounded walk once
its binder count fits. Metadata at the source's terminal node is allowed. -/
theorem source_stripAllFull (reader : ECx) (empty : reader.src.sharing = #[])
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (expression : Ixon.Expr) (meaning : SourceRead reader names sourceParams params source expression)
    (count fuel : Nat) (enough : count < fuel) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) (last : SourceNonForall body) :
    ∃ rawTypes residual, stripAllFull reader.src fuel expression = (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names sourceParams params) types rawTypes ∧
      SourceRead reader names sourceParams params body residual := by
  obtain ⟨rawTypes, residual, rawParsed, typeMeanings, bodyValue, bodyMeaning, bodyRead⟩ :=
    source_stripAll reader empty names sourceParams params source expression meaning count types body parsed
  have final := related_nonForall reader residual bodyValue bodyRead names sourceParams params body bodyMeaning last
  exact ⟨rawTypes, residual, full_of_strip reader.src empty count fuel enough expression rawTypes residual final rawParsed,
    typeMeanings, bodyValue, bodyMeaning, bodyRead⟩

private theorem last_pair {relation : α → β → Prop} {left : List α} {right : List β}
    (pairs : List.Forall₂ relation left right) (last : α) (selected : left.getLast? = some last) :
    ∃ value, right.getLast? = some value ∧ relation last value := by
  induction pairs generalizing last with
  | nil => simp at selected
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases found : leftTail.getLast? with
    | none =>
      have empty : leftTail = [] := List.getLast?_eq_none_iff.mp found
      subst leftTail
      cases tail
      have same : leftHead = last := by simpa using selected
      subst last
      exact ⟨rightHead, rfl, head⟩
    | some value =>
      have same : value = last := by simpa [List.getLast?_cons, found] using selected
      subst last
      obtain ⟨target, targetLast, related⟩ := ih value found
      exact ⟨target, by simp [List.getLast?_cons, targetLast], related⟩

/-- The last source domain supplies the anonymous reference actually used
for a major premise or motive carrier. -/
theorem source_lastHead (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (types : List Ix.Expr) (rawTypes : List Ixon.Expr)
    (related : List.Forall₂ (SourceRead reader names sourceParams params) types rawTypes)
    (source : Ix.Expr) (last : types.getLast? = some source) (enough : sourceAppDepth source < spineFuel)
    (name : Name) (levels : Array Level) (hash : Address) (head : sourceHead source = .const name levels hash) :
    ∃ ref, ReaderSpines.lastHead reader.cx.store owner reader.src rawTypes = some ref ∧
      names name (reader.cx.nameOf ref) := by
  obtain ⟨raw, rawLast, target, meaning, read⟩ := last_pair related source last
  obtain ⟨ref, resolved, mapped⟩ := source_constant_head reader empty owner self raw target read
    names sourceParams params source meaning enough name levels hash head
  exact ⟨ref, by simp [ReaderSpines.lastHead, rawLast, resolved], mapped⟩

/-- Motive-carrier discovery follows its source telescope and last-domain
head, using the reader's actual fuel and address-table/self lookup. -/
theorem source_carrier (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (source : Ix.Expr) (expression : Ixon.Expr)
    (meaning : SourceRead reader names sourceParams params source expression)
    (count : Nat) (binderBound : count < spineFuel) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) (terminal : SourceNonForall body)
    (domain : Ix.Expr) (last : types.getLast? = some domain) (enough : sourceAppDepth domain < spineFuel)
    (name : Name) (levels : Array Level) (hash : Address) (head : sourceHead domain = .const name levels hash) :
    ∃ ref, ReaderSpines.carrier reader.cx.store owner reader.src expression = some ref ∧
      names name (reader.cx.nameOf ref) := by
  obtain ⟨rawTypes, residual, walked, domains, _⟩ := source_stripAllFull reader empty names sourceParams params
    source expression meaning count spineFuel binderBound types body parsed terminal
  obtain ⟨ref, found, mapped⟩ := source_lastHead reader empty owner self names sourceParams params types rawTypes
    domains domain last enough name levels hash head
  exact ⟨ref, by simpa only [ReaderSpines.carrier, walked] using found, mapped⟩

end Ix.CompileCert.ReaderSourceSpines
