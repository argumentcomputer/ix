import Ix.CompileCert.ReaderSpines
import Ix.CompileCert.Emission
import IxC.Kernel.Ixon.ReaderSpec

/-! # The reader's syntactic walks follow the source

The certified reader indexes a recursor by walking its raw (unconverted)
type: a binder telescope (`stripAll`, `stripAllFull`), the application head
of the body (`appHead`) and the head references of the motives' and the
major premise's domains (`headRef`). On an unshared record these walks agree
with the converted reading (`convExpr`): a successful reading keeps the
outer constructor and supplies the children's readings (`read_outer`), so a
`∀`-telescope, an application head, a bound variable or a constant head of
the reading is present in the raw syntax (`read_stripAll`, `read_appHead`,
`read_constant_head`). Composed with the source relation
(`ExpressionState.Related`, a reading up to keys and level values), the
walks follow the source expression: a source telescope determines the raw
one with every domain still related (`source_stripAll`,
`source_stripAllFull`), a source bound-variable head gives the raw variable
head (`source_variable_head`, `source_telescope_variable`), and a source
constant head gives the raw head reference, whose key is related to the
source name (`source_constant_head`, `source_carrier`). A contract frame
(`Related.contract`) changes only a binder's metadata, which the walks do
not read.

Keys are read through `Ctx.keyAt`/`Ctx.memberKey` (which can decline), so a
head reference's key is the key of the address it resolves from, or its
member key (`HeadKey`). `ReaderSourceSpines`, adapted to keys,
binder contracts and the contract frame; the walks are those of the donor's
reader, unchanged. -/

namespace Ix.CompileCert.ReaderSourceSpines

open Ix.Kernel (Mode)
open Ix.Kernel.Reader
open Ix.CompileCert.ExpressionState (Related withContract)

variable {md : Mode}

/-! ## The outer constructor of a reading -/

/-- What a successful unshared reading keeps of the raw expression: its
outer constructor, the children's readings on spines and telescopes, and
the head key. -/
def Outer (reader : ECx md) : Ixon.Expr → CExpr md → Prop
  | .var index, .bvar target => index.toNat = target
  | .all _ _ type body, .forallE targetType targetBody _ =>
    convExpr reader #[] type = .ok targetType ∧ convExpr reader #[] body = .ok targetBody
  | .app function argument, .app targetFunction targetArgument =>
    convExpr reader #[] function = .ok targetFunction ∧ convExpr reader #[] argument = .ok targetArgument
  | .ref index _, .const key _ => reader.keyAt index = .ok key
  | .recur index _, .const key _ => ∃ member, reader.self index.toNat = some member ∧ member = .ok key
  | .sort _, .sort _ | .lam .., .lam .. | .letE .., .letE .. | .prj .., .proj .. => True
  | .nat _, .lit (.natVal _) | .str _, .lit (.strVal _) => True
  | _, _ => False

theorem read_outer (reader : ECx md) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target) : Outer reader expression target := by
  cases expression with
  | var index =>
    simp only [convExpr, Ix.Kernel.Expr.mkBvar_eq, pure, Except.pure, Except.ok.injEq] at read
    cases read
    rfl
  | sort index =>
    simp only [convExpr] at read
    obtain ⟨level, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    cases Except.ok.inj returned
    trivial
  | ref index levels =>
    simp only [convExpr] at read
    obtain ⟨key, found, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨universes, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact found
  | recur index levels =>
    simp only [convExpr] at read
    cases found : reader.self index.toNat with
    | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at read
    | some member =>
      simp only [found] at read
      obtain ⟨key, keyRead, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
      obtain ⟨universes, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
      cases Except.ok.inj returned
      exact ⟨member, found, keyRead⟩
  | prj index field value =>
    simp only [convExpr] at read
    obtain ⟨key, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨value, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | str index =>
    simp only [convExpr] at read
    obtain ⟨bytes, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    cases found : String.fromUTF8? bytes with
    | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at rest
    | some value =>
      simp only [found] at rest
      cases Except.ok.inj rest
      trivial
  | nat index =>
    simp only [convExpr] at read
    obtain ⟨bytes, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    cases Except.ok.inj returned
    trivial
  | app function argument =>
    simp only [convExpr] at read
    obtain ⟨targetFunction, first, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetArgument, second, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact ⟨first, second⟩
  | lam contract type body =>
    simp only [convExpr] at read
    obtain ⟨targetType, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetBody, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | all contract result type body =>
    simp only [convExpr] at read
    obtain ⟨targetType, first, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetBody, second, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    exact ⟨first, second⟩
  | letE contract type value body =>
    simp only [convExpr] at read
    obtain ⟨targetType, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok read
    obtain ⟨targetValue, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    obtain ⟨targetBody, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
    cases Except.ok.inj returned
    trivial
  | share index => simp [convExpr, malformed, throw, throwThe, MonadExceptOf.throw] at read

theorem read_forall (reader : ECx md) (expression : Ixon.Expr) (type body : CExpr md)
    (binder : Ix.Kernel.BinderMeta) (read : convExpr reader #[] expression = .ok (.forallE type body binder)) :
    ∃ contract result rawType rawBody, expression = .all contract result rawType rawBody ∧
      convExpr reader #[] rawType = .ok type ∧ convExpr reader #[] rawBody = .ok body := by
  have shape := read_outer reader expression _ read
  cases expression <;> simp only [Outer] at shape
  exact ⟨_, _, _, _, rfl, shape⟩

theorem read_bvar (reader : ECx md) (expression : Ixon.Expr) (index : Nat)
    (read : convExpr reader #[] expression = .ok (.bvar index)) :
    ∃ raw, expression = .var raw ∧ raw.toNat = index := by
  have shape := read_outer reader expression _ read
  cases expression <;> simp only [Outer] at shape
  exact ⟨_, rfl, shape⟩

/-! ## Telescopes -/

/-- The domains and body of a `count`-binder `∀`-telescope (`Expr.stripPis`
without the binders' metadata). -/
def piTypes (count : Nat) (target : CExpr md) : Option (List (CExpr md) × CExpr md) :=
  (Ix.Kernel.Expr.stripPis count target).map fun result => (result.1.map (·.1), result.2)

theorem piTypes_zero (target : CExpr md) : piTypes 0 target = some ([], target) := rfl

theorem piTypes_forall (count : Nat) (type body : CExpr md) (binder : Ix.Kernel.BinderMeta) :
    piTypes (count + 1) (.forallE type body binder) =
      (piTypes count body).map fun result => (type :: result.1, result.2) := by
  simp only [piTypes, Ix.Kernel.Expr.stripPis]
  rcases Ix.Kernel.Expr.stripPis count body with _ | ⟨binders, residual⟩ <;> rfl

/-- A telescope of the reading is present in the unshared raw syntax, with
corresponding domain and body readings. -/
theorem read_stripAll (reader : ECx md) (empty : reader.src.sharing = #[]) (count : Nat)
    (expression : Ixon.Expr) (target : CExpr md) (read : convExpr reader #[] expression = .ok target)
    (types : List (CExpr md)) (body : CExpr md) (parsed : piTypes count target = some (types, body)) :
    ∃ rawTypes residual, stripAll reader.src count expression = some (rawTypes, residual) ∧
      List.Forall₂ (fun raw type => convExpr reader #[] raw = .ok type) rawTypes types ∧
      convExpr reader #[] residual = .ok body := by
  induction count generalizing expression target types body with
  | zero =>
    rw [piTypes_zero] at parsed
    cases Option.some.inj parsed
    exact ⟨[], _, rfl, .nil, read⟩
  | succ count ih =>
    cases target with
    | forallE type tail binder =>
      obtain ⟨contract, result, rawType, rawBody, rawEq, typeRead, bodyRead⟩ :=
        read_forall reader expression type tail binder read
      subst rawEq
      rw [piTypes_forall] at parsed
      cases tailParsed : piTypes count tail with
      | none => rw [tailParsed] at parsed; cases parsed
      | some value =>
        rcases value with ⟨rest, residualTarget⟩
        rw [tailParsed] at parsed
        obtain ⟨typesEq, bodyEq⟩ := Prod.mk.inj (Option.some.inj parsed)
        subst typesEq
        subst bodyEq
        obtain ⟨rawTypes, residual, stripped, meanings, residualRead⟩ :=
          ih rawBody tail bodyRead rest residualTarget tailParsed
        exact ⟨rawType :: rawTypes, residual,
          by simp [stripAll, ReaderSpines.unshare_empty reader.src empty, stripped], .cons typeRead meanings,
          residualRead⟩
    | _ => simp [piTypes, Ix.Kernel.Expr.stripPis] at parsed

/-! ## Application heads -/

def kernelAppDepth : CExpr md → Nat
  | .app function _ => kernelAppDepth function + 1
  | _ => 0

theorem read_appDepth (reader : ECx md) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target) :
    ReaderSpines.appDepth expression = kernelAppDepth target := by
  induction expression generalizing target with
  | app function argument ihf _ =>
    have shape := read_outer reader (.app function argument) target read
    cases target <;> simp only [Outer] at shape
    exact congrArg (· + 1) (ihf _ shape.1)
  | _ =>
    have shape := read_outer reader _ target read
    cases target <;> simp only [Outer] at shape <;> rfl

/-- With enough application fuel, the unshared head walk reads to the head
of the reading. -/
theorem read_appHead (reader : ECx md) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : CExpr md) (read : convExpr reader #[] expression = .ok target)
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
      have head := ih function _ shape.1 (by omega)
      simp only [appHead, ReaderSpines.unshare_empty reader.src empty]
      exact head
    | _ =>
      cases target <;> simp only [Outer] at shape
      all_goals (simp only [appHead, ReaderSpines.unshare_empty reader.src empty]; exact read)

theorem read_variable_head (reader : ECx md) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : CExpr md) (read : convExpr reader #[] expression = .ok target)
    (enough : kernelAppDepth target < fuel) (index : Nat) (head : target.getAppFn = .bvar index) :
    ∃ raw, appHead reader.src fuel expression = .var raw ∧ raw.toNat = index := by
  have headRead := read_appHead reader empty fuel expression target read enough
  rw [head] at headRead
  exact read_bvar reader _ index headRead

/-! ## The source side -/

def sourceAppDepth : Ix.Expr → Nat
  | .app function _ _ => sourceAppDepth function + 1
  | .mdata _ body _ => sourceAppDepth body
  | _ => 0

def sourceHead : Ix.Expr → Ix.Expr
  | .app function _ _ => sourceHead function
  | .mdata _ body _ => sourceHead body
  | expression => expression

/-- A contract frame only lowers a binder, keeping its children. -/
theorem withContract_shape {c : Ix.SemanticContract.Contract} {source : Ix.Expr} {target result : CExpr md}
    (lowered : withContract c source target = some result) :
    (∃ name type body info hash, source = .lam name type body info hash) ∨
      (∃ name type body info hash, source = .forallE name type body info hash) ∨
      (∃ name type value body nonDep hash, source = .letE name type value body nonDep hash) := by
  unfold withContract at lowered
  split at lowered
  · exact .inl ⟨_, _, _, _, _, rfl⟩
  · exact .inr (.inl ⟨_, _, _, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, _, _, _, _, rfl⟩)
  · cases lowered

theorem withContract_depth {c : Ix.SemanticContract.Contract} {source : Ix.Expr} {target result : CExpr md}
    (lowered : withContract c source target = some result) : kernelAppDepth result = kernelAppDepth target := by
  unfold withContract at lowered
  split at lowered <;> cases lowered <;> rfl

theorem withContract_head {c : Ix.SemanticContract.Contract} {source : Ix.Expr} {target result : CExpr md}
    (lowered : withContract c source target = some result) :
    sourceHead source = source ∧ (∀ index hash, source ≠ .bvar index hash) ∧
      ∀ name levels hash, source ≠ .const name levels hash := by
  rcases withContract_shape lowered with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
    exact ⟨rfl, fun _ _ => Ix.Expr.noConfusion, fun _ _ _ => Ix.Expr.noConfusion⟩

theorem withContract_piTypes {c : Ix.SemanticContract.Contract} {source : Ix.Expr} {target result : CExpr md}
    (lowered : withContract c source target = some result) (count : Nat) :
    piTypes (count + 1) result = piTypes (count + 1) target := by
  unfold withContract at lowered
  split at lowered <;> cases lowered
  · rfl
  · rw [piTypes_forall, piTypes_forall]
  · rfl

theorem related_appDepth {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
    {source : Ix.Expr} {target : CExpr md} (related : Related names levels source target) :
    kernelAppDepth target = sourceAppDepth source := by
  induction related with
  | app _ _ _ ihf _ => exact congrArg (· + 1) ihf
  | mdata _ _ _ _ ih => exact ih
  | contract _ _ _ _ _ _ lowered ih => exact (withContract_depth lowered).trans ih
  | bvar => rw [Ix.Kernel.Expr.mkBvar_eq]; rfl
  | _ => rfl

/-- The raw spine's depth is the source spine's (metadata erased). -/
theorem source_appDepth (reader : ECx md) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target)
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
    (related : Related names levels source target) :
    ReaderSpines.appDepth expression = sourceAppDepth source :=
  (read_appDepth reader expression target read).trans (related_appDepth related)

theorem related_variable_head {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
    {source : Ix.Expr} {target : CExpr md} (related : Related names levels source target)
    (index : Nat) (hash : Address) (head : sourceHead source = .bvar index hash) :
    target.getAppFn = .bvar index := by
  induction related with
  | bvar index' hash' =>
    injection head with indexEq
    rw [Ix.Kernel.Expr.mkBvar_eq, indexEq]
    rfl
  | app _ _ _ ihf _ => exact ihf head
  | mdata _ _ _ _ ih => exact ih head
  | @contract inner _ _ _ _ _ _ _ _ lowered _ =>
    have shape := withContract_head lowered
    have reduced : sourceHead inner = _ := head
    rw [shape.1] at reduced
    exact absurd reduced (shape.2.1 index hash)
  | _ => cases head

/-- A source bound-variable head is the raw variable head, with the same
index. -/
theorem source_variable_head (reader : ECx md) (empty : reader.src.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (target : CExpr md) (read : convExpr reader #[] expression = .ok target)
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
    (related : Related names levels source target) (enough : sourceAppDepth source < fuel) (index : Nat)
    (hash : Address) (head : sourceHead source = .bvar index hash) :
    ∃ raw, appHead reader.src fuel expression = .var raw ∧ raw.toNat = index :=
  read_variable_head reader empty fuel expression target read (by rw [related_appDepth related]; exact enough) index
    (related_variable_head related index hash head)

theorem related_constant_head {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr} {target : CExpr md}
    (related : Related names levels source target) (name : Ix.Name) (sourceLevels : Array Ix.Level)
    (hash : Address) (head : sourceHead source = .const name sourceLevels hash) :
    ∃ key targetLevels, target.getAppFn = .const key targetLevels ∧ names name key := by
  induction related with
  | const _ _ _ mapped _ =>
    injection head with nameEq
    exact ⟨_, _, rfl, nameEq ▸ mapped⟩
  | app _ _ _ ihf _ => exact ihf head
  | mdata _ _ _ _ ih => exact ih head
  | @contract inner _ _ _ _ _ _ _ _ lowered _ =>
    have shape := withContract_head lowered
    have reduced : sourceHead inner = _ := head
    rw [shape.1] at reduced
    exact absurd reduced (shape.2.2 name sourceLevels hash)
  | _ => cases head

/-! ## Head references and their keys -/

/-- The key of a head reference: the key of the address it resolves from,
or its member key (a self reference). -/
def HeadKey (cx : Ctx md) (ref : Ix.Kernel.ConstRef Address) (key : CName md) : Prop :=
  (∃ address, resolve cx.store address = some ref ∧ keyOfAddress cx.store cx.roles address = some key) ∨
    cx.memberKey ref = .ok key

/-- The reader's self slots are the record's own members. -/
def SelfAligned (reader : ECx md) (owner : Address) : Prop :=
  ∀ (index : UInt64) member, reader.self index.toNat = some member →
    ∃ ref, ReaderSpines.selfRef reader.src owner index = some ref ∧ member = reader.cx.memberKey ref

/-- A constant head of the reading is the raw head reference, with the
head's key. -/
theorem read_constant_head (reader : ECx md) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target) (enough : kernelAppDepth target < spineFuel)
    (key : CName md) (levels : List Ix.Kernel.Level) (head : target.getAppFn = .const key levels) :
    ∃ ref, headRef reader.cx.store owner reader.src expression = some ref ∧ HeadKey reader.cx ref key := by
  have headRead := read_appHead reader empty spineFuel expression target read enough
  rw [head] at headRead
  have shape := read_outer reader (appHead reader.src spineFuel expression) _ headRead
  cases found : appHead reader.src spineFuel expression <;> simp only [found, Outer] at shape
  case ref index universes =>
    unfold ECx.keyAt at shape
    cases stored : reader.src.refs[index.toNat]? with
    | none => simp [stored, malformed, throw, throwThe, MonadExceptOf.throw] at shape
    | some address =>
      simp only [stored] at shape
      have keyed := Ctx.keyAt_eq_ok.mp shape
      cases resolved : resolve reader.cx.store address with
      | none => simp [keyOfAddress, resolved] at keyed
      | some ref =>
        exact ⟨ref, by simp [headRef, found, stored, resolved], Or.inl ⟨address, resolved, keyed⟩⟩
  case recur index universes =>
    obtain ⟨member, memberFound, memberKey⟩ := shape
    obtain ⟨ref, resolved, named⟩ := self index member memberFound
    refine ⟨ref, ?_, Or.inr (named.symm.trans memberKey)⟩
    simp only [headRef, found]
    exact resolved

/-- A source constant head is the raw head reference, whose key the source
name is related to. -/
theorem source_constant_head (reader : ECx md) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target)
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
    (related : Related names levels source target) (enough : sourceAppDepth source < spineFuel)
    (name : Ix.Name) (sourceLevels : Array Ix.Level) (hash : Address)
    (head : sourceHead source = .const name sourceLevels hash) :
    ∃ ref key, headRef reader.cx.store owner reader.src expression = some ref ∧ HeadKey reader.cx ref key ∧
      names name key := by
  obtain ⟨key, targetLevels, targetHead, mapped⟩ := related_constant_head related name sourceLevels hash head
  obtain ⟨ref, found, keyed⟩ := read_constant_head reader empty owner self expression target read
    (by rw [related_appDepth related]; exact enough) key targetLevels targetHead
  exact ⟨ref, key, found, keyed, mapped⟩

/-! ## Source telescopes -/

/-- The domains and body of a `count`-binder source telescope, through
metadata. -/
def sourceStrip (count : Nat) (expression : Ix.Expr) : Option (List Ix.Expr × Ix.Expr) :=
  match count, expression with
  | 0, expression => some ([], expression)
  | count + 1, .mdata _ body _ => sourceStrip (count + 1) body
  | count + 1, .forallE _ type body _ _ =>
    (sourceStrip count body).map fun (types, residual) => (type :: types, residual)
  | _ + 1, _ => none
termination_by structural expression

theorem sourceStrip_zero (expression : Ix.Expr) : sourceStrip 0 expression = some ([], expression) := by
  cases expression <;> rfl

theorem related_strip {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
    (count : Nat) {source : Ix.Expr} {target : CExpr md} (related : Related names levels source target)
    (types : List Ix.Expr) (body : Ix.Expr) (parsed : sourceStrip count source = some (types, body)) :
    ∃ targetTypes residual, piTypes count target = some (targetTypes, residual) ∧
      List.Forall₂ (Related names levels) types targetTypes ∧ Related names levels body residual := by
  induction count generalizing source target types body with
  | zero =>
    rw [sourceStrip_zero] at parsed
    obtain ⟨typesEq, bodyEq⟩ := Prod.mk.inj (Option.some.inj parsed)
    subst typesEq
    subst bodyEq
    exact ⟨[], _, piTypes_zero _, .nil, related⟩
  | succ count ih =>
    induction related generalizing types body with
    | @all sourceType sourceBody targetType targetBody _ _ _ typeRel bodyRel _ _ =>
      cases tail : sourceStrip count sourceBody with
      | none => simp [sourceStrip, tail] at parsed
      | some result =>
        rcases result with ⟨rest, residualSource⟩
        have same : (sourceType :: rest, residualSource) = (types, body) := by
          simpa [sourceStrip, tail] using parsed
        obtain ⟨typesEq, bodyEq⟩ := Prod.mk.inj same
        subst typesEq
        subst bodyEq
        obtain ⟨targetTypes, residual, stripped, meanings, bodyMeaning⟩ :=
          ih (source := sourceBody) (target := targetBody) bodyRel rest residualSource tail
        refine ⟨targetType :: targetTypes, residual, ?_, .cons typeRel meanings, bodyMeaning⟩
        simp [piTypes_forall, stripped]
    | mdata _ _ _ _ ihBody => exact ihBody types body (by simpa [sourceStrip] using parsed)
    | contract _ _ _ _ _ _ lowered ihBody =>
      obtain ⟨targetTypes, residual, stripped, meanings, bodyMeaning⟩ :=
        ihBody types body (by simpa [sourceStrip] using parsed)
      exact ⟨targetTypes, residual, (withContract_piTypes lowered count).trans stripped, meanings, bodyMeaning⟩
    | _ => simp [sourceStrip] at parsed

/-- A source expression and a raw expression whose unshared reading is
related to it. -/
abbrev SourceRead (reader : ECx md) (names : Ix.Name → CName md → Prop)
    (levels : Ix.Level → Ix.Kernel.Level → Prop) (source : Ix.Expr) (raw : Ixon.Expr) : Prop :=
  ∃ target, Related names levels source target ∧ convExpr reader #[] raw = .ok target

theorem pairs_match {α β γ : Type} {left : List α} {middle : List β} {right : List γ}
    {first : α → β → Prop} {second : γ → β → Prop} {result : α → γ → Prop}
    (combine : ∀ a b c, first a b → second c b → result a c)
    (firsts : List.Forall₂ first left middle) (seconds : List.Forall₂ second right middle) :
    List.Forall₂ result left right := by
  induction firsts generalizing right with
  | nil => cases seconds; exact .nil
  | cons head _ ih =>
    cases seconds with
    | cons secondHead secondTail => exact .cons (combine _ _ _ head secondHead) (ih secondTail)

/-- **The source telescope determines the raw unshared telescope**; every
domain and the residual body keep their source relation. -/
theorem source_stripAll (reader : ECx md) (empty : reader.src.sharing = #[])
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (source : Ix.Expr)
    (expression : Ixon.Expr) (meaning : SourceRead reader names levels source expression)
    (count : Nat) (types : List Ix.Expr) (body : Ix.Expr) (parsed : sourceStrip count source = some (types, body)) :
    ∃ rawTypes residual, stripAll reader.src count expression = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names levels) types rawTypes ∧
      SourceRead reader names levels body residual := by
  obtain ⟨target, related, read⟩ := meaning
  obtain ⟨targetTypes, bodyValue, targetParsed, typeMeanings, bodyMeaning⟩ :=
    related_strip count related types body parsed
  obtain ⟨rawTypes, residual, rawParsed, typeReads, bodyRead⟩ :=
    read_stripAll reader empty count expression target read targetTypes bodyValue targetParsed
  exact ⟨rawTypes, residual, rawParsed,
    pairs_match (fun _ type _ relation reading => ⟨type, relation, reading⟩) typeMeanings typeReads,
    bodyValue, bodyMeaning, bodyRead⟩

/-- **The result-variable walk of a raw telescope follows the source**: the
source telescope and its body's bound-variable head give the raw ones. -/
theorem source_telescope_variable (reader : ECx md) (empty : reader.src.sharing = #[])
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (source : Ix.Expr)
    (expression : Ixon.Expr) (meaning : SourceRead reader names levels source expression)
    (count : Nat) (types : List Ix.Expr) (body : Ix.Expr) (parsed : sourceStrip count source = some (types, body))
    (enough : sourceAppDepth body < spineFuel) (index : Nat) (hash : Address)
    (head : sourceHead body = .bvar index hash) :
    ∃ rawTypes residual rawIndex,
      stripAll reader.src count expression = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names levels) types rawTypes ∧
      appHead reader.src spineFuel residual = .var rawIndex ∧ rawIndex.toNat = index := by
  obtain ⟨rawTypes, residual, rawParsed, typeMeanings, bodyValue, bodyMeaning, bodyRead⟩ :=
    source_stripAll reader empty source expression meaning count types body parsed
  obtain ⟨rawIndex, headFound, sameIndex⟩ := source_variable_head reader empty spineFuel residual bodyValue bodyRead
    bodyMeaning enough index hash head
  exact ⟨rawTypes, residual, rawIndex, rawParsed, typeMeanings, headFound, sameIndex⟩

/-! ## Full telescopes and carriers -/

def NonForall : Ixon.Expr → Prop
  | .all .. => False
  | _ => True

def SourceNonForall : Ix.Expr → Prop
  | .forallE .. => False
  | .mdata _ body _ => SourceNonForall body
  | _ => True

def KernelNonForall : CExpr md → Prop
  | .forallE .. => False
  | _ => True

theorem withContract_nonForall {c : Ix.SemanticContract.Contract} {source : Ix.Expr} {target result : CExpr md}
    (lowered : withContract c source target = some result) (last : SourceNonForall source) :
    KernelNonForall result := by
  unfold withContract at lowered
  split at lowered <;> cases lowered
  · trivial
  · exact False.elim last
  · trivial

theorem related_kernelNonForall {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr} {target : CExpr md}
    (related : Related names levels source target) (last : SourceNonForall source) : KernelNonForall target := by
  induction related with
  | all => exact False.elim last
  | mdata _ _ _ _ ih => exact ih last
  | contract _ _ _ _ _ _ lowered _ => exact withContract_nonForall lowered last
  | bvar => rw [Ix.Kernel.Expr.mkBvar_eq]; trivial
  | _ => trivial

theorem related_nonForall (reader : ECx md) (expression : Ixon.Expr) (target : CExpr md)
    (read : convExpr reader #[] expression = .ok target)
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
    (related : Related names levels source target) (last : SourceNonForall source) : NonForall expression := by
  have kernel := related_kernelNonForall related last
  have shape := read_outer reader expression target read
  cases expression with
  | all =>
    cases target <;> simp only [Outer] at shape
    exact False.elim kernel
  | _ => trivial

theorem full_of_nonForall (constant : Ixon.Constant) (empty : constant.sharing = #[]) (fuel : Nat)
    (expression : Ixon.Expr) (last : NonForall expression) :
    stripAllFull constant (fuel + 1) expression = ([], expression) := by
  cases expression with
  | all => exact False.elim last
  | _ => simp only [stripAllFull, ReaderSpines.unshare_empty constant empty]

theorem full_of_strip (constant : Ixon.Constant) (empty : constant.sharing = #[])
    (count fuel : Nat) (enough : count < fuel) (expression : Ixon.Expr)
    (types : List Ixon.Expr) (body : Ixon.Expr) (last : NonForall body)
    (parsed : stripAll constant count expression = some (types, body)) :
    stripAllFull constant fuel expression = (types, body) := by
  induction count generalizing fuel expression types body with
  | zero =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    simp only [stripAll, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨typesEq, bodyEq⟩ := parsed
    subst typesEq
    subst bodyEq
    exact full_of_nonForall constant empty fuel _ last
  | succ count ih =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    cases expression with
    | all contract binder type tail =>
      cases tailParsed : stripAll constant count tail with
      | none => simp [stripAll, ReaderSpines.unshare_empty constant empty, tailParsed] at parsed
      | some result =>
        rcases result with ⟨rest, residual⟩
        have same : (type :: rest, residual) = (types, body) := by
          simpa [stripAll, ReaderSpines.unshare_empty constant empty, tailParsed] using parsed
        obtain ⟨typesEq, bodyEq⟩ := Prod.mk.inj same
        subst typesEq
        subst bodyEq
        have full := ih fuel (by omega) tail rest residual last tailParsed
        simp only [stripAllFull, ReaderSpines.unshare_empty constant empty, full]
    | _ => simp [stripAll, ReaderSpines.unshare_empty constant empty] at parsed

/-- **A complete source telescope determines the reader's fuel-bounded
walk** once its binder count fits; metadata at the source's terminal node
is allowed. -/
theorem source_stripAllFull (reader : ECx md) (empty : reader.src.sharing = #[])
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (source : Ix.Expr)
    (expression : Ixon.Expr) (meaning : SourceRead reader names levels source expression)
    (count fuel : Nat) (enough : count < fuel) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) (last : SourceNonForall body) :
    ∃ rawTypes residual, stripAllFull reader.src fuel expression = (rawTypes, residual) ∧
      List.Forall₂ (SourceRead reader names levels) types rawTypes ∧
      SourceRead reader names levels body residual := by
  obtain ⟨rawTypes, residual, rawParsed, typeMeanings, bodyValue, bodyMeaning, bodyRead⟩ :=
    source_stripAll reader empty source expression meaning count types body parsed
  have final := related_nonForall reader residual bodyValue bodyRead bodyMeaning last
  exact ⟨rawTypes, residual, full_of_strip reader.src empty count fuel enough expression rawTypes residual final
    rawParsed, typeMeanings, bodyValue, bodyMeaning, bodyRead⟩

theorem last_pair {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (pairs : List.Forall₂ relation left right) (last : α) (selected : left.getLast? = some last) :
    ∃ value, right.getLast? = some value ∧ relation last value := by
  induction pairs generalizing last with
  | nil => simp at selected
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases found : leftTail.getLast? with
    | none =>
      have emptyTail : leftTail = [] := List.getLast?_eq_none_iff.mp found
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

/-- The last source domain's constant head is the raw last domain's head
reference, whose key the source name is related to. -/
theorem source_lastHead (reader : ECx md) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} (types : List Ix.Expr) (rawTypes : List Ixon.Expr)
    (related : List.Forall₂ (SourceRead reader names levels) types rawTypes)
    (source : Ix.Expr) (last : types.getLast? = some source) (enough : sourceAppDepth source < spineFuel)
    (name : Ix.Name) (sourceLevels : Array Ix.Level) (hash : Address)
    (head : sourceHead source = .const name sourceLevels hash) :
    ∃ ref key, ReaderSpines.lastHead reader.cx.store owner reader.src rawTypes = some ref ∧
      HeadKey reader.cx ref key ∧ names name key := by
  obtain ⟨raw, rawLast, target, meaning, read⟩ := last_pair related source last
  obtain ⟨ref, key, resolved, keyed, mapped⟩ := source_constant_head reader empty owner self raw target read
    meaning enough name sourceLevels hash head
  exact ⟨ref, key, by simp [ReaderSpines.lastHead, rawLast, resolved], keyed, mapped⟩

/-- **A motive carrier follows its source**: the source telescope of a
domain and its last domain's constant head give the reader's carrier
reference, whose key the source name is related to. -/
theorem source_carrier (reader : ECx md) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : SelfAligned reader owner) {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} (source : Ix.Expr) (expression : Ixon.Expr)
    (meaning : SourceRead reader names levels source expression)
    (count : Nat) (binderBound : count < spineFuel) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip count source = some (types, body)) (terminal : SourceNonForall body)
    (domain : Ix.Expr) (last : types.getLast? = some domain) (enough : sourceAppDepth domain < spineFuel)
    (name : Ix.Name) (sourceLevels : Array Ix.Level) (hash : Address)
    (head : sourceHead domain = .const name sourceLevels hash) :
    ∃ ref key, ReaderSpines.carrier reader.cx.store owner reader.src expression = some ref ∧
      HeadKey reader.cx ref key ∧ names name key := by
  obtain ⟨rawTypes, residual, walked, domains, _⟩ := source_stripAllFull reader empty source expression meaning
    count spineFuel binderBound types body parsed terminal
  obtain ⟨ref, key, found, keyed, mapped⟩ := source_lastHead reader empty owner self types rawTypes domains domain
    last enough name sourceLevels hash head
  exact ⟨ref, key, by simpa only [ReaderSpines.carrier, walked] using found, keyed, mapped⟩

/-! ## Compiled recursors -/

/-- The binder depth of a source recursor's analysis telescope. -/
def sourceDepth (source : RecursorVal) : Nat :=
  source.numParams + source.numMotives + source.numMinors + source.numIndices + 1

/-- The compiled recursor's header counts are the source's. -/
theorem recursor_counts (source : RecursorVal) :
    Emission.Yields (Ix.CompileM.compileRecursor source) (fun output =>
      output.1.params.toNat = source.numParams ∧ output.1.indices.toNat = source.numIndices ∧
      output.1.motives.toNat = source.numMotives ∧ output.1.minors.toNat = source.numMinors) := by
  unfold Ix.CompileM.compileRecursor
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Emission.Yields.bindAny _ fun rules => ?_
  intro context before output after ran
  obtain ⟨_, params, indices, motives, minors, _⟩ :=
    Emission.recursorHeader source typeExpr typeRoot rules context before output after ran
  exact ⟨params, indices, motives, minors⟩

/-- **The compiled recursor's result-variable walk follows its source**: in
the in-flight (unshared) reader, the emitted recursor type's telescope of
the analysis depth is the source's, domain by domain, and its body's
variable head is the source body's. -/
theorem compiled_telescope_variable (cx : Ctx md) (param : Nat → Ix.Kernel.LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → Ix.Kernel.LevelParam) (bindings : ExpressionState.Bindings)
    (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names) (source : RecursorVal)
    (scope : ExpressionState.ConstsSatisfy (ExpressionState.SelfName context.2 self names) source.cnst.type)
    (ruleScope : ∀ rule ∈ source.rules.toList,
      ExpressionState.ConstsSatisfy (ExpressionState.SelfName context.2 self names) rule.rhs)
    {before after : Ix.CompileM.BlockState} {output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr}
    (good : ExpressionState.Good cx param self
      (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
      bindings before)
    (ran : rawRun (Ix.CompileM.compileRecursor source) context before = (.ok output, after))
    (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : sourceStrip (sourceDepth source) source.cnst.type = some (types, body))
    (enough : sourceAppDepth body < spineFuel) (index : Nat) (hash : Address)
    (head : sourceHead body = .bvar index hash) :
    ∃ rawTypes residual rawIndex,
      stripAll (ExpressionRead.blockReader cx param self after).ecx.src (ReaderSpines.depth output.1)
        output.1.typ = some (rawTypes, residual) ∧
      List.Forall₂ (SourceRead (ExpressionRead.blockReader cx param self after).ecx names
        (UniversePipeline.LevelMeaning source.cnst.levelParams.toList σ param)) types rawTypes ∧
      appHead (ExpressionRead.blockReader cx param self after).ecx.src spineFuel residual = .var rawIndex ∧
      rawIndex.toNat = index := by
  obtain ⟨_, _, _, _, _, roots⟩ := Emission.recursor_correct cx param self names σ bindings context
    aligned external source scope ruleScope good ran
  obtain ⟨params, indices, motives, minors⟩ := recursor_counts source context before output after ran
  have depthEq : ReaderSpines.depth output.1 = sourceDepth source := by
    simp only [ReaderSpines.depth, sourceDepth, params, indices, motives, minors]
  rw [depthEq]
  cases roots with
  | cons typeRead _ =>
    obtain ⟨type, typeRel, read⟩ := typeRead
    exact source_telescope_variable (ExpressionRead.blockReader cx param self after).ecx rfl
      (names := names) (levels := UniversePipeline.LevelMeaning source.cnst.levelParams.toList σ param)
      source.cnst.type output.1.typ
      ⟨type, typeRel, by simpa only [MemberReader.read, ExpressionRead.blockReader_tbl] using read⟩
      (sourceDepth source) types body parsed enough index hash head

end Ix.CompileCert.ReaderSourceSpines
