import Ix.CompileCert.Opt.FreshOpeningSupport
import Ix.CompileCert.Canon.Loop

/-!
F-1: the actual O11a field array and cross-target opening. The proof-only
factorization retains the source preparation, every callback and refusal, the
four loop-state fields, and the final expression. A structural field read is
proved observationally redundant from the empty-array initialization and the
actual allocator's output, not assumed at a final caller.

This additive leaf is UNCOMPILED. Its support result is relative to the actual
input minor; the source-preparation supply-growth, instance conversion,
abstraction and general O2/O11a faithfulness/totality obligations remain open.
-/

namespace Ix.CompileCert.Opt.O11aFields

open Ix (Name Level Expr RecursorVal)
open Ix.AuxGen (FreshFVars LocalDecl SourceRecTarget)
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Conv
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.FreshFVarsProof

def IsFieldFVar (field : Expr) : Prop :=
  ∃ name hash, field = Expr.fvar name hash

def FieldsAreFVars (fields : Array Expr) : Prop :=
  ∀ field ∈ fields, IsFieldFVar field

def FieldsProtected (supply : FreshFVars) (fields : Array Expr) : Prop :=
  ∀ field ∈ fields, Protects supply field

def SupportedFrom (source : Expr) (supply : FreshFVars) (e : Expr) : Prop :=
  ∀ key, Occurs key e → Occurs key source ∨ key ∈ supply.used

/-- The tuple order is the mutable-variable declaration order in the actual
loop: supply, current body, binder declarations, then allocated fields. -/
abbrev BinderState := FreshFVars × Expr × Array LocalDecl × Array Expr

def BinderInv (source : Expr) (state : BinderState) : Prop :=
  FieldsAreFVars state.2.2.2 ∧ FieldsProtected state.1 state.2.2.2 ∧
    SupportedFrom source state.1 state.2.1

def rawFieldRead (fields : Array Expr) (index : Nat) (cause : String) : O11aM Expr :=
  O11aM.side fields[index]? cause

/-- Proof-only confirmation, with exactly the original missing-field refusal.
The runtime does not execute this additional match. -/
def fvarFieldRead (fields : Array Expr) (index : Nat) (cause : String) : O11aM Expr := do
  let field ← rawFieldRead fields index cause
  match field with
  | .fvar .. => return field
  | _ => throw (some cause)

theorem side_ok {α : Type} {value : Option α} {out : α} {cause : String}
    (run : O11aM.side value cause = .ok out) : value = some out := by
  cases value with
  | none => cases run
  | some value => cases run; rfl

theorem rawFieldRead_eq_fvarFieldRead (fields : Array Expr)
    (shapes : FieldsAreFVars fields) (index : Nat) (cause : String) :
    rawFieldRead fields index cause = fvarFieldRead fields index cause := by
  cases found : fields[index]? with
  | none => simp only [rawFieldRead, fvarFieldRead, found, O11aM.side, bind, Except.bind]
  | some field =>
      obtain ⟨name, hash, rfl⟩ := shapes field (Array.mem_of_getElem? found)
      simp only [rawFieldRead, fvarFieldRead, found, O11aM.side, bind, Except.bind,
        pure, Except.pure]

theorem fvarFieldRead_shape (fields : Array Expr) (index : Nat) (cause : String)
    (field : Expr) (run : fvarFieldRead fields index cause = .ok field) :
    IsFieldFVar field := by
  unfold fvarFieldRead at run
  obtain ⟨value, _, run⟩ := except_bind_ok.1 run
  cases value with
  | fvar name hash =>
      have same : Expr.fvar name hash = field := Except.ok.inj run
      subst field
      exact ⟨name, hash, rfl⟩
  | _ => cases run

theorem fields_push_fresh (supply : FreshFVars) (fields : Array Expr)
    (shapes : FieldsAreFVars fields) (pfx : String) (index : Nat) :
    FieldsAreFVars (fields.push (supply.fresh pfx index).1.2) := by
  intro field member
  rcases Array.mem_push.1 member with old | rfl
  · exact shapes field old
  · rw [fresh_pair_expr]
    exact ⟨_, _, rfl⟩

theorem fields_protected_fresh (supply : FreshFVars) (fields : Array Expr)
    (covered : FieldsProtected supply fields) (pfx : String) (index : Nat) :
    FieldsProtected (supply.fresh pfx index).2 fields := by
  intro field member
  exact protects_mono supply _ field (fresh_grows supply pfx index) (covered field member)

theorem fresh_field_protected (supply : FreshFVars) (pfx : String) (index : Nat) :
    Protects (supply.fresh pfx index).2 (supply.fresh pfx index).1.2 := by
  rw [fresh_pair_expr]
  exact (protects_fvar _ _ _).2 (fresh_reserved supply pfx index)

theorem fields_protected_push_fresh (supply : FreshFVars) (fields : Array Expr)
    (covered : FieldsProtected supply fields) (pfx : String) (index : Nat) :
    FieldsProtected (supply.fresh pfx index).2
      (fields.push (supply.fresh pfx index).1.2) := by
  intro field member
  rcases Array.mem_push.1 member with old | rfl
  · exact fields_protected_fresh supply fields covered pfx index field old
  · exact fresh_field_protected supply pfx index

theorem supported_open (source body replacement : Expr) (supply : FreshFVars)
    (bodySupport : SupportedFrom source supply body)
    (replacementSupport : Protects supply replacement) :
    SupportedFrom source supply (Ix.AuxGen.instantiate1 body replacement) := by
  intro key occurs
  rcases instantiate1At_occurs_source body replacement 0 key occurs with old | added
  · exact bodySupport key old
  · exact .inr (replacementSupport key added)

theorem lam_body_support (cur : Expr) (parts : Name × Expr × Expr × Lean.BinderInfo)
    (cause : String)
    (read : O11aM.side (match cur with
      | .lam bn dom body bi _ => some (bn, dom, body, bi)
      | _ => none) cause = .ok parts) :
    ∀ key, Occurs key parts.2.2.1 → Occurs key cur := by
  have shape := side_ok read
  cases cur with
  | lam name domain body info hash =>
      have same : (name, domain, body, info) = parts := Option.some.inj shape
      subst parts
      exact fun _ h => .inr h
  | _ => cases shape

/-- The actual body of the source loop. The parameter changes only the field
read, after the instance callback. Both its raw and confirming instantiations
use all four source state fields and every original error branch. -/
open O11aM in
def binderStepWith (readField : Array Expr → Nat → String → O11aM Expr)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (i : Nat) (state : BinderState) : O11aM (ForInStep BinderState) := do
  let (supply, cur, decls, fvars) := state
  let (bn, dom, b, bi) ← side (match cur with
    | .lam bn dom b bi _ => some (bn, dom, b, bi)
    | _ => none) s!"minor {j} is not a λ over its {numFields} field(s) and \
      {recFields.size} induction hypothesis(es)"
  let ((fvName, fv), nextSupply) := supply.fresh "o11a" i
  if i < numFields then
    return .yield (nextSupply, Ix.AuxGen.instantiate1 b fv,
      decls.push { fvarName := fvName, binderName := bn, domain := dom, info := bi },
      fvars.push fv)
  else
    let (fieldIdx, target) := recFields[i - numFields]!
    if inBlock.getD target.sourcePos false then
      return .yield (nextSupply, Ix.AuxGen.instantiate1 b fv,
        decls.push { fvarName := fvName, binderName := bn, domain := dom, info := bi }, fvars)
    else
      let T ← side rv.all[target.sourcePos]? unread
      need target.xsFvars.isEmpty s!"field {fieldIdx} of minor {j} is reflexive (a function \
        into the cross target {T.pretty})"
      need target.idxArgs.isEmpty s!"field {fieldIdx} of minor {j} has index arguments \
        (its cross target {T.pretty} is indexed)"
      let (inst, l) ← inst? T telescope
      let field ← readField fvars fieldIdx unread
      let sz := Ix.Compile.Canon.mkAppN (Expr.mkConst nSizeOf #[l])
        #[Expr.mkConst T #[], Expr.mkConst inst #[], field]
      return .yield (nextSupply, Ix.AuxGen.instantiate1 b sz, decls, fvars)

theorem binderStep_read_eq (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) (i : Nat)
    (state : BinderState) (shapes : FieldsAreFVars state.2.2.2) :
    binderStepWith rawFieldRead inst? rv inBlock recFields telescope numFields j unread i state =
      binderStepWith fvarFieldRead inst? rv inBlock recFields telescope numFields j unread i state := by
  have reads := rawFieldRead_eq_fvarFieldRead state.2.2.2 shapes
  simp only [binderStepWith, reads]

/-- Allocation, array origin and source support are derived from every actual
successful body step. No property of the callback's answer is assumed. -/
theorem binderStep_preserves (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) (source : Expr)
    (i : Nat) (state : BinderState) (out : ForInStep BinderState)
    (valid : BinderInv source state)
    (run : binderStepWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread i state = .ok out) :
    ∃ next, out = .yield next ∧ BinderInv source next := by
  rcases state with ⟨supply, cur, decls, fvars⟩
  rcases valid with ⟨shapes, covered, support⟩
  unfold binderStepWith at run
  obtain ⟨parts, read, run⟩ := except_bind_ok.1 run
  rcases parts with ⟨bn, dom, body, bi⟩
  have bodySource := lam_body_support cur (bn, dom, body, bi) _ read
  have bodySupport : SupportedFrom source (supply.fresh "o11a" i).2 body := by
    intro key occurs
    rcases support key (bodySource key occurs) with original | allocated
    · exact .inl original
    · exact .inr (fresh_grows supply "o11a" i key allocated)
  have newField := fresh_field_protected supply "o11a" i
  have oldFields := fields_protected_fresh supply fvars covered "o11a" i
  dsimp only at run
  split at run
  · cases run
    exact ⟨_, rfl, fields_push_fresh supply fvars shapes "o11a" i,
      fields_protected_push_fresh supply fvars covered "o11a" i,
      supported_open source body _ _ bodySupport newField⟩
  · dsimp only at run
    split at run
    · cases run
      exact ⟨_, rfl, shapes, oldFields,
        supported_open source body _ _ bodySupport newField⟩
    · obtain ⟨target, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨answer, _, run⟩ := except_bind_ok.1 run
      rcases answer with ⟨inst, level⟩
      obtain ⟨field, readField, run⟩ := except_bind_ok.1 run
      have found : fvars[(recFields[i - numFields]!).1]? = some field := side_ok readField
      have fieldSupport := oldFields field (Array.mem_of_getElem? found)
      have replacementSupport : Protects (supply.fresh "o11a" i).2
          (sizeOfReplacement target inst level field) := by
        intro key occurs
        exact fieldSupport key ((sizeOfReplacement_occurs target inst level field key).1 occurs)
      cases run
      exact ⟨_, rfl, shapes, oldFields,
        supported_open source body _ _ bodySupport replacementSupport⟩

/-- Complete Except equality for a loop under an internally maintained
invariant, including an error at any step. -/
theorem forIn_except_eq {α σ ε : Type}
    (f g : α → σ → Except ε (ForInStep σ)) (P : σ → Prop)
    (same : ∀ x state, P state → f x state = g x state)
    (next : ∀ x state out, P state → f x state = .ok out → P out.value) :
    ∀ (xs : List α) (state : σ), P state → forIn xs state f = forIn xs state g
  | [], _, _ => rfl
  | x :: xs, state, valid => by
    rw [List.forIn_cons, List.forIn_cons, ← same x state valid]
    cases step : f x state with
    | error error => rfl
    | ok out =>
      have valid' := next x state out valid step
      cases out with
      | done out => rfl
      | yield out => exact forIn_except_eq f g P same next xs out valid'

def binderLoopWith (readField : Array Expr → Nat → String → O11aM Expr)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) : O11aM BinderState :=
  forIn [0:count] (supply, minor, #[], #[])
    (binderStepWith readField inst? rv inBlock recFields telescope numFields j unread)

theorem binderInv_initial (supply : FreshFVars) (minor : Expr) :
    BinderInv minor (supply, minor, #[], #[]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro field member; simp at member
  · intro field member; simp at member
  · exact fun _ occurs => .inl occurs

theorem binderLoop_invariant (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) : BinderInv minor out := by
  unfold binderLoopWith at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  exact Ix.CompileCert.Canon.forIn_except_list _ (fun _ state => BinderInv minor state)
    (fun _ i state out valid run => binderStep_preserves inst? rv inBlock recFields
      telescope numFields j unread minor i state out valid run)
    _ [] _ out (binderInv_initial supply minor) run

theorem binderLoop_read_eq (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) :
    binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor =
    binderLoopWith fvarFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor := by
  unfold binderLoopWith
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_except_eq _ _ (BinderInv minor)
    (fun i state valid => binderStep_read_eq inst? rv inBlock recFields
      telescope numFields j unread i state valid.1)
  · intro i state out valid run
    obtain ⟨next, rfl, valid'⟩ := binderStep_preserves inst? rv inBlock recFields
      telescope numFields j unread minor i state out valid run
    exact valid'
  · exact binderInv_initial supply minor

/-- Every successful prefix has only actual FVar field operands, still
protected after intervening allocations. `count` also covers the full loop. -/
theorem binderLoop_field_access (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out)
    (index : Nat) (field : Expr) (found : out.2.2.2[index]? = some field) :
    IsFieldFVar field ∧ Protects out.1 field := by
  have valid := binderLoop_invariant inst? rv inBlock recFields telescope
    numFields j unread count supply minor out run
  have member := Array.mem_of_getElem? found
  exact ⟨valid.1 field member, valid.2.1 field member⟩

theorem binderLoop_source_support (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) :
    SupportedFrom minor out.1 out.2.1 :=
  (binderLoop_invariant inst? rv inBlock recFields telescope
    numFields j unread count supply minor out run).2.2

/-- Source preparation copied literally, followed by the factored actual loop.
No source/type/target success or callback validity is assumed. -/
open O11aM in
def minorWithReader (readField : Array Expr → Nat → String → O11aM Expr)
    (env : OptEnv) (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) : O11aM (Option Expr) := do
  let ienv := env.ienv
  let initial := (Ix.AuxGen.FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)
  let (auxSigs, supply) := (Ix.AuxGen.auxMotiveSigsWith rv us ps ms ienv).run initial
  let unread := s!"the constructor and minor type of minor {j} cannot be read"
  let (_, ctor) ← side (Ix.AuxGen.sourceCtorForMinor j rv ienv auxSigs) unread
  let minorTy ← side (Ix.AuxGen.sourceMinorType rv us ps ms mins j) unread
  let (fields?, supply) :=
    (Ix.AuxGen.peelBindersWith minorTy ctor.numFields "split_field" 0).run supply
  let (fieldDecls, _, _) ← side fields? unread
  let mut supply := supply
  let mut recFields : Array (Nat × Ix.AuxGen.SourceRecTarget) := #[]
  for (decl, fieldIdx) in fieldDecls.zipIdx do
    let (target?, nextSupply) := (Ix.AuxGen.findSourceRecTargetWith decl.domain rv.all
      ps ienv "split_xs" fieldIdx auxSigs).run supply
    supply := nextSupply
    if let some target := target? then
      recFields := recFields.push (fieldIdx, target)
  if !recFields.any (fun (_, t) => !(inBlock.getD t.sourcePos false)) then
    return none
  let m ← side mins[j]? unread
  let out ← binderLoopWith readField inst? rv inBlock recFields (ps ++ ms ++ mins)
    ctor.numFields j unread (ctor.numFields + recFields.size) supply m
  return some (Ix.AuxGen.mkLambda out.2.1 out.2.2.1)

/-- Exact result, including every failure, optional absence and raw output.
This is the connection to the runtime helper, not an assumed copy law. -/
theorem sizeOfMinorWith_eq_raw (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) :
    sizeOfMinorWith env inst? rv inBlock us ps ms mins j =
      minorWithReader rawFieldRead env inst? rv inBlock us ps ms mins j := by
  unfold sizeOfMinorWith minorWithReader binderLoopWith binderStepWith rawFieldRead
  rfl

/-- The actual public helper may use the FVar-confirming read with exactly
the same complete Except outcome, on arbitrary source/environment/callback
inputs. The invariant is initialized and preserved inside its loop. -/
theorem sizeOfMinorWith_eq_fvarReader (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) :
    sizeOfMinorWith env inst? rv inBlock us ps ms mins j =
      minorWithReader fvarFieldRead env inst? rv inBlock us ps ms mins j := by
  rw [sizeOfMinorWith_eq_raw]
  simp only [minorWithReader, binderLoop_read_eq]

/-- The exact cross-branch callback/read/opening sequence, on the equivalent
confirmed runtime path. Arbitrary errors, missing fields, raw bodies and
callback name/level answers are retained; only successful values are erased. -/
theorem field_callback_opening (inst? : Name → Array Expr → O11aM (Name × Level))
    (target : Name) (telescope : Array Expr) (fields : Array Expr)
    (index : Nat) (cause : String) (body : Expr) :
    (do
      let answer ← inst? target telescope
      let field ← fvarFieldRead fields index cause
      pure (er (Ix.AuxGen.instantiate1 body
        (sizeOfReplacement target answer.1 answer.2 field))) : O11aM Tm) =
    (do
      let answer ← inst? target telescope
      let field ← fvarFieldRead fields index cause
      pure (Tm.inst (er (sizeOfReplacement target answer.1 answer.2 field)) 0 (er body)) : O11aM Tm) := by
  cases inst? target telescope with
  | error error => rfl
  | ok answer =>
      cases read : fvarFieldRead fields index cause with
      | error error => rfl
      | ok field =>
          obtain ⟨name, hash, rfl⟩ := fvarFieldRead_shape fields index cause field read
          exact congrArg Except.ok
            (er_open_sizeOfReplacement body target answer.1 name answer.2 hash 0)

/-- The corresponding original read, at any successful prefix of the actual
loop. The source execution supplies the array shape; the callback and raw
body remain arbitrary, including callback errors and a missing field. -/
theorem prefix_field_callback_opening (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out)
    (target : Name) (index : Nat) (body : Expr) :
    (do
      let answer ← inst? target telescope
      let field ← rawFieldRead out.2.2.2 index unread
      pure (er (Ix.AuxGen.instantiate1 body
        (sizeOfReplacement target answer.1 answer.2 field))) : O11aM Tm) =
    (do
      let answer ← inst? target telescope
      let field ← rawFieldRead out.2.2.2 index unread
      pure (Tm.inst (er (sizeOfReplacement target answer.1 answer.2 field)) 0 (er body)) : O11aM Tm) := by
  have shapes := (binderLoop_invariant inst? rv inBlock recFields telescope
    numFields j unread count supply minor out run).1
  simp only [rawFieldRead_eq_fvarFieldRead out.2.2.2 shapes index unread]
  exact field_callback_opening inst? target telescope out.2.2.2 index unread body

theorem callback_error_precedes_field_read (inst? : Name → Array Expr → O11aM (Name × Level))
    (target : Name) (telescope : Array Expr) (fields : Array Expr)
    (index : Nat) (cause : String) (error : Option String)
    (failed : inst? target telescope = .error error) :
    (do
      let _ ← inst? target telescope
      fvarFieldRead fields index cause : O11aM Expr) = .error error := by
  rw [failed]
  rfl

/-- Forged cached hashes do not affect structural confirmation. -/
theorem forged_fvar_neighbour (name : Name) (hash : _root_.Address) (cause : String) :
    fvarFieldRead #[Expr.fvar name hash] 0 cause = .ok (Expr.fvar name hash) := rfl

/-- A fabricated loose field is not covered by the redundant-read claim for
arbitrary tables. The actual source loop derives its stronger array invariant. -/
theorem loose_field_negative (index : Nat) (hash : _root_.Address) (cause : String) :
    rawFieldRead #[Expr.bvar index hash] 0 cause = .ok (Expr.bvar index hash) ∧
      fvarFieldRead #[Expr.bvar index hash] 0 cause = .error (some cause) := ⟨rfl, rfl⟩

theorem missing_field_retained (cause : String) (index : Nat) :
    rawFieldRead #[] index cause = .error (some cause) ∧
      fvarFieldRead #[] index cause = .error (some cause) := by
  simp only [rawFieldRead, fvarFieldRead, Array.getElem?_empty, O11aM.side,
    bind, Except.bind, and_self]

end Ix.CompileCert.Opt.O11aFields
