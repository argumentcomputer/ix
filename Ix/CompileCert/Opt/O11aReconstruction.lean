import Ix.CompileCert.Opt.FreshTelescope
import Ix.CompileCert.Opt.O11aReaderGrowth

/-!
Actual O11a binder reconstruction from source-derived protection.
SOURCE-ONLY / UNCOMPILED. The retained-prefix theorem closes multiple actual
allocations in declaration order. The whole-Except theorem exposes the actual
final batch reconstruction without changing any read, callback or error order.
Cross-branch semantic conversion, `sizeOfInstanceE`, and the original
O11aFaithful endpoint are not discharged here.
-/

namespace Ix.CompileCert.Opt.O11aReconstruction

open Ix (Name Level Expr RecursorVal)
open Ix.AuxGen (FreshFVars LocalDecl SourceRecTarget)
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Conv
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.FreshFVarsProof
open Ix.CompileCert.Opt.FreshTelescope
open Ix.CompileCert.Opt.O11aFields
open Ix.CompileCert.Opt.O11aSourceBounds
open Ix.CompileCert.Opt.O11aReaderGrowth

/-- The two actual branches that retain a lambda binder. This is an internal
prefix condition, not an extra premise on O11a or its source inputs. -/
def RetainedIndex (numFields : Nat) (inBlock : Array Bool)
    (recFields : Array (Nat × SourceRecTarget)) (index : Nat) : Prop :=
  index < numFields ∨ inBlock.getD (recFields[index - numFields]!).2.sourcePos false = true

private theorem close_push_fresh (supply : FreshFVars) (decls : Array LocalDecl)
    (name : Name) (domain body : Expr) (info : Lean.BinderInfo) (hash : Address)
    (index : Nat) (covered : Protects supply (.lam name domain body info hash)) :
    er (closeDecls
      (decls.push { fvarName := (supply.fresh "o11a" index).1.1,
        binderName := name, domain := domain, info := info }).toList
      (Ix.AuxGen.instantiate1 body (supply.fresh "o11a" index).1.2)) =
      er (closeDecls decls.toList (.lam name domain body info hash)) := by
  rw [Array.toList_push, closeDecls_append]
  exact closeDecls_er_congr decls.toList _ _
    (fresh_lambda_close supply name domain body info hash "o11a" index covered)

/-- A successful retained step appends exactly the current domain and binder
metadata. Closing that fresh opening recovers the previous reconstructed term.
No property of the instance callback is used. -/
theorem binderStep_retained_close
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) (index : Nat)
    (state : BinderState) (step : ForInStep BinderState)
    (kept : RetainedIndex numFields inBlock recFields index)
    (covered : Protects state.1 state.2.1)
    (run : binderStepWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread index state = .ok step) :
    ∃ next, step = .yield next ∧ Protects next.1 next.2.1 ∧
      er (closeDecls next.2.2.1.toList next.2.1) =
        er (closeDecls state.2.2.1.toList state.2.1) := by
  rcases state with ⟨supply, cur, decls, fields⟩
  unfold binderStepWith at run
  obtain ⟨parts, read, run⟩ := except_bind_ok.1 run
  have shape := side_ok read
  cases cur with
  | lam name domain body info hash =>
      have same : (name, domain, body, info) = parts := Option.some.inj shape
      subst parts
      have bodyCovered : Protects supply body := fun key occurs => covered key (.inr occurs)
      have nextCovered := fresh_open_protects_of supply body "o11a" index 0 bodyCovered
      have roundtrip := close_push_fresh supply decls name domain body info hash index covered
      dsimp only at run
      split at run
      · cases run
        exact ⟨_, rfl, nextCovered, roundtrip⟩
      · rename_i notField
        have internal := kept.resolve_left notField
        rw [internal] at run
        cases run
        exact ⟨_, rfl, nextCovered, roundtrip⟩
  | _ => cases shape

/-- A finite actual loop of retained binders, with arbitrary starting
declarations and field arrays. Every successful step supplies its roundtrip;
the equality is not a semantic callback premise. -/
theorem binderList_retained_close
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) :
    ∀ (indices : List Nat) (state out : BinderState),
      (∀ index ∈ indices, RetainedIndex numFields inBlock recFields index) →
      Protects state.1 state.2.1 →
      forIn indices state (binderStepWith rawFieldRead inst? rv inBlock recFields
        telescope numFields j unread) = .ok out →
      Protects out.1 out.2.1 ∧
        er (closeDecls out.2.2.1.toList out.2.1) =
          er (closeDecls state.2.2.1.toList state.2.1)
  | [], state, out, _, covered, run => by
      change Except.ok state = Except.ok out at run
      cases run
      exact ⟨covered, rfl⟩
  | index :: rest, state, out, kept, covered, run => by
      rw [List.forIn_cons] at run
      obtain ⟨step, succeeded, run⟩ := except_bind_ok.1 run
      obtain ⟨next, rfl, nextCovered, one⟩ := binderStep_retained_close inst? rv inBlock
        recFields telescope numFields j unread index state step
        (kept index (.head _)) covered succeeded
      obtain ⟨lastCovered, more⟩ := binderList_retained_close inst? rv inBlock recFields
        telescope numFields j unread rest next out
        (fun i member => kept i (.tail _ member)) nextCovered run
      exact ⟨lastCovered, more.trans one⟩

/-- All source-field binders are retained. The requested prefix length is
bounded by the constructor's field count, not by a new input-domain restriction.
The initial protection premise is discharged by the prepared-source theorem. -/
theorem binderLoop_field_prefix_close
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (fieldsOnly : count ≤ numFields) (covered : Protects supply minor)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) :
    Protects out.1 out.2.1 ∧ er (closeDecls out.2.2.1.toList out.2.1) = er minor := by
  unfold binderLoopWith at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at run
  apply binderList_retained_close inst? rv inBlock recFields telescope numFields j unread
    (List.range' 0 count) (supply, minor, #[], #[]) out ?_ covered run
  intro index member
  have bound := (List.mem_range'_1.1 member).2
  exact .inl (by omega)

/-- Concrete source preparation supplies the protection used by the entire
multi-binder retained-prefix reconstruction. Preferred-name collisions and
pre-existing FVars are handled by the actual allocator. -/
theorem prepared_field_prefix_close (rv : RecursorVal) (levels : Array Level)
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
      Protects out.1 out.2.1 ∧ er (closeDecls out.2.2.1.toList out.2.1) = er minor := by
  dsimp only
  intro prepareRun loopRun
  exact binderLoop_field_prefix_close inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
    numFields index unread count prepared.1 minor out fieldsOnly
    (prepared_minor_protected rv levels ps ms mins env minorTy numFields index
      unread prepared minor read prepareRun) loopRun

/-- The actual preparation and binder loop, with only the successful final
value reconstructed in Tm. Every original error and callback read is retained. -/
def minorErasedPrepared (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) : O11aM (Option Tm) := do
  let initial := (FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)
  let (auxSigs, supply) := (Ix.AuxGen.auxMotiveSigsWith rv us ps ms env.ienv).run initial
  let unread := s!"the constructor and minor type of minor {j} cannot be read"
  let (_, ctor) ← O11aM.side (Ix.AuxGen.sourceCtorForMinor j rv env.ienv auxSigs) unread
  let minorTy ← O11aM.side (Ix.AuxGen.sourceMinorType rv us ps ms mins j) unread
  let prepared ← prepareFields minorTy ctor.numFields supply
    (actualTargetRead rv ps env.ienv auxSigs) unread
  if !prepared.2.any (fun (_, target) => !(inBlock.getD target.sourcePos false)) then
    return none
  let minor ← O11aM.side mins[j]? unread
  let out ← binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
    ctor.numFields j unread (ctor.numFields + prepared.2.size) prepared.1 minor
  return some (erasedLambda (er out.2.1) out.2.2.1)

private theorem except_map_bind {ε α β γ : Type} (action : Except ε α)
    (next : α → Except ε β) (f : β → γ) :
    (action >>= next).map f = action >>= fun value => (next value).map f := by
  cases action <;> rfl

/-- Whole-Except refinement of the actual public helper. This theorem is
independent of callback semantics and of success or availability assumptions. -/
theorem sizeOfMinorWith_erased (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) :
    (sizeOfMinorWith env inst? rv inBlock us ps ms mins j).map (Option.map er) =
      minorErasedPrepared env inst? rv inBlock us ps ms mins j := by
  rw [sizeOfMinorWith_eq_prepared]
  unfold minorPrepared minorErasedPrepared
  generalize (Ix.AuxGen.auxMotiveSigsWith rv us ps ms env.ienv).run
    ((FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)) = aux
  rcases aux with ⟨auxSigs, supply⟩
  rw [except_map_bind]
  apply bind_congr
  rintro ⟨sourcePos, ctor⟩
  rw [except_map_bind]
  apply bind_congr
  intro minorTy
  rw [except_map_bind]
  apply bind_congr
  intro prepared
  split
  · rfl
  · rw [except_map_bind]
    apply bind_congr
    intro minor
    rw [except_map_bind]
    apply bind_congr
    intro opened
    exact congrArg Except.ok (congrArg some (er_mkLambda opened.2.1 opened.2.2.1))

/-- Successful final reconstruction and its protected source operands are
obtained together from the actual source/helper run, including cross branches. -/
theorem sizeOfMinorWith_reconstruction (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (levels : Array Level)
    (ps ms mins : Array Expr) (index : Nat) (output : Expr)
    (run : sizeOfMinorWith env inst? rv inBlock levels ps ms mins index = .ok (some output)) :
    ∃ opened : BinderState,
      er output = erasedLambda (er opened.2.1) opened.2.2.1 ∧
      Grows (initialSupply rv ps ms mins) opened.1 ∧
      Protects opened.1 rv.cnst.type ∧
      (∀ value ∈ ps ++ ms ++ mins, Protects opened.1 value) ∧
      Protects opened.1 opened.2.1 := by
  obtain ⟨opened, outputEq, grow, typeCovered, operandsCovered, bodyCovered⟩ :=
    sizeOfMinorWith_success_protection env inst? rv inBlock levels ps ms mins index output run
  refine ⟨opened, ?_, grow, typeCovered, operandsCovered, bodyCovered⟩
  rw [outputEq, er_mkLambda]

end Ix.CompileCert.Opt.O11aReconstruction
