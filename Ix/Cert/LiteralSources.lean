import Ix.Cert.RefTables
import IxSharingVerify.FamilyDomain
import IxSharingVerify.CanonicalProduction
import IxSharingVerify.ReexpandSuccess
import Ix.CompileCert.SharingRoots

/-! # A compiled record's literals come from its source terms

`Ix.Kernel.Reader.literalKinds` reads whether a record holds a `Nat` or a `String` literal
from its sharing table and its payload's expressions; the check order follows a literal to the
roles it is checked against (`GroundEdge`'s literal disjunct). This module traces those
literals back to the terms the record was compiled from.

**Output conditions.** `RefTables.Triple I P action Q` carries a frame invariant `I` and a
postcondition `Q` on the returned value. The expression compiler's literal fact is a
postcondition of that form, `LitsFrom source`: the compiled expression holds a literal of a
kind only if its source term does. Its frame invariant is the cache's (`CacheLits`: every
cached output satisfies the postcondition at its exact source key), kept by every leaf that
leaves the cache alone (`cacheFrame`, through `RefTables.Holds.preserves`). Loops carry their
accumulator's condition (`Triple.forIn_list`). -/

namespace Ix.Cert.LiteralSources

open Ix.CompileM Ix.CompileCert
open Ix.Cert.RefTables (Triple Holds)

/-! ## Literal kinds of an Ixon expression -/

/-- An Ixon expression's literal kinds, `(nat, str)`, as `literalKinds` walks it (through
applications, binders, lets and projections, not through `share`). -/
abbrev ixLits (e : Ixon.Expr) : Bool × Bool := Ix.Kernel.Reader.literalKinds.go (false, false) e

theorem go_spec : ∀ (e : Ixon.Expr) (acc : Bool × Bool),
    Ix.Kernel.Reader.literalKinds.go acc e = (acc.1 || (ixLits e).1, acc.2 || (ixLits e).2)
  | .nat _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .str _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .prj _ _ v, acc => by
    simp only [ixLits, Ix.Kernel.Reader.literalKinds.go]
    rw [go_spec v acc, go_spec v (false, false)]
    simp
  | .app f a, acc => by
    simp only [ixLits, Ix.Kernel.Reader.literalKinds.go]
    rw [go_spec a, go_spec f, go_spec a (Ix.Kernel.Reader.literalKinds.go (false, false) f)]
    simp [Bool.or_assoc]
  | .lam _ t b, acc => by
    simp only [ixLits, Ix.Kernel.Reader.literalKinds.go]
    rw [go_spec b, go_spec t, go_spec b (Ix.Kernel.Reader.literalKinds.go (false, false) t)]
    simp [Bool.or_assoc]
  | .all _ _ t b, acc => by
    simp only [ixLits, Ix.Kernel.Reader.literalKinds.go]
    rw [go_spec b, go_spec t, go_spec b (Ix.Kernel.Reader.literalKinds.go (false, false) t)]
    simp [Bool.or_assoc]
  | .letE _ t v b, acc => by
    simp only [ixLits, Ix.Kernel.Reader.literalKinds.go]
    rw [go_spec b, go_spec v, go_spec t, go_spec b (Ix.Kernel.Reader.literalKinds.go _ v),
      go_spec v (Ix.Kernel.Reader.literalKinds.go (false, false) t)]
    simp [Bool.or_assoc]
  | .sort _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .var _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .ref _ _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .recur _ _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]
  | .share _, acc => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go]

theorem ixLits_app (f a : Ixon.Expr) :
    ixLits (.app f a) = ((ixLits f).1 || (ixLits a).1, (ixLits f).2 || (ixLits a).2) := by
  show Ix.Kernel.Reader.literalKinds.go (Ix.Kernel.Reader.literalKinds.go (false, false) f) a = _
  rw [go_spec]

theorem ixLits_lam (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    ixLits (.lam c t b) = ((ixLits t).1 || (ixLits b).1, (ixLits t).2 || (ixLits b).2) := by
  show Ix.Kernel.Reader.literalKinds.go (Ix.Kernel.Reader.literalKinds.go (false, false) t) b = _
  rw [go_spec]

theorem ixLits_all (c : Ixon.BinderContract) (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    ixLits (.all c r t b) = ((ixLits t).1 || (ixLits b).1, (ixLits t).2 || (ixLits b).2) := by
  show Ix.Kernel.Reader.literalKinds.go (Ix.Kernel.Reader.literalKinds.go (false, false) t) b = _
  rw [go_spec]

theorem ixLits_letE (c : Ixon.LetContract) (t v b : Ixon.Expr) :
    ixLits (.letE c t v b) = ((ixLits t).1 || (ixLits v).1 || (ixLits b).1,
      (ixLits t).2 || (ixLits v).2 || (ixLits b).2) := by
  show Ix.Kernel.Reader.literalKinds.go (Ix.Kernel.Reader.literalKinds.go
    (Ix.Kernel.Reader.literalKinds.go (false, false) t) v) b = _
  rw [go_spec, go_spec v]

theorem ixLits_prj (r f : UInt64) (v : Ixon.Expr) : ixLits (.prj r f v) = ixLits v := rfl

/-! ## The postcondition and the cache invariant -/

/-- **A compiled expression's literals are its source's**: it holds a `Nat` literal only if
its source does, and a `String` literal only if its source does. -/
def LitsFrom (source : Ix.Expr) (out : Ixon.Expr) : Prop :=
  ((ixLits out).1 = true → hasNatLit source = true) ∧ ((ixLits out).2 = true → hasStrLit source = true)

theorem LitsFrom.none {source : Ix.Expr} {out : Ixon.Expr} (h : ixLits out = (false, false)) :
    LitsFrom source out := by
  constructor <;> intro hx <;> simp [h] at hx

/-- **Every cached output's literals are its exact source key's.** -/
def CacheLits (s : BlockState) : Prop :=
  ∀ (key : Ix.Compile.ExactKey.ExprKey) value, s.exprCache.get? key = some value → LitsFrom key.expr value.1

/-- The frame invariant, as `Triple` takes it. -/
abbrev LI : CompileEnv → BlockState → Prop := fun _ s => CacheLits s

/-- The view of the state the cache invariant reads. -/
abbrev cacheView (s : BlockState) := s.exprCache

theorem cacheFrame {α : Type} {action : CompileM α} (frame : Preserves cacheView action) : Holds LI action :=
  Holds.preserves frame fun _ _ _ same hI key value found => by
    have := same
    simp only [cacheView] at this
    rw [this] at found
    exact hI key value found

/-! ## Loops with an accumulator condition -/

theorem Triple.forIn_list {α β : Type} {I : CompileEnv → BlockState → Prop} (J : β → Prop) (items : List α)
    (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item ∈ items, ∀ acc, Triple I (fun _ _ => J acc) (body item acc) (fun _ _ r => J r.value)) :
    Triple I (fun _ _ => J initial) (forIn items initial body) (fun _ _ r => J r) := by
  induction items generalizing initial with
  | nil => exact Triple.returns fun _ _ _ h => h
  | cons item rest ih =>
    rw [List.forIn_cons]
    refine Triple.bind (each item (by simp) initial) fun step => ?_
    cases step with
    | done value => exact Triple.returns fun _ _ _ h => h
    | yield value => exact ih value fun item member acc => each item (List.mem_cons_of_mem _ member) acc

/-! ## The leaves keep the cache -/

theorem frame_checkedIndex (table : String) (index : Nat) : Preserves cacheView (checkedTableIndex table index) :=
  fun context before => by rw [Interning.checkedTableIndex_state]

theorem frame_checkedCount (table : String) (count : Nat) : Preserves cacheView (checkedTableCount table count) :=
  fun context before => by rw [Interning.checkedTableCount_state]

theorem frame_alloc (node : Ixon.ExprMetaData) : Preserves cacheView (allocArenaNode node) := by
  unfold allocArenaNode
  exact Preserves.modifyGet _ _ fun _ => rfl

theorem frame_patch (root : UInt64) (indices : Array UInt64) : Preserves cacheView (pushUnivPatch root indices) := by
  unfold pushUnivPatch
  exact Preserves.modify _ _ fun _ => rfl

theorem frame_level (source : Ix.Level) : Preserves cacheView (compileAndInternUnivCanon source) :=
  fun context before => by
    have same := congrArg BlockState.exprCache (UniversePipeline.compileAndInternUnivCanon_frame source context before)
    exact same

theorem frame_namesBlobs {α : Type} {action : CompileM α} (framed : Serializers.NamesBlobs action) :
    Preserves cacheView action :=
  fun context before => by
    have same := congrArg BlockState.exprCache (framed context before).1
    exact same

theorem frame_lookup (name : Ix.Name) : Preserves cacheView (lookupConstAddr name) :=
  fun context before => by rw [ExpressionState.lookupConstAddr_state]

theorem frame_internRef (address : Address) : Preserves cacheView (internRef address) :=
  fun context before => (Interning.internRef_tables address context before).2.2

/-! ## Chaining value conditions -/

/-- A condition on the run's earlier values, as a precondition. -/
theorem Triple.of_imp {α : Type} {I : CompileEnv → BlockState → Prop} {P : Prop} {action : CompileM α}
    {Q : CompileEnv → BlockState → α → Prop} (h : P → Triple I (fun _ _ => True) action Q) :
    Triple I (fun _ _ => P) action Q :=
  fun c b v a hI hP ran => h hP c b v a hI trivial ran

/-- **Bind with the head's value condition in scope.** -/
theorem Triple.andThen {α β : Type} {I : CompileEnv → BlockState → Prop} {action : CompileM α}
    {next : α → CompileM β} {Q : α → Prop} {R : CompileEnv → BlockState → β → Prop}
    (head : Triple I (fun _ _ => True) action (fun _ _ v => Q v))
    (tail : ∀ v, Q v → Triple I (fun _ _ => True) (next v) R) : Triple I (fun _ _ => True) (action >>= next) R :=
  Triple.bind head fun v => Triple.of_imp (tail v)

/-- A leaf the invariant holds over, then the rest. -/
theorem Triple.seqHolds {α β : Type} {I : CompileEnv → BlockState → Prop} {action : CompileM α}
    {next : α → CompileM β} {R : CompileEnv → BlockState → β → Prop}
    (head : Holds I action) (tail : ∀ v, Triple I (fun _ _ => True) (next v) R) :
    Triple I (fun _ _ => True) (action >>= next) R :=
  Triple.bind head fun v => Triple.pre (tail v) fun _ _ _ _ => trivial

/-! ## The expression compiler -/

/-- A compile on a subterm, under the cache invariant, with its source's literals. -/
abbrev Compiles (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (child : Ix.Expr) : Prop :=
  Triple LI (fun _ _ => True) (compile child) (fun _ _ r => LitsFrom child r.1)

theorem litsFrom_mono {s s' : Ix.Expr} {out : Ixon.Expr} (h : LitsFrom s out)
    (nat : hasNatLit s = true → hasNatLit s' = true) (str : hasStrLit s = true → hasStrLit s' = true) :
    LitsFrom s' out :=
  ⟨fun hx => nat (h.1 hx), fun hx => str (h.2 hx)⟩

theorem litsFrom_two {s : Ix.Expr} {a b out : Ixon.Expr} (ha : LitsFrom s a) (hb : LitsFrom s b)
    (shape : ixLits out = ((ixLits a).1 || (ixLits b).1, (ixLits a).2 || (ixLits b).2)) : LitsFrom s out := by
  constructor <;> intro h <;> rw [shape] at h <;> simp only [Bool.or_eq_true] at h <;> rcases h with h | h
  exacts [ha.1 h, hb.1 h, ha.2 h, hb.2 h]

/-- The head and arguments of an application spine have only the spine's literals. -/
theorem decompose_lits : ∀ (expr : Ix.Expr) (args : Array Ix.Expr) (whole : Ix.Expr),
    (hasNatLit expr = true → hasNatLit whole = true) → (hasStrLit expr = true → hasStrLit whole = true) →
    (∀ x ∈ args, (hasNatLit x = true → hasNatLit whole = true) ∧ (hasStrLit x = true → hasStrLit whole = true)) →
    ((hasNatLit (Ix.AuxGen.decomposeApps.go expr args).1 = true → hasNatLit whole = true) ∧
      (hasStrLit (Ix.AuxGen.decomposeApps.go expr args).1 = true → hasStrLit whole = true)) ∧
    ∀ x ∈ (Ix.AuxGen.decomposeApps.go expr args).2,
      (hasNatLit x = true → hasNatLit whole = true) ∧ (hasStrLit x = true → hasStrLit whole = true) := by
  intro expr
  induction expr
  case app f a h ihf iha =>
    intro args whole nat str hargs
    refine ihf (args.push a) whole (fun hf => nat (by simp [hasNatLit, hf]))
      (fun hf => str (by simp [hasStrLit, hf])) (fun x hx => ?_)
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hargs x hx
    · exact ⟨fun ha => nat (by simp [hasNatLit, ha]), fun ha => str (by simp [hasStrLit, ha])⟩
  all_goals
    intro args whole nat str hargs
    exact ⟨⟨nat, str⟩, fun x hx => hargs x (Array.mem_reverse.mp hx)⟩

/-- A semantic contract changes only a binder's annotations. -/
theorem lower_lits {contract : Ix.SemanticContract.Contract} {source : Ix.Expr} {compiled value : Ixon.Expr}
    (h : contract.lower source compiled = .ok value) : ixLits value = ixLits compiled := by
  unfold Ix.SemanticContract.Contract.lower at h
  split at h
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       simp only [ixLits_lam, ixLits_all, ixLits_letE])
    | cases h

/-- **One step returns its source's literals**, given the same of the recursive compile on
every strict subterm, under the cache invariant. -/
theorem step_lits (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Expr)
    (each : ∀ child, sizeOf child < sizeOf source → Compiles compile child) :
    Triple LI (fun _ _ => True) (ExpressionState.step compile source) (fun _ _ r => LitsFrom source r.1) := by
  cases source with
  | bvar index hash =>
    rw [ExpressionState.bvar_step_eq]
    exact Triple.seqHolds (cacheFrame (frame_checkedIndex _ _)) fun _ =>
      Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ => LitsFrom.none rfl
  | sort level hash =>
    rw [ExpressionState.sort_step_eq]
    refine Triple.seqHolds (cacheFrame (frame_level _)) fun result => ?_
    obtain ⟨index, patch⟩ := result
    dsimp only
    unfold ExpressionState.finishSort
    refine Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => ?_
    split
    · exact Triple.seqHolds (cacheFrame (frame_patch _ _)) fun _ =>
        Triple.returns fun _ _ _ _ => LitsFrom.none rfl
    · exact Triple.returns fun _ _ _ _ => LitsFrom.none rfl
  | const name levels hash =>
    rw [ExpressionState.const_step_eq, ExpressionState.compileConstExprRaw_eq]
    refine Triple.seqHolds (cacheFrame (Preserves.read _)) fun block => ?_
    dsimp only
    refine Triple.seqHolds (RefTables.Holds.mapM_array _ _ fun _ _ => cacheFrame (frame_level _)) fun compiled =>
      Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName name))) fun _ => ?_
    unfold ExpressionState.constBody ExpressionState.finishReference
    split
    · refine Triple.seqHolds (cacheFrame (frame_checkedIndex _ _)) fun _ =>
        Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => ?_
      split
      · exact Triple.seqHolds (cacheFrame (frame_patch _ _)) fun _ =>
          Triple.returns fun _ _ _ _ => LitsFrom.none rfl
      · exact Triple.returns fun _ _ _ _ => LitsFrom.none rfl
    · refine Triple.seqHolds (cacheFrame (frame_lookup _)) fun _ =>
        Triple.seqHolds (cacheFrame (frame_internRef _)) fun _ =>
        Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => ?_
      split
      · exact Triple.seqHolds (cacheFrame (frame_patch _ _)) fun _ =>
          Triple.returns fun _ _ _ _ => LitsFrom.none rfl
      · exact Triple.returns fun _ _ _ _ => LitsFrom.none rfl
  | app fn arg hash =>
    rw [ExpressionState.app_step_eq]
    have parts := decompose_lits (.app fn arg hash) #[] (.app fn arg hash) id id (fun x hx => by simp at hx)
    refine Triple.andThen (each _ (Ix.AuxGen.decomposeApps_app_head_lt fn arg hash)) fun head hhead => ?_
    rw [forIn'_eq_forIn _ _ _ (fun x acc => ExpressionState.appBody compile acc x) (fun _ _ _ => rfl)]
    rw [← Array.forIn_toList]
    refine Triple.bind (Triple.pre (Triple.forIn_list (fun acc : Ixon.Expr × UInt64 =>
        LitsFrom (.app fn arg hash) acc.1) _ _ _ fun x member acc => ?_) fun _ _ _ _ =>
          litsFrom_mono hhead parts.1.1 parts.1.2) fun spine => Triple.returns fun _ _ _ h => h
    have hx := parts.2 x (by
      have hm : x ∈ (Ix.AuxGen.decomposeApps (.app fn arg hash)).2 := by simpa using member
      exact hm)
    unfold ExpressionState.appBody
    refine Triple.of_imp fun hacc => ?_
    refine Triple.andThen (each x (Ix.AuxGen.decomposeApps_app_mem_lt fn arg hash (by simpa using member)))
      fun child hchild => ?_
    refine Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ => ?_
    exact litsFrom_two hacc (litsFrom_mono hchild hx.1 hx.2) (ixLits_app _ _)
  | lam name type body info hash =>
    rw [show ExpressionState.step compile (.lam name type body info hash) = _ from
      ExpressionState.binder_step_eq false compile name type body info hash]
    unfold ExpressionState.finishBinder
    refine Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName name))) fun _ =>
      Triple.andThen (each type (by simp; omega)) fun t ht =>
      Triple.andThen (each body (by simp; omega)) fun b hb =>
      Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ => ?_
    exact litsFrom_two (litsFrom_mono ht (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h]))
      (litsFrom_mono hb (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])) (ixLits_lam _ _ _)
  | forallE name type body info hash =>
    rw [show ExpressionState.step compile (.forallE name type body info hash) = _ from
      ExpressionState.binder_step_eq true compile name type body info hash]
    unfold ExpressionState.finishBinder
    refine Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName name))) fun _ =>
      Triple.andThen (each type (by simp; omega)) fun t ht =>
      Triple.andThen (each body (by simp; omega)) fun b hb =>
      Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ => ?_
    exact litsFrom_two (litsFrom_mono ht (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h]))
      (litsFrom_mono hb (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])) (ixLits_all _ _ _ _)
  | letE name type value body nonDep hash =>
    rw [ExpressionState.let_step_eq]
    unfold ExpressionState.finishLet
    refine Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName name))) fun _ =>
      Triple.andThen (each type (by simp; omega)) fun t ht =>
      Triple.andThen (each value (by simp; omega)) fun v hv =>
      Triple.andThen (each body (by simp; omega)) fun b hb =>
      Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ => ?_
    have ht' := litsFrom_mono (s' := .letE name type value body nonDep hash) ht
      (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])
    have hv' := litsFrom_mono (s' := .letE name type value body nonDep hash) hv
      (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])
    have hb' := litsFrom_mono (s' := .letE name type value body nonDep hash) hb
      (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])
    constructor <;> intro h <;> simp only [Ixon.Expr.leanLet, ixLits_letE, Bool.or_eq_true] at h <;>
      rcases h with (h | h) | h
    exacts [ht'.1 h, hv'.1 h, hb'.1 h, ht'.2 h, hv'.2 h, hb'.2 h]
  | lit literal hash =>
    cases literal
    · rw [ExpressionState.nat_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.storeBlob _))) fun _ =>
        Triple.seqHolds (cacheFrame (frame_internRef _)) fun _ =>
        Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ =>
          ⟨fun _ => by simp [hasNatLit], fun h => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go] at h⟩
    · rw [ExpressionState.string_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.storeBlob _))) fun _ =>
        Triple.seqHolds (cacheFrame (frame_internRef _)) fun _ =>
        Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ =>
          ⟨fun h => by simp [ixLits, Ix.Kernel.Reader.literalKinds.go] at h, fun _ => by simp [hasStrLit]⟩
  | proj name field value hash =>
    rw [ExpressionState.projection_step_eq]
    unfold ExpressionState.finishProjection
    exact Triple.seqHolds (cacheFrame (frame_checkedIndex _ _)) fun _ =>
      Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName name))) fun _ =>
      Triple.seqHolds (cacheFrame (frame_lookup _)) fun _ =>
      Triple.seqHolds (cacheFrame (frame_internRef _)) fun _ =>
      Triple.andThen (each value (by simp; omega)) fun v hv =>
      Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ => Triple.returns fun _ _ _ _ =>
        litsFrom_mono hv (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])
  | mdata data value hash =>
    unfold ExpressionState.step compileExprNoSurgeryStep
    dsimp only
    have child := each value (by simp; omega)
    have up : ∀ out, LitsFrom value out → LitsFrom (.mdata data value hash) out := fun out h =>
      litsFrom_mono h (fun h => by simp [hasNatLit, h]) (fun h => by simp [hasStrLit, h])
    split
    · split
      · refine Triple.seqHolds (RefTables.Holds.pure _) fun _ => Triple.andThen child fun v hv => ?_
        split
        · rename_i lowered hl
          exact Triple.returns fun _ _ _ _ => up _ (by unfold LitsFrom; rw [lower_lits hl]; exact hv)
        · exact Triple.throwBind _ _
      · exact Triple.throwBind _ _
    · exact Triple.seqHolds (cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileKVMap _))) fun _ =>
        Triple.andThen child fun v hv => Triple.seqHolds (cacheFrame (frame_alloc _)) fun _ =>
          Triple.returns fun _ _ _ _ => up _ hv
  | fvar name hash =>
    unfold ExpressionState.step compileExprNoSurgeryStep
    exact Triple.throw _
  | mvar name hash =>
    unfold ExpressionState.step compileExprNoSurgeryStep
    exact Triple.throw _

/-- Reading the state returns a state with the cache invariant. -/
theorem get_lits : Triple LI (fun _ _ => True) getBlockState (fun _ _ v => CacheLits v) := by
  intro context before v after hI _ ran
  have hv := ran
  rw [show rawRun getBlockState context before = (.ok before, before) from rfl] at hv
  cases hv
  exact ⟨hI, hI⟩

/-- **The expression compiler returns its source's literals**, under the cache invariant. -/
theorem expression_lits (source : Ix.Expr) :
    Triple LI (fun _ _ => True) (compileExpr source) (fun _ _ r => LitsFrom source r.1) := by
  unfold compileExpr
  induction source using (measure (fun e : Ix.Expr => sizeOf e)).wf.induction with
  | h source ih =>
    rw [compileExprNoSurgery]
    refine Triple.andThen get_lits fun state hstate => ?_
    split
    · rename_i cached hc
      exact Triple.returns fun _ _ _ _ => hstate _ cached hc
    · rw [show (compileExprNoSurgeryStep source fun x _h => compileExprNoSurgery x) =
        ExpressionState.step compileExprNoSurgery source from rfl]
      refine Triple.andThen (step_lits compileExprNoSurgery source fun child smaller => ih child smaller)
        fun value hvalue => ?_
      refine Triple.bind (I := LI) (Q := fun _ _ _ => True) ?_ fun _ => Triple.returns fun _ _ _ _ => hvalue
      intro context before v after hI _ ran
      have hr := ran
      rw [show rawRun (modifyBlockState fun c =>
          { c with exprCache := c.exprCache.insert (↑source) (value.1, value.2) }) context before =
        (.ok (), { before with exprCache := before.exprCache.insert (↑source) (value.1, value.2) }) from rfl] at hr
      cases hr
      refine ⟨fun key out found => ?_, trivial⟩
      rw [Std.HashMap.get?_insert] at found
      split at found
      · rename_i same
        cases found
        rw [← LawfulBEq.eq_of_beq same]
        exact hvalue
      · exact hI key out found


/-! ## The canonical sharing keeps literals -/

/-- Whether an Ixon expression holds a literal of the kind `k` (`true`: `String`, `false`:
`Nat`), as `literalKinds` walks it. -/
abbrev has (k : Bool) (e : Ixon.Expr) : Bool := if k then (ixLits e).2 else (ixLits e).1

theorem has_app (k : Bool) (f a : Ixon.Expr) : has k (.app f a) = (has k f || has k a) := by
  cases k <;> simp [has, ixLits_app]

theorem has_lam (k : Bool) (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    has k (.lam c t b) = (has k t || has k b) := by
  cases k <;> simp [has, ixLits_lam]

theorem has_all (k : Bool) (c : Ixon.BinderContract) (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    has k (.all c r t b) = (has k t || has k b) := by
  cases k <;> simp [has, ixLits_all]

theorem has_letE (k : Bool) (c : Ixon.LetContract) (t v b : Ixon.Expr) :
    has k (.letE c t v b) = (has k t || has k v || has k b) := by
  cases k <;> simp [has, ixLits_letE]

theorem has_prj (k : Bool) (r f : UInt64) (v : Ixon.Expr) : has k (.prj r f v) = has k v := rfl

theorem has_subst (k : Bool) (σ : Nat → Ixon.Expr) :
    ∀ e, has k e = true → has k (Ix.Sharing.Verify.SharingExact.substShares σ e) = true
  | .share i, h => by cases k <;> simp [has, ixLits, Ix.Kernel.Reader.literalKinds.go] at h
  | .prj t f v, h => by
    simp only [Ix.Sharing.Verify.SharingExact.substShares, has_prj] at h ⊢
    exact has_subst k σ v h
  | .app f a, h => by
    have hf := has_subst k σ f
    have ha := has_subst k σ a
    simp only [Ix.Sharing.Verify.SharingExact.substShares, has_app, Bool.or_eq_true] at h ⊢
    exact h.imp hf ha
  | .lam c t b, h => by
    have ht := has_subst k σ t
    have hb := has_subst k σ b
    simp only [Ix.Sharing.Verify.SharingExact.substShares, has_lam, Bool.or_eq_true] at h ⊢
    exact h.imp ht hb
  | .all c r t b, h => by
    have ht := has_subst k σ t
    have hb := has_subst k σ b
    simp only [Ix.Sharing.Verify.SharingExact.substShares, has_all, Bool.or_eq_true] at h ⊢
    exact h.imp ht hb
  | .letE c t v b, h => by
    have ht := has_subst k σ t
    have hv := has_subst k σ v
    have hb := has_subst k σ b
    simp only [Ix.Sharing.Verify.SharingExact.substShares, has_letE, Bool.or_eq_true] at h ⊢
    exact h.imp (fun h => h.imp ht hv) hb
  | .sort _, h => h
  | .var _, h => h
  | .ref _ _, h => h
  | .recur _ _, h => h
  | .str _, h => h
  | .nat _, h => h

open Ix.Sharing.Exact (Dag Node Head) in
/-- In a model of a well-formed DAG, a node's term has its children's literals. -/
theorem has_child (k : Bool) {dag : Dag} {E : Nat → Ixon.Expr}
    (model : Ix.Sharing.Verify.SharingExact.DagModel dag E)
    (arity : Ix.Sharing.Verify.SharingExact.NodeArity dag.nodes) {t c : Nat}
    (hc : c < (dag.node t).children.size) (h : has k (E ((dag.node t).child c)) = true) :
    has k (E t) = true := by
  have ht : t < dag.size := by
    by_contra hn
    have hd : dag.node t = default := by
      simp only [Dag.node, Dag.size] at hn ⊢
      rw [Array.getElem?_eq_none (by omega)]
      rfl
    rw [hd] at hc
    have hz : (default : Node).children.size = 0 := rfl
    omega
  have harity := arity t ht
  rw [← Ix.Sharing.Verify.UniformModel.dag_node_eq ht] at harity
  rw [model t]
  generalize dag.node t = n at hc h harity
  obtain ⟨head, children⟩ := n
  simp only at hc harity
  rw [harity] at hc
  cases head <;> simp only [Head.arity] at hc
  all_goals first
    | omega
    | (simp only [Node.toExpr, has_prj]
       obtain rfl : c = 0 := by omega
       exact h)
    | (simp only [Node.toExpr, has_app, has_lam, has_all, Bool.or_eq_true]
       rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
       · exact .inl h
       · exact .inr h)
    | (simp only [Node.toExpr, has_letE, Bool.or_eq_true]
       rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
       · exact .inl (.inl h)
       · exact .inl (.inr h)
       · exact .inr h)

open Ix.Sharing.Exact (Dag) in
/-- A descendant's literals are its ancestor's. -/
theorem has_desc (k : Bool) {dag : Dag} {E : Nat → Ixon.Expr}
    (model : Ix.Sharing.Verify.SharingExact.DagModel dag E)
    (arity : Ix.Sharing.Verify.SharingExact.NodeArity dag.nodes) {r y : Nat}
    (desc : Ix.Sharing.Verify.SharingExact.Desc dag r y) (h : has k (E y) = true) : has k (E r) = true := by
  induction desc with
  | refl => exact h
  | child c hc _ ih => exact has_child k model arity hc (ih h)

theorem forall₂_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, h => nomatch h
  | x :: _, _ :: _, .cons hr rest, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, hr⟩
    · obtain ⟨x', hx', r'⟩ := forall₂_right rest y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', r'⟩

/-- **The canonical sharing keeps literals**: a literal of the built constant's sharing table
or roots is a literal of one of the input roots. Every table entry expands to the term of a
DAG node, every node descends from a root (`ExpandedDomain.reachable`), and the roots expand
to the inputs. -/
theorem build_has (k : Bool) {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo}
    {refs : Array Address} {univs : Array Ixon.Univ} {out : Ixon.Constant}
    (ran : buildConstantWithSharing limits info refs univs = .ok out) :
    ∀ e ∈ out.sharing.toList ++ (constantInfoRootExprs out.info).toList, has k e = true →
      ∃ src ∈ (constantInfoRootExprs info).toList, has k src = true := by
  obtain ⟨r, info', sharedRan, -, written, rfl⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  have rewritten : Ix.Sharing.Exact.withRoots info r.result.roots = .ok info' := by
    simp only [Ix.CompileM.withRootExprs] at written
    cases w : Ix.Sharing.Exact.withRoots info r.result.roots with
    | error error => rw [w] at written; cases written
    | ok value => rw [w] at written; cases written; rfl
  have roots' : constantInfoRootExprs info' = r.result.roots := by
    rw [Ix.Sharing.Verify.constantInfoRootExprs_eq_roots info', (SharingRoots.withRoots_inv rewritten).1]
  obtain ⟨expanded, before, after⟩ := Ix.Sharing.Verify.CanonicalProduction.canonicalSharingTiered_parts sharedRan
  have domain := Ix.Sharing.Family.familyExpanded_domain after
  have output := Ix.Sharing.Family.familyExpanded_output_of_success after
  have model := Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf domain.wf
  obtain ⟨entries, rootsMeaning⟩ := output.meaning _ model
  have sources := Ix.Sharing.Verify.CanonicalMeaning.expand_root_terms limits _ expanded before
  have rootSrc : ∀ x ∈ expanded.roots.toList,
      has k (Ix.Sharing.Verify.SharingExact.termOf expanded.dag.nodes x) = true →
        ∃ src ∈ (constantInfoRootExprs info).toList, has k src = true := by
    intro x hx hh
    refine ⟨_, ?_, hh⟩
    rw [← sources, Array.toList_map]
    exact List.mem_map_of_mem hx
  intro e he hh
  rw [Array.toList_append.symm, roots'] at he
  rcases (by simpa using he : e ∈ r.result.sharing ∨ e ∈ r.result.roots) with he | he
  · obtain ⟨j, hj', rfl⟩ := Array.getElem_of_mem he
    have hsub := has_subst k
      (fun i => Ix.Sharing.Verify.SharingExact.termOf expanded.dag.nodes r.result.tableTerms[i]!) _ hh
    rw [entries j hj'] at hsub
    by_cases hin : r.result.tableTerms[j]! < expanded.dag.size
    · obtain ⟨root, hroot, hdesc⟩ := domain.reachable _ hin
      exact rootSrc root hroot (has_desc k model domain.wf.arity hdesc hsub)
    · exfalso
      rw [model] at hsub
      have hd : expanded.dag.node r.result.tableTerms[j]! = default := by
        simp only [Ix.Sharing.Exact.Dag.node, Ix.Sharing.Exact.Dag.size] at hin ⊢
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [hd, show ∀ F, (default : Ix.Sharing.Exact.Node).toExpr F = Ixon.Expr.sort 0 from fun _ => rfl] at hsub
      cases k <;> simp [has, ixLits, Ix.Kernel.Reader.literalKinds.go] at hsub
  · obtain ⟨x, hx, hxe⟩ := forall₂_right rootsMeaning e (Array.mem_toList_iff.mpr he)
    have hsub := has_subst k
      (fun i => Ix.Sharing.Verify.SharingExact.termOf expanded.dag.nodes r.result.tableTerms[i]!) _ hh
    rw [hxe] at hsub
    exact rootSrc x hx hsub

end Ix.Cert.LiteralSources

/--
info: 'Ix.Cert.LiteralSources.expression_lits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LiteralSources.expression_lits

/--
info: 'Ix.Cert.LiteralSources.build_has' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LiteralSources.build_has
