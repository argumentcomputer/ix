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
accumulator's condition (`Triple.forIn_list`).

**The steps.**
* `expression_lits`: the expression compiler returns a literal of a kind only where its source
  term has one.
* `build_has`: the canonical sharing keeps literals, and `literalKinds_has`: a record's literal
  is in its sharing table or its roots.
* The payloads (`definitionData_lits` … `inductiveData_lits`, `member_lits`, `members_lits`): a
  payload's roots are its source terms' compiled forms. The finishers return the compiled
  expressions they are given, and the preseed leaves the cache alone (`frame_preseed`).
* `runBlock_lits`: a compiled block's record holds only literals of the terms its compile reads
  under its members' names (`ReadTerm`, `RefTables.TermOf`), the same walk as
  `RefTables.runBlock_refs`. -/

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
    ((hasNatLit (Ix.CompileM.decomposeApps.go expr args).1 = true → hasNatLit whole = true) ∧
      (hasStrLit (Ix.CompileM.decomposeApps.go expr args).1 = true → hasStrLit whole = true)) ∧
    ∀ x ∈ (Ix.CompileM.decomposeApps.go expr args).2,
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
    refine Triple.andThen (each _ (Ix.CompileM.decomposeApps_app_head_lt fn arg hash)) fun head hhead => ?_
    rw [forIn'_eq_forIn _ _ _ (fun x acc => ExpressionState.appBody compile acc x) (fun _ _ _ => rfl)]
    rw [← Array.forIn_toList]
    refine Triple.bind (Triple.pre (Triple.forIn_list (fun acc : Ixon.Expr × UInt64 =>
        LitsFrom (.app fn arg hash) acc.1) _ _ _ fun x member acc => ?_) fun _ _ _ _ =>
          litsFrom_mono hhead parts.1.1 parts.1.2) fun spine => Triple.returns fun _ _ _ h => h
    have hx := parts.2 x (by
      have hm : x ∈ (Ix.CompileM.decomposeApps (.app fn arg hash)).2 := by simpa using member
      exact hm)
    unfold ExpressionState.appBody
    refine Triple.of_imp fun hacc => ?_
    refine Triple.andThen (each x (Ix.CompileM.decomposeApps_app_mem_lt fn arg hash (by simpa using member)))
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
    unfold ExpressionState.step compileExprStep
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
    unfold ExpressionState.step compileExprStep
    exact Triple.throw _
  | mvar name hash =>
    unfold ExpressionState.step compileExprStep
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
  induction source using (measure (fun e : Ix.Expr => sizeOf e)).wf.induction with
  | h source ih =>
    rw [compileExpr]
    refine Triple.andThen get_lits fun state hstate => ?_
    split
    · rename_i cached hc
      exact Triple.returns fun _ _ _ _ => hstate _ cached hc
    · rw [show (compileExprStep source fun x _h => compileExpr x) =
        ExpressionState.step compileExpr source from rfl]
      refine Triple.andThen (step_lits compileExpr source fun child smaller => ih child smaller)
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


/-! ## A record's literal kinds come from its table and roots -/

/-- The kind `k` component of a pair of literal kinds (`true`: `String`, `false`: `Nat`). -/
abbrev kindOf (k : Bool) (p : Bool × Bool) : Bool := if k then p.2 else p.1

theorem foldl_go (l : List Ixon.Expr) (acc : Bool × Bool) :
    l.foldl Ix.Kernel.Reader.literalKinds.go acc =
      (acc.1 || l.any (fun e => (ixLits e).1), acc.2 || l.any (fun e => (ixLits e).2)) := by
  induction l generalizing acc with
  | nil => simp
  | cons e rest ih =>
    rw [List.foldl_cons, ih, go_spec]
    simp [Bool.or_assoc]

theorem fold_has (k : Bool) (xs : Array Ixon.Expr)
    (h : kindOf k (xs.foldl Ix.Kernel.Reader.literalKinds.go (false, false)) = true) :
    ∃ e ∈ xs.toList, has k e = true := by
  rw [← Array.foldl_toList, foldl_go] at h
  cases k
  · simp only [kindOf, Bool.false_or, Bool.false_eq_true, ↓reduceIte, List.any_eq_true] at h
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, he, h⟩
  · simp only [kindOf, Bool.false_or, ↓reduceIte, List.any_eq_true] at h
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, he, h⟩

/-- **A record's literal of a kind is in its sharing table or its roots.** -/
theorem literalKinds_has (k : Bool) (c : Ixon.Constant)
    (h : kindOf k (Ix.Kernel.Reader.literalKinds c) = true) :
    ∃ e ∈ c.sharing.toList ++ (constantInfoRootExprs c.info).toList, has k e = true := by
  rcases c with ⟨info, sharing, refs, univs⟩
  unfold Ix.Kernel.Reader.literalKinds at h
  obtain ⟨e, he, hk⟩ := fold_has k _ h
  clear h
  refine ⟨e, ?_, hk⟩
  simp only [Array.toList_append, List.mem_append] at he ⊢
  rcases he with he | he
  · exact .inl he
  · right
    cases info <;> simp_all [constantInfoRootExprs, mutConstRootExprs]
    obtain ⟨m, hm, he⟩ := he
    exact ⟨m, hm, by cases m <;> simp_all⟩

/-! ## Terms a compiled expression's literals come from -/

/-- Whether a source term holds a literal of the kind `k`. -/
abbrev hasK (k : Bool) (s : Ix.Expr) : Bool := if k then hasStrLit s else hasNatLit s

/-- **A compiled expression's literals are among the terms `T` holds of.** -/
def LitsIn (T : Ix.Expr → Prop) (e : Ixon.Expr) : Prop := ∀ k, has k e = true → ∃ s, T s ∧ hasK k s = true

theorem LitsIn.of_from {s : Ix.Expr} {e : Ixon.Expr} {T : Ix.Expr → Prop} (h : LitsFrom s e) (hs : T s) :
    LitsIn T e := by
  intro k hk
  refine ⟨s, hs, ?_⟩
  cases k
  · exact h.1 hk
  · exact h.2 hk

/-! ## Leaves that keep the cache invariant -/

theorem hold_takeArena : Holds LI takeArena :=
  cacheFrame (by unfold takeArena; exact Preserves.modifyGet _ _ fun _ => rfl)

theorem hold_takeUnivPatches : Holds LI takeUnivPatches :=
  cacheFrame (by unfold takeUnivPatches; exact Preserves.modifyGet _ _ fun _ => rfl)

theorem hold_resetArena : Holds LI resetArena :=
  cacheFrame (by unfold resetArena; exact Preserves.modify _ _ fun _ => rfl)

theorem hold_recordDefHints (name : Ix.Name) (hints : Lean.ReducibilityHints) : Holds LI (recordDefHints name hints) :=
  cacheFrame (by unfold recordDefHints; exact Preserves.modify _ _ fun _ => rfl)

theorem hold_mutCtxAddrs : Holds LI getMutCtxAddrs :=
  cacheFrame (by unfold getMutCtxAddrs; exact Preserves.bind (Preserves.read _) fun _ => Preserves.pure _ _)

/-- Clearing the cache makes the invariant hold. -/
theorem hold_clear : Holds LI clearExprCache := by
  intro context before v after _ _ ran
  have hr := ran
  rw [show rawRun clearExprCache context before = (.ok (), { before with exprCache := {} }) from rfl] at hr
  cases hr
  refine ⟨fun key value found => ?_, trivial⟩
  simp at found

theorem hold_inductiveMeta : Holds LI takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  exact Holds.seq hold_takeArena fun _ =>
    Holds.seq hold_takeUnivPatches fun _ => Holds.seq hold_clear fun _ => Holds.pure _

theorem Triple.withUnivCtxL (params : List Ix.Name) {α : Type} {action : CompileM α}
    {Q : CompileEnv → BlockState → α → Prop} (h : Triple LI (fun _ _ => True) action Q) :
    Triple LI (fun _ _ => True) (withUnivCtx params action) Q := by
  unfold Ix.CompileM.withUnivCtx
  exact Triple.seqHolds (cacheFrame (Preserves.modify _ _ fun _ => rfl)) fun _ => Triple.withBlockEnv _ h

/-! ## The preseed keeps the cache -/

theorem frame_compileUniv (source : Ix.Level) : Preserves cacheView (compileUniv source) :=
  fun context before => by
    have same := congrArg BlockState.exprCache (CanonUnivCache.compileUniv_frame source context before)
    exact same

theorem frame_blob (bytes : ByteArray) : Preserves cacheView (storeBlob bytes) :=
  fun context before => by
    have same := congrArg BlockState.exprCache (BlobWrites.storeBlob_preserves bytes context before).1
    exact same

theorem frame_collectUnivs (levels : List Ix.Level) (initial : Array Ixon.Univ) :
    Preserves cacheView (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact Preserves.bind (frame_compileUniv level) (fun value => ih (initial.push value))

theorem frame_structural (context : Address) (mutualContext : MutCtx) (params : List Ix.Name)
    (expr : Ix.Expr) (acc : ExprTableCollection) :
    Preserves cacheView (collectExprTablesStructural context mutualContext params expr acc) := by
  induction expr generalizing acc
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases acc with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact Preserves.pure _ _
    · with_reducible repeat' first
        | exact Preserves.pure _ _
        | exact Preserves.throw _ _
        | exact frame_compileUniv _
        | exact frame_lookup _
        | exact frame_blob _
        | exact frame_collectUnivs _ _
        | refine Preserves.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem frame_collectRoots (roots : List (Ix.Expr × List Ix.Name)) (initial : ExprTableCollection) :
    Preserves cacheView (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons root rest ih =>
    rcases root with ⟨expr, params⟩
    rw [collectPreseedExprs]
    refine Preserves.bind ?_ (fun next => ih next)
    unfold Ix.CompileM.withUnivCtx collectExprTables
    exact Preserves.bind (Preserves.modify _ _ (fun _ => rfl)) (fun _ => Preserves.withBlockEnv (update := _)
      (Preserves.bind (Preserves.read _) fun block => frame_structural _ block.mutCtx block.univCtx expr initial))

theorem frame_internRefs (refs : List Address) (previous : Option Address) :
    Preserves cacheView (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Preserves.pure _ ()
  | cons address rest ih =>
    unfold internPreseedRefs
    split
    · unfold Functor.discard
      exact Preserves.bind (Preserves.bind (frame_internRef address) fun _ => Preserves.pure _ ()) fun _ => ih _
    · exact ih _

theorem frame_canonUnivs (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Preserves cacheView (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons value rest ih =>
    unfold canonPreseedUnivs
    refine Preserves.bind ?_ (fun canonical => ih (initial.push canonical))
    intro context before
    rw [CanonUnivCache.canonUnivCached_run]
    cases before.canonUnivCache.get? value <;> rfl

theorem frame_internUniv (univ : Ixon.Univ) : Preserves cacheView (internUniv univ) := by
  intro context before
  cases found : before.univsIndex.get? univ with
  | some index => rw [Interning.internUniv_hit univ context before found]
  | none =>
    rw [Interning.internUniv_miss univ context before found]
    split
    · rfl
    · rw [Interning.checkedTableCount_state]

theorem frame_internUnivs (entries : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Preserves cacheView (internPreseedUnivs entries previous) := by
  induction entries generalizing previous with
  | nil => exact Preserves.pure _ ()
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    unfold internPreseedUnivs
    split
    · unfold Functor.discard
      exact Preserves.bind (Preserves.bind (frame_internUniv value) fun _ => Preserves.pure _ ()) fun _ => ih _
    · exact ih _

/-- **The preseed leaves the expression cache alone.** -/
theorem frame_preseed (roots : Array (Ix.Expr × List Ix.Name)) : Preserves cacheView (preseedExprTables roots) := by
  unfold preseedExprTables
  refine Preserves.bind (frame_collectRoots _ _) fun collection => ?_
  obtain ⟨refs, univs, seen⟩ := collection
  refine Preserves.bind (frame_internRefs _ none) fun _ => ?_
  refine Preserves.bind (frame_canonUnivs _ _) fun canonical => ?_
  refine Preserves.bind ?_ fun _ => ?_
  · unfold checkPreseedUnivs
    split
    · exact Preserves.pure _ ()
    · exact Preserves.throw _ _
  · exact Preserves.bind (frame_internUnivs _ none) fun _ => Preserves.modify _ _ fun _ => rfl

/-! ## The finishers return the compiled expressions they are given -/

/-- The finishers' steps keep the cache invariant; the returned payload holds the given
expressions. -/
local macro "lits_finish" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Holds.pure _
    | exact Triple.returns fun _ _ _ _ => ⟨rfl, rfl⟩
    | exact Triple.returns fun _ _ _ _ => rfl
    | exact hold_takeArena
    | exact hold_takeUnivPatches
    | exact hold_clear
    | exact cacheFrame (frame_checkedCount _ _)
    | exact cacheFrame (frame_checkedIndex _ _)
    | exact cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileName _))
    | exact cacheFrame (frame_namesBlobs (Serializers.NamesBlobs.compileNames _))
    | exact hold_recordDefHints _ _
    | exact hold_mutCtxAddrs
    | exact cacheFrame (Preserves.read _)
    | refine Triple.seqHolds ?_ (fun _ => ?_)
    | dsimp only)

theorem finishDefinitionData_value (source : Ix.Def) (type : Ixon.Expr) (typeRoot : UInt64)
    (value : Ixon.Expr) (valueRoot : UInt64) :
    Triple LI (fun _ _ => True) (finishDefinitionDataCompilation source type typeRoot value valueRoot)
      (fun _ _ r => r.1.typ = type ∧ r.1.value = value) := by
  unfold finishDefinitionDataCompilation
  lits_finish

theorem finishAxiom_value (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) :
    Triple LI (fun _ _ => True) (finishAxiomCompilation source type root) (fun _ _ r => r.1.typ = type) := by
  unfold finishAxiomCompilation
  lits_finish

theorem finishQuotient_value (source : QuotVal) (type : Ixon.Expr) (root : UInt64) :
    Triple LI (fun _ _ => True) (finishQuotientCompilation source type root) (fun _ _ r => r.1.typ = type) := by
  unfold finishQuotientCompilation
  lits_finish

theorem finishRecursor_value (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) :
    Triple LI (fun _ _ => True) (finishRecursorCompilation source type root rules)
      (fun _ _ r => r.1.typ = type ∧ r.1.rules = rules.rules) := by
  unfold finishRecursorCompilation
  lits_finish

theorem finishConstructor_value (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Triple LI (fun _ _ => True) (finishConstructorCompilation source type root) (fun _ _ r => r.1.typ = type) := by
  unfold finishConstructorCompilation
  lits_finish

theorem finishInductive_value (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Triple LI (fun _ _ => True) (finishInductiveCompilation source type root metadata constructors)
      (fun _ _ r => r.1.typ = type ∧ r.1.ctors = constructors.ctors) := by
  unfold finishInductiveCompilation
  lits_finish

theorem finishInductiveData_value (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Triple LI (fun _ _ => True) (finishInductiveDataCompilation source type root metadata constructors)
      (fun _ _ r => r.1.typ = type ∧ r.1.ctors = constructors.ctors) := by
  unfold finishInductiveDataCompilation
  lits_finish

/-! ## The payloads hold their sources' compiled terms -/

theorem definitionData_lits {T : Ix.Expr → Prop} (d : Ix.Def) (ht : T d.type) (hv : T d.value) :
    Triple LI (fun _ _ => True) (compileDefinitionData d)
      (fun _ _ r => ∀ e ∈ mutConstRootExprs (.defn r.1), LitsIn T e) := by
  unfold compileDefinitionData
  refine Triple.withCurrent _ (Triple.withUnivCtxL _ ?_)
  refine Triple.seqHolds hold_resetArena fun _ => ?_
  refine Triple.andThen (expression_lits d.type) fun type htype => ?_
  rcases type with ⟨te, tr⟩
  dsimp only
  refine Triple.andThen (expression_lits d.value) fun value hvalue => ?_
  rcases value with ⟨ve, vr⟩
  dsimp only
  refine Triple.post (finishDefinitionData_value d te tr ve vr) fun _ _ r _ hr => ?_
  intro e he
  simp only [mutConstRootExprs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [hr.1]; exact LitsIn.of_from htype ht
  · rw [hr.2]; exact LitsIn.of_from hvalue hv

theorem axiom_lits {T : Ix.Expr → Prop} (a : AxiomVal) (ht : T a.cnst.type) :
    Triple LI (fun _ _ => True) (compileAxiom a) (fun _ _ r => LitsIn T r.1.typ) := by
  unfold compileAxiom
  refine Triple.withCurrent _ (Triple.withUnivCtxL _ ?_)
  refine Triple.seqHolds hold_resetArena fun _ => ?_
  refine Triple.andThen (expression_lits a.cnst.type) fun type htype => ?_
  rcases type with ⟨te, tr⟩
  dsimp only
  exact Triple.post (finishAxiom_value a te tr) fun _ _ r _ hr => by rw [hr]; exact LitsIn.of_from htype ht

theorem quotient_lits {T : Ix.Expr → Prop} (q : QuotVal) (ht : T q.cnst.type) :
    Triple LI (fun _ _ => True) (compileQuotient q) (fun _ _ r => LitsIn T r.1.typ) := by
  unfold compileQuotient
  refine Triple.withCurrent _ (Triple.withUnivCtxL _ ?_)
  refine Triple.seqHolds hold_resetArena fun _ => ?_
  refine Triple.andThen (expression_lits q.cnst.type) fun type htype => ?_
  rcases type with ⟨te, tr⟩
  dsimp only
  exact Triple.post (finishQuotient_value q te tr) fun _ _ r _ hr => by rw [hr]; exact LitsIn.of_from htype ht

theorem rules_lits {T : Ix.Expr → Prop} (sources : List RecursorRule) (initial : RecursorRuleCompileState)
    (hT : ∀ rule ∈ sources, T rule.rhs) :
    Triple LI (fun _ _ => ∀ x ∈ initial.rules.toList, LitsIn T x.rhs) (compileRecursorRules sources initial)
      (fun _ _ r => ∀ x ∈ r.rules.toList, LitsIn T x.rhs) := by
  induction sources generalizing initial with
  | nil => exact Triple.returns fun _ _ _ h => h
  | cons source rest ih =>
    rw [compileRecursorRules]
    refine Triple.of_imp fun hinit => ?_
    refine Triple.andThen (Q := fun out => LitsIn T out.1.rhs) ?_ fun out hout => ?_
    · unfold compileRecursorRule
      refine Triple.andThen (expression_lits source.rhs) fun rhs hr => ?_
      rcases rhs with ⟨e, root⟩
      dsimp only
      refine Triple.seqHolds (cacheFrame (frame_checkedCount _ _)) fun _ => ?_
      exact Triple.returns fun _ _ _ _ => LitsIn.of_from hr (hT source (by simp))
    · rcases out with ⟨ixonRule, ctorAddr, ruleRoot⟩
      dsimp only
      refine Triple.pre (ih _ (fun r hr => hT r (List.mem_cons_of_mem _ hr))) fun _ _ _ _ => ?_
      intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hinit x hx
      · exact hout

theorem recursor_lits {T : Ix.Expr → Prop} (r : RecursorVal) (ht : T r.cnst.type)
    (hr : ∀ rule ∈ r.rules.toList, T rule.rhs) :
    Triple LI (fun _ _ => True) (compileRecursor r)
      (fun _ _ out => ∀ e ∈ mutConstRootExprs (.recr out.1), LitsIn T e) := by
  unfold compileRecursor
  refine Triple.withCurrent _ (Triple.withUnivCtxL _ ?_)
  refine Triple.seqHolds hold_resetArena fun _ => ?_
  refine Triple.andThen (expression_lits r.cnst.type) fun type htype => ?_
  rcases type with ⟨te, tr⟩
  dsimp only
  refine Triple.andThen (Triple.pre (rules_lits r.rules.toList {} hr) fun _ _ _ _ x hx => by simp at hx)
    fun rules hrules => ?_
  refine Triple.post (finishRecursor_value r te tr rules) fun _ _ out _ hout => ?_
  intro e he
  simp only [mutConstRootExprs, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨x, hx, rfl⟩
  · rw [hout.1]; exact LitsIn.of_from htype ht
  · rw [hout.2] at hx; exact hrules x hx

theorem constructors_lits {T : Ix.Expr → Prop} (sources : List ConstructorVal)
    (initial : InductiveConstructorCompileState) (hT : ∀ c ∈ sources, T c.cnst.type) :
    Triple LI (fun _ _ => ∀ x ∈ initial.ctors.toList, LitsIn T x.typ) (compileInductiveConstructors sources initial)
      (fun _ _ r => ∀ x ∈ r.ctors.toList, LitsIn T x.typ) := by
  induction sources generalizing initial with
  | nil => exact Triple.returns fun _ _ _ h => h
  | cons source rest ih =>
    rw [compileInductiveConstructors]
    refine Triple.of_imp fun hinit => ?_
    refine Triple.andThen (Q := fun out => LitsIn T out.1.typ) ?_ fun out hout => ?_
    · unfold compileConstructor
      refine Triple.withCurrent _ ?_
      refine Triple.seqHolds hold_resetArena fun _ => ?_
      refine Triple.andThen (expression_lits source.cnst.type) fun type htype => ?_
      rcases type with ⟨te, tr⟩
      dsimp only
      exact Triple.post (finishConstructor_value source te tr) fun _ _ r _ hr => by
        rw [hr]; exact LitsIn.of_from htype (hT source (by simp))
    · rcases out with ⟨ctor, ctorMeta, ctorExpr⟩
      dsimp only
      refine Triple.pre (ih _ (fun c hc => hT c (List.mem_cons_of_mem _ hc))) fun _ _ _ _ => ?_
      intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hinit x hx
      · exact hout

theorem inductiveData_lits {T : Ix.Expr → Prop} (i : Ix.Ind) (ht : T i.type)
    (hc : ∀ c ∈ i.ctors.toList, T c.cnst.type) :
    Triple LI (fun _ _ => True) (compileInductiveData i)
      (fun _ _ r => ∀ e ∈ mutConstRootExprs (.indc r.1), LitsIn T e) := by
  unfold compileInductiveData
  refine Triple.withCurrent _ (Triple.withUnivCtxL _ ?_)
  refine Triple.seqHolds hold_resetArena fun _ => ?_
  refine Triple.andThen (expression_lits i.type) fun type htype => ?_
  rcases type with ⟨te, tr⟩
  dsimp only
  refine Triple.seqHolds hold_inductiveMeta fun metadata => ?_
  refine Triple.andThen (Triple.pre (constructors_lits i.ctors.toList _ hc) fun _ _ _ _ x hx => by simp at hx)
    fun built hbuilt => ?_
  refine Triple.post (finishInductiveData_value i te tr metadata built) fun _ _ out _ hout => ?_
  intro e he
  simp only [mutConstRootExprs, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨x, hx, rfl⟩
  · rw [hout.1]; exact LitsIn.of_from htype ht
  · rw [hout.2] at hx; exact hbuilt x hx

/-- `T` holds of every term of a mutual member. -/
def MutLits (T : Ix.Expr → Prop) : MutConst → Prop
  | .defn d => T d.type ∧ T d.value
  | .indc i => T i.type ∧ ∀ c ∈ i.ctors.toList, T c.cnst.type
  | .recr r => T r.cnst.type ∧ ∀ rule ∈ r.rules.toList, T rule.rhs

theorem member_lits {T : Ix.Expr → Prop} (c : MutConst) (hc : MutLits T c) :
    Triple LI (fun _ _ => True) (compileMutConstMember c)
      (fun _ _ m => ∀ e ∈ mutConstRootExprs m.payload, LitsIn T e) := by
  cases c <;> unfold compileMutConstMember
  · refine Triple.andThen (Triple.withCurrent _ (definitionData_lits _ hc.1 hc.2)) fun out hout => ?_
    rcases out with ⟨defn, md, te, ve⟩
    exact Triple.returns fun _ _ _ _ => hout
  · refine Triple.andThen (Triple.withCurrent _ (inductiveData_lits _ hc.1 hc.2)) fun out hout => ?_
    rcases out with ⟨ind, md, pairs, exprs⟩
    exact Triple.returns fun _ _ _ _ => hout
  · refine Triple.andThen (Triple.withCurrent _ (recursor_lits _ hc.1 hc.2)) fun out hout => ?_
    rcases out with ⟨recursor, md, te⟩
    exact Triple.returns fun _ _ _ _ => hout

/-- Every retained payload's roots have their literals among `T`'s terms. -/
abbrev PayloadsLits (T : Ix.Expr → Prop) (state : MutConstCompileState) : Prop :=
  ∀ p ∈ state.payloads.toList, ∀ e ∈ mutConstRootExprs p, LitsIn T e

theorem members_lits {T : Ix.Expr → Prop} (sources : List MutConst) (initial : MutConstCompileState)
    (hc : ∀ c ∈ sources, MutLits T c) :
    Triple LI (fun _ _ => PayloadsLits T initial) (compileMutConstMembers sources initial)
      (fun _ _ r => PayloadsLits T r) := by
  induction sources generalizing initial with
  | nil => exact Triple.returns fun _ _ _ h => h
  | cons source rest ih =>
    rw [compileMutConstMembers]
    refine Triple.of_imp fun hinit => ?_
    refine Triple.andThen (member_lits source (hc source (by simp))) fun member hmember => ?_
    refine Triple.pre (ih _ fun c h => hc c (List.mem_cons_of_mem _ h)) fun _ _ _ _ => ?_
    intro p hp
    simp only [MutConstCompileState.addMember, Array.toList_push, List.mem_append,
      List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hinit p hp
    · exact hmember

/-! ## The block's record holds its payload's literals -/

/-- **The block record's literals are its payload roots'.** -/
abbrev BlockLits (T : Ix.Expr → Prop) (r : BlockResult) : Prop :=
  ∀ k, kindOf k (Ix.Kernel.Reader.literalKinds r.block) = true → ∃ s, T s ∧ hasK k s = true

theorem built_lits {T : Ix.Expr → Prop} {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo}
    {refs : Array Address} {univs : Array Ixon.Univ} {block : Ixon.Constant}
    (ran : buildConstantWithSharing limits info refs univs = .ok block)
    (roots : ∀ e ∈ (constantInfoRootExprs info).toList, LitsIn T e) :
    ∀ k, kindOf k (Ix.Kernel.Reader.literalKinds block) = true → ∃ s, T s ∧ hasK k s = true := by
  intro k hk
  obtain ⟨e, he, hke⟩ := literalKinds_has k block hk
  obtain ⟨src, hsrc, hks⟩ := build_has k ran e he hke
  exact roots src hsrc k hks

theorem finishConstant_lits {T : Ix.Expr → Prop} (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (roots : ∀ e ∈ (constantInfoRootExprs info).toList, LitsIn T e) :
    Triple LI (fun _ _ => True) (finishConstantInfoWithSharing info blockMeta) (fun _ _ r => BlockLits T r) := by
  intro context before value after hI _ ran
  unfold finishConstantInfoWithSharing finishConstantWithSharing at ran
  obtain ⟨cache, mid, hc, ran⟩ := bind_ok ran
  have hc : (Except.ok before, before) = (Except.ok cache, mid) := hc
  cases hc
  obtain ⟨block, mid', hb, done⟩ := bind_ok ran
  have same : mid' = before := by
    have := RefTables.buildBlockConstant_preserves info before.refs before.univs context before
    rw [hb] at this
    exact this
  subst same
  rw [rawRun_pure] at done
  cases done
  exact ⟨hI, built_lits (BlockLayout.buildBlockConstant_ok hb) roots⟩

theorem mutual_lits {T : Ix.Expr → Prop} {limits : Ix.Sharing.Exact.Limits} {classes : List MutConst}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult} (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out)
    (roots : ∀ p ∈ payloads.toList, ∀ e ∈ mutConstRootExprs p, LitsIn T e) : BlockLits T out := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    refine built_lits hb fun e he => ?_
    rcases payloads with ⟨l⟩
    rcases l with _ | ⟨m, _ | ⟨m₂, rest⟩⟩
    · cases hs
    rotate_left
    · cases hs
    cases m with
    | indc i => cases hs
    | recr r =>
      cases hs
      exact roots (.recr r) (by simp) e (by simpa [constantInfoRootExprs] using he)
    | defn d =>
      cases hs
      exact roots (.defn d) (by simp) e (by simpa [constantInfoRootExprs] using he)
  | none =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    refine built_lits hb fun e he => ?_
    simp only [constantInfoRootExprs, List.toList_toArray, List.mem_flatMap] at he
    obtain ⟨p, hp, he⟩ := he
    exact roots p hp e he

theorem mutConsts_lits {T : Ix.Expr → Prop} (classes : List MutConst)
    (hc : ∀ c ∈ classes, MutLits T c) :
    Triple LI (fun _ _ => True) (compileMutConsts classes)
      (fun _ _ out => ∀ p ∈ out.1.toList, ∀ e ∈ mutConstRootExprs p, LitsIn T e) := by
  unfold compileMutConsts
  exact Triple.bind (Triple.pre (members_lits classes {} hc) fun _ _ _ _ p hp => by simp at hp)
    fun state => Triple.returns fun _ _ _ h => h

theorem mutualPayload_lits {T : Ix.Expr → Prop} (classes : List MutConst)
    (hc : ∀ c ∈ classes, MutLits T c) :
    Triple LI (fun _ _ => True) (compileMutualPayload classes) (fun _ _ r => BlockLits T r) := by
  unfold compileMutualPayload
  refine Triple.andThen (mutConsts_lits classes hc) fun compiled hcompiled => ?_
  obtain ⟨payloads, roots, metas⟩ := compiled
  dsimp only
  intro context before value after hI _ ran
  obtain ⟨same, -, built⟩ := ProjectionLayout.finish_mutual_ok context classes payloads metas ran
  subst same
  exact ⟨hI, mutual_lits built hcompiled⟩

theorem mutualBlock_lits {T : Ix.Expr → Prop} (classes : List MutConst)
    (hc : ∀ c ∈ classes, MutLits T c) :
    Triple LI (fun _ _ => True) (compileMutualBlock classes) (fun _ _ r => BlockLits T r) := by
  unfold compileMutualBlock
  dsimp only
  refine Triple.withMutCtx _ ?_
  exact Triple.seqHolds (cacheFrame (frame_preseed _)) fun _ => mutualPayload_lits classes hc

/-! ## A block's literals come from the terms its compile reads -/

/-- **A term a block compile reads under a name `N` admits**: one of the constant's terms, or the
type of a constructor an inductive lists (`RefTables.TermOf`). -/
abbrev ReadTerm (E : Ix.Environment) (N : Ix.Name → Prop) (e : Ix.Expr) : Prop :=
  ∃ x, N x ∧ RefTables.TermOf E x e

theorem cacheLits_empty : CacheLits ({} : BlockState) := by
  intro key value found
  have empty : ({} : BlockState).exprCache = {} := rfl
  rw [empty] at found
  simp at found

theorem definitionDataInfo_lits {T : Ix.Expr → Prop} (d : Ix.Def) (ht : T d.type) (hv : T d.value) :
    Triple LI (fun _ _ => True) (compileDefinitionDataInfo d) (fun _ _ r => BlockLits T r) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  refine Triple.seqHolds (cacheFrame (frame_preseed _)) fun _ => ?_
  refine Triple.andThen (definitionData_lits d ht hv) fun out hout => ?_
  obtain ⟨defn, md, te, ve⟩ := out
  dsimp only
  exact finishConstant_lits _ _ fun e he => hout e (by simpa [constantInfoRootExprs] using he)

/-- **A lone constant's block holds only literals of the terms read under its name.** -/
theorem constantInfo_lits {E : Ix.Environment} {N : Ix.Name → Prop} {x : Ix.Name} {const : ConstantInfo}
    (found : E.get? x = some const) (hN : N x) (hi : ∀ v, const = .inductInfo v → False)
    (hc : ∀ v, const = .ctorInfo v → False) :
    Triple LI (fun _ _ => True) (compileConstantInfo const) (fun _ _ r => BlockLits (ReadTerm E N) r) := by
  have cov : ∀ e ∈ termsOf const, ReadTerm E N e := fun e he => ⟨x, hN, const, found, .inl he⟩
  cases const with
  | defnInfo v =>
    show RefTables.Triple _ _ (compileDefinitionConstantInfo v) _
    unfold compileDefinitionConstantInfo
    rw [EmissionDispatch.compileDefinitionInfo_eq]
    exact Triple.withMutCtx _ (definitionDataInfo_lits _ (cov _ (by simp [termsOf, definitionValData]))
      (cov _ (by simp [termsOf, definitionValData])))
  | thmInfo v =>
    show RefTables.Triple _ _ (compileTheoremConstantInfo v) _
    unfold compileTheoremConstantInfo compileTheoremInfo
    exact Triple.withMutCtx _ (definitionDataInfo_lits _ (cov _ (by simp [termsOf, theoremValData]))
      (cov _ (by simp [termsOf, theoremValData])))
  | opaqueInfo v =>
    show RefTables.Triple _ _ (compileOpaqueConstantInfo v) _
    unfold compileOpaqueConstantInfo compileOpaqueInfo
    exact Triple.withMutCtx _ (definitionDataInfo_lits _ (cov _ (by simp [termsOf, opaqueValData]))
      (cov _ (by simp [termsOf, opaqueValData])))
  | axiomInfo v =>
    show RefTables.Triple _ _ (compileConstantInfoCore (.axiomInfo v)) _
    unfold compileConstantInfoCore
    refine Triple.withMutCtx _ ?_
    show RefTables.Triple _ _ (compileAxiomInfo v) _
    unfold compileAxiomInfo compileAxiomBlock
    refine Triple.seqHolds (cacheFrame (frame_preseed _)) fun _ => ?_
    refine Triple.andThen (axiom_lits v (cov _ (by simp [termsOf, ConstantInfo.getCnst]))) fun out hout => ?_
    obtain ⟨ax, md, te⟩ := out
    dsimp only
    refine finishConstant_lits _ _ fun e he => ?_
    simp only [constantInfoRootExprs, List.toList_toArray, List.mem_singleton] at he
    rw [he]
    exact hout
  | quotInfo v =>
    show RefTables.Triple _ _ (compileQuotientConstantInfo v) _
    unfold compileQuotientConstantInfo
    refine Triple.withMutCtx _ ?_
    unfold compileQuotientInfo compileQuotientBlock
    refine Triple.seqHolds (cacheFrame (frame_preseed _)) fun _ => ?_
    refine Triple.andThen (quotient_lits v (cov _ (by simp [termsOf, ConstantInfo.getCnst]))) fun out hout => ?_
    obtain ⟨q, md, te⟩ := out
    dsimp only
    refine finishConstant_lits _ _ fun e he => ?_
    simp only [constantInfoRootExprs, List.toList_toArray, List.mem_singleton] at he
    rw [he]
    exact hout
  | recInfo v =>
    show RefTables.Triple _ _ (compileRecursorConstantInfo v) _
    unfold compileRecursorConstantInfo
    refine Triple.withMutCtx _ ?_
    unfold compileRecursorInfo compileRecursorBlock
    refine Triple.seqHolds (cacheFrame (frame_preseed _)) fun _ => ?_
    refine Triple.andThen (recursor_lits v (cov _ (by simp [termsOf]))
      fun rule hr => cov _ (by simp only [termsOf]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr)))
      fun out hout => ?_
    obtain ⟨rc, md, te⟩ := out
    dsimp only
    exact finishConstant_lits _ _ fun e he => hout e (by simpa [constantInfoRootExprs] using he)
  | inductInfo v => exact (hi v rfl).elim
  | ctorInfo v => exact (hc v rfl).elim

/-- **The members a block compile reads hold the terms read under their names.** -/
theorem members_lits (ctx : CompileEnv × BlockEnv) (all : Ix.Set Ix.Name) {N : Ix.Name → Prop}
    (hN : ∀ x, all.contains x = true → N x) :
    Claims.RunPost ctx (fun cs : Array MutConst => ∀ m ∈ cs, MutLits (ReadTerm ctx.1.env N) m)
      (forIn all #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine Claims.RunPost.forIn ctx _ _ all.toList (fun n hn acc hacc => ?_) #[] (by simp)
  have hin : N n := hN n (Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hn))
  have push : ∀ m, MutLits (ReadTerm ctx.1.env N) m →
      ∀ m' ∈ acc.push m, MutLits (ReadTerm ctx.1.env N) m' := by
    intro m hm m' hm'
    rcases Array.mem_push.1 hm' with hm' | rfl
    · exact hacc m' hm'
    · exact hm
  refine Claims.RunPost.bind (Claims.RunPost.findConst ctx n) fun ci hci => ?_
  have cov : ∀ e ∈ termsOf ci, ReadTerm ctx.1.env N e := fun e he => ⟨n, hin, ci, hci, .inl he⟩
  split
  · rename_i val
    refine Claims.RunPost.bind (q := fun m => MutLits (ReadTerm ctx.1.env N) m) ?_
      fun m hm => Claims.RunPost.pure (push m hm)
    unfold MutConst.mkIndc
    refine Claims.RunPost.bind (Claims.collectCtors_post ctx val.ctors.toList _ #[] (by simp) fun _ h => h)
      fun ctors h => Claims.RunPost.pure ⟨cov _ (by simp [termsOf, ConstantInfo.getCnst]), fun ctor hctor => ?_⟩
    obtain ⟨c, hc, hcs⟩ := h ctor (by simpa using hctor)
    exact ⟨n, hin, _, hci, .inr ⟨val, c, ctor, rfl, Array.mem_toList_iff.1 hc, hcs, rfl⟩⟩
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]), cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]), cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]), cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]),
      fun rule hr => cov _ (by simp only [termsOf]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr))⟩)
  · exact Claims.RunPost.pure hacc

/-- **A compiled block's record holds only literals of the terms its compile reads**: those of
its members' constants (or of its key's, for a lone constant), and of the constructors their
inductives list. -/
theorem compileBlock_lits {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {r : BlockResult} {s' : BlockState}
    (h : rawRun (compileBlock lo all) ctx {} = (.ok r, s')) :
    BlockLits (ReadTerm ctx.1.env (fun x => all.contains x = true ∨ x = lo)) r := by
  unfold compileBlock at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  have found := BlockRecords.findConst_ok hc
  have h₁ : s₁ = {} := by
    have := BlockRecords.findConst_preserves lo ctx {}
    rw [hc] at this
    exact this
  subst h₁
  dsimp only at h
  split at h <;> split at h
  all_goals first
    | (rename_i hcond; simp at hcond; done)
    | (obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
       obtain ⟨out, s₄, hout, h⟩ := bind_ok h
       have same : BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
         revert h
         refine BlockRecords.Returns.elim
           (P := fun (x : BlockResult) => BlockRecords.recordsOf x = BlockRecords.recordsOf out) ?_
         repeat returns_step
       have block : r.block = out.block := (Prod.mk.inj same).1
       have members := members_lits ctx all (N := fun x => all.contains x = true ∨ x = lo)
         (fun x hx => .inl hx) {} cs s₂ hcs
       have h₂ : s₂ = {} := BlockRecords.forIn_set_state hcs fun n acc => by
         refine Preserves.bind (BlockRecords.findConst_preserves n) fun c => ?_
         split
         · exact Preserves.bind (BlockRecords.mkIndc_preserves _) fun _ => Preserves.pure id _
         all_goals exact Preserves.pure id _
       subst h₂
       obtain ⟨-, lits⟩ := mutualBlock_lits (sourceMembers cs)
         (fun c hc => members c (Claims.mem_sourceMembers hc)) ctx {} out s₄ cacheLits_empty
         trivial hout
       intro k hk
       rw [block] at hk
       exact lits k hk)
    | (obtain ⟨-, lits⟩ := constantInfo_lits (N := fun x => all.contains x = true ∨ x = lo) found (Or.inr rfl)
         (by assumption) (by assumption) ctx {} r s' cacheLits_empty trivial h
       exact lits)

/-- **A compiled block's record holds only literals of the terms its compile reads**, for
`runBlock`. -/
theorem runBlock_lits {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} (h : runBlock cenv all lo = .ok (r, c)) :
    BlockLits (ReadTerm cenv.env (fun x => all.contains x = true ∨ x = lo)) r :=
  compileBlock_lits (Ix.CompileCert.run_success (BlockRecords.runBlock_compiles h))

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

/--
info: 'Ix.Cert.LiteralSources.frame_preseed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LiteralSources.frame_preseed

/--
info: 'Ix.Cert.LiteralSources.runBlock_lits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LiteralSources.runBlock_lits
