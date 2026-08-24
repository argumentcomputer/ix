import Ix.Compile.Verify.Catalog
import Ix.CompileM
import Std.Data.HashMap.Lemmas

/-!
# Production compiler table invariants

This module begins the refinement from `CompileM` to the total reference
compiler at the state operations that assign wire indices.  Raw addresses
have lawful structural equality even though the syntax objects they address
do not; the local instances below unlock the `Std.HashMap` laws without
asserting collision freedom for `Ix.Name`, `Ix.Level`, or `Ix.Expr`.
-/

namespace Ix.Compile.Verify

local instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

local instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

local instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

instance : LawfulBEq Ixon.Univ where
  eq_of_beq {left right} h := by
    induction left generalizing right with
    | zero =>
      cases right with
      | zero => rfl
      | succ right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | max right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | imax right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | var right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
    | succ left ih =>
      cases right with
      | zero => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | succ right =>
        apply congrArg Ixon.Univ.succ
        apply ih
        simpa [BEq.beq, Ixon.instBEqUniv.beq] using h
      | max right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | imax right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | var right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
    | max left₁ left₂ ih₁ ih₂ =>
      cases right with
      | zero => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | succ right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | max right₁ right₂ =>
        simp only [BEq.beq, Ixon.instBEqUniv.beq, Bool.and_eq_true] at h
        have hleft := ih₁ h.1
        have hright := ih₂ h.2
        cases hleft
        cases hright
        rfl
      | imax right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | var right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
    | imax left₁ left₂ ih₁ ih₂ =>
      cases right with
      | zero => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | succ right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | max right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | imax right₁ right₂ =>
        simp only [BEq.beq, Ixon.instBEqUniv.beq, Bool.and_eq_true] at h
        have hleft := ih₁ h.1
        have hright := ih₂ h.2
        cases hleft
        cases hright
        rfl
      | var right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
    | var left =>
      cases right with
      | zero => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | succ right => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | max right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | imax right₁ right₂ => simp [BEq.beq, Ixon.instBEqUniv.beq] at h
      | var right =>
        exact congrArg Ixon.Univ.var (eq_of_beq (by
          simpa [BEq.beq, Ixon.instBEqUniv.beq] using h))
  rfl {u} := by
    induction u with
    | zero => rfl
    | succ u ih =>
      simpa [BEq.beq, Ixon.instBEqUniv.beq] using ih
    | max left right ih₁ ih₂ =>
      change Ixon.instBEqUniv.beq left left = true at ih₁
      change Ixon.instBEqUniv.beq right right = true at ih₂
      change Ixon.instBEqUniv.beq (left.max right) (left.max right) = true
      simpa only [Ixon.instBEqUniv.beq, Bool.and_eq_true] using And.intro ih₁ ih₂
    | imax left right ih₁ ih₂ =>
      change Ixon.instBEqUniv.beq left left = true at ih₁
      change Ixon.instBEqUniv.beq right right = true at ih₂
      change Ixon.instBEqUniv.beq (left.imax right) (left.imax right) = true
      simpa only [Ixon.instBEqUniv.beq, Bool.and_eq_true] using And.intro ih₁ ih₂
    | var idx =>
      simp [BEq.beq, Ixon.instBEqUniv.beq]

instance : LawfulHashable Ixon.Univ where
  hash_eq left right h := by rw [eq_of_beq h]

/-- The immutable table/address projection used while compiling one
expression. Universe/reference caches, metadata, blobs, names, and the arena
may evolve; these primary tables and resolution maps must remain frozen so a
`RefCompileCtx` built from the preseed snapshot keeps the same meaning. -/
structure ExprTableView where
  refs : Array Address
  refsIndex : Std.HashMap Address UInt64
  univs : Array Ixon.Univ
  univsIndex : Std.HashMap Ixon.Univ UInt64
  blockNameToAddr : Std.HashMap Ix.Name Address
  auxNameToAddr : Std.HashMap Ix.Name Address

def exprTableView (state : Ix.CompileM.BlockState) : ExprTableView :=
  { refs := state.refs
    refsIndex := state.refsIndex
    univs := state.univs
    univsIndex := state.univsIndex
    blockNameToAddr := state.blockNameToAddr
    auxNameToAddr := state.auxNameToAddr }

/-- Resolve a source constant name against exactly the maps consulted by
production `lookupConstAddr`, but without entering `CompileM`.  The global
maps are immutable inputs and the two block-local maps belong to the frozen
expression-table view. -/
def resolveConstAddr? (compileEnv : Ix.CompileM.CompileEnv)
    (snapshot : Ix.CompileM.BlockState) (name : Ix.Name) : Option Address :=
  match snapshot.blockNameToAddr.get? name with
  | some addr => some addr
  | none =>
    match compileEnv.nameToAddr.get? name with
    | some addr => some addr
    | none =>
      match snapshot.auxNameToAddr.get? name with
      | some addr => some addr
      | none => compileEnv.auxNameToAddr.get? name

/-- The address committed by the production literal branches. -/
def literalAddress : Lean.Literal → Address
  | .natVal value => Address.blake3 (ByteArray.mk (Nat.toBytesLE value))
  | .strVal value => Address.blake3 value.toUTF8

theorem resolveConstAddr?_of_exprTableView_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    {left right : Ix.CompileM.BlockState}
    (hview : exprTableView left = exprTableView right) (name : Ix.Name) :
    resolveConstAddr? compileEnv left name =
      resolveConstAddr? compileEnv right name := by
  have hblock := congrArg ExprTableView.blockNameToAddr hview
  have haux := congrArg ExprTableView.auxNameToAddr hview
  change left.blockNameToAddr = right.blockNameToAddr at hblock
  change left.auxNameToAddr = right.auxNameToAddr at haux
  simp [resolveConstAddr?, hblock, haux]

theorem refsIndex_eq_of_exprTableView_eq
    {left right : Ix.CompileM.BlockState}
    (hview : exprTableView left = exprTableView right) :
    left.refsIndex = right.refsIndex := by
  have hmaps := congrArg ExprTableView.refsIndex hview
  exact hmaps

theorem univsIndex_eq_of_exprTableView_eq
    {left right : Ix.CompileM.BlockState}
    (hview : exprTableView left = exprTableView right) :
    left.univsIndex = right.univsIndex := by
  have hmaps := congrArg ExprTableView.univsIndex hview
  exact hmaps

@[simp] theorem cacheUniv_exprTableView
    (state : Ix.CompileM.BlockState) (level : Ix.Level) (u : Ixon.Univ) :
    exprTableView (state.cacheUniv level u) = exprTableView state := by
  rfl

@[simp] theorem cacheUniv_exprCache
    (state : Ix.CompileM.BlockState) (level : Ix.Level) (u : Ixon.Univ) :
    (state.cacheUniv level u).exprCache = state.exprCache := by
  rfl

@[simp] theorem cacheUniv_canonUnivCache
    (state : Ix.CompileM.BlockState) (level : Ix.Level) (u : Ixon.Univ) :
    (state.cacheUniv level u).canonUnivCache = state.canonUnivCache := by
  rfl

/-- The reference-index map is sound for the emitted array, and the next
array index is representable as `UInt64`.  Completeness is intentionally not
needed by semantic preservation: a cache miss may duplicate an address but
cannot make the returned index denote a different one. -/
structure RefTableWF (state : Ix.CompileM.BlockState) : Prop where
  size : state.refs.size < UInt64.size
  index : ∀ {addr idx}, state.refsIndex.get? addr = some idx →
    state.refs[idx.toNat]? = some addr

theorem RefTableWF.empty : RefTableWF (default : Ix.CompileM.BlockState) := by
  constructor
  · change 0 < UInt64.size
    exact UInt64.toNat_lt 0
  · intro addr idx h
    change ({} : Std.HashMap Address UInt64).get? addr = some idx at h
    simp at h

theorem RefTableWF.index_lt {state : Ix.CompileM.BlockState}
    (hstate : RefTableWF state) {addr idx}
    (hindex : state.refsIndex.get? addr = some idx) :
    idx.toNat < state.refs.size := by
  exact (Array.getElem?_eq_some_iff.mp (hstate.index hindex)).1

/-- Pure production interning preserves reference-table soundness and returns
an index that reads back to the requested address. -/
theorem BlockState.internRef_wf {state : Ix.CompileM.BlockState}
    (hstate : RefTableWF state) (addr : Address)
    (hroom : state.refs.size + 1 < UInt64.size) :
    let (state', idx) := state.internRef addr
    RefTableWF state' ∧ state'.refs[idx.toNat]? = some addr := by
  simp only [Ix.CompileM.BlockState.internRef]
  split
  next idx hindex =>
    exact ⟨hstate, hstate.index hindex⟩
  next hmissing =>
    let idx := state.refs.size.toUInt64
    have hidxNat : idx.toNat = state.refs.size := by
      exact UInt64.toNat_ofNat_of_lt hstate.size
    have hreturned : (state.refs.push addr)[idx.toNat]? = some addr := by
      simp [hidxNat]
    refine ⟨?_, hreturned⟩
    constructor
    · simpa using hroom
    · intro queried found hfound
      simp only [Std.HashMap.get?_insert] at hfound
      split at hfound
      next heq =>
        have hqueried : queried = addr := (eq_of_beq heq).symm
        subst queried
        have hfoundEq : found = idx := (Option.some.inj hfound).symm
        subst found
        exact hreturned
      next hne =>
        have hold := hstate.index hfound
        have hlt : found.toNat < state.refs.size :=
          (Array.getElem?_eq_some_iff.mp hold).1
        simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using hold

/-- The universe-index map is sound for the emitted primary universe table.
This invariant is independent of universe canonicity; canonicity is an
additional production precondition established by the preseeding pass. -/
structure UnivTableWF (state : Ix.CompileM.BlockState) : Prop where
  size : state.univs.size < UInt64.size
  index : ∀ {u idx}, state.univsIndex.get? u = some idx →
    state.univs[idx.toNat]? = some u

theorem UnivTableWF.empty : UnivTableWF (default : Ix.CompileM.BlockState) := by
  constructor
  · change 0 < UInt64.size
    exact UInt64.toNat_lt 0
  · intro u idx h
    change ({} : Std.HashMap Ixon.Univ UInt64).get? u = some idx at h
    simp at h

theorem UnivTableWF.index_lt {state : Ix.CompileM.BlockState}
    (hstate : UnivTableWF state) {u idx}
    (hindex : state.univsIndex.get? u = some idx) :
    idx.toNat < state.univs.size := by
  exact (Array.getElem?_eq_some_iff.mp (hstate.index hindex)).1

/-- Pure production interning preserves universe-table soundness and returns
an index that reads back to the requested universe. -/
theorem BlockState.internUniv_wf {state : Ix.CompileM.BlockState}
    (hstate : UnivTableWF state) (u : Ixon.Univ)
    (hroom : state.univs.size + 1 < UInt64.size) :
    let (state', idx) := state.internUniv u
    UnivTableWF state' ∧ state'.univs[idx.toNat]? = some u := by
  simp only [Ix.CompileM.BlockState.internUniv]
  split
  next idx hindex =>
    exact ⟨hstate, hstate.index hindex⟩
  next hmissing =>
    let idx := state.univs.size.toUInt64
    have hidxNat : idx.toNat = state.univs.size := by
      exact UInt64.toNat_ofNat_of_lt hstate.size
    have hreturned : (state.univs.push u)[idx.toNat]? = some u := by
      simp [hidxNat]
    refine ⟨?_, hreturned⟩
    constructor
    · simpa using hroom
    · intro queried found hfound
      simp only [Std.HashMap.get?_insert] at hfound
      split at hfound
      next heq =>
        have hqueried : queried = u := (eq_of_beq heq).symm
        subst queried
        have hfoundEq : found = idx := (Option.some.inj hfound).symm
        subst found
        exact hreturned
      next hne =>
        have hold := hstate.index hfound
        have hlt : found.toNat < state.univs.size :=
          (Array.getElem?_eq_some_iff.mp hold).1
        simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using hold

/-- The public production `CompileM.internRef` computation is exactly the
verified pure state transition: it cannot fail, preserves the table
invariant, and returns an index that resolves to its input address. -/
theorem internRef_run_wf (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {state : Ix.CompileM.BlockState}
    (hstate : RefTableWF state) (addr : Address)
    (hroom : state.refs.size + 1 < UInt64.size) :
    ∃ idx state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internRef addr) = .ok (idx, state') ∧
      RefTableWF state' ∧ state'.refs[idx.toNat]? = some addr := by
  cases hstep : state.internRef addr with
  | mk state' idx =>
    have hwf := BlockState.internRef_wf hstate addr hroom
    simp only [hstep] at hwf
    refine ⟨idx, state', ?_, hwf⟩
    change Except.ok ((state.internRef addr).2, (state.internRef addr).1) =
      Except.ok (idx, state')
    rw [hstep]

/-- The corresponding public universe interning computation refines the
verified primary-universe table transition. -/
theorem internUniv_run_wf (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {state : Ix.CompileM.BlockState}
    (hstate : UnivTableWF state) (u : Ixon.Univ)
    (hroom : state.univs.size + 1 < UInt64.size) :
    ∃ idx state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internUniv u) = .ok (idx, state') ∧
      UnivTableWF state' ∧ state'.univs[idx.toNat]? = some u := by
  cases hstep : state.internUniv u with
  | mk state' idx =>
    have hwf := BlockState.internUniv_wf hstate u hroom
    simp only [hstep] at hwf
    refine ⟨idx, state', ?_, hwf⟩
    change Except.ok ((state.internUniv u).2, (state.internUniv u).1) =
      Except.ok (idx, state')
    rw [hstep]

end Ix.Compile.Verify
