import IxVMRefinement.Assembly.TypingSkeleton
import IxVMRefinement.Assembly.TypingDefnCheck

/-! # The step of a definition, theorem or opaque record

`unitStep_defn` proves the skeleton's `UnitStep` for a standalone definition, theorem or
opaque record, by composing the check evidence of the record at the limit of its check
(`checkedAtFullAt_defn_step`, from the same lemmas as `LoadedReads.checkedAtFull_defn_step`)
with the walked-constant step (`Decl.walkedConst_step`). The unit installs one constant, at
the record's key; the extra clause `X` is kept (`KeepsValues`).

What the step reads of the store it runs against is `StepStore` (a part of the skeleton's
`StepCtx`, `StepCtx.toStepStore`): decoded records, the run's records and blobs, good calls.

The references the record uses enter through the two clauses of
`Decl.usedRefsStored_of_clauses`: no used reference is an inert axiom's (`InertClause`, a
fact about the record), and at the step's environment every other used reference is stored
(`CoverAt`). The second is taken as a function of what the skeleton hands the step
(`HandedRefs`): there a used reference is stored, or is a constant address of the record,
or is no in-logic constant address of the run's store (`¬ NeedOk`). The last case is the
seam: a used reference whose record is a block, or is outside Lean's logic, is handed in that
form, and nothing makes it stored. `coverAt_of_needOk` and `coverAt_of_graph` discharge
`CoverAt` where that case does not arise: the second rules out the record's own addresses
and covered references from the walk (`TopGraph`), and asks of the claim layer only that a
used reference that is not covered is `NeedOk`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)

/-! ## What a step reads of its store -/

/-- **The store a step runs against**: its records decode exactly, it holds the run's
records and blobs, and the calls are good for it at every environment and limit. -/
structure StepStore (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) :
    Prop where
  decoded : Ingress.EnvDecoded E
  runRecord : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c
  runBlob : ∀ a b, E₀.blobs.get? a = some b → E.blobs.get? a = some b
  good : ∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Core.Good ⟨E, env, t, lim⟩ calls

theorem StepCtx.toStepStore {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    (h : StepCtx.{u} calls t R envT E₀ E) : StepStore calls t E₀ E :=
  ⟨h.recordsFor.1, h.runRecord, h.runBlob, h.good⟩

/-- In a store whose records decode exactly, the exact decoding of the stored bytes is the
decoded cache. -/
theorem recordOf_eq_recordAt_of_decoded {E : Ixon.Env} (hdec : Ingress.EnvDecoded E)
    (a : _root_.Address) : recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hce⟩ := hdec a lc hget
    show (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hce, hc]
    rfl

theorem StepStore.held {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    (h : StepStore calls t E₀ E) {a : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ a = some c) : recordOf E a = some c :=
  (recordOf_eq_recordAt_of_decoded h.decoded a).trans (h.runRecord a c hc)

/-! ## The references the record uses -/

/-- **No reference the record uses is an inert axiom's** (the `hinert` clause of
`Decl.usedRefsStored_of_clauses`). -/
def InertClause (t : Ix.Kernel.RoleTable) (c : Ixon.Constant) : Prop :=
  ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x → inertKey (keyOf t x) = false

/-- **The environment stores every reference the record uses that is no inert axiom's** (the
`hcover` clause of `Decl.usedRefsStored_of_clauses`). -/
def CoverAt (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (c : Ixon.Constant) : Prop :=
  ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x → inertKey (keyOf t x) = false →
    ∃ ci, env.find? (keyOf t x) = some ci

theorem usedRefsStored_of_cover {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {c : Ixon.Constant} (hcover : CoverAt t env c) (hinert : InertClause t c) :
    Decl.UsedRefsStored t env c :=
  Decl.usedRefsStored_of_clauses hcover hinert

/-- **What `UnitStep` hands a step about the environment and the record at `A`**: the
environment extends the witness's; a reference the record uses is stored, or is a constant
address of the record, or is no in-logic constant address of the run's store; the record's
constant addresses are not stored. -/
structure HandedRefs (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (A : _root_.Address) (c : Ixon.Constant) (env : Ix.Kernel.Env .anon) : Prop where
  ext : ∀ ci ∈ envT.consts, ci ∈ env.consts
  refs : ∀ x, UsedRef E₀ A x →
    (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x
  fresh : ∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none

theorem usedRef_of_idx {E₀ : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ A = some c) {i : Nat} (hi : i ∈ usedRefIdxs c) {x : _root_.Address}
    (hx : c.refs.toList[i]? = some x) : UsedRef E₀ A x :=
  ⟨c, i, hc, hi, by rw [← Array.getElem?_toList]; exact hx⟩

/-- **The cover clause, where every used reference that is no inert axiom's is one a step
may need and none of the record's own.** The seam is the first conjunct: a used reference
whose record is a block or outside Lean's logic is not `NeedOk`. -/
theorem coverAt_of_needOk {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant} (hc : recordOf E₀ A = some c)
    (hneed : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      inertKey (keyOf t x) = false → NeedOk E₀ x ∧ ¬ ConstAddrOf A c x)
    (env : Ix.Kernel.Env .anon) (h : HandedRefs t envT E₀ A c env) : CoverAt t env c := by
  intro i hi x hx hnin
  obtain ⟨hok, hown⟩ := hneed i hi x hx hnin
  rcases h.refs x (usedRef_of_idx hc hi hx) with hs | ho | hn
  · exact Option.isSome_iff_exists.mp hs
  · exact absurd ho hown
  · exact absurd hok hn

section Graph

variable {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {seeds : List _root_.Address}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {envT : Ix.Kernel.Env .anon}

/-- **A top-walked record uses none of its own constant addresses**, at an environment the
skeleton hands its step: such a reference would be top-walked at a smaller rank (impossible
for the record's own address and, through its block, for a projection address of the block),
or covered, and then stored by the witness's environment, which the step's environment
extends, against freshness. -/
theorem not_constAddr_of_used (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {A : _root_.Address} {c : Ixon.Constant} (hT : Top A) (hc : recordOf E₀ A = some c)
    {env : Ix.Kernel.Env .anon} (h : HandedRefs t envT E₀ A c env) {x : _root_.Address}
    (hused : UsedRef E₀ A x) : ¬ ConstAddrOf A c x := by
  intro hx
  have hnone := h.fresh x hx
  rcases hG.closed A x hT hused with ⟨hTx, hrk⟩ | hcov
  · rcases hG.constAddr_cases hT hc hx with ⟨hxA, -⟩ | ⟨-, P, hP, hPp, hPo⟩
    · rw [hxA] at hrk
      exact absurd hrk (Nat.lt_irrefl _)
    · obtain ⟨-, hrkB⟩ := hG.owner x P hTx hP hPp
      rw [hPo] at hrkB
      exact absurd (Nat.lt_trans hrk hrkB) (Nat.lt_irrefl _)
  · obtain ⟨ci, hci, hname⟩ := covered_stored hshape htwf hcov
    have hs : (env.find? (keyOf t x)).isSome = true :=
      find_isSome_of_storedAt ⟨ci, h.ext ci hci, hname⟩
    rw [hnone] at hs
    simp at hs

/-- **The cover clause from the walk**, where every used reference that is no inert
axiom's and is not covered is one a step may need (`NeedOk`). A covered reference is stored
by the witness's environment; the record's own addresses are ruled out by
`not_constAddr_of_used`. What remains of the claim layer is `hneed`, and the seam is there: by
`TopGraph.closed` such a reference is top-walked, and nothing says its record is no block and
in Lean's logic. -/
theorem coverAt_of_graph (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {A : _root_.Address} {c : Ixon.Constant} (hT : Top A) (hc : recordOf E₀ A = some c)
    (hneed : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      inertKey (keyOf t x) = false → ¬ Covered t x → NeedOk E₀ x)
    (env : Ix.Kernel.Env .anon) (h : HandedRefs t envT E₀ A c env) : CoverAt t env c := by
  intro i hi x hx hnin
  have hused := usedRef_of_idx hc hi hx
  by_cases hcov : Covered t x
  · obtain ⟨ci, hci, hname⟩ := covered_stored hshape htwf hcov
    exact Option.isSome_iff_exists.mp (find_isSome_of_storedAt ⟨ci, h.ext ci hci, hname⟩)
  · rcases h.refs x hused with hs | ho | hn
    · exact Option.isSome_iff_exists.mp hs
    · exact absurd ho (not_constAddr_of_used hG hshape htwf hT hc h hused)
    · exact absurd (hneed i hi x hx hnin hcov) hn

end Graph

/-! ## The extra clause and the installed constant -/

/-- **A definition, a theorem or an axiom.** -/
def IsValueConst (ci : ConstantInfo .anon) : Prop :=
  (∃ cv v h, ci = .defnInfo cv v h) ∨ (∃ cv v, ci = .thmInfo cv v) ∨ ∃ cv, ci = .axiomInfo cv

/-- **The extra clause is kept by storing a definition, a theorem or an axiom at a fresh
key.** This kind of step keeps `X`; it is the one fact about `X` the step reads. -/
def KeepsValues (X : Ix.Kernel.Env .anon → Prop) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (ci : ConstantInfo .anon), X env → env.find? ci.name = none →
    IsValueConst ci → X ⟨ci :: env.consts⟩

theorem keepsValues_true : KeepsValues (fun _ => True) :=
  fun _ _ _ _ _ => trivial

theorem isValueConst_defnConst (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (v : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    IsValueConst (LoadedReads.defnConst kind cv v hn) := by
  unfold IsValueConst
  cases kind with
  | defn => exact Or.inl ⟨cv, v, hn, rfl⟩
  | opaq => exact Or.inr (Or.inr ⟨cv, rfl⟩)
  | thm => exact Or.inr (Or.inl ⟨cv, v, rfl⟩)

/-- The constant of the annotations is the constant of the readings, stored. -/
theorem storedAs_defnConst (kind : Ix.DefKind) (k : Ix.Kernel.Key .anon)
    (ps : List Ix.Kernel.LevelParam) (hn : Ix.Kernel.ReducibilityHint)
    {ty' ty₀ val' val₀ : Ix.Kernel.Expr .anon} (hT : Annotates ty' ty₀)
    (hV : Annotates val' val₀) :
    StoredAs (LoadedReads.defnConst kind ⟨k, ps, ty'⟩ val' hn)
      (LoadedReads.defnConst kind ⟨k, ps, ty₀⟩ val₀ hn) := by
  cases kind with
  | defn =>
    show StoredAs (.defnInfo ⟨k, ps, ty'⟩ val' hn) (.defnInfo ⟨k, ps, ty₀⟩ val₀ hn)
    exact ⟨⟨rfl, rfl, hT⟩, hV, rfl⟩
  | opaq =>
    show StoredAs (.axiomInfo ⟨k, ps, ty'⟩) (.axiomInfo ⟨k, ps, ty₀⟩)
    exact ⟨⟨rfl, rfl, hT⟩, trivial⟩
  | thm =>
    show StoredAs (.thmInfo ⟨k, ps, ty'⟩ val') (.thmInfo ⟨k, ps, ty₀⟩ val₀)
    exact ⟨⟨rfl, rfl, hT⟩, hV⟩

/-! ## The key -/

/-- A key that is no role key of a role outside Lean's compiler-trust axioms is free. -/
theorem keyFree_of_ne_role {k : Ix.Kernel.Key .anon}
    (hne : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → k ≠ .role r) :
    Decl.KeyFree k :=
  ⟨Decl.reservedBasisNames_false_of_ne_nonTrustRole hne,
    Decl.natOpNames_false_of_ne_nonTrustRole hne,
    Decl.natDivModNames_false_of_ne_nonTrustRole hne⟩

theorem keyFree_id (a : _root_.Address) : Decl.KeyFree (Ix.Kernel.Key.id a : Ix.Kernel.Key .anon) :=
  keyFree_of_ne_role (fun r _ h => by cases h)

/-- The key of an address the table binds no role to is free. -/
theorem keyFree_keyOf_of_unbound {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (h : ∀ r, (r, a) ∉ t.bound.toList) : Decl.KeyFree (keyOf t a) := by
  rcases keyOf_cases t a with ⟨hk, -⟩ | ⟨r, hr, -⟩
  · rw [hk]
    exact keyFree_id a
  · exact absurd hr (h r)

/-! ## The step of a standalone definition, theorem or opaque record -/

/-- **`UnitStep` for a standalone definition, theorem or opaque record.** The run's store
`E₀` is a run store and holds the record `c` at `A`, in Lean's logic; the walk checked `A`
under a role context at the limit `n`, the walk's (`hlim`); the record's key is free; no used
reference is an inert axiom's; and at every environment the skeleton hands the step, the
other used references are stored. Then the step at `A` holds against any store `E` the step
runs against (`StepStore`), for any extra clause kept by storing a value constant.

The unit installs one constant: the declaration of the record's canonical annotations, at
the record's key. Its prefix invariant is `Decl.walkedConst_step`'s, transported to `E` by
the reload of the record at `E`. -/
theorem unitStep_defn {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : CheckedAtFullAt calls bAddr t A n) (hlim : lim = some n)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hX : KeepsValues X) :
    UnitStep.{u} X t envT E₀ E lim A c := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  have hbound : Bounded calls := (hst.good env none).2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    checkedAtFullAt_defn_step (order_role := []) ht hbound hS hrec₀ hinfo hlogic
      List.not_mem_nil hchk E hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  have hfreshA : env.find? (keyOf t A) = none := hfresh A hown
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfreshA
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  obtain ⟨-, htrans⟩ := Decl.walkedConst_step hinv hev (hst.good env none) hfreshD hkeyD
    (fun cv h => absurd h (LoadedReads.defnDecl_ne_axiomDecl _ _ _ _ cv))
  have hinv' := htrans E (some n) (hreload E (hst.held hc) hst.runBlob) hinv
  rw [LoadedReads.installs_defnDecl] at hinv'
  have hname : (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t A :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨[LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)], List.nodup_singleton _, ?_, hinv', ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hfreshA
  · exact hX env (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)) hXe (by rw [hname]; exact hfreshA) (isValueConst_defnConst _ _ _ _)
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨_, List.mem_singleton_self _, _, hname, hreads,
        storedAs_defnConst _ _ _ _ hannT hannV⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

/-- **`UnitStep` for a standalone definition, theorem or opaque record, from the walk**: as
`unitStep_defn` at the skeleton's step context, with the cover clause from the walk
(`coverAt_of_graph`). -/
theorem unitStep_defn_of_graph {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hctx : StepCtx.{u} calls t R envT E₀ E) (hG : TopGraph t E₀ seeds Top rank) (hT : Top A)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : CheckedAtFullAt calls bAddr t A n) (hlim : lim = some n)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hneed : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      inertKey (keyOf t x) = false → ¬ Covered t x → NeedOk E₀ x)
    (hX : KeepsValues X) :
    UnitStep.{u} X t envT E₀ E lim A c := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  exact unitStep_defn ht hS hctx.toStepStore hc hinfo hlogic hchk hlim hkey hinert
    (coverAt_of_graph hG hctx.shape htwf hT hc hneed) hX

end IxVM.Refinement.Typing
