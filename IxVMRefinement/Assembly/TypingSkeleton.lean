import IxVMRefinement.Assembly.TypingFold
import IxVMRefinement.Assembly.TypingFacts
import IxVMRefinement.Assembly.TypingModel
import IxVMRefinement.StatementRel.DefInhabit
import IxVMRefinement.Assembly.Closure

/-! # The typing statement over explicit interfaces

`typing_skeleton` proves the typing half of the consistency statement
(`IxVM.Consistency.TypingSpecOn`, with `FactsWith X` for the witness's internal part) from
three hypotheses, each the interface of a layer that is proved elsewhere:

* `ClaimExport Walk`: the claim layer. For an accepted claim in scope and a table that
  admits, the run hashed a collision or there are a store of the run's records
  (`LoadedReads.RunStore`) and a walk of them (`Walk`, an abstract predicate: the claim layer
  chooses what evidence it carries).
* `Walk → TopGraph`: the part of the walk the assembly reads. The top-walked addresses hold
  records; a reference a top-walked record uses is top-walked at a smaller rank or bound to a
  role whose record a validation walks (`Covered`); a projection record's block is top-walked
  at a smaller rank and the record is the canonical projection of one of its members; a block's
  member and constructor projection records are in the store; an axiom or quotient record
  stands at one of seven roles; the seeds are in Lean's logic.
* `UnitStep`, for every top-walked definition, recursor or block record in Lean's logic: the
  step of one unit. From the prefix invariant at an environment that stores what the record
  uses and stores none of its constant addresses, some fresh constants keep the invariant and
  store, at each constant address of the record, a constant that stores a reading of that
  address.

What is proved here, with no further hypothesis: which records are units (those with a
constant address the witness's environment does not store), that a unit's constant addresses
are then all unstored (block wholeness, from `Facts`), that distinct units own distinct
addresses, that every address a unit needs is stored by the witness's environment or owned by
a unit of smaller rank (so the units can be folded: `UnitFold.run`), that an axiom or
quotient record is never a unit, the freshness and distinctness of names, the provenance
clause over the joint store, the seed clause including block seeds and projection seeds, the
store the steps run against (`merged_exists`, with the prefix invariant from `Facts` and good
calls from the absence of a collision), and the model of the claimed sub-environment from the
provenance clause.

`typing_of_no_fresh_units` needs none of the three interfaces: where the witness's
environment already stores every constant address the seeds cover, the conclusion holds from
the public shape of the witness alone. `typing_def_instance` is that theorem at a real table,
store and environment (`DefInhabit.tableShape_def`), for a seed that is not a pin.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)

/-! ## Kinds of records -/

/-- A record that declares one constant at its own address. -/
def Standalone (c : Ixon.Constant) : Prop :=
  (∃ d, c.info = .defn d) ∨ (∃ rc, c.info = .recr rc) ∨ (∃ ax, c.info = .axio ax) ∨
    ∃ q, c.info = .quot q

/-- A projection record. -/
def IsProj (c : Ixon.Constant) : Prop :=
  (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .cPrj p) ∨
    ∃ p, c.info = .rPrj p

/-- A block record. -/
def IsBlock (c : Ixon.Constant) : Prop := ∃ ms, c.info = .muts ms

theorem kind_cases (c : Ixon.Constant) : Standalone c ∨ IsProj c ∨ IsBlock c := by
  cases h : c.info with
  | defn d => exact Or.inl (Or.inl ⟨d, h⟩)
  | recr rc => exact Or.inl (Or.inr (Or.inl ⟨rc, h⟩))
  | axio ax => exact Or.inl (Or.inr (Or.inr (Or.inl ⟨ax, h⟩)))
  | quot q => exact Or.inl (Or.inr (Or.inr (Or.inr ⟨q, h⟩)))
  | dPrj p => exact Or.inr (Or.inl (Or.inl ⟨p, h⟩))
  | iPrj p => exact Or.inr (Or.inl (Or.inr (Or.inl ⟨p, h⟩)))
  | cPrj p => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨p, h⟩))))
  | rPrj p => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨p, h⟩))))
  | muts ms => exact Or.inr (Or.inr ⟨ms, h⟩)

theorem standalone_not_proj {c : Ixon.Constant} (hs : Standalone c) (hp : IsProj c) : False := by
  rcases hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
    rcases hp with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;>
    (rw [h] at h'; cases h')

theorem standalone_not_block {c : Ixon.Constant} (hs : Standalone c) (hb : IsBlock c) :
    False := by
  obtain ⟨ms, h'⟩ := hb
  rcases hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h] at h'; cases h')

theorem proj_not_block {c : Ixon.Constant} (hp : IsProj c) (hb : IsBlock c) : False := by
  obtain ⟨ms, h'⟩ := hb
  rcases hp with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h] at h'; cases h')

theorem memberProjection_isProj (B : _root_.Address) (i : Nat) (m : Ixon.MutConst) :
    IsProj (memberProjection B i m) := by
  cases m with
  | defn d => exact Or.inl ⟨_, rfl⟩
  | indc ind => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | recr rc => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

theorem constructorProjection_isProj (B : _root_.Address) (i j : Nat) :
    IsProj (constructorProjection B i j) :=
  Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))

theorem ownerOf_memberProjection (x B : _root_.Address) (i : Nat) (m : Ixon.MutConst) :
    Ix.Cert.ownerOf x (memberProjection B i m) = B := by
  cases m <;> rfl

theorem ownerOf_constructorProjection (x B : _root_.Address) (i j : Nat) :
    Ix.Cert.ownerOf x (constructorProjection B i j) = B :=
  rfl

/-! ## The walk -/

/-- The eleven non-container anchors validated by a binding run and skipped under an assumed
role table: `Bool`, `And`, `String`, `Char`, and their bound constructors/recursors/helpers. -/
def coveredAnchors : List Ix.Kernel.Role :=
  [.bool, .boolFalse, .boolTrue, .boolRec,
   .and, .andIntro, .andRec,
   .string, .stringOfList, .char, .charOfNat]

set_option maxRecDepth 100000 in
theorem coveredAnchors_mem_shape_or_prelude (r : Ix.Kernel.Role) (h : r ∈ coveredAnchors) :
    r ∈ shapeAnchors ∨ r ∈ preludeRoles := by
  cases r <;> first
    | exact absurd h (by decide)
    | exact Or.inl (by decide)
    | exact Or.inr (by decide)

/-- **A reference bound to a role whose record a validation walks.** A run that assumes its
table skips such a reference; a run that validates it walks the record under another role
context. Either way the valid table's environment keeps the role's constant. -/
def Covered (t : Ix.Kernel.RoleTable) (b : _root_.Address) : Prop :=
  ∃ r, t.addressOf? r = some b ∧
    (walkedRole r = true ∨ r ∈ coveredAnchors)

/-- **The record at `a` uses the reference `x`.** -/
def UsedRef (E₀ : Ixon.Env) (a x : _root_.Address) : Prop :=
  ∃ c i, recordOf E₀ a = some c ∧ i ∈ usedRefIdxs c ∧ c.refs[i]? = some x

/-- **`x` is a constant address of the record `c` at `A`**: `A` itself for a record that
declares one constant; a member's address or a constructor's address for a block. A
projection record has none: its address is a constant address of its block. -/
def ConstAddrOf (A : _root_.Address) (c : Ixon.Constant) (x : _root_.Address) : Prop :=
  (x = A ∧ Standalone c) ∨
  ∃ ms i m, c.info = .muts ms ∧ ms[i]? = some m ∧
    (x = memberAddr A i m ∨ ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ x = ctorAddr A i j)

/-- **A reference a step has to find stored**: the run's store holds a record at `x` that is
no block and is in Lean's logic, with its block. -/
def NeedOk (E₀ : Ixon.Env) (x : _root_.Address) : Prop :=
  ∃ c, recordOf E₀ x = some c ∧ ¬ IsBlock c ∧ InLogic c ∧
    ∀ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb → InLogic cb

/-- The roles at which an axiom record or a quotient record may stand: the standard axioms
and the quotient package. -/
def standingRoles : List Ix.Kernel.Role :=
  [.propext, .choice, .quot, .quotMk, .quotLift, .quotInd, .quotSound]

/-- **What the assembly reads of a run's walk**: the addresses `Top` walked under the run's
top-level role context, with their ranks (module docstring). -/
structure TopGraph (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (seeds : List _root_.Address)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat) : Prop where
  /-- The seeds are top-walked. -/
  seedsTop : ∀ a ∈ seeds, Top a
  /-- A top-walked address holds a record. -/
  record : ∀ a, Top a → ∃ c, recordOf E₀ a = some c
  /-- A used reference is top-walked at a smaller rank, or covered. -/
  closed : ∀ a x, Top a → UsedRef E₀ a x → (Top x ∧ rank x < rank a) ∨ Covered t x
  /-- A projection record's block is top-walked at a smaller rank. -/
  owner : ∀ a c, Top a → recordOf E₀ a = some c → IsProj c →
    Top (Ix.Cert.ownerOf a c) ∧ rank (Ix.Cert.ownerOf a c) < rank a
  /-- A top-walked block's member and constructor projection records are in the store. -/
  members : ∀ B c ms, Top B → recordOf E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  /-- A top-walked projection record is at a member's or a constructor's address of its
  block. -/
  projMember : ∀ a c, Top a → recordOf E₀ a = some c → IsProj c →
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  /-- A top-walked axiom or quotient record stands at a standard axiom's role or a role of
  the quotient package. -/
  standing : ∀ a c, Top a → recordOf E₀ a = some c →
    ((∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q) →
    ∃ r ∈ standingRoles, t.addressOf? r = some a
  /-- A seed is in Lean's logic, with its block. -/
  seedLogic : ∀ a ∈ seeds, ∀ c, recordOf E₀ a = some c →
    InLogic c ∧ ∀ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb → InLogic cb

/-! ## What an environment stores -/

/-- **The environment stores a constant at the key of the address.** -/
def StoredAt (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (x : _root_.Address) : Prop :=
  ∃ ci ∈ env.consts, ci.name = keyOf t x

theorem storedAt_of_find {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {x : _root_.Address} {ci : ConstantInfo .anon} (h : env.find? (keyOf t x) = some ci) :
    StoredAt t env x :=
  ⟨ci, Ix.Kernel.Semantics.Env.find?_mem h, Ix.Kernel.Semantics.Env.find?_name h⟩

theorem find_isSome_of_storedAt {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {x : _root_.Address} (h : StoredAt t env x) : (env.find? (keyOf t x)).isSome = true := by
  obtain ⟨ci, hci, hname⟩ := h
  unfold Ix.Kernel.Env.find?
  exact List.find?_isSome.mpr ⟨ci, hci, by simpa using hname⟩

theorem find_none_of_not_storedAt {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {x : _root_.Address} (h : ¬ StoredAt t env x) : env.find? (keyOf t x) = none := by
  cases hf : env.find? (keyOf t x) with
  | none => rfl
  | some ci => exact absurd (storedAt_of_find hf) h

theorem find_of_mem_nodup {env : Ix.Kernel.Env .anon} (hnd : (env.consts.map (·.name)).Nodup)
    {ci : ConstantInfo .anon} (h : ci ∈ env.consts) : env.find? ci.name = some ci :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := env.consts) hnd ci h

/-- A claimed constant at a derived key is a projection table. -/
theorem projInfo_of_aux {ci : ConstantInfo .anon} (haux : ∃ k s, ci.name = .aux k s)
    (hkeep : isModelAux ci = false) : ∃ tbl, ci = .projInfo tbl := by
  obtain ⟨k, s, haux⟩ := haux
  by_cases hproj : ∃ tbl, ci = .projInfo tbl
  · exact hproj
  · have haux_true : isModelAux ci = true := by
      unfold isModelAux
      rw [haux]
      cases ci with
      | projInfo tbl => exact absurd ⟨tbl, rfl⟩ hproj
      | _ => rfl
    rw [hkeep] at haux_true
    cases haux_true

theorem storedAt_of_role {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {env : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    (ha : t.addressOf? r = some a) {ci : ConstantInfo .anon} (hci : ci ∈ env.consts)
    (hname : ci.name = .role r) : StoredAt t env a := by
  have hk : keyOf t a = .role r := Core.keyOf_of_addressOf htwf ha
  exact ⟨ci, hci, hname.trans hk.symm⟩

/-- The pinned quotient package's keys are the five quotient roles. -/
theorem quotPins_names :
    ((Ix.Kernel.BasisKind.quotK.declsA : List (ConstantInfo .anon)).map (·.name)) =
      ([.quot, .quotMk, .quotLift, .quotInd, .quotSound] : List Ix.Kernel.Role).map
        Ix.Kernel.Key.role :=
  rfl

section Shape

variable {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}

/-- **A covered reference is stored by a valid table's environment.** -/
theorem covered_stored (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {x : _root_.Address} (h : Covered t x) : StoredAt t envT x := by
  obtain ⟨r, ha, hw | ha'⟩ := h
  · obtain ⟨ci, hfind, -⟩ := hshape.kept (Ix.SpecDigest.groupOf r) r x trivial
      (role_mem_roleGroup r) (Or.inl (Or.inl hw)) ha
    exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
      (Ix.Kernel.Semantics.Env.find?_name hfind)
  · rcases coveredAnchors_mem_shape_or_prelude r ha' with hs | hp
    · obtain ⟨ci, hfind, -⟩ := hshape.kept (Ix.SpecDigest.groupOf r) r x trivial
        (role_mem_roleGroup r) (Or.inl (Or.inr hs)) ha
      exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
        (Ix.Kernel.Semantics.Env.find?_name hfind)
    · obtain ⟨ci, hfind, -⟩ := hshape.preludeKept (Ix.SpecDigest.groupOf r) r x trivial
        (role_mem_roleGroup r) hp ha
      exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
        (Ix.Kernel.Semantics.Env.find?_name hfind)

/-- **The address of a standard axiom or of a role of the quotient package is stored by a
valid table's environment**: the two axioms that are records of their own are kept, and the
quotient package is pinned whole. -/
theorem standing_stored (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {r : Ix.Kernel.Role} {a : _root_.Address} (hr : r ∈ standingRoles)
    (ha : t.addressOf? r = some a) : StoredAt t envT a := by
  rcases List.mem_cons.mp hr with h | hr1
  · have hax : r ∈ standardAxioms := by
      rw [h]
      exact List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨ci, hfind, -⟩ := hshape.kept (Ix.SpecDigest.groupOf r) r a trivial
      (role_mem_roleGroup r) (Or.inr hax) ha
    exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
      (Ix.Kernel.Semantics.Env.find?_name hfind)
  · rcases List.mem_cons.mp hr1 with h | hr2
    · have hax : r ∈ standardAxioms := by
        rw [h]
        exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨ci, hfind, -⟩ := hshape.kept (Ix.SpecDigest.groupOf r) r a trivial
        (role_mem_roleGroup r) (Or.inr hax) ha
      exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
        (Ix.Kernel.Semantics.Env.find?_name hfind)
    · have hmem : Ix.Kernel.Key.role r ∈
          ((Ix.Kernel.BasisKind.quotK.declsA : List (ConstantInfo .anon)).map (·.name)) := by
        rw [quotPins_names]
        exact List.mem_map.mpr ⟨r, hr2, rfl⟩
      obtain ⟨ci, hci, hname⟩ := List.mem_map.mp hmem
      exact storedAt_of_role htwf ha (hshape.pins .quotK ci hci) hname

end Shape

/-! ## Units -/

section Units

variable {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- A member's or constructor's address of a top-walked block holds a projection record of
that block. -/
theorem TopGraph.block_record (hG : TopGraph t E₀ seeds Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} (hT : Top A) (hc : recordOf E₀ A = some c)
    (hms : c.info = .muts ms) {i : Nat} {m : Ixon.MutConst} (hm : ms[i]? = some m)
    {x : _root_.Address}
    (hx : x = memberAddr A i m ∨ ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ x = ctorAddr A i j) :
    ∃ P, recordOf E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = A := by
  obtain ⟨hmem, hctor⟩ := hG.members A c ms hT hc hms i m hm
  rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
  · rw [hx]
    exact ⟨_, hmem, memberProjection_isProj A i m, ownerOf_memberProjection _ A i m⟩
  · rw [hx]
    exact ⟨_, hctor ind j hind hj, constructorProjection_isProj A i j,
      ownerOf_constructorProjection _ A i j⟩

/-- A constant address of a top-walked record is the record's own address, or holds a
projection record of the block. -/
theorem TopGraph.constAddr_cases (hG : TopGraph t E₀ seeds Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {x : _root_.Address} (hT : Top A) (hc : recordOf E₀ A = some c)
    (hx : ConstAddrOf A c x) :
    (x = A ∧ Standalone c) ∨
      (IsBlock c ∧ ∃ P, recordOf E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = A) := by
  rcases hx with h | ⟨ms, i, m, hms, hm, hx⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨ms, hms⟩, hG.block_record hT hc hms hm hx⟩

/-- **Two top-walked records with a constant address in common are one record.** -/
theorem TopGraph.owns_apart (hG : TopGraph t E₀ seeds Top rank) {A A' : _root_.Address}
    {c c' : Ixon.Constant} {x : _root_.Address} (hT : Top A) (hT' : Top A')
    (hc : recordOf E₀ A = some c) (hc' : recordOf E₀ A' = some c') (hx : ConstAddrOf A c x)
    (hx' : ConstAddrOf A' c' x) : A = A' := by
  rcases hG.constAddr_cases hT hc hx with ⟨h1, hs⟩ | ⟨hb, P, hP, hPp, hPo⟩
  · rcases hG.constAddr_cases hT' hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · exact h1.symm.trans h1'
    · rw [h1, hc] at hP'
      have hcc : c = P' := Option.some.inj hP'
      rw [hcc] at hs
      exact (standalone_not_proj hs hPp').elim
  · rcases hG.constAddr_cases hT' hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · rw [h1', hc'] at hP
      have hcc : c' = P := Option.some.inj hP
      rw [hcc] at hs'
      exact (standalone_not_proj hs' hPp).elim
    · rw [hP] at hP'
      have hPP : P = P' := Option.some.inj hP'
      rw [← hPP] at hPo'
      exact hPo.symm.trans hPo'

/-- **A unit's anchor**: a top-walked record in Lean's logic with a constant address the
witness's environment does not store. -/
def IsAnchor (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Top : _root_.Address → Prop) (A : _root_.Address) : Prop :=
  Top A ∧ ∃ c, recordOf E₀ A = some c ∧ InLogic c ∧
    ∃ x, ConstAddrOf A c x ∧ ¬ StoredAt t envT x

/-- The addresses with a property that implies a record are the members of a list. -/
theorem exists_list_of_records (E₀ : Ixon.Env) (P : _root_.Address → Prop)
    (h : ∀ a, P a → ∃ c, recordOf E₀ a = some c) :
    ∃ us : List _root_.Address, ∀ a, a ∈ us ↔ P a := by
  have : DecidablePred P := fun a => Classical.propDecidable (P a)
  refine ⟨(E₀.consts.toList.map (·.1)).filter (fun a => decide (P a)), fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · intro h'
    exact of_decide_eq_true h'.2
  · intro h'
    obtain ⟨c, hc⟩ := h a h'
    obtain ⟨lc, hl, -⟩ := recordOf_some hc
    have hmem : (a, lc) ∈ E₀.consts.toList := by
      refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
      rw [← Std.HashMap.get?_eq_getElem?]
      exact hl
    exact ⟨List.mem_map.mpr ⟨(a, lc), hmem, rfl⟩, decide_eq_true h'⟩

variable {R E : Ixon.Env} {envT : Ix.Kernel.Env .anon}

/-- **A unit's constant addresses are all unstored**: one is, and a block is stored whole. -/
theorem anchor_fresh (hG : TopGraph t E₀ seeds Top rank)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    {A : _root_.Address} (hA : IsAnchor t envT E₀ Top A) {c : Ixon.Constant}
    {x : _root_.Address} (hc : recordOf E₀ A = some c) (hx : ConstAddrOf A c x) :
    ¬ StoredAt t envT x := by
  obtain ⟨hT, c', hc', -, x₀, hx₀, hun⟩ := hA
  rw [hc] at hc'
  have hcc : c = c' := Option.some.inj hc'
  rw [← hcc] at hx₀
  intro hst
  rcases hx with ⟨h1, hs⟩ | ⟨ms, i, m, hms, hm, hxm⟩
  · rcases hx₀ with ⟨h0, -⟩ | ⟨ms₀, i₀, m₀, hms₀, -, -⟩
    · rw [h1] at hst
      rw [h0] at hun
      exact hun hst
    · exact standalone_not_block hs ⟨ms₀, hms₀⟩
  · rcases hx₀ with ⟨-, hs₀⟩ | ⟨ms₀, i₀, m₀, hms₀, hm₀, hx₀m⟩
    · exact standalone_not_block hs₀ ⟨ms, hms⟩
    · obtain ⟨P, hP, hPp, hPo⟩ := hG.block_record hT hc hms hm hxm
      have hne : A ≠ x := by
        intro hAx
        rw [← hAx, hc] at hP
        have hcP : c = P := Option.some.inj hP
        rw [← hcP] at hPp
        exact proj_not_block hPp ⟨ms, hms⟩
      have hbs : BlockStored t envT A ms :=
        hwhole x A P c ms (find_isSome_of_storedAt hst) (hrun x P hP) hPo hne (hrun A c hc) hms
      rw [hms] at hms₀
      have hmm : ms = ms₀ := Ixon.ConstantInfo.muts.inj hms₀
      rw [← hmm] at hm₀
      obtain ⟨hmem, hctor⟩ := hbs i₀ m₀ hm₀
      rcases hx₀m with h | ⟨ind, j, hind, hj, h⟩
      · rw [h] at hun
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hmem
        exact hun (storedAt_of_find hci)
      · rw [h] at hun
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hctor ind j hind hj)
        exact hun (storedAt_of_find hci)

end Units

/-! ## The step of a unit -/

/-- **The records a unit's step is asked for**: a definition, a recursor or a block. An axiom
or quotient record is never a unit (`standing_stored`). -/
def UnitKind (c : Ixon.Constant) : Prop :=
  (∃ d, c.info = .defn d) ∨ (∃ rc, c.info = .recr rc) ∨ IsBlock c

/-- **What a step reads of the run and of the table**: the witness's public shape; a record
store `E` for the witness store that holds the run's records and blobs; and calls that are
good for `E` at every environment and limit. -/
structure StepCtx (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) : Prop where
  shape : TableShape.{u} t (fun _ => True) R envT
  recordsFor : RecordsFor R E
  runRecord : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c
  runBlob : ∀ a b, E₀.blobs.get? a = some b → E.blobs.get? a = some b
  good : ∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Core.Good ⟨E, env, t, lim⟩ calls

/-- **The step of the unit of the record `c` at `A`**, against the store `E` at the limit
`lim`. At every environment `env` that extends the witness's, has distinct names, satisfies
the prefix invariant and the extra clause `X`, stores every reference the record uses that is
not one of its own constant addresses (unless the reference is no in-logic constant address
of the run's store), and stores none of the record's constant addresses: there are fresh
constants `new` with distinct names such that `new ++ env` satisfies the prefix invariant and
`X`; at each constant address of the record `new` holds a constant at that address's key that
stores a reading of the address over the run's records; and every other constant of `new` is
at a derived key. -/
def UnitStep (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat) (A : _root_.Address)
    (c : Ixon.Constant) : Prop :=
  ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env → X env →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ new : List (ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ ∧ X ⟨new ++ env.consts⟩ ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-! ## The fold -/

/-- **What is known of every environment the fold reaches**: distinct names, the prefix
invariant at the run's store and limit, the extra clause, and the provenance clause of the
conclusion over the joint store. -/
structure FoldInv (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E₀ R E : Ixon.Env) (lim : Option Nat) (env : Ix.Kernel.Env .anon) : Prop where
  nodup : (env.consts.map (·.name)).Nodup
  inv : Decl.PrefixInv.{u} E t lim env
  extra : X env
  prov : ∀ ci ∈ (claimedEnv env).consts,
    (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
      ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci

/-- **The typing run as a system of units**: a unit is the address of a record; it owns the
record's constant addresses and needs the in-logic constant addresses the record uses. A
state is an environment; it stores an address when it holds a constant at the address's
key. -/
def typingFold (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable) (E₀ R E : Ixon.Env)
    (lim : Option Nat) (rank : _root_.Address → Nat) :
    UnitFold (Ix.Kernel.Env .anon) _root_.Address _root_.Address where
  Inv := FoldInv.{u} X t E₀ R E lim
  Ext := fun env env' => ∀ ci ∈ env.consts, ci ∈ env'.consts
  Stored := StoredAt t
  Post := fun A env => ∀ c, recordOf E₀ A = some c → ∀ x, ConstAddrOf A c x →
    ∃ ci ∈ env.consts, ci.name = keyOf t x ∧ KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci
  owns := fun A x => ∃ c, recordOf E₀ A = some c ∧ ConstAddrOf A c x
  needs := fun A x => UsedRef E₀ A x ∧ NeedOk E₀ x
  rank := rank
  ext_refl := fun _ _ h => h
  ext_trans := fun h₁ h₂ ci hci => h₂ ci (h₁ ci hci)
  stored_mono := fun x h hx => by
    obtain ⟨ci, hci, hname⟩ := hx
    exact ⟨ci, h ci hci, hname⟩
  post_mono := fun A h hp c hc x hx => by
    obtain ⟨ci, hci, hname, hk⟩ := hp c hc x hx
    exact ⟨ci, h ci hci, hname, hk⟩

section Fold

variable {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
  {envT : Ix.Kernel.Env .anon} {seeds : List _root_.Address} {Top : _root_.Address → Prop}
  {rank : _root_.Address → Nat} {lim : Option Nat} {us : List _root_.Address}

/-- **Every address a unit needs is stored by the witness's environment or owned by a unit of
smaller rank.** A covered reference is stored. A top-walked reference of smaller rank that is
not stored is a constant address of its own record or of its block, which is then a unit of
smaller rank. -/
theorem needs_earlier (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A) :
    (typingFold.{u} X t E₀ R E lim rank).NeedsEarlier envT us := by
  intro A hA x hneed
  obtain ⟨hused, cx, hcx, hnb, hlog, hlogB⟩ := hneed
  have hAn := (hus A).mp hA
  rcases hG.closed A x hAn.1 hused with ⟨hTx, hrk⟩ | hcov
  · by_cases hst : StoredAt t envT x
    · exact Or.inl hst
    · rcases kind_cases cx with hsa | hpr | hbl
      · exact Or.inr (Or.inr ⟨x,
          (hus x).mpr ⟨hTx, cx, hcx, hlog, x, Or.inl ⟨rfl, hsa⟩, hst⟩,
          ⟨cx, hcx, Or.inl ⟨rfl, hsa⟩⟩, hrk⟩)
      · obtain ⟨hTB, hrkB⟩ := hG.owner x cx hTx hcx hpr
        obtain ⟨cb, hcb, hconst⟩ := hG.projMember x cx hTx hcx hpr
        exact Or.inr (Or.inr ⟨Ix.Cert.ownerOf x cx,
          (hus _).mpr ⟨hTB, cb, hcb, hlogB cb hcb, x, hconst, hst⟩,
          ⟨cb, hcb, hconst⟩, Nat.lt_trans hrkB hrk⟩)
      · exact absurd hbl hnb
  · exact Or.inl (covered_stored hshape htwf hcov)

/-- **The steps of the fold**, from the step of each unit. An axiom or quotient record is no
unit: its address is stored by the witness's environment. -/
theorem fold_steps (hG : TopGraph t E₀ seeds Top rank)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A)
    (hstep : ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
      UnitStep.{u} X t envT E₀ E lim A c) :
    (typingFold.{u} X t E₀ R E lim rank).Steps envT us := by
  intro env A hA hinv hext hneed hfr
  have hFI : FoldInv.{u} X t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  have hAn := (hus A).mp hA
  obtain ⟨hT, c, hc, hlog, x₀, hx₀, hun⟩ := hAn
  have hkind : UnitKind c := by
    rcases kind_cases c with hsa | hpr | hbl
    · rcases hsa with ⟨d, h⟩ | ⟨rc, h⟩ | hax | hq
      · exact Or.inl ⟨d, h⟩
      · exact Or.inr (Or.inl ⟨rc, h⟩)
      · exfalso
        obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inl hax)
        exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hax))⟩) (standing_stored hshape htwf hr ha)
      · exfalso
        obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inr hq)
        exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr hq))⟩) (standing_stored hshape htwf hr ha)
    · exfalso
      rcases hx₀ with ⟨-, hs⟩ | ⟨ms, i, m, hms, -, -⟩
      · exact standalone_not_proj hs hpr
      · exact proj_not_block hpr ⟨ms, hms⟩
    · exact Or.inr (Or.inr hbl)
  have hrefs : ∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x := by
    intro x hused
    by_cases hok : NeedOk E₀ x
    · rcases hneed x ⟨hused, hok⟩ with hs | ⟨c', hc', hca⟩
      · exact Or.inl (find_isSome_of_storedAt hs)
      · rw [hc] at hc'
        have hcc : c = c' := Option.some.inj hc'
        rw [← hcc] at hca
        exact Or.inr (Or.inl hca)
    · exact Or.inr (Or.inr hok)
  have hfresh : ∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none :=
    fun x hx => find_none_of_not_storedAt (hfr x ⟨c, hc, hx⟩)
  obtain ⟨new, hnd', hfresh', hinv', hX', hreads, hnames⟩ :=
    hstep A c hT hc hlog hkind env hextT hFI.nodup hFI.inv hFI.extra hrefs hfresh
  have hgrow : Ix.Kernel.Grows (fun _ => True) env ⟨new ++ env.consts⟩ :=
    ⟨new, rfl, fun ci hci => ⟨trivial, hfresh' ci hci⟩, hnd'⟩
  have hkept : ∀ x, ConstAddrOf A c x → ∃ ci ∈ new,
      ci.name = keyOf t x ∧ KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci := by
    intro x hx
    obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
    refine ⟨ci, hci, hname, keptIn_over_run ⟨fun c' ax hc' hinfo => ?_, ci₀, hr, hst⟩⟩
    exfalso
    rcases hG.constAddr_cases hT hc hx with ⟨h1, hs⟩ | ⟨-, P, hP, hPp, -⟩
    · rw [h1, hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hkind with ⟨d, h⟩ | ⟨rc, h⟩ | ⟨ms, h⟩ <;> (rw [h] at hinfo; cases hinfo)
    · rw [hP] at hc'
      have hcc : P = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hinfo; cases hinfo)
  have hprov : ∀ ci ∈ (claimedEnv ⟨new ++ env.consts⟩).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
    intro ci hci
    obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hci
    rcases List.mem_append.mp hmem with hnew | hold
    · rcases hnames ci hnew with ⟨x, hx, hname⟩ | haux
      · obtain ⟨ci', hci', hname', hk⟩ := hkept x hx
        have hcc : ci' = ci := eq_of_name_eq hnd' hci' hnew (hname'.trans hname.symm)
        rw [hcc] at hk
        exact Or.inr (Or.inr ⟨x, hk⟩)
      · exact Or.inl (projInfo_of_aux haux (by simpa using hkeep))
    · exact hFI.prov ci (List.mem_filter.mpr ⟨hold, hkeep⟩)
  have hFI' : FoldInv.{u} X t E₀ R E lim ⟨new ++ env.consts⟩ :=
    ⟨hgrow.nodup hFI.nodup, hinv', hX', hprov⟩
  refine ⟨⟨new ++ env.consts⟩, hFI', fun ci hci => List.mem_append_right _ hci, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c', hc', hca⟩ := hx
    rw [hc] at hc'
    have hcc : c = c' := Option.some.inj hc'
    rw [← hcc] at hca
    obtain ⟨ci, hci, hname, -⟩ := hkept x hca
    exact ⟨ci, List.mem_append_left _ hci, hname⟩
  · intro c' hc' x hca
    rw [hc] at hc'
    have hcc : c = c' := Option.some.inj hc'
    rw [← hcc] at hca
    obtain ⟨ci, hci, hname, hk⟩ := hkept x hca
    exact ⟨ci, List.mem_append_left _ hci, hname, hk⟩
  · intro x hx
    obtain ⟨ci, hci, hname⟩ := hx
    rcases List.mem_append.mp hci with hnew | hold
    · rcases hnames ci hnew with ⟨x', hx', hname'⟩ | ⟨k, s, haux⟩
      · have hxx : x = x' := keyOf_inj hroles (hname.symm.trans hname')
        rw [hxx]
        exact Or.inr ⟨c, hc, hx'⟩
      · exact absurd (hname.symm.trans haux) (keyOf_nonAux t x k s)
    · exact Or.inl ⟨ci, hold, hname⟩

end Fold

/-! ## The skeleton -/

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}

/-- **The conclusion of the typing statement, at an environment that already stores every
constant address the seeds cover**: from the public shape of the witness, records the run
loaded, and the agreement of the two stores. No step, no walk and no internal fact is used:
the environment is the witness's. -/
theorem consistentReadOver_of_stored {G : Nat → Prop} (hshape : TableShape.{u} t G R envT)
    (hroles : (t.bound.toList.map (·.1)).Nodup) (hload : LoadedBy calls E₀)
    (hrec : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    (hblob : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    (hstored : ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      (envT.find? (keyOf t a')).isSome = true) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  refine ⟨E₀, envT, hload, hshape.reading.nodup, fun _ h => h,
    provenance_over_witness hrec hblob hshape.reading.provenance, ?_, hshape.model⟩
  intro a ha a' hsc
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hstored a ha a' hsc)
  exact ⟨ci, hci, stored_provenance hroles hrec hblob hshape.reading.provenance hci⟩

/-- **The typing conclusion when no unit is fresh**: where the witness's environment stores
every constant address the seeds cover, the run hashed a collision with the witness's store,
or the conclusion holds with the witness's environment. From the public shape alone. -/
theorem typing_of_no_fresh_units {G : Nat → Prop} {V : View} {extra : List ByteArray}
    (hshape : TableShape.{u} t G R envT) (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hload : LoadedBy calls E₀)
    (hstored : ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      (envT.find? (keyOf t a')).isSome = true) :
    CollisionWith V extra R calls ∨ ConsistentReadOver.{u} calls t R envT seeds := by
  by_cases hnc : CollisionWith V extra R calls
  · exact Or.inl hnc
  · exact Or.inr (consistentReadOver_of_stored hshape hroles hload (records_agree hload hnc)
      (blobs_agree hload hnc) hstored)

variable {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion, from the walk and the steps**, where the run hashed no
collision. -/
theorem typing_skeleton_core {V : View} {extra : List ByteArray}
    {X : Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hfacts : Facts.{u} t (fun _ => True) R envT) (hX : X envT) (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank)
    (hstep : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → recordOf E₀ A = some c →
      InLogic c → UnitKind c → UnitStep.{u} X t envT E₀ E lim A c) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hload : LoadedBy calls E₀ := hS.loaded
  have hdec : Ingress.EnvDecoded E₀ := hS.decoded
  obtain ⟨E, hM⟩ := merged_exists E₀ R
  have hrf : RecordsFor R E := hM.recordsFor hload hdec hshape.committed hextra hnc
  have hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c :=
    fun a c h => hM.run_record hload hdec hextra hnc h
  have hctx : StepCtx.{u} calls t R envT E₀ E :=
    ⟨hshape, hrf, hrun, fun a b h => hM.run_blob hload hnc h,
      fun env lim => hM.good hload hshape.zeroFree hextra hnc hb env t lim⟩
  have hrec := records_agree hload hnc
  have hblob := blobs_agree hload hnc
  have hinvT : Decl.PrefixInv.{u} E t lim envT := hfacts.inv E hrf lim (limWithin_all t lim)
  have hwhole := hfacts.whole E hrf
  obtain ⟨us, hus⟩ := exists_list_of_records E₀ (IsAnchor t envT E₀ Top)
    (fun A hA => hG.record A hA.1)
  have h₀ : FoldInv.{u} X t E₀ R E lim envT :=
    ⟨hshape.reading.nodup, hinvT, hX,
      provenance_over_witness hrec hblob hshape.reading.provenance⟩
  have hown : (typingFold.{u} X t E₀ R E lim rank).OwnsApart us := by
    intro A hA A' hA' x hx hx'
    obtain ⟨c, hc, hca⟩ := hx
    obtain ⟨c', hc', hca'⟩ := hx'
    exact hG.owns_apart ((hus A).mp hA).1 ((hus A').mp hA').1 hc hc' hca hca'
  have hfreshT : (typingFold.{u} X t E₀ R E lim rank).FreshAt envT us := by
    intro A hA x hx hst
    obtain ⟨c, hc, hca⟩ := hx
    exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc hca hst
  obtain ⟨env, hinv, hext, hdone, -⟩ :=
    (typingFold.{u} X t E₀ R E lim rank).run h₀ hown hfreshT
      (needs_earlier hG hshape htwf hus)
      (fold_steps hG hshape htwf hroles hwhole hrun hus (hstep E hctx))
  have hFI : FoldInv.{u} X t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  refine ⟨E₀, env, hload, hFI.nodup, hextT, hFI.prov, ?_,
    claimedEnv_models_of_prefixInv hFI.inv hFI.nodup hFI.prov⟩
  intro a ha a' hsc
  have hTa := hG.seedsTop a ha
  obtain ⟨c, hc⟩ := hG.record a hTa
  obtain ⟨hlogc, hlogB⟩ := hG.seedLogic a ha c hc
  have hpost : ∀ (A : _root_.Address) (cA : Ixon.Constant) (y : _root_.Address), A ∈ us →
      recordOf E₀ A = some cA → ConstAddrOf A cA y →
      ∃ ci, env.find? (keyOf t y) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) y ci) := by
    intro A cA y hA hcA hca
    have hP : ∀ c, recordOf E₀ A = some c → ∀ x, ConstAddrOf A c x →
        ∃ ci ∈ env.consts, ci.name = keyOf t x ∧
          KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci := (hdone A hA).2
    obtain ⟨ci, hci, hname, hk⟩ := hP cA hcA y hca
    have hf := find_of_mem_nodup hFI.nodup hci
    rw [hname] at hf
    exact ⟨ci, hf, Or.inr hk⟩
  by_cases hst : StoredAt t envT a'
  · obtain ⟨ci, hci, hname⟩ := hst
    have hfT := find_of_mem_nodup hshape.reading.nodup hci
    rw [hname] at hfT
    have hf := find_of_mem_nodup hFI.nodup (hextT ci hci)
    rw [hname] at hf
    exact ⟨ci, hf, stored_provenance hroles hrec hblob hshape.reading.provenance hfT⟩
  · rcases hsc with ⟨haa, hnm⟩ | ⟨c', ms, i, m, hc', hms, hm, hx⟩
    · rw [haa] at hst
      rw [haa]
      rcases kind_cases c with hsa | hpr | hbl
      · exact hpost a c a ((hus a).mpr ⟨hTa, c, hc, hlogc, a, Or.inl ⟨rfl, hsa⟩, hst⟩) hc
          (Or.inl ⟨rfl, hsa⟩)
      · obtain ⟨hTB, -⟩ := hG.owner a c hTa hc hpr
        obtain ⟨cb, hcb, hconst⟩ := hG.projMember a c hTa hc hpr
        exact hpost _ cb a ((hus _).mpr ⟨hTB, cb, hcb, hlogB cb hcb, a, hconst, hst⟩) hcb hconst
      · obtain ⟨ms, hms⟩ := hbl
        exact absurd hms (hnm c ms hc)
    · rw [hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hms
      have hca : ConstAddrOf a c a' := Or.inr ⟨ms, i, m, hms, hm, hx⟩
      exact hpost a c a' ((hus a).mpr ⟨hTa, c, hc, hlogc, a', hca, hst⟩) hc hca

end Skeleton

/-- **The claim layer's export, as the skeleton takes it**: for a claim in scope and a table
that admits at the address the claim names, the run hashed a collision, or there are a store
of the run's records and a walk of them. `Walk` is the claim layer's: the assembly reads it
through `TopGraph`, and the steps read whatever evidence it carries. -/
def ClaimExport
    (Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop)
    (calls : List (Call F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Ix.Claim), Ix.Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScopeTyping c →
      ∀ (V : View) (seeds : List _root_.Address), ClaimSeeds c V seeds →
        ∀ ctx, c.context? = some ctx → ∀ (tb : ByteArray) (t : Ix.Kernel.RoleTable),
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t →
          V.HashedCollision (bytes :: tb :: committedFootprint) calls ∨
            ∃ (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
              (rank : _root_.Address → Nat),
              LoadedReads.RunStore calls E₀ ∧ Walk t seeds E₀ lim Top rank

/-- **The typing statement over explicit interfaces** (module docstring): from a bounded
run, the claim layer's export, what the assembly reads of a walk, and the step of each unit,
the typing half of the consistency statement, for the witness's internal part `FactsWith X`
with any extra clause `X` that the steps keep. -/
theorem typing_skeleton
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstep : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t (fun _ => True) R) t envT E₀ E lim A c) :
    TypingSpecOn.{u} (FactsWith.{u} X) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : Facts.{u} t (fun _ => True) R envT := hW.facts.1
      have hX : X t (fun _ => True) R envT := hW.facts.2
      exact typing_skeleton_core hW.shape hF hX ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank hWalk)
        (fun E hE => hstep t seeds E₀ lim Top rank hWalk R envT E hE)

/-! ## A real instance of the case with no fresh unit -/

open IxVM.Refinement.RoleVal IxVM.Refinement.DefInhabit in
/-- **The typing conclusion at a real table, store and environment**, for the seed
`defAddr`, a definition record that is not a pin (`DefInhabit.tableShape_def`), and any run.
The run's own store is taken empty, so no collision alternative is needed: every clause of
the conclusion is met by the witness's environment, the provenance and seed clauses through a
real reading (`KeptIn`). -/
theorem typing_def_instance (calls : List (Call F)) :
    ConsistentReadOver.{u} calls committedDefaultRoleTable defStore defEnv [defAddr] := by
  have hroles : (committedDefaultRoleTable.bound.toList.map (·.1)).Nodup := by
    obtain ⟨b₀, t₀, hdef, hadm, -⟩ := StoreInhabit.preludePinned_default
    have ht₀ : t₀ = committedDefaultRoleTable := admitBinding_committedDefault hdef hadm
    rw [← ht₀]
    exact roles_nodup_of_admitBinding hadm
  refine consistentReadOver_of_stored (E₀ := {}) tableShape_def.{u} hroles ⟨?_, ?_⟩ ?_ ?_ ?_
  · intro a lc h
    rw [TableInhabit.emptyStore_consts] at h
    cases h
  · intro a b h
    rw [TableInhabit.emptyStore_blobs] at h
    cases h
  · intro x c c' h
    rw [TableInhabit.emptyStore_record] at h
    cases h
  · intro x b b' h
    rw [TableInhabit.emptyStore_blobs] at h
    cases h
  · intro a ha a' hsc
    have haa : a = defAddr := List.mem_singleton.mp ha
    rcases hsc with ⟨h1, -⟩ | ⟨c, ms, i, m, hc, -⟩
    · have hf : defEnv.find? (keyOf committedDefaultRoleTable a') = some defConst := by
        rw [h1, haa, defKey]
        exact defEnv_find_def
      exact (congrArg Option.isSome hf).trans rfl
    · rw [TableInhabit.emptyStore_record] at hc
      cases hc

/-! ## The walk interface at the existing claim layer -/

/-- **The existing claim layer gives five of the clauses of `TopGraph`** for a run that
validates its table: its walked set and rank (`Claim.WalkedClaim`) hold the seeds, hold a record
at every address, decrease strictly along every used reference and along the edge from a
record to a block that is not itself, and the seeds are in Lean's logic. The other three
clauses (`members`, `projMember`, `standing`) and the covered branch of `closed` are not
exported by it. -/
theorem walkedClaim_graph {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {seeds : List _root_.Address} (hload : LoadedBy calls E₀)
    (hw : Claim.WalkedClaim calls t E₀ seeds) (hseedOk : ∀ a ∈ seeds, ¬ OutsideLogicAt E₀ a) :
    ∃ (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
      (∀ a ∈ seeds, Top a) ∧
      (∀ a, Top a → ∃ c, recordOf E₀ a = some c) ∧
      (∀ a x, Top a → UsedRef E₀ a x → Top x ∧ rank x < rank a) ∧
      (∀ a c, Top a → recordOf E₀ a = some c → Ix.Cert.ownerOf a c ≠ a →
        Top (Ix.Cert.ownerOf a c) ∧ rank (Ix.Cert.ownerOf a c) < rank a) ∧
      ∀ a ∈ seeds, ∀ c, recordOf E₀ a = some c →
        InLogic c ∧ ∀ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb → InLogic cb := by
  have hS := LoadedReads.RunStore.of_walkedClaim hload hw
  have hat : ∀ {a : _root_.Address} {c : Ixon.Constant}, recordOf E₀ a = some c →
      Ix.Cert.recordAt E₀ a = some c :=
    fun {a c} h => (hS.recordOf_eq_recordAt a).symm.trans h
  obtain ⟨bAddr, -, -, -, -, -, Wk, rank, hseeds, hclosed, hchecked⟩ := hw
  refine ⟨Wk, rank, hseeds, ?_, ?_, ?_, ?_⟩
  · intro a hTa
    obtain ⟨c, hc, -⟩ := hchecked a hTa
    exact ⟨c, hS.recordOf_of_recordAt hc⟩
  · intro a x hTa hused
    obtain ⟨c, i, hc, hi, hx⟩ := hused
    have hi' : i ∈ Core.BaseSeams.usedRefIdxs c := by
      rw [Assembly.usedRefIdxs_eq]
      exact hi
    exact hclosed a x hTa ⟨c, hat hc, Or.inr ⟨i, hi', hx⟩⟩
  · intro a c hTa hc hne
    exact hclosed a (Ix.Cert.ownerOf a c) hTa ⟨c, hat hc, Or.inl ⟨rfl, hne⟩⟩
  · intro a ha c hc
    refine ⟨?_, fun cb hcb => ?_⟩
    · by_contra hn
      exact hseedOk a ha ⟨c, hat hc, Or.inl hn⟩
    · by_contra hn
      exact hseedOk a ha ⟨c, hat hc, Or.inr ⟨cb, hat hcb, hn⟩⟩

end IxVM.Refinement.Typing
