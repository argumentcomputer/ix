/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.BlockOrder
import Ix.Ixon.ProjectionProofs

namespace Ix.Ixon.BlockOrder

open Kernel

/-- An independently counted refinement derivation. A terminal derivation
must exhibit an unchanged complete pass; a changing pass cannot be terminal.
No rule converts exhaustion into a result. -/
inductive Refinement (block : Block) (comparison : Nat) : Nat → Classes → Classes → Prop where
  | fixed {classes} (step : refineStep block comparison classes = .ok classes) :
      Refinement block comparison 1 classes classes
  | next {classes next result rounds}
      (step : refineStep block comparison classes = .ok next)
      (changed : next ≠ classes) (tail : Refinement block comparison rounds next result) :
      Refinement block comparison (rounds + 1) classes result

theorem Refinement.positive {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) : 0 < rounds := by
  cases h <;> omega

theorem Refinement.fixedPoint {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) :
    refineStep block comparison result = .ok result := by
  induction h with
  | fixed step => exact step
  | next _ _ _ ih => exact ih

theorem refine_sound {block comparison fuel initial result}
    (h : refine block comparison fuel initial = .ok result) :
    ∃ rounds, rounds ≤ fuel ∧ Refinement block comparison rounds initial result := by
  induction fuel generalizing initial with
  | zero => simp [refine] at h
  | succ fuel ih =>
    cases step : refineStep block comparison initial with
    | error error => simp [refine, step, bind, Except.bind] at h
    | ok next =>
      by_cases same : next = initial
      · subst next
        simp [refine, step, bind, Except.bind, pure, Except.pure] at h
        subst result
        exact ⟨1, by omega, .fixed step⟩
      · simp [refine, step, same, bind, Except.bind] at h
        obtain ⟨rounds, bound, trace⟩ := ih h
        exact ⟨rounds + 1, by omega, .next step same trace⟩

theorem Refinement.complete {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) {fuel : Nat} (bound : rounds ≤ fuel) :
    refine block comparison fuel initial = .ok result := by
  induction h generalizing fuel with
  | fixed step =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [refine, step, bind, Except.bind, pure, Except.pure]
  | next step changed tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [refine, step, changed, bind, Except.bind]
      exact ih (by omega)

theorem refine_ok_iff (block : Block) (comparison fuel : Nat) (initial result : Classes) :
    refine block comparison fuel initial = .ok result ↔
      ∃ rounds, rounds ≤ fuel ∧ Refinement block comparison rounds initial result :=
  ⟨refine_sound, fun ⟨_, bound, trace⟩ => trace.complete bound⟩

theorem refine_fixedPoint {block comparison fuel initial result}
    (h : refine block comparison fuel initial = .ok result) :
    refineStep block comparison result = .ok result := by
  obtain ⟨_, _, trace⟩ := refine_sound h
  exact trace.fixedPoint

theorem refine_mono {block comparison small large initial result}
    (h : refine block comparison small initial = .ok result) (bound : small ≤ large) :
    refine block comparison large initial = .ok result := by
  obtain ⟨_, used, trace⟩ := refine_sound h
  exact trace.complete (Nat.le_trans used bound)

/-- The stored order must be the recomputed list of ordered singletons.
This predicate records physical preparation, deterministic seeding, and a
finite refinement derivation, independently of the bounded loop's verdict. -/
def Canonical (limits : Limits) (owner : Address) (source : _root_.Ixon.Constant)
    (blobs : Ingress.Blobs) : Prop :=
  ∃ block initial rounds, prepare owner source blobs = .ok block ∧ seed block = .ok initial ∧
    rounds ≤ limits.refinement ∧
    Refinement block limits.comparison rounds initial (orderedSingletons block.entries.size)

theorem canonicalClasses_ok_iff (limits : Limits) (block : Block) (classes : Classes) :
    canonicalClasses limits block = .ok classes ↔
      ∃ initial rounds, seed block = .ok initial ∧ rounds ≤ limits.refinement ∧
        Refinement block limits.comparison rounds initial classes := by
  cases seeded : seed block with
  | error error => simp [canonicalClasses, seeded, bind, Except.bind]
  | ok initial => simp [canonicalClasses, seeded, bind, Except.bind, refine_ok_iff]

theorem checkBlock_ok_iff (limits : Limits) (owner : Address) (source : _root_.Ixon.Constant)
    (blobs : Ingress.Blobs) : checkBlock limits owner source blobs = .ok () ↔
      Canonical limits owner source blobs := by
  cases prepared : prepare owner source blobs with
  | error error => simp [checkBlock, Canonical, prepared, bind, Except.bind]
  | ok block =>
    have run : checkBlock limits owner source blobs = .ok () ↔
        canonicalClasses limits block = .ok (orderedSingletons block.entries.size) := by
      cases sorted : canonicalClasses limits block with
      | error error => simp [checkBlock, prepared, sorted, bind, Except.bind]
      | ok result =>
        by_cases same : result = orderedSingletons block.entries.size <;>
          simp [checkBlock, prepared, sorted, same, bind, Except.bind, pure, Except.pure, throw]
    rw [run, canonicalClasses_ok_iff]
    simp [Canonical, prepared]

/-! ## Recursor blocks in motive order -/

open Ix.Kernel.ConLecheReader in
/-- `recursorMotive` is the motive the Ixon reader indexes a recursor under:
whenever the reader's analysis (`ConLecheReader.analyseRecursor`) succeeds,
it reads the same motive, so a recursor block in motive order is a block the
reader regroups without permuting it. -/
theorem recursorMotive_of_analyse {store owner c r m carriers major}
    (h : analyseRecursor store owner c r = some (m, carriers, major)) :
    recursorMotive c r = some m := by
  unfold analyseRecursor at h
  unfold recursorMotive
  cases hs : stripAll c
      (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat + 1) r.typ with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨doms, body⟩ := p
    cases hd : appHead c spineFuel body with
    | var k =>
      simp only [hs, hd, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h ⊢
      obtain ⟨u, hu, rest⟩ := Option.bind_eq_some_iff.mp h
      rw [Option.bind_eq_some_iff]
      refine ⟨u, hu, ?_⟩
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, _, _, _, _, _, hm, _⟩ := rest
      exact congrArg some hm
    | _ => simp [hs, hd] at h

/-- The members, from `start` on, are recursors in motive order: the one at
position `start + j` eliminates motive `start + j` (`recursorMotive`, as the
reader reads it) and declares `size` motives. -/
def MotivesFrom (source : _root_.Ixon.Constant) (size start : Nat)
    (members : List _root_.Ixon.MutConst) : Prop :=
  ∀ j (h : j < members.length), ∃ r, members[j] = .recr r ∧ r.motives.toNat = size ∧
    recursorMotive source r = some (start + j)

/-- A recursor block in motive order: member `j` eliminates motive `j`, and
every member declares one motive per member of the block. -/
def MotiveOrdered (source : _root_.Ixon.Constant) (members : Array _root_.Ixon.MutConst) : Prop :=
  MotivesFrom source members.size 0 members.toList

theorem motivesFrom_cons (source : _root_.Ixon.Constant) (size start : Nat)
    (member : _root_.Ixon.MutConst) (rest : List _root_.Ixon.MutConst) :
    MotivesFrom source size start (member :: rest) ↔
      (∃ r, member = .recr r ∧ r.motives.toNat = size ∧ recursorMotive source r = some start) ∧
        MotivesFrom source size (start + 1) rest := by
  constructor
  · intro h
    obtain ⟨r, hr, hm, hmot⟩ := h 0 (by simp)
    refine ⟨⟨r, by simpa using hr, hm, by simpa using hmot⟩, fun j hj => ?_⟩
    obtain ⟨r, hr, hm, hmot⟩ := h (j + 1) (by simp; omega)
    exact ⟨r, by simpa using hr, hm, by rw [hmot]; congr 1; omega⟩
  · rintro ⟨⟨r, rfl, hm, hmot⟩, h⟩ j hj
    cases j with
    | zero => exact ⟨r, rfl, hm, by simpa using hmot⟩
    | succ j =>
      obtain ⟨r', hr', hm', hmot'⟩ := h j (by simp at hj; omega)
      exact ⟨r', by simpa using hr', hm', by rw [hmot']; congr 1; omega⟩

theorem checkMotives_ok_iff (owner : Address) (source : _root_.Ixon.Constant) (size : Nat) :
    ∀ (start : Nat) (members : List _root_.Ixon.MutConst),
      checkMotives owner source size start members = .ok () ↔ MotivesFrom source size start members
  | start, [] => by simp [checkMotives, MotivesFrom]
  | start, member :: rest => by
    rw [motivesFrom_cons, ← checkMotives_ok_iff owner source size (start + 1) rest]
    cases member with
    | recr r =>
      by_cases ok : r.motives.toNat = size ∧ recursorMotive source r = some start
      · simp [checkMotives, ok]
      · have bad : (r.motives.toNat == size && recursorMotive source r == some start) = false := by
          simpa [Bool.and_eq_true, beq_iff_eq] using ok
        simp only [checkMotives, bad]
        simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
        intro hm hmot
        exact absurd ⟨hm, hmot⟩ ok
    | defn _ | indc _ =>
      simp [checkMotives, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem checkMotiveOrder_ok_iff (owner : Address) (source : _root_.Ixon.Constant)
    (members : Array _root_.Ixon.MutConst) :
    checkMotives owner source members.size 0 members.toList = .ok () ↔
      MotiveOrdered source members :=
  checkMotives_ok_iff owner source members.size 0 members.toList

/-- A record's order: a recursor block in motive order, any other `muts`
block in canonical structural order, any other record unconstrained. -/
def OrderedRecord (limits : Limits) (blobs : Ingress.Blobs) (pair : Address × _root_.Ixon.Constant) : Prop :=
  match pair.2.info with
  | .muts members =>
    if members.all isRecursor then MotiveOrdered pair.2 members else Canonical limits pair.1 pair.2 blobs
  | _ => True

theorem checkRecord_ok_iff (limits : Limits) (blobs : Ingress.Blobs) (owner : Address)
    (source : _root_.Ixon.Constant) :
    checkRecord limits blobs owner source = .ok () ↔ OrderedRecord limits blobs (owner, source) := by
  rcases source with ⟨info, sharing, refs, univs⟩
  cases info with
  | muts members =>
    by_cases recursors : members.all isRecursor
    · simp only [checkRecord, OrderedRecord, recursors, ite_true]
      exact checkMotiveOrder_ok_iff owner _ members
    · simp only [checkRecord, OrderedRecord, recursors, Bool.false_eq_true, ite_false]
      exact checkBlock_ok_iff limits owner _ blobs
  | _ => simp [checkRecord, OrderedRecord]

def Ordered (limits : Limits) (blobs : Ingress.Blobs) (input : Ingress.Constants) : Prop :=
  ∀ pair ∈ input, OrderedRecord limits blobs pair

theorem checkConstants_ok_iff (limits : Limits) (blobs : Ingress.Blobs) (input : Ingress.Constants) :
    checkConstants limits blobs input = .ok () ↔ Ordered limits blobs input := by
  induction input with
  | nil => simp [checkConstants, Ordered]
  | cons pair rest ih =>
    rcases pair with ⟨owner, source⟩
    have orderedCons : Ordered limits blobs ((owner, source) :: rest) ↔
        OrderedRecord limits blobs (owner, source) ∧ Ordered limits blobs rest := by
      simp only [Ordered, List.mem_cons, forall_eq_or_imp]
    rw [orderedCons, ← ih, ← checkRecord_ok_iff]
    cases checked : checkRecord limits blobs owner source with
    | error error => simp [checkConstants, checked, bind, Except.bind]
    | ok value => cases value; simp [checkConstants, checked, bind, Except.bind]

universe v

/-! ## The certified entry (L5) -/

open Ix.Kernel.ConLecheReader (defaultPins builtinPrelude builtinNatOpPins)

theorem checkBytes_run_iff (maxProjections : Nat) (limits : Admission.Limits) (orderLimits : Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env) :
    checkBytes maxProjections limits orderLimits records blobs hint = .ok env ↔
      Admission.preflight limits records blobs = .ok () ∧
      Admission.uniqueKeys records blobs = .ok () ∧ ∃ input output,
        Admission.decodeRecords limits records = .ok input ∧
        Projection.reconstruct maxProjections input = .ok output ∧
        checkConstants orderLimits blobs input = .ok () ∧
        ConLecheAdmission.checkConstants output blobs hint = .ok env := by
  cases flight : Admission.preflight limits records blobs with
  | error error => simp [checkBytes, flight, Except.mapError, bind, Except.bind]
  | ok value =>
    cases value
    cases unique : Admission.uniqueKeys records blobs with
    | error error => simp [checkBytes, flight, unique, Except.mapError, bind, Except.bind]
    | ok value =>
      cases value
      cases decoded : Admission.decodeRecords limits records with
      | error error => simp [checkBytes, flight, unique, decoded, Except.mapError, bind, Except.bind]
      | ok input =>
        cases expanded : Projection.reconstruct maxProjections input with
        | error error =>
          simp [checkBytes, flight, unique, decoded, expanded, Except.mapError, bind, Except.bind]
        | ok output =>
          cases ordered : checkConstants orderLimits blobs input with
          | error error =>
            simp [checkBytes, flight, unique, decoded, expanded, ordered, Except.mapError, bind,
              Except.bind]
          | ok value =>
            cases value
            cases checked : ConLecheAdmission.checkConstants output blobs hint <;>
              simp [checkBytes, flight, unique, decoded, expanded, ordered, checked, Except.mapError,
                bind, Except.bind]

theorem checkBytes_ok_iff (maxProjections : Nat) (limits : Admission.Limits) (orderLimits : Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env) :
    checkBytes maxProjections limits orderLimits records blobs hint = .ok env ↔
      Verify.Admission.WithinBatch limits records blobs ∧
      Verify.Admission.UniqueKeys records blobs ∧ ∃ input output,
        Verify.Admission.RecordsRead limits records input ∧
        Projection.Expanded maxProjections input output ∧ Ordered orderLimits blobs input ∧
        ConLecheAdmission.checkConstants output blobs hint = .ok env := by
  simp only [checkBytes_run_iff, Verify.Admission.preflight_ok_iff, Verify.Admission.uniqueKeys_ok_iff,
    Verify.Admission.decodeRecords_ok_iff, Projection.reconstruct_ok_iff, checkConstants_ok_iff]

/-- **Fidelity**: unique keys, exact reading, computed projections,
canonical order, and the checker installed what the expanded records
describe. -/
theorem checkBytes_reading {maxProjections : Nat} {limits : Admission.Limits} {orderLimits : Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes maxProjections limits orderLimits records blobs hint = .ok env) :
    Verify.Admission.UniqueKeys records blobs ∧ ∃ input output, Verify.Admission.RecordsRead limits records input ∧
      Projection.Expanded maxProjections input output ∧ Ordered orderLimits blobs input ∧
      ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
        builtinNatOpPins = .ok natPins ∧
        ConLecheAdmission.Installed pins pre natPins output blobs hint env := by
  obtain ⟨_, keys, input, output, reading, expanded, ordered, checked⟩ :=
    (checkBytes_ok_iff _ _ _ _ _ _ _).mp h
  obtain ⟨pins, pre, natPins, hp, hq, hn, hw⟩ := ConLecheAdmission.checkConstants_with checked
  exact ⟨keys, input, output, reading, expanded, ordered, pins, pre, natPins, hp, hq, hn,
    ConLecheAdmission.checkConstantsWith_installed hw⟩

/-- **Model existence** for the certified ordered entry. -/
theorem checkBytes_has_model (V : Type v) [ConLeche.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {orderLimits : Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytes maxProjections limits orderLimits records blobs hint = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, installed⟩ := checkBytes_reading h
  exact installed.has_model V

/-- **No proof of `False`** for the certified ordered entry. -/
theorem checkBytes_no_proof_of_False (V : Type v) [ConLeche.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {orderLimits : Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytes maxProjections limits orderLimits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, installed⟩ := checkBytes_reading h
  exact installed.no_proof_of_False V

/-- On a read, expanded, canonically ordered input, every checker outcome
survives unchanged. -/
theorem checkBytes_of_ordered {maxProjections limits orderLimits records input output blobs hint}
    (within : Verify.Admission.WithinBatch limits records blobs)
    (keys : Verify.Admission.UniqueKeys records blobs)
    (reading : Verify.Admission.RecordsRead limits records input)
    (expanded : Projection.Expanded maxProjections input output)
    (ordered : Ordered orderLimits blobs input) :
    checkBytes maxProjections limits orderLimits records blobs hint =
      (ConLecheAdmission.checkConstants output blobs hint).mapError .checker := by
  have flight := (Verify.Admission.preflight_ok_iff _ _ _).mpr within
  have unique := (Verify.Admission.uniqueKeys_ok_iff _ _).mpr keys
  have decoded := (Verify.Admission.decodeRecords_ok_iff _ _ _).mpr reading
  have reconstructed := (Projection.reconstruct_ok_iff _ _ _).mpr expanded
  have order := (checkConstants_ok_iff _ _ _).mpr ordered
  simp [checkBytes, flight, unique, decoded, reconstructed, order, Except.mapError, bind, Except.bind]

end Ix.Ixon.BlockOrder
