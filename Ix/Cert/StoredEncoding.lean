import Ix.Cert.Resolution
import Ix.Cert.Stream
import IxC.Ixon.Verify.Framing
import IxC.Ixon.Verify.BoundedConstant

/-! # The compiled store is canonically encoded

`Stream.StoredCanonical` asks that every stored record of the compiled closure decode to a
wire-valid constant whose canonical encoding is its stored bytes. This module reduces that,
for every order of a compiled artifact, to the fold's store: the artifact stores each of the
fold's final records as its own buffer (`assembleEnv_consts_inv`, with the original-data
finalization keeping the records), and a wire-valid canonical encoding within the loader's
universe budget decodes to that constant (`get?_serConstant`). So the artifact is stored canonically
once every record the fold stores is such an encoding (`Encoded`); the fold starts from an
empty store (`compileReport_start`, `FoldStart`), so it is enough that every outcome the fold
applies to a reached state keeps its store encoded (`StepsEncode`, `storedCanonical_of_steps`).

`StepsEncode` is the fold's provenance: a merge stores the block's record, its projections and
its auxiliary records (`blockRecordWrites`), each the encoding of a constant the block compile
returned, which the block codec theorems (`EmissionDispatch.constant_codec`,
`MutualArtifact.mutual_correct`) show wire-valid. Successful block compilation checks the
universe budget for its block and projection records (`BlockRecords.runBlock_bounded`). -/

namespace Ix.Cert.StoredEncoding

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule

/-- Every record is a wire-valid constant's canonical encoding and fits the
production loader's aggregate universe-expansion budget. -/
def Encoded (store : Std.HashMap Address ByteArray) : Prop :=
  ∀ a b, store.get? a = some b → ∃ c : Ixon.Constant, c.wireWF ∧
    Ixon.Bounded.univNodes c.univs ≤ Ixon.loadMaxUnivNodes ∧ Ixon.serConstant c = b

theorem encoded_empty : Encoded ({} : Std.HashMap Address ByteArray) := fun a b h => by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
  cases h

/-! ## Decoding an encoded record -/

/-- A wire-valid constant within the loader's universe budget parses back
from its canonical encoding in place. -/
theorem deConstantAt_serConstant {c : Ixon.Constant} (h : c.wireWF)
    (fits : Ixon.Bounded.univNodes c.univs ≤ Ixon.loadMaxUnivNodes) :
    Ixon.deConstantAt (Ixon.serConstant c) 0 (Ixon.serConstant c).size = .ok c := by
  have exact := Ixon.Verify.deConstantExact_serConstant c h
  unfold Ixon.deConstantExact at exact
  obtain ⟨state, hrun, hidx⟩ := Ixon.Verify.runGetExact_complete exact
  have bounded := Ixon.Verify.BoundedConstant.getConstant_complete _ _ _ _ hrun fits
  unfold Ixon.deConstantAt
  simp only [EStateM.run]
  rw [ite_eq_left (Nat.le_of_eq (Nat.zero_add _)), bounded]
  simp [hidx]

/-- **A wire-valid constant's canonical encoding, held as its own buffer, decodes to it**,
and is its own raw bytes. -/
theorem get?_serConstant {c : Ixon.Constant} (h : c.wireWF)
    (fits : Ixon.Bounded.univNodes c.univs ≤ Ixon.loadMaxUnivNodes) :
    ({ buf := Ixon.serConstant c, len := (Ixon.serConstant c).size } : Ixon.LazyConstant).get? = some c ∧
      ({ buf := Ixon.serConstant c, len := (Ixon.serConstant c).size } : Ixon.LazyConstant).rawBytes =
        Ixon.serConstant c := by
  refine ⟨?_, by simp [Ixon.LazyConstant.rawBytes]⟩
  show (Ixon.deConstantAt (Ixon.serConstant c) 0 (Ixon.serConstant c).size).toOption = some c
  rw [deConstantAt_serConstant h fits]
  rfl

/-! ## The artifact's store is the fold's -/

/-- **Every record the assembled environment stores is one of the driver's records**, as its
own buffer. -/
theorem assembleEnv_consts_inv (acc : DriverAcc) {a : Address} {lc : Ixon.LazyConstant}
    (h : (assembleEnv acc).1.consts.get? a = some lc) :
    ∃ b, acc.cenv.constants.get? a = some b ∧ lc = { buf := b, len := b.size } := by
  change (acc.cenv.constants.fold (init := {}) fun (m : Std.HashMap Address Ixon.LazyConstant) a bytes =>
    m.insert a ({ buf := bytes, len := bytes.size } : Ixon.LazyConstant)).get? a = some lc at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  have step : ∀ (l : List (Address × ByteArray)) (m : Std.HashMap Address Ixon.LazyConstant),
      (l.foldl (fun m x => m.insert x.1 ({ buf := x.2, len := x.2.size } : Ixon.LazyConstant)) m).get? a =
        some lc → m.get? a = some lc ∨ ∃ b, (a, b) ∈ l ∧ lc = { buf := b, len := b.size } := by
    intro l
    induction l with
    | nil => intro m hm; exact .inl hm
    | cons x l ih =>
      intro m hm
      rw [List.foldl_cons] at hm
      rcases ih _ hm with hm | ⟨b, hb, rfl⟩
      · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hm
        split at hm
        · rename_i same
          have e : x.1 = a := beq_iff_eq.mp same
          cases hm
          exact .inr ⟨x.2, by rw [← e]; exact List.mem_cons_self, rfl⟩
        · exact .inl (by rw [Std.HashMap.get?_eq_getElem?]; exact hm)
      · exact .inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
  rcases step _ _ h with hm | ⟨b, hb, rfl⟩
  · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hm
    cases hm
  · refine ⟨b, ?_, rfl⟩
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hb

/-- **An artifact that stores an encoded store's records, each as its own buffer, is stored
canonically.** -/
theorem storedCanonical_of_store {ixe : Ixon.Env} {store : Std.HashMap Address ByteArray}
    (stores : ∀ a lc, ixe.consts.get? a = some lc → ∃ b, store.get? a = some b ∧ lc = { buf := b, len := b.size })
    (encoded : Encoded store) (order : List Address) : Stream.StoredCanonical ixe order := by
  intro a _ lc hlc
  obtain ⟨b, hb, rfl⟩ := stores a lc hlc
  obtain ⟨c, wire, fits, rfl⟩ := encoded a b hb
  obtain ⟨hget, hraw⟩ := get?_serConstant wire fits
  exact ⟨c, hget, wire, hraw.symm⟩

/-! ## The fold keeps its store encoded -/

/-- **Every outcome the fold applies keeps the store encoded**: a condensation block's outcome,
computed against a reached state and applied to a reached state that follows it, leaves an
encoded store encoded. -/
def StepsEncode (blocks : Ix.CondensedBlocks) (init : DriverAcc) : Prop :=
  ∀ (snap acc : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name),
    Reach blocks init snap → Reach blocks init acc → Mono snap.cenv acc.cenv →
    blocks.blocks.get? rep = some all → Encoded acc.cenv.constants →
    Encoded (applyAuxBlockOutcome acc (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)).1.cenv.constants

/-- Every state the fold reaches from an encoded start has an encoded store. -/
theorem reach_encoded {blocks : Ix.CondensedBlocks} {init : DriverAcc}
    (start : Encoded init.cenv.constants) (steps : StepsEncode blocks init) :
    ∀ {acc : DriverAcc}, Reach blocks init acc → Encoded acc.cenv.constants := by
  intro acc h
  induction h with
  | init => exact start
  | step hsnap hacc hm hall _ ih => exact steps _ _ _ _ hsnap hacc hm hall ih

/-- **The fold's start**: its store and resolution map are empty, and it views the
input. -/
structure FoldStart (env : Ix.Environment) (cenv₀ : CompileEnv) : Prop where
  constants : cenv₀.constants = {}
  nameToAddr : cenv₀.nameToAddr = {}
  view : cenv₀.env = { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) }

/-- **The fold behind a compile**: `compileReport` ran the waves over its condensation from a
start with an empty store (`FoldStart`), and the artifact stores the final state's records,
each as its own buffer. -/
theorem compileReport_start {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      FoldStart env cenv₀ ∧
      foldWavesSeq (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched
        ((Ix.CondenseM.run (groundSplit { consts := env.consts }).1).blocks.size + 1)
        (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched) = .ok st ∧
      ∀ a lc, ixe.consts.get? a = some lc →
        ∃ b, st.acc.cenv.constants.get? a = some b ∧ lc = { buf := b, len := b.size } := by
  obtain ⟨cenv, hu, -⟩ := compileReport_ok h
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold hu
  rw [compileEnvFold_eq_seq] at hf
  unfold compileEnvFoldSeq at hf
  generalize missingBlockRefs? _ = missing at hf
  generalize validateInductiveFlags _ = flags at hf
  generalize validateMutualSafety _ _ = safety at hf
  cases missing <;> cases flags <;> cases safety <;>
    simp only [bind, Except.bind, pure, Except.pure] at hf <;> try cases hf
  generalize hr : foldWavesSeq _ _ _ _ = r at hf
  cases r with
  | error => cases hf
  | ok st =>
    simp only [finalizeEnv, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, -, -⟩ := hf
    exact ⟨_, _, st, ⟨rfl, rfl, rfl⟩, hr, fun a lc hlc => assembleEnv_consts_inv _ hlc⟩

/-- **A compile whose fold keeps its store encoded is stored canonically**, in every order:
from a start like the fold's (`FoldStart`), every outcome the fold applies keeps the store
encoded. -/
theorem storedCanonical_of_steps {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures))
    (steps : ∀ (cenv₀ : CompileEnv) (sched : FoldSchedule), FoldStart env cenv₀ →
      StepsEncode (Ix.CondenseM.run (groundSplit { consts := env.consts }).1)
        (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched).acc)
    (order : List Address) : Stream.StoredCanonical ixe order := by
  obtain ⟨cenv₀, sched, st, h₀, hst, stores⟩ := compileReport_start h
  have start : Encoded (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1)
      sched).acc.cenv.constants := by
    show Encoded cenv₀.constants
    rw [h₀.constants]
    exact encoded_empty
  have reached := foldWavesSeq_reach _ _ _ hst (Reach.init (blocks := Ix.CondenseM.run
    (groundSplit { consts := env.consts }).1) (init := (FoldState.init cenv₀ _ sched).acc))
  exact storedCanonical_of_store stores (reach_encoded start (steps cenv₀ sched h₀) reached) order

/--
info: 'Ix.Cert.StoredEncoding.storedCanonical_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms storedCanonical_of_steps

end Ix.Cert.StoredEncoding
