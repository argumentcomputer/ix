import Ix.Cert.StoredEncoding
import Ix.Cert.BlockWire
import Ix.Cert.FreshSnapshot

/-! # The fold keeps its store encoded

`StoredEncoding.StepsEncode`: every outcome the fold applies keeps every stored record the
canonical encoding of a wire-valid constant (`stepsEncode`). A failed outcome, or a compiled
one whose check fails, stores nothing. A merged outcome stores its block record and then each
projection (`mergeCompiledBlock_constants`): the block record is the serialization of the block
`runBlock` returned (`BlockLayout.ResultShape.bytes`), which is wire-valid (`BlockWire.blocksWire`),
and every projection is the block itself or a wire-valid projection of it
(`BlockLayout.ResultShape.rows`).

So a compiled artifact is stored canonically in every order (`storedCanonical_of_compile`), from
the compile alone. -/

namespace Ix.Cert.StepsEncode

open Ix.CompileM Ix.Cert.Resolution
open Ix.Cert.StoredEncoding (Encoded StepsEncode)

/-- Storing a wire-valid constant's canonical encoding keeps a store encoded. -/
theorem encoded_insert {store : Std.HashMap Address ByteArray} (h : Encoded store) (a : Address)
    {c : Ixon.Constant} (wire : c.wireWF) {b : ByteArray} (hb : Ixon.serConstant c = b) :
    Encoded (store.insert a b) := by
  intro k v hk
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hk
  split at hk
  · cases hk
    exact ⟨c, wire, hb⟩
  · exact h k v (by rw [Std.HashMap.get?_eq_getElem?]; exact hk)

set_option hygiene false in
/-- `mergeCompiledBlock`'s loops after its primary registrations, which leave the stored
records: the block's `Muts` entry and the class registry. -/
local macro "constants_tail" held:term:max : tactic => `(tactic| (
  refine loop_bind (P := fun d : DriverAcc => Q d.cenv.constants)
    (I := fun c : CompileEnv => Q c.constants) _ _ _ _ $held ?_ ?_
  · intro _ _ _ h; split <;> exact h
  · intro L' hL'
    split
    · refine loop_bind (P := fun d : DriverAcc => Q d.cenv.constants)
        (I := fun c : CompileEnv => Q c.constants) _ _ _ _ hL' ?_ ?_
      · intro cls _ s hs
        exact forIn_inv_array (fun c : CompileEnv => Q c.constants) _ cls (by intros; assumption) s hs
      · intro _ h
        exact h
    · exact hL'))

/-- **A merge stores the block's record, then each projection's**: a property of stores that
those writes keep holds of the merged store. -/
theorem mergeCompiledBlock_constants (Q : Std.HashMap Address ByteArray → Prop) {acc : DriverAcc}
    {lo : Ix.Name} {result : BlockResult} {cache : BlockState}
    (block : Q (acc.cenv.constants.insert result.blockAddr result.blockBytes))
    (rows : ∀ p ∈ result.projections, ∀ s, Q s →
      Q (s.insert (Address.admissionHash (Ixon.ser p.2.1)) (Ixon.ser p.2.1))) :
    Q (mergeCompiledBlock acc lo result cache).cenv.constants := by
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · split
    · constants_tail block
    · constants_tail block
  · refine loop_bind (P := fun d : DriverAcc => Q d.cenv.constants)
      (I := fun c : CompileEnv => Q c.constants) _ _ _ _ block ?_ ?_
    · intro x hx s hs
      split <;> exact rows x hx _ hs
    · intro L hL
      constants_tail hL

/-- **Applying an outcome stores only what its merge stores**: a property of stores the state
has holds after the outcome, if it holds of every checked merge of a compiled outcome. -/
theorem applyAuxBlockOutcome_constants (Q : Std.HashMap Address ByteArray → Prop) (acc : DriverAcc)
    (lo : Ix.Name) (all : Ix.Set Ix.Name) (o : AuxBlockOutcome) (h : Q acc.cenv.constants)
    (merged : ∀ r c, o = .compiled r c → checkCompiledBlock acc.cenv lo r c = .ok () →
      Q (mergeCompiledBlock acc lo r c).cenv.constants) :
    Q (applyAuxBlockOutcome acc lo all o).1.cenv.constants := by
  cases o with
  | compiled r c =>
    unfold applyAuxBlockOutcome
    simp only [Id.run]
    split
    · exact loop_bind _ _ _ _ (fun d : DriverAcc => Q d.cenv.constants) (fun d : DriverAcc => Q d.cenv.constants)
        h (fun _ _ _ h => h) (fun _ h => h)
    · rename_i hc
      have hm := merged r c rfl hc
      split
      · exact FreshSnapshot.loopNames_any (Q := fun d => Q d.cenv.constants) _ _ _ _ fun _ => hm
      · exact FreshSnapshot.loopNames_any (Q := fun d => Q d.cenv.constants) _ _ _ _
          fun _ => FreshSnapshot.loopNames_any (Q := fun d => Q d.cenv.constants) _ _ _ _ fun _ => hm
  | failed msg =>
    unfold applyAuxBlockOutcome
    simp only [Id.run]
    exact loop_bind _ _ _ _ (fun d : DriverAcc => Q d.cenv.constants) (fun d : DriverAcc => Q d.cenv.constants)
      h (fun _ _ _ h => h) (fun _ h => h)

/-- **A block's merge keeps the store encoded**: its block record is the wire-valid block's
encoding, and each projection is the block or a wire-valid projection of it. -/
theorem merge_encoded {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} (hr : runBlock cenv all lo = .ok (r, c)) (acc : DriverAcc)
    (h : Encoded acc.cenv.constants) : Encoded (mergeCompiledBlock acc lo r c).cenv.constants := by
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  refine mergeCompiledBlock_constants Encoded (encoded_insert h _ wire shape.bytes.symm) ?_
  intro p hp s hs
  have pwire : p.2.1.wireWF := by
    rcases shape.rows p hp with same | ⟨pw, -, -⟩
    · rw [same]; exact wire
    · exact pw
  exact encoded_insert hs _ pwire rfl

/-- **Every outcome the fold applies keeps the store encoded** (`StoredEncoding.StepsEncode`),
for every condensation and start. -/
theorem stepsEncode (blocks : Ix.CondensedBlocks) (init : DriverAcc) : StepsEncode blocks init := by
  intro snap acc rep all _ _ _ _ henc
  refine applyAuxBlockOutcome_constants Encoded acc _ all _ henc fun r c ho _ => ?_
  unfold auxBlockOutcome at ho
  split at ho
  · cases ho
  · rename_i result cache hrun
    cases ho
    exact merge_encoded hrun acc henc

/-- **A compiled artifact is stored canonically**, in every order. -/
theorem storedCanonical_of_compile {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) (order : List Address) : Stream.StoredCanonical ixe order :=
  StoredEncoding.storedCanonical_of_steps h (fun _ _ _ => stepsEncode _ _) order

/--
info: 'Ix.Cert.StepsEncode.stepsEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stepsEncode

/--
info: 'Ix.Cert.StepsEncode.storedCanonical_of_compile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms storedCanonical_of_compile

end Ix.Cert.StepsEncode
