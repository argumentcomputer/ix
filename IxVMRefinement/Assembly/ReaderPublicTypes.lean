import IxVMRefinement.Assembly.ReaderPublicKeys

/-! # Public value types throughout an actual record stream

Generated model declarations are kept separate. Every other value declaration comes from a
member reader, whose header conversion includes only public keys and keeps projection targets.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (RolesKeyed ite_ok fail_bind throw_ok)

private theorem forIn_valueTypes {α σ : Type} (I : σ → Prop)
    (f : α → σ → ReadM (ForInStep σ))
    (step : ∀ x s r, I s → f x s = .ok r → ∃ s', r = .yield s' ∧ I s') :
    ∀ (xs : List α) {s res : σ}, I s → forIn xs s f = .ok res → I res
  | [], _, _, invariant, read => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at read
    rwa [← read]
  | x :: xs, _, _, invariant, read => by
    rw [List.forIn_cons] at read
    obtain ⟨result, first, rest⟩ := except_bind_ok.mp read
    obtain ⟨next, rfl, nextInvariant⟩ := step x _ result invariant first
    exact forIn_valueTypes I f step xs nextInvariant rest

private theorem lowerTwin_publicValueTypes {md : Mode} {cx : Ctx md}
    {twins : Array (ConstRef _root_.Address × RecEntry)} {r : Read md}
    (read : lowerTwin cx twins = .ok r) :
    ∀ d ∈ r.decls.toList, d.isGenerated = false → ValueTypePublic d := by
  unfold lowerTwin at read
  split at read
  · dsimp only at read
    rcases ite_ok read with read | read
    · split at read
      · split at read
        · split at read
          · rcases ite_ok read with read | read
            · split at read
              · rcases ite_ok read with read | read
                · exact (fail_bind read).elim
                · rcases ite_ok read with read | read
                  · obtain ⟨_, _, read⟩ := except_bind_ok.mp read
                    obtain ⟨recs, _, read⟩ := except_bind_ok.mp read
                    simp only [ite_not, bne_iff_ne, ne_eq] at read
                    split at read
                    all_goals
                      rcases ite_ok read with read | read
                      all_goals obtain ⟨_, _, read⟩ := except_bind_ok.mp read
                      all_goals
                        split at read
                        · exact (fail_bind read).elim
                        · simp only [pure, Except.pure, Except.ok.injEq] at read
                          subst read
                          intro d member _
                          simp only [Array.toList_singleton, List.mem_singleton] at member
                          subst d
                          trivial
                  · exact (fail_bind read).elim
              · exact (throw_ok read).elim
            · exact (fail_bind read).elim
          · exact (throw_ok read).elim
        · exact (throw_ok read).elim
      · exact (throw_ok read).elim
    · exact (fail_bind read).elim
  · simp only [pure, Except.pure, Except.ok.injEq] at read
    subst read
    intro _ member
    cases member

private theorem readInductive_publicValueTypes {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read md}
    (read : readInductive cx st owner c ms = .ok r) :
    ∀ d ∈ r.decls.toList, d.isGenerated = false → ValueTypePublic d := by
  obtain ⟨lowerState, blockRead, lowered⟩ := Ix.Cert.EvidenceTransfer.readInductive_lower read
  obtain ⟨generated, declarations, count, _, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok lowered
  have allGenerated := Ix.Cert.SourceNames.lowerInductive_generated lowered
  rw [declarations, count, Array.toList_push, List.toList_toArray, List.take_left] at allGenerated
  intro d member notGenerated
  rw [declarations, Array.toList_push, List.toList_toArray, List.mem_append] at member
  rcases member with inGenerated | closer
  · have generated := allGenerated d inGenerated
    rw [notGenerated] at generated
    cases generated
  · obtain rfl := List.mem_singleton.mp closer
    trivial

/-- Every actual non-generated value declaration has a public raw type. -/
theorem readRecord_publicValueTypes {cx : Ctx .anon} (hrk : RolesKeyed cx) {st : State .anon}
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read .anon}
    (read : readRecord cx st owner c = .ok r) :
    ∀ d ∈ r.decls.toList, d.isGenerated = false → ValueTypePublic d := by
  unfold readRecord at read
  cases info : c.info with
  | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    simp only [info] at read
    rcases ite_ok read with read | read
    · exact (fail_bind read).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at read
      subst read
      intro _ member
      cases member
  | defn defnRec =>
    simp only [info] at read
    have selfPublic : ∀ i m k,
        (if i == 0 then some (cx.memberKey (.member owner 0)) else none) = some m →
        m = .ok k → NonAuxKey k := by
      intro i m k selected found
      split at selected
      · injection selected with selected
        rw [← selected] at found
        exact memberKey_nonAux hrk found
      · cases selected
    obtain ⟨⟨decl, rewrote⟩, definition, read⟩ := except_bind_ok.mp read
    simp only [pure, Except.pure, Except.ok.injEq] at read
    subst read
    intro d member _
    simp only [Array.toList_singleton, List.mem_singleton] at member
    subst d
    exact readDefinition_publicType hrk selfPublic definition
  | recr _ =>
    simp only [info] at read
    rcases ite_ok read with read | read
    · simp only [pure, Except.pure, Except.ok.injEq] at read
      subst read
      intro _ member
      cases member
    · split at read
      · exact lowerTwin_publicValueTypes read
      · exact (throw_ok read).elim
  | axio ax =>
    simp only [info] at read
    rcases ite_ok read with read | read
    · exact (fail_bind read).elim
    · obtain ⟨_, _, read⟩ := except_bind_ok.mp read
      obtain ⟨_, _, read⟩ := except_bind_ok.mp read
      simp only [pure, Except.pure, Except.ok.injEq] at read
      subst read
      intro d member _
      simp only [Array.toList_singleton, List.mem_singleton] at member
      subst d
      trivial
  | quot q =>
    simp only [info] at read
    obtain ⟨_, _, read⟩ := except_bind_ok.mp read
    obtain ⟨_, _, read⟩ := except_bind_ok.mp read
    simp only [pure, Except.pure, Except.ok.injEq] at read
    subst read
    intro d member _
    simp only [Array.toList_singleton, List.mem_singleton] at member
    subst d
    trivial
  | muts ms =>
    simp only [info] at read
    rcases ite_ok read with read | read
    · rcases ite_ok read with read | read
      · exact (fail_bind read).elim
      · obtain ⟨ind, indRead, finish⟩ := except_bind_ok.mp read
        have indTypes := readInductive_publicValueTypes indRead
        rcases finishInductiveRead_spec finish with rfl | ⟨twin, twinRead, rfl⟩
        · exact indTypes
        · intro d member notGenerated
          rw [Array.toList_append, List.mem_append] at member
          exact member.elim (fun hd => indTypes d hd notGenerated)
            (fun hd => lowerTwin_publicValueTypes twinRead d hd notGenerated)
    · rcases ite_ok read with read | read
      · rcases ite_ok read with read | read
        · simp only [pure, Except.pure, Except.ok.injEq] at read
          subst read
          intro _ member
          cases member
        · obtain ⟨_, _, read⟩ := except_bind_ok.mp read
          exact lowerTwin_publicValueTypes read
      · rcases ite_ok read with read | read
        · split at read
          · exact (fail_bind read).elim
          · split at read
            · have selfPublic : ∀ i m k,
                  (if i < ms.size then some (cx.memberKey (.member owner i)) else none) = some m →
                  m = .ok k → NonAuxKey k := by
                intro i m k selected found
                split at selected
                · injection selected with selected
                  rw [← selected] at found
                  exact memberKey_nonAux hrk found
                · cases selected
              obtain ⟨result, loop, read⟩ := except_bind_ok.mp read
              simp only [pure, Except.pure, Except.ok.injEq] at read
              subst read
              rw [← Array.forIn_toList] at loop
              exact forIn_valueTypes
                (fun s => ∀ d ∈ s.2.1.toList, d.isGenerated = false → ValueTypePublic d)
                _
                (fun _ s q invariant step => by
                  obtain ⟨⟨decl, rewrote⟩, definition, step⟩ := except_bind_ok.mp step
                  have publicType := readDefinition_publicType hrk selfPublic definition
                  dsimp only at step
                  split at step <;> split at step <;>
                  · simp only [pure, Except.pure, Except.ok.injEq] at step
                    subst step
                    refine ⟨_, rfl, fun d member notGenerated => ?_⟩
                    rw [Array.toList_push, List.mem_append, List.mem_singleton] at member
                    rcases member with member | rfl
                    · exact invariant d member notGenerated
                    · exact publicType)
                _ (by simp) loop
            · exact (throw_ok read).elim
        · exact (throw_ok read).elim

/-- The property follows the actual record stream without any state invariant premise. -/
theorem StreamRead.publicValueTypes {cx : Ctx .anon} (hrk : RolesKeyed cx)
    {st st' : State .anon} {records : List (_root_.Address × Ixon.Constant)}
    {out : Array (Declaration .anon)} (read : StreamRead cx st records st' out) :
    ∀ d ∈ out.toList, d.isGenerated = false → ValueTypePublic d := by
  induction read with
  | nil => intro _ member; cases member
  | cons first _ ih =>
    intro d member notGenerated
    rw [Array.toList_append, List.mem_append] at member
    exact member.elim (fun hd => readRecord_publicValueTypes hrk first d hd notGenerated)
      (fun hd => ih d hd notGenerated)

/-- The actual committed prelude reading supplies the same type support. -/
theorem preludeFor_publicValueTypes {table : RoleTable} {pre : Prelude .anon}
    (prepared : preludeFor table = .ok pre) :
    ∀ d ∈ pre.ix.decls.toList, d.isGenerated = false → ValueTypePublic d := by
  obtain ⟨records, extra, extraBlobs, read⟩ := preludeRead_unpack (preludeFor_checks prepared).1
  have keyed : RolesKeyed (contextOf (md := .anon) table records [] extra extraBlobs) :=
    contextOf_rolesKeyed (md := .anon) table records [] extra extraBlobs _ _
  exact (readRecords_spec read).publicValueTypes keyed

/-- Prelude selection and ground hoisting preserve the actual raw header property. -/
theorem preparePrelude_publicValueTypes {pre : Frontend.PreludeIx .anon}
    {input : Array (Declaration .anon)}
    (preludeTypes : ∀ d ∈ pre.decls.toList, d.isGenerated = false → ValueTypePublic d)
    (inputTypes : ∀ d ∈ input.toList, d.isGenerated = false → ValueTypePublic d) :
    ∀ d ∈ (Frontend.preparePrelude pre input).toList,
      d.isGenerated = false → ValueTypePublic d := by
  obtain ⟨extra, covered, permutation⟩ := Frontend.preparePrelude_perm pre input
  intro d member notGenerated
  have original := permutation.mem_iff.mp member
  rcases List.mem_append.mp original with inInput | inExtra
  · exact inputTypes d inInput notGenerated
  · exact preludeTypes d (covered d inExtra) notGenerated

/-- The coherent admission witness supplies public raw types in its actual prepared array. -/
theorem admitted_publicValueTypes {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    ∀ d ∈ (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList,
      d.isGenerated = false → ValueTypePublic d := by
  have keyed := streamContext_rolesKeyed _root_.Address.admissionHash w.table w.prelude
    (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
  exact preparePrelude_publicValueTypes (preludeFor_publicValueTypes w.preludeRead)
    ((readRecords_spec w.read).publicValueTypes keyed)

end IxVM.Refinement.Assembly
