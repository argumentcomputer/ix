import Ix.CompileCert.CheckCompiled
import IxC.Kernel.Verify.Cached.PushChain
import IxC.Kernel.Verify.Cached.KnotCongr

/-! # The certified fold, continued (package C, C-fold)

W+ folds its support rows with the certified checker on top of the admitted
artifact: the fact it needs is `checkDecls .verified pins (base ++ support) = .ok env`
(`FoldedSupport.checked`, `Ix/CompileCert/Changed.lean`). Computing it by running
`checkDecls` over `base ++ support` re-checks the whole artifact (on Mathlib about 78
of the run's 189 minutes and its 84 GB peak, `plans/review2/M5-B-budget.md` §9.4).
This module proves, from what `IxC` states about its own fold, that the fact
follows from the admission's two phases over `base` and the two phases over the
support **continued from the admission's state**, so that only the support is
installed and checked:

* `checkDecls` is phase A (`annotDeclStep` folded over the records) followed by
  phase B (`checkPendingList`, every pending record checked against the prefix
  view `fe.restrictTo pc.vis` from a fresh memo state);
  `IxC/Kernel/Cached/Installed.lean`. A fold over `base ++ support` is phase A over
  `base`, then phase A over `support` from where it stopped (`InstallRun.append`).
* Phase A only pushes fresh names onto a canonical index (`installRun_trace`,
  `IxC/Kernel/Verify/Cached/PushChain.lean`), so the final index extends the
  admission's, names stay unique, and at every bound up to the admission's length
  the two prefix views look every name up alike (`restrictTo_find?_of_chain`, from
  `mkFEnv_find?_visibleBelow` and `Env.prefixTo`, `IxC/Kernel/Verify/EnvBound.lean`).
* A pending check reads its index only through the prefix view's `find?`
  (`checkPending_congr`, from `coreKnotI_congr`, `opSIxC_congr` and
  `constsResolveFC_congr`, `IxC/Kernel/Verify/Cached/KnotCongr.lean`), so every
  record of the admission, checked there, is checked on the extended index.
* Hence `checkDecls_append_of_phases`: the admission's run and checks, the support's
  run continued from the admission's state and the checks of the support's own
  records give the fold over `base ++ support`, with the extended environment.

The one condition no `IxC` lemma states, that every pending record of the
admission names a bound within its environment (`pc.vis ≤ length`), is decided at
run time (`StagedAdmission.bounded`); it holds on every phase A, whose records
take the counter of the index they are installed at.

`prepareArtifactStaged` is `prepareArtifact` that keeps its phase A's result and
state (`StagedAdmission`): the same `AdmittedArtifact`, its `admitted` field proved
from the two phases instead of by running `checkBytes`. Nothing here changes
`IxC/**` or what any statement of the lane concludes. -/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission
open Ix.Kernel Ix.Kernel.Cached

/-! ## Two installs, one run -/

/-- Phase A's accepting runs compose: a run over `ds₁` followed by a run over
`ds₂` from where it stopped is a run over `ds₁ ++ ds₂`. -/
theorem InstallRun.append {mode : CheckMode} {pins : List NatOpPinSet} {ds₁ ds₂ : List Declaration}
    {p q r : Nat × FEnv × Array PendingCheck} {s₀ s₁ s₂ : CState}
    (h₁ : InstallRun mode pins ds₁ p s₀ q s₁) (h₂ : InstallRun mode pins ds₂ q s₁ r s₂) :
    InstallRun mode pins (ds₁ ++ ds₂) p s₀ r s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hstep _ ih => exact .cons hstep (ih h₂)

/-! ## The prefix view of an extended index -/

/-- `annotValC` reads its index only through `find?` (as `IxC`'s own
`annotValC_congr`, which its module does not re-export). -/
theorem annotValC_congr' {mode : CheckMode} {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotValC mode fe₁ = annotValC mode fe₂ := by
  funext cvA jty value record
  unfold annotValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]

/-- **A pending check reads its index only through the prefix view's `find?`.** -/
theorem checkPending_congr {mode : CheckMode} {fe₁ fe₂ : FEnv} {pc : PendingCheck}
    (hfe : (fe₁.restrictTo pc.vis).find? = (fe₂.restrictTo pc.vis).find?) :
    checkPending mode fe₁ pc = checkPending mode fe₂ pc := by
  unfold checkPending
  simp only [coreKnotI_congr hfe, opSIxC_congr hfe, annotValC_congr' hfe]

/-- The prefix of an environment extended at its front, at a bound within the
original, is the original's prefix. -/
theorem prefixTo_of_append {env₁ env₂ : Env} {new : List Kernel.ConstantInfo}
    (hext : env₂.consts = new ++ env₁.consts) {k : Nat} (hk : k ≤ env₁.consts.length) :
    env₂.prefixTo k = env₁.prefixTo k := by
  unfold Env.prefixTo
  have h1 : new.length ≤ new.length + env₁.consts.length - k := by omega
  have h2 : new.length + env₁.consts.length - k - new.length = env₁.consts.length - k := by omega
  rw [hext, List.length_append, List.drop_append, List.drop_eq_nil_of_le h1, List.nil_append, h2]

/-- **The prefix views of a canonical index and of a fresh-chain extension of it
agree below the original's length.** -/
theorem restrictTo_find?_of_chain {fe₁ fe₂ : FEnv}
    (h₁ : fe₁ = mkFEnv fe₁.env) (h₂ : fe₂ = mkFEnv fe₂.env) (hnd : NodupNames fe₂.env)
    {new : List Kernel.ConstantInfo} (hext : fe₂.env.consts = new ++ fe₁.env.consts)
    {k : Nat} (hk : k ≤ fe₁.env.consts.length) :
    (fe₂.restrictTo k).find? = (fe₁.restrictTo k).find? := by
  have hnd₁ : NodupNames fe₁.env := by
    unfold NodupNames at hnd ⊢
    rw [hext, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.1
  funext n
  have e₂ : (fe₂.restrictTo k).find? n = ((mkFEnv fe₂.env).restrictTo k).find? n := by rw [← h₂]
  have e₁ : (fe₁.restrictTo k).find? n = ((mkFEnv fe₁.env).restrictTo k).find? n := by rw [← h₁]
  rw [e₂, e₁, mkFEnv_find?_visibleBelow _ _ _ hnd, mkFEnv_find?_visibleBelow _ _ _ hnd₁,
    prefixTo_of_append hext hk]

/-! ## The fold over `base ++ support` from its two halves -/

/-- **The certified fold over `base ++ support`, composed.** Phase A over `base` from
the empty environment and phase B over its records (the admission), phase A over
`support` continued from the admission's accumulator and memo state, and phase B
over the records the support added: together they are the fold over
`base ++ support`, returning the extended environment. The bound on the
admission's records (`pc.vis` within its environment) is the one premise `IxC`
leaves to the caller. -/
theorem checkDecls_append_of_phases {mode : CheckMode} {pins : List NatOpPinSet}
    {base support : Array Declaration}
    {pa : Nat × FEnv × Array PendingCheck} {sa : CState}
    (runA : (base.toList.foldlM (annotDeclStep mode pins) (0, mkFEnv Env.empty, #[])) {} = .ok (pa, sa))
    (checkedA : checkPendingList mode pa.2.1 pa.2.2.toList = .ok ())
    (boundedA : ∀ pc ∈ pa.2.2.toList, pc.vis ≤ pa.2.1.env.consts.length)
    {pb : Nat × FEnv × Array PendingCheck} {sb : CState}
    (runB : (support.toList.foldlM (annotDeclStep mode pins) pa) sa = .ok (pb, sb))
    (checkedB : checkPendingList mode pb.2.1 (pb.2.2.toList.drop pa.2.2.size) = .ok ()) :
    checkDecls mode pins (base ++ support) = .ok pb.2.1.env := by
  have hA := InstallRun.of_foldlM mode base.toList _ _ runA
  have hB := InstallRun.of_foldlM mode support.toList _ _ runB
  obtain ⟨chainA, -⟩ := installRun_trace mode (env := Env.empty) hA (PushChain.refl Env.empty)
  obtain ⟨chainB, new, hnew⟩ := installRun_trace mode hB (PushChain.self chainA.canon)
  have hnd : NodupNames pb.2.1.env :=
    (chainA.trans chainB).2.2 (by simp [NodupNames, Env.empty])
  obtain ⟨added, hext⟩ := chainB.2.1
  have hall : checkPendingList mode pb.2.1 pb.2.2.toList = .ok () := by
    apply checkPendingList_ok
    intro pc hpc
    rw [hnew, List.mem_append] at hpc
    rcases hpc with old | fresh
    · obtain ⟨s', h⟩ := checkPendingList_records mode pa.2.1 pa.2.2.toList checkedA pc old
      refine ⟨s', ?_⟩
      rw [checkPending_congr (restrictTo_find?_of_chain chainA.canon chainB.canon hnd hext
        (boundedA pc old))]
      exact h
    · have hdrop : pb.2.2.toList.drop pa.2.2.size = new := by
        rw [hnew, ← Array.length_toList, List.drop_left]
      exact checkPendingList_records mode pb.2.1 _ checkedB pc (hdrop ▸ fresh)
  have run := InstallRun.foldlM mode (InstallRun.append hA hB)
  obtain ⟨n, fe, pend⟩ := pb
  unfold checkDecls
  rw [← Array.foldlM_toList, Array.toList_append, run]
  show (checkPendingList mode fe pend.toList >>= fun _ => pure fe.env) = _
  rw [hall]
  rfl

/-- Nothing is pending past an array's own records. -/
theorem checkPendingList_drop_size {mode : CheckMode} (fe : FEnv) (xs : Array PendingCheck) :
    checkPendingList mode fe (xs.toList.drop xs.size) = .ok () := by
  rw [← Array.length_toList, List.drop_length]
  rfl

/-! ## The admission, staged -/

/-- What continuing the admission's fold needs, kept from the admission: the
Nat-operation pin list, phase A's accumulator and memo state with the proof that
phase A over the prepared declarations produced them, phase B's acceptance of
every record, and the bound of every record within the installed environment. -/
structure StagedAdmission {input : ArtifactInput} (artifact : AdmittedArtifact input) where
  pins : List NatOpPinSet
  pins_checked : builtinNatOpPins = .ok pins
  installed : Nat × FEnv × Array PendingCheck
  state : CState
  run : ((Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations).toList.foldlM
    (annotDeclStep .verified pins) (0, mkFEnv Env.empty, #[])) {} = .ok (installed, state)
  checked : checkPendingList .verified installed.2.1 installed.2.2.toList = .ok ()
  bounded : ∀ pc ∈ installed.2.2.toList, pc.vis ≤ installed.2.1.env.consts.length

/-- The admitted environment is the installed one. -/
theorem StagedAdmission.env_eq {input : ArtifactInput} {artifact : AdmittedArtifact input}
    (staged : StagedAdmission artifact) : staged.installed.2.1.env = artifact.env := by
  obtain ⟨natPins, hn, hc⟩ := artifact.checked_declarations
  have same : natPins = staged.pins := Except.ok.inj (hn.symm.trans staged.pins_checked)
  subst same
  have h := checkDecls_append_of_phases (support := #[]) (pa := staged.installed) (sa := staged.state)
    (pb := staged.installed) (sb := staged.state) staged.run staged.checked staged.bounded rfl
    (checkPendingList_drop_size _ _)
  rw [Array.append_empty] at h
  exact Except.ok.inj (h.symm.trans hc)

/-- The admission's fold run over its own read of the decoded records, both phases
kept: the read, phase A's accumulator and memo state, phase B's acceptance, and the
bound of every pending record. -/
structure StagedFold (pins : Pins) (pre : Prelude) (natPins : List NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : Kernel.Ingress.Blobs)
    (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint) where
  installed : Nat × FEnv × Array PendingCheck
  state : CState
  /-- The read is a proof's witness only: the fold's declarations are not kept. -/
  run : ∃ decls, readStream pins pre constants blobs hint = .ok decls ∧
    ((Kernel.Frontend.preparePrelude pre.ix decls).toList.foldlM
      (annotDeclStep .verified natPins) (0, mkFEnv Env.empty, #[])) {} = .ok (installed, state)
  checked : checkPendingList .verified installed.2.1 installed.2.2.toList = .ok ()
  bounded : ∀ pc ∈ installed.2.2.toList, pc.vis ≤ installed.2.1.env.consts.length

/-- `checkConstantsWith`'s fold in its two phases, kept (`StagedFold`), or `none` when
either phase refuses or a pending record's bound fails (decided here, once). It reads
the records itself, as `checkBytes` does, so that the fold runs on declarations no one
else holds, as in the plain admission (the checker's walks memoize the subterms they
find shared); `@[noinline]` keeps its read apart from the caller's. -/
@[noinline] def stageFold (pins : Pins) (pre : Prelude) (natPins : List NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : Kernel.Ingress.Blobs)
    (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint) :
    Option (StagedFold pins pre natPins constants blobs hint) :=
  match hs : readStream pins pre constants blobs hint with
  | .error _ => none
  | .ok decls =>
    let prepared := Kernel.Frontend.preparePrelude pre.ix decls
    -- phase A as `checkDecls` runs it (over the array), read as the list fold by `Array.foldlM_toList`
    match hA : (prepared.foldlM (annotDeclStep .verified natPins) (0, mkFEnv Env.empty, #[])) {} with
    | .error _ => none
    | .ok (pa, sa) =>
      have ha : (prepared.toList.foldlM (annotDeclStep .verified natPins) (0, mkFEnv Env.empty, #[])) {} =
          .ok (pa, sa) := by rw [Array.foldlM_toList]; exact hA
      match hb : checkPendingList .verified pa.2.1 pa.2.2.toList with
      | .error _ => none
      | .ok () =>
        -- the environment's length once, not per record
        let length := pa.2.1.env.consts.length
        if hv : pa.2.2.toList.all (fun pc => decide (pc.vis ≤ length)) = true then
          some ⟨pa, sa, ⟨decls, hs, ha⟩, hb, fun pc hpc => of_decide_eq_true (List.all_eq_true.mp hv pc hpc)⟩
        else none

/-- **Admission, staged**: `prepareArtifact` with `checkBytes`'s fold computed in its
two phases and phase A's result and state kept (`StagedAdmission`, from `stageFold`);
the `AdmittedArtifact` is the same structure, its `admitted` field proved from the
phases (`checkBytes` unfolded to them by `checkBytesWith_eq`). When anything fails,
or the bound on the pending records does not hold, the plain `prepareArtifact`
decides (and reports its own error). -/
def prepareArtifactStaged (input : ArtifactInput) :
    Except Decline ((artifact : AdmittedArtifact input) × Option (StagedAdmission artifact)) :=
  -- a thunk: a `let` of the value itself may be computed whether or not a branch needs it
  let plain (_ : Unit) : Except Decline ((artifact : AdmittedArtifact input) × Option (StagedAdmission artifact)) :=
    (prepareArtifact input).map fun a => ⟨a, none⟩
  if hk : ArtifactKeysValid input then
  match hp : defaultPins, hq : builtinPrelude, hn : builtinNatOpPins with
  | .ok pins, .ok pre, .ok natPins =>
    match hf : preflight input.limits input.records input.blobs,
        hu : uniqueKeys input.records input.blobs,
        hc : decodeRecords input.limits input.records with
    | .ok (), .ok (), .ok constants =>
      match stageFold pins pre natPins constants input.blobs input.hint with
      | none => plain ()
      | some fold =>
        -- the artifact's own reading (declarations and reader state), apart from the fold's
        match hr : readRecords (streamContext pins pre constants input.blobs input.hint)
            pre.state constants.toArray with
        | .error _ => plain ()
        | .ok (state, decls) =>
          have hs : readStream pins pre constants input.blobs input.hint = .ok decls := by
            unfold readStream
            change (match readRecords
              (streamContext pins pre constants input.blobs input.hint)
              pre.state constants.toArray with
              | .ok (_, ds) => Except.ok ds
              | .error (e, i) => Except.error (Kernel.Admission.Error.read i e)) = .ok decls
            rw [hr]
          have ha : ((Kernel.Frontend.preparePrelude pre.ix decls).toList.foldlM
              (annotDeclStep .verified natPins) (0, mkFEnv Env.empty, #[])) {} = .ok (fold.installed, fold.state) := by
            obtain ⟨d, hread, hrun⟩ := fold.run
            obtain rfl : d = decls := Except.ok.inj (hread.symm.trans hs)
            exact hrun
          have hd : checkDecls .verified natPins (Kernel.Frontend.preparePrelude pre.ix decls) =
              .ok fold.installed.2.1.env := by
            have h := checkDecls_append_of_phases (support := #[]) (pb := fold.installed) (sb := fold.state)
              ha fold.checked fold.bounded rfl (checkPendingList_drop_size _ _)
            rwa [Array.append_empty] at h
          have admitted : checkBytes input.limits input.records input.blobs input.hint =
              .ok fold.installed.2.1.env := by
            unfold checkBytes
            simp only [hp, hq, hn, Except.mapError, bind, Except.bind]
            rw [checkBytesWith_eq]
            simp only [hf, hu, hc, Except.mapError, bind, Except.bind, checkConstantsWith, hs, hd]
          let artifact : AdmittedArtifact input :=
            ⟨hk, fold.installed.2.1.env, admitted, pins, hp, pre, hq, constants, hc, decls, state, hr, hs⟩
          .ok ⟨artifact, some ⟨natPins, hn, fold.installed, fold.state, ha, fold.checked, fold.bounded⟩⟩
    | _, _, _ => plain ()
  | _, _, _ => plain ()
  else plain ()

end Ix.CompileCert
