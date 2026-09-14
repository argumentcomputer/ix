/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Expr
import Ix.Kernel.Verify.UniverseSupport
import Ix.Theory.Model.LevelCongruence

/-!
# Production universe instantiation in the consistency model

The existing walker proof establishes equality with its memo-free specification
under finite interning support. This module connects that specification to
the structural reader, including simplifying universe constructors and lets.
Its final theorem supplies an annotated reading of the actual returned tree,
with the same interpretation and hereditary validity as model substitution.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

/-- The precise level-side assumptions used by the simplifying constructors. -/
structure UniverseSubstitutionSupport (arguments : Array (KUniv .anon))
    (term : KExpr .anon) : Prop where
  faithful : ∀ left right, KExpr.LevelReach arguments term left →
    KExpr.LevelReach arguments term right → left.AddrFaithful right
  bounded : ∀ level, KExpr.LevelReach arguments term level → level.size < UInt64.size

private theorem substUniv_readLevel {arguments : Array (KUniv .anon)}
    {level result : KUniv .anon}
    (run : TcM.substUniv level arguments = .ok result)
    (faithful : ∀ left right, KUniv.SubstUnivReach arguments level left →
      KUniv.SubstUnivReach arguments level right → left.AddrFaithful right)
    (bounded : ∀ value, KUniv.SubstUnivReach arguments level value →
      value.size < UInt64.size) :
    (readLevel level).inst (arguments.toList.map readLevel) ≈ readLevel result := by
  rw [show (readLevel : KUniv .anon → VLevel) = KUniv.toVLevel from funext readLevel_eq]
  exact VLevel.equiv_def.mpr fun valuation =>
    (VLevel.equiv_def.mp (TcM.substUniv_toVLevel run faithful bounded) valuation).symm

private theorem list_substUniv_readLevels {arguments : Array (KUniv .anon)} :
    ∀ {levels results : List (KUniv .anon)},
      levels.mapM (TcM.substUniv · arguments) = .ok results →
      (∀ level ∈ levels, ∀ left right, KUniv.SubstUnivReach arguments level left →
        KUniv.SubstUnivReach arguments level right → left.AddrFaithful right) →
      (∀ level ∈ levels, ∀ value, KUniv.SubstUnivReach arguments level value →
        value.size < UInt64.size) →
      ∀ valuation,
        ((levels.map readLevel).map (VLevel.inst (arguments.toList.map readLevel))).map
          (VLevel.eval valuation) = (results.map readLevel).map (VLevel.eval valuation) := by
  intro levels
  induction levels with
  | nil =>
      intro results run _ _ valuation
      simp only [List.mapM_nil] at run
      cases run
      rfl
  | cons level rest ih =>
      intro results run faithful bounded valuation
      rw [List.mapM_cons] at run
      cases first : TcM.substUniv level arguments with
      | error err => rw [first] at run; contradiction
      | ok result =>
          cases tail : rest.mapM (TcM.substUniv · arguments) with
          | error err => rw [first, tail] at run; contradiction
          | ok remaining =>
              rw [first, tail] at run
              cases run
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨VLevel.equiv_def.mp (substUniv_readLevel first
                (faithful level List.mem_cons_self) (bounded level List.mem_cons_self)) valuation,
                ih tail
                  (fun level member => faithful level (List.mem_cons_of_mem _ member))
                  (fun level member => bounded level (List.mem_cons_of_mem _ member)) valuation⟩

private theorem array_substUniv_readLevels {arguments levels results : Array (KUniv .anon)}
    (run : levels.mapM (TcM.substUniv · arguments) = .ok results)
    (faithful : ∀ level ∈ levels, ∀ left right, KUniv.SubstUnivReach arguments level left →
      KUniv.SubstUnivReach arguments level right → left.AddrFaithful right)
    (bounded : ∀ level ∈ levels, ∀ value, KUniv.SubstUnivReach arguments level value →
      value.size < UInt64.size) :
    ∀ valuation,
      ((levels.toList.map readLevel).map (VLevel.inst (arguments.toList.map readLevel))).map
        (VLevel.eval valuation) = (results.toList.map readLevel).map (VLevel.eval valuation) := by
  have listRun : levels.toList.mapM (TcM.substUniv · arguments) = .ok results.toList := by
    rw [← Array.toList_mapM, run]
    rfl
  exact list_substUniv_readLevels listRun
    (fun level member => faithful level (by simpa using member))
    (fun level member => bounded level (by simpa using member))

private theorem substUniv_readLevel_wf {arguments : Array (KUniv .anon)} {n : Nat}
    (argumentsWF : ∀ level ∈ arguments, (readLevel level).WF n)
    {level result : KUniv .anon} (run : TcM.substUniv level arguments = .ok result) :
    (readLevel result).WF n := by
  simpa only [readLevel_eq] using TcM.substUniv_wf
    (fun level member => readLevel_eq level ▸ argumentsWF level member) run

private theorem list_substUniv_readLevels_wf {arguments : Array (KUniv .anon)} {n : Nat}
    (argumentsWF : ∀ level ∈ arguments, (readLevel level).WF n) :
    ∀ {levels results : List (KUniv .anon)},
      levels.mapM (TcM.substUniv · arguments) = .ok results →
      ∀ result ∈ results, (readLevel result).WF n := by
  intro levels
  induction levels with
  | nil => intro results run; cases run; simp
  | cons level rest ih =>
      intro results run
      rw [List.mapM_cons] at run
      cases first : TcM.substUniv level arguments with
      | error err => rw [first] at run; contradiction
      | ok result =>
          cases tail : rest.mapM (TcM.substUniv · arguments) with
          | error err => rw [first, tail] at run; contradiction
          | ok remaining =>
              rw [first, tail] at run
              cases run
              intro value member
              rcases List.mem_cons.mp member with rfl | member
              · exact substUniv_readLevel_wf argumentsWF first
              · exact ih tail value member

private theorem except_bind_success {ε α γ : Type _} {action : Except ε α}
    {next : α → Except ε γ} {result : γ} (run : action.bind next = .ok result) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok result := by
  cases action with
  | error err => contradiction
  | ok value => exact ⟨value, rfl, run⟩

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

/-- Successful pure instantiation reads as model substitution, up to equivalent
universe levels. All expression positions are covered; the reader's existing
exclusions of free variables and unresolved references are retained. -/
theorem instUnivSpec_readExpr?_withScope {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : VExpr β}
    (support : UniverseSubstitutionSupport arguments term)
    (reading : readExpr? resolve term = some source)
    (run : KExpr.instUnivSpec term arguments = .ok result) :
    ∃ output, readExpr? resolve result = some output ∧
      VExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output ∧
      ∀ n, (∀ level ∈ arguments, (readLevel level).WF n) → output.LevelWF n := by
  induction term generalizing source result with
  | var index name info =>
      cases run
      cases reading
      exact ⟨_, rfl, .bvar _, fun _ _ => trivial⟩
  | fvar _ _ _ => contradiction
  | str value _ _ =>
      cases run
      refine ⟨source, reading, ?_, fun n _ => readString?_levelWF reading n⟩
      rw [readString?_instL reading]
      exact VExpr.LevelEquivalent.refl source
  | nat value name info =>
      cases run
      cases reading
      exact ⟨_, rfl, .natLit _, fun _ _ => trivial⟩
  | sort level info =>
      cases reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨value, substituted, run⟩ := except_bind_success run
      cases run
      exact ⟨_, rfl, .sort (substUniv_readLevel substituted
        (fun left right hl hr => support.faithful left right
          ⟨level, .sort, hl⟩ ⟨level, .sort, hr⟩)
        (fun value hv => support.bounded value ⟨level, .sort, hv⟩)),
        fun _ argumentsWF => substUniv_readLevel_wf argumentsWF substituted⟩
  | const id levels info =>
      cases resolved : resolve id.addr with
      | none => simp [readExpr?, resolved] at reading
      | some ref =>
          simp [readExpr?, resolved] at reading
          subst source
          rw [KExpr.instUnivSpec] at run
          obtain ⟨values, substituted, run⟩ := except_bind_success run
          cases run
          refine ⟨.const ref (values.toList.map readLevel), ?_, .const ref ?_, ?_⟩
          · change readExpr? resolve (.const id values _) = _
            simp [readExpr?, resolved]
          · exact array_substUniv_readLevels substituted
              (fun level member left right hl hr => support.faithful left right
                ⟨level, .const member, hl⟩ ⟨level, .const member, hr⟩)
              (fun level member value hv => support.bounded value ⟨level, .const member, hv⟩)
          · intro n argumentsWF level member
            obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
            have listRun : levels.toList.mapM (TcM.substUniv · arguments) =
                .ok values.toList := by rw [← Array.toList_mapM, substituted]; rfl
            exact list_substUniv_readLevels_wf argumentsWF listRun value valueMember
  | app fn arg info hf ha =>
      rw [readExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨f', fRun, run⟩ := except_bind_success run
      obtain ⟨a', aRun, run⟩ := except_bind_success run
      cases run
      obtain ⟨vf, vfReads, vfSame, vfWF⟩ := hf
        ⟨fun x y hx hy => support.faithful x y hx.app_f hy.app_f,
          fun x hx => support.bounded x hx.app_f⟩ fReads fRun
      obtain ⟨va, vaReads, vaSame, vaWF⟩ := ha
        ⟨fun x y hx hy => support.faithful x y hx.app_a hy.app_a,
          fun x hx => support.bounded x hx.app_a⟩ aReads aRun
      refine ⟨.app vf va, ?_, .app vfSame vaSame,
        fun n h => ⟨vfWF n h, vaWF n h⟩⟩
      change readExpr? resolve (.app f' a' _) = _
      simp [readExpr?, vfReads, vaReads]
  | lam name bi domain body info hA hb =>
      rw [readExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := option_bind_success reading
      obtain ⟨b, bReads, reading⟩ := option_bind_success reading
      cases reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨A', aRun, run⟩ := except_bind_success run
      obtain ⟨b', bRun, run⟩ := except_bind_success run
      cases run
      obtain ⟨vA, vAReads, vASame, vAWF⟩ := hA
        ⟨fun x y hx hy => support.faithful x y hx.lam_ty hy.lam_ty,
          fun x hx => support.bounded x hx.lam_ty⟩ aReads aRun
      obtain ⟨vb, vbReads, vbSame, vbWF⟩ := hb
        ⟨fun x y hx hy => support.faithful x y hx.lam_body hy.lam_body,
          fun x hx => support.bounded x hx.lam_body⟩ bReads bRun
      refine ⟨.lam vA vb, ?_, .lam vASame vbSame,
        fun n h => ⟨vAWF n h, vbWF n h⟩⟩
      change readExpr? resolve (.lam name bi A' b' _) = _
      simp [readExpr?, vAReads, vbReads]
  | all name bi domain body info hA hb =>
      rw [readExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := option_bind_success reading
      obtain ⟨b, bReads, reading⟩ := option_bind_success reading
      cases reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨A', aRun, run⟩ := except_bind_success run
      obtain ⟨b', bRun, run⟩ := except_bind_success run
      cases run
      obtain ⟨vA, vAReads, vASame, vAWF⟩ := hA
        ⟨fun x y hx hy => support.faithful x y hx.all_ty hy.all_ty,
          fun x hx => support.bounded x hx.all_ty⟩ aReads aRun
      obtain ⟨vb, vbReads, vbSame, vbWF⟩ := hb
        ⟨fun x y hx hy => support.faithful x y hx.all_body hy.all_body,
          fun x hx => support.bounded x hx.all_body⟩ bReads bRun
      refine ⟨.forallE vA vb, ?_, .forallE vASame vbSame,
        fun n h => ⟨vAWF n h, vbWF n h⟩⟩
      change readExpr? resolve (.all name bi A' b' _) = _
      simp [readExpr?, vAReads, vbReads]
  | letE name domain value body nonDep info hA hv hb =>
      rw [readExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      obtain ⟨body, bodyReads, reading⟩ := option_bind_success reading
      cases reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨A', aRun, run⟩ := except_bind_success run
      obtain ⟨v', vRun, run⟩ := except_bind_success run
      obtain ⟨b', bRun, run⟩ := except_bind_success run
      cases run
      obtain ⟨vA, vAReads, _, _⟩ := hA
        ⟨fun x y hx hy => support.faithful x y hx.letE_ty hy.letE_ty,
          fun x hx => support.bounded x hx.letE_ty⟩ aReads aRun
      obtain ⟨vv, vvReads, vvSame, vvWF⟩ := hv
        ⟨fun x y hx hy => support.faithful x y hx.letE_val hy.letE_val,
          fun x hx => support.bounded x hx.letE_val⟩ valueReads vRun
      obtain ⟨vb, vbReads, vbSame, vbWF⟩ := hb
        ⟨fun x y hx hy => support.faithful x y hx.letE_body hy.letE_body,
          fun x hx => support.bounded x hx.letE_body⟩ bodyReads bRun
      refine ⟨vb.inst vv, ?_, ?_, fun n h => (vbWF n h).inst (vvWF n h)⟩
      · change readExpr? resolve (.letE name A' v' b' nonDep _) = _
        simp [readExpr?, vAReads, vvReads, vbReads]
      · rw [VExpr.instL_inst]
        exact vbSame.inst vvSame
  | prj id index value info ih =>
      cases resolved : resolve id.addr with
      | none => simp [readExpr?, resolved] at reading
      | some ref =>
          rw [readExpr?, resolved] at reading
          change (readExpr? resolve value).bind
            (fun value => some (.proj ref index.toNat value)) = some source at reading
          obtain ⟨source, sourceReads, reading⟩ := option_bind_success reading
          cases reading
          rw [KExpr.instUnivSpec] at run
          obtain ⟨value', valueRun, run⟩ := except_bind_success run
          cases run
          obtain ⟨output, outputReads, outputSame, outputWF⟩ := ih
            ⟨fun x y hx hy => support.faithful x y hx.prj hy.prj,
              fun x hx => support.bounded x hx.prj⟩ sourceReads valueRun
          refine ⟨.proj ref index.toNat output, ?_, .proj ref index.toNat outputSame, outputWF⟩
          change readExpr? resolve (.prj id index value' _) = _
          simp [readExpr?, resolved, outputReads]

/-- The unscoped refinement remains useful in arbitrary inference contexts. -/
theorem instUnivSpec_readExpr? {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : VExpr β}
    (support : UniverseSubstitutionSupport arguments term)
    (reading : readExpr? resolve term = some source)
    (run : KExpr.instUnivSpec term arguments = .ok result) :
    ∃ output, readExpr? resolve result = some output ∧
      VExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output := by
  obtain ⟨output, reads, same, _⟩ := instUnivSpec_readExpr?_withScope support reading run
  exact ⟨output, reads, same⟩

/-- Runtime resources for the memoized walker, all on its actual finite support. -/
structure UniverseInstantiationSupport (before : TcState .anon)
    (term : KExpr .anon) (arguments : Array (KUniv .anon)) : Prop where
  coherent : before.env.intern.WF
  faithful : KExpr.CollisionFree fun candidate => before.env.intern.ExprSupport candidate ∨
    KExpr.InstUnivReach arguments term candidate
  levels : UniverseSubstitutionSupport arguments term

/-- Connect the actual memoized and interned execution to model substitution.
The empty-argument shortcut requires scope because production skips its usual
parameter-range checks on that path. -/
theorem instantiateUnivParams_readExpr? {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : VExpr β}
    {before after : TcState .anon}
    (support : UniverseInstantiationSupport before term arguments)
    (scope : source.LevelWF arguments.size)
    (reading : readExpr? resolve term = some source)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after) :
    ∃ output, readExpr? resolve result = some output ∧
      VExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output := by
  have post := TcM.instantiateUnivParams_wf support.faithful
    (fun _ h => Or.inr h) ⟨support.coherent, fun _ h => Or.inl h⟩
  rw [run] at post
  have spec := post.2.1
  by_cases empty : arguments.isEmpty = true
  · have args : arguments = #[] := Array.isEmpty_iff.mp empty
    subst arguments
    change Except.ok term = .ok result at spec
    cases spec
    refine ⟨source, reading, ?_⟩
    simpa only [Array.toList_empty, List.map_nil, scope.instL_nil] using
      VExpr.LevelEquivalent.refl source
  · rw [KExpr.instantiateUnivParamsSpec, if_neg empty] at spec
    exact instUnivSpec_readExpr? support.levels reading spec

/-- An annotated reading of the returned tree, preserving all binder conditions
after their model-side universe substitution. -/
theorem instantiateUnivParams_readAnnotated {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : AExpr β}
    {before after : TcState .anon}
    (support : UniverseInstantiationSupport before term arguments)
    (scope : source.erase.LevelWF arguments.size)
    (reading : readExpr? resolve term = some source.erase)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after) :
    ∃ output : AExpr β, readExpr? resolve result = some output.erase ∧
      AExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output := by
  obtain ⟨raw, rawReads, same⟩ := instantiateUnivParams_readExpr? support scope reading run
  rw [← AExpr.erase_instL] at same
  obtain ⟨output, erased, equivalent⟩ := AExpr.reannotate_levels _ same
  exact ⟨output, erased ▸ rawReads, equivalent⟩

/-- Scope and dependencies of the actual returned annotated type. Nonempty
substitution checks every source parameter; the empty shortcut uses source
scope. Neither syntactic property follows from semantic equivalence alone. -/
theorem instantiateUnivParams_readAnnotated_scoped
    {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : AExpr β}
    {before after : TcState .anon} {n depth : Nat}
    (support : UniverseInstantiationSupport before term arguments)
    (scope : source.Scope arguments.size depth)
    (argumentsWF : ∀ level ∈ arguments, (readLevel level).WF n)
    (reading : readExpr? resolve term = some source.erase)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after) :
    ∃ output : AExpr β, readExpr? resolve result = some output.erase ∧
      AExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output ∧
      output.Scope n depth ∧ output.references = source.references := by
  obtain ⟨output, reads, same⟩ :=
    instantiateUnivParams_readAnnotated support scope.erase.1 reading run
  have args : ∀ level ∈ arguments.toList.map readLevel, level.WF n := by
    intro level member
    obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
    exact argumentsWF value (by simpa using valueMember)
  have outputWF : output.erase.LevelWF n := by
    have post := TcM.instantiateUnivParams_wf support.faithful
      (fun _ h => Or.inr h) ⟨support.coherent, fun _ h => Or.inl h⟩
    rw [run] at post
    have spec := post.2.1
    by_cases empty : arguments.isEmpty = true
    · have emptyArgs : arguments = #[] := Array.isEmpty_iff.mp empty
      subst arguments
      change Except.ok term = .ok result at spec
      cases spec
      have equal := Option.some.inj (reads.symm.trans reading)
      rw [equal]
      have substituted := (scope.instL args).erase.1
      simpa only [AExpr.erase_instL, Array.toList_empty, List.map_nil,
        scope.erase.1.instL_nil] using substituted
    · rw [KExpr.instantiateUnivParamsSpec, if_neg empty] at spec
      obtain ⟨raw, rawReads, _, rawWF⟩ :=
        instUnivSpec_readExpr?_withScope support.levels reading spec
      have equal := Option.some.inj (reads.symm.trans rawReads)
      exact equal ▸ rawWF n argumentsWF
  exact ⟨output, reads, same, same.scope (scope.instL args) outputWF,
    same.references.symm.trans (AExpr.references_instL source _)⟩

end Ix.Kernel.Consistency
