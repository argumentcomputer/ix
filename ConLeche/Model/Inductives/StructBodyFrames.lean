module

public import ConLeche.Model.Inductives.StructEntryFree
import ConLeche.Verify.Inductives.StructBody
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.StructIntro

public section

/-!
# The projection body's frame (task #175 S1)

The table stores, per field, a **body** `F_i[p⃗ ↦ bvars, f_j ↦ .proj T
j (bvar 0)]` (`structProjBodies`), and the tower law (A) reads it
through the dummy telescope `projTele (nP + 1) body`
(`ConLeche/Verify/ProjTele.lean`).  Two facts make the reading what the
law needs:

* **the telescope's reading is the opened body's** (`denoteMeta_projTele`):
  `denoteMeta` opens the `nP + 1` dummy binders at fresh variables, so
  the telescope reads to `mkPisAV` over `nP + 1` dummy `Sort 0` binder
  data with the body instantiated at the variables as its residual;
* **the opened body is the constructor's field domain at the frame**
  (`bodyFrames`): by `structProjBody_open` the opened body *is* the
  head domain of the constructor telescope peeled at the variables and
  the subject's earlier projections, so its reading is the field
  domain's instantiation sequence along the readings of those
  arguments (`Rules.denoteMeta_instPisAt_peel`), which at the frame — the
  subject a member of the family at the parameters — agrees with the
  field domain read at the subject's projection spine
  (`chain_entry_agree`) and is graded there (the graph regime by the
  projections' fit, the squash regime by the point spine's agreement
  with a fitting prefix at every used slot, `free_of_diff`).

No annotation, inference or definitional-equality run is consumed:
the body is a substitution instance of the stored constructor type,
and the reading is a homomorphism for substitution.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The telescope's reading -/

/-- **The dummy telescope reads to the opened body**: `k` dummy
binders at depth `d` open at the variables `d, …, d + k - 1`, and the
residual is the body's instantiation sequence at them. -/
theorem denoteMeta_projTele {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (k d : Nat) (body : Expr) {RA : AnnotTerm},
      denoteMeta acval env φ (d + k)
        (Expr.instSeq ((List.range k).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k - 1) body) = some RA →
      denoteMeta acval env φ d (ConLeche.projTele k body)
        = some (mkPisAV (List.replicate k (0, 1, .sort 0)) RA)
  | 0, d, body, RA, h => by
    simpa [ConLeche.projTele, Expr.instSeq, mkPisAV] using h
  | k + 1, d, body, RA, h => by
    have hspine : Expr.instSeq ((List.range (k + 1)).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k + 1 - 1) body
        = Expr.instSeq ((List.range k).map fun j =>
            Expr.fvar (d + 1 + j) (.sort .zero)) (k - 1)
            (body.instantiate1 (Expr.fvar d (.sort .zero)) k) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
      show Expr.instSeq _ (k - 1) (body.instantiate1 _ k) = _
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [show d + (j + 1) = d + 1 + j from by omega]
    rw [hspine, show d + (k + 1) = d + 1 + k from by omega] at h
    have ih := denoteMeta_projTele k (d + 1)
      (body.instantiate1 (Expr.fvar d (.sort .zero)) k) h
    rw [ConLeche.projTele, denoteMeta_forallE, denoteMeta_sort, ConLeche.projTele_instantiate1,
      Nat.zero_add, ih]
    rfl

/-- The telescope over the parameters and the subject, at depth `0`:
the residual is the body at the direct install's own variable
spelling (`fvsD`/`tfvD`). -/
theorem denoteMeta_projTele_zero {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP : Nat} {body : Expr} {RA : AnnotTerm}
    (h : denoteMeta acval env φ (nP + 1)
      (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) = some RA) :
    denoteMeta acval env φ 0 (ConLeche.projTele (nP + 1) body)
      = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) RA) := by
  refine denoteMeta_projTele (nP + 1) 0 body ?_
  rw [Nat.zero_add, Nat.add_sub_cancel]
  rw [Expr.instSpine_eq_instSeq] at h
  have e : ((List.range (nP + 1)).map fun j => Expr.fvar (0 + j) (.sort .zero))
      = ConLeche.fvsD nP ++ [ConLeche.tfvD nP] := by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    simp only [ConLeche.fvsD, ConLeche.tfvD, Nat.zero_add]
  rw [e]
  exact h

/-! ## The frame -/

omit [SetTheory V] in
theorem DomsBelow.getD_below {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} (j : Nat), DomsBelow k ds → j < ds.length →
      Term.bvarsBelow (k + j) (ds.getD j default).2.2.erase
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d :: ds, 0, h, _ => by simpa using h.1
  | d :: ds, j + 1, h, hj => by
    rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.getD_below j h.2 (by simpa using hj)

/-- **The opened body's frame.**  At the frame (the subject a member of
the family at the parameters — `ρ 0` in the tower over the field chain
at `ρ ∘ succ`, which satisfies the constructor's parameter context)
the opened body reads to a graded term whose value is the field
domain at the subject's projection spine.  The grading in the squash
regime rides the official guard's content (`hguard`) and the unused
earlier fields' invariance (`hfree`). -/
theorem bodyFrames {env : Env} (m : EnvModel V env)
    {nP nF i off : Nat} {T : Name} {cty : Expr} {cds : List Expr}
    {bodyC : Expr} {mbC : BinderMeta} {body : Expr}
    (hcf : Expr.instPisAt (ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP) cty
      = some (cds, .forallE
          (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) bodyC mbC))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    -- the earlier fields' entries, at the table's projection offset
    -- (task #210 Part A: the tagged tower of the fixpoint route reads
    -- its fields at offset `1`)
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry ∧ entry.off = off)
    (hi : i < nF)
    {ds : List (Nat × Nat × AnnotTerm)} {bodyA : AnnotTerm} {ψ : Name → Nat} {w : Nat}
    (hlenDs : ds.length = nP + nF) (hbelow : DomsBelow 0 ds)
    (hctyRead0 : denoteMeta m.acval env ψ 0 cty = some (mkPisAV ds bodyA))
    {sorts : List Level}
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)) ∧ FieldsValid ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    -- THE SUBJECT'S FRAME, abstractly (task #210 Part A): whatever
    -- carrier the subject `ρ 0` lives in, at a squash instance it is
    -- the point and the fields admit a fitting spine; in the graph
    -- regime the subject's projection tuple (below the offset) fits
    -- the fields; and the subject's projection readings are graded
    (Frame : (Nat → V) → Prop)
    (hsq : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) → w = 0 →
      ρ 0 = pt ∧ ∃ as' : List V, SpineFit (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2)) as')
    (hgr : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) → w ≠ 0 →
      SpineFit (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2)) (projList nF (dropS off (ρ 0))))
    (hokProj : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      ∀ j, j < nF → WellDenoted V ρ (projAV (j + off) (.bvar 0))) :
    ∃ fdomA : AnnotTerm,
      denoteMeta m.acval env ψ (nP + 1)
        (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) = some fdomA ∧
      ((w = 0 → ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0) →
        ∀ ρ : Nat → V, Frame ρ →
          Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
          WellDenotedV V ρ fdomA) ∧
      (∀ ρ : Nat → V, Frame ρ →
        Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
        interp V ρ fdomA
          = interp V (consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)))
              (((ds.drop nP).map (·.2.2)).getD i default)) := by
  -- the constructor type's reading at the body's depth
  have hctyRead : denoteMeta m.acval env ψ (nP + 1) cty = some (mkPisAV ds bodyA) :=
    denoteMeta_depth_of_closed m.acval_closed hCf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hCf hCb hctyRead0 1 k)
      hctyRead0 (nP + 1)
  -- the arguments' scoping
  have hlenP : (ConLeche.fvsD nP).length = nP := ConLeche.fvsD_length nP
  have hfvsDidx : ∀ (k : Nat) (x : Expr), (ConLeche.fvsD nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1; rwa [hlenP] at this
    rw [ConLeche.fvsD_getElem? nP k hk] at hx
    exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
  have hargs : ∀ a ∈ ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP,
      Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hk
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, and_true]
      omega
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, ConLeche.tfvD, and_true]
      omega
  have hctyW : Expr.WScoped (nP + 1) cty := Expr.WScoped.of_not_hasFvar hCf
  -- the arguments' readings: the parameters and the earlier projections
  have hspP := denoteMetaSpine_entryParams (acval := m.acval) (env := env) (φ := ψ)
    hfvsDidx hlenP
  have hspX := denoteMetaSpine_entryProjs (acval := m.acval) (env := env) (φ := ψ)
    (nP := nP) (sdom := .sort .zero) hprev
  have hsp : DenoteMetaSpine m.acval env ψ (nP + 1) (ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP)
      (entryParamBvars nP ++ entryProjAVs off i) :=
    DenoteMetaSpine.append hspP hspX
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denoteMeta_instPisAt_peel m.acval_closed
    (acval_inst_self m) _ hcf hctyW hargs hctyRead hsp
  obtain ⟨fdomA, ba, hfdA, -, rfl⟩ := denoteMeta_forallE_inv hrest
  -- the peel is the instantiation sequence of the field domain
  have hlenVs : (entryParamBvars nP ++ entryProjAVs off i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  have hsplitDs : ds = ds.take (nP + i) ++ ds.drop (nP + i) :=
    (List.take_append_drop _ _).symm
  have htele : PiTeleAV (nP + i) (mkPisAV ds bodyA)
      (((ds.take (nP + i)).map (·.2.2)).reverse)
      (mkPisAV (ds.drop (nP + i)) bodyA) := by
    have h := piTeleAV_mkPisAV (ds.take (nP + i)) (mkPisAV (ds.drop (nP + i)) bodyA)
    rw [← mkPisAV_append, ← hsplitDs, List.length_take, hlenDs,
      show min (nP + i) (nP + nF) = nP + i from by omega] at h
    exact h
  have hpeel' := peelPis_of_piTeleAV (nP + i) htele hlenVs
  rw [hpeel] at hpeel'
  have hdropDs : ds.drop (nP + i) = ds.getD (nP + i) default :: ds.drop (nP + i + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hdropDs] at hpeel'
  simp only [mkPisAV] at hpeel'
  obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ entryProjAVs off i) (nP + i - 1)
    (ds.getD (nP + i) default).1 (ds.getD (nP + i) default).2.1
    (ds.getD (nP + i) default).2.2
    (mkPisAV (ds.drop (nP + i + 1)) bodyA)
  rw [hB'] at hpeel'
  obtain ⟨-, -, hfdomA, -⟩ := AnnotTerm.pi.inj (Option.some.inj hpeel')
  -- the field's domain, named
  have hFi : ((ds.drop nP).map (·.2.2)).getD i default = (ds.getD (nP + i) default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hFiBelow : Term.bvarsBelow (nP + i) (ds.getD (nP + i) default).2.2.erase := by
    have := DomsBelow.getD_below (nP + i) hbelow (by omega)
    rwa [Nat.zero_add] at this
  have hlenFs : ((ds.drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
  have hlen' : (entryParamBvars nP ++ entryProjAVs off i).length - 1 = nP + i - 1 := by
    rw [hlenVs]
  refine ⟨fdomA, hfdA, ?_, ?_⟩
  · -- the grading at the frame
    intro hguard ρ hx hsat
    -- the field's grading at the subject's projection spine: in the
    -- graph regime the projections fit; at a squash instance they are
    -- the point spine, which differs from a fitting prefix only at
    -- unused slots, where the field is a lift
    have hokPre : WellDenotedV V (consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)))
        (((ds.drop nP).map (·.2.2)).getD i default) := by
      by_cases hw : w = 0
      · obtain ⟨hpt, as', hspAs⟩ := hsq ρ hx hsat hw
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
        rw [hpt, dropS_pt, projList_pt]
        have hlenTake : (as'.take i).length = i :=
          spineFit_take_length hspAs (by rw [hlenFs]; omega)
        rw [wellDenotedV_congr_lifts i
          (free_of_diff hlenDs hi (hsorts _ hsat) (hguard hw) hfree hspAs)
          (consList_prefix_agree hlenTake _).2]
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
      · have hspAll := hgr ρ hx hsat hw
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAll (by rw [hlenFs]; exact hi)
        rw [projList_take nF i _ (Nat.le_of_lt hi)] at hpre
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
    -- the readings' gradings at the frame
    have hokArgs : ∀ w' ∈ entryParamBvars nP ++ entryProjAVs off i, WellDenotedV V ρ w' := by
      intro w' hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw'
        exact ⟨trivial, trivial⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw'
        have hj' : j < i := List.mem_range.mp hj
        exact ⟨hokProj ρ hx hsat j (by omega), projAV_validV trivial⟩
    rw [hfdomA, ← hlen']
    refine wellDenotedV_instSeq _ hokArgs ?_
    rw [(WellDenotedV_congr_below _ (nP + i) _ _ hFiBelow (chain_entry_agree nP off i ρ))]
    rw [← hFi]
    exact hokPre
  · -- the value at the frame
    intro ρ _ _
    rw [hfdomA, ← hlen', interp_instSeq, hFi]
    exact interp_congr_below V _ (nP + i) _ _ hFiBelow (chain_entry_agree nP off i ρ)

end ConLeche.Model
