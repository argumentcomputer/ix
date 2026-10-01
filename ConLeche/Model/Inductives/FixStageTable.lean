module

public import ConLeche.Model.Inductives.FixEntryLaw
public import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.StructStageTable
import ConLeche.Verify.Inductives.FixParts
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitInst
public section

/-!
# The projection table's cons on the fixpoint route (task #210 Part A)

`stageFixTable`: the P step at the recursive route's last stage — the
projection **table** of a STRUCTURE-LIKE block (one constructor, no
index; `checkNativeTable`).  It is the structure route's table
stage (`stageTable`, `ConLeche/Model/Inductives/StructStageTable.lean`)
read against the fixpoint carrier: the family at the parameters is
the one-constructor fibre of the tagged union (`sumSet w (sumFibre w
ρ' [Fs ++ [idxEqAV []]])`, the block's `hfold`), so the subject of a
projection is a TAGGED point-terminated tuple and the fields sit at
projection offset `1` (`ProjTable.off`).  The three laws are the fix
entry cores (`FixEntryLawP.lean`); the bodies' frames are
`bodyFrames` at the fibre's frame.

`declNativeTable` is the assembly-facing wrapper: the case split
on `checkNativeTable` (nothing consed at a block that is not
structure-like), the block's data specialised to one constructor and
no index, and the `NoProjEnv` bookkeeping across the block's conses
(the former, the constructor, the generated recursor).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  NativeParts BinderMeta ProjEntry ProjTable RecRule RecFieldKind projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Small facts -/

omit [SetTheory V] in
/-- Lifting by nothing is the identity on a field chain. -/
theorem liftFields_zero : ∀ (k : Nat) (Fs : List AnnotTerm), liftFields 0 k Fs = Fs
  | _, [] => rfl
  | k, F :: Fs => by rw [liftFields_cons, AnnotTerm.liftN_zero, liftFields_zero (k + 1) Fs]

omit [SetTheory V] in
/-- The one constructor's restricted chain at no index is its
unrestricted chain closed by the trivial index equation. -/
theorem rChains_single_nil (Fs : List AnnotTerm) :
    rChains 0 0 [Fs] [[]] = [Fs ++ [idxEqAV []]] := by
  simp [rChains, rChain, idxEqsAt, liftFields_zero]

/-- The capability record at a structure-like block, spelled out. -/
theorem _root_.ConLeche.nativeCaps_single {p : NativeParts} {c : ConstantVal × Nat}
    (h : p.ctors = [c]) :
    ConLeche.nativeCaps p =
      { eta := p.nIdx == 0 && !p.isProp &&
          !(p.kinds.any fun ks => ks.any fun k => k == .recursive || k == .reflexive),
        etaCtor := c.1.name, etaParams := p.nP,
        etaFields := c.2, unitlike := p.nIdx == 0 && c.2 == 0, unitParams := p.nP,
        ruleK := c.2 == 0 && p.isProp,
        sortZ := Level.zeronessOf p.resSort } := by
  unfold ConLeche.nativeCaps ConLeche.nativeCapsAt ConLeche.nativeIsRec
  rw [h]

/-- At a structure-like block the table stage keeps the projection
FUNCTION family free (it stores a table, never `T.proj.i`), so the
block's η claim is vacuous below and at the table's environment. -/
theorem fixTableFamFree {p : NativeParts} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {env₃ env₂ : Env}
    (hTbl : ConLeche.checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss env₃ = .ok env₂)
    (hlenA : ctorsA.length = p.ctors.length) (hlenS : sortss.length = p.ctors.length)
    (hnFc : ∀ cA c, ctorsA = [cA] → p.ctors = [c] → cA.2 = c.2)
    (hU : (ConLeche.nativeCaps p).unitlike = false) :
    (ConLeche.nativeCaps p).eta = true →
      env₃.find? (projFnName p.cvT.name 0) = none := by
  intro he
  have he' := he
  unfold ConLeche.nativeCaps ConLeche.nativeCapsAt at he'
  split at he'
  · next c hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at he'
    obtain ⟨⟨hnIdx, -⟩, -⟩ := he'
    rw [ConLeche.nativeCaps_single hc] at hU
    have hU' : (p.nIdx == 0 && c.2 == 0) = false := hU
    rw [hnIdx] at hU'
    simp only [beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hU'
    have hnF : c.2 ≠ 0 := hU'
    rw [hc, List.length_singleton] at hlenA hlenS
    obtain ⟨cA, rfl⟩ := List.length_eq_one_iff.mp hlenA
    obtain ⟨sorts, rfl⟩ := List.length_eq_one_iff.mp hlenS
    simp only [ConLeche.checkNativeTable, hnIdx, beq_self_eq_true, ↓reduceIte] at hTbl
    obtain ⟨-, -, -, hfree, -, -⟩ := ConLeche.checkStructProjTable_inv hTbl
    have hpos : 0 < cA.2 := by rw [hnFc cA c rfl hc]; omega
    have := List.all_eq_true.mp hfree 0 (List.mem_range.mpr hpos)
    exact Option.isNone_iff_eq_none.mp this
  · exact nomatch he'

/-- The block's capability laws are vacuous (task #210 Part A): the
constructor has a field, so the block is never unit-like; its η claim
is premised on the projection-function family being stored. -/
theorem fixCapsLawsAt_vacuous {env' : Env} (m' : EnvModel V env') {p : NativeParts}
    {cvTa : ConstantVal}
    (hU : (ConLeche.nativeCaps p).unitlike = false)
    (hfr : (ConLeche.nativeCaps p).eta = true →
      env'.find? (projFnName p.cvT.name 0) = none) :
    CapsLawsAt m' p.cvT.name cvTa (ConLeche.nativeCaps p) := by
  refine capsLawsAt_vacuous m' hU fun he => ⟨?_, hfr he⟩
  have he' := he
  unfold ConLeche.nativeCaps ConLeche.nativeCapsAt at he'
  split at he'
  · next c hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at he'
    obtain ⟨⟨hnIdx, -⟩, -⟩ := he'
    rw [ConLeche.nativeCaps_single hc] at hU ⊢
    have hU' : (p.nIdx == 0 && c.2 == 0) = false := hU
    rw [hnIdx] at hU'
    simp only [beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hU'
    show 0 < c.2
    omega
  · exact nomatch he'

/-- `NoProjEnv` across the constructors' conses. -/
theorem noProjEnv_consSumCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env₀ : Env},
      NoProjEnv env₀ T i → (∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consSumCtors nP ctorsA env₀) T i
  | [], _, h, _ => h
  | cA :: rest, env₀, h, hall => by
    simp only [ConLeche.consSumCtors]
    refine noProjEnv_consSumCtors (h.cons (c₀ := .ctorInfo cA.1 nP cA.2) (NoProjHead.ofType
      (hall cA List.mem_cons_self) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))) ?_
    exact fun c hc => hall c (List.mem_cons_of_mem _ hc)

/-! ## The P step -/

set_option maxHeartbeats 3200000 in
/-- **The P step at the fixpoint route's projection table** (task #210
Part A): `stageTable` against the one-constructor fibre. -/
theorem stageFixTable (mp : EnvModelM V μ env)
    {p : NativeParts} {cvTa cvCa : ConstantVal} {nF : Nat} {sorts : List Level}
    {envOut : Env} {caps : IndCaps}
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) p.cvT.name cvCa.name
      p.cvT.levelParams p.nP nF p.resSort
      (ConLeche.structProjGuards cvCa.type p.nP nF sorts) 1 cvCa env = .ok envOut)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hcaps : caps.eta = true → (Level.isEquiv p.resSort .zero == some true) = false ∧
      caps.etaCtor = cvCa.name ∧ caps.etaParams = p.nP ∧ caps.etaFields = nF)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? cvCa.name = some (.ctorInfo cvCa p.nP nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (hstripC : (cvCa.type.stripPis (p.nP + nF)).isSome = true)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hCshape : cvCa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains p.cvT.name = false)
    (hresR : ConLeche.reservedBasisNames.contains (p.cvT.name.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains cvCa.name = false)
    (hnp : ∀ j, NoProjEnv env p.cvT.name j)
    {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCDread : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 p.cvT.name p.nP nF ψ (Es ψ))))
    (hCDlen : ∀ ψ, (ds ψ).length = p.nP + nF)
    (hCDbelow : ∀ ψ, DomsBelow 0 (ds ψ))
    (hleq : ∀ k, k < nF → p.isProp = false → Level.leq (sorts.getD k .zero) p.resSort = some true)
    {u : (Name → Nat) → Nat} {rss : List (List Bool)}
    {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {eiss : (Name → Nat) → List (List (List AnnotTerm))} {Fss₀ Ess : (Name → Nat) → List (List AnnotTerm)}
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = nativeTyAVI (u ψ) (p.resSort.eval ψ) (pps ψ) [] rss (tlss ψ) (eiss ψ) (Fss₀ ψ) (Ess ψ))
    (hleafC : ∀ ψ, mp.base2.acval cvCa.name ψ
      = sumMkAV (p.resSort.eval ψ) 0 (ds ψ) (((ds ψ).drop p.nP).map (·.2.2))
          (uChains [((ds ψ).drop p.nP).map (·.2.2)]))
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ
          (nativeTyAVI (u ψ) (p.resSort.eval ψ) (pps ψ) [] rss (tlss ψ) (eiss ψ) (Fss₀ ψ) (Ess ψ)))
        = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ) (consList ts ρ)
            [((ds ψ).drop p.nP).map (·.2.2) ++ [idxEqAV []]]))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)))
    (hboundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        p.isProp = false → FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)))
    (hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    Nonempty (EnvModelM V μ envOut) := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv hTbl
  let tbl : ProjTable := ⟨p.cvT.name, p.cvT.levelParams, p.nP, cvCa.name, nF, p.resSort,
    bodies, ConLeche.structProjGuards cvCa.type p.nP nF sorts, 1⟩
  -- the field-chain facts, in the frames' spelling
  have hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ → p.resSort.eval ψ ≠ 0 →
      FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ ρ hρ hw
    cases hp : p.isProp
    · exact hboundP ψ ρ hρ hp
    · exfalso
      apply hw
      rw [hp] at hProp
      exact Level.isEquiv_sound (beq_iff_eq.mp hProp.symm) ψ
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
      FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) :=
    fun ψ ρ h => (hfields ψ ρ h).1
  -- the guards' content: the official join over the used earlier slots
  have hguardSem : ∀ k, k < nF → ∀ ψ : Name → Nat,
      ((ConLeche.structProjGuards cvCa.type p.nP nF sorts).getD k .zero).eval ψ = 0 →
      (sorts.getD k .zero).eval ψ = 0 ∧
      ∀ j, j < k → ConLeche.structUsedLater cvCa.type p.nP j = true →
        (sorts.getD j .zero).eval ψ = 0 := by
    intro k hk ψ h0
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)] at h0
    exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
  have hguardOf : ∀ k, k < nF → ∀ ψ : Name → Nat,
      (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
      ((ConLeche.structProjGuards cvCa.type p.nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk ψ hall
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)]
    exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
  have hO5 : ∀ k, k < nF → (Level.isEquiv p.resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 →
      ((ConLeche.structProjGuards cvCa.type p.nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine hguardOf k hk ψ fun j hj => ?_
    have := Level.leq_sound (hleq j (by omega) (by rw [hProp]; exact hne)) ψ
    omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + nF) 0 hstripC
  have hlenA : fvsA.length = p.nP + nF := openPisAtFvars_length _ hopAll
  have hfree : ∀ (ψ : Name → Nat) (k : Nat), k < nF → ∀ (j : Nat), j < k →
      ConLeche.structUsedLater cvCa.type p.nP j = false →
      ∃ X : AnnotTerm, (((ds ψ).drop p.nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
    intro ψ k hk j hj hun
    have hsome : (cvCa.type.stripPis (p.nP + j + 1)).isSome = true :=
      ConLeche.stripPis_isSome_of_le (by omega) hstripC
    obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
    have hrest : rest.hasLooseBVar 0 = false := by
      unfold ConLeche.structUsedLater at hun
      rw [hst] at hun
      have hun' : rest.hasLooseBVarB 0 = false := hun
      rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
      exact hun'
    obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (p.nP + nF) (p.nP + j) hopAll (by omega)
      hst hrest (by
        intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
        exact absurd hl List.not_mem_nil)
    obtain ⟨pps', b, hstA, -, -, hbind⟩ := denoteMeta_openPis (p.nP + nF) hopAll (hCDread ψ)
    have hppsEq : pps' = ds ψ := by
      have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI mp.base2 p.cvT.name p.nP nF ψ (Es ψ))
      rw [hCDlen ψ] at h2
      exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
    obtain ⟨x, hx⟩ : ∃ x, fvsA[p.nP + k]? = some x :=
      ⟨fvsA[p.nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨q, hq, -, hqread⟩ := hbind (p.nP + k) x hx
    rw [hppsEq] at hq
    have hW : Expr.WScoped (0 + (p.nP + k)) (Expr.fvarTypeD x) :=
      openPisAtFvars_typeWScoped (p.nP + nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
    have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ p.nP + j := by
      intro l hl
      have hsub : l ∈ x.fvarLeaves := by
        cases x with
        | fvar idx ty =>
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl
        | _ => exact hl
      have := hleavesK (p.nP + k) (by omega) x hx l hsub
      simpa using this
    obtain ⟨X, hX⟩ := denoteMeta_liftN_of_leaf_free mp.base2 (0 + (p.nP + k)) (Expr.fvarTypeD x) hW
      (q := p.nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
    refine ⟨X, ?_⟩
    have hFk : (((ds ψ).drop p.nP).map (·.2.2)).getD k default = q.2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
      rfl
    rw [hFk, hX, show 0 + (p.nP + k) - 1 - (p.nP + j) = k - 1 - j from by omega]
  -- names
  have hneT : p.cvT.name ≠ projTableName p.cvT.name := by
    intro h
    have := projTableName_isProjFnShape p.cvT.name
    rw [← h, hTshape] at this
    exact nomatch this
  have hneC : cvCa.name ≠ projTableName p.cvT.name := by
    intro h
    have := projTableName_isProjFnShape p.cvT.name
    rw [← h, hCshape] at this
    exact nomatch this
  have hnres : ConLeche.reservedBasisNames.contains (projTableName p.cvT.name) = false :=
    ConLeche.reservedBasisNames_not_num _ _
  -- the crossings
  have hcrossT : ConsCrossAt (.projInfo tbl) cvTa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)).2.2.1
  -- the lookups at the extension
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa caps) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneT h.symm)]
    exact hfT
  have hfC₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? cvCa.name
      = some (.ctorInfo cvCa p.nP nF) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneC h.symm)]
    exact hfC
  have hfTbl₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? (projTableName p.cvT.name)
      = some (.projInfo tbl) := ConLeche.Env.find?_cons_self _ _
  have hprev₂ : ∀ j, j < nF →
      ∃ entry, (⟨.projInfo tbl :: env.consts⟩ : Env).findProj? p.cvT.name j
        = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < nF → ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i) :=
    fun i hi => ⟨hresT, hresR, hresC, hi, ⟨cvTa, caps, hfT₂, hlpsT⟩,
      ⟨cvCa, hfC₂, hlpsC, hstripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', -⟩ := declStep_preserves_of_tower_cons mp (tbl := tbl) hfresh hnres hwf' hnp hhead hlaw
    exact ⟨mp'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < nF := hi
  have hacT : ∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName p.cvT.name) _ p.cvT.name ψ = _
    rw [acvalWith_ne hneT]
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = mp.base2.acval cvCa.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName p.cvT.name) _ cvCa.name ψ = _
    rw [acvalWith_ne hneC]
  have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .projInfo tbl) hfresh hcrossT hcbT m₂ hac
  -- the constructor type's reading at the extension
  have hCDread₂ : ∀ ψ, denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI m₂ p.cvT.name p.nP nF ψ (Es ψ))) := by
    intro ψ
    have hbody : ctorBodyAVI m₂ p.cvT.name p.nP nF ψ (Es ψ)
        = ctorBodyAVI mp.base2 p.cvT.name p.nP nF ψ (Es ψ) := by
      unfold ctorBodyAVI; rw [hacT]
    rw [hbody, hac]
    exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (hCDread ψ)
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, mbB, hcf⟩ :=
    ConLeche.structProjBody_open hbodies hstripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, caps, hfT₂, hlpsT, hcaps⟩,
    hO5 i hi, cvCa, hfC₂, hlpsC, ?_, ?_⟩
  · -- the per-instantiation laws
    intro us _
    -- the subject's frame: a member of the one-constructor fibre of
    -- the tagged union (offset 1)
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ (off := 1) hcf hCf hCb
      (fun j hj => by
        obtain ⟨entry, hfe⟩ := hprev₂ j (by omega)
        refine ⟨entry, hfe, ?_⟩
        obtain ⟨tbl', hf', -, rfl⟩ := ConLeche.Env.findProj?_some hfe
        obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hfTbl₂.symm.trans hf'))
        rfl) hi
      (hCDlen (Level.substFn φ p.cvT.levelParams us))
      (hCDbelow (Level.substFn φ p.cvT.levelParams us))
      (hCDread₂ (Level.substFn φ p.cvT.levelParams us))
      (fun ρ h => hfields _ ρ h) (hsortsF _)
      (used := ConLeche.structUsedLater cvCa.type p.nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ sumSet (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
        (sumFibre (p.resSort.eval (Level.substFn φ p.cvT.levelParams us)) (fun j => ρ (j + 1))
          [((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2) ++ [idxEqAV []]]))
      (fun ρ hx _ hw => by
        rw [hw] at hx
        exact fixFibre_zero_elim hx)
      (fun ρ hx _ hw => by
        obtain ⟨fs, heq, hsp, -⟩ := fixFibre_elim hw hx
        have hlenF : fs.length = nF := by
          rw [hsp.length_eq, List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]
        rw [heq, dropS_one_inj, ← hlenF, projList_mkTower_take (Nat.le_refl _), List.take_length]
        exact hsp)
      (fun ρ hx hsat j hj => by
        refine wellDenoted_projAV_succ_fibre (fun _ => hokB _ _ hsat) trivial ?_ ?_
        · rw [interp_bvar]; exact hx
        · rw [List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]; exact hj)
    have hread : denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (p.nP + 1) (0, 1, .sort 0)) fdomA) := by
      show denoteMeta m₂.acval _ φ 0 (ConLeche.projTele (p.nP + 1)
        ((bodies.getD i default).instantiateLevelParams p.cvT.levelParams us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ p.cvT.levelParams us 0]
      exact denoteMeta_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
      have hguard' : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ p.cvT.levelParams us) = 0 ∧
          ∀ j, j < i → ConLeche.structUsedLater cvCa.type p.nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ p.cvT.levelParams us) = 0 :=
        fun h0 => hguardSem i hi _ (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = nativeTyAVI (u (Level.substFn φ p.cvT.levelParams us))
            (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (pps (Level.substFn φ p.cvT.levelParams us)) [] rss
            (tlss (Level.substFn φ p.cvT.levelParams us))
            (eiss (Level.substFn φ p.cvT.levelParams us))
            (Fss₀ (Level.substFn φ p.cvT.levelParams us))
            (Ess (Level.substFn φ p.cvT.levelParams us)) := by
        show m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacT, hleafT]
      rw [hacT'] at hokApp hmem
      exact fixEntryTypingCore (hCDlen _) (hFD.len _) (by simp) (hiff _) (hokB _)
        (hsortsF _) (used := ConLeche.structUsedLater cvCa.type p.nP) hguard' (hfree _ i hi) hi
        (hfold _) hresFd (hokFd (fun h0 => (hguard' h0).2)) ρ vs x rest hlenVs hokApp hokx hmem
        hpeel
    · -- (B): the constructor type's reading at the instantiation,
      -- then the two regimes
      refine ⟨mkPisAV (ds (Level.substFn φ p.cvT.levelParams us))
        (ctorBodyAVI m₂ p.cvT.name p.nP nF (Level.substFn φ p.cvT.levelParams us)
          (Es (Level.substFn φ p.cvT.levelParams us))), ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCDread₂ _
      · intro hguardAt ρ ys rest hlen hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = sumMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us)) 0
              (ds (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2))
              (uChains [((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)]) := by
          show m₂.acval cvCa.name (Level.substFn φ p.cvT.levelParams us) = _
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        show interp V ρ (projAV (i + 1) _) = _
        by_cases hw : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0
        · -- squash: the certified fit pins the selected field to a
          -- proposition's domain
          have hsp : SpineFit ρ ((ds (Level.substFn φ p.cvT.levelParams us)).map (·.2.2))
              (ys.map (interp V ρ)) :=
            spineFit_of_teleFit (by simp only [List.length_map, hlen, hCDlen]; rfl) hfit
          rw [hw]
          exact fixEntryIotaCoreZero (hCDlen _) hi (hsortsF _)
            (hguardSem i hi _ (hguardAt hw)).1 ys hlen hsp
        · -- graph: the grading's slot chain
          exact fixEntryIotaCore hw (hCDlen _) hi (hokB _) ys hlen hok
  · -- (C)
    intro cvT capsT hf us _
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
    refine ⟨mkPisAV (pps (Level.substFn φ p.cvT.levelParams us))
      (.sort (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))), ?_, hFD.okTy _, ?_⟩
    · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, hlpsT]
      exact hFD₂.read _
    · intro ρ ts rest x hlents hfit hmem
      have hsp := spineFit_of_teleFit (by rw [hFD.len]; exact hlents) hfit
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = nativeTyAVI (u (Level.substFn φ p.cvT.levelParams us))
            (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (pps (Level.substFn φ p.cvT.levelParams us)) [] rss
            (tlss (Level.substFn φ p.cvT.levelParams us))
            (eiss (Level.substFn φ p.cvT.levelParams us))
            (Fss₀ (Level.substFn φ p.cvT.levelParams us))
            (Ess (Level.substFn φ p.cvT.levelParams us)) := by
        show m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacT, hleafT]
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = sumMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us)) 0
            (ds (Level.substFn φ p.cvT.levelParams us))
            (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2))
            (uChains [((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)]) := by
        show m₂.acval cvCa.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacC, hleafC]
      rw [hacT'] at hmem
      rw [hacC']
      show x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app _
      exact fixEntryEtaCore (hCDlen _) (hFD.len _) (hiff _) (hokB _) (hfold _) ts x hlents hsp hmem

/-! ## The assembly-facing wrapper -/

set_option maxHeartbeats 3200000 in
/-- **The table stage of a direct recursive install** (task #210 Part
A): at a structure-like block the P carrier survives the table's cons
(`stageFixTable`); at any other block the stage conses nothing. -/
theorem declNativeTable {F : Nat} {env env₁ envC env₂ : Env} {p : NativeParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {rhss : List Expr}
    (h₁ : env₁ = ⟨.indInfo cvTa (ConLeche.nativeCaps p) :: env.consts⟩)
    (hC : envC = ConLeche.consSumCtors p.nP ctorsA env₁)
    (hTbl : ConLeche.checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: envC.consts⟩ = .ok env₂)
    (mpC : EnvModelM V μ envC)
    (mp₃ : EnvModelM V μ ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: envC.consts⟩)
    {sAV : (Name → Nat) → Nat} {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hac₃ : mp₃.base2.acval = acvalWith mpC.base2.acval cvRa.name
      (fixLeafAV mpC.base2 p ppsAll dsF esF ksF eissF tssF ctorsA sAV))
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hRname : p.cvR.name = p.cvT.name.str "rec")
    (hCres : ∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (hresT : ConLeche.reservedBasisNames.contains p.cvT.name = false)
    (hresR₀ : ConLeche.reservedBasisNames.contains p.cvR.name = false)
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hwfEnv : ConLeche.EnvWF env)
    (hlenA : ctorsA.length = p.ctors.length)
    (hnFc : ∀ (j : Nat) (cA c : ConstantVal × Nat), ctorsA[j]? = some cA → p.ctors[j]? = some c →
      cA.2 = c.2)
    (hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, p.ctors[j]? = some c ∧
      cA.1.name = c.1.name ∧ cA.1.levelParams = p.cvT.levelParams ∧
      env₁.find? cA.1.name = none ∧
      cA.1.type.constsResolve env₁ = true ∧
      cA.1.name.isProjFnShape = false ∧
      ∃ sorts : List Level, sortss[j]? = some sorts ∧
      ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env₁
        p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa
        = .ok (cA.1, sorts))
    (hfT_C : envC.find? p.cvT.name = some (.indInfo cvTa (ConLeche.nativeCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hTfresh : env.find? p.cvT.name = none)
    (htrT : cvTa.type.constsResolve env = true)
    (hFD_C : FormerData mpC.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    (hcf_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      FixCtorFactsAt mpC.base2 env p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF j cA)
    {uAV : (Name → Nat) → Nat} {fssZ : (Name → Nat) → List (List AnnotTerm)}
    (hleafT : ∀ ψ, mpC.base2.acval p.cvT.name ψ
      = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mpC.base2.acval cA.1.name ψ
      = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    (hframes : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
          Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
            (∀ E ∈ esF j ψ, WellDenotedV V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs))))
    (hsortsOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ sorts : List Level, sortss[j]? = some sorts ∧ sorts.length = cA.2 ∧
      (∀ k, k < cA.2 → p.isProp = false → Level.leq (sorts.getD k .zero) p.resSort = some true) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        (p.isProp = false →
          FieldsBound (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2))) ∧
        ∀ k, k < cA.2 → ∀ as : List V,
          SpineFit ρ ((((dsF j ψ).drop p.nP).map (·.2.2)).take k) as →
          interp V (consList as ρ) ((((dsF j ψ).drop p.nP).map (·.2.2)).getD k default)
            ∈ˢ (univ ((sorts.getD k .zero).eval ψ) : V)))
    (hXR : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
        (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hRec : ConLeche.checkNativeRec (ConLeche.fueledOps μ F) envC p cvTa ctorsA = .ok (cvRa, rhss)) :
    Nonempty (EnvModelM V μ env₂) := by
  -- the case split: only a structure-like block conses a table
  unfold ConLeche.checkNativeTable at hTbl
  split at hTbl
  · next cA sorts =>
    split at hTbl
    · next hnIdx =>
      have hnIdx' : p.nIdx = 0 := beq_iff_eq.mp hnIdx
      obtain ⟨c, hc, hCname, hlpsC, -, -, hCshape, sorts', hsj, hCtor⟩ := hrunOf 0 cA rfl
      obtain rfl : sorts = sorts' := Option.some.inj hsj
      have hc' : p.ctors = [c] := by
        rw [List.length_singleton] at hlenA
        obtain ⟨c', hc''⟩ := List.length_eq_one_iff.mp hlenA.symm
        rw [hc''] at hc ⊢
        obtain rfl := Option.some.inj hc
        rfl
      have hnFc' : cA.2 = c.2 := hnFc 0 cA c rfl hc
      have hresC : ConLeche.reservedBasisNames.contains cA.1.name = false := by
        rw [hCname]; exact (hCres c (by rw [hc']; exact List.mem_singleton_self _)).2
      have hresR : ConLeche.reservedBasisNames.contains (p.cvT.name.str "rec") = false := by
        rw [← hRname]; exact hresR₀
      -- the capability record at a structure-like block
      have hcapsR := ConLeche.nativeCaps_single (p := p) hc'
      have hcaps : (ConLeche.nativeCaps p).eta = true →
          (Level.isEquiv p.resSort .zero == some true) = false ∧
          (ConLeche.nativeCaps p).etaCtor = cA.1.name ∧
          (ConLeche.nativeCaps p).etaParams = p.nP ∧
          (ConLeche.nativeCaps p).etaFields = cA.2 := by
        intro he
        rw [hcapsR] at he ⊢
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at he
        refine ⟨by rw [← hProp]; exact he.1.2, hCname.symm, rfl, hnFc'.symm⟩
      -- the recursor's constant and its freshness
      obtain ⟨cvRi, recTy, sty, u, hccvR, hgenR, -, -, -, -, -, -, -, hrules, hcvRa⟩ :=
        ConLeche.checkNativeRec_shape hRec
      obtain ⟨hRfresh₀, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := ConLeche.checkConstantVal_inv hccvR
      have hRname' : cvRa.name = p.cvR.name := by rw [hcvRa]
      have hRtype : cvRa.type = recTy := by rw [hcvRa]
      have hRfresh : envC.find? cvRa.name = none := by rw [hRname']; exact hRfresh₀
      have hfC_C : envC.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) := (hcf_C 0 cA rfl).1
      have hTR : p.cvT.name ≠ cvRa.name := by
        intro h; rw [h, hRfresh] at hfT_C; exact nomatch hfT_C
      have hCR : cA.1.name ≠ cvRa.name := by
        intro h; rw [h, hRfresh] at hfC_C; exact nomatch hfC_C
      -- the lookups at the recursor's environment
      have hfT₃ : (⟨.recInfo cvRa p.majorIdx p.rulePrefix
          (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA] rhss)
          :: envC.consts⟩ : Env).find? p.cvT.name
          = some (.indInfo cvTa (ConLeche.nativeCaps p)) :=
        ConLeche.Env.find?_cons_of_fresh hRfresh hfT_C
      have hfC₃ : (⟨.recInfo cvRa p.majorIdx p.rulePrefix
          (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA] rhss)
          :: envC.consts⟩ : Env).find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) :=
        ConLeche.Env.find?_cons_of_fresh hRfresh hfC_C
      -- the constructor type's shape
      obtain ⟨⟨_, hccvC⟩, ⟨cbs, es, hstrip, -⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
      have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by
        rw [hstrip]; rfl
      -- the structure's slots are mentioned by no stored piece: no table
      -- is stored below the table stage
      obtain ⟨-, -, -, -, hfreshTbl₃, -⟩ := ConLeche.checkStructProjTable_inv hTbl
      have hfreshTbl₁ : env₁.find? (projTableName p.cvT.name) = none := by
        have h1 := find?_none_of_cons hfreshTbl₃
        rw [hC] at h1
        exact ConLeche.consSumCtors_find?_none h1
      -- `NoProjEnv` across the block's conses
      obtain ⟨hfindC₀, -, -, -, -, hnfC, typeC, -, -, hannC, -, -, -, -, htyC⟩ :=
        ConLeche.checkConstantVal_inv hccvC
      have hnpT : ∀ j, Expr.NoProjAt p.cvT.name j cvTa.type :=
        fun j => ConLeche.Expr.noProjAt_of_constsResolve hTfresh _ htrT
      have hnpC : ∀ j, Expr.NoProjAt p.cvT.name j cA.1.type := by
        intro j
        have : cA.1.type = typeC := by rw [htyC]
        rw [this]
        exact ConLeche.annotateCore_noProjAt μ hannC hnfC
          (ConLeche.Env.findProj?_none_of_fresh hfreshTbl₁ j)
      have hnpC4 : ∀ j, ∀ c' ∈ ConLeche.nativeCtors4 [cA] p.kinds,
          Expr.NoProjAt p.cvT.name j c'.2.2.1 := by
        intro j c'
        unfold ConLeche.nativeCtors4
        cases p.kinds with
        | nil => intro hc'; simp at hc'
        | cons ks rest =>
          intro hc'
          simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_singleton] at hc'
          subst hc'
          exact hnpC j
      have hnp₃ : ∀ j, NoProjEnv ⟨.recInfo cvRa p.majorIdx p.rulePrefix
          (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA] rhss)
          :: envC.consts⟩ p.cvT.name j := by
        intro j
        have h0 : NoProjEnv env p.cvT.name j := noProjEnv_of_fresh hwfEnv hTfresh j
        have h1 : NoProjEnv env₁ p.cvT.name j := by
          rw [h₁]
          exact h0.cons (c₀ := .indInfo cvTa (ConLeche.nativeCaps p))
            (NoProjHead.ofType (hnpT j) (fun _ _ _ h => nomatch h)
              (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))
        have h2 : NoProjEnv envC p.cvT.name j := by
          rw [hC]
          exact noProjEnv_consSumCtors h1 (fun c' hc' => by
            obtain rfl := List.mem_singleton.mp hc'
            exact hnpC j)
        refine h2.cons ⟨?_, (fun _ _ _ h => nomatch h), ?_,
          (fun _ h => nomatch h)⟩
        · show Expr.NoProjAt p.cvT.name j cvRa.type
          rw [hRtype]
          exact ConLeche.Expr.NoProjAt.structRecTyR hgenR (hnpT j) (hnpC4 j)
        · intro cv mI rP rules heq r hr
          injection heq with _ _ _ hrules'
          subst hrules'
          obtain ⟨hlenR, hallR⟩ := ConLeche.checkNativeRules_inv hrules
          cases rhss with
          | nil => exact absurd hr List.not_mem_nil
          | cons rhs rest =>
            simp only [ConLeche.sumRules, List.mem_cons, List.not_mem_nil, or_false] at hr
            subst hr
            obtain ⟨rhs', hget, hgen, -, -, -, -⟩ := hallR 0 (by
              rw [← hlenR]; exact Nat.succ_pos _)
            obtain rfl : rhs = rhs' := by simpa using hget
            refine ⟨ConLeche.Expr.NoProjAt.structRecRhsR hgen (hnpT j) (hnpC4 j), ?_⟩
            intro lvls pins hfire
            split at hfire <;> exact nomatch hfire
      -- the former's and the constructor's data at the recursor's carrier
      have hcbT_C : ConstsBound envC cvTa.type := constsBound_of_constsResolve _
        (mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT_C)).2.2.1
      have hcbC_C : ConstsBound envC cA.1.type := constsBound_of_constsResolve _
        (mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC_C)).2.2.1
      have hFD₃ : FormerData mp₃.base2 cvTa p.nP p.resSort ppsAll := by
        have := hFD_C.cross (c₀ := .recInfo cvRa p.majorIdx p.rulePrefix
          (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA] rhss))
          hRfresh (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT_C mp₃.base2 hac₃
        rwa [hnIdx', Nat.add_zero] at this
      have hCD_C := (hcf_C 0 cA rfl).2.2
      have hidxNil : idxF 0 = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [hCD_C.idxLen, hnIdx']
      have hCD₃ := hCD_C.toCtorDataI.cross (c₀ := .recInfo cvRa p.majorIdx p.rulePrefix
        (ConLeche.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA] rhss))
        hRfresh hTR (fun _ => ConsCrossAt.ofNtc fun _ h => nomatch h) hcbC_C
        (fun e he => by rw [hidxNil] at he; exact absurd he List.not_mem_nil) mp₃.base2 hac₃
      have hEsNil : ∀ ψ, esF 0 ψ = [] := by
        intro ψ
        apply List.eq_nil_of_length_eq_zero
        rw [hCD_C.lenE, hnIdx']
      -- the parameter telescope is the whole former telescope
      have hlenP : ∀ ψ, (ppsAll ψ).length = p.nP := by
        intro ψ; rw [hFD_C.len ψ, hnIdx', Nat.add_zero]
      have hIds : ∀ ψ, ((ppsAll ψ).drop p.nP).map (·.2.2) = [] := by
        intro ψ; rw [List.drop_of_length_le (Nat.le_of_eq (hlenP ψ))]; rfl
      have hTake : ∀ ψ, (ppsAll ψ).take p.nP = ppsAll ψ :=
        fun ψ => List.take_of_length_le (Nat.le_of_eq (hlenP ψ))
      -- the one constructor's chains
      have hFssEq : ∀ ψ, fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)
          = [((dsF 0 ψ).drop p.nP).map (·.2.2)] := fun _ => rfl
      have hEssEq : ∀ ψ, essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0) = [[]] := by
        intro ψ
        show [esF 0 ψ] = [[]]
        rw [hEsNil]
      -- the leaves at the recursor's carrier
      have hleafT₃ : ∀ ψ, mp₃.base2.acval p.cvT.name ψ
          = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) [] (rssOfK ksF [cA].length)
              (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0))
              (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)) (fssZ ψ)
              (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)) := by
        intro ψ
        rw [hac₃, acvalWith_ne hTR, hleafT ψ, hIds ψ]
      have hleafC₃ : ∀ ψ, mp₃.base2.acval cA.1.name ψ
          = sumMkAV (p.resSort.eval ψ) 0 (dsF 0 ψ) (((dsF 0 ψ).drop p.nP).map (·.2.2))
              (uChains [((dsF 0 ψ).drop p.nP).map (·.2.2)]) := by
        intro ψ
        rw [hac₃, acvalWith_ne hCR, hleafC 0 cA rfl ψ, hFssEq ψ]
      -- the family at the parameters is the one-constructor fibre
      have hfoldAt : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
          SpineFit ρ ((ppsAll ψ).map (·.2.2)) ts →
          ts.foldl SetTheory.app (interp V ρ
              (nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) [] (rssOfK ksF [cA].length)
                (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0))
                (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)) (fssZ ψ)
                (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0))))
            = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ) (consList ts ρ)
                [((dsF 0 ψ).drop p.nP).map (·.2.2) ++ [idxEqAV []]]) := by
        intro ψ ρ ts hsp
        have hρ' : Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse (consList ts ρ) := by
          rw [hTake]
          have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
          rwa [List.append_nil] at this
        obtain ⟨hX, hreal⟩ := hXR ψ (consList ts ρ) hρ'
        rw [hIds ψ] at hX hreal
        rw [hnIdx'] at hreal
        have hsh : shiftE ([] : List AnnotTerm).length 0 (consList ts ρ) = consList ts ρ :=
          shiftE_zero_zero _
        have hfr : ConLeche.Semantics.frameIdx ([] : List AnnotTerm).length (consList ts ρ) = [] := rfl
        have hbase : FixBaseI (uAV ψ) (p.resSort.eval ψ) (consList ts ρ) [] (rssOfK ksF [cA].length)
            (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0))
            (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)) (fssZ ψ)
            (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ [cA] 0)) := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hsh]; exact hX.hI
          · rw [hsh]; exact hX.hok
          · rw [hsh, hfr]; trivial
        rw [nativeTyAVI_fold hsp hbase, hsh, hfr, fixFamI_app_eq_sum hX hreal (is := []) trivial,
          consList_nil, hFssEq ψ, hEssEq ψ]
        show sumSet _ (sumFibre _ _ (rChains 0 0 [_] [[]])) = _
        rw [rChains_single_nil]
      -- the constructor's frames
      have hframes₀ := hframes 0 cA rfl
      obtain ⟨sorts'', hsj', -, hleq, hsortsAll⟩ := hsortsOf 0 cA rfl
      obtain rfl : sorts = sorts'' := Option.some.inj hsj'
      refine stageFixTable mp₃ hTbl hfT₃ hcaps hlpsT hfC₃ hlpsC hstripC
        hProp hTshape hCshape hresT hresR hresC hnp₃ hFD₃ hCD₃.read hCD₃.len hCD₃.below hleq
        hleafT₃ hleafC₃ hfoldAt ?_ ?_ ?_ ?_
      · intro ψ ρ
        have := hframes₀.1 ψ ρ
        rwa [hTake] at this
      · intro ψ ρ hρ
        exact ⟨(hframes₀.2 ψ ρ hρ).1, (hframes₀.2 ψ ρ hρ).2.1⟩
      · intro ψ ρ hρ hp
        exact (hsortsAll ψ ρ hρ).1 hp
      · intro ψ ρ hρ
        exact (hsortsAll ψ ρ hρ).2
    · next =>
      obtain rfl := Except.ok.inj hTbl
      exact ⟨mp₃⟩
  · next =>
    obtain rfl := Except.ok.inj hTbl
    exact ⟨mp₃⟩

end ConLeche.Model
