module

-- lane S-red's kit is the SHARED one: `DenoteMetaSpine`'s list algebra,
-- `denoteMeta_mkAppN(_inv)`, `frame_spine`, `hoist_spine`,
-- `mkAppN_of_fitA`, `PiChain`/`peelPis_of_piChain` and the tower
-- entry's reading live there, not here.
public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitShift
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Model.Annot.BitClosed
import ConLeche.Semantics.DenoteClosed

public section

/-!
# The ι lane's transplanted kit (task #305, lane S-iota)

The spine, frame and fit lemmas the ι rule and the three stuck-major
rescues need, restated over `Model/Annot/BitLemmas.lean`'s
`DenoteMetaSpine` and proved here rather than imported: every row this
lane mines is TRANSPLANTED from the `Model/Steps/*` file the docstring
cites — the argument, not the import — and that tier is gone since the
task #305 closing.

Provenance, row by row (the original is the docstring's citation):

* the `DenoteMetaSpine` residue this lane alone uses
  (`exists_of_all`); the rest of the spine API is
  `Model/Annot/BitLemmas.lean`'s, shared;
* `interp_mkAppN_congrK` — `Model/Steps/Stuck.lean:146`;
* `constTy_pkg` — `constType_pkg` (`Model/Steps/IotaRows.lean:200`);
* `denoteMeta_const_arityK` — `denoteMeta_const_arity` (`:233`);
* the annotated `take`/`drop`/`getD` list algebra — `IotaRows.lean:107-153`.

Nothing here is new mathematics; the statements are the originals',
with the `Frame`/`Graded`/`LeavesSub` abbreviations of `Motive.lean`
in place of the claims' spelled-out conjunctions.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The `DenoteMetaSpine` API

`mem` and `getD` are `Model/Annot/BitLemmas.lean`'s since the task
#305 closing; what is left here is the residue only this lane uses. -/

namespace DenoteMetaSpine

variable {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}

/-- Every list of readable expressions has a reading spine. -/
theorem exists_of_all :
    ∀ (as : List Expr), (∀ x ∈ as, ∃ v, denoteMeta acval env φ d x = some v) →
      ∃ vs, DenoteMetaSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil => intro _; exact ⟨[], .nil⟩
  | cons a as ih =>
    intro h
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun y hy => h y (List.mem_cons_of_mem a hy))
    exact ⟨v :: vs, .cons hv hvs⟩

end DenoteMetaSpine

/-- **The spine congruence at `interp`** (`interp_mkAppN_congr`,
`Model/Steps/Stuck.lean:146`). -/
theorem interp_mkAppN_congrK {ρ : Nat → V} :
    ∀ (asa bsa : List AnnotTerm) {fa fb : AnnotTerm},
      interp V ρ fa = interp V ρ fb →
      asa.map (interp V ρ) = bsa.map (interp V ρ) →
      interp V ρ (AnnotTerm.mkAppN fa asa)
        = interp V ρ (AnnotTerm.mkAppN fb bsa) := by
  intro asa
  induction asa with
  | nil =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => exact hf
    | cons _ _ => simp at hall
  | cons a as ih =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => simp at hall
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hall
      exact ih bs (by simp only [interp_app, hf, hall.1]) hall.2

/-- The frame of an application built over framed parts. -/
theorem frame_mkAppN {d : Nat} {f : Expr} {as : List Expr}
    (hf : Frame d f) (has : ∀ x ∈ as, Frame d x) :
    Frame d (Expr.mkAppN f as) := by
  refine ⟨ConLeche.Expr.WScoped.mkAppN hf.1 (fun y hy => (has y hy).1),
    ConLeche.looseBVarsBounded_mkAppN hf.2.1 (fun y hy => (has y hy).2.1),
    fun l hl => ?_⟩
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf.2.2 l hl'
  · exact (has y hy).2.2 l hly

/-- The leaves of an application are its parts' (`fvarLeaves_mkAppN`,
packaged at `Motive.lean`'s `LeavesSub`). -/
theorem leavesSub_mkAppN {f e : Expr} {as : List Expr}
    (hf : LeavesSub f e) (has : ∀ x ∈ as, LeavesSub x e) :
    LeavesSub (Expr.mkAppN f as) e := by
  intro l hl
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf l hl'
  · exact has y hy l hly

/-- A closed expression has no leaves at all. -/
theorem leavesSub_of_not_hasFvar {f e : Expr} (h : f.hasFvar = false) :
    LeavesSub f e := by
  intro l hl
  rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  exact nomatch hl

/-! ## The stored data -/

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and closed (`constType_pkg`,
`Model/Steps/IotaRows.lean:200`). -/
theorem constTy_pkg {m : EnvModel V env} (hct : ConstType m φ)
    {n : Name} {ci : ConLeche.ConstantInfo} (hf : env.find? n = some ci)
    (hnt : ci.isTowerEntry = false) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : AnnotTerm,
      (∀ d : Nat, denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hnt hlen
  have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hta 1 k)
      hta,
    hok, hmem, hnf, hbd⟩

/-- A closed stored type is framed and in context at every depth. -/
theorem frame_of_not_hasFvar {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {e : Expr} (hnf : e.hasFvar = false)
    (hbd : e.looseBVarsBounded 0 = true) (hlen : Δa.length = d) :
    Frame d e ∧ CtxOk m φ d Δa e :=
  ⟨⟨ConLeche.Expr.WScoped.of_not_hasFvar hnf, hbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    ⟨hlen, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl
      exact nomatch hl⟩⟩

/-- A `.const` that reads was applied at the stored arity, and its
reading is the leaf (`denoteMeta_const_arity`,
`Model/Steps/IotaRows.lean:233`). -/
theorem denoteMeta_const_arityK {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    {ea : AnnotTerm} (hf : env.find? n = some ci)
    (h : denoteMeta acval env φ d (.const n us) = some ea) :
    us.length = ci.toConstantVal.levelParams.length ∧
      ea = acval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [denoteMeta, hf] at h
  dsimp only at h
  split at h
  · next hlen => exact ⟨hlen, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The annotated list algebra

`map_interp_getD_eq`, `getD_takeA`, `getD_dropA`, `take_getD_splitA`
(`Model/Steps/IotaRows.lean:107-153`), transplanted verbatim. -/

/-- Pointwise reading of a map equality at `getD` slots. -/
theorem map_interp_getD_eqK {ρ : Nat → V} {as bs : List AnnotTerm}
    (h : as.map (interp V ρ) = bs.map (interp V ρ))
    {i : Nat} (hi : i < as.length) :
    interp V ρ (as.getD i default) = interp V ρ (bs.getD i default) := by
  have hlen : as.length = bs.length := by
    have := congrArg List.length h
    simpa using this
  have h1 : (as.map (interp V ρ))[i]? = (bs.map (interp V ρ))[i]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)] at h1
  simpa using h1

/-- `getD` through `take`, below the cut. -/
theorem getD_takeAK {as : List AnnotTerm} {k i : Nat} (hi : i < k) :
    (as.take k).getD i default = as.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi]

/-- `getD` through `drop`. -/
theorem getD_dropAK (as : List AnnotTerm) (k i : Nat) :
    (as.drop k).getD i default = as.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A list of length `k + 1` splits as its prefix plus its last element. -/
theorem take_getD_splitAK {as : List AnnotTerm} {k : Nat}
    (h : as.length = k + 1) :
    as = as.take k ++ [as.getD k default] := by
  have hlen : (as.drop k).length = 1 := by
    rw [List.length_drop, h]; omega
  obtain ⟨a, ha⟩ : ∃ a, as.drop k = [a] := by
    match hd : as.drop k with
    | [a] => exact ⟨a, rfl⟩
    | [] => rw [hd] at hlen; simp at hlen
    | a :: b :: t => rw [hd] at hlen; simp at hlen
  have hget : a = as.getD k default := by
    have h0 : (as.drop k).getD 0 default = a := by rw [ha]; rfl
    rw [getD_dropAK, Nat.add_zero] at h0
    exact h0.symm
  calc as = as.take k ++ as.drop k := (List.take_append_drop k as).symm
    _ = as.take k ++ [as.getD k default] := by rw [ha, hget]

/-! ## The redex's own slots

`AnnotTerm.mkAppN_append`, `wellDenotedV_app_congr_arg` and
`wellDenotedV_mkAppN_snoc_congr` (`Model/Steps/IotaGate.lean:81-115`):
the subject's grading is about the ORIGINAL major slot and the licensed
walk is handed the prepared one, so the last argument is exchanged
along the reduction's own `interp` equation. -/

theorem AnnotTerm.mkAppN_appendK (f : AnnotTerm) :
    ∀ (as bs : List AnnotTerm),
      AnnotTerm.mkAppN f (as ++ bs) = AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs
  | [], _ => rfl
  | _ :: as, bs => AnnotTerm.mkAppN_appendK _ as bs

/-- **An app's argument may be exchanged for an interpretation-equal
graded one**. -/
theorem wellDenotedV_app_congr_argK {ρ : Nat → V} {f a a' : AnnotTerm}
    (h : WellDenotedV V ρ (.app f a)) (ha' : WellDenotedV V ρ a')
    (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (.app f a') := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  obtain ⟨hf, -, v, A, B, hslot, hmem, hcod⟩ := h1
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hf, ha'.1, v, A, B, hslot, heq ▸ hmem, hcod⟩
  · rw [AnnotValid_app]
    exact ⟨h2.1, ha'.2⟩

/-- The same at a spine's last argument. -/
theorem wellDenotedV_mkAppN_snoc_congrK {ρ : Nat → V} {f a a' : AnnotTerm}
    {as : List AnnotTerm}
    (h : WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a])))
    (ha' : WellDenotedV V ρ a') (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a'])) := by
  rw [AnnotTerm.mkAppN_appendK] at h ⊢
  exact wellDenotedV_app_congr_argK h ha' heq

/-! ## The fired rule's right-hand side and the telescope residual -/

/-- The fired rule's right-hand side reads at every depth
(`recRhs_depth`, `Model/Steps/IotaRows.lean:296`). -/
theorem recRhs_depthK {m : EnvModel V env}
    {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) {us : List Level} {Ra : AnnotTerm}
    (hRa0 : denoteMeta m.acval env φ 0
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
      = some Ra) :
    (∀ d : Nat, denoteMeta m.acval env φ d
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra) ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).hasFvar = false ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP rules rfl rl hmem
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hRnf
  have hbd : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hRa0 1 k)
      hRa0,
    hnf, hbd⟩

/-- The frame of a `∀`-telescope's residual (`piResidual_frame`,
`Model/Steps/IotaRows.lean:155`, at `Motive.lean`'s `Frame`). -/
theorem piResidual_frameK {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      ConLeche.piResidual T args = some rest →
      Frame d T → CtxOk m φ d Δa T →
      (∀ x ∈ args, Frame d x ∧ CtxOk m φ d Δa x) →
      Frame d rest ∧ CtxOk m φ d Δa rest := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hfr hCt _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact ⟨hfr, hCt⟩
  | cons a as ih =>
    intro rest h hfr hCt hfrA
    obtain ⟨hw, hb, hL⟩ := hfr
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _ _, h => exact nomatch h
    | .letE _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE ty body mb, h =>
    obtain ⟨⟨hwa, hba, hLa⟩, hCa⟩ := hfrA a (by simp)
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ih h ⟨Expr.WScoped.instantiate1_gen hwa 0 hw.2,
        Expr.looseBVarsBounded_instantiate1_gen hba hb.2, fun l hl => ?_⟩
      ⟨hCt.1, fun l hl => ?_⟩ (fun x hx => hfrA x (by simp [hx])) <;>
    · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · first
        | exact hL l (by simp [Expr.fvarLeaves, h2])
        | exact hCt.2 l (by simp [Expr.fvarLeaves, h2])
      · first
        | exact hLa l h2
        | exact hCa.2 l h2

/-- **A `TeleFitPA` fit's residual is the reading of the checker's own
`piResidual`** (`teleFitPA_residual`, `Model/Steps/IotaKit.lean:174`). -/
theorem teleFitPA_residualK {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {ρ : Nat → V} {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {Ta restA : AnnotTerm}
      {vs : List AnnotTerm},
      ConLeche.piResidual ty args = some rest →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteMeta acval env φ d ty = some Ta →
      DenoteMetaSpine acval env φ d args vs →
      TeleFitPA V ρ Ta vs restA →
      denoteMeta acval env φ d rest = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest Ta restA vs hpr _ _ hty hsp hfit
    obtain rfl : rest = ty := (Option.some.inj hpr).symm
    cases hsp
    cases hfit
    exact hty
  | cons a as ih =>
    intro ty rest Ta restA vs hpr hwty hargs hty hsp hfit
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body mb, hpr, hwty, hty => ?_
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hty
    have hbody' : denoteMeta acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteMeta_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    cases hfit with
    | cons _ hfit' =>
      exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp' hfit'

/-! ## The reverse opening, read

`denoteMeta_openRev_base` and `denoteMeta_openRev`
(`Model/Steps/IotaKit.lean:66`, `:103`), transplanted — the ONE copy
since the task #305 closing, which is why `Model/IndOpenRev.lean` and
`Model/IndBottomNested.lean` read them from here: the `.nested`
fire's comparands are stored pins instantiated at the recursor's
parameter prefix, and this is what turns the law's OPEN reading at
depth `rP` into the instantiated comparand's reading at the ambient
depth. -/

/-- **The base-independence of the opened validated reading**
(`denote_openRev_base`'s mirror, `Model/Steps/IotaKit.lean:66`): a
constant-frame subject's reverse opening reads to the same annotation at every base.  The lift the
induction has to absorb is killed by `AnnotTerm.liftN_eq_self` at the
erasure's bvar bound — `denoteMeta_closed`'s route, one depth up. -/
theorem denoteMeta_openRev_base {acval : Name → (Name → Nat) → AnnotTerm}
    {cval : TConstVal}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denoteMeta acval env φ (d + n) (openRev d n e)
      = denoteMeta acval env φ n (openRev 0 n e) := by
  intro d
  induction d with
  | zero => rw [Nat.zero_add]
  | succ d ih =>
    have h1 : openRev (d + 1) n e = (openRev d n e).shiftFrom 0 :=
      (openRev_shiftFrom hnf d n).symm
    rw [show d + 1 + n = (d + n) + 1 from by omega, h1,
      denoteMeta_shiftFrom (p := 0) hacl (openRev d n e) (d + n)
        (Nat.zero_le _)
        (openRev_WScoped (Expr.WScoped.of_not_hasFvar hnf) n),
      ih]
    cases hden : denoteMeta acval env φ n (openRev 0 n e) with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Nat.sub_zero]
      refine AnnotTerm.liftN_eq_self v ?_ 1
      have hws : Expr.WScoped n (openRev 0 n e) := by
        have h2 := openRev_WScoped (d := 0)
          (Expr.WScoped.of_not_hasFvar hnf) n
        rwa [Nat.zero_add] at h2
      have hbv := denote_bvarsBelow (cval := cval) (env := env) (φ := φ)
        hcl n (openRev 0 n e) hws
        (openRev_bounded n 0 (by simpa using hb))
        (denoteMeta_erase hlink n (openRev 0 n e) hden)
      exact hbv.mono (by omega)

/-- **Real-argument instantiation, read through the reverse opening**
(`denote_openRev`'s mirror, `Model/Steps/IotaKit.lean:103`). -/
theorem denoteMeta_openRev {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      denoteMeta acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denoteMeta acval env φ (d + as.length)
            (openRev d as.length e)).map (AnnotTerm.instRevChain vs) := by
  intro as
  induction as with
  | nil =>
    intro e d _ _ _ vs hsp
    cases hsp
    show denoteMeta acval env φ d e = (denoteMeta acval env φ (d + 0) e).map _
    cases denoteMeta acval env φ d e <;> rfl
  | cons a as ih =>
    intro e d hargs hfb hb vs hsp
    cases hsp with
    | @cons _ va _ vs' ha hsp' => ?_
    have hargs' : ∀ x ∈ as, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true :=
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    show denoteMeta acval env φ d
      (Expr.instSeq as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))) = _
    rw [show (a :: as).length - 1 - 1 = as.length - 1 from by simp,
      show (a :: as).length - 1 = as.length from by simp]
    rw [ih (e := e.instantiate1 a as.length) hargs'
      (Expr.fvarsBelow_instantiate1_gen hwa.fvarsBelow _ hfb)
      (Expr.looseBVarsBounded_instantiate1_gen hba (by simpa using hb))
      hsp']
    -- the opened side: commute the argument out, then β at the top
    rw [openRev_instantiate1_top hba d as.length e]
    have ha' : denoteMeta acval env φ (d + as.length) a
        = some (va.liftN as.length) := by
      rw [denoteMeta_lift hacl hwa (d + as.length) (by omega), ha,
        show d + as.length - d = as.length from by omega]
      rfl
    rw [denoteMeta_beta (ty := .sort .zero) hacl hainst
      (openRev_fvarsBelow hfb as.length) (hwa.mono (by omega)) hba ha' 0]
    show ((denoteMeta acval env φ (d + as.length + 1)
      (openRev d (as.length + 1) e)).map
        (AnnotTerm.inst · (va.liftN as.length) 0)).map
        (AnnotTerm.instRevChain vs') = _
    rw [Option.map_map,
      show d + as.length + 1 = d + (a :: as).length from by
        simp only [List.length_cons]
        omega,
      show (a :: as).length = as.length + 1 from rfl]
    cases denoteMeta acval env φ (d + (as.length + 1))
        (openRev d (as.length + 1) e) with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
      show AnnotTerm.instRevChain vs' (X.inst (va.liftN as.length) 0) = _
      rw [show AnnotTerm.instRevChain (va :: vs') X
        = AnnotTerm.instRevChain vs' (X.inst (va.liftN vs'.length) 0) from rfl,
        hsp'.length]

/-- **The base-independence of the opened validated reading**, at the
lane's own spelling — `denoteMeta_openRev_base` above, whose statement
this is. -/
theorem denoteMeta_openRev_baseK {acval : Name → (Name → Nat) → AnnotTerm}
    {cval : TConstVal}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denoteMeta acval env φ (d + n) (openRev d n e)
      = denoteMeta acval env φ n (openRev 0 n e) :=
  denoteMeta_openRev_base hacl hlink hcl hnf hb

/-- **Real-argument instantiation, read through the reverse opening**,
at the lane's own spelling — `denoteMeta_openRev` above at `m.acval`. -/
theorem denoteMeta_openRevK {m : EnvModel V env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (m.acval n ψ).inst y k = m.acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List AnnotTerm}, DenoteMetaSpine m.acval env φ d as vs →
      denoteMeta m.acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denoteMeta m.acval env φ (d + as.length)
            (openRev d as.length e)).map (AnnotTerm.instRevChain vs) :=
  denoteMeta_openRev hacl hainst

/-- A list member is the value at one of its indices (the shape the
`∀ x ∈ bsa` grading premises need when the fact is indexed). -/
theorem mem_getD_index {α : Type _} [Inhabited α] {l : List α} {x : α}
    (h : x ∈ l) : ∃ j, j < l.length ∧ l.getD j default = x := by
  obtain ⟨j, hj, hx⟩ := List.getElem_of_mem h
  exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hx]; rfl⟩

end ConLeche.Model.Rules
