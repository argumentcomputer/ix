import IxCCGrounding.RecRun

/-!
# ι at a recursor with parameters, from the law's own spine (`IxCCCorrect.SpineIota`)

The check the orchestrator asked for (`plans/GROUNDING.md` §21.4): at a recursor with parameters,
does the kernel's ι law by itself put the constructor's fields in the rule's λ-domains **at the
recursor's parameters**, in every model, with no canonicity hypothesis?

**Yes, for parameters.** The ι law (`Ix.Kernel.IotaRule`) concludes `SpineOk H (xs.take rP ++
ys.drop nP)`: each step of the rule's right-hand side `H` lies in some product with its argument
in that product's domain. `spineOk_lamTele` reads that against the right-hand side's λs: a
graph-regime λ lying in a graph-regime product has the product's domain (`lamR_dom_eq`), and a
graph-regime λ never lies in a regime-0 product (it is no proof point, `lamR_ne_pt`). So every
argument is in its λ's own domain, which gives both the β step and the `Fits` the rule body's
context needs. `paramsBlindIota` is `noParamsIota` at a rule that does not compare parameters
(`compareParams = false`, all of the corpus's `List.rec`/`Option.rec` rules): the major is the
constructor applied to **its own** parameters and fields, and nothing relates them to the
recursor's parameters.

**What remains is levels.** The ι law asks the major to be the constructor's image at the levels
the major's domain names (`hK`, `hys`). A SrcEval constructor value carries the levels it was
built at (`RelV.con`); where those differ from the recursor's, equating the two images is
`CtorCanon`'s level half (`ctorFields_canon`). For a constructor without level parameters it is
`cval_params` alone (`ctorFields_noLevels`). See `plans/GROUNDING.md` §23.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Grounding

universe u

section Sem

variable {V : Type u} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **The law's spine puts each argument in its λ's domain.** A λ-telescope denoting `H`, every
λ of it in graph regime, applied along a `SpineOk` spine of its length: the arguments fit the
telescope's domains (as a `∀`-telescope over any codomain), and the application is the body's
denotation with them bound. No typing and no canonicity: `lamR_dom_eq` and `lamR_ne_pt`. -/
theorem spineOk_lamTele {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (b : KExpr) {ρ : BVarIdx → V} {H : V} {xs : List V},
      Denotes cval env φ ρ (lamTele bs b) H → SpineOk H xs → xs.length = bs.length →
      (∀ p ∈ bs, regime φ p.2.pw ≠ 0) →
      (∀ C : KExpr, Fits cval env φ ρ (piTele bs C) xs (pushAll xs ρ) C) ∧
        ∃ Y, Denotes cval env φ (pushAll xs ρ) b Y ∧ xs.foldl app H = Y
  | [], b, ρ, H, [], hH, _, _, _ =>
    ⟨fun C => by rw [pushAll_nil]; exact .nil, H, by rwa [pushAll_nil], rfl⟩
  | [], _, _, _, _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, _, _, _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, b, ρ, H, x :: xs, hH, hsp, hl, hreg => by
    have hH' : Denotes cval env φ ρ (.lam A (lamTele bs b) m) H := hH
    obtain ⟨Ad, F, hA, hF, -, rfl⟩ := den_lam.mp hH'
    have hr : regime φ m.pw ≠ 0 := hreg (A, m) (List.mem_cons_self ..)
    obtain ⟨⟨v, A', B, hmem, hx⟩, hsp'⟩ := hsp
    -- the product the law names is in graph regime, so it has the λ's domain
    have hv : v ≠ 0 := by
      intro hv0
      subst hv0
      exact lamR_ne_pt hr (eq_pt_of_mem_piR_zero hmem)
    have hAA : A' = Ad := lamR_dom_eq hr hv hmem
    rw [hAA] at hx
    have happ : app (lamR (regime φ m.pw) Ad F) x = F x := app_lamR_pos hr hx
    rw [happ] at hsp'
    obtain ⟨hfit, Y, hY, hfold⟩ := spineOk_lamTele bs b (ρ := push x ρ) (hF x hx) hsp'
      (by simpa using hl) (fun p hp => hreg p (List.mem_cons_of_mem _ hp))
    refine ⟨fun C => ?_, Y, by rwa [pushAll_cons], ?_⟩
    · have h := hfit C
      rw [← pushAll_cons] at h
      exact .cons hA hx h
    · rw [List.foldl_cons, happ]
      exact hfold

/-- **ι at a recursor with parameters, at a rule that does not compare them** (no canonicity):
the recursor applied to its prefix `As.take mI` and to a major that is rule `krl`'s constructor
image `K` at the major domain's levels applied to `ys` (the constructor's **own** parameters and
its fields, fitting the constructor's type there) is the rule body's denotation with the prefix
and the fields `ys.drop nP` bound, which fit the rule's λ-domains. Laws: ι alone. -/
theorem paramsBlindIota (M : Model V env) (hι : IotaLaw M.cval env) {kr : KKey}
    {cvr : ConstantVal .anon} {mI : Nat} {krules : List (RecRule .anon)}
    (hf : env.find? kr = some (.recInfo cvr mI mI krules)) {krl : RecRule .anon}
    (hkrl : krl ∈ krules) (hcmp : krl.compareParams = false) {cvC : ConstantVal .anon}
    {nP nF : Nat} (hcC : env.find? krl.ctor = some (.ctorInfo cvC nP nF))
    {bs : List (KExpr × BinderMeta)} {b : KExpr} (hrhs : krl.rhs = lamTele bs b)
    (hbsl : bs.length = mI + nF) {φ : LevelParam → Nat} (hreg : ∀ p ∈ bs, regime φ p.2.pw ≠ 0)
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey} {ls : List Level}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    {K : V} {ys : List V} {σC : BVarIdx → V} {RC : KExpr}
    (hK : Denotes M.cval env φ ρ (.const krl.ctor ls) K)
    (hys : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC)
    (hyl : ys.length = nP + nF) (hmaj : As[mI]? = some (ys.foldl app K)) :
    ∃ H Y, Denotes M.cval env φ ρ krl.rhs H ∧
      Denotes M.cval env φ (pushAll (As.take mI ++ ys.drop nP) ρ) b Y ∧
      As.foldl app (M.cval kr φ) = Y ∧
      ∀ C : KExpr, Fits M.cval env φ ρ (piTele bs C) (As.take mI ++ ys.drop nP)
        (pushAll (As.take mI ++ ys.drop nP) ρ) C := by
  -- the arguments: the prefix and the major
  have hdrop : As.drop mI = [ys.foldl app K] := by
    rw [List.getElem?_eq_getElem (by omega)] at hmaj
    rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hmaj,
      List.drop_eq_nil_of_le (by omega)]
  have hsplit : As = As.take mI ++ [ys.foldl app K] := by rw [← hdrop, List.take_append_drop]
  have hxl : (As.take mI).length = mI := by simp; omega
  have hfit' := hfit
  rw [hsplit] at hfit'
  obtain ⟨σ1, R1, hf1, hf2⟩ := fits_append hfit'
  have hR1 : R1 = .forallE dom body m := by rw [fits_piBody hf1, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hKX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ ys.foldl app K ∈ˢ X := by
    cases hf2 with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  -- ι at rule `krl`, at the recursor's own level parameters; no parameter comparison
  have hRden : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param)) (M.cval kr φ) := by
    have h1 : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param))
        (M.cval kr (Level.substFn φ cvr.levelParams (cvr.levelParams.map .param))) :=
      Denotes.const (ci := .recInfo cvr mI mI krules) hf (by simp [ConstantInfo.toConstantVal])
    rwa [substFn_self] at h1
  obtain ⟨H, hH, -, hspine, heq⟩ := hι kr cvr mI mI krules krl hf hkrl cvC nP nF hcC
    (cvr.levelParams.map .param) φ ρ σ1 σC (As.take mI) ys dom body RC m D ls (M.cval kr φ) K X
    (by simp) hxl hyl hRden (by rw [inst_self]; exact hf1) hdom hX hK hys hKX
    (fun h => absurd h (by rw [hcmp]; decide)) (fun h => absurd rfl h)
  rw [inst_self] at hH
  have e2 : (As.take mI).take mI = As.take mI := by rw [List.take_take, Nat.min_self]
  rw [e2] at hspine heq
  -- β through the right-hand side, along the law's own spine
  rw [hrhs] at hH
  obtain ⟨hfits, Y, hY, hYe⟩ := spineOk_lamTele bs b hH hspine
    (by simp [hxl, hyl]; omega) hreg
  refine ⟨H, Y, by rw [hrhs]; exact hH, hY, ?_, hfits⟩
  have e3 : As.foldl app (M.cval kr φ) =
      (As.take mI ++ [ys.foldl app K]).foldl app (M.cval kr φ) := by rw [← hsplit]
  rw [e3, heq, hYe]

end Sem

end IxCC.Correct
