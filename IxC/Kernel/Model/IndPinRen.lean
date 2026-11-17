module

public import IxC.Kernel.Model.IndPinRow
public import IxC.Kernel.Model.IndNestedParam
public import IxC.Kernel.Model.IndRenJudge
import IxC.Kernel.Verify.Denote.IndFrame
import IxC.Kernel.Verify.BridgeWfImp
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Denote.OpenRevDenote

public section

/-!
# A nested rule's pins, typed renamed

A nested rule's pins are open terms of the recursor's prefix: `nestedParamSupply` and
`nestedPinRow` (`Model/IndNestedParam.lean`, `Model/IndPinRow.lean`) read their typing
against the constructor's parameter domains at the **public** frame (the prefix variables
opened from the recursor's type). The renamed record (`IotaThmNRenRunJ`) types the renamed
pins against the renamed constructor's domains instead.

Both theorems are generic in that frame, and their conclusions are about readings only. So
each is called here at the **renamed frame**: the public frame's variables, pins, constructor
type and domains, renamed (`renFrame`). Where the renaming is invisible to the reading
(`RenameOk`), the renamed frame reads as the public one; the block renaming is idempotent
(`blockRen_idem`), so renaming the renamed frame once more changes nothing. The conclusions
transport back through `openRev_renameConsts` and `denoteMeta_renameConsts`.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env md} {φ : LevelParam → Nat}

/-! ## Renaming commutes with the frame operations -/

/-- Renaming commutes with instantiating a telescope context at a spine. -/
theorem instSpine_renameConsts (f : Key md → Key md) :
    ∀ (args : List (Expr md)) (t : Nat) (e : Expr md),
      (Expr.instSpine args t e).renameConsts f
        = Expr.instSpine (args.map (·.renameConsts f)) t (e.renameConsts f) := by
  intro args
  induction args with
  | nil => intro t e; rfl
  | cons a as ih =>
    intro t e
    show (Expr.instSpine as (t - 1) (e.instantiate1 a t)).renameConsts f
      = Expr.instSpine (as.map (·.renameConsts f)) (t - 1)
          ((e.renameConsts f).instantiate1 (a.renameConsts f) t)
    rw [ih, Expr.renameConsts_instantiate1_gen]

/-- Renaming commutes with instantiating a `∀`-telescope at a spine. -/
theorem instPisAt_renameConsts (f : Key md → Key md) :
    ∀ (sp : List (Expr md)) {ty : Expr md} {ds : List (Expr md)} {r : Expr md},
      Expr.instPisAt sp ty = some (ds, r) →
      Expr.instPisAt (sp.map (·.renameConsts f)) (ty.renameConsts f)
        = some (ds.map (·.renameConsts f), r.renameConsts f) := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds r h
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a sp ih =>
    intro ty ds r h
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨ds', r'⟩ := p
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        have h2 := ih h1
        rw [Expr.renameConsts_instantiate1_gen] at h2
        show (Expr.instPisAt (sp.map (·.renameConsts f))
            ((body.renameConsts f).instantiate1 (a.renameConsts f))).map
              (fun x => (dom.renameConsts f :: x.1, x.2)) = _
        rw [h2]
        rfl

/-- The renamed pins at the renamed frame are the renamed pins at the frame. -/
theorem pinSpine_renameConsts (f : Key md → Key md) (fvsP pins : List (Expr md)) (rP : Nat) :
    (pins.map (·.renameConsts f)).map
        (Expr.instSpine ((fvsP.map (·.renameConsts f)).take rP) (rP - 1))
      = (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).map (·.renameConsts f) := by
  rw [List.map_map, List.map_map, ← List.map_take]
  refine List.map_congr_left (fun p _ => ?_)
  exact (instSpine_renameConsts f (fvsP.take rP) (rP - 1) p).symm

/-- A renamed list at an index below its length. -/
theorem getD_map_renameConsts (f : Key md → Key md) {l : List (Expr md)} {q : Nat}
    (hq : q < l.length) :
    (l.map (·.renameConsts f)).getD q default = (l.getD q default).renameConsts f := by
  rw [List.getD, List.getElem?_map, List.getD, List.getElem?_eq_getElem hq]
  rfl

/-! ## The renamed frame -/

/-- **The renamed frame's facts**, from the public frame's: the variables keep their indices
and shapes, their annotations read as before. -/
theorem renFrame {m : EnvModel V env} {f : Key md → Key md}
    (hro : RenameOk m.acval env f) {rP : Nat}
    {fvsP : List (Expr md)}
    (hshapeP : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr md),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {ΓP : List AnnotTerm}
    (hdomsP0 : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default)) :
    (∀ (i : Nat) (x : Expr md), (fvsP.map (·.renameConsts f))[i]? = some x →
      ∃ ty, x = Expr.fvar i ty) ∧
    (∀ x ∈ fvsP.map (·.renameConsts f), Expr.WScoped rP x) ∧
    (∀ l, (∃ x ∈ fvsP.map (·.renameConsts f), l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP.map (·.renameConsts f)) ∧
    (∀ (i : Nat) (ty : Expr md),
      Expr.fvar i ty ∈ fvsP.map (·.renameConsts f) → ty.looseBVarsBounded 0 = true) ∧
    (∀ (i : Nat) (x : Expr md), (fvsP.map (·.renameConsts f))[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    rw [List.getElem?_map] at hx
    rcases hy : fvsP[i]? with _ | y
    · rw [hy] at hx; exact nomatch hx
    · rw [hy] at hx
      obtain rfl := (Option.some.inj hx).symm
      obtain ⟨ty, rfl⟩ := hshapeP i y hy
      exact ⟨ty.renameConsts f, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact wscoped_renameConsts y (hwsFvsP y hy)
  · intro l ⟨x, hx, hl⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [fvarLeaves_renameConstsE] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    have h := hleafClosedP l₀ ⟨y, hy, hl₀⟩
    exact List.mem_map.mpr ⟨_, h, rfl⟩
  · intro i ty hmem
    obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hy
    obtain ⟨ty₀, rfl⟩ := hshapeP q y hq
    simp only [Expr.renameConsts, Expr.fvar.injEq] at hyeq
    obtain ⟨rfl, rfl⟩ := hyeq
    rw [Expr.looseBVarsBounded_renameConsts]
    exact hlbFvsP q ty₀ hy
  · intro i x hx
    rw [List.getElem?_map] at hx
    rcases hy : fvsP[i]? with _ | y
    · rw [hy] at hx; exact nomatch hx
    · rw [hy] at hx
      obtain rfl := (Option.some.inj hx).symm
      obtain ⟨ty, rfl⟩ := hshapeP i y hy
      have h := hdomsP0 i _ hy
      exact (denoteMeta_renameConsts hro ty i).trans h

/-! ## The two pin theorems, at the renamed frame -/

set_option maxHeartbeats 1600000 in
/-- **`nestedParamSupply` from the renamed pin typing**: the same conclusion, with the pins'
typing taken on the renamed pins against the renamed constructor's domains. -/
theorem nestedParamSupplyRen {m : EnvModel V env} {J : Judgements md}
    (hclaims : DefEqClaimJ J m φ)
    (hinfC : InferClaimJ J m φ)
    (hreads : InferReadsJ J m φ)
    (hframe : InferFrameJ J m φ)
    {f : Key md → Key md} (hro : RenameOk m.acval env f) (hidem : ∀ n, f (f n) = f n)
    {rP cnP cnF N : Nat} (hrPN : rP ≤ N)
    {fvs : List (Expr md)} (hfvslen : fvs.length = rP + cnF)
    {Γs : List AnnotTerm} (hΓslen : Γs.length = rP + cnF)
    {fvsP : List (Expr md)} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr md),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    {Δa : List AnnotTerm} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < N →
      Δa[(rP + cnF) - 1 - i]?
        = some (Γs.getD ((rP + cnF) - 1 - i) default))
    (hpre : ∀ n, n ≤ N → n < rP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (rP + cnF - n)))
          (ΓP.getD (rP - 1 - n) default) ∧
        interp V (fun j => ρ' (j + (rP + cnF - n)))
            (Γs.getD (rP + cnF - 1 - n) default)
          = interp V (fun j => ρ' (j + (rP + cnF - n)))
              (ΓP.getD (rP - 1 - n) default))
    {pins : List (Expr md)} (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {ctyP : Expr md} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm}
    (hTVjP : denoteMeta m.acval env φ (rP + cnF) ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    {psP : List (Expr md)}
    (hpsPdef : psP = pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
    {cdomsP : List (Expr md)} {crestP : Expr md}
    (hcinstP : Expr.instPisAt psP ctyP = some (cdomsP, crestP))
    (hTyped : TypedListJ J env (rP + cnF)
      (psP.map (·.renameConsts f)) (cdomsP.map (·.renameConsts f)))
    {sp : List (Expr md)} (hsplen : sp.length = cnP + cnF)
    (hspPar : ∀ q, q < cnP → sp[q]?
      = some (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)))
    {ctyR : Expr md} {cdoms : List (Expr md)} {cres : Expr md}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    (hrenCty : RenEqT f ctyP ctyR)
    (hpsRen : ∀ q, q < cnP →
      RenEqT f (Expr.instSpine (fvsP.take rP) (rP - 1)
          (pins.getD q default))
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)))
    (hpinRead : ∀ q, q < cnP → ∃ w,
      denoteMeta m.acval env φ (rP + cnF) (sp.getD q default) = some w) :
    ∀ q, q < cnP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      ∃ w, denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ (rP + cnF)
            (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
  subst hpsPdef
  obtain ⟨hshapeR, hwsR, hleafR, hlbR, hdomsR⟩ :=
    renFrame (φ := φ) hro hshapeP hwsFvsP hleafClosedP hlbFvsP hdomsP0
  have hlenR : pins.length = (pins.map (·.renameConsts f)).length := by
    rw [List.length_map]
  have hpinGet : ∀ q, q < cnP →
      (pins.map (·.renameConsts f)).getD q default
        = (pins.getD q default).renameConsts f :=
    fun q hq => getD_map_renameConsts f (by rw [hpinsLen]; exact hq)
  refine nestedParamSupply (m := m) hclaims hinfC hreads hframe hro hrPN hfvslen hΓslen
    (fvsP := fvsP.map (·.renameConsts f)) (by rw [List.length_map, hfvsPlen])
    hshapeR hwsR hleafR hlbR htowerP hokTV hdomsR hΔalen hΔaent hpre
    (pins := pins.map (·.renameConsts f)) (by rw [List.length_map, hpinsLen])
    (fun p hp => by
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
      exact ⟨(hasFvar_renameConsts f p₀).trans (hpinsWf p₀ hp₀).1,
        (Expr.looseBVarsBounded_renameConsts f p₀ rP).trans (hpinsWf p₀ hp₀).2⟩)
    (ctyP := ctyP.renameConsts f) ((hasFvar_renameConsts f ctyP).trans hCw)
    ((Expr.looseBVarsBounded_renameConsts f ctyP 0).trans hCb)
    ((denoteMeta_renameConsts hro ctyP (rP + cnF)).trans hTVjP) hokTVjP
    (psP := (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).map (·.renameConsts f))
    (pinSpine_renameConsts f fvsP pins rP).symm
    (instPisAt_renameConsts f _ hcinstP) hTyped hsplen
    (fun q hq => by rw [hpinGet q hq, renameConsts_idem hidem]; exact hspPar q hq)
    hcinst
    (by
      show Expr.ErasedEq ((ctyP.renameConsts f).renameConsts f) ctyR
      rw [renameConsts_idem hidem]
      exact hrenCty)
    (fun q hq => by
      rw [hpinGet q hq, renameConsts_idem hidem, ← List.map_take,
        ← instSpine_renameConsts]
      show Expr.ErasedEq (((Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD q default)).renameConsts f).renameConsts f) _
      rw [renameConsts_idem hidem]
      exact hpsRen q hq)
    hpinRead

set_option maxHeartbeats 1600000 in
/-- **`nestedPinRow` from the renamed pin typing**: `RecRuleLaw`'s pin conjunct at one index,
with the pins' typing taken on the renamed pins against the renamed constructor's domains. -/
theorem nestedPinRowRen {m : EnvModel V env} {J : Judgements md}
    (hclaims : DefEqClaimJ J m φ)
    (hinfC : InferClaimJ J m φ)
    (hreads : InferReadsJ J m φ)
    (hframe : InferFrameJ J m φ)
    {f : Key md → Key md} (hro : RenameOk m.acval env f)
    {rP cnF cnP : Nat}
    {fvsP : List (Expr md)} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr md),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr md), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    {pins : List (Expr md)} (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {ctyP : Expr md} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm}
    (hTVjP : denoteMeta m.acval env φ (rP + cnF) ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    {cdomsP : List (Expr md)} {crestP : Expr md}
    (hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) ctyP
      = some (cdomsP, crestP))
    (hTyped : TypedListJ J env (rP + cnF)
      ((pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).map (·.renameConsts f))
      (cdomsP.map (·.renameConsts f)))
    (hpinRead : ∀ q, q < cnP → ∃ w, denoteMeta m.acval env φ (rP + cnF)
      (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
      = some w) :
    ∀ q, q < cnP →
      ∃ vpa : AnnotTerm,
        denoteMeta m.acval env φ rP
          (openRev 0 rP (pins.getD q default)) = some vpa ∧
        ∀ (ρ : Nat → V) (zs : List AnnotTerm) (restR : AnnotTerm),
          zs.length = rP → (∀ z ∈ zs, WellDenotedV V ρ z) →
          TeleFitPA V ρ TV zs restR →
          WellDenotedV V ρ (AnnotTerm.instRevChain zs vpa) := by
  obtain ⟨hshapeR, hwsR, hleafR, hlbR, hdomsR⟩ :=
    renFrame (φ := φ) hro hshapeP hwsFvsP hleafClosedP hlbFvsP hdomsP0
  have hpinGet : ∀ q, q < cnP →
      (pins.map (·.renameConsts f)).getD q default
        = (pins.getD q default).renameConsts f :=
    fun q hq => getD_map_renameConsts f (by rw [hpinsLen]; exact hq)
  have hrow := nestedPinRow (m := m) (φ := φ) hclaims hinfC hreads hframe
    (fvsP := fvsP.map (·.renameConsts f)) (by rw [List.length_map, hfvsPlen])
    hshapeR hwsR hleafR hlbR htowerP hokTV hdomsR
    (pins := pins.map (·.renameConsts f)) (by rw [List.length_map, hpinsLen])
    (fun p hp => by
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
      exact ⟨(hasFvar_renameConsts f p₀).trans (hpinsWf p₀ hp₀).1,
        (Expr.looseBVarsBounded_renameConsts f p₀ rP).trans (hpinsWf p₀ hp₀).2⟩)
    (ctyP := ctyP.renameConsts f) ((hasFvar_renameConsts f ctyP).trans hCw)
    ((Expr.looseBVarsBounded_renameConsts f ctyP 0).trans hCb)
    ((denoteMeta_renameConsts hro ctyP (rP + cnF)).trans hTVjP) hokTVjP
    (by rw [pinSpine_renameConsts]; exact instPisAt_renameConsts f _ hcinstP)
    (by rw [pinSpine_renameConsts]; exact hTyped)
    (fun q hq => by
      obtain ⟨w, hw⟩ := hpinRead q hq
      refine ⟨w, ?_⟩
      rw [hpinGet q hq, ← List.map_take, ← instSpine_renameConsts,
        denoteMeta_renameConsts hro]
      exact hw)
  intro q hq
  obtain ⟨vpa, hvp, hgr⟩ := hrow q hq
  refine ⟨vpa, ?_, hgr⟩
  rw [hpinGet q hq, openRev_renameConsts, denoteMeta_renameConsts hro] at hvp
  exact hvp

end Ix.Kernel.Model
