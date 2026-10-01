module

public import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndPlainParam
import ConLeche.Verify.Denote.OpenRevDenote
public section

/-!
# The `.nested` fire's parameter supply (task #161, IND TIER part 8)

`plainParamSupply`'s sibling, and the stage part 7 declined to write
before its consumer existed.  `zipper`/`fieldGradeFire`/`point` all
take the constructor run's parameter positions abstractly (`hpar`,
`hspMem`); the `.plain` fire supplies them from the recursor frame's
own openers through `paramGradeFire`, and the `.nested` fire supplies
them from **the pins** — which are not openers at all, and which no
`DefEqListOk` row compares.

The row that types them is `IotaThmNR`'s `TypedListOk`
(`SetR/Decl.lean`, the second widening's other row), and its
conversion is the one place in the ind tier where `InferClaim`
does the work `DefEqClaim` does everywhere else:

```
   TypedListOk … pinsP cdomsP        (inferTypeCore pinsP_q = ok ty,
                                      isDefEqCore ty cdomsP_q = ok true)
     ⇒ InferReads                    ty reads
     ⇒ InferClaim                  pinsP_q graded, ty graded,
                                      ⟦pinsP_q⟧ ∈ˢ ⟦ty⟧
     ⇒ DefEqClaim (defEqAt_of_run) ⟦ty⟧ = ⟦cdomsP_q⟧
```

Three things are worth naming:

* **the ladder is still an induction, and for `paramGradeFire`'s
  reason**: the *b-side* grading (`WellDenotedV ρ' dw` for the run's `q`-th
  domain) is `instPisAt_doms_graded`, which walks the constructor
  type's tower past every earlier position and needs those positions'
  memberships.  What changes is where the membership at `q` comes
  from — the inference claim, not the frame's own `Sat` slot;
* **a run carries no reading** (part 4's lesson): the pins' readings
  are a *premise* here.  Their source is the checked statement's own
  major argument, which `IotaThmNR` pins to the pin application up to
  `ErasedEq` — the bottom reads them off `denoteMeta_mkAppN_inv` and
  hands them down;
* **the context is the recursor frame's** (`Δb`), exactly as in
  `paramGradeFire`: the pins mention only the public frame's openers,
  whose annotations are the *recursor* tower's domains, so the
  statement frame's context cannot guard their conversion.  The
  consumer transports into `Δb` on the prefix equalities, and that
  transport is `nestedParamSupply`, the wrapper below.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name isDefEqCore inferTypeCore
  DefEqListOk TypedListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The typed walk's run, at one index

`TypedListOk` is a pairwise run predicate, so — exactly as with
`defEqListOk_getD` — its conversion is an index lookup. -/

/-- The inference and comparison runs at one index of a recorded typed
walk. -/
theorem typedListOk_getD {F : Nat} {d : Nat} :
    ∀ {as bs : List Expr}, TypedListOk μ F env d as bs →
      ∀ i, i < as.length →
        ∃ ty, inferTypeCore μ env F d (as.getD i default) = .ok ty ∧
          isDefEqCore μ env F d ty (bs.getD i default) = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h i hi
    simp only [List.length_nil] at hi
    omega
  | cons a as ih =>
    intro bs h i hi
    match bs, h with
    | b :: bs, ⟨⟨ty, hty, hde⟩, hrest⟩ =>
      match i with
      | 0 => exact ⟨ty, hty, hde⟩
      | i + 1 =>
        have h1 := ih hrest i (by simpa using hi)
        exact h1

/-! ## The ladder, at the recursor frame -/

set_option maxHeartbeats 3200000 in
/-- **The pins' gradings and memberships, by position** —
`paramGradeFire`'s `.nested` twin, on the `TypedListOk` row.

At every `ρ'` satisfying the recursor-frame context, the `q`-th
instantiated pin reads to a *graded* annotation whose value inhabits
the constructor run's `q`-th parameter domain. -/
theorem nestedPinFire {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    (hinfC : InferClaim μ m φ F)
    (hreads : InferReads m μ φ F)
    {K rP cnP : Nat} (hrPK : rP ≤ K)
    -- the public (recursor) frame
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    -- the stored pins
    {pins : List Expr} (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    -- the constructor type at the public frame, and the pins' run
    {ctyP : Expr} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm} (hTVjP : denoteMeta m.acval env φ K ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) ctyP
      = some (cdomsP, crestP))
    (hTyped : TypedListOk μ F env K
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) cdomsP)
    -- the pins' readings (a run carries none; the statement's own
    -- major supplies them — see the module docstring)
    (hpinRead : ∀ q, q < cnP → ∃ w, denoteMeta m.acval env φ K
      (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
      = some w)
    -- the recursor-frame context
    {Δb : List AnnotTerm} (hΔblen : Δb.length = K)
    (hΔbent : ∀ i, i < rP →
      Δb[K - 1 - i]? = some (ΓP.getD (rP - 1 - i) default)) :
    ∀ q, q < cnP → ∀ ρ' : Nat → V, Sat V Δb ρ' →
      ∃ w, denoteMeta m.acval env φ K
          (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ K (cdomsP.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hpinsPlen :
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).length = cnP := by
    rw [List.length_map, hpinsLen]
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hbFvsP : ∀ x ∈ fvsP, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshapeP q x hq
    rfl
  have hwsFvsPK : ∀ x ∈ fvsP, Expr.WScoped K x :=
    fun x hx => (hwsFvsP x hx).mono (by omega)
  -- the pins, pointwise
  have hpgetd : ∀ q, q < cnP → pins[q]? = some (pins.getD q default) := by
    intro q hq
    rw [List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp
      omega
    · rfl
  have hpwd : ∀ q, q < cnP → (pins.getD q default).hasFvar = false ∧
      (pins.getD q default).looseBVarsBounded rP = true :=
    fun q hq => hpinsWf _ (List.mem_of_getElem? (hpgetd q hq))
  have hpinsPget : ∀ q, q < cnP →
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))[q]?
        = some (Expr.instSpine (fvsP.take rP) (rP - 1)
            (pins.getD q default)) := by
    intro q hq
    rw [List.getElem?_map, hpgetd q hq]
    rfl
  have hpinsPgetD : ∀ q, q < cnP →
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).getD q default
        = Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default) := by
    intro q hq
    rw [List.getD, hpinsPget q hq]
    rfl
  -- the openers' leaves stay in the frame, below `rP`
  have hopenerLeafP : ∀ (q0 : Nat) (a : Expr), (fvsP.take rP)[q0]? = some a →
      ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP ∧ l.1 < rP := by
    intro q0 a ha l hl
    have hq0lt : q0 < rP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [htkPlen] at this
      exact this
    rw [List.getElem?_take_of_lt hq0lt] at ha
    obtain ⟨ty, rfl⟩ := hshapeP q0 a ha
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨List.mem_of_getElem? ha, hq0lt⟩
    · have hwsty : Expr.WScoped q0 ty := by
        have h' := hwsFvsP _ (List.mem_of_getElem? ha)
        simp only [Expr.WScoped] at h'
        exact h'.2
      have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty l hl'
      refine ⟨hleafClosedP l ⟨_, List.mem_of_getElem? ha, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  -- the instantiated pins' syntactic frame
  have hpinWs : ∀ p ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      Expr.WScoped K p := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact (instSpine_WScoped (rP - 1)
      (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
      (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))).mono (by omega)
  have hpinB : ∀ p ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      p.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    have h := instSpine_closed (args := fvsP.take rP) (e := p)
      (fun x hx => hbFvsP x (List.mem_of_mem_take hx))
      (by rw [htkPlen]; exact (hpinsWf p hp).2)
    rwa [htkPlen] at h
  have hpinLeaf : ∀ p ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      ∀ l ∈ p.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP ∧ l.1 < rP := by
    intro a ha l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinsWf p hp).1] at hl'
      exact nomatch hl'
    · obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
      exact hopenerLeafP q0 x hq0 l hlx
  have hpinMem : ∀ q, q < cnP →
      Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default)
        ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)) := by
    intro q hq
    exact List.mem_of_getElem? (hpinsPget q hq)
  -- the constructor type's own frame
  have hfbCty : Expr.fvarsBelow K ctyP := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl
    exact nomatch hl
  have hcdlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [hpinsPlen] at h
    exact h
  have hcdMem : ∀ q, q < cnP → cdomsP.getD q default ∈ cdomsP := by
    intro q hq
    rw [List.getD]
    rcases hr : cdomsP[q]? with _ | r
    · rw [List.getElem?_eq_none_iff] at hr; omega
    · exact List.mem_of_getElem? hr
  have hwsCdAll : ∀ q, q < cnP → Expr.WScoped K (cdomsP.getD q default) := by
    intro q hq
    exact (instPisAt_WScoped (d := K) _ ctyP hcinstP
      (Expr.WScoped.of_not_hasFvar hCw) hpinWs).1 _ (hcdMem q hq)
  have hbCdAll : ∀ q, q < cnP →
      (cdomsP.getD q default).looseBVarsBounded 0 = true := by
    intro q hq
    exact (instPisAt_bounded _ hcinstP hCb hpinB).1 _ (hcdMem q hq)
  have hleafCdAll : ∀ q, q < cnP →
      ∀ l ∈ (cdomsP.getD q default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP ∧ l.1 < rP := by
    intro q hq l hl
    rcases instPisAt_leaves _ hcinstP l (Or.inl ⟨_, hcdMem q hq, hl⟩) with
      hty' | ⟨a, ha, hla⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at hty'
      exact nomatch hty'
    · exact hpinLeaf a ha l hla
  -- the tower's slots are graded by satisfaction alone
  have hokAll : ∀ i, i < rP → ∀ ρ0 : Nat → V, Sat V Δb ρ0 →
      WellDenotedV V (fun j => ρ0 (j + (K - 1 - i) + 1))
        (ΓP.getD (rP - 1 - i) default) := by
    intro i hi ρ0 hρ0
    have hbase : WellDenotedV V
        (fun j => (fun t => ρ0 (t + (K - rP))) (j + rP)) TV := by
      have h := hokTV (fun j => ρ0 (j + K))
      refine cast (by congr 1; funext j; congr 1; omega) h
    refine cast ?_ (wellDenotedV_tower_slot rP htowerP
      (ρ' := fun t => ρ0 (t + (K - rP))) hbase (rP - 1 - i) (by omega)
      (fun q hq1 hq2 => ?_))
    · congr 1
      funext j
      show ρ0 (j + (rP - 1 - i) + 1 + (K - rP)) = ρ0 (j + (K - 1 - i) + 1)
      congr 1
      omega
    · have hsatm := hρ0 (K - 1 - (rP - 1 - q))
        (ΓP.getD (rP - 1 - (rP - 1 - q)) default)
        (hΔbent (rP - 1 - q) (by omega))
      show (fun t => ρ0 (t + (K - rP))) q ∈ˢ _
      rw [show (fun t => ρ0 (t + (K - rP))) q
          = ρ0 (K - 1 - (rP - 1 - q)) from by
          show ρ0 (q + (K - rP)) = _
          congr 1
          omega,
        show (fun j => (fun t => ρ0 (t + (K - rP))) (j + q + 1))
          = (fun j => ρ0 (j + (K - 1 - (rP - 1 - q)) + 1)) from by
          funext j
          show ρ0 (j + q + 1 + (K - rP)) = _
          congr 1
          omega,
        show ΓP.getD q default
          = ΓP.getD (rP - 1 - (rP - 1 - q)) default from by
          congr 1
          omega]
      exact hsatm
  -- a pin's context correspondence
  have hctxPin : ∀ q, q < cnP →
      CtxOk m φ K Δb
        (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default)) := by
    intro q hq
    exact ctxOk_of_openers m.acval_closed hΔblen hshapeP hwsFvsPK hdomsP0
      (fun l hl => (hpinLeaf _ (hpinMem q hq) l hl).1)
      (fun l hl => (hpinLeaf _ (hpinMem q hq) l hl).2) hΔbent hokAll
  -- the strong induction on the parameter position
  intro q
  induction q using Nat.strongRecOn with
  | _ q ihq =>
  intro hq
  obtain ⟨w, hw⟩ := hpinRead q hq
  -- the typed row at this index
  obtain ⟨ty, hInf, hDeq⟩ := typedListOk_getD hTyped q (by
    rw [hpinsPlen]; exact hq)
  rw [hpinsPgetD q hq] at hInf
  -- the inferred type's reading (the totality residue)
  obtain ⟨ta, hta⟩ := hreads hInf (hpinWs _ (hpinMem q hq))
    (hpinB _ (hpinMem q hq))
    (fun l hl => hlbFvsP l.1 l.2 (hpinLeaf _ (hpinMem q hq) l hl).1)
    (hctxPin q hq) hw
  -- the inference claim: the pin is graded and inhabits its type
  obtain ⟨hgw, hgta, hmem⟩ := hinfC hInf (hpinWs _ (hpinMem q hq))
    (hpinB _ (hpinMem q hq))
    (fun l hl => hlbFvsP l.1 l.2 (hpinLeaf _ (hpinMem q hq) l hl).1)
    (hctxPin q hq) hw hta
  -- the inferred type's syntactic frame (a run's tax, part 4's lesson)
  have hwsTy : Expr.WScoped K ty :=
    inferTypeCore_WScoped m.wf F hInf (hpinWs _ (hpinMem q hq))
  have hleafTy : ∀ l ∈ ty.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsP ∧ l.1 < rP := fun l hl =>
    hpinLeaf _ (hpinMem q hq) l
      (inferTypeCore_fvarLeaves m.wf F hInf
        (hpinWs _ (hpinMem q hq)) l hl)
  have hbTy : ty.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf F hInf (hpinWs _ (hpinMem q hq))
      (hpinB _ (hpinMem q hq))
      (fun l hl => hlbFvsP l.1 l.2
        (hpinLeaf _ (hpinMem q hq) l hl).1)
  intro ρ' hsat
  refine ⟨w, hw, hgw ρ' hsat, ?_⟩
  intro dw hdw
  -- the b-side grading: the constructor tower, past the earlier pins
  have hgdw : ∀ ρ0 : Nat → V, Sat V Δb ρ0 → WellDenotedV V ρ0 dw := by
    intro ρ0 hρ0
    refine instPisAt_doms_graded (ρ' := ρ0) m.acval_closed
      (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
        (fun k' => m.acval_closed n ψ k') y k)
      _ hcinstP q (fun i₀ x _ hx => ⟨hpinWs x (List.mem_of_getElem? hx),
        hpinB x (List.mem_of_getElem? hx)⟩)
      hfbCty hCb hTVjP (hokTVjP _) ?_
      (by rw [hpinsPlen]; exact hq) dw hdw
    intro i₀ x hlt hx
    obtain rfl : x = Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD i₀ default) := by
      have h := hpinsPget i₀ (by omega)
      rw [h] at hx
      exact (Option.some.inj hx).symm
    exact ihq i₀ hlt (by omega) ρ0 hρ0
  -- the comparison fires: the inferred type reads to the domain
  have hfire := defEqAt_of_run (m := m) hclaims (k := K) (fvs := fvsP)
    (Aa := fun i => ΓP.getD (rP - 1 - i) default) (Δa := Δb) hΔblen
    hshapeP hwsFvsPK hdomsP0 (n := rP) hΔbent hokAll hDeq hwsTy hbTy
    (fun l hl => hlbFvsP l.1 l.2 (hleafTy l hl).1)
    (hwsCdAll q hq) (hbCdAll q hq)
    (fun l hl => hlbFvsP l.1 l.2 (hleafCdAll q hq l hl).1)
    (fun l hl => (hleafTy l hl).1) (fun l hl => (hleafTy l hl).2)
    (fun l hl => (hleafCdAll q hq l hl).1)
    (fun l hl => (hleafCdAll q hq l hl).2)
    hta hdw hgta hgdw hsat
  rw [← hfire]
  exact hmem ρ' hsat

/-! ## The supply, at the statement frame -/

set_option maxHeartbeats 3200000 in
/-- **The `.nested` rule's parameter positions, supplied** — exactly
`zipper`/`fieldGradeFire`'s `hpar`, and `plainParamSupply`'s mirror.

The three moves are the plain supply's, with the ladder replaced:
the context swap onto the recursor frame (`Δb`, on the prefix
equalities), `nestedPinFire` there, and the renaming bridge back —
which here carries the *subjects* too, since the statement frame's
pins are the public frame's renamed. -/
theorem nestedParamSupply {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    (hinfC : InferClaim μ m φ F)
    (hreads : InferReads m μ φ F)
    {f : Name → Name} (hro : RenameOk m.acval env f)
    {rP cnP cnF N : Nat} (hrPN : rP ≤ N)
    -- the statement frame
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    {Γs : List AnnotTerm} (hΓslen : Γs.length = rP + cnF)
    -- the public (recursor) frame and its tower
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    -- the ambient (statement-frame) context
    {Δa : List AnnotTerm} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < N →
      Δa[(rP + cnF) - 1 - i]?
        = some (Γs.getD ((rP + cnF) - 1 - i) default))
    -- the prefix positions, already fired (`prefixGradeFire`)
    (hpre : ∀ n, n ≤ N → n < rP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (rP + cnF - n)))
          (ΓP.getD (rP - 1 - n) default) ∧
        interp V (fun j => ρ' (j + (rP + cnF - n)))
            (Γs.getD (rP + cnF - 1 - n) default)
          = interp V (fun j => ρ' (j + (rP + cnF - n)))
              (ΓP.getD (rP - 1 - n) default))
    -- the stored pins and the constructor type at the public frame
    {pins : List Expr} (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {ctyP : Expr} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm}
    (hTVjP : denoteMeta m.acval env φ (rP + cnF) ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    -- the public frame's pin spine, named (the bottom keeps it atomic;
    -- see `indBottomNested`'s note on term size)
    {psP : List Expr}
    (hpsPdef : psP = pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt psP ctyP = some (cdomsP, crestP))
    (hTyped : TypedListOk μ F env (rP + cnF) psP cdomsP)
    -- the statement-frame run, whose parameter spine is the renamed pins
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspPar : ∀ q, q < cnP → sp[q]?
      = some (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f))
    )
    {ctyR : Expr} {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    (hrenCty : RenEqT f ctyP ctyR)
    -- the two frames' pin spines are renaming-equal
    (hpsRen : ∀ q, q < cnP →
      RenEqT f (Expr.instSpine (fvsP.take rP) (rP - 1)
          (pins.getD q default))
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)))
    -- the pins' readings, at the statement frame (the bottom's own)
    (hpinRead : ∀ q, q < cnP → ∃ w,
      denoteMeta m.acval env φ (rP + cnF) (sp.getD q default) = some w) :
    ∀ q, q < cnP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      ∃ w, denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ (rP + cnF)
            (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
  subst hpsPdef
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hspgetD : ∀ q, q < cnP → sp.getD q default
      = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f) := by
    intro q hq
    rw [List.getD, hspPar q hq]
    rfl
  -- the subjects' readings are the public frame's, across the renaming
  have hsubj : ∀ q, q < cnP →
      denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
        = denoteMeta m.acval env φ (rP + cnF)
            (Expr.instSpine (fvsP.take rP) (rP - 1)
              (pins.getD q default)) := by
    intro q hq
    rw [hspgetD q hq]
    exact RenEqT.denoteMeta hro (hpsRen q hq) (rP + cnF)
  -- the recursor-frame context: the ambient context's low half with
  -- the recursor tower on top (`K - rP = cnF`)
  have hΔblen : (Δa.take cnF ++ ΓP).length = rP + cnF := by
    rw [List.length_append, List.length_take, hΓPlen, hΔalen]
    omega
  have hΔblow : ∀ q, q < cnF → (Δa.take cnF ++ ΓP)[q]? = Δa[q]? := by
    intro q hq
    rw [List.getElem?_append_left
      (by rw [List.length_take, hΔalen]; omega),
      List.getElem?_take_of_lt hq]
  have hΔbent : ∀ i, i < rP →
      (Δa.take cnF ++ ΓP)[(rP + cnF) - 1 - i]?
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
      (by rw [List.length_take, hΔalen]; omega),
      List.length_take, hΔalen,
      show (rP + cnF) - 1 - i - min cnF (rP + cnF) = rP - 1 - i from by
        omega,
      List.getD]
    rcases hg : ΓP[rP - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  -- satisfaction transports, on the prefix equalities
  have hsatB : ∀ ρ' : Nat → V, Sat V Δa ρ' →
      Sat V (Δa.take cnF ++ ΓP) ρ' := by
    intro ρ' hsat i Ai hi
    have hiK : i < rP + cnF := by
      rcases Nat.lt_or_ge i (rP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hi
        exact nomatch hi
    rcases Nat.lt_or_ge i cnF with hic | hic
    · exact hsat i Ai (by rw [← hΔblow i hic]; exact hi)
    · have hp : (rP + cnF) - 1 - ((rP + cnF) - 1 - i) = i := by omega
      have hplt : (rP + cnF) - 1 - i < rP := by omega
      obtain rfl : Ai = ΓP.getD (rP - 1 - ((rP + cnF) - 1 - i)) default := by
        have h := hΔbent ((rP + cnF) - 1 - i) hplt
        rw [hp] at h
        rw [h] at hi
        exact (Option.some.inj hi).symm
      have hsatA := hsat i (Γs.getD i default) (by
        have h := hΔaent ((rP + cnF) - 1 - i) (by omega)
        rw [hp] at h
        exact h)
      have heq := (hpre ((rP + cnF) - 1 - i) (by omega) hplt ρ' hsat).2
      rw [hp] at heq
      rw [show (fun j => ρ' (j + i + 1))
          = (fun j => ρ' (j + ((rP + cnF) - ((rP + cnF) - 1 - i)))) from by
        funext j; congr 1; omega] at hsatA ⊢
      rw [← heq]
      exact hsatA
  -- the ladder at the recursor frame
  have hladder := nestedPinFire (m := m) hclaims hinfC hreads
    (K := rP + cnF) (by omega) hfvsPlen hshapeP hwsFvsP hleafClosedP
    hlbFvsP htowerP hokTV hdomsP0 hpinsLen hpinsWf hCw hCb hTVjP hokTVjP
    hcinstP hTyped
    (fun q hq => by
      obtain ⟨w, hw⟩ := hpinRead q hq
      exact ⟨w, by rw [← hsubj q hq]; exact hw⟩)
    hΔblen hΔbent
  -- the renaming bridge between the two runs' domains
  obtain ⟨mid, htake, -⟩ := instPisAt_take sp cnP hcinst
  have hcdlen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    omega
  have hcdPlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [List.length_map, hpinsLen] at h
    exact h
  have hbridge : ∀ q, q < cnP →
      denoteMeta m.acval env φ (rP + cnF) (cdoms.getD q default)
        = denoteMeta m.acval env φ (rP + cnF) (cdomsP.getD q default) := by
    intro q hq
    have hargs : ∀ (i : Nat) (a a' : Expr),
        (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))[i]? = some a →
        (sp.take cnP)[i]? = some a' → RenEqT f a a' := by
      intro i a a' ha ha'
      have hi : i < cnP := by
        rcases Nat.lt_or_ge i cnP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none
            (by rw [List.length_map, hpinsLen]; omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hi, hspPar i hi] at ha'
      obtain rfl : a' = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD i default).renameConsts f) :=
        (Option.some.inj ha').symm
      rw [List.getElem?_map] at ha
      rcases hp : pins[i]? with _ | p
      · rw [List.getElem?_eq_none_iff, hpinsLen] at hp; omega
      rw [hp] at ha
      obtain rfl : a = Expr.instSpine (fvsP.take rP) (rP - 1) p :=
        (Option.some.inj ha).symm
      obtain rfl : p = pins.getD i default := by
        rw [List.getD, hp]
        rfl
      exact hpsRen i hi
    have hlen : (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).length
        = (sp.take cnP).length := by
      rw [List.length_map, List.length_take, hpinsLen, hsplen]
      omega
    obtain ⟨hds, -⟩ := instPisAt_renEq (f := f)
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
      (sp.take cnP) hcinstP htake hrenCty hargs hlen
    rcases hxP : cdomsP[q]? with _ | xP
    · rw [List.getElem?_eq_none_iff] at hxP; omega
    rcases hxR : (cdoms.take cnP)[q]? with _ | xR
    · rw [List.getElem?_take_of_lt hq, List.getElem?_eq_none_iff] at hxR
      omega
    have hrq := hds q xP xR hxP hxR
    rw [List.getElem?_take_of_lt hq] at hxR
    rw [List.getD, hxR, List.getD, hxP]
    exact RenEqT.denoteMeta hro hrq (rP + cnF)
  -- assemble
  intro q hq ρ' hsat
  obtain ⟨w, hw, hgw, hmem⟩ := hladder q hq ρ' (hsatB ρ' hsat)
  refine ⟨w, by rw [hsubj q hq]; exact hw, hgw, ?_⟩
  intro dw hdw
  rw [hbridge q hq] at hdw
  exact hmem dw hdw

end ConLeche.Model
