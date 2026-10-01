module

public import ConLeche.Model.NatWf
import ConLeche.Semantics.DivModEval
import ConLeche.Model.Annot.BitInst
public section

/-!
# The WF-recursive operations' clauses, established at `interp` from
the pin certificates (task #161, literal tier — the divmod leg, part 3)

`DivModPin.lean` extracts `DivModV`'s clauses from the checker's
`checkDivModCerts` verdict at the collapse currency.  This file is its
mirror at the validated-annotation currency, and the shape is the one
`NatEqsP.lean` established for the structural recurrences:
**establishment from run certificates**.  The certificate's three runs
(`annotateCore`/`inferTypeCore`/`isDefEqCore` at depth 4, unpacked by
the currency-free `checkDivModCerts_inv`) are converted by
`InferClaim`/`DefEqClaim` at the pre-insertion environment into
"the statement's interpretation is inhabited", and the pinned `Eq`
law turns inhabited into equal.

Everything `V`-free in `DivModPin.lean` is reused as it stands
(`dmFragOk`, `dmEvalV`, `dmLeavesOk` and its lemmas,
`fvarLeaves_substConst0`, `divModCertApplied_mem1`/`2`, the applied
forms' frame lemmas, the pinned-type inversions).  What is genuinely
new here is the **grading**: `CtxOk`, `InferClaim` and
`DefEqClaim` all demand `WellDenotedV` of what they compare, and
`CtxOkR` demanded nothing of the sort.  So the statements' fragment
gets a graded walk (`dmNatFrag_graded`), built the way `NatEqsP.lean`'s
`NatArg` walk is: argument memberships from the frame, head
memberships from `mem_type` at the pinned types, and the fibre facts
at *unknown* regime bits from `type_wellDenotedV`'s `AnnotValid` — so no bit
positivity is taken anywhere.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## Value-level head packages

What a fragment application rule needs of a head, at the value level:
a membership in a one- or two-step `piR` over the frame's `Nat`, with
`app_mem_piR`'s fibre premise at each step.  The bits are whatever the
stored annotation carries. -/

/-- A binary head over the frame's `Nat`, with codomain set `codS`. -/
def DmBinV (natS codS f : V) : Prop :=
  ∃ b₁ b₂ : Nat,
    f ∈ˢ piR b₁ natS (fun _ => piR b₂ natS (fun _ => codS)) ∧
    (b₁ = 0 → ∀ x, x ∈ˢ natS →
      piR b₂ natS (fun _ => codS) ∈ˢ (univZero : V)) ∧
    (b₂ = 0 → ∀ x, x ∈ˢ natS → codS ∈ˢ (univZero : V))

/-- A unary head over the frame's `Nat`. -/
def DmUnV (natS codS f : V) : Prop :=
  ∃ b₁ : Nat, f ∈ˢ piR b₁ natS (fun _ => codS) ∧
    (b₁ = 0 → ∀ x, x ∈ˢ natS → codS ∈ˢ (univZero : V))

/-- The binary rule, at the value level. -/
theorem DmBinV.app {natS codS f x y : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) (hy : y ∈ˢ natS) :
    SetTheory.app (SetTheory.app f x) y ∈ˢ codS := by
  obtain ⟨b₁, b₂, hm, hB1, hB2⟩ := h
  have hinner : SetTheory.app f x ∈ˢ piR b₂ natS (fun _ => codS) :=
    app_mem_piR hm hx hB1
  exact app_mem_piR hinner hy hB2

/-- The unary rule. -/
theorem DmUnV.app {natS codS f x : V} (h : DmUnV natS codS f)
    (hx : x ∈ˢ natS) : SetTheory.app f x ∈ˢ codS := by
  obtain ⟨b₁, hm, hB1⟩ := h
  exact app_mem_piR hm hx hB1

/-- The `WellDenoted` witness a binary head's first application needs. -/
theorem DmBinV.ok1 {natS codS f x : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) {ρ : Nat → V} {fa xa : AnnotTerm}
    (hfa : WellDenoted V ρ fa) (hxa : WellDenoted V ρ xa)
    (hf : interp V ρ fa = f) (hxv : interp V ρ xa = x) :
    WellDenoted V ρ (.app fa xa) := by
  obtain ⟨b₁, b₂, hm, hB1, -⟩ := h
  rw [WellDenoted_app]
  exact ⟨hfa, hxa, b₁, natS, fun _ => piR b₂ natS (fun _ => codS),
    by rw [hf]; exact hm, by rw [hxv]; exact hx, hB1⟩

/-- …and its second. -/
theorem DmBinV.wellDenoted {natS codS f x y : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) (hy : y ∈ˢ natS) {ρ : Nat → V}
    {fa xa ya : AnnotTerm}
    (hfa : WellDenoted V ρ fa) (hxa : WellDenoted V ρ xa)
    (hya : WellDenoted V ρ ya)
    (hf : interp V ρ fa = f) (hxv : interp V ρ xa = x)
    (hyv : interp V ρ ya = y) :
    WellDenoted V ρ (.app (.app fa xa) ya) := by
  have hok1 := DmBinV.ok1 h hx hfa hxa hf hxv
  obtain ⟨b₁, b₂, hm, hB1, hB2⟩ := h
  rw [WellDenoted_app]
  refine ⟨hok1, hya, b₂, natS, fun _ => codS, ?_,
    by rw [hyv]; exact hy, hB2⟩
  rw [interp_app, hf, hxv]
  have hinner : SetTheory.app f x ∈ˢ piR b₂ natS (fun _ => codS) :=
    app_mem_piR hm hx hB1
  exact hinner

/-- The unary head's `WellDenoted` witness. -/
theorem DmUnV.ok1 {natS codS f x : V} (h : DmUnV natS codS f)
    (hx : x ∈ˢ natS) {ρ : Nat → V} {fa xa : AnnotTerm}
    (hfa : WellDenoted V ρ fa) (hxa : WellDenoted V ρ xa)
    (hf : interp V ρ fa = f) (hxv : interp V ρ xa = x) :
    WellDenoted V ρ (.app fa xa) := by
  obtain ⟨b₁, hm, hB1⟩ := h
  rw [WellDenoted_app]
  exact ⟨hfa, hxa, b₁, natS, fun _ => codS, by rw [hf]; exact hm,
    by rw [hxv]; exact hx, hB1⟩

/-! ## The head packages, from the environment invariant

`mem_type` at a pinned operation type gives the membership;
`type_wellDenotedV`'s `AnnotValid` gives the fibre facts.  (These are
`NatEqsP.lean`'s `natBinHead_of_stored`/`natUnHead_of_stored` with
the two-variable context stripped off — the certificate frame is a
different context, and the packages never read one.) -/

/-- **A binary head, from its parts**: a membership in the two-step
pinned product's reading, and that reading's own grading (which is
where the fibre facts at the unknown regime bits come from). -/
theorem dmBinV_of_parts (m : EnvModel V env) {ψ : Name → Nat}
    {b₁ b₂ : Nat} {codN : Name} {fa : AnnotTerm} {ρ : Nat → V}
    (hmem : interp V ρ fa ∈ˢ interp V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ)
        (.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ)))
        : AnnotTerm))
    (htok : WellDenotedV V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ)
        (.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ)))
        : AnnotTerm)) :
    DmBinV (interp V ρ (m.acval ConLeche.natName ψ))
      (interp V ρ (m.acval codN ψ)) (interp V ρ fa) := by
  have hfib : interp V (cons (interp V ρ fa) ρ)
        ((.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
          : AnnotTerm)
      = piR b₂ (interp V ρ (m.acval ConLeche.natName ψ))
          (fun _ => interp V ρ (m.acval codN ψ)) := by
    rw [interp_pi]
    congr 1
    · exact acval_interp_closedC m _ ψ _ ρ
    · funext y
      exact acval_interp_closedC m _ ψ _ ρ
  refine ⟨b₁, b₂, ?_, ?_, ?_⟩
  · rw [interp_pi] at hmem
    rw [show (fun x => interp V (cons x ρ)
          ((.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
            : AnnotTerm))
        = fun _ => piR b₂ (interp V ρ (m.acval ConLeche.natName ψ))
            (fun _ => interp V ρ (m.acval codN ψ)) from by
      funext x
      rw [interp_pi]
      congr 1
      · exact acval_interp_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp_closedC m _ ψ _ ρ] at hmem
    exact hmem
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValid_pi] at hv
    have h := hv.2.2 hz x hx
    rw [show interp V (cons x ρ)
          ((.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
            : AnnotTerm)
        = piR b₂ (interp V ρ (m.acval ConLeche.natName ψ))
            (fun _ => interp V ρ (m.acval codN ψ)) from by
      rw [interp_pi]
      congr 1
      · exact acval_interp_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp_closedC m _ ψ _ ρ] at h
    exact h
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValid_pi] at hv
    have hinner := hv.2.1 x hx
    rw [AnnotValid_pi] at hinner
    have h := hinner.2.2 hz x
      (by rw [acval_interp_closedC m _ ψ (cons x ρ) ρ]; exact hx)
    rwa [acval_interp_closedC m _ ψ _ ρ] at h

/-- **A unary head, from its parts.** -/
theorem dmUnV_of_parts (m : EnvModel V env) {ψ : Name → Nat}
    {b₁ : Nat} {codN : Name} {fa : AnnotTerm} {ρ : Nat → V}
    (hmem : interp V ρ fa ∈ˢ interp V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
        : AnnotTerm))
    (htok : WellDenotedV V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
        : AnnotTerm)) :
    DmUnV (interp V ρ (m.acval ConLeche.natName ψ))
      (interp V ρ (m.acval codN ψ)) (interp V ρ fa) := by
  refine ⟨b₁, ?_, ?_⟩
  · rw [interp_pi] at hmem
    rw [show (fun x => interp V (cons x ρ) (m.acval codN ψ))
        = fun _ => interp V ρ (m.acval codN ψ) from by
      funext x
      exact acval_interp_closedC m _ ψ _ ρ] at hmem
    exact hmem
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValid_pi] at hv
    have h := hv.2.2 hz x hx
    rwa [acval_interp_closedC m _ ψ _ ρ] at h

/-- **A stored pinned binary head, at the value level.** -/
theorem dmBinV_of_stored (mp : EnvModelM V μ env) (ψ : Name → Nat)
    {o : Name} {cio : ConstantInfo}
    (hf : env.find? o = some cio)
    {mb₁ mb₂ : ConLeche.BinderMeta} {codN : Name}
    (hty : cio.toConstantVal.type
      = .forallE (.const ConLeche.natName [])
      (.forallE (.const ConLeche.natName []) (.const codN []) mb₂)
      mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = [])
    (ρ : Nat → V) :
    DmBinV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (mp.base2.acval codN ψ))
      (interp V ρ (mp.base2.acval o ψ)) := by
  have hmemE := ConLeche.Semantics.Env.find?_mem hf
  have hnm : cio.name = o := ConLeche.Semantics.Env.find?_name hf
  have hta : denoteMeta mp.base2.acval env ψ 0 cio.toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval ConLeche.natName ψ)
          (.pi 0 (pwBit ψ mb₂.pw) (mp.base2.acval ConLeche.natName ψ)
            (mp.base2.acval codN ψ))) := by
    rw [hty]
    exact denoteMeta_pinnedBinTy mp.base2 ψ hfN hlpN hcodF hcodLp
  have hmem := mp.mem_type _ hmemE ψ _ hta ρ
  rw [hnm] at hmem
  exact dmBinV_of_parts mp.base2 hmem (mp.type_wellDenotedV _ hmemE ψ _ hta ρ)

/-- **A stored pinned unary head, at the value level.** -/
theorem dmUnV_of_stored (mp : EnvModelM V μ env) (ψ : Name → Nat)
    {o : Name} {cio : ConstantInfo}
    (hf : env.find? o = some cio)
    {mb₁ : ConLeche.BinderMeta} {codN : Name}
    (hty : cio.toConstantVal.type
      = .forallE (.const ConLeche.natName []) (.const codN []) mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = [])
    (ρ : Nat → V) :
    DmUnV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (mp.base2.acval codN ψ))
      (interp V ρ (mp.base2.acval o ψ)) := by
  have hmemE := ConLeche.Semantics.Env.find?_mem hf
  have hnm : cio.name = o := ConLeche.Semantics.Env.find?_name hf
  have hta : denoteMeta mp.base2.acval env ψ 0 cio.toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval ConLeche.natName ψ)
          (mp.base2.acval codN ψ)) := by
    rw [hty, denoteMeta_forallE, denoteMeta_levelless_const hfN hlpN]
    rw [show (Expr.const codN ([] : List ConLeche.Level)).instantiate1
          (.fvar 0 (.const ConLeche.natName []))
        = Expr.const codN [] from ConLeche.Expr.instantiate1_eq_self
        (by simp [ConLeche.Expr.looseBVarsBounded])]
    rw [denoteMeta_levelless_const hcodF hcodLp]
    rfl
  have hmem := mp.mem_type _ hmemE ψ _ hta ρ
  rw [hnm] at hmem
  exact dmUnV_of_parts mp.base2 hmem (mp.type_wellDenotedV _ hmemE ψ _ hta ρ)

/-! ## The statements' `Nat`-valued fragment, and its graded walk

`dmFragOk` (v1) is the loose grammar: it does not record which heads
are unary and which binary, because v1 never needs to *type* a
subterm.  The P side does — a grading is a typing derivation — so the
walk below runs on the tighter grammar `dmNatFrag`, which is what the
certificate statements' `Nat`-valued sides actually are: the two frame
variables, `Nat.zero`, and saturated applications of the listed
unary/binary heads.  Membership of a concrete statement side in this
grammar is `by decide`. -/

/-- The `Nat`-valued statement fragment. -/
def dmNatFrag (bins uns : List Name) : Expr → Bool
  | .app (.app (.const n us) a) b =>
      bins.contains n && us.isEmpty &&
        dmNatFrag bins uns a && dmNatFrag bins uns b
  | .app (.const n us) a =>
      uns.contains n && us.isEmpty && dmNatFrag bins uns a
  | .const n us => (n == ConLeche.natZeroName) && us.isEmpty
  | .fvar i ty =>
      ((i == 0) || (i == 1)) &&
        ty == Expr.const ConLeche.natName []
  | _ => false

/-- **The graded walk.**  A `Nat`-valued statement fragment reads, and
at every valuation putting the two frame variables in the frame's
`Nat` its reading is graded, its value is in `Nat`, and that value is
the `dmEvalV` chain `DivModClausesV` is written in.

The valuation is quantified *inside* the reading, because the P claims
grade at every valuation satisfying the telescope, not at one. -/
theorem dmNatFrag_graded {m : EnvModel V env} {ψ : Name → Nat}
    {c : Name} {A : (Name → Nat) → AnnotTerm} {value' : Expr}
    {bins uns : List Name} {d : Nat} {natS : V}
    (hread : ∀ n ∈ ConLeche.natZeroName :: (bins ++ uns), ∀ d' : Nat,
      denoteMeta m.acval env ψ d' (Expr.substConst0 c value' (.const n []))
        = some (acvalWith m.acval c A n ψ))
    (hleafOk : ∀ (n : Name) (ρ : Nat → V),
      WellDenotedV V ρ (acvalWith m.acval c A n ψ))
    (hbin : ∀ n ∈ bins, ∀ ρ : Nat → V,
      DmBinV natS natS (interp V ρ (acvalWith m.acval c A n ψ)))
    (hun : ∀ n ∈ uns, ∀ ρ : Nat → V,
      DmUnV natS natS (interp V ρ (acvalWith m.acval c A n ψ)))
    (hzero : ∀ ρ : Nat → V,
      interp V ρ (acvalWith m.acval c A ConLeche.natZeroName ψ) ∈ˢ natS) :
    ∀ e : Expr, dmNatFrag bins uns e = true →
      ∃ ea, denoteMeta m.acval env ψ d
          (Expr.substConst0 c value' e) = some ea ∧
        ∀ ρ : Nat → V, ρ (d - 1 - 0) ∈ˢ natS → ρ (d - 1 - 1) ∈ˢ natS →
          WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ natS ∧
          interp V ρ ea = dmEvalV V
            (fun n => interp V ρ (acvalWith m.acval c A n ψ))
            (ρ (d - 1 - 0)) (ρ (d - 1 - 1)) e
  | .app (.app (.const n us) a) b, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hn, rfl⟩, ha⟩, hb⟩ := h
    have hnm : n ∈ bins := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hfa⟩ := dmNatFrag_graded hread hleafOk hbin hun hzero a ha
    obtain ⟨ba, hdb, hfb⟩ := dmNatFrag_graded hread hleafOk hbin hun hzero b hb
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (.app (acvalWith m.acval c A n ψ) aa) ba, ?_,
      fun ρ hx hy => ?_⟩
    · show denoteMeta m.acval env ψ d
        (.app (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) (Expr.substConst0 c value' b))
        = _
      rw [denoteMeta_app, denoteMeta_app, hdn, hda, hdb]
      rfl
    · obtain ⟨hoka, hma, hea⟩ := hfa ρ hx hy
      obtain ⟨hokb, hmb, heb⟩ := hfb ρ hx hy
      refine ⟨⟨DmBinV.wellDenoted (hbin n hnm ρ) hma hmb (hleafOk n ρ).1
          hoka.1 hokb.1 rfl rfl rfl,
          by rw [AnnotValid_app, AnnotValid_app]
             exact ⟨⟨(hleafOk n ρ).2, hoka.2⟩, hokb.2⟩⟩, ?_, ?_⟩
      · rw [interp_app, interp_app]
        exact DmBinV.app (hbin n hnm ρ) hma hmb
      · rw [interp_app, interp_app, hea, heb]
        rfl
  | .app (.const n us) a, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨hn, rfl⟩, ha⟩ := h
    have hnm : n ∈ uns := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hfa⟩ := dmNatFrag_graded hread hleafOk hbin hun hzero a ha
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (acvalWith m.acval c A n ψ) aa, ?_, fun ρ hx hy => ?_⟩
    · show denoteMeta m.acval env ψ d
        (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) = _
      rw [denoteMeta_app, hdn, hda]
      rfl
    · obtain ⟨hoka, hma, hea⟩ := hfa ρ hx hy
      refine ⟨⟨DmUnV.ok1 (hun n hnm ρ) hma (hleafOk n ρ).1 hoka.1 rfl
          rfl,
          by rw [AnnotValid_app]; exact ⟨(hleafOk n ρ).2, hoka.2⟩⟩,
        ?_, ?_⟩
      · rw [interp_app]
        exact DmUnV.app (hun n hnm ρ) hma
      · rw [interp_app, hea]
        rfl
  | .const n us, h => by
    simp only [dmNatFrag, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, hread _ (by simp) d,
      fun ρ _ _ => ⟨hleafOk _ ρ, hzero ρ, rfl⟩⟩
  | .fvar i ty, h => by
    simp only [dmNatFrag, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨.bvar (d - 1 - 0), ?_, fun ρ hx hy => ?_⟩
      · show denoteMeta m.acval env ψ d
          (.fvar 0
            (.const ConLeche.natName [])) = _
        rw [denoteMeta_fvar]
      · exact ⟨⟨by simp, by simp⟩, by rw [interp_bvar]; exact hx,
          by rw [interp_bvar]; rfl⟩
    · refine ⟨.bvar (d - 1 - 1), ?_, fun ρ hx hy => ?_⟩
      · show denoteMeta m.acval env ψ d
          (.fvar 1
            (.const ConLeche.natName [])) = _
        rw [denoteMeta_fvar]
      · exact ⟨⟨by simp, by simp⟩, by rw [interp_bvar]; exact hy,
          by rw [interp_bvar]; rfl⟩
  | .bvar _, h | .sort _, h | .lam _ _ _, h | .letE _ _ _, h
  | .forallE _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp [dmNatFrag] at h

/-! ## One certificate, converted

`certValueS`'s mirror.  The run's three components become, in order:
the annotated applied proof keeps the frame (currency-free), the
`InferClaim` row gives its reading's membership in the inferred
type's, and the `DefEqClaim` row identifies that type with the
pinned statement — so the statement's interpretation is inhabited.

Two premises v1 does not have, both the grading tax: the statement's
reading must be graded (`DefEqClaim` compares graded readings), and
the applied proof must *read* at all (v1's `InferClaimsR` concluded
existence; the P claim takes the reading as a premise, so the reads
bundle supplies it). -/

/-- **One certificate, extracted at `interp`.** -/
theorem certValue {F : Nat} (mp : EnvModelM V μ env) (ψ : Name → Nat)
    (hacc : ∀ {d : Nat} {e t : Expr},
      ConLeche.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta mp.base2.acval env ψ d e = some ea)
    (hreads : InferReads mp.base2 μ ψ F)
    (hinfC : InferClaim μ mp.base2 ψ F)
    (hdeC : DefEqClaim μ mp.base2 ψ F)
    {c : Name} {annVal : Expr} {st : List Expr × Expr} {proof : Expr}
    (hfacts : CertRunFacts μ env F c annVal st proof)
    {Δa : List AnnotTerm}
    (hW : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hB : (divModCertApplied (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))).looseBVarsBounded 0
      = true)
    (hL : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hCA : CtxOk mp.base2 ψ 4 Δa (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hWE : Expr.WScoped 4 (Expr.substConst0 c annVal st.2))
    (hBE : (Expr.substConst0 c annVal st.2).looseBVarsBounded 0 = true)
    (hLE : Expr.LeavesBounded (Expr.substConst0 c annVal st.2))
    (hCE : CtxOk mp.base2 ψ 4 Δa (Expr.substConst0 c annVal st.2))
    {vE : AnnotTerm}
    (hvE : denoteMeta mp.base2.acval env ψ 4
      (Expr.substConst0 c annVal st.2) = some vE)
    (hokE : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vE)
    (ρ : Nat → V) (hsat : Sat V Δa ρ) :
    ∃ w : V, w ∈ˢ interp V ρ vE := by
  obtain ⟨-, appliedA, tp, hann, hinf, hde⟩ := hfacts
  -- the annotated applied proof keeps the frame
  have hWA : Expr.WScoped 4 appliedA :=
    ConLeche.annotateCore_WScoped F _ hann hW
  have hBA : appliedA.looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F _ hann hB
  have hsub := ConLeche.annotateCore_leaves_sub F _ hann hW hB
  have hLA : Expr.LeavesBounded appliedA := fun l hl => hL l (hsub l hl)
  have hCA' : CtxOk mp.base2 ψ 4 Δa appliedA := hCA.of_subset hsub
  -- the readings
  obtain ⟨ea, hea⟩ := hacc hinf hWA hBA hLA
  obtain ⟨ta, hta⟩ :=
    hreads hinf hWA hBA hLA hCA' hea
  obtain ⟨-, hokT, hmem⟩ := hinfC hinf hWA hBA hLA hCA' hea hta
  -- the inferred type's frame
  have hWtp : Expr.WScoped 4 tp :=
    ConLeche.inferTypeCore_WScoped mp.base2.wf F hinf hWA
  have hBtp : tp.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeCore_looseBVars mp.base2.wf F hinf hWA hBA hLA
  have hLtp : Expr.LeavesBounded tp := fun l hl =>
    hLA l (ConLeche.inferTypeCore_fvarLeaves mp.base2.wf F hinf hWA
      l hl)
  have hCtp : CtxOk mp.base2 ψ 4 Δa tp :=
    hCA'.of_subset
      (ConLeche.inferTypeCore_fvarLeaves mp.base2.wf F hinf hWA)
  -- the defeq run identifies the inferred type with the statement
  have heq := hdeC hde hWtp hBtp hLtp hWE hBE hLE hCtp hCE hta hvE
    hokT hokE ρ hsat
  exact ⟨interp V ρ ea, by rw [← heq]; exact hmem ρ hsat⟩

/-! ## The frame's leaf discipline

`CtxOkR.pinnedCtxLift`'s mirror.  `CtxOk` is slack in the same way
`CtxOkR` is — it asks for the leaf annotation's *reading* to agree with
the entry read one telescope deeper, not for entry equality — so a
hypothesis slot may carry its type's reading at the depth the type is
*stated*, with the depth-4 reading its lift.  The P side adds the
grading conjunct, which is supplied at the depth-4 reading and
transported by the same equation. -/

/-- Two weakenings, composed. -/
theorem denotePLift {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (acval n ψ').liftN 1 k = acval n ψ')
    {d n : Nat} {e : Expr} {W : AnnotTerm} (hw : Expr.WScoped d e)
    (h : denoteMeta acval env ψ d e = some W) :
    denoteMeta acval env ψ (d + n) e = some (W.liftN n 0) := by
  induction n with
  | zero => rw [Nat.add_zero, h, AnnotTerm.liftN_zero]
  | succ n ih =>
    rw [show d + (n + 1) = (d + n) + 1 from rfl,
      denoteMeta_weaken_top hacl (hw.mono (by omega)), ih]
    simp only [Option.map_some]
    rw [AnnotTerm.liftN_liftN, Nat.add_comm 1 n]

/-- **The certificate frame's leaf discipline, in the lift-carrying
form.** -/
theorem ctxOk_pinnedLift {m : EnvModel V env} {ψ : Name → Nat}
    {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (hlen : Δa.length = d)
    (hslot : ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2 ∧
      ∃ tya, denoteMeta m.acval env ψ d l.2 = some tya ∧
        tya = (Δa.getD (d - 1 - l.1) default).liftN (d - l.1) 0 ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya) :
    CtxOk m ψ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, hden, heq, hok⟩ := hslot l hl
  have hidx : d - 1 - l.1 < Δa.length := by rw [hlen]; omega
  have hget : Δa[d - 1 - l.1]?
      = some (Δa.getD (d - 1 - l.1) default) := by
    rw [List.getD, List.getElem?_eq_getElem hidx]
    rfl
  refine ⟨hlt, hfb, tya, _, hden, hget, fun ρ _ => ?_, hok⟩
  rw [heq, interp_liftN]
  congr 1
  funext j
  simp only [shiftE]
  rw [if_neg (by omega)]
  congr 1
  omega

/-! ## The pinned `Eq` spine, read and graded -/

/-- The pinned `Eq` spine's reading (`denote_eqSpine`'s mirror): the
head carries `Eq.{1}`, whose level argument is not `[]`, so the
operation substitution leaves it alone. -/
theorem denoteMeta_eqSpine {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {c : Name} {value' : Expr}
    (hEq : env.find? eqName = some eqA) {A a b : Expr}
    {Aa aa ba : AnnotTerm} {d : Nat}
    (hA : denoteMeta acval env ψ d (Expr.substConst0 c value' A)
      = some Aa)
    (ha : denoteMeta acval env ψ d (Expr.substConst0 c value' a)
      = some aa)
    (hb : denoteMeta acval env ψ d (Expr.substConst0 c value' b)
      = some ba) :
    denoteMeta acval env ψ d (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero]) A) a) b))
      = some (.app (.app (.app (acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) Aa) aa)
          ba) := by
  have hhead : denoteMeta acval env ψ d
      (Expr.substConst0 c value' (.const eqName [.succ .zero]))
      = some (acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) := by
    rw [show Expr.substConst0 c value' (.const eqName [.succ .zero])
        = .const eqName [.succ .zero] from by
      simp only [Expr.substConst0]
      rw [if_neg (by rintro ⟨-, hh⟩; exact nomatch hh)]]
    exact denoteMeta_const hEq rfl
  show denoteMeta acval env ψ d
      (.app (.app (.app (Expr.substConst0 c value'
        (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' A)) (Expr.substConst0 c value' a))
        (Expr.substConst0 c value' b)) = _
  rw [denoteMeta_app, denoteMeta_app, denoteMeta_app, hhead, hA, ha, hb]
  rfl

/-- The `Eq.{1}` level assignment sends `u` to `1`. -/
theorem eqSubst_uN (ψ : Name → Nat) :
    Level.substFn ψ eqA.toConstantVal.levelParams [Level.zero.succ] uN
      = 1 := rfl

/-! ## The head names a certificate block reads -/

/-- The extension's valuation: the pinned operation at its own name
(through the annotated stored value), every dependency at its
storage. -/
def dmLeaf {env : Env} (m : EnvModel V env) (c : Name)
    (A : (Name → Nat) → AnnotTerm) (ψ : Name → Nat) (n : Name) : AnnotTerm :=
  acvalWith m.acval c A n ψ

/-- The binary heads the statements apply: the recurrence dependencies
minus the guard's `Nat.ble` and the unary `Nat.pred`. -/
def dmBinNames (c : Name) : List Name :=
  (ConLeche.natOpDeps c).filter fun n =>
    n != ConLeche.natBleName && n != ConLeche.natPredName

/-- The unary heads: `Nat.succ`.  Every pin-certified operation is
binary (`Nat.log2` left the family with its fast path), so the
operation itself never appears here. -/
def dmUnNames (_c : Name) : List Name := [ConLeche.natSuccName]

/-- Every head a certificate block mentions. -/
def dmHeadNames (c : Name) : List Name :=
  ConLeche.natName :: ConLeche.boolName :: ConLeche.natZeroName ::
    ConLeche.natBleName :: ConLeche.boolTrueName ::
    ConLeche.boolFalseName :: (dmBinNames c ++ dmUnNames c)

/-- The walk's head list sits inside the frame's. -/
theorem mem_dmHeadNames {c n : Name}
    (h : n ∈ ConLeche.natZeroName :: (dmBinNames c ++ dmUnNames c)) :
    n ∈ dmHeadNames c := by
  simp only [dmHeadNames, List.mem_cons] at h ⊢
  rcases h with rfl | h
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-! ## The statements' syntactic obligations, from the grammar

A `dmNatFrag` term has only the two frame variables as leaves, both at
`Nat`, and no bound variables at all — so every syntactic side
condition the frame asks for is a consequence of the grammar, not a
`by decide` at each call site. -/

/-- A frame variable is well-scoped at any depth above its index. -/
theorem dmFvarWScoped {d i : Nat} {ty : Expr} (hi : i < d)
    (hty : Expr.WScoped i ty) : Expr.WScoped d (Expr.fvar i ty) := by
  simp only [Expr.WScoped]
  exact ⟨hi, hty⟩

theorem dmNatFrag_syntax {bins uns : List Name} :
    ∀ e : Expr, dmNatFrag bins uns e = true →
      dmLeavesOk e = true ∧ e.looseBVarsBounded 0 = true ∧
      ∀ d : Nat, 2 ≤ d → Expr.WScoped d e
  | .app (.app (.const n us) a) b, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨-, rfl⟩, ha⟩, hb⟩ := h
    obtain ⟨hla, hba, hwa⟩ := dmNatFrag_syntax a ha
    obtain ⟨hlb, hbb, hwb⟩ := dmNatFrag_syntax b hb
    refine ⟨?_, ?_, fun d hd =>
      dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar (e := .const n []) rfl)
        (hwa d hd)) (hwb d hd)⟩
    · simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
        List.all_append, Bool.and_eq_true]
      exact ⟨hla, hlb⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨⟨trivial, hba⟩, hbb⟩
  | .app (.const n us) a, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨-, rfl⟩, ha⟩ := h
    obtain ⟨hla, hba, hwa⟩ := dmNatFrag_syntax a ha
    refine ⟨?_, ?_, fun d hd =>
      dmApp_wscoped (Expr.WScoped.of_not_hasFvar (e := .const n []) rfl)
        (hwa d hd)⟩
    · simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append]
      exact hla
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨trivial, hba⟩
  | .const n us, h => by
    simp only [dmNatFrag, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl, fun _ _ =>
      Expr.WScoped.of_not_hasFvar
        (e := .const ConLeche.natZeroName []) rfl⟩
  | .fvar i ty, h => by
    simp only [dmNatFrag, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl,
        fun d hd => dmFvarWScoped (by omega)
          (Expr.WScoped.of_not_hasFvar
            (e := .const ConLeche.natName []) rfl)⟩
    · exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl,
        fun d hd => dmFvarWScoped (by omega)
          (Expr.WScoped.of_not_hasFvar
            (e := .const ConLeche.natName []) rfl)⟩
  | .bvar _, h | .sort _, h | .lam _ _ _, h | .letE _ _ _, h
  | .forallE _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp [dmNatFrag] at h

/-- Scoping survives the operation substitution (the `WScoped` twin of
`wscopedB_substConst0`; `substConst0` rewrites `const` nodes and
recurses only through applications). -/
theorem wscoped_substConst0 {c : Name} {v : Expr}
    (hv : v.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, Expr.WScoped d e →
      Expr.WScoped d (Expr.substConst0 c v e)
  | .const n us, d, _ => by
    simp only [Expr.substConst0]
    split
    · exact Expr.WScoped.of_not_hasFvar hv
    · exact Expr.WScoped.of_not_hasFvar (e := .const n us) rfl
  | .app f a, d, hw => by
    simp only [Expr.WScoped] at hw
    exact dmApp_wscoped (wscoped_substConst0 hv f hw.1)
      (wscoped_substConst0 hv a hw.2)
  | .bvar _, _, hw | .fvar _ _, _, hw | .sort _, _, hw
  | .lit _, _, hw | .lam _ _ _, _, hw | .forallE _ _ _, _, hw
  | .letE _ _ _, _, hw | .proj _ _ _, _, hw => hw

/-! ## The certificate frame

Everything the nine clause blocks are read against, at one assignment:
the extension's valuation with its closedness and grading, the frame's
`Nat` and `Bool` as universes, the statements' heads as functions on
`Nat`, and the pinned `Eq`.  This is `dmFrameS`'s existential tuple as
a structure. -/

/-- **The div/mod certificate frame at `interp`.** -/
structure DmFrame {env : Env} (mp : EnvModelM V μ env) (c : Name)
    (A : (Name → Nat) → AnnotTerm) (value' : Expr) (ψ : Name → Nat) :
    Prop where
  /-- the pinned `Eq` is stored -/
  eqStored : env.find? eqName = some eqA
  /-- neither pinned type name is the operation being installed -/
  natNe : ConLeche.natName ≠ c
  boolNe : ConLeche.boolName ≠ c
  /-- the annotated stored value's reading, at every depth -/
  selfRead : ∀ d : Nat,
    denoteMeta mp.base2.acval env ψ d value' = some (A ψ)
  /-- the annotated value is closed -/
  valueNoFvar : value'.hasFvar = false
  valueBounded : value'.looseBVarsBounded 0 = true
  /-- every head the statements read is the operation itself or is
  stored level-monomorphically -/
  stored : ∀ n ∈ dmHeadNames c, n = c ∨ (n ≠ c ∧ ∃ ci,
    env.find? n = some ci ∧ ci.toConstantVal.levelParams = [])
  /-- the extension's leaves are graded and closed -/
  leafOk : ∀ (n : Name) (ρ : Nat → V),
    WellDenotedV V ρ (dmLeaf mp.base2 c A ψ n)
  leafClosed : ∀ (n : Name) (ρ ρ' : Nat → V),
    interp V ρ (dmLeaf mp.base2 c A ψ n)
      = interp V ρ' (dmLeaf mp.base2 c A ψ n)
  /-- the frame's two types are universes -/
  natU : ∀ ρ : Nat → V,
    interp V ρ (mp.base2.acval ConLeche.natName ψ) ∈ˢ (univ 1 : V)
  boolU : ∀ ρ : Nat → V,
    interp V ρ (mp.base2.acval ConLeche.boolName ψ) ∈ˢ (univ 1 : V)
  /-- the statements' heads are functions on the frame's `Nat` -/
  binHead : ∀ n ∈ dmBinNames c, ∀ ρ : Nat → V,
    DmBinV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (dmLeaf mp.base2 c A ψ n))
  unHead : ∀ n ∈ dmUnNames c, ∀ ρ : Nat → V,
    DmUnV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (dmLeaf mp.base2 c A ψ n))
  /-- …and the guard's `Nat.ble` is one into `Bool` -/
  bleHead : ∀ ρ : Nat → V,
    DmBinV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
      (interp V ρ (mp.base2.acval ConLeche.boolName ψ))
      (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
  /-- the constructors inhabit their types -/
  zeroMem : ∀ ρ : Nat → V,
    interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natZeroName)
      ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ)
  boolCtorMem : ∀ bn : Name,
    bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName →
    ∀ ρ : Nat → V, interp V ρ (dmLeaf mp.base2 c A ψ bn)
      ∈ˢ interp V ρ (mp.base2.acval ConLeche.boolName ψ)

namespace DmFrame

variable {mp : EnvModelM V μ env} {c : Name} {A : (Name → Nat) → AnnotTerm}
variable {value' : Expr} {ψ : Name → Nat}

/-- **A head reads to its leaf**, at every depth: the operation itself
through the substitution, a dependency through its storage. -/
theorem read (fr : DmFrame mp c A value' ψ) {n : Name}
    (hn : n ∈ dmHeadNames c) (d : Nat) :
    denoteMeta mp.base2.acval env ψ d
        (Expr.substConst0 c value' (.const n []))
      = some (dmLeaf mp.base2 c A ψ n) := by
  rcases fr.stored n hn with rfl | ⟨hne, ci, hf, hlp⟩
  · rw [show Expr.substConst0 n value' (.const n []) = value' from by
      rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
    rw [fr.selfRead d, dmLeaf,
      show acvalWith mp.base2.acval n A n = A from acvalWith_self]
  · rw [show Expr.substConst0 c value' (.const n []) = .const n []
      from by
      rw [Expr.substConst0, if_neg (fun hh => hne hh.1)]]
    rw [denoteMeta_levelless_const hf hlp, dmLeaf,
      show acvalWith mp.base2.acval c A n = mp.base2.acval n
        from acvalWith_ne hne]

/-- The `Nat` leaf is not moved by the extension. -/
theorem natLeaf (fr : DmFrame mp c A value' ψ) :
    dmLeaf mp.base2 c A ψ ConLeche.natName
      = mp.base2.acval ConLeche.natName ψ := by
  rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.natName
    = mp.base2.acval ConLeche.natName from acvalWith_ne fr.natNe]

/-- Nor is the `Bool` leaf. -/
theorem boolLeaf (fr : DmFrame mp c A value' ψ) :
    dmLeaf mp.base2 c A ψ ConLeche.boolName
      = mp.base2.acval ConLeche.boolName ψ := by
  rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.boolName
    = mp.base2.acval ConLeche.boolName from acvalWith_ne fr.boolNe]

end DmFrame

/-! ## The statement's equation, at a satisfied frame

`dmCertEq1S`/`dmCertEq2S`'s content, with the two hypothesis-slot
shapes factored out: what the certificate delivers depends on the
*frame* being satisfied, not on how many hypotheses it took to satisfy
it.  The caller supplies the four-entry telescope with its two `Nat`
slots at the bottom, the applied proof's frame conditions, and a
satisfying valuation. -/

/-- The frame's `Nat` leaf reads. -/
theorem DmFrame.readNat {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (d : Nat) :
    denoteMeta mp.base2.acval env ψ d (Expr.const ConLeche.natName [])
      = some (mp.base2.acval ConLeche.natName ψ) := by
  rcases fr.stored ConLeche.natName (by simp [dmHeadNames]) with
    hc | ⟨-, ci, hf, hlp⟩
  · exact absurd hc fr.natNe
  · exact denoteMeta_levelless_const hf hlp

/-- A `dmLeavesOk` term's leaves are the two `Nat` slots, so the frame
discipline is free for it. -/
theorem dmCtxOk_natLeaves {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) {Δa : List AnnotTerm}
    (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval ConLeche.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval ConLeche.natName ψ)
    {e : Expr} (he : dmLeavesOk e = true) :
    CtxOk mp.base2 ψ 4 Δa (Expr.substConst0 c value' e) := by
  have hself : ∀ k : Nat,
      (mp.base2.acval ConLeche.natName ψ).liftN k 0
        = mp.base2.acval ConLeche.natName ψ := fun k =>
    AnnotTerm.liftN_eq_self _
      (by rw [mp.base2.acval_erase]
          exact mp.base2.cval_closed ConLeche.natName ψ) k
  refine ctxOk_pinnedLift hlen (fun l hl => ?_)
  rw [fvarLeaves_substConst0 (n := c) fr.valueNoFvar e] at hl
  rcases dmLeavesOk_mem he hl with rfl | rfl
  · refine ⟨by omega, trivial, _, fr.readNat 4, ?_,
      fun ρ _ => ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩⟩
    show mp.base2.acval ConLeche.natName ψ
      = (Δa.getD 3 default).liftN 4 0
    rw [h3, hself 4]
  · refine ⟨by omega, trivial, _, fr.readNat 4, ?_,
      fun ρ _ => ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩⟩
    show mp.base2.acval ConLeche.natName ψ
      = (Δa.getD 2 default).liftN 3 0
    rw [h2, hself 3]

/-- The frame's two `Nat` slots, read off satisfaction. -/
theorem dmSat_slots {mp : EnvModelM V μ env} {ψ : Name → Nat}
    {Δa : List AnnotTerm} (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval ConLeche.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval ConLeche.natName ψ)
    {ρ : Nat → V} (hsat : Sat V Δa ρ) (ρ₀ : Nat → V) :
    ρ 3 ∈ˢ interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) ∧
      ρ 2 ∈ˢ interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) := by
  have hg : ∀ i : Nat, i < 4 →
      Δa[i]? = some (Δa.getD i default) := by
    intro i hi
    rw [List.getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    rfl
  have e3 := hsat 3 _ (by rw [hg 3 (by omega), h3])
  have e2 := hsat 2 _ (by rw [hg 2 (by omega), h2])
  rw [acval_interp_closedC mp.base2 _ ψ _ ρ₀] at e3 e2
  exact ⟨e3, e2⟩

/-- **The certificate's equation, at a satisfied frame.**  The
statement's two sides are `Nat`-valued fragments; how the frame's
hypothesis slots came to be satisfied is the caller's business. -/
theorem dmStmtEq {F : Nat} {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (heqlaw : EqLaw mp.base2)
    (hacc : ∀ {d : Nat} {e t : Expr},
      ConLeche.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta mp.base2.acval env ψ d e = some ea)
    (hreads : InferReads mp.base2 μ ψ F)
    (hinfC : InferClaim μ mp.base2 ψ F)
    (hdeC : DefEqClaim μ mp.base2 ψ F)
    {hyps : List Expr} {lhs rhs proof : Expr}
    (hfacts : CertRunFacts μ env F c value'
      (hyps, .app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.natName [])) lhs) rhs) proof)
    (hlhs : dmNatFrag (dmBinNames c) (dmUnNames c) lhs = true)
    (hrhs : dmNatFrag (dmBinNames c) (dmUnNames c) rhs = true)
    {Δa : List AnnotTerm} (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval ConLeche.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval ConLeche.natName ψ)
    (hWA : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (hBA : (divModCertApplied (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))).looseBVarsBounded 0
      = true)
    (hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (hCA : CtxOk mp.base2 ψ 4 Δa (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (ρ4 : Nat → V) (hsat : Sat V Δa ρ4) :
    dmEvalV V (fun n => interp V ρ4 (dmLeaf mp.base2 c A ψ n))
        (ρ4 3) (ρ4 2) lhs
      = dmEvalV V (fun n => interp V ρ4 (dmLeaf mp.base2 c A ψ n))
        (ρ4 3) (ρ4 2) rhs := by
  -- the walk's inputs, at the fixed `Nat` set
  have hmove : ∀ ρ : Nat → V,
      interp V ρ (mp.base2.acval ConLeche.natName ψ)
        = interp V ρ4 (mp.base2.acval ConLeche.natName ψ) :=
    fun ρ => acval_interp_closedC mp.base2 _ ψ ρ ρ4
  have hread : ∀ n ∈ ConLeche.natZeroName ::
      (dmBinNames c ++ dmUnNames c), ∀ d' : Nat,
      denoteMeta mp.base2.acval env ψ d'
        (Expr.substConst0 c value' (.const n []))
        = some (acvalWith mp.base2.acval c A n ψ) :=
    fun n hn d' => fr.read (mem_dmHeadNames hn) d'
  have hbin : ∀ n ∈ dmBinNames c, ∀ ρ : Nat → V,
      DmBinV (interp V ρ4 (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ4 (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ (acvalWith mp.base2.acval c A n ψ)) := by
    intro n hn ρ
    have h := fr.binHead n hn ρ
    rwa [hmove ρ] at h
  have hun : ∀ n ∈ dmUnNames c, ∀ ρ : Nat → V,
      DmUnV (interp V ρ4 (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ4 (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ (acvalWith mp.base2.acval c A n ψ)) := by
    intro n hn ρ
    have h := fr.unHead n hn ρ
    rwa [hmove ρ] at h
  have hzero : ∀ ρ : Nat → V,
      interp V ρ (acvalWith mp.base2.acval c A ConLeche.natZeroName ψ)
        ∈ˢ interp V ρ4 (mp.base2.acval ConLeche.natName ψ) := by
    intro ρ
    have h := fr.zeroMem ρ
    rwa [hmove ρ] at h
  -- the two sides, walked at depth 4
  obtain ⟨lhsa, hdl, hfl⟩ :=
    dmNatFrag_graded (d := 4) hread fr.leafOk hbin hun hzero lhs hlhs
  obtain ⟨rhsa, hdr, hfr⟩ :=
    dmNatFrag_graded (d := 4) hread fr.leafOk hbin hun hzero rhs hrhs
  -- the slots, at every satisfying valuation
  have hslots : ∀ ρ : Nat → V, Sat V Δa ρ →
      ρ 3 ∈ˢ interp V ρ4 (mp.base2.acval ConLeche.natName ψ) ∧
        ρ 2 ∈ˢ interp V ρ4 (mp.base2.acval ConLeche.natName ψ) :=
    fun ρ hρ => dmSat_slots hlen h3 h2 hρ ρ4
  -- the statement's reading
  have hnatRead : denoteMeta mp.base2.acval env ψ 4
      (Expr.substConst0 c value' (.const ConLeche.natName []))
      = some (mp.base2.acval ConLeche.natName ψ) := by
    rw [fr.read (by simp [dmHeadNames]) 4, fr.natLeaf]
  have hstmt := denoteMeta_eqSpine (acval := mp.base2.acval) (c := c)
    (value' := value') fr.eqStored hnatRead hdl hdr
  -- the statement's grading
  have hokE : ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ((.app (.app (.app (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.zero.succ])) (mp.base2.acval ConLeche.natName ψ)) lhsa)
        rhsa : AnnotTerm)) := by
    intro ρ hρ
    obtain ⟨hx, hy⟩ := hslots ρ hρ
    obtain ⟨hokl, hml, -⟩ := hfl ρ hx hy
    obtain ⟨hokr, hmr, -⟩ := hfr ρ hx hy
    exact ((heqlaw fr.eqStored _).2 ρ _ lhsa rhsa
      ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩ hokl hokr
      (by rw [eqSubst_uN, hmove ρ]; exact fr.natU ρ4)
      (by rw [hmove ρ]; exact hml)
      (by rw [hmove ρ]; exact hmr)).1
  -- the statement's syntactic frame
  obtain ⟨hlL, hbL, hwL⟩ := dmNatFrag_syntax lhs hlhs
  obtain ⟨hlR, hbR, hwR⟩ := dmNatFrag_syntax rhs hrhs
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const ConLeche.natName [])) lhs)
      rhs) = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hWE : Expr.WScoped 4 (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.natName [])) lhs) rhs)) :=
    wscoped_substConst0 fr.valueNoFvar _
      (dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar
          (e := .const eqName [.succ .zero]) rfl)
        (Expr.WScoped.of_not_hasFvar
          (e := .const ConLeche.natName []) rfl))
        (hwL 4 (by omega))) (hwR 4 (by omega)))
  have hBE : (Expr.substConst0 c value' (.app (.app (.app
      (.const eqName [.succ .zero]) (.const ConLeche.natName [])) lhs)
      rhs)).looseBVarsBounded 0 = true :=
    looseBVarsBounded_substConst0 fr.valueBounded _
      (by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨⟨⟨trivial, trivial⟩, hbL⟩, hbR⟩)
  have hLE : Expr.LeavesBounded (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.natName [])) lhs) rhs)) :=
    dmLeavesOk_leavesBounded
      (dmLeavesOk_substConst0 fr.valueNoFvar hlE)
  have hCE := dmCtxOk_natLeaves fr hlen h3 h2 hlE
  -- the certificate: the statement is inhabited
  obtain ⟨w, hw⟩ := certValue mp ψ hacc hreads hinfC hdeC hfacts
    hWA hBA hLA hCA hWE hBE hLE hCE hstmt hokE ρ4 hsat
  -- …hence the two sides are equal
  obtain ⟨hx4, hy4⟩ := hslots ρ4 hsat
  obtain ⟨-, hml4, hel⟩ := hfl ρ4 hx4 hy4
  obtain ⟨-, hmr4, her⟩ := hfr ρ4 hx4 hy4
  rw [show interp V ρ4 ((.app (.app (.app (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.zero.succ])) (mp.base2.acval ConLeche.natName ψ)) lhsa)
        rhsa : AnnotTerm))
      = eqv (interp V ρ4 lhsa) (interp V ρ4 rhsa) from by
    rw [interp_app, interp_app, interp_app]
    exact (heqlaw fr.eqStored _).1 ρ4 _ _ _
      (by rw [eqSubst_uN]; exact fr.natU ρ4) hml4 hmr4] at hw
  have hlr := eq_of_mem_eqv hw
  show dmEvalV V
      (fun n => interp V ρ4 (acvalWith mp.base2.acval c A n ψ))
      (ρ4 (4 - 1 - 0)) (ρ4 (4 - 1 - 1)) lhs
    = dmEvalV V
      (fun n => interp V ρ4 (acvalWith mp.base2.acval c A n ψ))
      (ρ4 (4 - 1 - 0)) (ρ4 (4 - 1 - 1)) rhs
  rw [← hel, ← her]
  exact hlr

/-! ## The guard spine

Every one of the nine operations guards its recurrence with
`Eq Bool (Nat.ble a b) (Bool.true/false)`, so the hypothesis slot has
one shape.  Read at depth 2 it is the telescope entry the frame is
satisfied with; read at depth 4 it is the leaf annotation `CtxOk`
reads. -/

/-- The walk's inputs, packaged from the frame. -/
theorem dmWalkInputs {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (ρ₀ : Nat → V) :
    (∀ n ∈ ConLeche.natZeroName :: (dmBinNames c ++ dmUnNames c),
      ∀ d' : Nat, denoteMeta mp.base2.acval env ψ d'
        (Expr.substConst0 c value' (.const n []))
        = some (acvalWith mp.base2.acval c A n ψ)) ∧
    (∀ n ∈ dmBinNames c, ∀ ρ : Nat → V,
      DmBinV (interp V ρ₀ (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ₀ (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ (acvalWith mp.base2.acval c A n ψ))) ∧
    (∀ n ∈ dmUnNames c, ∀ ρ : Nat → V,
      DmUnV (interp V ρ₀ (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ₀ (mp.base2.acval ConLeche.natName ψ))
        (interp V ρ (acvalWith mp.base2.acval c A n ψ))) ∧
    (∀ ρ : Nat → V,
      interp V ρ (acvalWith mp.base2.acval c A ConLeche.natZeroName ψ)
        ∈ˢ interp V ρ₀ (mp.base2.acval ConLeche.natName ψ)) := by
  have hmove : ∀ ρ : Nat → V,
      interp V ρ (mp.base2.acval ConLeche.natName ψ)
        = interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) :=
    fun ρ => acval_interp_closedC mp.base2 _ ψ ρ ρ₀
  refine ⟨fun n hn d' => fr.read (mem_dmHeadNames hn) d', ?_, ?_, ?_⟩
  · intro n hn ρ
    have h := fr.binHead n hn ρ
    rwa [hmove ρ] at h
  · intro n hn ρ
    have h := fr.unHead n hn ρ
    rwa [hmove ρ] at h
  · intro ρ
    have h := fr.zeroMem ρ
    rwa [hmove ρ] at h

/-- **The guard spine, read and graded.** -/
theorem dmGuardSpine {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (heqlaw : EqLaw mp.base2)
    {t1 t2 : Expr} {bn : Name}
    (hbn : bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName)
    (ht1 : dmNatFrag (dmBinNames c) (dmUnNames c) t1 = true)
    (ht2 : dmNatFrag (dmBinNames c) (dmUnNames c) t2 = true)
    (ρ₀ : Nat → V) (d : Nat) :
    ∃ ga, denoteMeta mp.base2.acval env ψ d (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) t1) t2))
          (.const bn []))) = some ga ∧
      ∀ ρ : Nat → V,
        ρ (d - 1 - 0)
          ∈ˢ interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) →
        ρ (d - 1 - 1)
          ∈ˢ interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) →
        WellDenotedV V ρ ga ∧
        interp V ρ ga = eqv
          (SetTheory.app (SetTheory.app
            (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
            (dmEvalV V
              (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
              (ρ (d - 1 - 0)) (ρ (d - 1 - 1)) t1))
            (dmEvalV V
              (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
              (ρ (d - 1 - 0)) (ρ (d - 1 - 1)) t2))
          (interp V ρ (dmLeaf mp.base2 c A ψ bn)) := by
  obtain ⟨hread, hbin, hun, hzero⟩ := dmWalkInputs fr ρ₀
  obtain ⟨t1a, hd1, hf1⟩ :=
    dmNatFrag_graded (d := d) hread fr.leafOk hbin hun hzero t1 ht1
  obtain ⟨t2a, hd2, hf2⟩ :=
    dmNatFrag_graded (d := d) hread fr.leafOk hbin hun hzero t2 ht2
  have hbleRead : denoteMeta mp.base2.acval env ψ d
      (Expr.substConst0 c value' (.const ConLeche.natBleName []))
      = some (dmLeaf mp.base2 c A ψ ConLeche.natBleName) :=
    fr.read (by simp [dmHeadNames]) d
  have hbnRead : denoteMeta mp.base2.acval env ψ d
      (Expr.substConst0 c value' (.const bn []))
      = some (dmLeaf mp.base2 c A ψ bn) := by
    refine fr.read ?_ d
    rcases hbn with rfl | rfl <;> simp [dmHeadNames]
  have hbleApp : denoteMeta mp.base2.acval env ψ d
      (Expr.substConst0 c value'
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
      = some (.app (.app (dmLeaf mp.base2 c A ψ ConLeche.natBleName)
          t1a) t2a) := by
    show denoteMeta mp.base2.acval env ψ d
      (.app (.app (Expr.substConst0 c value'
        (.const ConLeche.natBleName [])) (Expr.substConst0 c value' t1))
        (Expr.substConst0 c value' t2)) = _
    rw [denoteMeta_app, denoteMeta_app, hbleRead, hd1, hd2]
    rfl
  have hboolRead : denoteMeta mp.base2.acval env ψ d
      (Expr.substConst0 c value' (.const ConLeche.boolName []))
      = some (mp.base2.acval ConLeche.boolName ψ) := by
    rw [fr.read (by simp [dmHeadNames]) d, fr.boolLeaf]
  refine ⟨_, denoteMeta_eqSpine fr.eqStored hboolRead hbleApp hbnRead,
    fun ρ hx hy => ?_⟩
  obtain ⟨hok1, hm1, he1⟩ := hf1 ρ hx hy
  obtain ⟨hok2, hm2, he2⟩ := hf2 ρ hx hy
  have hmoveB : interp V ρ (mp.base2.acval ConLeche.boolName ψ)
      = interp V ρ (mp.base2.acval ConLeche.boolName ψ) := rfl
  have hbleV := fr.bleHead ρ
  have hmoveN : interp V ρ (mp.base2.acval ConLeche.natName ψ)
      = interp V ρ₀ (mp.base2.acval ConLeche.natName ψ) :=
    acval_interp_closedC mp.base2 _ ψ ρ ρ₀
  rw [hmoveN] at hbleV
  have hbleOk : WellDenotedV V ρ
      ((.app (.app (dmLeaf mp.base2 c A ψ ConLeche.natBleName) t1a) t2a
        : AnnotTerm)) :=
    ⟨DmBinV.wellDenoted hbleV hm1 hm2 (fr.leafOk _ ρ).1 hok1.1 hok2.1 rfl rfl
        rfl,
      by rw [AnnotValid_app, AnnotValid_app]
         exact ⟨⟨(fr.leafOk _ ρ).2, hok1.2⟩, hok2.2⟩⟩
  have hbleMem : interp V ρ
      ((.app (.app (dmLeaf mp.base2 c A ψ ConLeche.natBleName) t1a) t2a
        : AnnotTerm))
      ∈ˢ interp V ρ (mp.base2.acval ConLeche.boolName ψ) := by
    rw [interp_app, interp_app]
    exact DmBinV.app hbleV hm1 hm2
  have hlaw := (heqlaw fr.eqStored (Level.substFn ψ
      eqA.toConstantVal.levelParams [Level.zero.succ])).2 ρ
    (mp.base2.acval ConLeche.boolName ψ) _ (dmLeaf mp.base2 c A ψ bn)
    ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩ hbleOk
    (fr.leafOk _ ρ)
    (by rw [eqSubst_uN]; exact fr.boolU ρ) hbleMem
    (fr.boolCtorMem bn hbn ρ)
  refine ⟨hlaw.1, ?_⟩
  rw [interp_app, interp_app, interp_app]
  rw [(heqlaw fr.eqStored (Level.substFn ψ
      eqA.toConstantVal.levelParams [Level.zero.succ])).1 ρ _ _ _
    (by rw [eqSubst_uN]; exact fr.boolU ρ) hbleMem
    (fr.boolCtorMem bn hbn ρ)]
  rw [interp_app, interp_app, he1, he2]
  rfl

/-! ## A guarded clause, discharged

`dmClause1S`'s mirror: build the four-entry telescope with the guard's
depth-2 reading in its hypothesis slot, satisfy it (the slot's
inhabitant is the canonical proof, because the guard *fired*), and
hand the statement to `dmStmtEq`. -/

/-- **A guarded div/mod clause, discharged at `interp`.** -/
theorem dmClause1 {F : Nat} {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (heqlaw : EqLaw mp.base2)
    (hacc : ∀ {d : Nat} {e t : Expr},
      ConLeche.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta mp.base2.acval env ψ d e = some ea)
    (hreads : InferReads mp.base2 μ ψ F)
    (hinfC : InferClaim μ mp.base2 ψ F)
    (hdeC : DefEqClaim μ mp.base2 ψ F)
    (ρ : Nat → V) {xx yy : V}
    (hxx : xx ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ))
    (hyy : yy ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ))
    {t1 t2 lhs rhs proof : Expr} {bn : Name}
    (hbn : bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName)
    (hfacts : CertRunFacts μ env F c value'
      ([Expr.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) t1) t2))
          (.const bn [])],
       Expr.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.natName [])) lhs) rhs) proof)
    (ht1 : dmNatFrag (dmBinNames c) (dmUnNames c) t1 = true)
    (ht2 : dmNatFrag (dmBinNames c) (dmUnNames c) t2 = true)
    (hlhs : dmNatFrag (dmBinNames c) (dmUnNames c) lhs = true)
    (hrhs : dmNatFrag (dmBinNames c) (dmUnNames c) rhs = true)
    (hfired : SetTheory.app (SetTheory.app
        (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy t1))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy t2)
      = interp V ρ (dmLeaf mp.base2 c A ψ bn)) :
    dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
        xx yy lhs
      = dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
        xx yy rhs := by
  -- the proof blob's syntax, off the certificate guard
  have hg := hfacts.1
  simp only [divModCertGuard, Bool.and_eq_true,
    Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨hpb, hpf⟩, -⟩, -⟩, -⟩, -⟩ := hg
  -- the guard spine, at the two depths it is read
  obtain ⟨H1a, hG2, hG2f⟩ := dmGuardSpine fr heqlaw hbn ht1 ht2 ρ 2
  obtain ⟨G4, hG4, hG4f⟩ := dmGuardSpine fr heqlaw hbn ht1 ht2 ρ 4
  obtain ⟨hl1, hb1, hw1⟩ := dmNatFrag_syntax t1 ht1
  obtain ⟨hl2, hb2, hw2⟩ := dmNatFrag_syntax t2 ht2
  -- the hypothesis type's syntax
  have hlH : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
      (.app (.app (.const ConLeche.natBleName []) t1) t2))
      (.const bn [])) = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.append_nil, List.all_append, Bool.and_eq_true]
    exact ⟨hl1, hl2⟩
  have hwH : Expr.WScoped 2 (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
        (.const bn []))) :=
    wscoped_substConst0 fr.valueNoFvar _
      (dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar
          (e := .const eqName [.succ .zero]) rfl)
        (Expr.WScoped.of_not_hasFvar
          (e := .const ConLeche.boolName []) rfl))
        (dmApp_wscoped (dmApp_wscoped
          (Expr.WScoped.of_not_hasFvar
            (e := .const ConLeche.natBleName []) rfl)
          (hw1 2 (by omega))) (hw2 2 (by omega))))
        (Expr.WScoped.of_not_hasFvar (e := .const bn []) rfl))
  have hbH : (Expr.substConst0 c value' (.app (.app (.app
      (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
      (.app (.app (.const ConLeche.natBleName []) t1) t2))
      (.const bn []))).looseBVarsBounded 0 = true :=
    looseBVarsBounded_substConst0 fr.valueBounded _
      (by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨⟨⟨trivial, trivial⟩, ⟨⟨trivial, hb1⟩, hb2⟩⟩, trivial⟩)
  -- the depth-4 reading of the hypothesis type is the entry, lifted
  have hlift : denoteMeta mp.base2.acval env ψ 4 (Expr.substConst0 c
      value' (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
        (.const bn []))) = some (H1a.liftN 2 0) :=
    denotePLift (n := 2) mp.base2.acval_closed hwH hG2
  obtain rfl : G4 = H1a.liftN 2 0 :=
    Option.some.inj (hG4.symm.trans hlift)
  -- the telescope and its satisfying valuation
  have hnatCl : ∀ ρ' ρ'' : Nat → V,
      interp V ρ' (mp.base2.acval ConLeche.natName ψ)
        = interp V ρ'' (mp.base2.acval ConLeche.natName ψ) :=
    fun ρ' ρ'' => acval_interp_closedC mp.base2 _ ψ ρ' ρ''
  have hshift : (fun j => cons xx (cons pt (cons yy (cons xx ρ)))
      (j + 1 + 1)) = cons yy (cons xx ρ) := funext fun _ => rfl
  have hsat : Sat V [mp.base2.acval ConLeche.natName ψ, H1a,
      mp.base2.acval ConLeche.natName ψ,
      mp.base2.acval ConLeche.natName ψ]
      (cons xx (cons pt (cons yy (cons xx ρ)))) := by
    intro i Aa hi
    match i with
    | 0 =>
      obtain rfl : mp.base2.acval ConLeche.natName ψ = Aa := by
        simpa using hi
      show xx ∈ˢ interp V _ (mp.base2.acval ConLeche.natName ψ)
      rw [hnatCl _ ρ]
      exact hxx
    | 1 =>
      obtain rfl : H1a = Aa := by simpa using hi
      show pt ∈ˢ interp V (fun j => cons xx (cons pt
        (cons yy (cons xx ρ))) (j + 1 + 1)) H1a
      rw [hshift]
      obtain ⟨-, hval⟩ := hG2f (cons yy (cons xx ρ))
        (by show xx ∈ˢ _; rw [hnatCl _ ρ]; exact hxx)
        (by show yy ∈ˢ _; rw [hnatCl _ ρ]; exact hyy)
      rw [hval,
        show (fun n => interp V (cons yy (cons xx ρ))
            (dmLeaf mp.base2 c A ψ n))
          = fun n => interp V ρ (dmLeaf mp.base2 c A ψ n) from
          funext fun n => fr.leafClosed n _ ρ,
        fr.leafClosed ConLeche.natBleName _ ρ,
        fr.leafClosed bn _ ρ]
      show pt ∈ˢ eqv (SetTheory.app (SetTheory.app
          (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy t1))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy t2))
        (interp V ρ (dmLeaf mp.base2 c A ψ bn))
      rw [hfired]
      exact pt_mem_eqv_self _
    | 2 =>
      obtain rfl : mp.base2.acval ConLeche.natName ψ = Aa := by
        simpa using hi
      show yy ∈ˢ interp V _ (mp.base2.acval ConLeche.natName ψ)
      rw [hnatCl _ ρ]
      exact hyy
    | 3 =>
      obtain rfl : mp.base2.acval ConLeche.natName ψ = Aa := by
        simpa using hi
      show xx ∈ˢ interp V _ (mp.base2.acval ConLeche.natName ψ)
      rw [hnatCl _ ρ]
      exact hxx
    | n + 4 => simp at hi
  -- the applied proof's frame
  obtain ⟨hWA, hBA⟩ := dmApplied1_frame hpf hpb hwH
  have hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      [Expr.substConst0 c value' (.app (.app (.app
        (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
        (.const bn []))]) := by
    intro lf hlf
    rcases divModCertApplied_mem1 hpf hlf with rfl | rfl | rfl | hm
    · rfl
    · rfl
    · exact hbH
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 fr.valueNoFvar hlH) lf hm
  have hCA : CtxOk mp.base2 ψ 4
      [mp.base2.acval ConLeche.natName ψ, H1a,
        mp.base2.acval ConLeche.natName ψ,
        mp.base2.acval ConLeche.natName ψ]
      (divModCertApplied (Expr.substConstAll c value' proof)
        [Expr.substConst0 c value' (.app (.app (.app
          (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) t1) t2))
          (.const bn []))]) := by
    have hself : ∀ k : Nat,
        (mp.base2.acval ConLeche.natName ψ).liftN k 0
          = mp.base2.acval ConLeche.natName ψ := fun k =>
      AnnotTerm.liftN_eq_self _
        (by rw [mp.base2.acval_erase]
            exact mp.base2.cval_closed ConLeche.natName ψ) k
    have hnatSlot : ∀ i k : Nat,
        [mp.base2.acval ConLeche.natName ψ, H1a,
          mp.base2.acval ConLeche.natName ψ,
          mp.base2.acval ConLeche.natName ψ].getD i default
          = mp.base2.acval ConLeche.natName ψ →
        ∃ tya, denoteMeta mp.base2.acval env ψ 4
            (Expr.const ConLeche.natName []) = some tya ∧
          tya = ([mp.base2.acval ConLeche.natName ψ, H1a,
            mp.base2.acval ConLeche.natName ψ,
            mp.base2.acval ConLeche.natName ψ].getD i default).liftN k 0
            ∧ ∀ ρ' : Nat → V,
              Sat V [mp.base2.acval ConLeche.natName ψ, H1a,
                mp.base2.acval ConLeche.natName ψ,
                mp.base2.acval ConLeche.natName ψ] ρ' →
              WellDenotedV V ρ' tya := by
      intro i k hi
      exact ⟨_, fr.readNat 4, by rw [hi, hself k],
        fun ρ' _ => ⟨mp.base2.acval_wellDenoted _ _ ρ',
          mp.acval_validV _ _ ρ'⟩⟩
    refine ctxOk_pinnedLift rfl (fun l hl => ?_)
    rcases divModCertApplied_mem1 hpf hl with rfl | rfl | rfl | hm
    · exact ⟨by omega, trivial, hnatSlot 3 4 rfl⟩
    · exact ⟨by omega, trivial, hnatSlot 2 3 rfl⟩
    · refine ⟨by omega, Expr.WScoped.fvarsBelow hwH, _, hlift, rfl,
        fun ρ' hρ' => ?_⟩
      obtain ⟨hx', hy'⟩ := dmSat_slots rfl rfl rfl hρ' ρ
      exact (hG4f ρ' hx' hy').1
    · rw [fvarLeaves_substConst0 (n := c) fr.valueNoFvar _] at hm
      rcases dmLeavesOk_mem hlH hm with rfl | rfl
      · exact ⟨by omega, trivial, hnatSlot 3 4 rfl⟩
      · exact ⟨by omega, trivial, hnatSlot 2 3 rfl⟩
  -- the statement
  have hres := dmStmtEq fr heqlaw hacc hreads hinfC hdeC hfacts
    hlhs hrhs rfl rfl rfl hWA hBA hLA hCA
    (cons xx (cons pt (cons yy (cons xx ρ)))) hsat
  rw [show (fun n => interp V (cons xx (cons pt (cons yy
        (cons xx ρ)))) (dmLeaf mp.base2 c A ψ n))
      = fun n => interp V ρ (dmLeaf mp.base2 c A ψ n) from
      funext fun n => fr.leafClosed n _ ρ] at hres
  exact hres

/-- **A two-hypothesis guarded clause, discharged** —
`Nat.div`/`Nat.mod`'s recursive certificate.  The second hypothesis's
type is stated one binder deeper, so its telescope entry is its
*depth-3* reading. -/
theorem dmClause2 {F : Nat} {mp : EnvModelM V μ env} {c : Name}
    {A : (Name → Nat) → AnnotTerm} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrame mp c A value' ψ) (heqlaw : EqLaw mp.base2)
    (hacc : ∀ {d : Nat} {e t : Expr},
      ConLeche.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta mp.base2.acval env ψ d e = some ea)
    (hreads : InferReads mp.base2 μ ψ F)
    (hinfC : InferClaim μ mp.base2 ψ F)
    (hdeC : DefEqClaim μ mp.base2 ψ F)
    (ρ : Nat → V) {xx yy : V}
    (hxx : xx ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ))
    (hyy : yy ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ))
    {t1 t2 s1 s2 lhs rhs proof : Expr} {bn cn : Name}
    (hbn : bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName)
    (hcn : cn = ConLeche.boolTrueName ∨ cn = ConLeche.boolFalseName)
    (hfacts : CertRunFacts μ env F c value'
      ([Expr.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) t1) t2))
          (.const bn []),
        Expr.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) s1) s2))
          (.const cn [])],
       Expr.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.natName [])) lhs) rhs) proof)
    (ht1 : dmNatFrag (dmBinNames c) (dmUnNames c) t1 = true)
    (ht2 : dmNatFrag (dmBinNames c) (dmUnNames c) t2 = true)
    (hs1 : dmNatFrag (dmBinNames c) (dmUnNames c) s1 = true)
    (hs2 : dmNatFrag (dmBinNames c) (dmUnNames c) s2 = true)
    (hlhs : dmNatFrag (dmBinNames c) (dmUnNames c) lhs = true)
    (hrhs : dmNatFrag (dmBinNames c) (dmUnNames c) rhs = true)
    (hfired1 : SetTheory.app (SetTheory.app
        (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy t1))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy t2)
      = interp V ρ (dmLeaf mp.base2 c A ψ bn))
    (hfired2 : SetTheory.app (SetTheory.app
        (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy s1))
        (dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
          xx yy s2)
      = interp V ρ (dmLeaf mp.base2 c A ψ cn)) :
    dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
        xx yy lhs
      = dmEvalV V (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
        xx yy rhs := by
  have hg := hfacts.1
  simp only [divModCertGuard, Bool.and_eq_true,
    Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨hpb, hpf⟩, -⟩, -⟩, -⟩, -⟩ := hg
  obtain ⟨H1a, hG2, hG2f⟩ := dmGuardSpine fr heqlaw hbn ht1 ht2 ρ 2
  obtain ⟨G4, hG4, hG4f⟩ := dmGuardSpine fr heqlaw hbn ht1 ht2 ρ 4
  obtain ⟨H2a, hK3, hK3f⟩ := dmGuardSpine fr heqlaw hcn hs1 hs2 ρ 3
  obtain ⟨K4, hK4, hK4f⟩ := dmGuardSpine fr heqlaw hcn hs1 hs2 ρ 4
  obtain ⟨hl1, hb1, hw1⟩ := dmNatFrag_syntax t1 ht1
  obtain ⟨hl2, hb2, hw2⟩ := dmNatFrag_syntax t2 ht2
  obtain ⟨hm1, hc1, hv1⟩ := dmNatFrag_syntax s1 hs1
  obtain ⟨hm2, hc2, hv2⟩ := dmNatFrag_syntax s2 hs2
  -- both hypothesis types' syntax
  have hlH : ∀ {u1 u2 : Expr} {b : Name},
      dmLeavesOk u1 = true → dmLeavesOk u2 = true →
      dmLeavesOk (Expr.app (.app (.app
        (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) u1) u2))
        (.const b [])) = true := by
    intro u1 u2 b h1 h2
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.append_nil, List.all_append, Bool.and_eq_true]
    exact ⟨h1, h2⟩
  have hwH : ∀ {u1 u2 : Expr} {b : Name} (d : Nat), 2 ≤ d →
      (∀ d' : Nat, 2 ≤ d' → Expr.WScoped d' u1) →
      (∀ d' : Nat, 2 ≤ d' → Expr.WScoped d' u2) →
      Expr.WScoped d (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero])
          (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) u1) u2))
          (.const b []))) := by
    intro u1 u2 b d hd hu1 hu2
    exact wscoped_substConst0 fr.valueNoFvar _
      (dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar
          (e := .const eqName [.succ .zero]) rfl)
        (Expr.WScoped.of_not_hasFvar
          (e := .const ConLeche.boolName []) rfl))
        (dmApp_wscoped (dmApp_wscoped
          (Expr.WScoped.of_not_hasFvar
            (e := .const ConLeche.natBleName []) rfl)
          (hu1 d hd)) (hu2 d hd)))
        (Expr.WScoped.of_not_hasFvar (e := .const b []) rfl))
  have hbH : ∀ {u1 u2 : Expr} {b : Name},
      u1.looseBVarsBounded 0 = true → u2.looseBVarsBounded 0 = true →
      (Expr.substConst0 c value' (.app (.app (.app
        (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) u1) u2))
        (.const b []))).looseBVarsBounded 0 = true := by
    intro u1 u2 b h1 h2
    exact looseBVarsBounded_substConst0 fr.valueBounded _
      (by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨⟨⟨trivial, trivial⟩, ⟨⟨trivial, h1⟩, h2⟩⟩, trivial⟩)
  -- the two entries, lifted to depth 4
  have hlift1 : denoteMeta mp.base2.acval env ψ 4 (Expr.substConst0 c
      value' (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
        (.const bn []))) = some (H1a.liftN 2 0) :=
    denotePLift (n := 2) mp.base2.acval_closed
      (hwH 2 (by omega) hw1 hw2) hG2
  have hlift2 : denoteMeta mp.base2.acval env ψ 4 (Expr.substConst0 c
      value' (.app (.app (.app (.const eqName [.succ .zero])
        (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) s1) s2))
        (.const cn []))) = some (H2a.liftN 1 0) :=
    denotePLift (n := 1) mp.base2.acval_closed
      (hwH 3 (by omega) hv1 hv2) hK3
  obtain rfl : G4 = H1a.liftN 2 0 :=
    Option.some.inj (hG4.symm.trans hlift1)
  obtain rfl : K4 = H2a.liftN 1 0 :=
    Option.some.inj (hK4.symm.trans hlift2)
  have hnatCl : ∀ ρ' ρ'' : Nat → V,
      interp V ρ' (mp.base2.acval ConLeche.natName ψ)
        = interp V ρ'' (mp.base2.acval ConLeche.natName ψ) :=
    fun ρ' ρ'' => acval_interp_closedC mp.base2 _ ψ ρ' ρ''
  have hsat : Sat V [H2a, H1a,
      mp.base2.acval ConLeche.natName ψ,
      mp.base2.acval ConLeche.natName ψ]
      (cons pt (cons pt (cons yy (cons xx ρ)))) := by
    intro i Aa hi
    match i with
    | 0 =>
      obtain rfl : H2a = Aa := by simpa using hi
      show pt ∈ˢ interp V (fun j => cons pt (cons pt
        (cons yy (cons xx ρ))) (j + 0 + 1)) H2a
      rw [show (fun j => cons pt (cons pt (cons yy (cons xx ρ)))
          (j + 0 + 1)) = cons pt (cons yy (cons xx ρ)) from
        funext fun _ => rfl]
      obtain ⟨-, hval⟩ := hK3f (cons pt (cons yy (cons xx ρ)))
        (by show xx ∈ˢ _; rw [hnatCl _ ρ]; exact hxx)
        (by show yy ∈ˢ _; rw [hnatCl _ ρ]; exact hyy)
      rw [hval,
        show (fun n => interp V (cons pt (cons yy (cons xx ρ)))
            (dmLeaf mp.base2 c A ψ n))
          = fun n => interp V ρ (dmLeaf mp.base2 c A ψ n) from
          funext fun n => fr.leafClosed n _ ρ,
        fr.leafClosed ConLeche.natBleName _ ρ,
        fr.leafClosed cn _ ρ]
      show pt ∈ˢ eqv (SetTheory.app (SetTheory.app
          (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy s1))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy s2))
        (interp V ρ (dmLeaf mp.base2 c A ψ cn))
      rw [hfired2]
      exact pt_mem_eqv_self _
    | 1 =>
      obtain rfl : H1a = Aa := by simpa using hi
      show pt ∈ˢ interp V (fun j => cons pt (cons pt
        (cons yy (cons xx ρ))) (j + 1 + 1)) H1a
      rw [show (fun j => cons pt (cons pt (cons yy (cons xx ρ)))
          (j + 1 + 1)) = cons yy (cons xx ρ) from
        funext fun _ => rfl]
      obtain ⟨-, hval⟩ := hG2f (cons yy (cons xx ρ))
        (by show xx ∈ˢ _; rw [hnatCl _ ρ]; exact hxx)
        (by show yy ∈ˢ _; rw [hnatCl _ ρ]; exact hyy)
      rw [hval,
        show (fun n => interp V (cons yy (cons xx ρ))
            (dmLeaf mp.base2 c A ψ n))
          = fun n => interp V ρ (dmLeaf mp.base2 c A ψ n) from
          funext fun n => fr.leafClosed n _ ρ,
        fr.leafClosed ConLeche.natBleName _ ρ,
        fr.leafClosed bn _ ρ]
      show pt ∈ˢ eqv (SetTheory.app (SetTheory.app
          (interp V ρ (dmLeaf mp.base2 c A ψ ConLeche.natBleName))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy t1))
          (dmEvalV V
            (fun n => interp V ρ (dmLeaf mp.base2 c A ψ n))
            xx yy t2))
        (interp V ρ (dmLeaf mp.base2 c A ψ bn))
      rw [hfired1]
      exact pt_mem_eqv_self _
    | 2 =>
      obtain rfl : mp.base2.acval ConLeche.natName ψ = Aa := by
        simpa using hi
      show yy ∈ˢ interp V _ (mp.base2.acval ConLeche.natName ψ)
      rw [hnatCl _ ρ]
      exact hyy
    | 3 =>
      obtain rfl : mp.base2.acval ConLeche.natName ψ = Aa := by
        simpa using hi
      show xx ∈ˢ interp V _ (mp.base2.acval ConLeche.natName ψ)
      rw [hnatCl _ ρ]
      exact hxx
    | n + 4 => simp at hi
  obtain ⟨hWA, hBA⟩ := dmApplied2_frame hpf hpb
    (hwH 2 (by omega) hw1 hw2) (hwH 3 (by omega) hv1 hv2)
  have hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      [Expr.substConst0 c value' (.app (.app (.app
        (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) t1) t2))
        (.const bn [])),
       Expr.substConst0 c value' (.app (.app (.app
        (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
        (.app (.app (.const ConLeche.natBleName []) s1) s2))
        (.const cn []))]) := by
    intro lf hlf
    rcases divModCertApplied_mem2 hpf hlf with
      rfl | rfl | rfl | hm | rfl | hm
    · rfl
    · rfl
    · exact hbH hb1 hb2
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 fr.valueNoFvar (hlH hl1 hl2)) lf hm
    · exact hbH hc1 hc2
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 fr.valueNoFvar (hlH hm1 hm2)) lf hm
  have hself : ∀ k : Nat,
      (mp.base2.acval ConLeche.natName ψ).liftN k 0
        = mp.base2.acval ConLeche.natName ψ := fun k =>
    AnnotTerm.liftN_eq_self _
      (by rw [mp.base2.acval_erase]
          exact mp.base2.cval_closed ConLeche.natName ψ) k
  have hnatSlot : ∀ i k : Nat,
      [H2a, H1a, mp.base2.acval ConLeche.natName ψ,
        mp.base2.acval ConLeche.natName ψ].getD i default
        = mp.base2.acval ConLeche.natName ψ →
      ∃ tya, denoteMeta mp.base2.acval env ψ 4
          (Expr.const ConLeche.natName []) = some tya ∧
        tya = ([H2a, H1a, mp.base2.acval ConLeche.natName ψ,
          mp.base2.acval ConLeche.natName ψ].getD i default).liftN k 0
          ∧ ∀ ρ' : Nat → V,
            Sat V [H2a, H1a, mp.base2.acval ConLeche.natName ψ,
              mp.base2.acval ConLeche.natName ψ] ρ' →
            WellDenotedV V ρ' tya := by
    intro i k hi
    exact ⟨_, fr.readNat 4, by rw [hi, hself k],
      fun ρ' _ => ⟨mp.base2.acval_wellDenoted _ _ ρ',
        mp.acval_validV _ _ ρ'⟩⟩
  have hCA : CtxOk mp.base2 ψ 4
      [H2a, H1a, mp.base2.acval ConLeche.natName ψ,
        mp.base2.acval ConLeche.natName ψ]
      (divModCertApplied (Expr.substConstAll c value' proof)
        [Expr.substConst0 c value' (.app (.app (.app
          (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) t1) t2))
          (.const bn [])),
         Expr.substConst0 c value' (.app (.app (.app
          (.const eqName [.succ .zero]) (.const ConLeche.boolName []))
          (.app (.app (.const ConLeche.natBleName []) s1) s2))
          (.const cn []))]) := by
    refine ctxOk_pinnedLift rfl (fun l hl => ?_)
    rcases divModCertApplied_mem2 hpf hl with
      rfl | rfl | rfl | hm | rfl | hm
    · exact ⟨by omega, trivial, hnatSlot 3 4 rfl⟩
    · exact ⟨by omega, trivial, hnatSlot 2 3 rfl⟩
    · refine ⟨by omega,
        Expr.WScoped.fvarsBelow (hwH 2 (by omega) hw1 hw2), _,
        hlift1, rfl, fun ρ' hρ' => ?_⟩
      obtain ⟨hx', hy'⟩ := dmSat_slots rfl rfl rfl hρ' ρ
      exact (hG4f ρ' hx' hy').1
    · rw [fvarLeaves_substConst0 (n := c) fr.valueNoFvar _] at hm
      rcases dmLeavesOk_mem (hlH hl1 hl2) hm with rfl | rfl
      · exact ⟨by omega, trivial, hnatSlot 3 4 rfl⟩
      · exact ⟨by omega, trivial, hnatSlot 2 3 rfl⟩
    · refine ⟨by omega,
        Expr.WScoped.fvarsBelow (hwH 3 (by omega) hv1 hv2), _,
        hlift2, rfl, fun ρ' hρ' => ?_⟩
      obtain ⟨hx', hy'⟩ := dmSat_slots rfl rfl rfl hρ' ρ
      exact (hK4f ρ' hx' hy').1
    · rw [fvarLeaves_substConst0 (n := c) fr.valueNoFvar _] at hm
      rcases dmLeavesOk_mem (hlH hm1 hm2) hm with rfl | rfl
      · exact ⟨by omega, trivial, hnatSlot 3 4 rfl⟩
      · exact ⟨by omega, trivial, hnatSlot 2 3 rfl⟩
  have hres := dmStmtEq fr heqlaw hacc hreads hinfC hdeC hfacts
    hlhs hrhs rfl rfl rfl hWA hBA hLA hCA
    (cons pt (cons pt (cons yy (cons xx ρ)))) hsat
  rw [show (fun n => interp V (cons pt (cons pt (cons yy
        (cons xx ρ)))) (dmLeaf mp.base2 c A ψ n))
      = fun n => interp V ρ (dmLeaf mp.base2 c A ψ n) from
      funext fun n => fr.leafClosed n _ ρ] at hres
  exact hres

/-! ## The frame, assembled from the guards

`dmFrameS`'s mirror.  Everything is read off `divModEnvGuard` at the
*extension* and descended to the prefix, except the operation's own
head, which comes through the value front door's products the harvest
already holds (`hmemA`/`hTok`) — `c` is not stored in `env`; it is
what the declaration is installing. -/

set_option maxHeartbeats 1600000 in
/-- **The div/mod certificate frame at `interp`, assembled.** -/
theorem dmFrame_of {mp : EnvModelM V μ env} {c : Name}
    {lps : List Name} {type' value' : Expr} {hint : ReducibilityHint}
    (hmem : c ∈ ConLeche.natDivModNames)
    (hgenv : ConLeche.divModEnvGuard
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env) c
      = true)
    {A Ta : (Name → Nat) → AnnotTerm}
    (hA : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hTa : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Ta ψ))
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ))
    (ψ : Name → Nat) :
    DmFrame mp c A value' ψ := by
  obtain ⟨hnog, hdeps, hEq2, hbT2, hbF2⟩ :=
    ConLeche.divModEnvGuard_inv hgenv
  obtain ⟨hs, hdeps', hbool⟩ := ConLeche.natOpGuard_inv hnog
  have hdepAll := List.all_eq_true.mp hdeps
  obtain ⟨hnN0, hnZ0, hnS0, hnB0, hnT0, hnF0, hnE0, -, -, -, -⟩ :=
    ConLeche.natDivModNames_ne_env hmem
  have hnN : ConLeche.natName ≠ c := hnN0.symm
  have hnZ : ConLeche.natZeroName ≠ c := hnZ0.symm
  have hnS : ConLeche.natSuccName ≠ c := hnS0.symm
  have hnB : ConLeche.boolName ≠ c := hnB0.symm
  have hnT : ConLeche.boolTrueName ≠ c := hnT0.symm
  have hnF : ConLeche.boolFalseName ≠ c := hnF0.symm
  have hnE : eqName ≠ c := hnE0.symm
  have hdown : ∀ (n : Name) (ci : ConstantInfo), n ≠ c →
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩
        : Env).find? n = some ci → env.find? n = some ci := by
    intro n ci hnn hf
    rwa [ConLeche.Env.find?_cons, if_neg (fun hh => hnn hh.symm)] at hf
  -- the numeral heads, at the prefix
  obtain ⟨cvN, capsN, cv0, i0, j0, cv1, i1, j1, hfN2, hfZ2, hfS2,
    hlpN, hlpZ, hlpS, htyN, htyZ, mbS, htyS⟩ :=
    ConLeche.natLitSupported_inv hs
  have hfN : env.find? ConLeche.natName
      = some (.indInfo cvN capsN) := hdown _ _ hnN hfN2
  have hfZ : env.find? ConLeche.natZeroName
      = some (.ctorInfo cv0 i0 j0) := hdown _ _ hnZ hfZ2
  have hfS : env.find? ConLeche.natSuccName
      = some (.ctorInfo cv1 i1 j1) := hdown _ _ hnS hfS2
  -- `Nat.ble` is a dependency of every pin-certified operation, and it
  -- is where `Bool` enters
  have hbleDep : ConLeche.natBleName ∈ ConLeche.natOpDeps c := by
    simp only [ConLeche.natDivModNames, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  have hbleNe : ConLeche.natBleName ≠ c := by
    simp only [ConLeche.natDivModNames, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  have hstoredDep : ∀ n ∈ ConLeche.natOpDeps c, n ≠ c →
      ∃ cvn vn hn, env.find? n = some (.defnInfo cvn vn hn) ∧
        cvn.levelParams = [] ∧
        ConLeche.natOpTyPinned
          (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩
            : Env) n cvn.type = true := by
    intro n hn hnc
    obtain ⟨cvn, vn, hintn, hfn2, hpinn⟩ :=
      ConLeche.natOpStoredOk_tyPinned (hdepAll n hn)
    have hd := hdepAll n hn
    unfold ConLeche.natOpStoredOk at hd
    rw [hfn2] at hd
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hd
    exact ⟨cvn, vn, hintn, hdown _ _ hnc hfn2, hd.1, hpinn⟩
  obtain ⟨cvb, vb, hintb, hfble, hlpble, hpinb⟩ :=
    hstoredDep _ hbleDep hbleNe
  obtain ⟨mbb, mbb2, codb, htyb, hcodb⟩ :=
    natOpTyPinned_binaryE (by decide) hpinb
  obtain ⟨rfl, ciB, hfB2, hlpB, htyB⟩ := natOpCod_ble hcodb
  have hfB : env.find? ConLeche.boolName = some ciB :=
    hdown _ _ hnB hfB2
  -- the `Bool` constructors
  obtain ⟨⟨ciT, hfT2, hlpT⟩, ⟨ciF, hfF2, hlpF⟩⟩ :=
    hbool (Or.inr (Or.inr (by simpa using hmem)))
  obtain ⟨ciT', hfT2', htyT'⟩ := hbT2
  obtain ⟨ciF', hfF2', htyF'⟩ := hbF2
  have htyT : ciT.toConstantVal.type = .const ConLeche.boolName [] := by
    rw [← show ciT' = ciT from
      Option.some.inj (hfT2'.symm.trans hfT2)]
    exact htyT'
  have htyF : ciF.toConstantVal.type = .const ConLeche.boolName [] := by
    rw [← show ciF' = ciF from
      Option.some.inj (hfF2'.symm.trans hfF2)]
    exact htyF'
  have hfT : env.find? ConLeche.boolTrueName = some ciT :=
    hdown _ _ hnT hfT2
  have hfF : env.find? ConLeche.boolFalseName = some ciF :=
    hdown _ _ hnF hfF2
  -- the operation's own pinned type
  have hselfDep : c ∈ ConLeche.natOpDeps c := by
    simp only [ConLeche.natDivModNames, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  obtain ⟨cvS2, vS2, hS2, hfS2', hpinS2⟩ :=
    ConLeche.natOpStoredOk_tyPinned (hdepAll _ hselfDep)
  have htyS2 : cvS2.type = type' := by
    rw [ConLeche.Env.find?_cons] at hfS2'
    rw [if_pos (show (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
      hint).name = c from rfl)] at hfS2'
    obtain ⟨h1, -, -⟩ :=
      ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj hfS2')
    rw [← h1]
  -- no pin-certified operation is a comparison
  have hnotcmp : (decide (c = ConLeche.natBeqName)
      || decide (c = ConLeche.natBleName)) = false := by
    simp only [ConLeche.natDivModNames, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  have hnotpred : (decide (c = ConLeche.natPredName)) = false := by
    simp only [ConLeche.natDivModNames, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  -- the leaves' closedness and grading
  have hAerCl : ∀ ψ' : Name → Nat, Term.Closed (A ψ').erase :=
    fun ψ' => denote_closed mp.base2.cval_closed hvf' hbv'
      (denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ'))
  have hleafOk : ∀ (n : Name) (ρ : Nat → V),
      WellDenotedV V ρ (dmLeaf mp.base2 c A ψ n) := by
    intro n ρ
    by_cases hn : n = c
    · subst hn
      rw [dmLeaf, show acvalWith mp.base2.acval n A n = A
        from acvalWith_self]
      exact hAok ψ ρ
    · rw [dmLeaf, show acvalWith mp.base2.acval c A n
        = mp.base2.acval n from acvalWith_ne hn]
      exact ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩
  have hleafClosed : ∀ (n : Name) (ρ ρ' : Nat → V),
      interp V ρ (dmLeaf mp.base2 c A ψ n)
        = interp V ρ' (dmLeaf mp.base2 c A ψ n) := by
    intro n ρ ρ'
    by_cases hn : n = c
    · subst hn
      rw [dmLeaf, show acvalWith mp.base2.acval n A n = A
        from acvalWith_self]
      exact interp_closed V (hAerCl ψ) ρ ρ'
    · rw [dmLeaf, show acvalWith mp.base2.acval c A n
        = mp.base2.acval n from acvalWith_ne hn]
      exact acval_interp_closedC mp.base2 _ ψ ρ ρ'
  -- a stored constant's `.sort 1` type gives its universe membership
  have huniv : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci →
      ci.toConstantVal.type = .sort (.succ .zero) →
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval n ψ) ∈ˢ (univ 1 : V) := by
    intro n ci hf hty ρ
    have hta : denoteMeta mp.base2.acval env ψ 0 ci.toConstantVal.type
        = some (.sort 1) := by
      rw [hty]
      exact denoteMeta_sort _ _ _
    have h := mp.mem_type ci (ConLeche.Semantics.Env.find?_mem hf)
      ψ _ hta ρ
    rw [show ci.name = n from ConLeche.Semantics.Env.find?_name hf,
      interp_sort] at h
    exact h
  -- a stored constant whose type is a stored level-mono constant
  have hmemC : ∀ (n t : Name) (ci ti : ConstantInfo),
      env.find? n = some ci → env.find? t = some ti →
      ti.toConstantVal.levelParams = [] →
      ci.toConstantVal.type = .const t [] →
      ∀ ρ : Nat → V, interp V ρ (mp.base2.acval n ψ)
        ∈ˢ interp V ρ (mp.base2.acval t ψ) := by
    intro n t ci ti hf hft hlpt hty ρ
    have hta : denoteMeta mp.base2.acval env ψ 0 ci.toConstantVal.type
        = some (mp.base2.acval t ψ) := by
      rw [hty]
      exact denoteMeta_levelless_const hft hlpt
    have h := mp.mem_type ci (ConLeche.Semantics.Env.find?_mem hf)
      ψ _ hta ρ
    rwa [show ci.name = n from ConLeche.Semantics.Env.find?_name hf] at h
  refine
    { eqStored := hdown _ _ hnE hEq2
      natNe := hnN
      boolNe := hnB
      selfRead := fun d => denoteMeta_depth_of_closed
        mp.base2.acval_closed hvf' (hAclosed ψ) (hA ψ) d
      valueNoFvar := hvf'
      valueBounded := hbv'
      stored := ?stored
      leafOk := hleafOk
      leafClosed := hleafClosed
      natU := huniv _ _ hfN htyN
      boolU := huniv _ _ hfB htyB
      binHead := ?binHead
      unHead := ?unHead
      bleHead := ?bleHead
      zeroMem := ?zeroMem
      boolCtorMem := ?boolCtorMem }
  case stored =>
    intro n hn
    by_cases hnc : n = c
    · exact Or.inl hnc
    refine Or.inr ⟨hnc, ?_⟩
    simp only [dmHeadNames, List.mem_cons, List.mem_append] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | hn
    · exact ⟨_, hfN, hlpN⟩
    · exact ⟨_, hfB, hlpB⟩
    · exact ⟨_, hfZ, hlpZ⟩
    · exact ⟨_, hfble, hlpble⟩
    · exact ⟨_, hfT, hlpT⟩
    · exact ⟨_, hfF, hlpF⟩
    · -- a recurrence dependency, or `Nat.succ`
      rcases hn with hn | hn
      · have hnd : n ∈ ConLeche.natOpDeps c :=
          (List.mem_filter.mp hn).1
        obtain ⟨cvn, vn, hintn, hfn, hlpn, -⟩ :=
          hstoredDep n hnd hnc
        exact ⟨_, hfn, hlpn⟩
      · unfold dmUnNames at hn
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hn
        subst hn
        exact ⟨_, hfS, hlpS⟩
  case bleHead =>
    intro ρ
    rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.natBleName
      = mp.base2.acval ConLeche.natBleName from acvalWith_ne hbleNe]
    exact dmBinV_of_stored mp ψ hfble htyb hfN hlpN hfB hlpB ρ
  case binHead =>
    intro n hn ρ
    obtain ⟨hnd, hfilt⟩ := List.mem_filter.mp hn
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hfilt
    obtain ⟨hnble, hnpred⟩ := hfilt
    have hnu : ¬(n = ConLeche.natPredName) := hnpred
    have hnbeqAll : ((ConLeche.natOpDeps c).all
        fun m => m != ConLeche.natBeqName) = true := by
      simp only [ConLeche.natDivModNames, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with h|h|h|h|h|h|h|h <;> (rw [h]; decide)
    have hnbeq : n ≠ ConLeche.natBeqName := by
      have := List.all_eq_true.mp hnbeqAll n hnd
      simpa using this
    have hnb : (decide (n = ConLeche.natBeqName)
        || decide (n = ConLeche.natBleName)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨hnbeq, hnble⟩
    by_cases hnc : n = c
    · -- the operation itself, through the value front door
      subst hnc
      obtain ⟨mbT, mbT2, codT, htyT2, hcodT⟩ :=
        natOpTyPinned_binaryE hnu (htyS2 ▸ hpinS2)
      have hcodN : codT = Expr.const ConLeche.natName [] := by
        unfold ConLeche.natOpCod at hcodT
        rw [if_neg (show ¬((decide (n = ConLeche.natBeqName)
          || decide (n = ConLeche.natBleName)) = true) from by
          simp [hnb])] at hcodT
        simpa using hcodT
      subst hcodN
      have hTshape := denoteMeta_pinnedBinTy (codN := ConLeche.natName)
        (mb₁ := mbT) (mb₂ := mbT2)
        mp.base2 ψ hfN hlpN hfN hlpN
      rw [← htyT2] at hTshape
      obtain heq : Ta ψ = _ :=
        Option.some.inj ((hTa ψ).symm.trans hTshape)
      rw [dmLeaf, show acvalWith mp.base2.acval n A n = A
        from acvalWith_self]
      exact dmBinV_of_parts mp.base2 (heq ▸ hmemA ψ ρ)
        (heq ▸ hTok ψ ρ)
    · obtain ⟨cvn, vn, hintn, hfn, hlpn, hpinn⟩ :=
        hstoredDep n hnd hnc
      obtain ⟨mbn, mbn2, codn, htyn, hcodn⟩ :=
        natOpTyPinned_binaryE hnu hpinn
      have hcodN : codn = Expr.const ConLeche.natName [] := by
        unfold ConLeche.natOpCod at hcodn
        rw [if_neg (show ¬((decide (n = ConLeche.natBeqName)
          || decide (n = ConLeche.natBleName)) = true) from by
          simp [hnb])] at hcodn
        simpa using hcodn
      subst hcodN
      rw [dmLeaf, show acvalWith mp.base2.acval c A n
        = mp.base2.acval n from acvalWith_ne hnc]
      exact dmBinV_of_stored mp ψ hfn htyn hfN hlpN hfN hlpN ρ
  case unHead =>
    intro n hn ρ
    have hsuccCase : n = ConLeche.natSuccName →
        DmUnV (interp V ρ (mp.base2.acval ConLeche.natName ψ))
          (interp V ρ (mp.base2.acval ConLeche.natName ψ))
          (interp V ρ (dmLeaf mp.base2 c A ψ n)) := by
      rintro rfl
      rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.natSuccName
        = mp.base2.acval ConLeche.natSuccName from acvalWith_ne hnS]
      exact dmUnV_of_stored mp ψ hfS htyS hfN hlpN hfN hlpN ρ
    unfold dmUnNames at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact hsuccCase hn
  case zeroMem =>
    intro ρ
    rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.natZeroName
      = mp.base2.acval ConLeche.natZeroName from acvalWith_ne hnZ]
    exact hmemC _ _ _ _ hfZ hfN hlpN htyZ ρ
  case boolCtorMem =>
    intro bn hbn ρ
    rcases hbn with rfl | rfl
    · rw [dmLeaf, show acvalWith mp.base2.acval c A ConLeche.boolTrueName
        = mp.base2.acval ConLeche.boolTrueName from acvalWith_ne hnT]
      exact hmemC _ _ _ _ hfT hfB hlpB htyT ρ
    · rw [dmLeaf,
        show acvalWith mp.base2.acval c A ConLeche.boolFalseName
        = mp.base2.acval ConLeche.boolFalseName from acvalWith_ne hnF]
      exact hmemC _ _ _ _ hfF hfB hlpB htyF ρ

/-! ## `DivMod` at the operation's own install

The nine clause blocks.  Each denotes its statement's two sides
through the graded walk, reads the equation off a certificate
(`dmClause1`/`dmClause2`), and matches it against `DivModClausesV` —
where the match is definitional, because `dmEvalV` computes the same
`app`-chain. -/

set_option maxHeartbeats 3200000 in
/-- **`DivMod` at the operation's own install** — the
run-certificate conversion for the WF-recursive family. -/
theorem divMod_install {F : Nat} (mp : EnvModelM V μ env)
    {φ : Name → Nat} (hprev : DivMod mp.base2 φ)
    (heqlaw : EqLaw mp.base2)
    (hacc : ∀ {d : Nat} {e t : Expr},
      ConLeche.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta mp.base2.acval env φ d e = some ea)
    (hreads : InferReads mp.base2 μ φ F)
    (hinfC : InferClaim μ mp.base2 φ F)
    (hdeC : DefEqClaim μ mp.base2 φ F)
    {c : Name} {lps : List Name} {type' value' : Expr}
    {hint : ReducibilityHint}
    (hcmem : c ∈ ConLeche.natDivModNames)
    (hfresh : env.find? c = none)
    (hgenv : ConLeche.divModEnvGuard
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env) c
      = true)
    {ps : ConLeche.NatOpPinSet}
    (hcerts : ConLeche.checkDivModCerts (m := ConLeche.CheckM)
      (ConLeche.fueledOps μ F) env c value'
      (ConLeche.divModCertStmts c) (ConLeche.divModCertProofs ps c)
      = .ok true)
    {A Ta : (Name → Nat) → AnnotTerm}
    (hA : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hTa : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Ta ψ))
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ))
    (m₂ : EnvModel V
      ⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c A) :
    DivMod m₂ φ := by
  intro cq hcqN cv' v' hint' hf₂
  by_cases hne : cq = c
  case neg =>
    exact divMod_entry_cons hprev
      (c₀ := .defnInfo ⟨c, lps, type'⟩ value' hint)
      (show env.find? (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name = none from hfresh) m₂ hac hcqN
      (show cq ≠ (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name from hne) hf₂
  subst hne
  clear hf₂ hcqN
  refine ⟨(ConLeche.divModEnvGuard_inv hgenv).1, fun ρ x y hx hy => ?_⟩
  have hnatNe : ConLeche.natName ≠ cq :=
    (ConLeche.natDivModNames_ne_env hcmem).1.symm
  rw [hac, show acvalWith mp.base2.acval cq A ConLeche.natName
    = mp.base2.acval ConLeche.natName from acvalWith_ne hnatNe] at hx hy
  have fr := dmFrame_of hcmem hgenv hA hAclosed hvf' hbv' hTa hTok
    hAok hmemA φ
  have hruns := ConLeche.checkDivModCerts_inv hcerts
  -- the matched variant's proof list stays opaque (task #273): the
  -- `CertRuns` destructuring below reads the STATEMENT list's shape
  -- and takes the proofs as they come
  generalize ConLeche.divModCertProofs ps cq = prs at hruns
  rw [hac]
  simp only [ConLeche.natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hcmem
  rcases hcmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (
    simp only [ConLeche.divModCertStmts, reduceIte] at hruns
    simp +decide only [DivModClausesV, if_false, if_true])
  · -- `Nat.div`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
      cases r2 with | cons f3 r3 =>
    refine ⟨fun hg1 hg2 => ?_, fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause2 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) (Or.inl rfl) f1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg1)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg2)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f3 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.mod`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
      cases r2 with | cons f3 r3 =>
    refine ⟨fun hg1 hg2 => ?_, fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause2 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) (Or.inl rfl) f1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg1)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg2)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f3 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.gcd`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.land`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.lor`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.xor`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.shiftLeft`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
  · -- `Nat.shiftRight`
    cases hruns with | cons f1 r1 => cases r1 with | cons f2 r2 =>
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inl rfl) f1 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h
    · have h := dmClause1 fr heqlaw hacc hreads hinfC hdeC ρ hx hy
        (Or.inr rfl) f2 (by decide) (by decide) (by decide)
        (by decide)
        (by simpa +decide only [dmEvalV_app, dmEvalV_const,
              dmEvalV_fvar, reduceIte, dmLeaf] using hg)
      simpa +decide only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
        reduceIte, dmLeaf] using h

end ConLeche.Model
