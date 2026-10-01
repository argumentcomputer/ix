module

public import ConLeche.Model.Inductives.StructTele
public section

/-!
# The direct structure's two parameter frames, identified (task #175 W4c, P3 module 3, part 4)

The type former's parameter telescope and the constructor's are opened
at their own variables (`checkStructCtor`), and `checkStructDomsAt`
pins the domains definitionally, binder by binder, each at its own
frame.  `paramFrames` turns the pins into the semantic identification
the leaves need: the two contexts have the same satisfying valuations
at every depth, and the corresponding entries interpret alike under
them.  With it, a fit of the former's parameter domains is a fit of
the constructor's, and the field chain graded at the constructor's
frame is graded at the former's.

Also here: the closedness of readings (`bvarsBelow_of_reading`, the
wire-side currency of `TowerWire`) and the Π-bit congruence
(`piR_congr_bit`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche ConLeche.Semantics ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetModel
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Small kit -/

/-- A reading at depth `d` of a term scoped at `d` mentions no variable
at or above `d`. -/
theorem bvarsBelow_of_reading {m : EnvModel V env} {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    {ea : AnnotTerm} (h : denoteMeta m.acval env φ d e = some ea) :
    Term.bvarsBelow d ea.erase :=
  denote_bvarsBelow m.cval_closed d e hw hb (denoteMeta_erase m.acval_erase d e h)

/-- `piR` reads its bit only through the zero test. -/
theorem piR_congr_bit {v v' : Nat} (h : v = 0 ↔ v' = 0) (A : V) (B : V → V) :
    piR v A B = piR v' A B := by
  by_cases hv : v = 0
  · rw [hv, h.mp hv]
  · rw [piR_pos hv, piR_pos (fun h' => hv (h.mpr h'))]

/-! ## The identification -/

/-- **The two parameter frames, identified** from the binder-domain
pins: at every depth `i ≤ nP` the constructor's context and the
former's have the same satisfying valuations, and below `nP` the
`i`-th entries interpret alike under the constructor's context. -/
theorem paramFrames {m : EnvModel V env} {F : Nat}
    (hc : ClaimsAt μ m φ F) {nP nF : Nat}
    {tty cty : Expr} {tfvs cfvs : List Expr} {trest crest : Expr}
    {Γt Γc : List AnnotTerm} {Rt Rc : AnnotTerm}
    (hT : Opened m φ nP tty tfvs trest Γt Rt)
    (hC : Opened m φ (nP + nF) cty cfvs crest Γc Rc)
    (hpin : ∀ i, i < nP → ∃ a b, cfvs[i]? = some a ∧ tfvs[i]? = some b ∧
      ConLeche.isDefEqCore μ env F i (Expr.fvarTypeD a) (Expr.fvarTypeD b)
        = .ok true) :
    ∀ i, i ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ ↔
        Sat V (Γt.drop (nP - i)) ρ) ∧
      (i < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - i) default)
          = interp V ρ (Γt.getD (nP - 1 - i) default)) := by
  suffices ∀ i j, j ≤ i → j ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ ↔
        Sat V (Γt.drop (nP - j)) ρ) ∧
      (j < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - j) default)
          = interp V ρ (Γt.getD (nP - 1 - j) default)) from
    fun i hi => this i i (Nat.le_refl _) hi
  intro i
  induction i with
  | zero =>
    intro j hj _
    obtain rfl : j = 0 := by omega
    refine ⟨fun ρ => ?_, fun _ ρ hρ => ?_⟩
    · rw [Nat.sub_zero, Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega),
        List.drop_eq_nil_of_le (by have := hT.len; omega)]
    · -- the head binder's pin, at the empty frame
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpin 0 (by omega)
      obtain ⟨-, hwa, hba, hLa, hleafa⟩ := hC.var 0 a ha
      obtain ⟨-, hwb, hbb, hLb, hleafb⟩ := hT.var 0 b hb
      have hCa : CtxOk m φ 0 (Γc.drop (nP + nF - 0)) (Expr.fvarTypeD a) :=
        hC.ctx (by omega) hwa hleafa
      have hCb : CtxOk m φ 0 (Γt.drop (nP - 0)) (Expr.fvarTypeD b) :=
        hT.ctx (by omega) hwb hleafb
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hT.len; omega)] at hCb
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega)] at hCa hρ
      have hda := hC.doms 0 a ha
      have hdb := hT.doms 0 b hb
      exact hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb hda hdb
        (fun ρ hρ => by
          have := hC.okΓ 0 (by omega) ρ
          rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega)] at this
          exact this hρ)
        (fun ρ hρ => by
          have := hT.okΓ 0 (by omega) ρ
          rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hT.len; omega)] at this
          exact this hρ) ρ hρ
  | succ i ih =>
    intro j hj hjn
    rcases Nat.lt_or_ge j (i + 1) with hjl | hjg
    · exact ih j (by omega) hjn
    obtain rfl : j = i + 1 := by omega
    obtain ⟨ihsat, iheq⟩ := ih i (Nat.le_refl _) (by omega)
    have hlt : i < nP := by omega
    -- the contexts at depth `i + 1` are the depth-`i` ones with the
    -- `i`-th entries on top
    have hdc : Γc.drop (nP + nF - (i + 1))
        = Γc.getD (nP + nF - 1 - i) default :: Γc.drop (nP + nF - i) := by
      rw [show nP + nF - (i + 1) = nP + nF - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γc) (i := nP + nF - i - 1)
          (by rw [hC.len]; omega)]
      have hG : Γc[nP + nF - i - 1]'(by have := hC.len; omega)
          = Γc.getD (nP + nF - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hC.len]; omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show nP + nF - i - 1 + 1 = nP + nF - i from by omega]
    have hdt : Γt.drop (nP - (i + 1))
        = Γt.getD (nP - 1 - i) default :: Γt.drop (nP - i) := by
      rw [show nP - (i + 1) = nP - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γt) (i := nP - i - 1)
          (by rw [hT.len]; omega)]
      have hG : Γt[nP - i - 1]'(by have := hT.len; omega)
          = Γt.getD (nP - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hT.len]; omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show nP - i - 1 + 1 = nP - i from by omega]
    have hsat : ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ ↔
        Sat V (Γt.drop (nP - (i + 1))) ρ := by
      intro ρ
      rw [hdc, hdt]
      constructor
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have := Sat_cons V ((ihsat _).mp htl) (by
          rw [← iheq hlt _ htl]; exact h0)
        rwa [cons_eta] at this
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have htl' := (ihsat _).mpr htl
        have := Sat_cons V htl' (by rw [iheq hlt _ htl']; exact h0)
        rwa [cons_eta] at this
    refine ⟨hsat, fun hlt' ρ hρ => ?_⟩
    -- the pin at depth `i + 1`, with the former's comparand transferred
    -- to the constructor's context
    obtain ⟨a, b, ha, hb, hdeq⟩ := hpin (i + 1) hlt'
    obtain ⟨-, hwa, hba, hLa, hleafa⟩ := hC.var (i + 1) a ha
    obtain ⟨-, hwb, hbb, hLb, hleafb⟩ := hT.var (i + 1) b hb
    have hCa : CtxOk m φ (i + 1) (Γc.drop (nP + nF - (i + 1)))
        (Expr.fvarTypeD a) := hC.ctx (by omega) hwa hleafa
    have hCb₀ : CtxOk m φ (i + 1) (Γt.drop (nP - (i + 1)))
        (Expr.fvarTypeD b) := hT.ctx (by omega) hwb hleafb
    -- the entries of the two depth-`(i+1)` contexts interpret alike
    -- under the constructor's: position `p` is binder `i - p`
    have hent : ∀ (p : Nat) (A₁ A₂ : AnnotTerm),
        (Γt.drop (nP - (i + 1)))[p]? = some A₁ →
        (Γc.drop (nP + nF - (i + 1)))[p]? = some A₂ →
        ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ →
          interp V (fun j => ρ (j + p + 1)) A₁
            = interp V (fun j => ρ (j + p + 1)) A₂ := by
      intro p A₁ A₂ hA₁ hA₂ ρ hρ
      have hpl : p < i + 1 := by
        have := (List.getElem?_eq_some_iff.mp hA₂).1
        rw [List.length_drop, hC.len] at this
        omega
      rw [List.getElem?_drop] at hA₁ hA₂
      have hj : nP - (i + 1) + p = nP - 1 - (i - p) := by omega
      have hj' : nP + nF - (i + 1) + p = nP + nF - 1 - (i - p) := by omega
      rw [hj] at hA₁
      rw [hj'] at hA₂
      have e1 : A₁ = Γt.getD (nP - 1 - (i - p)) default := by
        rw [List.getD, hA₁]; rfl
      have e2 : A₂ = Γc.getD (nP + nF - 1 - (i - p)) default := by
        rw [List.getD, hA₂]; rfl
      subst e1 e2
      have hd := Sat_drop hρ (p + 1)
      rw [List.drop_drop, show nP + nF - (i + 1) + (p + 1) = nP + nF - (i - p)
        from by omega] at hd
      have e : (fun j => ρ (j + p + 1)) = fun j => ρ (j + (p + 1)) := by
        funext j; rw [Nat.add_assoc]
      rw [e]
      exact ((ih (i - p) (by omega) (by omega)).2 (by omega) _ hd).symm
    have hCb : CtxOk m φ (i + 1) (Γc.drop (nP + nF - (i + 1)))
        (Expr.fvarTypeD b) :=
      hCb₀.transfer (by rw [List.length_drop, hC.len]; omega)
        (fun ρ hρ => (hsat ρ).mp hρ) hent
    have hda := hC.doms (i + 1) a ha
    have hdb := hT.doms (i + 1) b hb
    exact hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb hda hdb
      (fun ρ hρ => hC.okΓ (i + 1) (by omega) ρ hρ)
      (fun ρ hρ => hT.okΓ (i + 1) (by omega) ρ ((hsat ρ).mp hρ)) ρ hρ

end ConLeche.Model
