module

public import ConLeche.Verify.Inductives.StructRec
import ConLeche.Kernel.Inductives.SumInstall

public section

/-!
# The generated recursor at a constructor list (task #175 sum-types)

`ConLeche/Verify/Inductives/StructRec.lean`'s syntactic kit at one
constructor, generalized to the list the generators fold over
(`structMinorsPis`/`structMinorsLams`): the unfoldings of
`structRecTy`/`structRecRhs`, the minor premise's telescope under any
number of earlier binders (`instSeq_minorBody_at`: the motive is the
first extra, the earlier minors follow), the rule body under the
motive and all minors (`instSeq_ruleBody_at`: minor `j` is extra
`j + 1`), and the `.proj`-freeness of the generated forms.
-/

namespace ConLeche

open Expr

/-! ## The unfoldings -/

/-! ## The closed spellings under extras -/

/-- The minor premise's conclusion `motive (C p⃗ f⃗)`, spelled under
`extras.length` binders (the motive first, then the earlier minors),
instantiated at the parameters and the extras and then at the
fields: the motive extra applied to the constructor at the
variables. -/
theorem instSeq_minorBody_at (tfvs extras xFvs : List Expr) {C : Name}
    {lps : List Name} {nP nF : Nat} {mfv : Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true)
    (hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true)
    (hhead : extras[0]? = some mfv) :
    instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
        (.app (.bvar (nF + extras.length - 1)) (structCtorSpineAt C lps extras.length nP nF)))
      = .app mfv (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)) := by
  have hpos : 0 < extras.length := by
    have := (List.getElem?_eq_some_iff.mp hhead).1
    omega
  have hcl : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlen : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
  have hclM : mfv.looseBVarsBounded 0 = true := hclE mfv (List.mem_of_getElem? hhead)
  unfold structCtorSpineAt
  rw [instSeq_app, instSeq_mkAppN, instSeq_app, instSeq_mkAppN,
    List.map_append, List.map_append]
  have hhead' : instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
      (.bvar (nF + extras.length - 1)) = mfv := by
    have := instSeq_bvar (tfvs ++ extras) (nP + extras.length - 1 + nF) (nF + extras.length - 1)
      hcl (by omega) (by rw [hlen]; omega)
    rw [show nP + extras.length - 1 + nF - (nF + extras.length - 1) = nP from by omega,
      List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
    exact (Option.some.inj this).symm
  rw [hhead', instSeq_eq_self _ _ hclM,
    instSeq_eq_self (e := Expr.const C (lps.map .param)) _ _ rfl,
    instSeq_eq_self (e := Expr.const C (lps.map .param)) _ _ rfl,
    show nP + extras.length - 1 + nF = extras.length + nF + nP - 1 from by omega,
    map_instSeq_structPsAt (tfvs ++ extras) (extras.length + nF) nP hcl (by omega),
    List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    show extras.length + nF + nP - 1 = nP + extras.length - 1 + nF from by omega,
    map_instSeq_fieldBvars_above (tfvs ++ extras) (nP + extras.length - 1 + nF) nF
      (by rw [hlen]; omega),
    map_instSeq_fieldBvars xFvs nF hclX hlenX]
  have htfvs : tfvs.map (fun x => instSeq xFvs (nF - 1) x) = tfvs := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map]
    exact instSeq_eq_self _ _ (hclT _ (List.getElem_mem h2))
  rw [htfvs]

/-! ## No projection nodes -/

namespace Expr

variable {T : Name} {i : Nat}

end Expr

end ConLeche

namespace ConLeche

open Expr

/-! ## The elimination restriction's readout -/

/-- `Level.isNeverZero` is sound: such a level evaluates to a nonzero
number at every assignment. -/
theorem Level.isNeverZero_sound (φ : Name → Nat) :
    ∀ l : Level, l.isNeverZero = true → Level.eval φ l ≠ 0
  | .zero, h => by simp [Level.isNeverZero] at h
  | .param _, h => by simp [Level.isNeverZero] at h
  | .succ _, _ => by simp [Level.eval]
  | .max l r, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true] at h
    simp only [Level.eval]
    rcases h with h | h
    · have := Level.isNeverZero_sound φ l h; omega
    · have := Level.isNeverZero_sound φ r h; omega
  | .imax l r, h => by
    simp only [Level.isNeverZero] at h
    have := Level.isNeverZero_sound φ r h
    simp only [Level.eval, if_neg this]
    omega

/-! ## The stored rules, positionally -/

/-- A stored rule is constructor `j`'s rule at right-hand side `j`. -/
theorem sumRules_getElem? {find? : Name → Option ConstantInfo}
    {recName : Name} {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules find? recName nP mI rP recTy ctorsA rhss →
      ∃ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        ctorsA[j]? = some cA ∧ rhss[j]? = some rhs ∧
        r = recRuleBits find? recName
          { ctor := cA.1.name, nfields := cA.2, ctorParams := nP,
            fire := if Expr.recRulePlain recTy mI rP nP then .plain
              else .inert,
            rhs := rhs, paramsBlind := true }
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, c, rhs, rfl, rfl, rfl⟩
    · obtain ⟨j, cA, rhs', hc, hr, rfl⟩ := sumRules_getElem? h
      exact ⟨j + 1, cA, rhs', by simpa using hc, by simpa using hr, rfl⟩

/-! ## The indexed generators, unfolded (task #175 indexed families) -/

/-! ## Instantiation under a mid-cutoff lift -/

/-- **Lifting above a cutoff and instantiating through the lifted
region**: `q` mentions its `c` innermost binders and the `pre.length`
above them; lifting `rest.length` at cutoff `c` and instantiating the
prefix and the rest above the innermost `c` is instantiating the
prefix alone (`instSeq_liftLooseBVars_prefix` at `c = 0`). -/
theorem instSeq_liftLooseBVars_mid :
    ∀ (pre rest : List Expr) {q : Expr} {c : Nat},
      (∀ a ∈ pre, a.looseBVarsBounded 0 = true) →
      q.looseBVarsBounded (pre.length + c) = true →
      instSeq (pre ++ rest) (pre.length + rest.length + c - 1)
        (q.liftLooseBVars rest.length c) =
      instSeq pre (pre.length + c - 1) q := by
  intro pre
  induction pre with
  | nil =>
    intro rest q c _ hq
    have hq0 : q.looseBVarsBounded c = true := by simpa using hq
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    rw [liftLooseBVars_eq_self hq0]
    show instSeq rest (rest.length + c - 1) q = q
    rcases Nat.eq_zero_or_pos (rest.length + c) with h0 | hpos
    · have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    · exact instSeq_eq_self_of_bounded rest _ hq0 (by omega)
  | cons a pre' ih =>
    intro rest q c hpre hq
    have ha : a.looseBVarsBounded 0 = true := hpre a List.mem_cons_self
    have hq' : (q.instantiate1 a (pre'.length + c)).looseBVarsBounded
        (pre'.length + c) = true :=
      looseBVarsBounded_instantiate1_gen ha (by simpa [Nat.add_right_comm] using hq)
    show instSeq (pre' ++ rest) ((a :: pre').length + rest.length + c - 1 - 1)
        ((q.liftLooseBVars rest.length c).instantiate1 a
          ((a :: pre').length + rest.length + c - 1)) =
      instSeq pre' ((a :: pre').length + c - 1 - 1)
        (q.instantiate1 a ((a :: pre').length + c - 1))
    rw [show (a :: pre').length + rest.length + c - 1 =
        (pre'.length + c) + rest.length from by simp; omega,
      show (a :: pre').length + c - 1 = pre'.length + c from by simp,
      show (pre'.length + c) + rest.length - 1 = pre'.length + rest.length + c - 1 from by omega,
      liftLooseBVars_instantiate1 ha (by omega)]
    exact ih rest (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hq'

/-- The minor premise's conclusion at an indexed family,
`motive e⃗ (C p⃗ f⃗)` spelled under `extras.length` binders, instantiated
at the parameters, the extras and the fields: the motive extra at the
index expressions (instantiated at the parameters and the fields
alone) and the constructor at the variables. -/
theorem instSeq_minorBodyI_at (tfvs extras xFvs : List Expr) {C : Name}
    {lps : List Name} {nP nF : Nat} {mfv : Expr} {es : List Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true)
    (hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true)
    (hhead : extras[0]? = some mfv)
    (hes : ∀ e ∈ es, e.looseBVarsBounded (nP + nF) = true) :
    instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
        (Expr.mkAppN (.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++ [structCtorSpineAt C lps extras.length nP nF])))
      = Expr.mkAppN mfv
          (es.map (fun e => instSeq xFvs (nF - 1) (instSeq tfvs (nP + nF - 1) e)) ++
            [Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)]) := by
  have hpos : 0 < extras.length := by
    have := (List.getElem?_eq_some_iff.mp hhead).1
    omega
  have hsp := instSeq_minorBody_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead
    (C := C) (lps := lps)
  simp only [instSeq_app] at hsp
  obtain ⟨hhd, hspine⟩ := Expr.app.inj hsp
  rw [Expr.mkAppN_append_one, Expr.mkAppN_append_one]
  simp only [instSeq_app, instSeq_mkAppN, hhd, hspine, List.map_map]
  congr 2
  apply List.map_congr_left
  intro e he
  simp only [Function.comp]
  congr 1
  have := instSeq_liftLooseBVars_mid tfvs extras (c := nF) hclT (by rw [hlenT]; exact hes e he)
  rw [hlenT, show nP + extras.length + nF - 1 = nP + extras.length - 1 + nF from by omega] at this
  exact this

end ConLeche
