import IxCCGrounding.Tele
import IxCCGrounding.Heads

/-!
# The generic `case` lemma, model side (`IxCCGrounding.Case`)

**`caseIota`**: at a `case` constant whose stored value, type, recursor and constructors have
the checked shape (`CaseStored`), `casesOn` applied to arguments that fit its type, the last
applied at a graph-regime site, with the major the image of constructor `j` at the `case`'s own
parameters and levels, is minor `j` applied to the constructor's fields, along a graph-regime
chain. In every model with δ and ι, at every level assignment, with no typing hypothesis.

The proof follows the stored terms:

1. δ on `casesOn` (`Laws.defn_value`), β through its λ-telescope at the arguments, which fit its
   type (`lamTele_app`): `casesOn ps mo t mins` is `rec ps mo W₀ … W_{n-1} t`, the `Wⱼ` being
   what the wrappers denote;
2. the recursor's arguments fit its stored type: the parameters and the motive are `casesOn`'s,
   and each wrapper lies in its minor premise (`wrapper_mem`, by `lamTele_mem`): the wrapper's
   domains are the minor premise's (fields: both are lifts of the constructor's field domains;
   induction hypotheses: both are the motive at a field), and the body, minor `j` applied to the
   fields, lies in the codomain since minor `j` lies in `casesOn`'s minor premise, whose codomain
   does not mention the earlier minors (`CaseWF.codom`);
3. ι (`Laws.iota_rule`) on the major, constructor `j` at the `case`'s parameters and levels, and
   β through the rule's right-hand side: `rec ps mo Ws t = Wⱼ fields ihs`, the induction
   hypotheses being the recursor at the recursive fields;
4. β through the wrapper, which drops the induction hypotheses (each lies in its domain, the
   motive at its field, by `mem` of the recursor): `Wⱼ fields ihs = minorⱼ fields`;
5. the chain: minor `j` lies in `casesOn`'s minor premise, whose field binders carry the last
   binder's zero-ness datum (`CaseWF.regime`), read in the graph regime at the saturating site
   (`last_regime`).

The major's fields must number the constructor's (`Fs.length = cs.nF`): with fewer, ι does not
apply, and the conclusion can fail (at `And.casesOn` the major proof point is also `And.intro`
applied to its two parameters alone).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-! ## Syntax -/

/-- A list of length `n + 2 + m` splits around two elements. -/
theorem split_ctx {α : Type _} (l : List α) (n m : Nat) (h : l.length = n + 2 + m) :
    ∃ a x y b, l = a ++ x :: y :: b ∧ a.length = n ∧ b.length = m := by
  have hd : (l.drop n).length = m + 2 := by simp; omega
  match hdl : l.drop n, hd with
  | x :: y :: b, hd =>
    exact ⟨l.take n, x, y, b, by rw [← hdl, List.take_append_drop], by simp; omega,
      by simpa using hd⟩
  | [], hd => simp at hd
  | [_], hd => simp at hd

theorem lift_zero (c : Nat) (e : KExpr) : e.liftLooseBVars 0 c = e := by
  induction e generalizing c with
  | bvar i => simp only [Expr.liftLooseBVars, Nat.add_zero]; split <;> rfl
  | fvar _ _ _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp [Expr.liftLooseBVars, ihf, iha]
  | lam t b m iht ihb => simp [Expr.liftLooseBVars, iht, ihb]
  | forallE t b m iht ihb => simp [Expr.liftLooseBVars, iht, ihb]
  | letE t v b l iht ihv ihb => simp [Expr.liftLooseBVars, iht, ihv, ihb]
  | lit _ => rfl
  | proj s i e ih => simp [Expr.liftLooseBVars, ih]

theorem liftTele_zero : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)), liftTele 0 c bs = bs
  | _, [] => rfl
  | c, (A, m) :: bs => by simp [liftTele, lift_zero, liftTele_zero (c + 1) bs]

theorem map_fst_get {bs : List (KExpr × BinderMeta)} {n : Nat} {A : KExpr}
    (h : bs[n]?.map (·.1) = some A) (f : KExpr → KExpr) :
    bs[n]?.map (fun b => f b.1) = some (f A) := by
  cases hb : bs[n]? with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h ⊢; rw [h]

theorem get_of_map_fst {bs : List (KExpr × BinderMeta)} {n : Nat} {A : KExpr}
    (h : bs[n]?.map (·.1) = some A) : ∃ m, bs[n]? = some (A, m) := by
  cases hb : bs[n]? with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨b.2, by rw [← h]⟩

/-- A minor premise's field domain `n` is the constructor's, lifted past the motive and the minors
before it. -/
theorem field_lift {fbs fields : List (KExpr × BinderMeta)} {j n : Nat} {AP : KExpr}
    (hf : (liftTele (j + 1) 0 fbs).map (·.1) = fields.map (·.1))
    (hP : fbs[n]?.map (·.1) = some AP) :
    fields[n]?.map (·.1) = some (AP.liftLooseBVars (j + 1) n) := by
  have h1 := congrArg (·[n]?) hf
  simp only [List.getElem?_map] at h1
  rw [← h1, liftTele_get, Nat.zero_add]
  exact map_fst_get hP _

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}
  {φ : LevelParam → Nat}

/-- **A field domain, wherever the minor premise is read**: lifted by `k'` above `j` and read
under the parameters, a block of `j + 1 + k'` sets and the earlier fields, it denotes what the
constructor's field domain denotes under the parameters and the earlier fields. -/
theorem fieldDom_iff {fbs fields : List (KExpr × BinderMeta)} {j k' : Nat}
    (hf : (liftTele (j + 1) 0 fbs).map (·.1) = fields.map (·.1)) {ps junk ys : List V}
    {ρ : BVarIdx → V} (hj : junk.length = j + 1 + k') {AL AP : KExpr}
    (hL : (liftTele k' j fields)[ys.length]?.map (·.1) = some AL)
    (hP : fbs[ys.length]?.map (·.1) = some AP) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ junk) ρ)) AL X ↔
      Denotes M.cval env φ (pushAll ys (pushAll ps ρ)) AP X := by
  have hF := field_lift hf hP
  rw [liftTele_get] at hL
  have h2 := hL.symm.trans (map_fst_get hF fun A => A.liftLooseBVars k' (j + ys.length))
  obtain rfl := Option.some.inj h2
  rw [← pushAll_append, ← pushAll_append, den_lift2 hj]

theorem den_app_bvars {ρ : BVarIdx → V} {a b : Nat} {X : V} :
    Denotes M.cval env φ ρ (.app (.bvar a) (.bvar b)) X ↔ X = app (ρ a) (ρ b) := by
  rw [den_app]
  constructor
  · rintro ⟨F, A, hF, hA, rfl⟩; rw [den_bvar.mp hF, den_bvar.mp hA]
  · rintro rfl; exact ⟨_, _, .bvar, .bvar, rfl⟩

/-! ## List facts -/

theorem take_ctx {α : Type _} (ps mins : List α) (mo t : α) (i : Nat) :
    (ps ++ mo :: t :: mins).take (ps.length + 2 + i) = ps ++ mo :: t :: mins.take i := by
  rw [List.take_append, List.take_of_length_le (show ps.length ≤ ps.length + 2 + i by omega),
    show ps.length + 2 + i - ps.length = i + 2 by omega]; rfl

theorem take_ctx1 {α : Type _} (ps mins : List α) (mo t : α) :
    (ps ++ mo :: t :: mins).take (ps.length + 1) = ps ++ [mo] := by
  rw [List.take_append, List.take_of_length_le (show ps.length ≤ ps.length + 1 by omega),
    show ps.length + 1 - ps.length = 1 by omega]; rfl

theorem get_ctx1 {α : Type _} (ps mins : List α) (mo t : α) :
    (ps ++ mo :: t :: mins)[ps.length + 1]? = some t := by
  rw [List.getElem?_append_right (show ps.length ≤ ps.length + 1 by omega)]; simp

theorem get_ctx2 {α : Type _} (ps mins : List α) (mo t : α) (i : Nat) :
    (ps ++ mo :: t :: mins)[ps.length + 2 + i]? = mins[i]? := by
  rw [List.getElem?_append_right (show ps.length ≤ ps.length + 2 + i by omega),
    show ps.length + 2 + i - ps.length = i + 2 by omega]; rfl

theorem filterMap_range {α β : Type _} (l : List α) (g : Nat → α → β) : ∀ (n : Nat),
    n ≤ l.length → ((List.range n).filterMap fun j => (l[j]?).map (g j)).length = n ∧
      ∀ j, j < n → ((List.range n).filterMap fun j => (l[j]?).map (g j))[j]? =
        (l[j]?).map (g j)
  | 0, _ => ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := filterMap_range l g n (by omega)
    rw [List.range_succ, List.filterMap_append]
    have e : ([n].filterMap fun j => (l[j]?).map (g j)) = [g n (l[n]'(by omega))] := by
      simp [List.getElem?_eq_getElem (show n < l.length by omega)]
    rw [e]
    refine ⟨by simp [h1], fun j hj => ?_⟩
    rw [List.getElem?_append, h1]
    by_cases hjn : j < n
    · simp only [hjn, ↓reduceIte]; exact h2 j hjn
    · have : j = n := by omega
      subst this
      simp [List.getElem?_eq_getElem (show j < l.length by omega)]

theorem drop_pred_of_getLast? {α : Type _} : ∀ {l : List α} {x : α}, l.getLast? = some x →
    l.drop (l.length - 1) = [x]
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; simp [h]
  | a :: b :: l, x, h => by
    have h' : (b :: l).getLast? = some x := by simpa [List.getLast?_cons_cons] using h
    have := drop_pred_of_getLast? h'
    simpa using this

theorem lift_bvarsFrom (m c k n : Nat) (h : c ≤ k) :
    (bvarsFrom k n).map (·.liftLooseBVars m c) = bvarsFrom (k + m) n := by
  simp only [bvarsFrom, List.map_map]
  apply List.map_congr_left
  intro i _
  have hc : k + i ≥ c := by omega
  simp only [Function.comp, Expr.liftLooseBVars, hc, ↓reduceIte]
  rw [Nat.add_right_comm]

/-! ## The context of a `case` constant's arguments

`ps`, `mo`, `t`, `mins` are `casesOn`'s arguments (parameters, motive, major, minors); `Ws` what the
wrappers denote. The environments: `casesOn`'s body (`pushAll (ps ++ mo :: t :: mins) ρ`), the
recursor's type at minor premise `j` (`pushAll (ps ++ [mo] ++ Ws.take j) ρ`), `casesOn`'s type at
minor `j` (`pushAll (ps ++ [mo, t] ++ mins.take j) ρ`), the constructor's type after its parameters
(`pushAll ps ρ`). -/

section Wrapper

variable {sh : CaseShape} {j : Nat} {cs : CtorShape} {fbs : List (KExpr × BinderMeta)}
  {ps mins Ws : List V} {mo t : V} {ρ : BVarIdx → V}

/-- The induction hypothesis domain `r` of minor premise `j`, read under the recursor's
arguments up to the minor or under `casesOn`'s (lifted past the major and the later minors),
denotes the motive at the recursive field. -/
theorem ihDom_den {pre : List V} (hpre : pre.length = j) {ys : List V} {r rf : Nat}
    (hys : ys.length = cs.nF + r) (hrf : rf < cs.nF) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ [mo] ++ pre) ρ)) (cs.ihDom j r rf) X ↔
      X = app mo (pushAll ys ρ (r + cs.nF - 1 - rf)) := by
  rw [CtorShape.ihDom, den_app_bvars, show r + cs.nF + j = pre.length + ys.length by omega,
    pushAll_offset, show ps ++ [mo] ++ pre = ps ++ mo :: pre by simp, pushAll_at,
    pushAll_lt (E' := ρ) (by omega : r + cs.nF - 1 - rf < ys.length)]

theorem ihDomL_den (hj : j < mins.length) {ys : List V} {r rf : Nat} (hys : ys.length = cs.nF + r)
    (hrf : rf < cs.nF) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ mo :: t :: mins) ρ))
        ((cs.ihDom j r rf).liftLooseBVars (mins.length + 1 - j) (j + cs.nF + r)) X ↔
      X = app mo (pushAll ys ρ (r + cs.nF - 1 - rf)) := by
  have h1 : r + cs.nF + j ≥ j + cs.nF + r := by omega
  have h2 : ¬ r + cs.nF - 1 - rf ≥ j + cs.nF + r := by omega
  simp only [CtorShape.ihDom, Expr.liftLooseBVars, h1, h2, ↓reduceIte]
  rw [den_app_bvars,
    show r + cs.nF + j + (mins.length + 1 - j) = (t :: mins).length + ys.length by simp; omega,
    pushAll_offset, pushAll_at, pushAll_lt (E' := ρ) (by omega : r + cs.nF - 1 - rf < ys.length)]

/-- The field domains of minor premise `j`, lifted by `k'` above `j` and read under a block of
`j + 1 + k'` sets after the parameters, denote the constructor's. -/
theorem fieldsCorr (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1)) {k' : Nat}
    {junk : List V} (hj : junk.length = j + 1 + k') :
    TeleCorr M.cval env φ (pushAll (ps ++ junk) ρ) (pushAll ps ρ) (liftTele k' j cs.fields) fbs :=
  fun _ _ _ hL hP _ hX => (fieldDom_iff hf hj hL hP).mpr hX

theorem fieldsCorr_rev (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1)) {k' : Nat}
    {junk : List V} (hj : junk.length = j + 1 + k') :
    TeleCorr M.cval env φ (pushAll ps ρ) (pushAll (ps ++ junk) ρ) fbs (liftTele k' j cs.fields) :=
  fun _ _ _ hP hL _ hX => (fieldDom_iff hf hj hL hP).mp hX

/-- **The wrapper's domains are the recursor's minor premise's**: under `casesOn`'s arguments
(the wrapper) and under the recursor's up to minor `j` (the premise), at the same earlier
arguments. -/
theorem wrapper_corr (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1))
    (hfl : cs.fields.length = cs.nF) (hih : cs.ihs.length = cs.recFields.length)
    (hihs : ∀ r rf, cs.recFields[r]? = some rf → (cs.ihs[r]?).map (·.1) = some (cs.ihDom j r rf))
    (hrf : ∀ rf ∈ cs.recFields, rf < cs.nF) (hj : j < mins.length) {pre : List V}
    (hpre : pre.length = j) :
    TeleCorr M.cval env φ (pushAll (ps ++ mo :: t :: mins) ρ) (pushAll (ps ++ [mo] ++ pre) ρ)
      (liftTele (mins.length + 1 - j) j (cs.fields ++ cs.ihs)) (cs.fields ++ cs.ihs) := by
  intro ys AL AP hL hP X hX
  rw [liftTele_append] at hL
  by_cases hn : ys.length < cs.nF
  · have hlt1 : ys.length < (liftTele (mins.length + 1 - j) j cs.fields).length := by
      rw [liftTele_length, hfl]; exact hn
    have hlt2 : ys.length < cs.fields.length := by rw [hfl]; exact hn
    rw [List.getElem?_append_left hlt1] at hL
    rw [List.getElem?_append_left hlt2] at hP
    have hfb : fbs.length = cs.fields.length := by
      have := congrArg List.length hf; simpa [liftTele_length] using this
    obtain ⟨b, hb⟩ : ∃ b, fbs[ys.length]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by rw [hfb, hfl]; exact hn)⟩
    have hP0 : fbs[ys.length]?.map (·.1) = some b.1 := by rw [hb]; rfl
    have h1 : (liftTele 0 j cs.fields)[ys.length]?.map (·.1) = some AP := by rwa [liftTele_zero]
    have e : ps ++ [mo] ++ pre = ps ++ ([mo] ++ pre) := by simp
    rw [e] at hX
    have hX' := (fieldDom_iff (k' := 0) hf (by simp; omega) h1 hP0).mp hX
    exact (fieldDom_iff (junk := mo :: t :: mins) hf (by simp; omega) hL hP0).mpr hX'
  · obtain ⟨r, hr⟩ : ∃ r, ys.length = cs.nF + r := ⟨ys.length - cs.nF, by omega⟩
    have hge1 : (liftTele (mins.length + 1 - j) j cs.fields).length ≤ ys.length := by
      rw [liftTele_length, hfl]; omega
    have hge2 : cs.fields.length ≤ ys.length := by rw [hfl]; omega
    rw [List.getElem?_append_right hge1, liftTele_length, hfl,
      show ys.length - cs.nF = r by omega] at hL
    rw [List.getElem?_append_right hge2, hfl, show ys.length - cs.nF = r by omega] at hP
    have hrl : r < cs.recFields.length := by
      rw [← hih]
      rcases h : cs.ihs[r]? with _ | _
      · rw [h] at hP; cases hP
      · exact (List.getElem?_eq_some_iff.mp h).1
    obtain ⟨rf, hrf'⟩ : ∃ rf, cs.recFields[r]? = some rf := ⟨_, List.getElem?_eq_getElem hrl⟩
    have hd := hihs r rf hrf'
    have hAP : AP = cs.ihDom j r rf := Option.some.inj (hP.symm.trans hd)
    rw [liftTele_get] at hL
    have hAL := Option.some.inj (hL.symm.trans (map_fst_get hd fun A =>
      A.liftLooseBVars (mins.length + 1 - j) (j + cs.nF + r)))
    subst hAP hAL
    have hrfn : rf < cs.nF := hrf rf (List.mem_of_getElem? hrf')
    exact (ihDomL_den hj hr hrfn).mpr ((ihDom_den hpre hr hrfn).mp hX)

/-- The wrapper's body, at fields `Fs'` and hypotheses `hs`, is minor `j` applied to the fields. -/
theorem wrapper_body (hj : j < mins.length) {Fs' hs : List V} :
    Denotes M.cval env φ (pushAll (Fs' ++ hs) (pushAll (ps ++ mo :: t :: mins) ρ))
      (Expr.mkAppN (.bvar (mins.length - 1 - j + (Fs'.length + hs.length)))
        (bvarsFrom hs.length Fs'.length)) (Fs'.foldl app mins[j]) := by
  refine (den_mkAppN _).mpr ⟨mins[j], Fs', ?_, ?_, rfl⟩
  · rw [show mins.length - 1 - j + (Fs'.length + hs.length) =
      (mins.length - 1 - j) + (Fs' ++ hs).length by simp]
    have h := Denotes.bvar (cval := M.cval) (env := env) (φ := φ)
      (ρ := pushAll (Fs' ++ hs) (pushAll (ps ++ mo :: t :: mins) ρ))
      (i := (mins.length - 1 - j) + (Fs' ++ hs).length)
    rw [pushAll_offset] at h
    have hlt : ps.length + 2 + j < (ps ++ mo :: t :: mins).length := by simp; omega
    have h2 := pushAll_rev (ps ++ mo :: t :: mins) ρ (ps.length + 2 + j) hlt
    have h3 : (ps ++ mo :: t :: mins).length - 1 - (ps.length + 2 + j) = mins.length - 1 - j := by
      simp; omega
    have h4 : (ps ++ mo :: t :: mins)[ps.length + 2 + j] = mins[j] := by
      have := get_ctx2 ps mins mo t j
      rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hj] at this
      exact Option.some.inj this
    rw [h3, h4] at h2
    rw [h2] at h
    exact h
  · rw [← pushAll_append, ← List.append_assoc]
    exact den_bvarsFrom ρ hs Fs' _

theorem fieldsCorr2 (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1)) {k1 k2 : Nat}
    {junk1 junk2 : List V} (h1 : junk1.length = j + 1 + k1) (h2 : junk2.length = j + 1 + k2) :
    TeleCorr M.cval env φ (pushAll (ps ++ junk1) ρ) (pushAll (ps ++ junk2) ρ)
      (liftTele k1 j cs.fields) (liftTele k2 j cs.fields) := by
  intro ys AL AP hL hP X hX
  have hfb : fbs.length = cs.fields.length := by
    have := congrArg List.length hf; simpa [liftTele_length] using this
  have hn : ys.length < fbs.length := by
    rw [hfb, ← liftTele_length k2 j]
    rcases h : (liftTele k2 j cs.fields)[ys.length]? with _ | _
    · rw [h] at hP; cases hP
    · exact (List.getElem?_eq_some_iff.mp h).1
  have hb : fbs[ys.length]?.map (·.1) = some (fbs[ys.length]'hn).1 := by
    rw [List.getElem?_eq_getElem hn]; rfl
  exact (fieldDom_iff hf h1 hL hb).mpr ((fieldDom_iff hf h2 hP hb).mp hX)

/-- **The wrapper lies in the recursor's minor premise**, read after the recursor's arguments up
to it. -/
theorem wrapper_mem (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1))
    (hfl : cs.fields.length = cs.nF) (hih : cs.ihs.length = cs.recFields.length)
    (hihs : ∀ r rf, cs.recFields[r]? = some rf → (cs.ihs[r]?).map (·.1) = some (cs.ihDom j r rf))
    (hrf : ∀ rf ∈ cs.recFields, rf < cs.nF) (hcod : avoids cs.nF j cs.codom = true)
    (hj : j < mins.length) (hWl : mins.length = Ws.length) {W P XM : V}
    (hWd : Denotes M.cval env φ (pushAll (ps ++ mo :: t :: mins) ρ)
      (lamTele (liftTele (mins.length + 1 - j) j (cs.fields ++ cs.ihs))
        (Expr.mkAppN (.bvar (mins.length - 1 - j + (cs.fields ++ cs.ihs).length))
          (bvarsFrom cs.ihs.length cs.nF))) W)
    (hPd : Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws.take j) ρ) cs.recMinor P)
    (hMn : Denotes M.cval env φ (pushAll (ps ++ mo :: t :: mins.take j) ρ)
      (CaseShape.casesMinor j cs) XM)
    (hmin : mins[j] ∈ˢ XM) : W ∈ˢ P := by
  have hpre : (Ws.take j).length = j := by simp; omega
  have htj : (mins.take j).length = j := by simp; omega
  have hc := wrapper_corr (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hf hfl hih
    hihs hrf hj hpre
  have hbody : ∀ (xs : List V) (σ : BVarIdx → V) (R : KExpr),
      Fits M.cval env φ (pushAll (ps ++ [mo] ++ Ws.take j) ρ)
        (piTele (cs.fields ++ cs.ihs) (cs.codom.liftLooseBVars cs.ihs.length 0)) xs σ R →
      xs.length = (cs.fields ++ cs.ihs).length →
      ∃ Y, Denotes M.cval env φ (pushAll xs (pushAll (ps ++ mo :: t :: mins) ρ))
          (Expr.mkAppN (.bvar (mins.length - 1 - j + (cs.fields ++ cs.ihs).length))
            (bvarsFrom cs.ihs.length cs.nF)) Y ∧
        ∀ CC, Denotes M.cval env φ (pushAll xs (pushAll (ps ++ [mo] ++ Ws.take j) ρ))
          (cs.codom.liftLooseBVars cs.ihs.length 0) CC → Y ∈ˢ CC := by
    intro xs σ R hfx hxl
    obtain ⟨Fs', hs, rfl, hF', hs'⟩ : ∃ Fs' hs, xs = Fs' ++ hs ∧ Fs'.length = cs.nF ∧
        hs.length = cs.ihs.length :=
      ⟨xs.take cs.nF, xs.drop cs.nF, (List.take_append_drop _ _).symm,
        by simp [List.length_append] at hxl; simp; omega,
        by simp [List.length_append] at hxl; simp; omega⟩
    refine ⟨Fs'.foldl app mins[j], ?_, fun CC hCC => ?_⟩
    · have hb := wrapper_body (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hj
        (Fs' := Fs') (hs := hs)
      rw [List.length_append, hfl, ← hF', ← hs']
      exact hb
    · rw [piTele_append] at hfx
      have hfx1 := fits_prefix (bs := cs.fields) hfx (by omega)
      have hc1 : TeleCorr M.cval env φ (pushAll (ps ++ mo :: t :: mins.take j) ρ)
          (pushAll (ps ++ [mo] ++ Ws.take j) ρ) (liftTele 1 j cs.fields) cs.fields := by
        have := fieldsCorr2 (M := M) (φ := φ) (ps := ps) (ρ := ρ) (k1 := 1) (k2 := 0)
          (junk1 := mo :: t :: mins.take j) (junk2 := [mo] ++ Ws.take j) hf
          (by simp; omega) (by simp; omega)
        rwa [liftTele_zero, ← List.append_assoc] at this
      have hfx2 := fits_transport (liftTele 1 j cs.fields) cs.fields
        (cs.codom.liftLooseBVars 1 (j + cs.fields.length)) _ (liftTele_length _ _ _) hc1 hfx1
        (by omega)
      rw [List.drop_eq_nil_of_le (show (liftTele 1 j cs.fields).length ≤ Fs'.length by
        rw [liftTele_length]; omega)] at hfx2
      have hMn' : Denotes M.cval env φ (pushAll (ps ++ mo :: t :: mins.take j) ρ)
          (piTele (liftTele 1 j cs.fields) (cs.codom.liftLooseBVars 1 (j + cs.fields.length))) XM := by
        rw [← lift_piTele]; exact hMn
      obtain ⟨RR, hRR, hYR⟩ := fits_app_mem hfx2 hMn' hmin
      have hRR2 : Denotes M.cval env φ (pushAll ((ps ++ [mo]) ++ (mins.take j ++ Fs')) ρ)
          cs.codom RR :=
        (den_lift_block (a := ps ++ [mo]) (b := [t]) (c := mins.take j ++ Fs')).mp (by
          have e1 : pushAll Fs' (pushAll (ps ++ mo :: t :: mins.take j) ρ) =
              pushAll ((ps ++ [mo]) ++ [t] ++ (mins.take j ++ Fs')) ρ := by
            rw [← pushAll_append]; simp
          have e2 : (mins.take j ++ Fs').length = j + cs.fields.length := by simp; omega
          rw [e2, ← e1]; exact hRR)
      have hRR3 : Denotes M.cval env φ (pushAll ((ps ++ [mo]) ++ Ws.take j ++ Fs') ρ) cs.codom RR := by
        refine den_agree (by rw [← List.append_assoc] at hRR2; exact hRR2) fun i hi => ?_
        have hlen' : (mins.take j).length = (Ws.take j).length := by rw [htj, hpre]
        apply pushAll_agree hlen'
        rcases Nat.lt_or_ge i Fs'.length with h1 | h1
        · exact Or.inl h1
        · rcases Nat.lt_or_ge i (Fs'.length + (mins.take j).length) with h2 | h2
          · have hnl := not_looseIn_of_avoids hcod (i := i) (by omega) (by omega)
            rw [hnl] at hi; cases hi
          · exact Or.inr h2
      have hCC' : Denotes M.cval env φ (pushAll ((ps ++ [mo] ++ Ws.take j ++ Fs') ++ []) ρ)
          cs.codom CC :=
        (den_lift_block (a := ps ++ [mo] ++ Ws.take j ++ Fs') (b := hs) (c := [])).mp (by
          have e3 : pushAll (Fs' ++ hs) (pushAll (ps ++ [mo] ++ Ws.take j) ρ) =
              pushAll ((ps ++ [mo] ++ Ws.take j ++ Fs') ++ hs ++ []) ρ := by
            rw [← pushAll_append]; simp
          rw [← e3, hs']; exact hCC)
      rw [List.append_nil] at hCC'
      rw [Denotes_functional hRR3 hCC'] at hYR
      exact hYR
  obtain ⟨L, hLd, hLm⟩ := lamTele_mem (liftTele (mins.length + 1 - j) j (cs.fields ++ cs.ihs))
    (cs.fields ++ cs.ihs) _ (cs.codom.liftLooseBVars cs.ihs.length 0) (liftTele_metas _ _ _) hc
    hPd hbody
  rw [Denotes_functional hWd hLd]
  exact hLm

end Wrapper

theorem denotesList_get {cval : KKey → (LevelParam → Nat) → V} {ρ : BVarIdx → V} :
    ∀ {es : List KExpr} {vs : List V} {i : Nat} {e : KExpr},
      DenotesList cval env φ ρ es vs → es[i]? = some e →
        ∃ v, vs[i]? = some v ∧ Denotes cval env φ ρ e v
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, hl, h => by
    cases hl with
    | cons hd _ => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨_, rfl, hd⟩
  | _ :: _, _, i + 1, _, hl, h => by
    cases hl with
    | cons _ hl' => simp only [List.getElem?_cons_succ] at h ⊢; exact denotesList_get hl' h


theorem wrapper_eq (sh : CaseShape) (j : Nat) (cs : CtorShape) (hfl : cs.fields.length = cs.nF) :
    sh.wrapper j cs = lamTele (liftTele (sh.nM + 1 - j) j (cs.fields ++ cs.ihs))
      (Expr.mkAppN (.bvar (sh.nM - 1 - j + (cs.fields ++ cs.ihs).length))
        (bvarsFrom cs.ihs.length cs.nF)) := by
  simp only [CaseShape.wrapper, liftTele_length, List.length_append, hfl, Nat.add_sub_cancel_left]

theorem take_left_ctx {α : Type _} (ps l : List α) : (ps ++ l).take ps.length = ps := by
  rw [List.take_append, List.take_of_length_le (Nat.le_refl _), Nat.sub_self, List.take_zero,
    List.append_nil]

/-- `Fits` through `casesOn`'s telescope, cut at the motive, the major and the minors. -/
theorem fits_ctx {cval : KKey → (LevelParam → Nat) → V} {bP bMin : List (KExpr × BinderMeta)}
    {bMo bMaj : KExpr × BinderMeta} {C : KExpr} {ps mins : List V} {mo t : V}
    {ρ σ : BVarIdx → V} {R : KExpr} (hl : bP.length = ps.length)
    (h : Fits cval env φ ρ (piTele (bP ++ bMo :: bMaj :: bMin) C) (ps ++ mo :: t :: mins) σ R) :
    (∀ C', Fits cval env φ ρ (piTele bP C') ps (pushAll ps ρ) C') ∧
    (∃ X, Denotes cval env φ (pushAll ps ρ) bMo.1 X ∧ mo ∈ˢ X) ∧
    (∃ X, Denotes cval env φ (pushAll (ps ++ [mo]) ρ) bMaj.1 X ∧ t ∈ˢ X) ∧
    Fits cval env φ (pushAll (ps ++ [mo, t]) ρ) (piTele bMin C) mins σ R := by
  rw [piTele_append] at h
  obtain ⟨σ1, R1, h1, h2⟩ := fits_append h
  obtain ⟨e1, e2, h3⟩ := fits_piTele bP _ h1 (by omega)
  have hd : bP.drop ps.length = [] := List.drop_eq_nil_of_le (show bP.length ≤ ps.length by omega)
  rw [hd] at e2
  subst e1 e2
  refine ⟨fun C' => by simpa [hd, piTele] using h3 C', ?_⟩
  have h2' : Fits cval env φ (pushAll ps ρ)
      (.forallE bMo.1 (.forallE bMaj.1 (piTele bMin C) bMaj.2) bMo.2) (mo :: t :: mins) σ R := h2
  cases h2' with
  | cons hA hx h4 =>
    cases h4 with
    | cons hB hy h5 =>
      refine ⟨⟨_, hA, hx⟩, ⟨_, by rwa [pushAll_snoc], hy⟩, ?_⟩
      rwa [show ps ++ [mo, t] = (ps ++ [mo]) ++ [t] by simp, pushAll_snoc, pushAll_snoc]

/-- The constructor's field telescope, read after the parameters `ps`, fits the fields `Fs`. -/
theorem ctor_fields_fit {cval : KKey → (LevelParam → Nat) → V} {pbs fbs : List (KExpr × BinderMeta)}
    {D : KExpr} {ps Fs : List V} {ρ σ : BVarIdx → V} {R : KExpr} (hpl : pbs.length = ps.length)
    (hfl : fbs.length = Fs.length)
    (h : Fits cval env φ ρ (piTele pbs (piTele fbs D)) (ps ++ Fs) σ R) :
    Fits cval env φ (pushAll ps ρ) (piTele fbs D) Fs (pushAll Fs (pushAll ps ρ)) D ∧ R = D := by
  obtain ⟨σ1, R1, h1, h2⟩ := fits_append h
  obtain ⟨e1, e2, _⟩ := fits_piTele pbs _ h1 (by omega)
  rw [List.drop_eq_nil_of_le (show pbs.length ≤ ps.length by omega)] at e2
  subst e1 e2
  obtain ⟨e3, e4, _⟩ := fits_piTele fbs D h2 (by omega)
  rw [List.drop_eq_nil_of_le (show fbs.length ≤ Fs.length by omega)] at e4
  subst e3 e4
  exact ⟨h2, rfl⟩

/-- **The generic `case` lemma, model side.** At a checked shape, `casesOn` applied to arguments
that fit its type, the last at a graph-regime site, with the major the image of constructor `j`
at the `case`'s own parameters and levels applied to as many fields as the constructor has, is
minor `j` applied to the fields, along a graph-regime chain. -/
theorem caseIota (M : Model V env) (hL : Laws M) {kc kr : KKey} {sh : CaseShape}
    (hS : CaseStored env kc kr sh) (cvc : ConstantVal .anon) (val : KExpr)
    (hint : ReducibilityHint) (hfc : env.find? kc = some (.defnInfo cvc val hint))
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : KExpr) (As : List V)
    (hfit : Fits M.cval env φ ρ cvc.type As σ R) (hlen : As.length = sh.nP + 2 + sh.nM)
    (hlast : LastSiteOk (M.cval kc φ) As)
    (j : Nat) (cs : CtorShape) (cvC : ConstantVal .anon) (K : V) (Fs : List V)
    (σC : BVarIdx → V) (RC : KExpr) (hj : sh.ctors[j]? = some cs)
    (hcC : env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF))
    (hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) K)
    (hFC : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels)
      (As.take sh.nP ++ Fs) σC RC)
    (hFl : Fs.length = cs.nF)
    (hmaj : As[sh.nP + 1]? = some ((As.take sh.nP ++ Fs).foldl app K)) :
    ∃ Mn, As[sh.nP + 2 + j]? = some Mn ∧ As.foldl app (M.cval kc φ) = Fs.foldl app Mn ∧
      AppChain Mn Fs := by
  obtain ⟨⟨hblen, _⟩, ⟨cvc', hint', hfc', _, hty⟩, hminors, ⟨mmaj, hbmaj⟩,
    ⟨cvr, rules, hfr, hlr, htr, hrl, hrules⟩, hctors, hwf⟩ := hS
  have hfc2 := hfc.symm.trans hfc'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hfc2
  obtain ⟨rfl, rfl, rfl⟩ := hfc2
  -- `casesOn`'s arguments and binders
  obtain ⟨ps, mo, t, mins, rfl, hps, hmins⟩ := split_ctx As sh.nP sh.nM hlen
  obtain ⟨bP, bMo, bMaj, bMin, hbs, hbP, hbMin⟩ := split_ctx sh.binders sh.nP sh.nM hblen
  have hjM : j < sh.ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  have hnM : sh.nM = sh.ctors.length := rfl
  have hjm : j < mins.length := by omega
  rw [← hps, take_left_ctx] at hFC hmaj
  rw [get_ctx1] at hmaj
  have ht : t = (ps ++ Fs).foldl app K := Option.some.inj hmaj
  refine ⟨mins[j], by rw [← hps, get_ctx2, List.getElem?_eq_getElem hjm], ?_⟩
  have hbm : bMaj = (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP), mmaj) := by
    have := get_ctx1 bP bMin bMo bMaj
    rw [hbP, ← hbs, hbmaj] at this
    exact (Option.some.inj this).symm
  have hbmin : ∀ j' cs', sh.ctors[j']? = some cs' →
      bMin[j']?.map (·.1) = some (CaseShape.casesMinor j' cs') := fun j' cs' h => by
    have := (hminors j' cs' h).1
    rwa [hbs, ← hbP, get_ctx2] at this
  obtain ⟨Alast, mLast, hgl, hreg⟩ := hwf.regime
  -- `casesOn`'s type, and its arguments' domains
  rw [hty] at hfit
  have hfit0 := hfit
  rw [hbs] at hfit
  obtain ⟨hfitP, ⟨XMo, hMoD, hmo⟩, ⟨Xmaj, hMajD, htm⟩, hrest⟩ := fits_ctx (by omega) hfit
  have hminD : ∀ j' (hj' : j' < mins.length), ∃ XM, Denotes M.cval env φ
      (pushAll (ps ++ mo :: t :: mins.take j') ρ) (bMin[j']'(by omega)).1 XM ∧ mins[j'] ∈ˢ XM := by
    intro j' hj'
    obtain ⟨X, hX, hm⟩ := fits_get bMin (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)) hrest j' hj' (by omega)
    refine ⟨X, ?_, hm⟩
    rwa [← pushAll_append, show ps ++ [mo, t] ++ mins.take j' = ps ++ mo :: t :: mins.take j' by
      simp] at hX
  -- δ on `casesOn`, β through its λs
  have hval := hL.defn_value cvc (lamTele sh.binders (sh.body kr)) hint (find_mem hfc) φ ρ
  rw [show cvc.name = kc from find_name hfc] at hval
  obtain ⟨Y, hY, hYe⟩ := lamTele_app sh.binders (sh.body kr) (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)) hval hfit0 (by simp; omega)
  rw [hYe]
  -- `casesOn`'s body: the recursor at the parameters, the motive, the wrappers and the major
  simp only [CaseShape.body] at hY
  obtain ⟨R0, Ys, hR0, hYs, rfl⟩ := (den_mkAppN _).mp hY
  obtain ⟨Y123, Y4, rfl, h123, h4⟩ := denotesList_append_inv hYs
  obtain ⟨Y12, Ws, rfl, h12, hWs⟩ := denotesList_append_inv h123
  obtain ⟨Y1, Y2, rfl, h1, h2⟩ := denotesList_append_inv h12
  have eY1 : Y1 = ps := by
    have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ (mo :: t :: mins) ps []
    rw [List.nil_append, show (mo :: t :: mins).length = sh.nM + 2 by simp; omega, hps] at this
    exact denotesList_functional h1 this
  have eY2 : Y2 = [mo] := by
    have := DenotesList.cons (cval := M.cval) (env := env) (φ := φ) (den_bvar_at (a := ps)
      (y := mo) (c := t :: mins) (ρ := ρ)) .nil
    rw [show (t :: mins).length = sh.nM + 1 by simp; omega] at this
    exact denotesList_functional h2 this
  have eY4 : Y4 = [t] := by
    have := DenotesList.cons (cval := M.cval) (env := env) (φ := φ) (den_bvar_at (a := ps ++ [mo])
      (y := t) (c := mins) (ρ := ρ)) .nil
    rw [hmins, show ps ++ [mo] ++ t :: mins = ps ++ mo :: t :: mins by simp] at this
    exact denotesList_functional h4 this
  subst Y1 Y2 Y4
  obtain ⟨hwl, hwg⟩ := filterMap_range sh.ctors (fun j cs => sh.wrapper j cs) sh.nM (Nat.le_refl _)
  have hWl : Ws.length = sh.nM := by rw [denotesList_length hWs, hwl]
  have hWd : ∀ j' cs' (hj' : j' < Ws.length), sh.ctors[j']? = some cs' →
      Denotes M.cval env φ (pushAll (ps ++ mo :: t :: mins) ρ) (sh.wrapper j' cs') Ws[j'] := by
    intro j' cs' hj' hc'
    have hget : ((List.range sh.nM).filterMap fun j => (sh.ctors[j]?).map (sh.wrapper j))[j']? =
        some (sh.wrapper j' cs') := by
      rw [hwg j' (by omega), hc']; rfl
    obtain ⟨v, hv, hd⟩ := denotesList_get hWs hget
    rw [List.getElem?_eq_getElem hj'] at hv
    rwa [Option.some.inj hv]
  -- the recursor
  have hR0ρ : Denotes M.cval env φ ρ (.const kr (sh.lps.map Level.param)) R0 := den_const_env hR0
  have hR0e : R0 = M.cval kr φ := by
    cases hR0 with
    | const hf' _ =>
      rw [hfr] at hf'; cases hf'
      simp only [ConstantInfo.toConstantVal, hlr, Level.substFn_param_self]
  subst hbm
  have e1 : sh.binders.take (sh.nP + 1) = bP ++ [bMo] := by rw [hbs, ← hbP, take_ctx1]
  have e2 : sh.binders[sh.nP + 1]? = some (Expr.mkAppN (.const sh.ind sh.indLevels)
      (bvarsFrom 1 sh.nP), mmaj) := hbmaj
  have hrt : cvr.type = piTele (bP ++ [bMo]) (piTele ((sh.ctors.map fun c => (c.recMinor, c.minorMeta))
      ++ [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)]) (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    rw [htr, ← piTele_append]
    simp only [CaseShape.recType, e1, e2, Option.toList_some, List.map_cons, List.map_nil,
      List.append_assoc]
  have hQ : ∀ j', j' ≤ sh.nM → Fits M.cval env φ ρ cvr.type (ps ++ [mo] ++ Ws.take j')
      (pushAll (ps ++ [mo] ++ Ws.take j') ρ)
      (piTele ((sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop j' ++
        [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
          sh.majorMeta)]) (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    intro j' hj'
    induction j' with
    | zero =>
      rw [hrt, List.take_zero, List.append_nil, List.drop_zero, piTele_append, pushAll_snoc]
      exact fits_trans (hfitP _) (.cons hMoD hmo .nil)
    | succ j' ih =>
      have ih' := ih (by omega)
      have hj'c : j' < sh.ctors.length := by omega
      obtain ⟨cs', hc'⟩ : ∃ cs', sh.ctors[j']? = some cs' := ⟨_, List.getElem?_eq_getElem hj'c⟩
      have hcs' : sh.ctors[j'] = cs' := Option.some.inj ((List.getElem?_eq_getElem hj'c).symm.trans hc')
      have hdrop : (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop j' =
          (cs'.recMinor, cs'.minorMeta) :: (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop (j' + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [hcs']
      rw [hdrop] at ih'
      obtain ⟨TR, hTR, hrm⟩ := mem_key M hfr φ ρ
      obtain ⟨RR, hRR, _⟩ := fits_app_mem ih' hTR hrm
      obtain ⟨PP, _, hPP, _, _, _⟩ := den_pi.mp hRR
      obtain ⟨_, hih', hfl'⟩ := hminors j' cs' hc'
      obtain ⟨_, _, fbs', _, _, _, hf'⟩ := hctors j' cs' hc'
      have hWj' := hWd j' cs' (by omega) hc'
      rw [wrapper_eq _ _ _ hfl', ← hmins] at hWj'
      obtain ⟨XM, hXM, hmXM⟩ := hminD j' (by omega)
      have hbj : (bMin[j']'(by omega)).1 = CaseShape.casesMinor j' cs' := by
        have := hbmin j' cs' hc'
        rw [List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      rw [hbj] at hXM
      have hmem := wrapper_mem (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ)
        (Ws := Ws) hf' hfl' hih' (hwf.ihs j' cs' hc')
        (fun rf h => (hwf.recFields j' cs' hc' rf h).1) (hwf.codom j' cs' hc') (by omega)
        (by omega) hWj' hPP hXM hmXM
      have hsn := fits_snoc ih' rfl hPP hmem
      rw [← pushAll_snoc] at hsn
      rw [List.take_add_one, List.getElem?_eq_getElem (show j' < Ws.length by omega),
        Option.toList_some, ← List.append_assoc]
      exact hsn
  have hQM := hQ sh.nM (Nat.le_refl _)
  rw [List.take_of_length_le (show Ws.length ≤ sh.nM by omega),
    List.drop_eq_nil_of_le (show (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).length ≤ sh.nM by
      simp [hnM]), List.nil_append] at hQM
  -- the major's domain, read in the recursor's type
  have hXmajR : Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws) ρ)
      ((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0) Xmaj := by
    have := (den_lift_block (cval := M.cval) (env := env) (φ := φ) (a := ps ++ [mo]) (b := Ws)
      (c := []) (ρ := ρ)).mpr (by rwa [List.append_nil])
    rwa [List.append_nil, hWl] at this
  -- the constructor's type at the `case`'s levels
  obtain ⟨cvC', pbs, fbs, hcC', hinst, hpbs, hf⟩ := hctors j cs hj
  rw [hcC] at hcC'
  cases hcC'
  obtain ⟨_, hih, hfl⟩ := hminors j cs hj
  have hpbl : pbs.length = ps.length := by
    have := congrArg List.length hpbs; simp at this; omega
  have hfbl : fbs.length = Fs.length := by
    have := congrArg List.length hf; simp [liftTele_length] at this; omega
  have hFC0 := hFC
  rw [hinst] at hFC
  obtain ⟨hFCf, hRC⟩ := ctor_fields_fit hpbl hfbl hFC
  -- ι
  obtain ⟨rl, hrl'⟩ : ∃ rl, rules[j]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (by omega : j < rules.length)⟩
  obtain ⟨hrlc, hrlr⟩ := hrules j cs rl hj hrl'
  obtain ⟨H, hH, heq⟩ := hL.iota_rule kr cvr _ _ rules rl hfr (List.mem_of_getElem? hrl') cvC
    sh.nP cs.nF (by rw [hrlc]; exact hcC) (sh.lps.map Level.param) φ ρ (pushAll (ps ++ [mo] ++ Ws) ρ)
    σC (ps ++ [mo] ++ Ws) (ps ++ Fs)
    ((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0)
    (.app (.bvar (sh.nM + 1)) (.bvar 0)) RC sh.majorMeta sh.ind sh.indLevels R0 K Xmaj
    (by simp [hlr]) (by simp; omega) (by simp; omega) hR0ρ
    (by rw [hlr, inst_self]; exact hQM)
    (by simp only [lift_mkAppN, getAppFn_mkAppN, Expr.liftLooseBVars, Expr.getAppFn])
    hXmajR (by rw [hrlc]; exact hK) hFC0 (by rw [← ht]; exact htm)
    (by
      rw [lift_mkAppN, getAppArgs_mkAppN, lift_bvarsFrom _ _ _ _ (Nat.zero_le _)]
      simp only [Expr.liftLooseBVars, Expr.getAppArgs, List.nil_append]
      rw [List.take_of_length_le (show (bvarsFrom (1 + sh.nM) sh.nP).length ≤ sh.nP by
        simp [bvarsFrom_length]), ← hps, take_left_ctx]
      have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ ([mo] ++ Ws) ps []
      rwa [List.nil_append, ← List.append_assoc, show ([mo] ++ Ws).length = 1 + sh.nM by
        simp; omega] at this)
    (by
      rw [hRC, getAppArgs_mkAppN]
      simp only [Expr.getAppArgs, List.nil_append]
      rw [List.drop_eq_nil_of_le (show (bvarsFrom cs.nF sh.nP).length ≤ sh.nP by
        simp [bvarsFrom_length]), List.drop_eq_nil_of_le (show (ps ++ [mo] ++ Ws).length ≤
          sh.nP + 1 + sh.nM by simp; omega)]
      exact .nil)
  rw [hlr, inst_self, hrlr] at hH
  -- β through the rule: the wrapper at the fields and the induction hypotheses
  have hH2 : Denotes M.cval env φ ρ (lamTele ((bP ++ [bMo]) ++ (sh.ctors.map fun c => (c.recMinor, c.minorMeta)))
      (lamTele (liftTele (sh.nM - j) j cs.fields)
        (Expr.mkAppN (.bvar (cs.nF + sh.nM - 1 - j)) (bvarsFrom 0 cs.nF ++ cs.recFields.map fun r =>
          Expr.mkAppN (.const kr (sh.lps.map Level.param)) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
            [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)]))))) H := by
    rw [← lamTele_append, ← e1]; exact hH
  have hQM' : Fits M.cval env φ ρ (piTele ((bP ++ [bMo]) ++ (sh.ctors.map fun c => (c.recMinor, c.minorMeta)))
      (piTele [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)] (.app (.bvar (sh.nM + 1)) (.bvar 0)))) (ps ++ [mo] ++ Ws)
      (pushAll (ps ++ [mo] ++ Ws) ρ)
      (piTele [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)] (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    rw [piTele_append, ← piTele_append (sh.ctors.map fun c => (c.recMinor, c.minorMeta)), ← hrt]
    exact hQM
  obtain ⟨Y1, hY1, eY1⟩ := lamTele_app _ _ _ hH2 hQM' (by simp; omega)
  have hcR : TeleCorr M.cval env φ (pushAll (ps ++ [mo] ++ Ws) ρ) (pushAll ps ρ)
      (liftTele (sh.nM - j) j cs.fields) fbs := by
    have := fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j)
      (k' := sh.nM - j) (junk := [mo] ++ Ws) hf (by simp; omega)
    rwa [← List.append_assoc] at this
  have hFR := fits_transport (liftTele (sh.nM - j) j cs.fields) fbs
    (cs.codom.liftLooseBVars 0 0) _ (by rw [liftTele_length, hfbl, hFl, hfl]) hcR hFCf (by omega)
  rw [List.drop_eq_nil_of_le (show (liftTele (sh.nM - j) j cs.fields).length ≤ Fs.length by
    rw [liftTele_length]; omega)] at hFR
  obtain ⟨Y2, hY2, eY2⟩ := lamTele_app _ _ _ hY1 hFR (by rw [liftTele_length]; omega)
  -- the induction hypotheses
  have hfv : ∀ rf (hrf : rf < cs.nF), pushAll Fs ρ (cs.nF - 1 - rf) = Fs[rf]'(by omega) := by
    intro rf hrf; rw [← hFl]; exact pushAll_rev Fs ρ rf (by omega)
  have hpre : (Ws.take j).length = j := by simp; omega
  have hcE : TeleCorr M.cval env φ (pushAll (ps ++ [mo] ++ Ws.take j) ρ) (pushAll ps ρ)
      cs.fields fbs := by
    have := fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j)
      (k' := 0) (junk := [mo] ++ Ws.take j) hf (by simp; omega)
    rwa [liftTele_zero, ← List.append_assoc] at this
  have hF1 := fits_transport cs.fields fbs (piTele cs.ihs (cs.codom.liftLooseBVars cs.ihs.length 0))
    _ (by omega) hcE hFCf (by omega)
  rw [List.drop_eq_nil_of_le (show cs.fields.length ≤ Fs.length by omega)] at hF1
  have hIHmem : ∀ rf ∈ cs.recFields, (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0
      ∈ˢ app mo (pushAll Fs ρ (cs.nF - 1 - rf)) := by
    intro rf hrfm
    obtain ⟨hrf, hrd⟩ := hwf.recFields j cs hj rf hrfm
    rw [hfv rf hrf]
    -- the recursive field lies in the major's domain
    obtain ⟨X', hX', hm'⟩ := fits_get cs.fields _ hF1 rf (by omega) (by omega)
    rw [List.getElem?_eq_getElem (show rf < cs.fields.length by omega)] at hrd
    simp only [Option.map_some, Option.some.injEq] at hrd
    rw [hrd, CaseShape.recFieldDom] at hX'
    obtain ⟨IND, Ps1, hIND, hPs1, rfl⟩ := (den_mkAppN _).mp hX'
    obtain ⟨IND', Ps2, hIND', hPs2, rfl⟩ := (den_mkAppN _).mp hMajD
    have e3 : Ps1 = ps := by
      have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ
        ([mo] ++ Ws.take j ++ Fs.take rf) ps []
      rw [List.nil_append, show ([mo] ++ Ws.take j ++ Fs.take rf).length = rf + j + 1 by simp; omega,
        hps, show ps ++ ([mo] ++ Ws.take j ++ Fs.take rf) =
          ps ++ [mo] ++ Ws.take j ++ Fs.take rf by simp, pushAll_append (ps ++ [mo] ++ Ws.take j)] at this
      exact denotesList_functional hPs1 this
    have e4 : Ps2 = ps := by
      have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ [mo] ps []
      rw [List.nil_append, hps] at this
      exact denotesList_functional hPs2 this
    subst Ps1 Ps2
    obtain rfl := Denotes_functional (den_const_env hIND) hIND'
    have hfX : Fs[rf] ∈ˢ ps.foldl app IND := hm'
    have hsn := fits_snoc hQM rfl hXmajR hfX
    obtain ⟨TR, hTR, hrm⟩ := mem_key M hfr φ ρ
    obtain ⟨RR, hRR, hmRR⟩ := fits_app_mem hsn hTR hrm
    have hRR' : Denotes M.cval env φ (push Fs[rf] (pushAll (ps ++ [mo] ++ Ws) ρ))
        (.app (.bvar (sh.nM + 1)) (.bvar 0)) RR := hRR
    rw [den_app_bvars] at hRR'
    have hmo : push Fs[rf] (pushAll (ps ++ [mo] ++ Ws) ρ) (sh.nM + 1) = mo := by
      show pushAll (ps ++ [mo] ++ Ws) ρ sh.nM = mo
      rw [← hWl, show ps ++ [mo] ++ Ws = ps ++ mo :: Ws by simp, pushAll_at]
    rw [hmo] at hRR'
    rw [hR0e, show app mo Fs[rf] = RR from hRR'.symm]
    exact hmRR
  -- the recursor's rule body: the wrapper at the fields and the induction hypotheses
  obtain ⟨IHs, hIHs⟩ : ∃ IHs : List V, IHs = cs.recFields.map fun rf =>
      (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0 := ⟨_, rfl⟩
  have hIHl : IHs.length = cs.ihs.length := by rw [hIHs, List.length_map, hih]
  have hE : pushAll Fs (pushAll (ps ++ [mo] ++ Ws) ρ) = pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ :=
    (pushAll_append _ _ _).symm
  have hIHterm : ∀ rf, rf < cs.nF → Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ)
      (Expr.mkAppN (.const kr (sh.lps.map Level.param)) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
        [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - rf)]))
      ((ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0) := by
    intro rf hrf
    refine (den_mkAppN _).mpr ⟨R0, _, den_const_env hR0, ?_, rfl⟩
    refine denotesList_append (denotesList_append (denotesList_append ?_ ?_) ?_) ?_
    · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ ([mo] ++ Ws ++ Fs) ps []
      rwa [List.nil_append, show ([mo] ++ Ws ++ Fs).length = cs.nF + sh.nM + 1 by simp; omega,
        hps, show ps ++ ([mo] ++ Ws ++ Fs) = ps ++ [mo] ++ Ws ++ Fs by simp] at this
    · have := den_bvar_at (cval := M.cval) (env := env) (φ := φ) (a := ps) (y := mo) (c := Ws ++ Fs)
        (ρ := ρ)
      rw [show (Ws ++ Fs).length = cs.nF + sh.nM by simp; omega,
        show ps ++ mo :: (Ws ++ Fs) = ps ++ [mo] ++ Ws ++ Fs by simp] at this
      exact .cons this .nil
    · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ Fs Ws (ps ++ [mo])
      rwa [hFl, hWl] at this
    · refine .cons ?_ .nil
      have hv : pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ (cs.nF - 1 - rf) = pushAll Fs ρ (cs.nF - 1 - rf) := by
        rw [pushAll_append (ps ++ [mo] ++ Ws)]
        exact pushAll_lt (show cs.nF - 1 - rf < Fs.length by omega)
      rw [← hv]
      exact .bvar
  have hbodyR : Denotes M.cval env φ (pushAll Fs (pushAll (ps ++ [mo] ++ Ws) ρ))
      (Expr.mkAppN (.bvar (cs.nF + sh.nM - 1 - j)) (bvarsFrom 0 cs.nF ++ cs.recFields.map fun r =>
        Expr.mkAppN (.const kr (sh.lps.map Level.param)) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
          [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)])))
      ((Fs ++ IHs).foldl app (Ws[j]'(by omega))) := by
    rw [hE]
    refine (den_mkAppN _).mpr ⟨_, Fs ++ IHs, ?_, ?_, rfl⟩
    · have hlt : ps.length + 1 + j < (ps ++ [mo] ++ Ws).length := by simp; omega
      have h2 := pushAll_rev (ps ++ [mo] ++ Ws) ρ (ps.length + 1 + j) hlt
      rw [show (ps ++ [mo] ++ Ws).length - 1 - (ps.length + 1 + j) = sh.nM - 1 - j by simp; omega]
        at h2
      have h4 : (ps ++ [mo] ++ Ws)[ps.length + 1 + j] = Ws[j]'(by omega) := by
        rw [List.getElem_append_right (show (ps ++ [mo]).length ≤ ps.length + 1 + j by simp)]
        simp
      have hv : pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ (cs.nF + sh.nM - 1 - j) = Ws[j]'(by omega) := by
        rw [pushAll_append (ps ++ [mo] ++ Ws),
          show cs.nF + sh.nM - 1 - j = (sh.nM - 1 - j) + Fs.length by omega, pushAll_offset, h2, h4]
      rw [← hv]
      exact .bvar
    · refine denotesList_append ?_ ?_
      · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ [] Fs (ps ++ [mo] ++ Ws)
        rwa [List.append_nil, List.length_nil, hFl] at this
      · rw [hIHs]
        have hall : ∀ l : List Nat, (∀ rf ∈ l, rf < cs.nF) →
            DenotesList M.cval env φ (pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ)
              (l.map fun r => Expr.mkAppN (.const kr (sh.lps.map Level.param))
                (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++ [.bvar (cs.nF + sh.nM)] ++
                  bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)]))
              (l.map fun rf => (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0) := by
          intro l hl
          induction l with
          | nil => exact .nil
          | cons rf l ih =>
            exact .cons (hIHterm rf (hl rf (by simp))) (ih fun r h => hl r (by simp [h]))
        exact hall cs.recFields fun rf h => (hwf.recFields j cs hj rf h).1
  have eY2' : Y2 = (Fs ++ IHs).foldl app (Ws[j]'(by omega)) := Denotes_functional hY2 hbodyR
  -- β through the wrapper
  have hF2 : Fits M.cval env φ (pushAll Fs (pushAll (ps ++ [mo] ++ Ws.take j) ρ))
      (piTele cs.ihs (cs.codom.liftLooseBVars cs.ihs.length 0)) IHs
      (pushAll IHs (pushAll Fs (pushAll (ps ++ [mo] ++ Ws.take j) ρ)))
      (cs.codom.liftLooseBVars cs.ihs.length 0) := by
    refine fits_of_forall cs.ihs _ hIHl fun r h1 h2 => ?_
    obtain ⟨rf, hrf'⟩ : ∃ rf, cs.recFields[r]? = some rf :=
      ⟨_, List.getElem?_eq_getElem (show r < cs.recFields.length by omega)⟩
    have hrfm : rf ∈ cs.recFields := List.mem_of_getElem? hrf'
    have hrfl := (hwf.recFields j cs hj rf hrfm).1
    have hd := hwf.ihs j cs hj r rf hrf'
    rw [List.getElem?_eq_getElem h2] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    refine ⟨app mo (pushAll Fs ρ (cs.nF - 1 - rf)), ?_, ?_⟩
    · rw [hd, ← pushAll_append]
      refine (ihDom_den hpre (by simp; omega) hrfl).mpr ?_
      rw [pushAll_append, show r + cs.nF - 1 - rf = (cs.nF - 1 - rf) + (IHs.take r).length by
        simp; omega, pushAll_offset]
    · have hr : cs.recFields[r]'(by omega) = rf :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hrf')
      simp only [hIHs, List.getElem_map, hr]
      exact hIHmem rf hrfm
  have hF12 := fits_trans hF1 hF2
  rw [← piTele_append] at hF12
  have hcW := wrapper_corr (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hf hfl hih
    (hwf.ihs j cs hj) (fun rf h => (hwf.recFields j cs hj rf h).1) hjm hpre
  have hFW := fits_transport _ _ (cs.codom.liftLooseBVars 0 0) _ (liftTele_length _ _ _) hcW hF12
    (by simp; omega)
  rw [List.drop_eq_nil_of_le (show (liftTele (mins.length + 1 - j) j (cs.fields ++ cs.ihs)).length ≤
    (Fs ++ IHs).length by rw [liftTele_length]; simp; omega)] at hFW
  have hWj := hWd j cs (by omega) hj
  rw [wrapper_eq _ _ _ hfl, ← hmins] at hWj
  obtain ⟨Y3, hY3, eY3⟩ := lamTele_app _ _ _ hWj hFW (by rw [liftTele_length]; simp; omega)
  have hwb := wrapper_body (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hjm
    (Fs' := Fs) (hs := IHs)
  rw [show (cs.fields ++ cs.ihs).length = Fs.length + IHs.length by simp; omega,
    show cs.ihs.length = IHs.length by omega, show cs.nF = Fs.length by omega] at hY3
  have eY3' := Denotes_functional hY3 hwb
  -- the last binder is read in the graph regime
  have hlastReg : regime φ mLast.pw ≠ 0 := by
    have hne : (ps ++ mo :: t :: mins) ≠ [] := by simp
    have hsplit := (List.dropLast_concat_getLast hne).symm
    obtain ⟨v, A, B, hv, hX, _⟩ := hlast _ _ hsplit
    have hpre' := fits_prefix (bs := sh.binders) (xs := (ps ++ mo :: t :: mins).dropLast)
      (ys := [(ps ++ mo :: t :: mins).getLast hne]) (by rw [← hsplit]; exact hfit0) (by simp; omega)
    rw [show ((ps ++ mo :: t :: mins).dropLast).length = sh.binders.length - 1 by simp; omega,
      drop_pred_of_getLast? hgl] at hpre'
    obtain ⟨TT, hTT, hHm⟩ := mem_key M hfc φ ρ
    have hTT' : Denotes M.cval env φ ρ (piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM))) TT := by
      rw [← hty]; exact hTT
    exact last_regime hpre' hTT' hHm hv hX
  -- the chain: minor `j` applies to the fields in the graph regime
  obtain ⟨XM, hXM, hmXM⟩ := hminD j hjm
  have hbj : (bMin[j]'(by omega)).1 = CaseShape.casesMinor j cs := by
    have := hbmin j cs hj
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  rw [hbj, CaseShape.casesMinor, lift_piTele] at hXM
  have hcC1 : TeleCorr M.cval env φ (pushAll (ps ++ mo :: t :: mins.take j) ρ) (pushAll ps ρ)
      (liftTele 1 j cs.fields) fbs :=
    fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j) (k' := 1)
      (junk := mo :: t :: mins.take j) hf (by simp; omega)
  have hFE := fits_transport (liftTele 1 j cs.fields) fbs
    (cs.codom.liftLooseBVars 1 (j + cs.fields.length)) _ (by rw [liftTele_length]; omega) hcC1 hFCf
    (by omega)
  have hreg' : ∀ b ∈ liftTele 1 j cs.fields, regime φ b.2.pw ≠ 0 := by
    intro b hb
    have hb2 : b.2 ∈ (liftTele 1 j cs.fields).map (·.2) := List.mem_map_of_mem hb
    rw [liftTele_metas] at hb2
    obtain ⟨b', hb', e⟩ := List.mem_map.mp hb2
    rw [← e, hreg j cs hj b' hb']
    exact hlastReg
  refine ⟨?_, appChain_of_fits _ _ hXM hmXM hFE (by rw [liftTele_length]; omega) hreg'⟩
  rw [ht, heq, List.take_of_length_le (show (ps ++ [mo] ++ Ws).length ≤ sh.nP + 1 + sh.nM by
    simp; omega), show (ps ++ Fs).drop sh.nP = Fs by rw [← hps]; simp, List.foldl_append, eY1, eY2,
    eY2', eY3, eY3']

end IxCC.Grounding
