import IxCC.Lam.Erase.Proof.Forms

/-! # Choosing an alternative

SrcEval's ordinary eliminators choose a rule by the constructor index of
the forced major (F2, F5: `selectRule`, `Nat` literals peeling); Lam's
`case` takes the first alternative whose key and arity match. For a related
major the two agree: the alternative of the rule SrcEval chooses is the
first that matches, since constructors of one inductive have distinct keys
(the `Decidable ↦ Bool` alias is injective on them), and its fields are
the kept fields of the constructor value, dropped ones being `irr`
(FieldsIrr). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

/-! ## Constructor keys -/

theorem alias_cases (I : Input) (c : CId) :
    I.alias c = c ∨ (I.known.decIsFalse = some c ∧ I.known.boolFalse = some (I.alias c)) ∨
      (I.known.decIsTrue = some c ∧ I.known.boolTrue = some (I.alias c)) := by
  simp only [Input.alias]
  split
  · next df dt bf bt hdf hdt hbf hbt =>
    by_cases h₁ : (c == df && I.fieldless df) = true
    · simp only [h₁, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁
      exact .inr (.inl ⟨h₁.1 ▸ hdf, hbf⟩)
    · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
      by_cases h₂ : (c == dt && I.fieldless dt) = true
      · simp only [h₂, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at h₂
        exact .inr (.inr ⟨h₂.1 ▸ hdt, hbt⟩)
      · simp only [h₂, Bool.false_eq_true, ↓reduceIte]
        exact .inl trivial
  · exact .inl rfl

section

variable {I : Input} (wf : ProgWF I)
include wf

/-- Constructors of one inductive have distinct keys. -/
theorem ctorKey_inj {x y ind : CId} {sf sf' : Bool} {lv lv' i j np np' nf nf' : Nat}
    {ty ty' : Src.Term} (hx : I.decl? x = some (.ctor sf lv ind i np nf ty))
    (hy : I.decl? y = some (.ctor sf' lv' ind j np' nf' ty')) (h : I.ctorKey x = I.ctorKey y) :
    x = y := by
  simp only [Input.ctorKey, Key.CtorKey.src.injEq] at h
  -- A `Decidable` constructor aliased to a `Bool` one cannot meet another of its inductive.
  have hdb : ∀ {d b : CId} {sfd lvd id npd nfd tyd sfb lvb ib npb nfb tyb},
      (I.known.decIsFalse = some d ∨ I.known.decIsTrue = some d) →
      (I.known.boolFalse = some b ∨ I.known.boolTrue = some b) →
      I.decl? d = some (.ctor sfd lvd ind id npd nfd tyd) →
      I.decl? b = some (.ctor sfb lvb ind ib npb nfb tyb) →
      False := by
    intro d b sfd lvd id npd nfd tyd sfb lvb ib npb nfb tyb hd hb hdd hbd
    exact wf.decOther hd (by rcases hb with h | h; exact .inl h; exact .inr (.inl h)) hdd hbd rfl
  rcases alias_cases I x with ex | ⟨hxd, hxb⟩ | ⟨hxd, hxb⟩ <;>
    rcases alias_cases I y with ey | ⟨hyd, hyb⟩ | ⟨hyd, hyb⟩
  · rw [ex, ey] at h; exact h
  · rw [ex] at h; rw [h] at hx
    exact (hdb (.inl hyd) (.inl hyb) hy hx).elim
  · rw [ex] at h; rw [h] at hx
    exact (hdb (.inr hyd) (.inr hyb) hy hx).elim
  · rw [ey] at h; rw [← h] at hy
    exact (hdb (.inl hxd) (.inl hxb) hx hy).elim
  · rw [hxd] at hyd; cases hyd; rfl
  · rw [h] at hxb
    obtain ⟨_, _, B, _, _, hf, t, ht, _, _, _, _, htd⟩ := wf.boolFalse hxb
    rw [hyb] at ht; cases ht
    rw [hf] at htd; cases htd
  · rw [ey] at h; rw [← h] at hy
    exact (hdb (.inr hxd) (.inr hxb) hx hy).elim
  · rw [h] at hxb
    obtain ⟨_, _, B, _, _, ht, f, hf, _, _, _, _, hfd⟩ := wf.boolTrue hxb
    rw [hyb] at hf; cases hf
    rw [ht] at hfd; cases hfd
  · rw [hxd] at hyd; cases hyd; rfl

end

/-! ## Alternatives, rule by rule -/

/-- Alternatives built rule by rule (`ruleAlt`), each body related by `Body`. -/
inductive AltsFor (I : Input) (Body : Nat → Src.Rule → List (Option Nat) → Nat → Term → Prop)
    (r : CId) (q : Profile) (base : Nat) (ind : CId) : Nat → List Src.Rule → List Alt → Prop
  | nil {j : Nat} : AltsFor I Body r q base ind j [] []
  | cons {j : Nat} {rule : Src.Rule} {rules : List Src.Rule} {key : Key.CtorKey} {n : Nat}
      {fields : List (Option Nat)} {body : Term} {alts : List Alt} :
      RuleAltR I r q base ind j rule key n fields → Body j rule fields n body →
      AltsFor I Body r q base ind (j + 1) rules alts →
      AltsFor I Body r q base ind j (rule :: rules) (.mk key n body :: alts)

theorem AltsR.altsFor {I : Input} {G : Key.GKey → GlobalId → Prop} :
    ∀ {cx : Cx} {r : CId} {q : Profile} {ind : CId} {refs : List Ref} {mbase j : Nat}
      {rules : List Src.Rule} {alts : List Alt}, AltsR I G cx r q ind refs mbase j rules alts →
      AltsFor I (fun j _ fields n body => MinorR I G (cx.extra n) (refs.getD (mbase + j) .box)
        fields body) r q cx.depth ind j rules alts
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, _, .cons ha hm hr => .cons ha hm (AltsR.altsFor hr)

theorem RecAltsR.altsFor {I : Input} {G : Key.GKey → GlobalId → Prop} {r : CId} {q : Profile}
    {pre arity : Nat} {minors : List (Nat × List Mode)} {ind : CId} :
    ∀ {j : Nat} {rules : List Src.Rule} {alts : List Alt},
      RecAltsR I G r q pre arity minors ind j rules alts →
      AltsFor I (fun _ rule fields n body => RuleBodyR I G r q pre (arity + n) minors rule fields body)
        r q arity ind j rules alts
  | _, _, _, .nil => .nil
  | _, _, _, .cons ha hb hr => .cons ha hb (RecAltsR.altsFor hr)

theorem lt_of_getElem?_eq_some {α : Type} {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) :
    i < xs.length := (List.getElem?_eq_some_iff.1 h).1

theorem range_getElem?_eq_some {n i i' : Nat} (h : (List.range n)[i]? = some i') : i = i' ∧ i < n := by
  have hl := lt_of_getElem?_eq_some h
  simp only [List.length_range] at hl
  rw [List.getElem?_range hl] at h
  exact ⟨by simpa using h, hl⟩

theorem Forall2.of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y) → Forall2 R xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h =>
    .cons (h 0 x y rfl rfl) (Forall2.of_getElem (by simpa using hl) fun i x' y' hx hy =>
      h (i + 1) x' y' (by simpa using hx) (by simpa using hy))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section

variable {I : Input} {G : Key.GKey → GlobalId → Prop} (wf : ProgWF I)
include wf

/-- Lam's `case` meets the alternative of the rule with the major's
constructor index first. -/
theorem evalAlts_find {Body : Nat → Src.Rule → List (Option Nat) → Nat → Term → Prop}
    {r : CId} {q : Profile} {base : Nat} {ind c : CId} {sf : Bool} {lv jr np nf : Nat}
    {ty : Src.Term} (hc : I.decl? c = some (.ctor sf lv ind jr np nf ty))
    {P : Program} :
    ∀ {j : Nat} {rules : List Src.Rule} {alts : List Alt}, AltsFor I Body r q base ind j rules alts →
      j ≤ jr → ∀ {rule : Src.Rule}, rules[jr - j]? = some rule →
      ∃ key n fields body, RuleAltR I r q base ind jr rule key n fields ∧ Body jr rule fields n body ∧
        key = I.ctorKey c ∧
        (∀ (k : Nat) (ρ : Env) (vals : List Val) (d : Option Term), n = vals.length →
          Lam.evalAlts P k ρ (I.ctorKey c) vals alts d =
          Lam.eval P k (vals.reverse.map .val ++ ρ) body)
  | _, _, _, .nil, _, _, h => by simp at h
  | j, rule₀ :: rules, .mk key n body :: alts, .cons ha hb hr, hj, rule, hrule => by
    obtain ⟨sf', lv', cidx', np', nf', ty', hd', hcidx, _, hkey, _, _⟩ := ha
    by_cases hjj : j = jr
    · subst hjj
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hrule
      subst hrule
      have hsame : rule₀.ctor = c := by
        have h₁ := wf.ctorIn hd'
        have h₂ := wf.ctorIn hc
        rw [hcidx] at h₁
        rw [h₁] at h₂
        cases h₂; rfl
      refine ⟨key, n, _, body, ⟨sf', lv', cidx', np', nf', ty', hd', hcidx, ‹_›, hkey, ‹_›, ‹_›⟩,
        hb, hkey.trans (by rw [hsame]), fun k ρ vals d hn => ?_⟩
      rw [Lam.evalAlts_cons, if_pos ⟨by rw [hkey, hsame], hn⟩]
    · have hlt : j < jr := by omega
      have hrule' : rules[jr - (j + 1)]? = some rule := by
        have e : jr - j = (jr - (j + 1)) + 1 := by omega
        rw [e, List.getElem?_cons_succ] at hrule
        exact hrule
      obtain ⟨key', n', fields', body', h₁, h₂, h₃, h₄⟩ :=
        evalAlts_find hc hr (by omega) hrule'
      refine ⟨key', n', fields', body', h₁, h₂, h₃, fun k ρ vals d hn => ?_⟩
      rw [Lam.evalAlts_cons, if_neg, h₄ k ρ vals d hn]
      rintro ⟨hk, _⟩
      rw [hkey] at hk
      have := ctorKey_inj wf hd' hc hk
      rw [this, hc] at hd'
      cases hd'
      omega

/-- A rule named by index `j` of inductive `ind` constructs the constructor
listed there. -/
theorem rule_ctor {r : CId} {q : Profile} {base : Nat} {ind c : CId} {j : Nat} {rule : Src.Rule}
    {key : Key.CtorKey} {n : Nat} {fields : List (Option Nat)}
    (ha : RuleAltR I r q base ind j rule key n fields) {sf : Bool} {lv np nf : Nat} {ty : Src.Term}
    (hc : I.decl? c = some (.ctor sf lv ind j np nf ty)) :
    rule.ctor = c ∧ key = I.ctorKey c ∧ n = I.keptCount c (I.ctorProfile r q) nf ∧
      fields = (List.range nf).map fun i =>
        if I.kept c (I.ctorProfile r q) i then some (base + I.rank c (I.ctorProfile r q) i)
        else none := by
  obtain ⟨sf', lv', cidx', np', nf', ty', hd', hcidx, hnf, hkey, hn, hf⟩ := ha
  have h₁ := wf.ctorIn hd'
  have h₂ := wf.ctorIn hc
  rw [hcidx] at h₁
  rw [h₁] at h₂
  cases h₂
  rw [hc] at hd'
  cases hd'
  exact ⟨rfl, hkey, hn, hf⟩

end

section

variable {S : Setting} (wf : ProgWF S.I)
include wf

/-- The fields a constructor value gives its alternative's body. -/
theorem fields_slots {c : CId} {q : Profile} {fs : List Src.Value} {fs' : List Val}
    (hk : KeptR S.I S.G c 0 fs fs') (ρ : Env) :
    Forall2 (FieldSlot S.I S.G (fs'.reverse.map .val ++ ρ))
      ((List.range fs.length).map fun i =>
        if S.I.kept c q i then some (ρ.length + S.I.rank c q i) else none)
      (fs.map .val) := by
  refine Forall2.of_getElem (by simp) fun i x y hx hy => ?_
  simp only [List.getElem?_map, List.getElem?_range, Option.map_eq_some_iff] at hx hy
  obtain ⟨i', hi', rfl⟩ := hx
  obtain ⟨f, hf, rfl⟩ := hy
  have hi : i' = i := by
    exact (range_getElem?_eq_some hi').1.symm
  subst hi
  by_cases hkept : S.I.kept c q i' = true
  · simp only [hkept, ↓reduceIte]
    obtain ⟨f', hf', hvf⟩ := hk.get_kept (j := i') hf (by rw [Nat.zero_add, ← Input.kept_prof]; exact hkept)
    have hlt : keptBelow S.I c 0 i' < fs'.length := lt_of_getElem?_eq_some hf'
    rw [rank_eq_keptBelow]
    refine .lvl (by simp; omega) ?_ hvf
    have e : (fs'.reverse.map Slot.val ++ ρ).length - 1 - (ρ.length + keptBelow S.I c 0 i') =
        fs'.length - 1 - keptBelow S.I c 0 i' := by simp; omega
    rw [e, List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_reverse (by omega)]
    simp only [show fs'.length - 1 - (fs'.length - 1 - keptBelow S.I c 0 i') =
      keptBelow S.I c 0 i' by omega, hf', Option.map_some]
  · simp only [hkept, Bool.false_eq_true, ↓reduceIte]
    have hirr := hk.get_drop (j := i') hf (by
      rw [Nat.zero_add, ← Input.kept_prof (q := q)]; simpa using hkept)
    cases f with
    | irr t ρ₀ ls₀ => exact .box ⟨_, _, _, rfl⟩
    | _ => simp [Src.Value.isIrr] at hirr

/-- SrcEval's rule choice against Lam's alternatives. -/
theorem select_alt {Body : Nat → Src.Rule → List (Option Nat) → Nat → Term → Prop}
    {r : CId} {q : Profile} {base : Nat} {ind : CId} {rules : List Src.Rule} {alts : List Alt}
    (h : AltsFor S.I Body r q base ind 0 rules alts)
    (hcount : (S.I.ctorsOf ind).length ≤ rules.length) (hu : S.I.unbox? ind [] = none)
    {v : Src.Value} {v' : Val} (hv : VR S.I S.G v v') {np jr : Nat} {flds : List Src.Slot}
    (hsel : S.p.selectRule ind np v = some (jr, flds)) (ρ : Env) (hbase : base = ρ.length) :
    ∃ rule key n fields body vals, rules[jr]? = some rule ∧ Body jr rule fields n body ∧
      v'.asCtor S.L.known = some (key, vals) ∧ n = vals.length ∧
      (∀ k d, Lam.evalAlts S.L k ρ key vals alts d =
        Lam.eval S.L k (vals.reverse.map .val ++ ρ) body) ∧
      Forall2 (FieldSlot S.I S.G (vals.reverse.map .val ++ ρ)) fields flds ∧
      (∀ l, some l ∈ fields → base ≤ l) := by
  subst hbase
  have hK : S.L.known = S.I.lamKnown := S.known
  cases v with
  | lit n =>
    simp only [Src.Program.selectRule] at hsel
    split at hsel
    · next hnat =>
      have hN : S.I.known.nat = some ind := by simp at hnat; exact hnat.symm
      obtain ⟨Z, Sc, hZ, hS, ⟨sfz, lvz, tyz, hdZ⟩, ⟨sfs, lvs, tys, hdS⟩⟩ := wf.natPins hN
      cases hv
      have h1 := wf.ctorIn hdS
      have hlen : 2 ≤ rules.length := by
        have : 1 < (S.I.ctorsOf ind).length := lt_of_getElem?_eq_some h1
        omega
      obtain ⟨r0, hr0⟩ : ∃ r0, rules[0]? = some r0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨r1, hr1⟩ : ∃ r1, rules[1]? = some r1 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      cases n with
      | zero =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        obtain ⟨key, k', fields, body, ha, hb, hkey, hev⟩ :=
          evalAlts_find wf hdZ (P := S.L) h (Nat.zero_le _) (by simpa using hr0)
        obtain ⟨_, _, hn, hfields⟩ := rule_ctor wf ha hdZ
        have hk0 : k' = 0 := by simp [hn, Input.keptCount, Input.rank]
        refine ⟨r0, key, k', fields, body, [], hr0, hb, ?_, hk0, fun k d => ?_, ?_, ?_⟩
        · simp only [Lam.Val.asCtor, hK, Input.lamKnown, hZ, Option.map_some, Function.comp,
            hkey, Input.ctorKey]
        · rw [hkey]; exact hev k ρ [] d hk0
        · rw [hfields]; exact .nil
        · rw [hfields]; simp
      | succ n =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        obtain ⟨key, k', fields, body, ha, hb, hkey, hev⟩ :=
          evalAlts_find wf hdS (P := S.L) h (Nat.zero_le _) (by simpa using hr1)
        obtain ⟨_, _, hn, hfields⟩ := rule_ctor wf ha hdS
        have hkept : S.I.kept Sc (S.I.ctorProfile r q) 0 = true := by
          rw [Input.kept_prof]; exact S.succKept Sc hS
        have hk1 : k' = 1 := by
          simp [hn, Input.keptCount, Input.rank, List.range_succ, hkept]
        refine ⟨r1, key, k', fields, body, [.lit (.nat n)], hr1, hb, ?_, hk1, fun k d => ?_, ?_, ?_⟩
        · simp only [Lam.Val.asCtor, hK, Input.lamKnown, hS, Option.map_some, Function.comp,
            hkey, Input.ctorKey]
        · rw [hkey]; exact hev k ρ _ d hk1
        · rw [hfields]
          simp only [List.range_one, List.map_cons, List.map_nil, hkept, ↓reduceIte,
            Input.rank, List.range_zero, List.filter_nil, List.length_nil, Nat.add_zero]
          exact .cons (.lvl (by simp) (by simp) VR.lit) .nil
        · rw [hfields]; simp [hkept]
    · cases hsel
  | con c ls ps fs =>
    simp only [Src.Program.selectRule] at hsel
    split at hsel
    · next sf lv ind' cidx np' nf ty hd =>
      split at hsel
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨rfl, _⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        have hd' : S.I.decl? c = some (.ctor sf lv ind' cidx np' nf ty) := hd
        obtain ⟨hlenf, hvr⟩ := hv.con_inv hd'
        rcases hvr with ⟨j, a, hu', _⟩ | ⟨_, fs', rfl, hkr⟩
        · rw [hu] at hu'; cases hu'
        have hcl := wf.ctorIn hd'
        have hjr : cidx < rules.length := by
          have := lt_of_getElem?_eq_some hcl
          omega
        obtain ⟨rule, hrule⟩ : ∃ rule, rules[cidx]? = some rule :=
          ⟨_, List.getElem?_eq_getElem hjr⟩
        obtain ⟨key, k', fields, body, ha, hb, hkey, hev⟩ :=
          evalAlts_find wf hd' (P := S.L) h (Nat.zero_le _) (by simpa using hrule)
        obtain ⟨_, _, hn, hfields⟩ := rule_ctor wf ha hd'
        have hkn : k' = fs'.length := by
          rw [hn, hkr.length, keptCount_eq_keptBelow, hlenf]
        refine ⟨rule, key, k', fields, body, fs', hrule, hb, by rw [hkey]; rfl, hkn,
          fun k d => by rw [hkey]; exact hev k ρ fs' d hkn, ?_, ?_⟩
        · rw [hfields, ← hlenf]
          exact fields_slots wf hkr ρ
        · rw [hfields]
          intro l hl
          simp only [List.mem_map, List.mem_range] at hl
          obtain ⟨i, _, hi⟩ := hl
          split at hi
          · cases hi; omega
          · cases hi
      · cases hsel
    · cases hsel
  | _ => simp [Src.Program.selectRule] at hsel

end

end IxCC.Lam.Erase.Proof
