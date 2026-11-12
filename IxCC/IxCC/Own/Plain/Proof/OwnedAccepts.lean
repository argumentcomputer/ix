import IxCC.Own.Plain.Proof.OwnedCanonical

/-! # The ownership checker accepts every map today's check accepts

`checkPlainMap_checkOwned` and `checkContractPlainMap_checkContractOwned`: the canonical
producer's map, the only map `checkPlainMap` accepts, is accepted by the ownership checker. The
proof is an induction on the Fir code (`lowerCode_checks`) from the invariant `Canon`
(`OwnedCanonical.lean`: every live variable that is not an immediate holds one token, the
producer's immediates are immediates, the join context is the producer's join list). No heap.

From them and `checkOwned_refines` / `checkOwned_reclaims`, the landed `checked_program_refines`,
`checked_contract_program_refines` and `checked_program_reclaims` are re-derived
(`checked_program_refines'`, …); `Candidate.lean` and `CheckedShape.lean` state the landed
names from these (checked there, by `rfl`, to be the same statements). -/

set_option autoImplicit false

namespace IxCC.Src.NatMap

theorem get?_map {α β : Type} (f : α → β) : ∀ (m : NatMap α) (k : Nat),
    (m.map f).get? k = (m.get? k).map f
  | .leaf, _ => rfl
  | .node v z o, k => by
    simp only [map, get?]
    split
    · rfl
    · split
      · exact get?_map f z _
      · exact get?_map f o _

end IxCC.Src.NatMap

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var Arg)

/-! ## The checker's steps, forwards -/

theorem checkCode_inc_of {Δ : JCtx} {Γ Γ' : Ctx} {x : Var} {k : Code} (h : Γ.inc x 1 = .ok Γ')
    (hc : checkCode Δ Γ' k = .ok ()) : checkCode Δ Γ (.act (.inc x 1) k) = .ok () := by
  show (Γ.inc x 1 >>= fun Γ' => checkCode Δ Γ' k) = .ok ()
  rw [h]
  exact hc

theorem checkCode_bind_of {Δ : JCtx} {Γ Γ' : Ctx} {x : Var} {r : Fir.Rhs} {k : Code}
    (hk : Γ.known x = false) (hb : bindCtx Γ x r = .ok Γ') (hc : checkCode Δ Γ' k = .ok ()) :
    checkCode Δ Γ (.bind x r k) = .ok () := by
  simp only [checkCode, hk, Bool.false_eq_true, ↓reduceIte]
  rw [hb]
  exact hc

theorem checkCode_jp_of {Δ : JCtx} {Γ : Ctx} {j : Fir.JoinId} {ps captured : List Var}
    {rec : Bool} {body k : Code} (hn : nodupVars captured = true)
    (hc : Γ.needCaptured j captured = .ok ())
    (hb : checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body = .ok ())
    (hk : checkCode (Δ.insert j captured) Γ k = .ok ()) :
    checkCode Δ Γ (.jp j ps captured rec body k) = .ok () := by
  simp only [checkCode, hn, ↓reduceIte, pure_bind]
  exact except_bind_of_ok hc (except_bind_of_ok hb hk)

theorem checkCode_jmp_of {Δ : JCtx} {Γ Γ₁ Γ₂ : Ctx} {j : Fir.JoinId} {args : List Arg}
    {captured : List Var} (hd : Δ.get? j = some captured) (h1 : Γ.takeArgs args = .ok Γ₁)
    (h2 : Γ₁.takeVars captured = .ok Γ₂) (h3 : Γ₂.closed s!"jump to j{j}" = .ok ()) :
    checkCode Δ Γ (.jmp j args) = .ok () := by
  simp only [checkCode, hd]
  exact except_bind_of_ok h1 (except_bind_of_ok h2 h3)

theorem checkCode_case_of {Δ : JCtx} {Γ : Ctx} {x : Var} {alts : List Alt} {d : Option Code}
    (h1 : Γ.need x "scrutinised" = .ok ()) (h2 : checkAlts Δ Γ alts = .ok ())
    (h3 : checkOpt Δ Γ d = .ok ()) : checkCode Δ Γ (.case x alts d) = .ok () := by
  simp only [checkCode]
  exact except_bind_of_ok h1 (except_bind_of_ok h2 h3)

theorem checkCode_ret_of {Δ : JCtx} {Γ Γ' : Ctx} {a : Arg} (h1 : Γ.takeArg a = .ok Γ')
    (h2 : Γ'.closed "return" = .ok ()) : checkCode Δ Γ (.ret a) = .ok () := by
  simp only [checkCode]
  exact except_bind_of_ok h1 h2

theorem checkCode_tcall_of {Δ : JCtx} {Γ Γ' : Ctx} {f : Fir.FunId} {args : List Arg}
    (h1 : Γ.takeArgs args = .ok Γ') (h2 : Γ'.closed s!"tail call of f{f}" = .ok ()) :
    checkCode Δ Γ (.tcall f args) = .ok () := by
  simp only [checkCode]
  exact except_bind_of_ok h1 h2

theorem checkAlts_cons_of {Δ : JCtx} {Γ : Ctx} {key : Key.CtorKey} {body : Code} {rest : List Alt}
    (h1 : checkCode Δ Γ body = .ok ()) (h2 : checkAlts Δ Γ rest = .ok ()) :
    checkAlts Δ Γ (.mk key body :: rest) = .ok () := by
  simp only [checkAlts]
  exact except_bind_of_ok h1 h2

theorem takeArgs_single (Γ : Ctx) (a : Arg) : Γ.takeArgs [a] = Γ.takeArg a := by
  simp only [Ctx.takeArgs]
  cases Γ.takeArg a <;> rfl

/-! ## Shapes -/

theorem Shape.congrI {Γ : Ctx} {I I' : Var → Bool} {t t' : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) (hi : ∀ x, I x = I' x) (ht : ∀ x, t x = t' x) : Shape Γ I' t' P :=
  ⟨fun x => (h.imm x).trans (hi x), fun x => (h.tokens x).trans (ht x), h.brw, h.toks,
    fun x hx => (ht x).symm.trans (h.immZero x ((hi x).trans hx)), h.own⟩

/-- A context with the same immediates, tokens and total, and nothing borrowed. -/
theorem Shape.same {Γ Γ' : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) (hi : Γ'.imm = Γ.imm) (ho : Γ'.own = Γ.own) (ht : Γ'.total = Γ.total)
    (hb : ∀ x, Γ'.brw.get? x = none) : Shape Γ' I t P := by
  obtain ⟨toks, htok⟩ := h.toks
  refine ⟨fun x => ?_, fun x => ?_, hb, ⟨toks, htok.same ho ht⟩, h.immZero,
    fun x hx => h.own x (by rw [← ho]; exact hx)⟩
  · rw [← h.imm x]; simp only [Ctx.isImm, hi]
  · rw [← h.tokens x]; simp only [Ctx.tokens, ho]

/-- After a primitive: every variable argument is an immediate, its tokens dropped. -/
theorem shape_immArgs {P : Var → Prop} : ∀ (args : List Arg) {Γ : Ctx} {I : Var → Bool}
    {t : Var → Nat}, Shape Γ I t P →
    Shape (Ctx.immArgs Γ (List.replicate args.length true) args)
      (fun y => decide (y ∈ argVars args) || I y) (fun y => if y ∈ argVars args then 0 else t y) P
  | [], Γ, I, t, h => by
    show Shape Γ _ _ P
    exact h.congrI (fun y => by simp [argVars]) (fun y => by simp [argVars])
  | .var x :: as, Γ, I, t, h => by
    show Shape (Ctx.immArgs (Γ.setImm x) (List.replicate as.length true) as) _ _ P
    refine (shape_immArgs as (shape_setImm h x)).congrI (fun y => ?_) (fun y => ?_)
    · by_cases h1 : y ∈ argVars as <;> by_cases h2 : y = x <;> simp [argVars, h1, h2]
    · by_cases h1 : y ∈ argVars as <;> by_cases h2 : y = x <;> simp [argVars, h1, h2]
  | .lit _ :: as, Γ, I, t, h => by
    show Shape (Ctx.immArgs Γ (List.replicate as.length true) as) _ _ P
    exact (shape_immArgs as h).congrI (fun y => rfl) (fun y => rfl)
  | .erased :: as, Γ, I, t, h => by
    show Shape (Ctx.immArgs Γ (List.replicate as.length true) as) _ _ P
    exact (shape_immArgs as h).congrI (fun y => rfl) (fun y => rfl)

/-! ## The invariant through declarations and bindings -/

theorem lookup_cons' {β : Type} (j j' : Nat) (v : β) (l : List (Nat × β)) :
    ((j, v) :: l).lookup j' = if j' = j then some v else l.lookup j' := by
  by_cases h : j' = j
  · subst h; simp [List.lookup]
  · have hb : (j' == j) = false := beq_eq_false_iff_ne.mpr h
    simp [List.lookup, hb, h]

section
variable {Γ : Ctx} {Δ : JCtx} {live : List Var} {joins : Joins} {imm : List Var}
  {arities : JoinArities}

theorem Canon.notImm (h : Canon Γ Δ live joins imm arities) {x : Var} (hx : x ∉ live) :
    Γ.isImm x = false := by
  cases hc : Γ.isImm x
  · rfl
  · exact absurd (h.immIn x hc) hx

theorem Canon.notImmOfImm (h : Canon Γ Δ live joins imm arities) {y : Var}
    (hy : Γ.isImm y = false) : y ∉ imm := fun hm => by rw [h.immSub y hm] at hy; cases hy

theorem Canon.avail (h : Canon Γ Δ live joins imm arities) {y : Var} (hy : y ∈ live) :
    Γ.avail y = true := by
  apply shape_avail h.shape
  cases hi : Γ.isImm y
  · right; simp [hy, hi]
  · left; simp [hi]

/-- The producer's next immediates, for a binding that is not a primitive. -/
theorem Canon.immNext (h : Canon Γ Δ live joins imm arities) (x : Var) (b : Bool) :
    ∀ z, z ∈ (if b then imm ++ [x] else imm) → Γ.isImm z = true ∨ z = x := by
  intro z hz
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hz
    exact Or.inl (h.immSub z hz)
  · simp only [↓reduceIte] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl (h.immSub z hz)
    · exact Or.inr (List.mem_singleton.mp hz)

theorem Canon.nextImmOf (h : Canon Γ Δ live joins imm arities) (x : Var) (r : Fir.Rhs)
    (hr : nextImm imm x r = if isImmRhs imm r then imm ++ [x] else imm) :
    ∀ z, z ∈ nextImm imm x r → Γ.isImm z = true ∨ z = x := by
  rw [hr]; exact h.immNext x _

/-- A join's declaration (`k` is checked with the join known). -/
theorem Canon.declare (h : Canon Γ Δ live joins imm arities) (j : Fir.JoinId) (n : Nat) :
    Canon Γ (Δ.insert j live) live ((j, live) :: joins) imm ((j, n) :: arities) := by
  refine ⟨h.shape, h.immSub, h.immIn, fun j' => ?_, fun j' C hC => ?_, fun j' m hm => ?_, h.nodup⟩
  · rw [Src.NatMap.get?_insert, lookup_cons', h.jctx]
  · rw [lookup_cons'] at hC
    by_cases hj : j' = j
    · simp only [hj, ↓reduceIte] at hC
      cases hC
      exact List.Sublist.refl _
    · simp only [hj, ↓reduceIte] at hC
      exact h.capIn j' C hC
  · rw [lookup_cons'] at hm ⊢
    by_cases hj : j' = j
    · simp only [hj, ↓reduceIte]; exact ⟨_, rfl⟩
    · simp only [hj, ↓reduceIte] at hm ⊢; exact h.arity j' m hm

/-- A join body starts from `Γ.enter live ps`: the producer captures the whole scope. -/
theorem Canon.enter (h : Canon Γ Δ live joins imm arities) (j : Fir.JoinId) (ps : List Var)
    (rec : Bool) (hf : fresh live ps = true) :
    Canon (Γ.enter live ps) (if rec then Δ.insert j live else Δ) (live ++ ps)
      (if rec then (j, live) :: joins else joins) []
      (if rec then (j, ps.length) :: arities else arities) := by
  have hn : (live ++ ps).Nodup := fresh_nodup_append h.nodup hf
  have hps : ∀ z, z ∈ ps → Γ.isImm z = false := fun z hz => by
    cases hc : Γ.isImm z
    · rfl
    · exact absurd hz (fresh_avoids hf (h.immIn z hc))
  have hsub : (Γ.entered live ps).Sublist (live ++ ps) := by
    unfold Ctx.entered
    exact List.Sublist.append List.filter_sublist (List.Sublist.refl ps)
  have hent : (Γ.entered live ps).Nodup := hsub.nodup hn
  have htok : ∀ z, (Γ.enter live ps).tokens z = if z ∈ Γ.entered live ps then 1 else 0 :=
    fun z => Ctx.tokens_ofList hent z
  have himm : ∀ z, (Γ.enter live ps).isImm z = Γ.isImm z := fun _ => rfl
  have hmem : ∀ z, z ∈ Γ.entered live ps ↔ z ∈ live ++ ps ∧ Γ.isImm z = false := by
    intro z
    simp only [Ctx.entered, List.mem_append, List.mem_filter, Bool.not_eq_true']
    constructor
    · rintro (⟨hl, hi⟩ | hp)
      · exact ⟨Or.inl hl, hi⟩
      · exact ⟨Or.inr hp, hps z hp⟩
    · rintro ⟨hl | hp, hi⟩
      · exact Or.inl ⟨hl, hi⟩
      · exact Or.inr hp
  have hk : ((Γ.entered live ps).map (·, 1) |>.map (·.1)).Nodup := by
    rw [Ctx.map_fst_pairs]; exact hent
  refine ⟨⟨fun x => rfl, fun x => ?_, fun x => rfl, ⟨_, Ctx.Tokens.enter Γ live ps hent⟩,
      fun x hx => ?_, fun x hx => ?_⟩, fun z hz => (by cases hz), fun z hz => ?_, fun j' => ?_,
      fun j' C hC => ?_, fun j' m hm => ?_, hn⟩
  · rw [htok, himm]
    by_cases hx : x ∈ Γ.entered live ps
    · rw [ite_cond_eq_true _ _ (eq_true hx), ite_cond_eq_true _ _ (eq_true ((hmem x).mp hx))]
    · rw [ite_cond_eq_false _ _ (eq_false hx),
        ite_cond_eq_false _ _ (eq_false (fun h' => hx ((hmem x).mpr h')))]
  · have hx' : (Γ.enter live ps).isImm x = true := hx
    simp [hx']
  · by_cases hx' : x ∈ Γ.entered live ps
    · exact ((hmem x).mp hx').1
    · have hnone : (Γ.enter live ps).own.get? x = none :=
        Src.NatMap.get?_ofList_none hk (by rw [Ctx.map_fst_pairs]; exact hx')
      simp [Src.NatMap.contains, hnone] at hx
  · have hz' : Γ.isImm z = true := by rw [← himm]; exact hz
    exact List.mem_append_left _ (h.immIn z hz')
  · cases rec
    · exact h.jctx j'
    · simp only [↓reduceIte]
      rw [Src.NatMap.get?_insert, lookup_cons', h.jctx]
  · cases rec
    · exact (h.capIn j' C hC).trans (List.sublist_append_left _ _)
    · simp only [↓reduceIte] at hC
      rw [lookup_cons'] at hC
      by_cases hj : j' = j
      · simp only [hj, ↓reduceIte] at hC
        cases hC
        exact List.sublist_append_left _ _
      · simp only [hj, ↓reduceIte] at hC
        exact (h.capIn j' C hC).trans (List.sublist_append_left _ _)
  · cases rec
    · exact h.arity j' m hm
    · simp only [↓reduceIte] at hm ⊢
      rw [lookup_cons'] at hm ⊢
      by_cases hj : j' = j
      · simp only [hj, ↓reduceIte]; exact ⟨_, rfl⟩
      · simp only [hj, ↓reduceIte] at hm ⊢; exact h.arity j' m hm

/-- The producer's copies of a consuming binding's arguments, then the binding's take: the
counts come back to the canonical ones. -/
theorem Canon.copiesTake (h : Canon Γ Δ live joins imm arities) (args : List Arg)
    (hargs : ∀ y, y ∈ argVars args → y ∈ live) {k : Code}
    (hk : ∀ Γ₁, (∃ t, Shape Γ₁ (fun z => Γ.isImm z) t (· ∈ live)) →
      (∃ Γ₂, Γ₁.takeArgs args = .ok Γ₂ ∧
        Shape Γ₂ (fun z => Γ.isImm z) (fun z => if z ∈ live ∧ Γ.isImm z = false then 1 else 0)
          (· ∈ live)) →
      checkCode Δ Γ₁ k = .ok ()) :
    checkCode Δ Γ (actionPrefix (copies (heapArgs imm args)) k) = .ok () := by
  rw [copies_eq]
  refine check_incs _ h.shape (fun y hy => ?_) (fun Γ₁ h₁ => ?_)
  · have hl : y ∈ live := hargs y (heapArgs_sub imm args y hy)
    refine ⟨?_, hl⟩
    cases hi : Γ.isImm y
    · right; simp [hl, hi]
    · left; simp [hi]
  · refine hk Γ₁ ⟨_, h₁⟩ ?_
    have hc : ∀ y, Γ.isImm y = false → (argVars args).count y ≤
        (if y ∈ live ∧ Γ.isImm y = false then 1 else 0) +
          (if Γ.isImm y = true then 0 else (argVars (heapArgs imm args)).count y) := by
      intro y hy
      rw [hy, heapArgs_count imm args y (h.notImmOfImm hy)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      (try split) <;> omega
    obtain ⟨Γ₂, ht, _, h₂⟩ := check_takeArgs args h₁ hc (fun y hy => hargs y hy)
    refine ⟨Γ₂, ht, h₂.congr (fun y => ?_)⟩
    cases hi : Γ.isImm y
    · simp [hi, heapArgs_count imm args y (h.notImmOfImm hi)]
    · simp [hi]

end

/-! ## The induction: the checker accepts `lowerCode` -/

theorem argIn_live {live : List Var} {a : Arg} (h : argIn live a = true) :
    ∀ y, y ∈ argVars [a] → y ∈ live := by
  intro y hy
  cases a with
  | var z =>
    simp only [argVars, List.mem_singleton] at hy
    subst hy
    simpa [argIn] using h
  | lit _ | erased => simp [argVars] at hy

theorem all_argIn_var {live : List Var} {args : List Arg} (h : args.all (argIn live) = true) :
    ∀ x, Arg.var x ∈ args → x ∈ live := by
  intro x hx
  have := List.all_eq_true.mp h _ hx
  simpa [argIn] using this

theorem rhsIn_ctor {functions : Signatures} {live : List Var} {c : Fir.CtorInfo} {args : List Arg}
    (h : rhsIn functions live (.ctor c args) = true) :
    args.length = c.arity ∧ args.all (argIn live) = true := by
  simp only [rhsIn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

theorem rhsIn_args {live : List Var} {args : List Arg} {b : Bool}
    (h : (b && args.all (argIn live)) = true) : args.all (argIn live) = true := by
  simp only [Bool.and_eq_true] at h
  exact h.2

mutual
theorem lowerCode_checks (functions : Signatures) : ∀ (c : Fir.Code) {Γ : Ctx} {Δ : JCtx}
    {live : List Var} {joins : Joins} {imm : List Var} {arities : JoinArities},
    Canon Γ Δ live joins imm arities → scopeOk functions live arities c = true →
    checkCode Δ Γ (lowerCode live joins c imm) = .ok ()
  | .bind x r k, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨⟨hx, hr⟩, hk⟩ := hs
    have hx' : x ∉ live := by simpa using hx
    have hxi : Γ.isImm x = false := h.notImm hx'
    cases r with
    | arg a =>
      simp only [rhsIn] at hr
      simp only [lowerCode]
      refine h.copiesTake [a] (argIn_live hr) ?_
      rintro Γ₁ ⟨t₁, h₁⟩ ⟨Γ₂, ht, h₂⟩
      rw [takeArgs_single] at ht
      have hknown := shape_unknown h₁ hx' hxi
      cases a with
      | var y =>
        have hy : Γ₁.take y = .ok Γ₂ := ht
        have hiy₁ : Γ₁.isImm y = Γ.isImm y := h₁.imm y
        cases hiy : Γ.isImm y
        · have hb : bindCtx Γ₁ x (.arg (.var y)) = .ok (Γ₂.addOwn x 1) := by
            simp only [bindCtx, hy, hiy₁, hiy] <;> rfl
          refine checkCode_bind_of hknown hb ?_
          have hyi : imm.contains y = false := by simpa using h.notImmOfImm hiy
          rw [show nextImm imm x (.arg (.var y)) = imm by
            simp only [nextImm, isImmRhs, isImmArg, hyi, Bool.false_eq_true, ↓reduceIte]]
          exact lowerCode_checks functions k (canon_bindOwn h hx' h₂ h.immIn imm h.immSub) hk
        · have hb : bindCtx Γ₁ x (.arg (.var y)) = .ok (Γ₂.setImm x) := by
            simp only [bindCtx, hy, hiy₁, hiy] <;> rfl
          refine checkCode_bind_of hknown hb ?_
          exact lowerCode_checks functions k
            (canon_bindImm h hx' h₂ h.immIn _ (h.nextImmOf x _ rfl)) hk
      | lit l =>
        have hb : bindCtx Γ₁ x (.arg (.lit l)) = .ok (Γ₂.setImm x) := by
          have hΓ : Γ₁ = Γ₂ := Except.ok.inj (ht : Except.ok Γ₁ = Except.ok Γ₂)
          rw [← hΓ]; rfl
        refine checkCode_bind_of hknown hb ?_
        exact lowerCode_checks functions k
          (canon_bindImm h hx' h₂ h.immIn _ (h.nextImmOf x _ rfl)) hk
      | erased =>
        have hb : bindCtx Γ₁ x (.arg .erased) = .ok (Γ₂.setImm x) := by
          have hΓ : Γ₁ = Γ₂ := Except.ok.inj (ht : Except.ok Γ₁ = Except.ok Γ₂)
          rw [← hΓ]; rfl
        refine checkCode_bind_of hknown hb ?_
        exact lowerCode_checks functions k
          (canon_bindImm h hx' h₂ h.immIn _ (h.nextImmOf x _ rfl)) hk
    | ctor c args =>
      obtain ⟨hlen, hall⟩ := rhsIn_ctor hr
      have hargs : ∀ y, y ∈ argVars args → y ∈ live := argVars_sub_live hall
      simp only [lowerCode]
      refine h.copiesTake args hargs ?_
      rintro Γ₁ ⟨t₁, h₁⟩ ⟨Γ₂, ht, h₂⟩
      have hknown := shape_unknown h₁ hx' hxi
      cases hc : c.arity == 0
      · have hb : bindCtx Γ₁ x (.ctor c args) = .ok (Γ₂.addOwn x 1) := by
          simp only [bindCtx, hc, Bool.false_eq_true, ↓reduceIte, ht] <;> rfl
        refine checkCode_bind_of hknown hb ?_
        rw [show nextImm imm x (.ctor c args) = imm by simp [nextImm, isImmRhs, hc]]
        exact lowerCode_checks functions k (canon_bindOwn h hx' h₂ h.immIn imm h.immSub) hk
      · have hnil : args = [] := by
          rw [beq_iff_eq] at hc
          rw [hc] at hlen
          exact List.eq_nil_of_length_eq_zero hlen
        subst hnil
        have hΓ : Γ₁ = Γ₂ := Except.ok.inj (ht : Except.ok Γ₁ = Except.ok Γ₂)
        have hb : bindCtx Γ₁ x (.ctor c []) = .ok (Γ₂.setImm x) := by
          rw [← hΓ]; simp only [bindCtx, hc, ↓reduceIte]
        refine checkCode_bind_of hknown hb ?_
        exact lowerCode_checks functions k
          (canon_bindImm h hx' h₂ h.immIn _ (h.nextImmOf x _ rfl)) hk
    | call f args =>
      have hargs : ∀ y, y ∈ argVars args → y ∈ live := argVars_sub_live (rhsIn_args hr)
      simp only [lowerCode]
      refine h.copiesTake args hargs ?_
      rintro Γ₁ ⟨t₁, h₁⟩ ⟨Γ₂, ht, h₂⟩
      have hknown := shape_unknown h₁ hx' hxi
      have hb : bindCtx Γ₁ x (.call f args) = .ok (Γ₂.release.addOwn x 1) := by
        simp only [bindCtx, ht] <;> rfl
      refine checkCode_bind_of hknown hb ?_
      rw [show nextImm imm x (.call f args) = imm by simp [nextImm, isImmRhs]]
      exact lowerCode_checks functions k
        (canon_bindOwn h hx' h₂.release h.immIn imm h.immSub) hk
    | proj y c i =>
      simp only [rhsIn] at hr
      have hy : y ∈ live := by simpa using hr
      have hknown := shape_unknown h.shape hx' hxi
      have hneed : Γ.need y "projected" = .ok () := need_ok (h.avail hy) _
      cases hc : imm.contains y
      · simp only [lowerCode, hc, Bool.false_eq_true, ↓reduceIte]
        rw [show nextImm imm x (.proj y c i) = imm by
          simp only [nextImm, isImmRhs, hc, Bool.false_eq_true, ↓reduceIte]]
        cases hiy : Γ.isImm y
        · -- borrowed, then the producer's increment makes it owned
          have hb : bindCtx Γ x (.proj y c i) = .ok (Γ.setBorrow x) := by
            simp only [bindCtx, hneed, hiy, Bool.false_eq_true, ↓reduceIte] <;> rfl
          refine checkCode_bind_of hknown hb ?_
          have hs₂ : Shape ({ Γ.setBorrow x with brw := (Γ.setBorrow x).brw.erase x } : Ctx)
              (fun z => Γ.isImm z) (fun z => if z ∈ live ∧ Γ.isImm z = false then 1 else 0)
              (· ∈ live) := by
            refine h.shape.same rfl rfl rfl (fun z => ?_)
            show ((Γ.setBorrow x).brw.erase x).get? z = none
            rw [Src.NatMap.get?_erase, Ctx.brw_setBorrow]
            by_cases hz : z = x
            · simp only [hz, ↓reduceIte]
            · simp only [hz, ↓reduceIte]; exact h.shape.brw z
          have htx : Γ.tokens x = 0 := by
            rw [h.shape.tokens x]; simp [hx']
          have hbx : (Γ.setBorrow x).borrowed x = true := by
            simp [Ctx.borrowed_eq, Ctx.brw_setBorrow]
          have hinc : (Γ.setBorrow x).inc x 1 =
              .ok (({ Γ.setBorrow x with brw := (Γ.setBorrow x).brw.erase x } : Ctx).addOwn x 1) := by
            have hix : (Γ.setBorrow x).isImm x = false := by rw [Ctx.isImm_setBorrow]; exact hxi
            have htx' : (Γ.setBorrow x).tokens x = 0 := by rw [Ctx.tokens_setBorrow]; exact htx
            simp only [Ctx.inc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hix, htx',
              Nat.lt_irrefl, hbx]
          refine checkCode_inc_of hinc ?_
          exact lowerCode_checks functions k (canon_bindOwn h hx' hs₂ h.immIn imm h.immSub) hk
        · have hb : bindCtx Γ x (.proj y c i) = .ok (Γ.setImm x) := by
            simp only [bindCtx, hneed, hiy, ↓reduceIte] <;> rfl
          refine checkCode_bind_of hknown hb ?_
          have hinc : (Γ.setImm x).inc x 1 = .ok (Γ.setImm x) := by
            simp [Ctx.inc, Ctx.isImm_setImm]
          refine checkCode_inc_of hinc ?_
          exact lowerCode_checks functions k
            (canon_bindImm h hx' h.shape h.immIn imm (fun z hz => Or.inl (h.immSub z hz))) hk
      · simp only [lowerCode, hc, ↓reduceIte]
        have hiy : Γ.isImm y = true := h.immSub y (by simpa using hc)
        have hb : bindCtx Γ x (.proj y c i) = .ok (Γ.setImm x) := by
          simp only [bindCtx, hneed, hiy, ↓reduceIte] <;> rfl
        refine checkCode_bind_of hknown hb ?_
        exact lowerCode_checks functions k
          (canon_bindImm h hx' h.shape h.immIn _ (h.nextImmOf x _ rfl)) hk
    | prim op args =>
      have hall := rhsIn_args hr
      have hargs : ∀ y, y ∈ argVars args → y ∈ live := argVars_sub_live hall
      have hknown := shape_unknown h.shape hx' hxi
      have hneed : Γ.needArgs args = .ok () :=
        needArgs_ok (fun z hz => h.avail (all_argIn_var hall z hz))
      have hb : bindCtx Γ x (.prim op args) =
          .ok ((Ctx.immArgs Γ (List.replicate args.length true) args).setImm x) := by
        simp only [bindCtx, hneed, primImmArgs_eq] <;> rfl
      simp only [lowerCode]
      refine checkCode_bind_of hknown hb ?_
      have hs₂' : Shape (Ctx.immArgs Γ (List.replicate args.length true) args)
          (fun y => decide (y ∈ argVars args) || Γ.isImm y)
          (fun z => if z ∈ live ∧ (decide (z ∈ argVars args) || Γ.isImm z) = false then 1 else 0)
          (· ∈ live) := by
        refine (shape_immArgs args h.shape).congrI (fun z => rfl) (fun z => ?_)
        by_cases ha : z ∈ argVars args
        · simp [ha]
        · simp [ha]
      have hI : ∀ z, (decide (z ∈ argVars args) || Γ.isImm z) = true → z ∈ live := by
        intro z hz
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hz
        rcases hz with hz | hz
        · exact hargs z hz
        · exact h.immIn z hz
      refine lowerCode_checks functions k (canon_bindImm h hx' hs₂' hI _ (fun z hz => ?_)) hk
      simp only [nextImm, List.mem_append, List.mem_singleton] at hz
      rcases hz with (hz | hz) | hz
      · left; simp [h.immSub z hz]
      · left; simp [hz]
      · right; exact hz
  | .jp j ps rec body k, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨_, hf⟩, hb⟩, hk⟩ := hs
    simp only [lowerCode]
    refine checkCode_jp_of (nodupFrom_of h.nodup (fun _ _ => rfl))
      (needCaptured_ok (fun c hc => h.avail hc)) ?_ ?_
    · exact lowerCode_checks functions body (h.enter j ps rec hf) hb
    · exact lowerCode_checks functions k (h.declare j ps.length) hk
  | .jmp j args, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨ha, hall⟩ := hs
    have hargs : ∀ y, y ∈ argVars args → y ∈ live := argVars_sub_live hall
    obtain ⟨C, hC⟩ := h.arity j _ ha
    have hCl : C.Sublist live := h.capIn j C hC
    have hCn : C.Nodup := hCl.nodup h.nodup
    simp only [lowerCode, hC, Option.getD_some]
    refine canonical_transfer h C hCl args hargs _ (fun Γ' t' hs ht => ?_)
    have hc : ∀ y, Γ.isImm y = false → (argVars args).count y ≤ t' y := by
      intro y hy; rw [ht y hy]; exact Nat.le_add_right _ _
    obtain ⟨Γ₁, h1, _, h₁⟩ := check_takeArgs args hs hc hargs
    have hpre : ∀ y, y ∈ C → (Γ.isImm y = true ∨
        0 < t' y - (if Γ.isImm y = true then 0 else (argVars args).count y)) ∧ y ∈ live := by
      intro y hy
      refine ⟨?_, hCl.subset hy⟩
      cases hi : Γ.isImm y
      · right
        rw [ht y hi, Ctx.count_nodup hCn]
        simp only [hy, Bool.false_eq_true, ↓reduceIte]
        omega
      · left; rfl
    obtain ⟨Γ₂, h2, h₂⟩ := check_takeVars C hCn h₁ hpre
    refine checkCode_jmp_of (by rw [h.jctx j, hC]) h1 h2 (shape_closed h₂ (fun y => ?_) _)
    cases hi : Γ.isImm y
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      rw [ht y hi]
      omega
    · have h0 : t' y = 0 := hs.immZero y hi
      simp only [hi, ↓reduceIte, Nat.sub_zero, h0]
  | .case x alts d, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk, Bool.and_eq_true] at hs
    obtain ⟨⟨hx, ha⟩, hd⟩ := hs
    simp only [lowerCode]
    exact checkCode_case_of (need_ok (h.avail (by simpa using hx)) _)
      (lowerAlts_checks functions alts h ha) (lowerOpt_checks functions d h hd)
  | .ret a, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk] at hs
    simp only [lowerCode]
    refine canonical_transfer h [] (List.nil_sublist _) [a] (argIn_live hs) _
      (fun Γ' t' hs' ht => ?_)
    have hc : ∀ y, Γ.isImm y = false → (argVars [a]).count y ≤ t' y := by
      intro y hy; rw [ht y hy]; simp
    obtain ⟨Γ₁, h1, _, h₁⟩ := check_takeArgs [a] hs' hc (argIn_live hs)
    rw [takeArgs_single] at h1
    refine checkCode_ret_of h1 (shape_closed h₁ (fun y => ?_) _)
    cases hi : Γ.isImm y
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      rw [ht y hi]
      simp
    · have h0 : t' y = 0 := hs'.immZero y hi
      simp only [hi, ↓reduceIte, Nat.sub_zero, h0]
  | .tcall f args, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOk, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨_, hall⟩ := hs
    have hargs : ∀ y, y ∈ argVars args → y ∈ live := argVars_sub_live hall
    simp only [lowerCode]
    refine canonical_transfer h [] (List.nil_sublist _) args hargs _ (fun Γ' t' hs' ht => ?_)
    have hc : ∀ y, Γ.isImm y = false → (argVars args).count y ≤ t' y := by
      intro y hy; rw [ht y hy]; simp
    obtain ⟨Γ₁, h1, _, h₁⟩ := check_takeArgs args hs' hc hargs
    refine checkCode_tcall_of h1 (shape_closed h₁ (fun y => ?_) _)
    cases hi : Γ.isImm y
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      rw [ht y hi]
      simp
    · have h0 : t' y = 0 := hs'.immZero y hi
      simp only [hi, ↓reduceIte, Nat.sub_zero, h0]
  | .trap, Γ, Δ, live, joins, imm, arities, h, _ => by
    simp only [lowerCode]
    exact canonical_transfer h [] (List.nil_sublist _) [] (fun _ hy => by simp [argVars] at hy) _
      (fun _ _ _ _ => by simp only [checkCode])

theorem lowerAlts_checks (functions : Signatures) : ∀ (alts : List Fir.Alt) {Γ : Ctx} {Δ : JCtx}
    {live : List Var} {joins : Joins} {imm : List Var} {arities : JoinArities},
    Canon Γ Δ live joins imm arities → scopeAlts functions live arities alts = true →
    checkAlts Δ Γ (lowerAlts live joins alts imm) = .ok ()
  | [], _, _, _, _, _, _, _, _ => by simp only [lowerAlts, checkAlts]
  | .mk key body :: rest, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeAlts, Bool.and_eq_true] at hs
    simp only [lowerAlts]
    exact checkAlts_cons_of (lowerCode_checks functions body h hs.1)
      (lowerAlts_checks functions rest h hs.2)

theorem lowerOpt_checks (functions : Signatures) : ∀ (d : Option Fir.Code) {Γ : Ctx} {Δ : JCtx}
    {live : List Var} {joins : Joins} {imm : List Var} {arities : JoinArities},
    Canon Γ Δ live joins imm arities → scopeOpt functions live arities d = true →
    checkOpt Δ Γ (lowerOpt live joins d imm) = .ok ()
  | none, _, _, _, _, _, _, _, _ => by simp only [lowerOpt, checkOpt]
  | some c, Γ, Δ, live, joins, imm, arities, h, hs => by
    simp only [scopeOpt] at hs
    simp only [lowerOpt, checkOpt]
    exact lowerCode_checks functions c h hs
end

/-! ## Function entry and the whole map -/

theorem isImm_entry (params : List Var) (x : Var) : (Ctx.entry params).isImm x = false := rfl

theorem canon_entry (params : List Var) (hn : params.Nodup) :
    Canon (Ctx.entry params) .leaf params [] [] [] := by
  have hk : ((params.map (·, 1)).map (·.1)).Nodup := by rw [Ctx.map_fst_pairs]; exact hn
  refine ⟨⟨fun x => rfl, fun x => ?_, fun x => rfl, ⟨_, Ctx.Tokens.entry params hn⟩,
      fun x hx => ?_, fun x hx => ?_⟩, fun z hz => (by cases hz), fun z hz => ?_,
      fun j => rfl, fun j C hC => (by cases hC), fun j m hm => (by cases hm), hn⟩
  · rw [show (Ctx.entry params).tokens x = if x ∈ params then 1 else 0 from Ctx.tokens_ofList hn x,
      isImm_entry]
    simp
  · have hx' : (Ctx.entry params).isImm x = true := hx
    rw [isImm_entry] at hx'
    cases hx'
  · by_cases hx' : x ∈ params
    · exact hx'
    · have hnone : (Ctx.entry params).own.get? x = none :=
        Src.NatMap.get?_ofList_none hk (by rw [Ctx.map_fst_pairs]; exact hx')
      simp [Src.NatMap.contains, hnone] at hx
  · have hz' : (Ctx.entry params).isImm z = true := hz
    rw [isImm_entry] at hz'
    cases hz'

mutual
theorem erases_self : ∀ c : Code, erases c (eraseCode c) = true
  | .act _ k => by simp only [eraseCode, erases]; exact erases_self k
  | .bind x r k => by simp [eraseCode, erases, erases_self k]
  | .jp j ps _ rec b k => by simp [eraseCode, erases, erases_self b, erases_self k]
  | .jmp j args => by simp [eraseCode, erases]
  | .case x alts d => by simp [eraseCode, erases, erasesAlts_self alts, erasesOpt_self d]
  | .ret a => by simp [eraseCode, erases]
  | .tcall f args => by simp [eraseCode, erases]
  | .trap => by simp [eraseCode, erases]
theorem erasesAlts_self : ∀ alts : List Alt, erasesAlts alts (eraseAlts alts) = true
  | [] => rfl
  | .mk key b :: rest => by simp [eraseAlts, erasesAlts, erases_self b, erasesAlts_self rest]
theorem erasesOpt_self : ∀ d : Option Code, erasesOpt d (eraseOpt d) = true
  | none => rfl
  | some c => by simp only [eraseOpt, erasesOpt]; exact erases_self c
end

theorem checkBodyE_of {fd : Fir.Fun} {body : Code} (he : erases body fd.body = true)
    (hc : checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body = .ok ()) :
    checkBodyE fd body = .ok () := by
  unfold checkBodyE
  simp only [he, ↓reduceIte, pure_bind]
  exact hc

theorem checkFuns_of {F : Fir.Program} {candidate : Src.NatMap Code} :
    ∀ (fs : List Fir.FunId), (∀ f, f ∈ fs → ∃ fd body, F.fun? f = some fd ∧
      candidate.get? f = some body ∧ checkBodyE fd body = .ok ()) →
      checkFuns F candidate fs = .ok ()
  | [], _ => rfl
  | f :: fs, h => by
    obtain ⟨fd, body, h1, h2, h3⟩ := h f List.mem_cons_self
    simp only [checkFuns, h1, h2, h3]
    exact checkFuns_of fs (fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem sameShape_map (g : Fir.Fun → Code) : ∀ m : Src.NatMap Fir.Fun, sameShape m (m.map g) = true
  | .leaf => rfl
  | .node v z o => by
    simp only [Src.NatMap.map, sameShape, Option.isSome_map, beq_self_eq_true, Bool.true_and,
      Bool.and_eq_true]
    exact ⟨sameShape_map g z, sameShape_map g o⟩

/-- **The canonical map passes the ownership checker's map check** (every numbered function in
the domain: fresh parameters, scoped body). -/
theorem canonical_checkMapE {F : Fir.Program} (domain : contractProgramDomain F = true) :
    checkMapE F (Program.canonical F).bodies = .ok () := by
  unfold checkMapE
  simp only [Program.canonical, sameShape_map, ↓reduceIte, pure_bind]
  apply checkFuns_of
  intro f hf
  have hf' := List.mem_range.mp hf
  unfold contractProgramDomain at domain
  have hd := List.all_eq_true.mp domain f hf
  cases hfd : F.fun? f with
  | none => rw [hfd] at hd; cases hd
  | some fd =>
    rw [hfd] at hd
    simp only [Bool.and_eq_true] at hd
    obtain ⟨⟨_, hfresh⟩, hscope⟩ := hd
    refine ⟨fd, lowerCode (fd.params.map (·.1)) [] fd.body, rfl, ?_, ?_⟩
    · rw [Src.NatMap.get?_map]
      simp only [Fir.Program.fun?] at hfd
      rw [hfd]; rfl
    · refine checkBodyE_of ?_ ?_
      · have := erases_self (lowerCode (fd.params.map (·.1)) [] fd.body)
        rwa [erase_lowerCode] at this
      · exact lowerCode_checks (signatures F) fd.body
          (canon_entry _ (fresh_nodup_append List.nodup_nil hfresh)) hscope

/-- **The canonical map is accepted** (`checkPlainMap` → `checkOwned`): every map today's check
accepts, the ownership checker accepts. -/
theorem checkPlainMap_checkOwned {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkPlainMap F candidate = true) : checkOwned F candidate = true := by
  obtain ⟨domain, pins, bound⟩ := checkPlainMap_parts h
  have hc : candidate = (Program.canonical F).bodies := congrArg Program.bodies bound
  simp only [checkOwned, Bool.and_eq_true, domain, pins, true_and, hc,
    canonical_checkMapE (programDomain_implies_contractProgramDomain domain)]
  rfl

/-- **The canonical map is accepted, contract domain** (`checkContractPlainMap` →
`checkContractOwned`). -/
theorem checkContractPlainMap_checkContractOwned {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkContractPlainMap F candidate = true) : checkContractOwned F candidate = true := by
  obtain ⟨domain, pins, bound⟩ := checkContractPlainMap_parts h
  have hc : candidate = (Program.canonical F).bodies := congrArg Program.bodies bound
  simp only [checkContractOwned, Bool.and_eq_true, domain, pins, true_and, hc,
    canonical_checkMapE domain]
  rfl

/-! ## The landed statements, re-derived from the ownership checker's theorems -/

/-- The landed `checked_program_refines`, re-derived: canonical acceptance, then refinement for
any accepted map. -/
theorem checked_program_refines' {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  checkOwned_refines (checkPlainMap_checkOwned checked) k hf hd hb

/-- The landed `checked_contract_program_refines`, re-derived. -/
theorem checked_contract_program_refines' {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  checkContractOwned_refines (checkContractPlainMap_checkContractOwned checked) k hf hd hb

/-- The landed `checked_program_reclaims`, re-derived. -/
theorem checked_program_reclaims' {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H (fun _ => 0) vs)
    (hh : HeapOk H) {w : Fir.Val} (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after released,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ dropAll after [v] = some released ∧
      ∀ l, l < released.size → released.cell? l = some .dead :=
  checkOwned_reclaims (checkPlainMap_checkOwned checked) k hf hd hb hh source

end IxCC.Own.Plain
