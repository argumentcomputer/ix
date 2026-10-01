module

public import ConLeche.Verify.Inductives.SumRec
import ConLeche.Kernel.Inductives.NativeParts

public section

/-!
# The generated recursive recursor, unfolded (task #188)

`ConLeche/Verify/Inductives/SumRec.lean`'s syntactic kit with the inductive
hypotheses threaded: the unfoldings of the recursive generators
(`structMinorTyR`, `structMinorsPisR`/`structMinorsLamsR`,
`structRecTyR`, `structRecRhsR`), and the closed spellings the
readings need.

The one genuinely new piece is `instSeq_structIdxAt`: a recursive
field's index expression is spelled at the field's own frame (the
parameters and the `i` earlier fields) and moved to the recursor's
frame `p⃗ x⃗ f⃗ ih⃗` by `structIdxAt`'s two lifts; instantiating there at
the frame's own variables undoes both lifts and leaves the expression
instantiated at the parameters and the `i` earlier field variables
alone — twice `instSeq_liftLooseBVars_mid`.

`Expr.shiftFromN` (`Expr.shiftFrom`, iterated) is here too: the
reading of those index expressions moves from the constructor's own
opening to the recursor's frame by inserting the `o` extra slots just
after the parameters, which is exactly that shift (its `denoteMeta` side
is `ConLeche/Model/Inductives/FixRecRead.lean`).
-/

namespace ConLeche

open Expr

/-! ## The recursive generators, unfolded -/

/-- `structMinorTyR`, unfolded to its three steps. -/
theorem structMinorTyR_unfold {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} {recIdx : List Nat}
    (h : structMinorTyR C lps nP nF o pw cty recIdx = some mty) :
    ∃ (cbs fbs : List (Expr × BinderMeta)) (crest0 res : Expr),
      cty.stripPis nP = some (cbs, crest0) ∧
      crest0.stripPis nF = some (fbs, res) ∧
      Expr.replacePisPw pw nF (crest0.liftLooseBVars o 0)
        (structIhPis nF o pw (structFieldTeleOf cty nP nF) (structFieldIdxOf cty nP nF) recIdx 0
          ((Expr.mkAppN (.bvar (nF + o - 1))
            ((res.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
              [structCtorSpineAt C lps o nP nF])).liftLooseBVars recIdx.length 0))
        = some mty := by
  unfold structMinorTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, r, hr, hmty⟩ := h
  exact ⟨q.1, r.1, q.2, r.2, hq, hr, hmty⟩

/-- The recursive minors' `∀`-telescope, one constructor peeled. -/
theorem structMinorsPisR_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {recIdx : List Nat} {cs : List (Name × Nat × Expr × List Nat)}
    {o : Nat} {body mins : Expr}
    (h : structMinorsPisR lps nP pw ((C, nF, cty, recIdx) :: cs) o body = some mins) :
    ∃ mty rest, structMinorTyR C lps nP nF o pw cty recIdx = some mty ∧
      structMinorsPisR lps nP pw cs (o + 1) body = some rest ∧
      mins = .forallE mty rest ⟨pw⟩ := by
  unfold structMinorsPisR at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

/-- The recursive minors' `λ`-telescope, one constructor peeled. -/
theorem structMinorsLamsR_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {recIdx : List Nat} {cs : List (Name × Nat × Expr × List Nat)}
    {o : Nat} {body mins : Expr}
    (h : structMinorsLamsR lps nP pw ((C, nF, cty, recIdx) :: cs) o body = some mins) :
    ∃ mty rest, structMinorTyR C lps nP nF o pw cty recIdx = some mty ∧
      structMinorsLamsR lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam mty rest ⟨pw⟩ := by
  unfold structMinorsLamsR at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

/-- The empty recursive `∀`-telescope is its body. -/
theorem structMinorsPisR_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : structMinorsPisR lps nP pw [] o body = some mins) : mins = body := by
  simp only [structMinorsPisR, Option.some.injEq] at h
  exact h.symm

/-- The empty recursive `λ`-telescope is its body. -/
theorem structMinorsLamsR_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : structMinorsLamsR lps nP pw [] o body = some mins) : mins = body := by
  simp only [structMinorsLamsR, Option.some.injEq] at h
  exact h.symm

/-- `structRecTyR`, unfolded to its five steps (`structRecTyI_unfold`
with the recursive minors). -/
theorem structRecTyR_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr × List Nat)}
    (h : structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ (tbs : List (Expr × BinderMeta)) (itele motiveTy major minors : Expr),
      tty.stripPis nP = some (tbs, itele) ∧
      structMotiveTyI T lps nP nIdx (structElimLevel elim large) itele = some motiveTy ∧
      Expr.replacePisPw (Level.zeronessOf (structElimLevel elim large)) nIdx
        (itele.liftLooseBVars (ctors.length + 1) 0)
        (.forallE (structFamI T lps nP nIdx (ctors.length + 1) 0)
          (Expr.mkAppN (.bvar (nIdx + ctors.length + 1)) (structPsAt 1 nIdx ++ [.bvar 0]))
          ⟨Level.zeronessOf (structElimLevel elim large)⟩) = some major ∧
      structMinorsPisR lps nP (Level.zeronessOf (structElimLevel elim large)) ctors 1 major
        = some minors ∧
      Expr.replacePisPw (Level.zeronessOf (structElimLevel elim large)) nP tty
        (.forallE motiveTy minors
          ⟨Level.zeronessOf (structElimLevel elim large)⟩) = some recTy := by
  unfold structRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, motiveTy, hmot, major, hmaj, minors, hmin, hr⟩ := h
  exact ⟨q.1, q.2, motiveTy, major, minors, hq, hmot, hmaj, hmin, hr⟩

/-- `structRecRhsR` at rule `j`, unfolded. -/
theorem structRecRhsR_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr × List Nat)} {j : Nat}
    {recC : Name} {rlvls : List Level}
    (h : structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some rhs) :
    ∃ (C : Name) (nF : Nat) (cty : Expr) (recIdx : List Nat)
      (tbs cbs : List (Expr × BinderMeta))
      (itele motiveTy crest0 inner minors : Expr),
      ctors[j]? = some (C, nF, cty, recIdx) ∧
      tty.stripPis nP = some (tbs, itele) ∧
      structMotiveTyI T lps nP nIdx (structElimLevel elim large) itele = some motiveTy ∧
      cty.stripPis nP = some (cbs, crest0) ∧
      Expr.pisToLamsPw (Level.zeronessOf (structElimLevel elim large)) nF
        (crest0.liftLooseBVars (ctors.length + 1) 0)
        (structRuleBodyR recC rlvls (Level.zeronessOf (structElimLevel elim large)) nP ctors.length nF
          j recIdx (structFieldTeleOf cty nP nF)
          (structFieldIdxOf cty nP nF)) = some inner ∧
      structMinorsLamsR lps nP (Level.zeronessOf (structElimLevel elim large)) ctors 1 inner
        = some minors ∧
      Expr.pisToLamsPw (Level.zeronessOf (structElimLevel elim large)) nP tty
        (.lam motiveTy minors
          ⟨Level.zeronessOf (structElimLevel elim large)⟩) = some rhs := by
  unfold structRecRhsR at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    obtain ⟨C, nF, cty, recIdx⟩ := c
    rw [hj] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tq, htq, motiveTy, hmot, q, hq, inner, hinner, minors, hminors, hr⟩ := h
    exact ⟨C, nF, cty, recIdx, tq.1, q.1, tq.2, motiveTy, q.2, inner, minors, rfl, htq, hmot,
      hq, hinner, hminors, hr⟩

/-! ## The index expression at the recursor's frame -/

/-- A lift raises the loose-bvar bound by the lift's amount. -/
theorem Expr.looseBVarsBounded_liftLooseBVars (k : Nat) :
    ∀ (e : Expr) {b c : Nat}, e.looseBVarsBounded b = true →
      (e.liftLooseBVars k c).looseBVarsBounded (b + k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro b c hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.liftLooseBVars]
    split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | fvar _ _ _ => intro b c _; rfl
  | sort _ => intro b c _; rfl
  | const _ _ => intro b c _; rfl
  | lit _ => intro b c _; rfl
  | app f a ihf iha =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf hb.1, iha hb.2⟩
  | lam ty body _ ihty ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty hb.1, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | forallE ty body _ ihty ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty hb.1, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | letE ty v body ihty ihv ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨⟨ihty hb.1.1, ihv hb.1.2⟩, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | proj _ _ e ih =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded] at hb ⊢
    exact ih hb

/-! ## Iterated variable shifts -/

/-- `Expr.shiftFrom p`, iterated `n` times: insert `n` fresh variable
slots at index `p`. -/
@[expose] def Expr.shiftFromN (p : Nat) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.shiftFrom p (Expr.shiftFromN p n e)

/-- A term without free variables is fixed by the shift. -/
theorem Expr.shiftFromN_eq_self_of_not_hasFvar {p : Nat} :
    ∀ (n : Nat) {e : Expr}, e.hasFvar = false → Expr.shiftFromN p n e = e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    show Expr.shiftFrom p (Expr.shiftFromN p n e) = e
    rw [Expr.shiftFromN_eq_self_of_not_hasFvar n h, Expr.shiftFrom_eq_self_of_not_hasFvar h]

/-- A shift bumps a free variable at or above the cut by one. -/
theorem Expr.shiftFromN_fvar (p : Nat) :
    ∀ (n idx : Nat) (ty : Expr),
      ∃ (ty' : Expr),
        Expr.shiftFromN p n (Expr.fvar idx ty)
          = Expr.fvar (if idx < p then idx else idx + n) ty'
  | 0, idx, ty => ⟨ty, by
      show Expr.fvar idx ty = _
      by_cases h : idx < p
      · rw [if_pos h]
      · rw [if_neg h, Nat.add_zero]⟩
  | n + 1, idx, ty => by
    obtain ⟨ty', hn⟩ := Expr.shiftFromN_fvar p n idx ty
    by_cases h : idx < p
    · refine ⟨ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_pos h, if_pos h]
      simp only [Expr.shiftFrom, if_neg (show ¬ idx ≥ p from by omega)]
    · refine ⟨Expr.shiftFrom p ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_neg h, if_neg h,
        show idx + (n + 1) = idx + n + 1 from by omega]
      simp only [Expr.shiftFrom, if_pos (show idx + n ≥ p from by omega)]

/-- Well-scopedness survives a shift, one slot up. -/
theorem Expr.WScoped_shiftFrom {p : Nat} :
    ∀ {e : Expr} {d : Nat}, Expr.WScoped d e → Expr.WScoped (d + 1) (Expr.shiftFrom p e) := by
  intro e
  induction e with
  | bvar i => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | sort u => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | const n us => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | lit l => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | fvar idx ty ih =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom]
    split
    · simp only [Expr.WScoped]
      exact ⟨by omega, ih hw.2⟩
    · simp only [Expr.WScoped]
      exact ⟨by omega, hw.2⟩
  | app f a ihf iha =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ihty ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihb hw.2⟩
  | forallE ty b bi ihty ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihb hw.2⟩
  | letE ty v b ihty ihv ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i e ih =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ih hw

/-- Well-scopedness survives an iterated shift, `n` slots up. -/
theorem Expr.WScoped_shiftFromN {p : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat},
      Expr.WScoped d e → Expr.WScoped (d + n) (Expr.shiftFromN p n e)
  | 0, _, _, hw => hw
  | n + 1, e, d, hw => by
    show Expr.WScoped (d + (n + 1)) (Expr.shiftFrom p (Expr.shiftFromN p n e))
    rw [show d + (n + 1) = d + n + 1 from by omega]
    exact Expr.WScoped_shiftFrom (Expr.WScoped_shiftFromN (p := p) n hw)

/-- A shift commutes with an instantiation sequence. -/
theorem Expr.shiftFrom_instSeq (p : Nat) :
    ∀ (sp : List Expr) (t : Nat) (e : Expr),
      Expr.shiftFrom p (instSeq sp t e)
        = instSeq (sp.map (Expr.shiftFrom p)) t (Expr.shiftFrom p e)
  | [], _, _ => rfl
  | a :: sp, t, e => by
    show Expr.shiftFrom p (instSeq sp (t - 1) (e.instantiate1 a t)) = _
    rw [Expr.shiftFrom_instSeq p sp (t - 1) (e.instantiate1 a t),
      Expr.shiftFrom_instantiate1_gen e t]
    rfl

/-- An iterated shift commutes with an instantiation sequence. -/
theorem Expr.shiftFromN_instSeq (p : Nat) :
    ∀ (n : Nat) (sp : List Expr) (t : Nat) (e : Expr),
      Expr.shiftFromN p n (instSeq sp t e)
        = instSeq (sp.map (Expr.shiftFromN p n)) t (Expr.shiftFromN p n e)
  | 0, sp, t, e => by simp [Expr.shiftFromN]
  | n + 1, sp, t, e => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (instSeq sp t e)) = _
    rw [Expr.shiftFromN_instSeq p n sp t e, Expr.shiftFrom_instSeq p]
    simp only [List.map_map]
    rfl

/-- Well-scopedness survives an instantiation sequence at well-scoped
arguments. -/
theorem Expr.instSeq_WScoped {d : Nat} :
    ∀ (sp : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ sp, Expr.WScoped d a) → Expr.WScoped d e → Expr.WScoped d (instSeq sp t e)
  | [], _, _, _, he => he
  | a :: sp, t, _e, hsp, he =>
    Expr.instSeq_WScoped sp (t - 1) (fun x hx => hsp x (List.mem_cons_of_mem _ hx))
      (Expr.WScoped.instantiate1_gen (hsp a List.mem_cons_self) t he)

/-! ## The rule body's spines -/

/-- The recursor's leading spine `p⃗ motive m⃗` in a rule body,
instantiated at the frame's own variables: the parameter and the extra
variables themselves. -/
theorem map_instSeq_structRecPrefixAt (tfvs extras xFvs : List Expr) {nP n nF : Nat}
    (hlenT : tfvs.length = nP) (hlenE : extras.length = n + 1) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true) :
    (structRecPrefixAt nP n nF 0).map
        (fun a => instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + n + nF) a))
      = tfvs ++ extras := by
  have hcl : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlen : (tfvs ++ extras).length = nP + n + 1 := by simp [hlenT, hlenE]; omega
  have hlenR : (structRecPrefixAt nP n nF 0).length = nP + n + 1 := by
    simp [structRecPrefixAt, structPsAt]
    omega
  have hlA : (structPsAt (0 + nF + n + 1) nP).length = nP := by simp [structPsAt]
  have hlAB : (structPsAt (0 + nF + n + 1) nP ++ [Expr.bvar (0 + nF + n)]).length = nP + 1 := by
    simp [structPsAt]
  have hget : ∀ k : Nat, k < nP + n + 1 →
      (structRecPrefixAt nP n nF 0)[k]? = some (Expr.bvar (nP + n + nF - k)) := by
    intro k hk
    unfold structRecPrefixAt
    by_cases hkp : k < nP
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [structPsAt, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range nP).length from by simp; omega),
        List.getElem_range, Option.map_some, Option.some.injEq]
      congr 1
      omega
    · by_cases hkm : k = nP
      · subst hkm
        rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hlA,
          Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), hlAB]
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem
            (show k - (nP + 1) < (List.range n).length from by simp; omega),
          List.getElem_range, Option.map_some, Option.some.injEq]
        congr 1
        omega
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  by_cases hk : k < nP + n + 1
  · rw [hget k hk, List.getElem?_eq_getElem (show k < (tfvs ++ extras).length from by
      rw [hlen]; omega)]
    simp only [Option.map_some, Option.some.injEq]
    have hb := Expr.instSeq_bvar (tfvs ++ extras) (nP + n + nF) (nP + n + nF - k) hcl
      (by omega) (by rw [hlen]; omega)
    rw [show nP + n + nF - (nP + n + nF - k) = k from by omega,
      List.getElem?_eq_getElem (show k < (tfvs ++ extras).length from by rw [hlen]; omega)] at hb
    rw [← Option.some.inj hb]
    exact Expr.instSeq_eq_self _ _ (hcl _ (List.getElem_mem _))
  · rw [List.getElem?_eq_none (by rw [hlenR]; omega),
      List.getElem?_eq_none (by rw [hlen]; omega)]
    rfl

end ConLeche

/-! ## No projection nodes in the generated recursor (task #210 Part A)

The table stage of a structure-like block on the fixpoint route needs
`NoProjEnv` at the recursor's cons: the generated recursor type and
rules mention no `.proj T j` node the former's and the constructors'
types do not (the sum route's `NoProjAt.structRecTy_list` for the
generators with the inductive hypotheses). -/

namespace ConLeche

namespace Expr

variable {T : Name} {i : Nat}

theorem NoProjAt.getAppArgs : ∀ {e : Expr}, NoProjAt T i e → ∀ a ∈ e.getAppArgs, NoProjAt T i a
  | .app f a, h, b, hb => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hb
    rw [noProjAt_app] at h
    rcases hb with hb | rfl
    · exact NoProjAt.getAppArgs h.1 b hb
    · exact h.2
  | .bvar _, _, _, hb | .fvar _ _, _, _, hb | .sort _, _, _, hb | .const _ _, _, _, hb
  | .lam _ _ _, _, _, hb | .forallE _ _ _, _, _, hb | .letE _ _ _, _, _, hb | .lit _, _, _, hb
  | .proj _ _ _, _, _, hb => by simp [Expr.getAppArgs] at hb

/-- The binder domains of a stripped telescope carry no projection node
of their body's telescope. -/
theorem NoProjAt.stripPis_doms :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis k = some (bs, body) → NoProjAt T i e → ∀ d ∈ bs, NoProjAt T i d.1
  | 0, e, bs, body, h, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; intro d hd; exact absurd hd List.not_mem_nil
  | k + 1, e, bs, body, h, he => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.stripPis] at h
      cases hs : rest.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [noProjAt_forallE] at he
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact he.1
        · exact NoProjAt.stripPis_doms k hs he.2 d hd
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

theorem NoProjAt.piBinders : ∀ {e : Expr}, NoProjAt T i e →
    (∀ d ∈ (Expr.piBinders e).1, NoProjAt T i d.1) ∧ NoProjAt T i (Expr.piBinders e).2
  | .forallE ty b m, h => by
    rw [noProjAt_forallE] at h
    obtain ⟨hbs, hbody⟩ := NoProjAt.piBinders h.2
    refine ⟨fun d hd => ?_, hbody⟩
    simp only [Expr.piBinders, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact h.1
    · exact hbs d hd
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
    ⟨fun d hd => by simp [Expr.piBinders] at hd, h⟩

theorem NoProjAt.mkPisOf : ∀ {bs : List (Expr × BinderMeta)} {b : Expr},
    (∀ d ∈ bs, NoProjAt T i d.1) → NoProjAt T i b → NoProjAt T i (Expr.mkPisOf bs b)
  | [], _, _, hb => hb
  | (ty, m) :: bs, b, hbs, hb => by
    simp only [Expr.mkPisOf, noProjAt_forallE]
    exact ⟨hbs _ List.mem_cons_self,
      NoProjAt.mkPisOf (fun d hd => hbs d (List.mem_cons_of_mem _ hd)) hb⟩

theorem NoProjAt.mkLamsOf : ∀ {bs : List (Expr × BinderMeta)} {b : Expr},
    (∀ d ∈ bs, NoProjAt T i d.1) → NoProjAt T i b → NoProjAt T i (Expr.mkLamsOf bs b)
  | [], _, _, hb => hb
  | (ty, m) :: bs, b, hbs, hb => by
    simp only [Expr.mkLamsOf, noProjAt_lam]
    exact ⟨hbs _ List.mem_cons_self,
      NoProjAt.mkLamsOf (fun d hd => hbs d (List.mem_cons_of_mem _ hd)) hb⟩

theorem NoProjAt.structTeleVars (m : Nat) : ∀ a ∈ structTeleVars m, NoProjAt T i a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  simp

theorem NoProjAt.structIdxAt {nF o j l m : Nat} {e : Expr} (h : NoProjAt T i e) :
    NoProjAt T i (structIdxAt nF o j l m e) :=
  h.liftLooseBVars.liftLooseBVars

theorem NoProjAt.structTeleAt {nF o j l : Nat} {pw : PropWhen}
    {tele : List (Expr × BinderMeta)} (h : ∀ d ∈ tele, NoProjAt T i d.1) :
    ∀ d ∈ structTeleAt nF o j l pw tele, NoProjAt T i d.1 := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
  have hlt : k < tele.length := List.mem_range.mp hk
  refine NoProjAt.structIdxAt (h _ ?_)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.getElem_mem hlt

theorem NoProjAt.structFieldTeleOf {cty : Expr} {nP nF j : Nat} (h : NoProjAt T i cty) :
    ∀ d ∈ structFieldTeleOf cty nP nF j, NoProjAt T i d.1 := by
  unfold ConLeche.structFieldTeleOf
  cases hs : cty.stripPis (nP + nF) with
  | none => intro d hd; simp at hd
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    intro d hd
    dsimp only at hd
    have hdoms := NoProjAt.stripPis_doms (nP + nF) hs h
    by_cases hlt : nP + j < cbs.length
    · have hmem : cbs.getD (nP + j) default ∈ cbs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      exact (NoProjAt.piBinders (hdoms _ hmem)).1 d hd
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hd
      have hdef : (Expr.piBinders (default : Expr × BinderMeta).1).1 = [] := rfl
      rw [Option.getD_none, hdef] at hd
      exact absurd hd List.not_mem_nil

theorem NoProjAt.structFieldIdxOf {cty : Expr} {nP nF j : Nat} (h : NoProjAt T i cty) :
    ∀ e ∈ structFieldIdxOf cty nP nF j, NoProjAt T i e := by
  unfold ConLeche.structFieldIdxOf
  cases hs : cty.stripPis (nP + nF) with
  | none => intro e he; simp at he
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    intro e he
    dsimp only at he
    have hdoms := NoProjAt.stripPis_doms (nP + nF) hs h
    by_cases hlt : nP + j < cbs.length
    · have hmem : cbs.getD (nP + j) default ∈ cbs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      exact NoProjAt.getAppArgs (NoProjAt.piBinders (hdoms _ hmem)).2 e (List.mem_of_mem_drop he)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
      have hdef : (Expr.piBinders (default : Expr × BinderMeta).1).2.getAppArgs = [] := rfl
      rw [Option.getD_none, hdef, List.drop_nil] at he
      exact absurd he List.not_mem_nil

theorem NoProjAt.structRecPrefixAt (nP n nF e : Nat) :
    ∀ a ∈ structRecPrefixAt nP n nF e, NoProjAt T i a := by
  intro a ha
  simp only [ConLeche.structRecPrefixAt, List.mem_append, List.mem_singleton, List.mem_map] at ha
  rcases ha with (ha | rfl) | ⟨k, -, rfl⟩
  · exact NoProjAt.structPsAt _ _ a ha
  · simp
  · simp

theorem NoProjAt.structIhApp {recC : Name} {rlvls : List Level} {pw : PropWhen}
    {nP n nF j : Nat} {tele : List (Expr × BinderMeta)} {idx : List Expr}
    (ht : ∀ d ∈ tele, NoProjAt T i d.1) (hidx : ∀ e ∈ idx, NoProjAt T i e) :
    NoProjAt T i (structIhApp recC rlvls pw nP n nF j tele idx) := by
  unfold ConLeche.structIhApp
  refine NoProjAt.mkLamsOf (NoProjAt.structTeleAt ht) ?_
  refine NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
  rcases ha with (ha | ⟨e, he, rfl⟩) | rfl
  · exact NoProjAt.structRecPrefixAt _ _ _ _ a ha
  · exact NoProjAt.structIdxAt (hidx e he)
  · exact NoProjAt.mkAppN (by simp) (NoProjAt.structTeleVars _)

theorem NoProjAt.structRuleBodyR {recC : Name} {rlvls : List Level} {pw : PropWhen}
    {nP n nF j : Nat} {recIdx : List Nat} {teleOf : Nat → List (Expr × BinderMeta)}
    {idxOf : Nat → List Expr}
    (ht : ∀ k, ∀ d ∈ teleOf k, NoProjAt T i d.1) (hidx : ∀ k, ∀ e ∈ idxOf k, NoProjAt T i e) :
    NoProjAt T i (structRuleBodyR recC rlvls pw nP n nF j recIdx teleOf idxOf) := by
  unfold ConLeche.structRuleBodyR
  refine NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_map] at ha
  rcases ha with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
  · simp
  · exact NoProjAt.structIhApp (ht k) (hidx k)

theorem NoProjAt.structIhPis {nF o : Nat} {pw : PropWhen} {teleOf : Nat → List (Expr × BinderMeta)}
    {idxOf : Nat → List Expr}
    (ht : ∀ k, ∀ d ∈ teleOf k, NoProjAt T i d.1) (hidx : ∀ k, ∀ e ∈ idxOf k, NoProjAt T i e) :
    ∀ {is : List Nat} {l : Nat} {body : Expr}, NoProjAt T i body →
      NoProjAt T i (structIhPis nF o pw teleOf idxOf is l body)
  | [], _, _, hb => hb
  | k :: is, l, body, hb => by
    simp only [ConLeche.structIhPis, noProjAt_forallE]
    refine ⟨NoProjAt.mkPisOf (NoProjAt.structTeleAt (ht k)) ?_, NoProjAt.structIhPis ht hidx hb⟩
    refine NoProjAt.mkAppN (by simp) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
    rcases ha with ⟨e, he, rfl⟩ | rfl
    · exact NoProjAt.structIdxAt (hidx k e he)
    · exact NoProjAt.mkAppN (by simp) (NoProjAt.structTeleVars _)

theorem NoProjAt.structMinorTyR {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} {recIdx : List Nat} (h : structMinorTyR C lps nP nF o pw cty recIdx = some mty)
    (hC : NoProjAt T i cty) : NoProjAt T i mty := by
  obtain ⟨cbs, fbs, crest0, res, hs, hr, hm⟩ := structMinorTyR_unfold h
  have hcrest : NoProjAt T i crest0 := NoProjAt.stripPis nP hs hC
  refine NoProjAt.replacePisPw nF hm hcrest.liftLooseBVars ?_
  refine NoProjAt.structIhPis (fun k => NoProjAt.structFieldTeleOf hC)
    (fun k => NoProjAt.structFieldIdxOf hC) ?_
  refine NoProjAt.liftLooseBVars ?_
  refine NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
  rcases ha with ⟨e, he, rfl⟩ | rfl
  · exact (NoProjAt.getAppArgs (NoProjAt.stripPis nF hr hcrest) e (List.mem_of_mem_drop he)).liftLooseBVars
  · exact NoProjAt.structCtorSpineAt _ _ _ _ _

theorem NoProjAt.structMinorsPisR {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {o : Nat} {body mins : Expr},
      structMinorsPisR lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, NoProjAt T i c.2.2.1) → NoProjAt T i body → NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [structMinorsPisR_nil h]; exact hb
  | (C, nF, cty, recIdx) :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := structMinorsPisR_cons h
    rw [noProjAt_forallE]
    exact ⟨NoProjAt.structMinorTyR hmty (hcs _ List.mem_cons_self),
      NoProjAt.structMinorsPisR hrest (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hb⟩

theorem NoProjAt.structMinorsLamsR {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {o : Nat} {body mins : Expr},
      structMinorsLamsR lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, NoProjAt T i c.2.2.1) → NoProjAt T i body → NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [structMinorsLamsR_nil h]; exact hb
  | (C, nF, cty, recIdx) :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := structMinorsLamsR_cons h
    rw [noProjAt_lam]
    exact ⟨NoProjAt.structMinorTyR hmty (hcs _ List.mem_cons_self),
      NoProjAt.structMinorsLamsR hrest (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hb⟩

theorem NoProjAt.structFamI (T' : Name) (lps : List Name) (nP nIdx e o : Nat) :
    NoProjAt T i (structFamI T' lps nP nIdx e o) := by
  unfold ConLeche.structFamI
  refine NoProjAt.mkAppN (by simp) ?_
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact NoProjAt.structPsAt _ _ a h
  · exact NoProjAt.structPsAt _ _ a h

theorem NoProjAt.structMotiveTyI {T' : Name} {lps : List Name} {nP nIdx : Nat} {ℓ : Level}
    {itele mty : Expr} (h : structMotiveTyI T' lps nP nIdx ℓ itele = some mty)
    (hI : NoProjAt T i itele) : NoProjAt T i mty := by
  unfold ConLeche.structMotiveTyI at h
  refine NoProjAt.replacePisPw nIdx h hI ?_
  simp only [noProjAt_forallE, noProjAt_sort, and_true]
  exact NoProjAt.structFamI _ _ _ _ _ _

/-- **The generated recursor type at a recursive block has no `.proj`
node** the type former's and the constructors' types do not have. -/
theorem NoProjAt.structRecTyR {T' : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr × List Nat)}
    (h : structRecTyR T' lps elim large nP nIdx tty ctors = some recTy)
    (hT : NoProjAt T i tty) (hC : ∀ c ∈ ctors, NoProjAt T i c.2.2.1) : NoProjAt T i recTy := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hs, hmot, hmaj, hmin, hr⟩ := structRecTyR_unfold h
  have hI : NoProjAt T i itele := NoProjAt.stripPis nP hs hT
  refine NoProjAt.replacePisPw nP hr hT ?_
  simp only [noProjAt_forallE]
  refine ⟨NoProjAt.structMotiveTyI hmot hI, NoProjAt.structMinorsPisR hmin hC ?_⟩
  refine NoProjAt.replacePisPw nIdx hmaj hI.liftLooseBVars ?_
  simp only [noProjAt_forallE]
  refine ⟨NoProjAt.structFamI _ _ _ _ _ _, NoProjAt.mkAppN (by simp) ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact NoProjAt.structPsAt _ _ a h
  · rcases List.mem_singleton.mp h with rfl; simp

/-- **The generated rules at a recursive block have no `.proj` node**
the type former's and the constructors' types do not have. -/
theorem NoProjAt.structRecRhsR {T' : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx j : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr × List Nat)}
    {recC : Name} {rlvls : List Level}
    (h : structRecRhsR T' lps elim large nP nIdx tty ctors recC rlvls j = some rhs)
    (hT : NoProjAt T i tty) (hC : ∀ c ∈ ctors, NoProjAt T i c.2.2.1) : NoProjAt T i rhs := by
  obtain ⟨C, nF, cty, recIdx, tbs, cbs, itele, motiveTy, crest0, inner, minors, hj, hs, hmot, hcs,
    hinner, hmins, hr⟩ := structRecRhsR_unfold h
  have hI : NoProjAt T i itele := NoProjAt.stripPis nP hs hT
  have hcty : NoProjAt T i cty := hC _ (List.mem_of_getElem? hj)
  have hcrest : NoProjAt T i crest0 := NoProjAt.stripPis nP hcs hcty
  have hinnerP : NoProjAt T i inner :=
    NoProjAt.pisToLamsPw nF hinner hcrest.liftLooseBVars
      (NoProjAt.structRuleBodyR (fun k => NoProjAt.structFieldTeleOf hcty)
        (fun k => NoProjAt.structFieldIdxOf hcty))
  refine NoProjAt.pisToLamsPw nP hr hT ?_
  rw [noProjAt_lam]
  exact ⟨NoProjAt.structMotiveTyI hmot hI, NoProjAt.structMinorsLamsR hmins hC hinnerP⟩

end Expr

end ConLeche
