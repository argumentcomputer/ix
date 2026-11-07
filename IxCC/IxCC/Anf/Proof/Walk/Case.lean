import IxCC.Anf.Proof.Walk.Jump
import IxCC.Src.Proof.NatMap

/-! # The rewriting walk: alternatives and the case tests

What the walk's case tests say about evaluation: a case identity's arms
rebuild the scrutinee (`identityTail`; never a pinned `Nat` key, whose
literals are not constructors) and equal field-free arms (`sameArms`) make
the case's choice irrelevant. One fuel level of the walk's simulation for
`walkAlts`: each alternative's walk under its fields, with the scrutinee's
constructor view recorded as a fact (M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

/-! ## Case identity -/

/-- The common tail of an identity arm, by `identityTail`'s result. -/
def idTail : Option Nat → Exp
  | none => .ret (.var 0)
  | some j => .jump j [.var 0]

/-- `identityTail`'s per-arm test. -/
def tailOf (K : Lam.Known) : Alt → Option (Nat × Option Nat)
  | .mk key 0 b =>
    let ok := fun (key' : Key.CtorKey) => decide (key' = key) && !(K.natZero == some key)
    match Walk.stripTicks b with
    | (m, .bind _ (.con key' []) (.ret (.var 0))) => if ok key' then some (m, none) else none
    | (m, .bind _ (.con key' []) (.jump j [.var 0])) => if ok key' then some (m, some j) else none
    | _ => none
  | _ => none

theorem identityTail_eq (K : Lam.Known) (alts : List Alt) : Walk.identityTail K alts =
    (match alts with
     | [] => none
     | a :: rest =>
       match tailOf K a with
       | some t => if rest.all (fun b => tailOf K b == some t) then some t else none
       | none => none) := by
  cases alts with
  | nil => rfl
  | cons a rest => rfl

/-- An identity arm. -/
def IdArm (K : Lam.Known) (m : Nat) (t : Option Nat) (a : Alt) : Prop :=
  ∃ key c0, a = .mk key 0 (Walk.ticks m (.bind c0 (.con key []) (idTail t))) ∧ K.natZero ≠ some key

theorem tailOf_spec {K : Lam.Known} {a : Alt} {m : Nat} {t : Option Nat}
    (h : tailOf K a = some (m, t)) : IdArm K m t a := by
  unfold tailOf at h
  split at h
  · next key b =>
    dsimp only at h
    split at h
    · next m' c0 key' hb =>
      split at h
      · next hok =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
        obtain ⟨rfl, hz⟩ := hok
        exact ⟨key', c0, by rw [stripTicks_eq hb]; rfl, hz⟩
      · cases h
    · next m' c0 key' j hb =>
      split at h
      · next hok =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
        obtain ⟨rfl, hz⟩ := hok
        exact ⟨key', c0, by rw [stripTicks_eq hb]; rfl, hz⟩
      · cases h
    · cases h
  · cases h

theorem identityTail_spec {K : Lam.Known} {alts : List Alt} {m : Nat} {t : Option Nat}
    (h : Walk.identityTail K alts = some (m, t)) : alts ≠ [] ∧ ∀ a ∈ alts, IdArm K m t a := by
  rw [identityTail_eq] at h
  split at h
  · cases h
  · next a rest =>
    split at h
    · next t' ht =>
      split at h
      · next hall =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.cons_ne_nil _ _, fun b hb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact tailOf_spec ht
        · have := List.all_eq_true.1 hall b hb
          exact tailOf_spec (beq_iff_eq.1 this)
      · cases h
    · cases h

/-- A constructor view that is a field-free constructor key other than the
pinned `Nat.zero` is that constructor. -/
theorem asCtor_nil {K : Lam.Known} {v : Val} {c : Key.CtorKey} (h : v.asCtor K = some (c, []))
    (hz : K.natZero ≠ some c) : v = .con c [] := by
  cases v with
  | con c' fs => simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | lit l =>
    cases l with
    | nat m =>
      cases m with
      | zero =>
        simp only [Val.asCtor] at h
        obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
        cases he; exact absurd hc' hz
      | succ m =>
        simp only [Val.asCtor] at h
        obtain ⟨c', _, he⟩ := Option.map_eq_some_iff.1 h
        cases he
    | str s => simp [Val.asCtor] at h
  | clos => simp [Val.asCtor] at h
  | box => simp [Val.asCtor] at h

/-- The alternatives of a case identity either fail to match (stuck) or
take a field-free arm of the scrutinee's constructor. -/
theorem evalAlts_identity {P : Program} {ρ : List Val} {J : List JClo} {c : Key.CtorKey}
    {fs : List Val} {K : Lam.Known} {m : Nat} {t : Option Nat} :
    ∀ {alts : List Alt}, (∀ a ∈ alts, IdArm K m t a) →
    (∀ k, evalAlts P k ρ J c fs alts none = .stuck) ∨
      (fs = [] ∧ K.natZero ≠ some c ∧ ∃ c0, ∀ k, evalAlts P k ρ J c fs alts none =
        eval P k ρ J (Walk.ticks m (.bind c0 (.con c []) (idTail t))))
  | [], _ => .inl fun k => by rw [evalAlts_nil]
  | a :: rest, h => by
    obtain ⟨key, c0, rfl, hz⟩ := h a List.mem_cons_self
    by_cases hsel : key = c ∧ 0 = fs.length
    · obtain ⟨rfl, hl⟩ := hsel
      have hfs : fs = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst hfs
      exact .inr ⟨rfl, hz, c0, fun k => by rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩]; rfl⟩
    · have ih := evalAlts_identity (P := P) (ρ := ρ) (J := J) (c := c) (fs := fs)
        fun b hb => h b (List.mem_cons_of_mem _ hb)
      rcases ih with ih | ⟨h1, h2, c1, h3⟩
      · exact .inl fun k => by rw [evalAlts_cons, if_neg hsel, ih]
      · exact .inr ⟨h1, h2, c1, fun k => by rw [evalAlts_cons, if_neg hsel, h3]⟩

/-! ## Equal arms -/

theorem sameArms_spec {alts : List Alt} {dflt : Option Exp} {b : Exp}
    (h : Walk.sameArms alts dflt = some b) :
    (∀ a ∈ alts, a.arity = 0 ∧ a.body = b) ∧ (∀ e, dflt = some e → e = b) ∧ alts ≠ [] := by
  unfold Walk.sameArms at h
  split at h
  · cases h
  · next key b0 rest =>
    simp only [Option.ite_none_right_eq_some] at h
    obtain ⟨hc, h⟩ := h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨hall, hd⟩, _⟩ := hc
      refine ⟨fun a ha => ?_, fun e he => ?_, List.cons_ne_nil _ _⟩
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := hall a ha
          exact ⟨h1, Exp.beq_eq h2⟩
      · subst he
        exact Exp.beq_eq hd
  · cases h

/-- With equal field-free arms, the alternatives evaluate the common arm or
are stuck. -/
theorem evalAlts_same {P : Program} {ρ : List Val} {J : List JClo} {c : Key.CtorKey} {fs : List Val}
    {b : Exp} {dflt : Option Exp} (hd : ∀ e, dflt = some e → e = b) :
    ∀ {alts : List Alt}, (∀ a ∈ alts, a.arity = 0 ∧ a.body = b) →
    (∀ k, evalAlts P k ρ J c fs alts dflt = eval P k ρ J b) ∨ (∀ k, evalAlts P k ρ J c fs alts dflt = .stuck)
  | [], _ => by
    cases dflt with
    | none => exact .inr fun k => by rw [evalAlts_nil]
    | some e => exact .inl fun k => by rw [evalAlts_nil, hd e rfl]
  | .mk key m b' :: rest, h => by
    obtain ⟨hm, hb⟩ := h _ List.mem_cons_self
    simp only [Alt.arity, Alt.body] at hm hb
    subst hm hb
    by_cases hsel : key = c ∧ 0 = fs.length
    · have hfs : fs = [] := List.eq_nil_of_length_eq_zero hsel.2.symm
      subst hfs
      exact .inl fun k => by rw [evalAlts_cons, if_pos hsel]; rfl
    · rcases evalAlts_same (P := P) (ρ := ρ) (J := J) (c := c) (fs := fs) hd
          (fun a ha => h a (List.mem_cons_of_mem _ ha)) with ih | ih
      · exact .inl fun k => by rw [evalAlts_cons, if_neg hsel, ih]
      · exact .inr fun k => by rw [evalAlts_cons, if_neg hsel, ih]

/-! ## Alternatives -/

variable {P Q : Program} {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n fuel : Nat}

theorem walkAlts_step (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg}
    {env : Walk.Env} {here : Here} {xo : Opd} {alts : List Alt} {k : Kont} {alts' : List Alt}
    {s s' : Fires} (h : (Walk.walkAlts C (fuel + 1) env here xo alts k).run s = .ok (alts', s'))
    (ρ : List Val) (J : List JClo) (ρ' : List Val) (J' : List JClo) (live jlive : List Bool)
    (SK : Val → Nat → Result Val) (hV : VOk Q Valid Xc C ρ ρ') (henv : WEnv Q Valid Xc C live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ')
    (hnd : ∀ a ∈ alts, NoDead (List.replicate a.arity true ++ live) jlive a.body)
    (hk : KontW Q Valid Xc n k SK ρ' J')
    (c : Key.CtorKey) (fs fs' : List Val) (w : Val) (dflt : Option Exp) (dflt' : Option Exp)
    (hfs : WVs Q Valid Xc fs fs') (hw : xo.val ρ' = some w) (hc : w.asCtor Q.known = some (c, fs'))
    (hdflt : (dflt = none ∧ dflt' = none) ∨ ∃ e e', dflt = some e ∧ dflt' = some e' ∧
      SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J e).bind (SK · k)) (fun k => eval Q k ρ' J' e')) :
    SimUpTo (WV Q Valid Xc) n (fun k => (evalAlts P k ρ J c fs alts dflt).bind (SK · k))
      (fun k => evalAlts Q k ρ' J' c fs' alts' dflt') := by
  have hfl := hfs.length
  cases alts with
  | nil =>
    rw [Walk.walkAlts.eq_2 C (fuel + 1) env here xo k (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    rcases hdflt with ⟨rfl, rfl⟩ | ⟨e, e', rfl, rfl, hs⟩
    · exact (SimUpTo.stuck _).congr (fun k => by rw [evalAlts_nil]; rfl) (fun k => by rw [evalAlts_nil])
    · exact hs.congr (fun k => by rw [evalAlts_nil]) (fun k => by rw [evalAlts_nil])
  | cons a rest =>
    obtain ⟨key, m, b⟩ := a
    -- the alternative's walk, for any facts that hold once it is taken
    have halt : ∀ (facts' : Src.NatMap Fact) (b' : Exp) (s0 s0' : Fires),
        (Walk.walk C fuel { σ := Walk.entsOf (paramOpds here.d m) ++ env.σ, jσ := env.jσ }
          { d := here.d + m, dj := here.dj, facts := facts' } b k).run s0 = .ok (b', s0') →
        (key = c ∧ m = fs.length → FactsOk Q Valid facts' (fs'.reverse ++ ρ')) →
        (rest' : List Alt) → (s1 s1' : Fires) →
        (Walk.walkAlts C fuel env here xo rest k).run s1 = .ok (rest', s1') →
        SimUpTo (WV Q Valid Xc) n (fun k => (evalAlts P k ρ J c fs (.mk key m b :: rest) dflt).bind (SK · k))
          (fun k => evalAlts Q k ρ' J' c fs' (.mk key m b' :: rest') dflt') := by
      intro facts' b' s0 s0' hb hfacts rest' s1 s1' hrest
      by_cases hsel : key = c ∧ m = fs.length
      · have hsel' : key = c ∧ m = fs'.length := ⟨hsel.1, by rw [hfl]; exact hsel.2⟩
        have hsuf : ρ' <:+ fs'.reverse ++ ρ' := List.suffix_append _ _
        have hp := paramOpds_val ρ' fs'
        rw [← hsel'.2, ← hd] at hp
        have henvb := WEnv.pushOpds hp hfs.reverse (henv.suffix hsuf)
        rw [paramOpds_length] at henvb
        have hndb := hnd (.mk key m b) List.mem_cons_self
        simp only [Alt.arity, Alt.body] at hndb
        exact (hW.walk hb (fs.reverse ++ ρ) J (fs'.reverse ++ ρ') J' _ jlive SK
          (hctx.vsuffix hV (List.suffix_append _ _) hsuf) henvb (hJ.suffixK hsuf (List.suffix_refl _))
          (by simp [hd, hsel'.2]; omega) hdj (hfacts hsel) hndb (hk.suffix hsuf (List.suffix_refl _))).congr
          (fun k => by rw [evalAlts_cons, if_pos hsel]) (fun k => by rw [evalAlts_cons, if_pos hsel'])
      · have hsel' : ¬ (key = c ∧ m = fs'.length) := by rw [hfl]; exact hsel
        exact (hW.walkAlts hrest ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf
          (fun a ha => hnd a (List.mem_cons_of_mem _ ha)) hk c fs fs' w dflt dflt' hfs hw hc hdflt).congr
          (fun k => by rw [evalAlts_cons, if_neg hsel]) (fun k => by rw [evalAlts_cons, if_neg hsel'])
    cases xo with
    | lvl l =>
      rw [Walk.walkAlts.eq_3] at h
      obtain ⟨b', s1, h1, h⟩ := Walk.run_bind_ok h
      obtain ⟨rest', s2, h2, h⟩ := Walk.run_bind_ok h
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
      refine halt _ b' s s1 h1 (fun hsel l' f hl' => ?_) rest' s1 s2 h2
      rw [Src.NatMap.get?_insert] at hl'
      split at hl'
      · next hll =>
        subst hll
        simp only [Option.some.injEq] at hl'
        subst hl'
        refine ⟨w, fs', Opd.val_suffix (List.suffix_append _ _) hw, ?_, ?_⟩
        · rw [hd, hsel.2, ← hfl]
          exact fieldOpds_val ρ' fs'
        · rw [hc, hsel.1]
      · exact (hf l' f hl').suffix (List.suffix_append _ _)
    | lit lt =>
      rw [Walk.walkAlts.eq_4 C env here (.lit lt) k fuel key m b rest (fun l e => nomatch e)] at h
      obtain ⟨b', s1, h1, h⟩ := Walk.run_bind_ok h
      obtain ⟨rest', s2, h2, h⟩ := Walk.run_bind_ok h
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
      exact halt _ b' s s1 h1 (fun _ => hf.suffix (List.suffix_append _ _)) rest' s1 s2 h2
    | box =>
      rw [Walk.walkAlts.eq_4 C env here .box k fuel key m b rest (fun l e => nomatch e)] at h
      obtain ⟨b', s1, h1, h⟩ := Walk.run_bind_ok h
      obtain ⟨rest', s2, h2, h⟩ := Walk.run_bind_ok h
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
      exact halt _ b' s s1 h1 (fun _ => hf.suffix (List.suffix_append _ _)) rest' s1 s2 h2

end IxCC.Anf.WalkProof
