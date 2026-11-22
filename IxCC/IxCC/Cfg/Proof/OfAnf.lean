import IxCC.Cfg.Proof.Lang
import IxCC.Fir.Proof.Lowering

/-! # Anf → Cfg (`Cfg.ofAnf_correct`)

The Phase 1 path from Anf to Cfg (`Cfg.ofAnf`: `Fir.lower`, then
`Own.immortal`, then `Cfg.lower`) refines every Anf program it accepts, on
every input: the three refinements (`Fir.Proof.lower_refines`,
`Own.immortal_refines_lang`, `Cfg.lower_refines`) composed by
`Sem.Refines.trans`. What the later two need of `Fir.lower`'s output:

* its `Bool` pins have no fields where listed (`bools_of_lower`, from
  `Fir.Lower.pinsOk`);
* its immortal embedding is `Good` for `Cfg.lower_correct`
  (`immortal_good`): functions below the size, signatures as long as the
  parameters, and names bound by the lowering's supply above everything in
  scope (`Scoped`, `exp_scoped`: every variable lowering `e` binds is at
  least the supply it started from, and a join point's body binds above its
  parameters).

The passes compose as `Sem.Transform`s (`ofAnfPass`) and lift to traced
ones (`ofAnfTPass`, decision D-1). -/

set_option autoImplicit false

namespace IxCC.Cfg.Proof

open IxCC.Fir.Lower
open IxCC.Fir.Proof (exp_call exp_glob exp_atom exp_con exp_proj exp_prim exp_app exp_fn exp_join
  exp_jump exp_case exp_ret exp_tick exp_trap exps_nil exps_cons opt_none opt_some atomVar_inv exp_grows
  exps_grows Grows)

/-! ## Names -/

mutual

theorem Scoped.mono : ∀ {lo lo' : Nat} {c : Own.Code}, Scoped lo c → lo' ≤ lo → Scoped lo' c
  | _, _, .bind .., h, hle => ⟨Nat.le_trans hle h.1, h.2⟩
  | _, _, .jp .., h, hle =>
    ⟨fun p hp => Nat.le_trans hle (h.1 p hp),
      let ⟨lo₁, h₁, h₂, h₃⟩ := h.2.1; ⟨lo₁, Nat.le_trans hle h₁, h₂, h₃⟩, Scoped.mono h.2.2 hle⟩
  | _, _, .case .., h, hle => ⟨ScopedAlts.mono h.1 hle, ScopedOpt.mono h.2 hle⟩
  | _, _, .jmp .., _, _ | _, _, .ret _, _, _ | _, _, .tcall .., _, _ | _, _, .trap, _, _ => trivial

theorem ScopedAlts.mono : ∀ {lo lo' : Nat} {alts : List Own.Alt}, ScopedAlts lo alts → lo' ≤ lo →
    ScopedAlts lo' alts
  | _, _, [], _, _ => trivial
  | _, _, .mk .. :: _, h, hle => ⟨Scoped.mono h.1 hle, ScopedAlts.mono h.2 hle⟩

theorem ScopedOpt.mono : ∀ {lo lo' : Nat} {d : Option Own.Code}, ScopedOpt lo d → lo' ≤ lo → ScopedOpt lo' d
  | _, _, none, _, _ => trivial
  | _, _, some c, h, hle => Scoped.mono (c := c) h hle

end

/-- An arm's projections bind its used fields in increasing order. -/
theorem projections_scoped (y : Fir.Var) (key : Key.CtorKey) (body : Anf.Exp) (b : Fir.Code) :
    ∀ (m s i : Nat), Scoped (s + m) (Own.immCode b) →
      Scoped s (Own.immCode (projections y key body (List.range' s m) i b))
  | 0, s, i, h => by simpa [projections] using h
  | m + 1, s, i, h => by
    have ih := projections_scoped y key body b m (s + 1) (i + 1) (by rw [Nat.add_right_comm]; simpa [Nat.add_assoc] using h)
    simp only [List.range'_succ, projections]
    split
    · exact ⟨Nat.le_refl s, ih⟩
    · exact Scoped.mono ih (Nat.le_succ s)

mutual

/-- **Lowering binds above its supply**: every variable the embedding of
lowering `e` binds is at least the supply lowering started from. -/
theorem exp_scoped {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Fir.Var} {J : List Fir.JoinId} {st : St} {e : Anf.Exp} {c : Fir.Code} {st' : St},
      exp A g ρ J st e = .ok (c, st') → Scoped st.vars (Own.immCode c)
  | _, _, st, .bind cc b e, _, _, h => by
    cases b with
    | call h0 as =>
      obtain ⟨_, _, _, ⟨_, rfl, rfl⟩ | ⟨_, k, hk, rfl⟩⟩ := exp_call h
      · trivial
      · exact ⟨Nat.le_refl _, by simpa using exp_scoped hk⟩
    | glob h0 =>
      obtain ⟨_, _, _, _, ⟨_, rfl, rfl⟩ | ⟨_, k, hk, rfl⟩⟩ := exp_glob h
      · trivial
      · exact ⟨Nat.le_refl _, by simpa using exp_scoped hk⟩
    | atom a =>
      obtain ⟨_, k, _, hk, rfl⟩ := exp_atom h
      exact ⟨Nat.le_refl _, by simpa using exp_scoped hk⟩
    | con key as =>
      obtain ⟨_, _, k, _, _, _, hk, rfl⟩ := exp_con h
      exact ⟨Nat.le_refl _, by simpa using exp_scoped hk⟩
    | proj key i a =>
      obtain ⟨y, pre, st₁, k, hav, hk, rfl⟩ := exp_proj h
      have hk' := exp_scoped hk
      rcases atomVar_inv hav with ⟨_, _, _, rfl, rfl⟩ | ⟨arg, _, _, _, rfl, rfl⟩
      · exact ⟨Nat.le_refl _, by simpa using hk'⟩
      · exact ⟨Nat.le_refl _, Nat.le_refl _, by simpa using hk'⟩
    | prim p as =>
      obtain ⟨_, k, _, _, hk, rfl⟩ := exp_prim h
      exact ⟨Nat.le_refl _, by simpa using exp_scoped hk⟩
    | app f as => exact (exp_app h).elim
    | fn ps b => exact (exp_fn h).elim
  | _, _, st, .join n r b e, _, _, h => by
    obtain ⟨st₀, body, st₁, k, h₀v, -, hb, hk, rfl⟩ := exp_join h
    have g₀₁ := exp_grows hb
    simp only [Own.immCode, Scoped]
    refine ⟨fun p hp => ?_, ⟨st₀.vars, by omega, fun p hp => ?_, exp_scoped hb⟩, ?_⟩
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      simp only [List.mem_range'_1] at hx
      exact hx.1
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      simp only [List.mem_range'_1] at hx
      have := hx.2
      cfg_omega
    · exact Scoped.mono (exp_scoped hk) (by have := g₀₁.1; omega)
  | _, _, _, .jump j as, _, _, h => by
    obtain ⟨_, _, _, _, rfl, -⟩ := exp_jump h
    trivial
  | _, _, st, .case x alts d, _, _, h => by
    obtain ⟨y, pre, st₁, alts', st₂, d', hav, has, hd, rfl⟩ := exp_case h
    have gₐ := exps_grows has
    have hd' : ScopedOpt st₁.vars (Own.immOpt d') := ScopedOpt.mono (opt_scoped hd) (by have := gₐ.1; omega)
    have hcase : Scoped st₁.vars (Own.immCode (.case y alts' d')) := ⟨exps_scoped has, hd'⟩
    rcases atomVar_inv hav with ⟨_, _, _, rfl, rfl⟩ | ⟨arg, _, _, _, rfl, rfl⟩
    · exact hcase
    · exact ⟨Nat.le_refl _, by simpa using hcase⟩
  | _, _, _, .ret a, _, _, h => by
    obtain ⟨_, _, rfl, -⟩ := exp_ret h
    trivial
  | _, _, _, .tick e, _, _, h => exp_scoped (exp_tick h)
  | _, _, _, .trap, _, _, h => by
    obtain ⟨rfl, -⟩ := exp_trap h
    trivial

theorem exps_scoped {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Fir.Var} {J : List Fir.JoinId} {y : Fir.Var} {st : St} {alts : List Anf.Alt}
      {alts' : List Fir.Alt} {st' : St}, exps A g ρ J y st alts = .ok (alts', st') →
      ScopedAlts st.vars (Own.immAlts alts')
  | _, _, _, _, [], _, _, h => by
    obtain ⟨rfl, -⟩ := exps_nil h
    trivial
  | _, _, _, st, .mk key n body :: as, _, _, h => by
    obtain ⟨-, b, st₃, rest, hb, hr, rfl⟩ := exps_cons h
    have g₃ := exp_grows hb
    refine ⟨projections_scoped _ key body b n st.vars 0 (by simpa using exp_scoped hb), ?_⟩
    exact ScopedAlts.mono (exps_scoped hr) (by have := g₃.1; simp at this; omega)

theorem opt_scoped {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Fir.Var} {J : List Fir.JoinId} {st : St} {d : Option Anf.Exp} {d' : Option Fir.Code}
      {st' : St}, opt A g ρ J st d = .ok (d', st') → ScopedOpt st.vars (Own.immOpt d')
  | _, _, _, none, _, _, h => by
    obtain ⟨rfl, -⟩ := opt_none h
    trivial
  | _, _, _, some e, _, _, h => by
    obtain ⟨c, hc, rfl⟩ := opt_some h
    exact exp_scoped hc

end

/-! ## What `Fir.lower`'s output provides -/

/-- Every function of a lowering is a global below the size, lowered. -/
theorem lower_fun_inv {A : Anf.Program} {F : Fir.Program} (h : Fir.lower A = .ok F) {f : Fir.FunId}
    {fd : Fir.Fun} (hf : F.fun? f = some fd) :
    f < A.size ∧ ∃ gd, A.global? f = some gd ∧ function A f gd = .ok fd := by
  obtain ⟨_, _, _, fs, hfs, rfl⟩ := Fir.Proof.lower_ok h
  obtain ⟨hm, hall⟩ := Fir.Proof.functions_ok hfs
  have hn : (fs.map (·.1)).Nodup := by rw [hm]; exact List.nodup_range
  simp only [Fir.Program.fun?] at hf
  by_cases hk : f ∈ fs.map (·.1)
  · have hs : f < A.size := by rw [hm] at hk; exact List.mem_range.1 hk
    obtain ⟨⟨f', fd'⟩, hmem, hf'⟩ := List.mem_map.1 hk
    simp only at hf'
    subst hf'
    rw [Src.NatMap.get?_ofList hn hmem] at hf
    cases hf
    exact ⟨hs, hall _ _ hmem⟩
  · rw [get?_ofList_none hn hk] at hf
    cases hf

/-- **The `Bool` pins of a lowering have no fields** (`Fir.Lower.pinsOk`). -/
theorem bools_of_lower {A : Anf.Program} {F : Fir.Program} (h : Fir.lower A = .ok F) : Own.Proof.BoolsOk F := by
  obtain ⟨-, hp, -⟩ := Fir.Proof.lower_ok h
  obtain ⟨-, -, hc, hk⟩ := Fir.Proof.lower_fields h
  obtain ⟨-, -, hf, ht⟩ := Fir.Proof.pinsOk_parts hp
  intro b c info hb hi
  rw [hc] at hi
  rw [hk] at hb
  cases b with
  | true =>
    simp only [↓reduceIte] at hb
    rw [hb] at ht
    exact Fir.Proof.pinOk_some ht hi
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hb
    rw [hb] at hf
    exact Fir.Proof.pinOk_some hf hi

/-- **The immortal embedding of a lowering is `Good`** for
`Cfg.lower_correct`: its parameters are `0, …, n - 1` and its body binds
from the supply `n` up (`exp_scoped`). -/
theorem immortal_good {A : Anf.Program} {F : Fir.Program} (h : Fir.lower A = .ok F) :
    Good (Own.immortal F) where
  dense {f fd} hf := by
    rw [Own.Proof.immortal_fun?] at hf
    obtain ⟨fd', hfd', -⟩ := Option.map_eq_some_iff.1 hf
    show f < F.size
    rw [(Fir.Proof.lower_fields h).1]
    exact (lower_fun_inv h hfd').1
  sigLen {f fd} hf := by
    rw [Own.Proof.immortal_fun?] at hf
    obtain ⟨fd', -, rfl⟩ := Option.map_eq_some_iff.1 hf
    simp [Own.immFun]
  names {f fd} hf := by
    rw [Own.Proof.immortal_fun?] at hf
    obtain ⟨fd', hfd', rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨-, gd, -, hfn⟩ := lower_fun_inv h hfd'
    obtain ⟨st, he, hps⟩ := Fir.Proof.function_ok hfn
    refine ⟨gd.ps.length, fun p hp => ?_, exp_scoped he⟩
    simp only [Own.immFun, hps, List.map_map, List.mem_map, List.mem_range, Function.comp] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact hx

end IxCC.Cfg.Proof

namespace IxCC.Cfg

open IxCC.Cfg.Proof

/-- **Anf → Cfg refines**: every program the Phase 1 path accepts refines
its Anf program, on every input (`Sem.Refines.trans` of the three passes'
refinements). -/
theorem ofAnf_correct {A : Anf.Program} {C : Program} (h : ofAnf A = .ok C) : Sem.Refines A C := by
  unfold ofAnf at h
  cases hF : Fir.lower A with
  | error e => rw [hF] at h; cases h
  | ok F =>
    rw [hF] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    exact (Fir.Proof.lower_refines hF).trans
      ((Own.immortal_refines_lang (bools_of_lower hF)).trans (lower_refines (immortal_good hF)))

/-- `ofAnf_correct` in the traced shape (decision D-1). -/
theorem ofAnf_correct_traced {A : Anf.Program} {C : Program} (h : ofAnf A = .ok C) : Sem.TRefines A C :=
  Sem.Refines.ofPure (ofAnf_correct h)

/-- The Phase 1 path as a composed pass: `Fir.lower`, then the immortal
embedding (whose precondition is the image of `Fir.lower`), then
`Cfg.lower`. -/
def ofAnfPass : Sem.Transform Anf.Program Program :=
  (Fir.Proof.lowerPass.comp
      (Own.immortalPass (fun F => ∃ A, Fir.lower A = .ok F) (fun _ ⟨_, h⟩ => bools_of_lower h) Good
        (fun _ ⟨_, h⟩ => immortal_good h))
      fun _ h => h).comp
    lowerPass fun _ h => h

/-- The composed pass runs `ofAnf` (with the error rendered). -/
theorem ofAnfPass_run (A : Anf.Program) (c : ofAnfPass.Cert) :
    ofAnfPass.run A c = (ofAnf A).mapError (·.render) := by
  show ((((Fir.lower A).mapError (·.render)).bind fun F => .ok (Own.immortal F)).bind
    fun q => .ok (lower q)) = _
  unfold ofAnf
  cases Fir.lower A <;> rfl

/-- The composed pass as a traced one (decision D-1). -/
def ofAnfTPass : Sem.TTransform Anf.Program Program := ofAnfPass.lift

end IxCC.Cfg
