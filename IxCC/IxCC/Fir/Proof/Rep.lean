import IxCC.Fir.Rep
import IxCC.Fir.Proof.Unfold
import IxCC.Fir.Proof.Shape
import IxCC.Src.Proof.NatMap
import IxCC.Sem.Forall2

/-! # Representation Soundness (`Fir.Rep.check_sound`, `Fir.Proof.Rep.ofShapes_runSound`)

For the side path: whenever `Fir.Rep.check P cert = true`, every `.word`-annotated parameter,
local variable, join-point parameter, function return, and constructor scalar-tail field
evaluates in `Fir.eval` to `.lit (.nat n)` with `n < 2 ^ 64` (`check_sound`, `run_sound`), and
explicit `RepRhs.box` / `RepRhs.unbox` preserve exact `Fir.Val` values on `[0, 2 ^ 64)`.

For representations derived from a checked shape certificate (`Fir.Rep.ofShapes`): the same
invariant, from the shape checker's soundness alone (`ofShapes_valOk`, `ofShapes_envOk`,
`ofShapes_runSound`, `ofShapes_codeSound`).

Zero `sorry`, strictly standard axioms `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

namespace IxCC.Fir.Proof.Rep

open IxCC.Fir
open IxCC.Fir.Rep
open IxCC.Sem (Result Forall2)

/-! ## Value, Environment, and Join-Stack Representation Invariants -/

/-- Structural invariant on `Fir.Val`: every constructor value whose key has a `CtorRep` override
in `cert` stores `.lit (.nat n)` with `n < 2^64` in every scalar-tail field (`i ≥ cr.nobj`),
recursively across all fields. -/
inductive CtorValOk (cert : Cert) : Val → Prop where
  | lit (l : Lam.Lit) : CtorValOk cert (.lit l)
  | erased : CtorValOk cert .erased
  | ctor {c : CtorInfo} {fs : List Val}
      (hfields : ∀ v ∈ fs, CtorValOk cert v)
      (hscalar : ∀ cr, cert.ctorRep? c.key = some cr →
        ∀ i v, cr.nobj ≤ i → fs[i]? = some v → ∃ n < 2 ^ 64, v = .lit (.nat n)) :
      CtorValOk cert (.ctor c fs)

/-- A `Fir.Val` satisfies representation `r` under `cert`:
* `.word`: exact 64-bit unsigned natural `.lit (.nat n)` with `n < 2 ^ 64`;
* `.tobj` / `.obj`: structurally `CtorValOk cert v`;
* `.erased`: `False` (unused in Stage W2 certificates). -/
def ValOk (cert : Cert) : Fir.Rep → Val → Prop
  | .word, v => ∃ n < 2 ^ 64, v = .lit (.nat n)
  | .tobj, v => CtorValOk cert v
  | .obj, v => CtorValOk cert v
  | .erased, _ => False

theorem ValOk.ctorValOk {cert : Cert} {r : Fir.Rep} {v : Val} (h : ValOk cert r v) :
    CtorValOk cert v := by
  cases r with
  | word => obtain ⟨n, _, rfl⟩ := h; exact .lit (.nat n)
  | tobj => exact h
  | obj => exact h
  | erased => exact h.elim

theorem ValOk.of_word_to_obj {cert : Cert} {v : Val} (h : ValOk cert .word v) :
    ValOk cert .obj v := h.ctorValOk

theorem ValOk.of_tobj_to_obj {cert : Cert} {v : Val} (h : ValOk cert .tobj v) :
    ValOk cert .obj v := h

/-- Every bound variable in `ρ` satisfies its declared representation in `fc`. -/
def EnvOk (cert : Cert) (fc : FunCert) (ρ : Env) : Prop :=
  ∀ x v, ρ.get? x = some v → ValOk cert (fc.varRep x) v

theorem EnvOk.insert {cert : Cert} {fc : FunCert} {ρ : Env} (h : EnvOk cert fc ρ)
    {x : Var} {v : Val} (hv : ValOk cert (fc.varRep x) v) :
    EnvOk cert fc (ρ.insert x v) := by
  intro y w hy
  rw [Src.NatMap.get?_insert] at hy
  split at hy
  · rename_i heq; subst heq; cases hy; exact hv
  · exact h y w hy

theorem EnvOk.leaf (cert : Cert) (fc : FunCert) : EnvOk cert fc .leaf := by
  intro x v h; cases h

theorem EnvOk.bindAll {cert : Cert} {fc : FunCert} :
    ∀ {xs : List Var} {rs : List Fir.Rep} {vs : List Val} (ρ : Env),
      EnvOk cert fc ρ →
      checkParams fc xs rs = true →
      Forall2 (ValOk cert) rs vs →
      EnvOk cert fc (Fir.bindAll ρ xs vs)
  | [], [], [], _, hρ, _, _ => hρ
  | x :: xs, r :: rs, v :: vs, ρ, hρ, hp, .cons hv hvs => by
    simp only [checkParams, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨_, hrx⟩, hps⟩ := hp
    rw [← hrx] at hv
    exact EnvOk.bindAll (ρ.insert x v) (hρ.insert hv) hps hvs
  | [], _ :: _, _, _, _, hp, _ => by simp [checkParams] at hp
  | _ :: _, [], _, _, _, hp, _ => by simp [checkParams] at hp

/-! ## Compatibility Lemmas -/

theorem argCompat_sound {cert : Cert} {fc : FunCert} {ρ : Env} (hρ : EnvOk cert fc ρ)
    {a : Arg} {r : Fir.Rep} {v : Val}
    (hc : argCompat fc a r = true) (hv : a.eval ρ = some v) :
    ValOk cert r v := by
  cases r with
  | erased => simp [argCompat] at hc
  | word =>
    cases a with
    | var y =>
      simp only [argCompat, beq_iff_eq] at hc
      have hy := hρ y v hv
      rw [hc] at hy
      exact hy
    | lit l =>
      cases l with
      | nat n =>
        simp only [argCompat, decide_eq_true_eq] at hc
        simp only [Arg.eval, Option.some.injEq] at hv
        exact ⟨n, hc, hv.symm⟩
      | str _ => simp [argCompat] at hc
    | erased => simp [argCompat] at hc
  | tobj =>
    cases a with
    | var y =>
      simp only [argCompat, beq_iff_eq] at hc
      have hy := hρ y v hv
      rw [hc] at hy
      exact hy
    | lit l =>
      simp only [Arg.eval, Option.some.injEq] at hv
      subst hv
      exact .lit l
    | erased =>
      simp only [Arg.eval, Option.some.injEq] at hv
      subst hv
      exact .erased
  | obj =>
    cases a with
    | var y => exact (hρ y v hv).ctorValOk
    | lit l =>
      simp only [Arg.eval, Option.some.injEq] at hv
      subst hv
      exact .lit l
    | erased =>
      simp only [Arg.eval, Option.some.injEq] at hv
      subst hv
      exact .erased

theorem argsCompat_sound {cert : Cert} {fc : FunCert} {ρ : Env} (hρ : EnvOk cert fc ρ) :
    ∀ {as : List Arg} {rs : List Fir.Rep} {vs : List Val},
      argsCompat fc as rs = true →
      Fir.evalArgs ρ as = some vs →
      Forall2 (ValOk cert) rs vs
  | [], [], [], _, _ => .nil
  | a :: as, r :: rs, vs, hc, hvs => by
    simp only [argsCompat, Bool.and_eq_true] at hc
    rw [evalArgs_cons] at hvs
    cases ha : a.eval ρ with
    | none => rw [ha] at hvs; cases hvs
    | some v =>
      rw [ha] at hvs
      cases hrest : Fir.evalArgs ρ as with
      | none => rw [hrest] at hvs; cases hvs
      | some ws =>
        rw [hrest] at hvs
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        subst hvs
        exact .cons (argCompat_sound hρ hc.1 ha) (argsCompat_sound hρ hc.2 hrest)
  | [], [], _ :: _, _, hvs => by simp [evalArgs] at hvs
  | [], _ :: _, _, hc, _ => by simp [argsCompat] at hc
  | _ :: _, [], _, hc, _ => by simp [argsCompat] at hc

theorem evalArgs_all_ctorValOk {cert : Cert} {fc : FunCert} {ρ : Env} (hρ : EnvOk cert fc ρ) :
    ∀ {as : List Arg} {vs : List Val},
      Fir.evalArgs ρ as = some vs → ∀ v ∈ vs, CtorValOk cert v
  | [], [], _, _, hv => nomatch hv
  | a :: as, vs, hvs, w, hw => by
    rw [evalArgs_cons] at hvs
    cases ha : a.eval ρ with
    | none => rw [ha] at hvs; cases hvs
    | some v =>
      rw [ha] at hvs
      cases hrest : Fir.evalArgs ρ as with
      | none => rw [hrest] at hvs; cases hvs
      | some ws =>
        rw [hrest] at hvs
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        subst hvs
        rcases List.mem_cons.1 hw with rfl | hw'
        · cases a with
          | var y => exact (hρ y w ha).ctorValOk
          | lit l => simp [Arg.eval] at ha; subst ha; exact .lit l
          | erased => simp [Arg.eval] at ha; subst ha; exact .erased
        · exact evalArgs_all_ctorValOk hρ hrest w hw'

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys →
      ∀ {i : Nat} {a b}, xs[i]? = some a → ys[i]? = some b → R a b
  | [], [], .nil, _, _, _, hx, _ => by simp at hx
  | x :: xs, y :: ys, .cons hxy hrest, 0, a, b, hx, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx hy
    exact hxy
  | _ :: _, _ :: _, .cons _ hrest, i + 1, a, b, hx, hy =>
    forall2_getElem? hrest hx hy

theorem replicate_append_getElem? {α : Type} (n m : Nat) (x y : α) {i : Nat}
    (hge : n ≤ i) (hlt : i < n + m) :
    (List.replicate n x ++ List.replicate m y)[i]? = some y := by
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, List.getElem?_replicate]
  have : i - n < m := by omega
  simp [this]

/-! ## Right-Hand Side Soundness -/

theorem ctorRep_objRep_ne_word {P : Program} {cert : Cert}
    (hctors : cert.ctors.all (checkCtorRep P) = true) {k : Key.CtorKey} {cr : CtorRep}
    (hcr : cert.ctorRep? k = some cr) : cr.objRep ≠ .word := by
  have hmem : cr ∈ cert.ctors := List.mem_of_find?_eq_some hcr
  have hck := List.all_eq_true.1 hctors cr hmem
  simp only [checkCtorRep, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hck
  rcases hck.1.1.1.1.1 with h | h <;> rw [h] <;> decide

theorem checkRhs_sound {P : Program} {cert : Cert} {fc : FunCert} {ρ : Env}
    (hctors : cert.ctors.all (checkCtorRep P) = true)
    (hρ : EnvOk cert fc ρ) {x : Var} {rhs : Fir.Rhs} {v : Val}
    (hc : checkRhs P cert fc x rhs = true)
    (heval : Fir.evalRhs P ρ rhs = .ok v) :
    ValOk cert (fc.varRep x) v := by
  cases rhs with
  | arg a =>
    simp only [checkRhs, Bool.and_eq_true] at hc
    simp only [evalRhs, Result.ofOption] at heval
    cases ha : a.eval ρ with
    | none => simp [ha] at heval
    | some v' =>
      simp only [ha, Result.ok.injEq] at heval
      subst heval
      exact argCompat_sound hρ hc.2 ha
  | ctor c as =>
    simp only [checkRhs, Bool.and_eq_true] at hc
    obtain ⟨_, hbody⟩ := hc
    simp only [evalRhs] at heval
    cases hvs : Fir.evalArgs ρ as with
    | none => simp [hvs] at heval
    | some vs =>
      simp only [hvs] at heval
      split at heval
      · simp only [Result.ok.injEq] at heval
        subst heval
        simp only [Bool.or_eq_true, beq_iff_eq] at hbody
        obtain ⟨hrx, hargs⟩ := hbody
        have hcv : CtorValOk cert (.ctor c vs) := by
          refine .ctor (evalArgs_all_ctorValOk hρ hvs) ?_
          intro cr hcr i w hi hw
          rw [hcr] at hargs
          simp only [Bool.and_eq_true, beq_iff_eq] at hargs
          have hf2 := argsCompat_sound hρ hargs.2 hvs
          have hlenvs : vs.length = cr.nobj + cr.nscalar := by
            have := evalArgs_length ρ hvs
            rw [this, hargs.1]; rfl
          have hilt : i < cr.nobj + cr.nscalar := by
            have hlt := (List.getElem?_eq_some_iff.1 hw).1
            omega
          have hrep := replicate_append_getElem? cr.nobj cr.nscalar cr.objRep .word hi hilt
          exact forall2_getElem? hf2 hrep hw
        rcases hrx with hrx | hrx <;> rw [hrx] <;> exact hcv
      · cases heval
  | proj y c i =>
    simp only [checkRhs, Bool.and_eq_true] at hc
    obtain ⟨hvalid, hbody⟩ := hc
    simp only [evalRhs] at heval
    cases hy : ρ.get? y with
    | none => simp [hy] at heval
    | some vy =>
      simp only [hy] at heval
      cases hasc : vy.asCtor P.known with
      | none => simp [hasc] at heval
      | some pair =>
        obtain ⟨c', fs⟩ := pair
        simp only [hasc] at heval
        split at heval
        · rename_i hceq
          subst hceq
          cases hfi : fs[i]? with
          | none => simp [hfi, Result.ofOption] at heval
          | some fw =>
            simp only [hfi, Result.ofOption, Result.ok.injEq] at heval
            subst heval
            have hvy := hρ y vy hy
            by_cases hns : P.known.natSucc == some c'
            · simp only [hns, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbody
              have hcv : CtorValOk cert fw := by
                cases vy with
                | lit l =>
                  cases l with
                  | nat n =>
                    cases n with
                    | zero =>
                      simp only [Val.asCtor] at hasc
                      cases hz : P.known.natZero with
                      | none => simp [hz] at hasc
                      | some kz =>
                        simp only [hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hasc
                        obtain ⟨_, rfl⟩ := hasc
                        simp at hfi
                    | succ m =>
                      simp only [Val.asCtor] at hasc
                      cases hs : P.known.natSucc with
                      | none => simp [hs] at hasc
                      | some ks =>
                        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hasc
                        obtain ⟨_, rfl⟩ := hasc
                        cases i with
                        | zero => simp at hfi; subst hfi; exact .lit (.nat m)
                        | succ _ => simp at hfi
                  | str _ => simp [Val.asCtor] at hasc
                | ctor ci gs =>
                  simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hasc
                  obtain ⟨rfl, rfl⟩ := hasc
                  cases hvy.ctorValOk with
                  | ctor hfs _ => exact hfs fw (List.mem_of_getElem? hfi)
                | erased => simp [Val.asCtor] at hasc
              rcases hbody.2 with hrx | hrx <;> rw [hrx] <;> exact hcv
            · simp only [hns, Bool.false_eq_true, ↓reduceIte] at hbody
              by_cases hnz : P.known.natZero == some c'
              · simp [hnz] at hbody
              · simp only [hnz, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hbody
                obtain ⟨_, hmatch⟩ := hbody
                cases vy with
                | lit l =>
                  cases l with
                  | nat n =>
                    cases n with
                    | zero =>
                      simp only [Val.asCtor] at hasc
                      cases hz : P.known.natZero with
                      | none => simp [hz] at hasc
                      | some kz =>
                        simp only [hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hasc
                        obtain ⟨_, rfl⟩ := hasc
                        simp at hfi
                    | succ m =>
                      simp only [Val.asCtor] at hasc
                      cases hs : P.known.natSucc with
                      | none => simp [hs] at hasc
                      | some ks =>
                        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hasc
                        obtain ⟨rfl, _⟩ := hasc
                        exact absurd (by simp [hs]) hns
                  | str _ => simp [Val.asCtor] at hasc
                | erased => simp [Val.asCtor] at hasc
                | ctor ci gs =>
                  simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hasc
                  obtain ⟨rfl, rfl⟩ := hasc
                  cases hvy.ctorValOk with
                  | ctor hfs hsc =>
                    have hfw : CtorValOk cert fw := hfs fw (List.mem_of_getElem? hfi)
                    cases hrx : fc.varRep x with
                    | tobj => exact hfw
                    | obj => exact hfw
                    | erased => simp [hrx, isValidRep] at hvalid
                    | word =>
                      simp only [hrx] at hmatch
                      cases hfr : cert.fieldRep ci.key i with
                      | word =>
                        unfold Cert.fieldRep at hfr
                        cases hcr : cert.ctorRep? ci.key with
                        | none => simp [hcr] at hfr
                        | some cr =>
                          simp only [hcr, CtorRep.fieldRep] at hfr
                          split at hfr
                          · exact absurd hfr (ctorRep_objRep_ne_word hctors hcr)
                          · rename_i hge
                            exact hsc cr hcr i fw (Nat.le_of_not_lt hge) hfi
                      | tobj => simp [hfr] at hmatch
                      | obj => simp [hfr] at hmatch
                      | erased => simp [hfr] at hmatch
        · cases heval
  | prim op as =>
    simp only [checkRhs, Bool.and_eq_true] at hc
    obtain ⟨hvalid, hbody⟩ := hc
    have hna : op.isArr = false := by
      cases op <;> first | rfl | simp [Lam.Prim.isArr] at hbody
    simp only [evalRhs] at heval
    cases hvs : Fir.evalArgs ρ as with
    | none => simp [hvs] at heval
    | some vs =>
      simp only [hvs, primResult, arrResult_of_not_arr hna] at heval
      cases hns : Fir.natArgs vs with
      | none => simp [hns] at heval
      | some ns =>
        simp only [hns] at heval
        cases hsem : op.sem ns with
        | none => simp [hsem] at heval
        | some r =>
          simp only [hsem] at heval
          cases r with
          | nat n =>
            simp only [Result.ok.injEq] at heval
            subst heval
            cases op with
            | word w wo =>
              have hlt : n < 2 ^ 64 := Lam.wordSem_lt_u64 hsem
              cases hrx : fc.varRep x with
              | word => exact ⟨n, hlt, rfl⟩
              | tobj => exact .lit (.nat n)
              | obj => exact .lit (.nat n)
              | erased => simp [hrx, isValidRep] at hvalid
            | _ =>
              simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbody
              rcases hbody.2.1 with hrx | hrx <;> rw [hrx] <;> exact .lit (.nat n)
          | bool b =>
            cases op with
            | word w wo => exact absurd hsem (Lam.wordSem_ne_bool w wo ns b)
            | _ =>
              simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbody
              cases hb : boolVal P b with
              | none => simp [hb, Result.ofOption] at heval
              | some bv =>
                simp only [hb, Result.ofOption, Result.ok.injEq] at heval
                subst heval
                have hbv : CtorValOk cert bv := by
                  unfold boolVal at hb
                  cases hbk : (if b then P.known.boolTrue else P.known.boolFalse) with
                  | none => simp [hbk] at hb
                  | some ck =>
                    simp only [hbk] at hb
                    cases hci : P.ctorInfo? ck with
                    | none => simp [hci] at hb
                    | some ci =>
                      simp only [hci, Option.map_some, Option.some.injEq] at hb
                      subst hb
                      exact .ctor (fun _ h => nomatch h) (fun _ _ _ _ _ h => by simp at h)
                rcases hbody.2.1 with hrx | hrx <;> rw [hrx] <;> exact hbv
  | call _ _ => simp [evalRhs] at heval

/-! ## Join-Stack Invariant & Full Program Soundness (`check_sound`, `run_sound`) -/

/-- Every entry on the join stack has a well-typed captured environment, parameter reps matching
`fc.joinReps e.id`, and checked body. -/
inductive JStackOk (P : Program) (cert : Cert) (fc : FunCert) : List JEntry → Prop where
  | nil : JStackOk P cert fc []
  | cons {e : JEntry} {rest : List JEntry}
      (henv : EnvOk cert fc e.env)
      (hparams : checkParams fc e.params (fc.joinReps e.id) = true)
      (hbody : checkCode P cert fc e.body = true)
      (hrest : JStackOk P cert fc rest) :
      JStackOk P cert fc (e :: rest)

theorem lookupJ_ok {P : Program} {cert : Cert} {fc : FunCert} :
    ∀ {j : JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry},
      JStackOk P cert fc J →
      Fir.lookupJ j J = some (e, rest) →
      e.id = j ∧ EnvOk cert fc e.env ∧ checkParams fc e.params (fc.joinReps j) = true ∧
        checkCode P cert fc e.body = true ∧ JStackOk P cert fc rest
  | _, [], _, _, _, h => by cases h
  | j, e' :: J', e, rest, .cons henv hparams hbody hrest, h => by
    simp only [Fir.lookupJ] at h
    split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [heq] at hparams
      exact ⟨heq, henv, hparams, hbody, hrest⟩
    · exact lookupJ_ok hrest h

theorem check_ctors {P : Program} {cert : Cert} (h : check P cert = true) :
    cert.ctors.all (checkCtorRep P) = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1

theorem check_fun {P : Program} {cert : Cert} (h : check P cert = true) {f : FunId} {fd : Fun}
    (hf : f < P.size) (hfd : P.fun? f = some fd) : checkFun P cert f fd = true := by
  simp only [check, Bool.and_eq_true] at h
  have hmem : f ∈ List.range P.size := List.mem_range.2 hf
  have h1 := List.all_eq_true.1 h.2 f hmem
  simpa [hfd] using h1

private theorem check_sound_aux (P : Program) (cert : Cert) (hchk : check P cert = true) :
    ∀ (k : Nat) (w : Nat) (fc : FunCert) (ρ : Env) (J : List JEntry) (c : Code) (v : Val),
      c.size + Fir.jweight J ≤ w →
      EnvOk cert fc ρ →
      JStackOk P cert fc J →
      checkCode P cert fc c = true →
      Fir.eval P k ρ J c = .ok v →
      ValOk cert fc.ret v := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
    intro w
    induction w using Nat.strongRecOn with
    | ind w ihw =>
      intro fc ρ J c v hle hρ hJ hc heval
      have hctors := check_ctors hchk
      cases c with
      | trap =>
        rw [eval_trap] at heval; cases heval
      | ret a =>
        rw [eval_ret] at heval
        cases ha : a.eval ρ with
        | none => simp [ha, Result.ofOption] at heval
        | some v' =>
          simp only [ha, Result.ofOption, Result.ok.injEq] at heval
          subst heval
          exact argCompat_sound hρ hc ha
      | bind x rhs k' =>
        simp only [checkCode, Bool.and_eq_true] at hc
        obtain ⟨hrhs, hk'⟩ := hc
        have hlt : k'.size + Fir.jweight J < w := by
          simp only [Code.size] at hle; omega
        cases rhs with
        | call g as =>
          rw [eval_bindCall] at heval
          cases has : Fir.evalArgs ρ as with
          | none => simp [has, Result.ofOption, Result.bind] at heval
          | some vs =>
            simp only [has, Result.ofOption, Result.bind_ok] at heval
            cases hcall : Fir.evalCall P k g vs with
            | ok rv =>
              simp only [hcall, Result.bind_ok] at heval
              simp only [checkRhs, Bool.and_eq_true, decide_eq_true_eq] at hrhs
              obtain ⟨_, hgsize, hargs, hret⟩ := hrhs
              rw [evalCall_eq] at hcall
              cases hgd : P.fun? g with
              | none => simp [hgd, Result.ofOption, Result.bind] at hcall
              | some gd =>
                simp only [hgd, Result.ofOption, Result.bind_ok, callFun] at hcall
                split at hcall
                · cases k with
                  | zero => simp [Sem.later] at hcall
                  | succ k0 =>
                    simp only [Sem.later] at hcall
                    have hfg := check_fun hchk hgsize hgd
                    simp only [checkFun, Bool.and_eq_true] at hfg
                    obtain ⟨⟨_, hgp⟩, hgb⟩ := hfg
                    have hf2 := argsCompat_sound hρ hargs has
                    have hρg := EnvOk.bindAll .leaf (EnvOk.leaf cert (cert.funCert g)) hgp hf2
                    have hrv := ihk k0 (Nat.lt_succ_self k0) (gd.body.size + Fir.jweight [])
                      (cert.funCert g) _ [] gd.body rv (Nat.le_refl _) hρg .nil hgb hcall
                    have hxok : ValOk cert (fc.varRep x) rv := by
                      cases hgr : (cert.funCert g).ret <;> cases hxr : fc.varRep x <;>
                        simp [hgr, hxr] at hret ⊢ <;> rw [hgr] at hrv
                      · exact hrv
                      · exact hrv
                      · exact hrv
                      · exact hrv.ctorValOk
                      · exact hrv
                    exact ihw (k'.size + Fir.jweight J) hlt fc (ρ.insert x rv) J k' v
                      (Nat.le_refl _) (hρ.insert hxok) hJ hk' heval
                · cases hcall
            | stuck => simp [hcall, Result.bind] at heval
            | timeout => simp [hcall, Result.bind] at heval
            | trap => simp [hcall, Result.bind] at heval
            | resource _ => simp [hcall, Result.bind] at heval
        | arg a =>
          rw [eval_bind_arg] at heval
          cases hr : Fir.evalRhs P ρ (.arg a) with
          | ok rv =>
            simp only [hr, Result.bind_ok] at heval
            have hxok := checkRhs_sound hctors hρ hrhs hr
            exact ihw (k'.size + Fir.jweight J) hlt fc (ρ.insert x rv) J k' v
              (Nat.le_refl _) (hρ.insert hxok) hJ hk' heval
          | stuck => simp [hr, Result.bind] at heval
          | timeout => simp [hr, Result.bind] at heval
          | trap => simp [hr, Result.bind] at heval
          | resource _ => simp [hr, Result.bind] at heval
        | ctor ci as =>
          rw [eval_bind_ctor] at heval
          cases hr : Fir.evalRhs P ρ (.ctor ci as) with
          | ok rv =>
            simp only [hr, Result.bind_ok] at heval
            have hxok := checkRhs_sound hctors hρ hrhs hr
            exact ihw (k'.size + Fir.jweight J) hlt fc (ρ.insert x rv) J k' v
              (Nat.le_refl _) (hρ.insert hxok) hJ hk' heval
          | stuck => simp [hr, Result.bind] at heval
          | timeout => simp [hr, Result.bind] at heval
          | trap => simp [hr, Result.bind] at heval
          | resource _ => simp [hr, Result.bind] at heval
        | proj y ci i =>
          rw [eval_bind_proj] at heval
          cases hr : Fir.evalRhs P ρ (.proj y ci i) with
          | ok rv =>
            simp only [hr, Result.bind_ok] at heval
            have hxok := checkRhs_sound hctors hρ hrhs hr
            exact ihw (k'.size + Fir.jweight J) hlt fc (ρ.insert x rv) J k' v
              (Nat.le_refl _) (hρ.insert hxok) hJ hk' heval
          | stuck => simp [hr, Result.bind] at heval
          | timeout => simp [hr, Result.bind] at heval
          | trap => simp [hr, Result.bind] at heval
          | resource _ => simp [hr, Result.bind] at heval
        | prim op as =>
          rw [eval_bind_prim] at heval
          cases hr : Fir.evalRhs P ρ (.prim op as) with
          | ok rv =>
            simp only [hr, Result.bind_ok] at heval
            have hxok := checkRhs_sound hctors hρ hrhs hr
            exact ihw (k'.size + Fir.jweight J) hlt fc (ρ.insert x rv) J k' v
              (Nat.le_refl _) (hρ.insert hxok) hJ hk' heval
          | stuck => simp [hr, Result.bind] at heval
          | timeout => simp [hr, Result.bind] at heval
          | trap => simp [hr, Result.bind] at heval
          | resource _ => simp [hr, Result.bind] at heval
      | jp j ps isRec body k' =>
        rw [eval_jp] at heval
        simp only [checkCode, Bool.and_eq_true] at hc
        obtain ⟨⟨hps, hbody⟩, hk'⟩ := hc
        let e : JEntry := { id := j, charged := false, env := ρ, params := ps, body, isRec }
        have hlt : k'.size + Fir.jweight (e :: J) < w := by
          simp only [Code.size] at hle
          simp only [Fir.jweight, JEntry.weight, e, Bool.false_eq_true, ↓reduceIte]
          omega
        exact ihw (k'.size + Fir.jweight (e :: J)) hlt fc ρ (e :: J) k' v
          (Nat.le_refl _) hρ (.cons hρ hps hbody hJ) hk' heval
      | jmp j as =>
        rw [eval_jmp] at heval
        cases hlu : Fir.lookupJ j J with
        | none => simp [hlu, Result.ofOption, Result.bind] at heval
        | some pair =>
          obtain ⟨e, rest⟩ := pair
          simp only [hlu, Result.ofOption, Result.bind_ok] at heval
          cases has : Fir.evalArgs ρ as with
          | none => simp [has, Result.bind] at heval
          | some vs =>
            simp only [has, Result.bind_ok, jumpTo] at heval
            split at heval
            · obtain ⟨hid, henv, hparams, hbody, hrest⟩ := lookupJ_ok hJ hlu
              have hf2 := argsCompat_sound hρ hc has
              have hρ' := EnvOk.bindAll e.env henv hparams hf2
              have hJ' : JStackOk P cert fc (e.after rest) := by
                unfold JEntry.after
                split
                · exact .cons henv (by rw [hid]; exact hparams) hbody hrest
                · exact hrest
              split at heval
              · cases k with
                | zero => simp [Sem.later] at heval
                | succ k0 =>
                  simp only [Sem.later] at heval
                  exact ihk k0 (Nat.lt_succ_self k0) (e.body.size + Fir.jweight (e.after rest))
                    fc _ (e.after rest) e.body v (Nat.le_refl _) hρ' hJ' hbody heval
              · rename_i hch
                have hchf : e.charged = false := Bool.eq_false_iff.2 hch
                have hw := Fir.lookupJ_weight j hlu
                have hafter := JEntry.jweight_after e rest
                have hlt : e.body.size + Fir.jweight (e.after rest) < w := by
                  simp only [Code.size] at hle
                  simp only [JEntry.weight, hchf, Bool.false_eq_true, ↓reduceIte] at hw
                  omega
                exact ihw (e.body.size + Fir.jweight (e.after rest)) hlt fc _ (e.after rest)
                  e.body v (Nat.le_refl _) hρ' hJ' hbody heval
            · cases heval
      | case x alts d =>
        rw [eval_case] at heval
        simp only [checkCode, Bool.and_eq_true] at hc
        obtain ⟨⟨_, halts⟩, hd⟩ := hc
        cases hx : ρ.get? x with
        | none => simp [hx, Result.ofOption, Result.bind] at heval
        | some vx =>
          simp only [hx, Result.ofOption, Result.bind_ok] at heval
          cases hasc : vx.asCtor P.known with
          | none => simp [hasc] at heval
          | some pair =>
            obtain ⟨key, _⟩ := pair
            simp only [hasc] at heval
            have hwalk : ∀ (as' : List Alt),
                checkAlts P cert fc as' = true →
                Code.altsSize as' + Code.optSize d + 2 + Fir.jweight J ≤ w →
                Fir.evalAlts P k ρ J key as' d = .ok v →
                ValOk cert fc.ret v := by
              intro as'
              induction as' with
              | nil =>
                intro _ hsz he
                rw [evalAlts_nil] at he
                cases d with
                | none => cases he
                | some dc =>
                  have hlt : dc.size + Fir.jweight J < w := by
                    simp only [Code.altsSize, Code.optSize] at hsz; omega
                  exact ihw _ hlt fc ρ J dc v (Nat.le_refl _) hρ hJ hd he
              | cons a rest ihA =>
                cases a with
                | mk akey abody =>
                  intro hca hsz he
                  simp only [checkAlts, Bool.and_eq_true] at hca
                  rw [evalAlts_cons] at he
                  split at he
                  · have hlt : abody.size + Fir.jweight J < w := by
                      simp only [Code.altsSize] at hsz; omega
                    exact ihw _ hlt fc ρ J abody v (Nat.le_refl _) hρ hJ hca.1 he
                  · refine ihA hca.2 ?_ he
                    simp only [Code.altsSize] at hsz ⊢
                    omega
            exact hwalk alts halts (by simpa only [Code.size] using hle) heval
      | tcall g as =>
        rw [eval_tcall] at heval
        cases has : Fir.evalArgs ρ as with
        | none => simp [has, Result.ofOption, Result.bind] at heval
        | some vs =>
          simp only [has, Result.ofOption, Result.bind_ok] at heval
          simp only [checkCode, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          obtain ⟨hgsize, hargs, hret⟩ := hc
          rw [evalCall_eq] at heval
          cases hgd : P.fun? g with
          | none => simp [hgd, Result.ofOption, Result.bind] at heval
          | some gd =>
            simp only [hgd, Result.ofOption, Result.bind_ok, callFun] at heval
            split at heval
            · cases k with
              | zero => simp [Sem.later] at heval
              | succ k0 =>
                simp only [Sem.later] at heval
                have hfg := check_fun hchk hgsize hgd
                simp only [checkFun, Bool.and_eq_true] at hfg
                obtain ⟨⟨_, hgp⟩, hgb⟩ := hfg
                have hf2 := argsCompat_sound hρ hargs has
                have hρg := EnvOk.bindAll .leaf (EnvOk.leaf cert (cert.funCert g)) hgp hf2
                rw [← hret]
                exact ihk k0 (Nat.lt_succ_self k0) (gd.body.size + Fir.jweight [])
                  (cert.funCert g) _ [] gd.body v (Nat.le_refl _) hρg .nil hgb heval
            · cases heval

/-- **Representation soundness for checked Fir code**: any checked code evaluated under a
well-represented environment and join stack produces a value satisfying `fc.ret` (in particular,
`.lit (.nat n)` with `n < 2 ^ 64` whenever `fc.ret = .word`). -/
theorem check_sound {P : Program} {cert : Cert} (hchk : check P cert = true)
    {fc : FunCert} {k : Nat} {ρ : Env} {J : List JEntry} {c : Code} {v : Val}
    (hρ : EnvOk cert fc ρ) (hJ : JStackOk P cert fc J) (hc : checkCode P cert fc c = true)
    (heval : Fir.eval P k ρ J c = .ok v) :
    ValOk cert fc.ret v :=
  check_sound_aux P cert hchk k (c.size + Fir.jweight J) fc ρ J c v (Nat.le_refl _) hρ hJ hc heval

/-- **Program-level representation soundness**: calling any function `f < P.size` with arguments
satisfying `(cert.funCert f).params` returns a value satisfying `(cert.funCert f).ret`. -/
theorem run_sound {P : Program} {cert : Cert} (hchk : check P cert = true)
    {f : FunId} {k : Nat} {args : List Val} {v : Val}
    (hf : f < P.size)
    (hargs : Forall2 (ValOk cert) (cert.funCert f).params args)
    (hrun : Fir.run P k f args = .ok v) :
    ValOk cert (cert.funCert f).ret v := by
  rw [run_eq, evalCall_eq] at hrun
  cases hfd : P.fun? f with
  | none => simp [hfd, Result.ofOption, Result.bind] at hrun
  | some fd =>
    simp only [hfd, Result.ofOption, Result.bind_ok, callFun] at hrun
    split at hrun
    · cases k with
      | zero => simp [Sem.later] at hrun
      | succ k0 =>
        simp only [Sem.later] at hrun
        have hfun := check_fun hchk hf hfd
        simp only [checkFun, Bool.and_eq_true] at hfun
        obtain ⟨⟨_, hgp⟩, hgb⟩ := hfun
        have hρ := EnvOk.bindAll .leaf (EnvOk.leaf cert (cert.funCert f)) hgp hargs
        exact check_sound hchk hρ .nil hgb hrun
    · cases hrun

/-! ## Explicit `box` / `unbox` Value Preservation -/

theorem evalRepRhs_box_word {P : Program} {ρ : Env} {a : Arg} {n : Nat}
    (ha : a.eval ρ = some (.lit (.nat n))) (hlt : n < 2 ^ 64) :
    evalRepRhs P ρ (.box a) = .ok (.lit (.nat n)) := by
  simp [evalRepRhs, ha, hlt]

theorem evalRepRhs_unbox_word {P : Program} {ρ : Env} {a : Arg} {n : Nat}
    (ha : a.eval ρ = some (.lit (.nat n))) (hlt : n < 2 ^ 64) :
    evalRepRhs P ρ (.unbox a) = .ok (.lit (.nat n)) := by
  simp [evalRepRhs, ha, hlt]

/-! ## Representations derived from shapes: their facts are the shape checker's

`Fir.Rep.ofShapes` states no fact of its own. A `.word` position is one of shape `natLt b` with
`b ≤ 2^64`, and the shape checker's soundness (`Fir.Proof.Shape.checkSound`, `codeSound`) says it
holds a literal below `b`. So the representation invariant of the derived layout holds of every
run with no representation checker (`ofShapes_runSound`, `ofShapes_codeSound`). -/

section Shapes

open IxCC.Fir.Shape (FunShapes ShapeCert ArrEnc)

theorem natMap_get?_map {α β : Type} (f : α → β) :
    ∀ (m : Src.NatMap α) (k : Nat), (m.map f).get? k = (m.get? k).map f
  | .leaf, _ => rfl
  | .node v z o, k => by
    simp only [Src.NatMap.map, Src.NatMap.get?]
    split
    · rfl
    · split
      · exact natMap_get?_map f z (k / 2)
      · exact natMap_get?_map f o (k / 2)

/-- The derived layout has no scalar tails. -/
theorem ofShapes_ctorRep? (sc : ShapeCert) (k : Key.CtorKey) : (ofShapes sc).ctorRep? k = none :=
  rfl

mutual

/-- Every value is well formed under the derived layout: it overrides no constructor. -/
theorem ctorValOk_ofShapes (sc : ShapeCert) : (v : Val) → CtorValOk (ofShapes sc) v
  | .lit l => .lit l
  | .erased => .erased
  | .ctor _ fs =>
    .ctor (ctorValsOk_ofShapes sc fs) (fun cr h => by rw [ofShapes_ctorRep?] at h; cases h)

theorem ctorValsOk_ofShapes (sc : ShapeCert) : (fs : List Val) → ∀ v ∈ fs, CtorValOk (ofShapes sc) v
  | [] => fun _ h => absurd h List.not_mem_nil
  | x :: xs => fun v h =>
    match List.mem_cons.1 h with
    | .inl e => e ▸ ctorValOk_ofShapes sc x
    | .inr h' => ctorValsOk_ofShapes sc xs v h'

end

/-- **A shape's fact gives its representation's.** -/
theorem ofShapes_valOk {sc : ShapeCert} {enc : ArrEnc} {σ : IxCC.Shape.Shape} {v : Val}
    (h : Fir.Shape.ValOk sc enc σ v) : ValOk (ofShapes sc) σ.rep v := by
  cases σ with
  | natLt b =>
    obtain ⟨n, rfl, hn⟩ := IxCC.Fir.Proof.Shape.valOk_natLt_inv h
    by_cases hb : b ≤ 2 ^ 64
    · simp only [IxCC.Shape.Shape.rep, hb, ↓reduceIte, ValOk]
      exact ⟨n, Nat.lt_of_lt_of_le hn hb, rfl⟩
    · simp only [IxCC.Shape.Shape.rep, hb, ↓reduceIte, ValOk]
      exact ctorValOk_ofShapes sc _
  | word w =>
    obtain ⟨n, rfl, hn⟩ := IxCC.Fir.Proof.Shape.valOk_word_inv h
    have hw : w.size ≤ 2 ^ 64 := by cases w <;> decide
    simp only [IxCC.Shape.Shape.rep, ValOk]
    exact ⟨n, Nat.lt_of_lt_of_le hn hw, rfl⟩
  | _ => exact ctorValOk_ofShapes sc v

theorem ofShapes_funCert (sc : ShapeCert) (f : FunId) :
    (ofShapes sc).funCert f = funCertOf (sc.fn f) := by
  simp only [Cert.funCert, ofShapes, ShapeCert.fn, Src.NatMap.getD, natMap_get?_map]
  cases sc.funs.get? f <;> rfl

theorem funCertOf_varRep (fs : FunShapes) (x : Var) : (funCertOf fs).varRep x = (fs.var x).rep := by
  simp only [FunCert.varRep, funCertOf, FunShapes.var, Src.NatMap.getD, natMap_get?_map]
  cases fs.vars.get? x <;> rfl

theorem funCertOf_ret (fs : FunShapes) : (funCertOf fs).ret = fs.ret.rep := rfl

theorem funCertOf_params (fs : FunShapes) : (funCertOf fs).params = fs.params.map (·.rep) := rfl

theorem funCertOf_joinReps (fs : FunShapes) (j : JoinId) :
    (funCertOf fs).joinReps j = (fs.join j).map (·.rep) := by
  simp only [FunCert.joinReps, funCertOf, FunShapes.join, Src.NatMap.getD, natMap_get?_map]
  cases fs.joins.get? j <;> rfl

/-- An environment that has its shapes has the derived representations. -/
theorem ofShapes_envOk {sc : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env}
    (h : Fir.Shape.EnvOk sc enc fs ρ) : EnvOk (ofShapes sc) (funCertOf fs) ρ := by
  intro x v hx
  rw [funCertOf_varRep]
  exact ofShapes_valOk (h x v hx)

/-- A `.word` position of the derived layout holds a literal below `2^64` in an environment that
has its shapes: the fact a native back end reads to keep the position in a raw register. -/
theorem ofShapes_word {sc : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env} {x : Var}
    {v : Val} (hρ : Fir.Shape.EnvOk sc enc fs ρ) (hw : (funCertOf fs).varRep x = .word)
    (hx : ρ.get? x = some v) : ∃ n < 2 ^ 64, v = .lit (.nat n) := by
  have h := ofShapes_envOk hρ x v hx
  rw [hw] at h
  exact h

/-- **The derived layout holds of every run** of a program whose shape certificate checks:
called on arguments of its parameters' shapes, a function returns a value of its result's
representation. From `checkSound` alone; no representation checker is involved. -/
theorem ofShapes_runSound {P : Program} {sc : ShapeCert}
    (hchk : Fir.Shape.Checked P sc) {f : FunId} {k : Nat} {args : List Val} {v : Val}
    (hf : f < P.size) (hargs : Fir.Shape.ValsOk sc Fir.Shape.arrEnc (sc.fn f).params args)
    (hrun : Fir.run P k f args = .ok v) :
    ValOk (ofShapes sc) ((ofShapes sc).funCert f).ret v := by
  rw [ofShapes_funCert, funCertOf_ret]
  exact ofShapes_valOk (IxCC.Fir.Proof.Shape.checkSound P sc hchk f k args v hf hargs hrun)

/-- The same from inside a body, the form a back end's simulation carries. -/
theorem ofShapes_codeSound {P : Program} {sc : ShapeCert}
    (hchk : Fir.Shape.Checked P sc) {fs : FunShapes} {k : Nat} {ρ : Env} {c : Code} {v : Val}
    (hρ : Fir.Shape.EnvOk sc Fir.Shape.arrEnc fs ρ) (hc : Fir.Shape.CodeOk P sc fs c)
    (heval : Fir.eval P k ρ [] c = .ok v) : ValOk (ofShapes sc) (funCertOf fs).ret v :=
  ofShapes_valOk (IxCC.Fir.Proof.Shape.codeSound P sc hchk fs k ρ c v hρ hc heval)

end Shapes

end IxCC.Fir.Proof.Rep
