import IxCC.Anf.Semantics

/-! # Anf: basic properties

Determinism holds by construction (`eval` is a function; stated below). The
rules below are the ones the pass proofs read off directly: `tick`,
`jump`, `call`, a CAF `glob` and a non-empty application charge exactly one
unit; a function `glob` and a local `fn` are free; □ is stuck under
application, projection, `case` and primitives; a key mismatch in
`proj` is stuck. Clock monotonicity (`eval k … = r → r ≠ timeout → k ≤ k' →
eval k' … = r`) is proved (`Anf.eval_mono`); `tests-anf` also checks it on
the fixtures and on random clocks. -/

namespace IxCC.Anf

open IxCC.Sem (Result)

variable {P : Program} {k : Nat} {ρ : List Val} {J : List JClo}

theorem eval_deterministic {e : Exp} {r₁ r₂ : Result Val} (h₁ : eval P k ρ J e = r₁)
    (h₂ : eval P k ρ J e = r₂) : r₁ = r₂ := h₁ ▸ h₂

theorem eval_trap : eval P k ρ J .trap = .trap := by
  rw [eval]

theorem eval_ret (a : Atom) : eval P k ρ J (.ret a) = Result.ofOption (a.eval ρ) := by
  rw [eval]

theorem eval_tick_zero (e : Exp) : eval P 0 ρ J (.tick e) = .timeout := by
  rw [eval]

theorem eval_tick_succ (e : Exp) : eval P (k + 1) ρ J (.tick e) = eval P k ρ J e := by
  rw [eval]

theorem eval_join (n : Nat) (r : Bool) (b e : Exp) :
    eval P k ρ J (.join n r b e) = eval P k ρ (.mk ρ J n b r :: J) e := by
  rw [eval]

/-- A jump charges one unit and runs the join body in its own environments;
a recursive join point sees itself. -/
theorem eval_jump_succ {j : Nat} {as : List Atom} {ρ' : List Val} {J' : List JClo} {n : Nat}
    {b : Exp} {r : Bool} {vs : List Val} (hj : J[j]? = some (.mk ρ' J' n b r))
    (hv : evalAtoms ρ as = some vs) (hn : vs.length = n) :
    eval P (k + 1) ρ J (.jump j as) =
      eval P k (vs.reverse ++ ρ') (if r then .mk ρ' J' n b r :: J' else J') b := by
  rw [eval]; simp [hj, hv, hn]

theorem eval_jump_zero {j : Nat} {as : List Atom} :
    eval P 0 ρ J (.jump j as) = .timeout ∨ eval P 0 ρ J (.jump j as) = .stuck := by
  rw [eval]; split
  · split <;> simp
  · simp

/-- A function global's value is its closure, without a charge. -/
theorem evalBind_glob_fn {g : GlobalId} {gd : GDef} (h : P.global? g = some gd)
    (hps : gd.ps ≠ []) : evalBind P k ρ (.glob g) = .ok (.clos [] gd.ps.length gd.body []) := by
  rw [evalBind]; simp only [h]
  cases hp : gd.ps with
  | nil => exact absurd hp hps
  | cons _ _ => simp

/-- A CAF's value is its body's, one unit deeper. -/
theorem evalBind_glob_caf {g : GlobalId} {gd : GDef} (h : P.global? g = some gd)
    (hps : gd.ps = []) : evalBind P (k + 1) ρ (.glob g) = eval P k [] [] gd.body := by
  rw [evalBind]; simp [h, hps]

theorem evalBind_call_succ {g : GlobalId} {gd : GDef} {as : List Atom} {vs : List Val}
    (h : P.global? g = some gd) (hv : evalAtoms ρ as = some vs) (hn : vs.length = gd.ps.length) :
    evalBind P (k + 1) ρ (.call g as) = eval P k vs.reverse [] gd.body := by
  rw [evalBind]; simp [h, hv, hn]

theorem applyN_nil (f : Val) : applyN P k f [] = .ok f := by
  rw [applyN]

theorem applyN_zero (f : Val) (v : Val) (vs : List Val) :
    applyN P 0 f (v :: vs) = .timeout ∨ applyN P 0 f (v :: vs) = .stuck := by
  cases f <;> simp [applyN]

/-- □ is stuck under application. -/
theorem applyN_box (v : Val) (vs : List Val) : applyN P k .box (v :: vs) = .stuck := by
  rw [applyN]; intros; contradiction

/-- A constructor is stuck under application. -/
theorem applyN_con (c : Key.CtorKey) (fs : List Val) (v : Val) (vs : List Val) :
    applyN P k (.con c fs) (v :: vs) = .stuck := by
  rw [applyN]; intros; contradiction

/-- □ is stuck under projection. -/
theorem evalBind_proj_box {c : Key.CtorKey} {i : Nat} {x : Atom} (h : x.eval ρ = some .box) :
    evalBind P k ρ (.proj c i x) = .stuck := by
  rw [evalBind]; simp [h]

/-- A projection with another constructor's key is stuck. -/
theorem evalBind_proj_key {c c' : Key.CtorKey} {i : Nat} {x : Atom} {fs : List Val}
    (h : x.eval ρ = some (.con c' fs)) (hne : c' ≠ c) :
    evalBind P k ρ (.proj c i x) = .stuck := by
  rw [evalBind]; simp [h, hne]

/-- A `case` on □ is stuck. -/
theorem eval_case_box {x : Atom} {alts : List Alt} {d : Option Exp} (h : x.eval ρ = some .box) :
    eval P k ρ J (.case x alts d) = .stuck := by
  rw [eval]; simp [h, Val.asCtor]

/-- A primitive with a □ argument is stuck. -/
theorem primResult_box (K : Lam.Known) (p : Lam.Prim) (vs₁ vs₂ : List Val) :
    primResult K p (vs₁ ++ .box :: vs₂) = .stuck := by
  have : natArgs (vs₁ ++ .box :: vs₂) = none := by
    induction vs₁ with
    | nil => simp [natArgs]
    | cons v vs ih =>
      cases v with
      | lit l => cases l <;> simp [natArgs, ih]
      | _ => simp [natArgs]
  simp [primResult, this]

end IxCC.Anf
