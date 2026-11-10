import IxCC.Anf.Semantics
import IxCC.Sem.Agrees

/-! # Anf: the evaluator in `bind` form

One equation per rule of `Anf.eval`, `evalBind`, `applyN` and `evalAlts`,
with every sequencing step written as `Result.bind`, every charge as
`Sem.later`, and every partial lookup as `Result.ofOption` (decision D-1). The definitions spell
each step out as a `match`; the proofs of clock monotonicity (`Anf.Proof.Mono`) and of the passes
(P1–P4) reason through these equations only, one bind at a time, so that moving the evaluator to a
traced monad later changes these equations and not the per-construct
proofs. -/

set_option autoImplicit false

namespace IxCC.Anf

open IxCC.Sem (Result later)

variable (P : Program) (k : Nat) (ρ : List Val) (J : List JClo)

/-! ## Atoms -/

theorem evalAtoms_nil : evalAtoms ρ [] = some [] := rfl

theorem evalAtoms_cons (a : Atom) (as : List Atom) :
    evalAtoms ρ (a :: as) = (a.eval ρ).bind fun v => (evalAtoms ρ as).map (v :: ·) := by
  simp only [evalAtoms]
  cases a.eval ρ <;> cases evalAtoms ρ as <;> rfl

theorem evalAtoms_length : ∀ {as : List Atom} {vs : List Val}, evalAtoms ρ as = some vs →
    vs.length = as.length
  | [], vs, h => by simp [evalAtoms] at h; subst h; rfl
  | a :: as, vs, h => by
    rw [evalAtoms_cons] at h
    cases ha : a.eval ρ with
    | none => rw [ha] at h; cases h
    | some v =>
      rw [ha] at h
      cases hs : evalAtoms ρ as with
      | none => rw [hs] at h; cases h
      | some ws =>
        rw [hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [evalAtoms_length hs]

/-! ## Expressions -/

theorem eval_bind (c : Ixon.V3.LetContract) (b : Bind) (e : Exp) :
    eval P k ρ J (.bind c b e) = (evalBind P k ρ b).bind fun v => eval P k (v :: ρ) J e := by
  rw [eval]; cases evalBind P k ρ b <;> rfl

theorem eval_join' (n : Nat) (r : Bool) (b e : Exp) :
    eval P k ρ J (.join n r b e) = eval P k ρ (.mk ρ J n b r :: J) e := by
  rw [eval]

/-- A jump to a join closure with arguments. -/
def jumpTo (k : Nat) (jc : JClo) (vs : List Val) : Result Val :=
  match jc with
  | .mk ρ' J' n b r =>
    if vs.length = n then
      later k fun k => eval P k (vs.reverse ++ ρ') (if r then .mk ρ' J' n b r :: J' else J') b
    else .stuck

theorem eval_jump (j : Nat) (as : List Atom) :
    eval P k ρ J (.jump j as) =
      (Result.ofOption J[j]?).bind fun jc =>
        (Result.ofOption (evalAtoms ρ as)).bind fun vs => jumpTo P k jc vs := by
  rw [eval]
  cases J[j]? with
  | none => rfl
  | some jc =>
    obtain ⟨ρ', J', n, b, r⟩ := jc
    cases evalAtoms ρ as with
    | none => rfl
    | some vs =>
      simp only [Result.ofOption, Result.bind_ok, jumpTo]
      split
      · cases k <;> rfl
      · rfl

theorem eval_jump_of {j : Nat} {as : List Atom} {ρ' : List Val} {J' : List JClo} {n : Nat}
    {b : Exp} {r : Bool} {vs : List Val} (hj : J[j]? = some (.mk ρ' J' n b r))
    (hv : evalAtoms ρ as = some vs) (hn : vs.length = n) :
    eval P k ρ J (.jump j as) =
      later k fun k => eval P k (vs.reverse ++ ρ') (if r then .mk ρ' J' n b r :: J' else J') b := by
  rw [eval_jump, hj, hv]; simp [Result.ofOption, jumpTo, hn]

theorem eval_case (x : Atom) (alts : List Alt) (d : Option Exp) :
    eval P k ρ J (.case x alts d) = (Result.ofOption (x.eval ρ)).bind fun v =>
      match v.asCtor P.known with
      | some (c, fs) => evalAlts P k ρ J c fs alts d
      | none => .stuck := by
  rw [eval]; cases x.eval ρ <;> rfl

theorem eval_ret' (a : Atom) : eval P k ρ J (.ret a) = Result.ofOption (a.eval ρ) := by
  rw [eval]

theorem eval_tick (e : Exp) : eval P k ρ J (.tick e) = later k fun k => eval P k ρ J e := by
  cases k <;> (rw [eval]; try rfl)

theorem eval_trap' : eval P k ρ J .trap = .trap := by
  rw [eval]

/-! ## Right-hand sides -/

theorem evalBind_atom (a : Atom) : evalBind P k ρ (.atom a) = Result.ofOption (a.eval ρ) := by
  rw [evalBind]

theorem evalBind_con (c : Key.CtorKey) (as : List Atom) :
    evalBind P k ρ (.con c as) = (Result.ofOption (evalAtoms ρ as)).bind fun vs => .ok (.con c vs) := by
  rw [evalBind]; cases evalAtoms ρ as <;> rfl

/-- A projection of a value. -/
def projVal (c : Key.CtorKey) (i : Nat) : Val → Result Val
  | .con c' fs => if c' = c then Result.ofOption fs[i]? else .stuck
  | _ => .stuck

theorem evalBind_proj (c : Key.CtorKey) (i : Nat) (x : Atom) :
    evalBind P k ρ (.proj c i x) = (Result.ofOption (x.eval ρ)).bind (projVal c i) := by
  rw [evalBind]
  cases x.eval ρ with
  | none => rfl
  | some v => cases v <;> rfl

theorem evalBind_prim (p : Lam.Prim) (as : List Atom) :
    evalBind P k ρ (.prim p as) = (Result.ofOption (evalAtoms ρ as)).bind (primResult P.known p) := by
  rw [evalBind]; cases evalAtoms ρ as <;> rfl

/-- The value of a global: a function global's closure (free), or a CAF's
body one clock down. -/
def globVal (k : Nat) (gd : GDef) : Result Val :=
  match gd.ps with
  | [] => later k fun k => eval P k [] [] gd.body
  | _ :: _ => .ok (.clos [] gd.ps.length gd.body [])

theorem evalBind_glob (g : GlobalId) :
    evalBind P k ρ (.glob g) = (Result.ofOption (P.global? g)).bind (globVal P k) := by
  rw [evalBind]
  cases P.global? g with
  | none => rfl
  | some gd =>
    simp only [Result.ofOption, Result.bind_ok, globVal]
    cases gd.ps with
    | nil => cases k <;> rfl
    | cons _ _ => rfl

/-- Entering a global on argument values. -/
def callVal (k : Nat) (gd : GDef) (vs : List Val) : Result Val :=
  if vs.length = gd.ps.length then later k fun k => eval P k vs.reverse [] gd.body else .stuck

theorem evalBind_call (g : GlobalId) (as : List Atom) :
    evalBind P k ρ (.call g as) =
      (Result.ofOption (P.global? g)).bind fun gd =>
        (Result.ofOption (evalAtoms ρ as)).bind (callVal P k gd) := by
  rw [evalBind]
  cases P.global? g with
  | none => rfl
  | some gd =>
    cases evalAtoms ρ as with
    | none => rfl
    | some vs =>
      simp only [Result.ofOption, Result.bind_ok, callVal]
      split
      · cases k <;> rfl
      · rfl

theorem evalBind_call_of {g : GlobalId} {gd : GDef} {as : List Atom} {vs : List Val}
    (h : P.global? g = some gd) (hv : evalAtoms ρ as = some vs) (hn : vs.length = gd.ps.length) :
    evalBind P k ρ (.call g as) = later k fun k => eval P k vs.reverse [] gd.body := by
  rw [evalBind_call, h, hv]; simp [Result.ofOption, callVal, hn]

theorem evalBind_app (f : Atom) (as : List Atom) :
    evalBind P k ρ (.app f as) =
      (Result.ofOption (f.eval ρ)).bind fun fv =>
        (Result.ofOption (evalAtoms ρ as)).bind (applyN P k fv) := by
  rw [evalBind]
  cases f.eval ρ <;> cases evalAtoms ρ as <;> rfl

theorem evalBind_fn (ps : List Ixon.V3.BinderContract) (b : Exp) (hps : ps ≠ []) :
    evalBind P k ρ (.fn ps b) = .ok (.clos ρ ps.length b []) := by
  cases ps with
  | nil => exact absurd rfl hps
  | cons _ _ => rw [evalBind]

theorem evalBind_fn_nil (b : Exp) : evalBind P k ρ (.fn [] b) = .stuck := by
  rw [evalBind.eq_def]

/-! ## Application -/

theorem applyN_nil' (f : Val) : applyN P k f [] = .ok f := by
  rw [applyN]

/-- Entering a closure body with enough arguments, then applying the result
to the rest (one more charge when some remain). -/
def enter (k : Nat) (ρ' : List Val) (n : Nat) (b : Exp) (all : List Val) : Result Val :=
  (eval P k ((all.take n).reverse ++ ρ') [] b).bind fun r => applyN P (k + 1) r (all.drop n)

theorem applyN_clos (ρ' : List Val) (n : Nat) (b : Exp) (got : List Val) (v : Val)
    (rest : List Val) :
    applyN P k (.clos ρ' n b got) (v :: rest) =
      later k fun k =>
        if got.length < n then
          if got.length + (v :: rest).length < n then .ok (.clos ρ' n b (got ++ v :: rest))
          else enter P k ρ' n b (got ++ v :: rest)
        else .stuck := by
  cases k with
  | zero => rw [applyN]; rfl
  | succ k =>
    rw [applyN]
    simp only [IxCC.Sem.later_succ, dite_eq_ite, enter]
    split
    · split
      · rfl
      · cases eval P k (((got ++ v :: rest).take n).reverse ++ ρ') [] b <;> rfl
    · rfl

theorem applyN_not_clos (f : Val) (v : Val) (rest : List Val)
    (h : ∀ ρ' n b got, f ≠ .clos ρ' n b got) : applyN P k f (v :: rest) = .stuck := by
  rw [applyN]
  intro ρ' n b got e
  exact h ρ' n b got e

/-! ## Alternatives -/

theorem evalAlts_nil (c : Key.CtorKey) (fs : List Val) (d : Option Exp) :
    evalAlts P k ρ J c fs [] d = (match d with | some e => eval P k ρ J e | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (c : Key.CtorKey) (fs : List Val) (key : Key.CtorKey) (n : Nat) (body : Exp)
    (rest : List Alt) (d : Option Exp) :
    evalAlts P k ρ J c fs (.mk key n body :: rest) d =
      if key = c ∧ n = fs.length then eval P k (fs.reverse ++ ρ) J body
      else evalAlts P k ρ J c fs rest d := by
  rw [evalAlts]

/-! ## Runs -/

theorem run_eq (root : GlobalId) (xs : List Val) :
    run P k root xs = (evalBind P k [] (.glob root)).bind fun f => applyN P k f xs := by
  unfold run
  cases evalBind P k [] (.glob root) <;> rfl

end IxCC.Anf
