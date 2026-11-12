import IxCC.Src.Semantics
import IxCC.Sem.Agrees

/-! # SrcEval in `bind` form

One equation per rule of SrcEval (`eval`, `evalConst`, `headValue`,
`apply`, `applyAll`, `fire`, `force`, `forceAll`), with every sequencing step
written as `Result.bind`. The definitions spell each step out as a
five-way `match`; these equations let clock monotonicity and the erasure
simulation reason one bind at a time. -/

namespace IxCC.Src

open IxCC.Sem (Result later later_zero later_succ)

variable (p : Program) (k : Nat) (ls : Levels) (ρ : Env)

/-! ## Terms -/

theorem eval_var (i : Nat) :
    eval p k ls ρ (.var i) = (match ρ[i]? with | some s => force p k s | none => .stuck) := by
  rw [eval]; rfl

theorem eval_var_of {i : Nat} {s : Slot} (h : ρ[i]? = some s) :
    eval p k ls ρ (.var i) = force p k s := by
  rw [eval_var, h]

theorem eval_sort (u : Ixon.Univ) : eval p k ls ρ (.sort u) = .ok (.irr (some (.sort u)) ρ ls) := by
  rw [eval]

theorem eval_pi (b : Binder) (res : Ixon.V3.ValueContract) (d c : Term) :
    eval p k ls ρ (.pi b res d c) = .ok (.irr (some (.pi b res d c)) ρ ls) := by
  rw [eval]

theorem eval_natLit (n : Nat) : eval p k ls ρ (.natLit n) = .ok (.lit n) := by
  rw [eval]

theorem eval_strLit (s : String) : eval p k ls ρ (.strLit s) = .ok (.str s) := by
  rw [eval]

theorem eval_lam (b : Binder) (d body : Term) :
    eval p k ls ρ (.lam b d body) = .ok (.clo b d body ρ ls) := by
  rw [eval]

theorem eval_letE (c : Ixon.V3.LetContract) (r : Rel) (ty v body : Term) :
    eval p k ls ρ (.letE c r ty v body) =
      if r.irrAt ls then eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body
      else (eval p k ls ρ v).bind fun x => eval p k ls (.val x :: ρ) body := by
  rw [eval]
  split
  · rfl
  · cases eval p k ls ρ v <;> rfl

theorem eval_proj (s i : Nat) (e : Term) :
    eval p k ls ρ (.proj s i e) = (eval p k ls ρ e).bind (p.projectField s i) := by
  rw [eval]; cases eval p k ls ρ e <;> rfl

theorem eval_app (f a : Term) (m : Mode) (r : Rel) :
    eval p k ls ρ (.app f a m r) = (eval p k ls ρ f).bind fun fv =>
      if r.irrAt ls then apply p k fv (.val (.irr (some a) ρ ls))
      else match m with
        | .strict => (eval p k ls ρ a).bind fun x => apply p k fv (.val x)
        | .byName => apply p k fv (.name a ρ ls) := by
  rw [eval]
  cases eval p k ls ρ f with
  | ok fv =>
    simp only [Result.bind]
    split
    · rfl
    · cases m <;> (try cases eval p k ls ρ a) <;> rfl
  | _ => rfl

theorem eval_const (c : CId) (us : List Ixon.Univ) :
    eval p k ls ρ (.const c us) = evalConst p k (us.map (evalUniv ls)) c := by
  rw [eval]

/-! ## Constants and heads -/

theorem evalConst_eq (c : CId) :
    evalConst p k ls c =
      match p.table.resolveOf c with
      | some (.prim op) => headValue p k ls (.prim op)
      | some (.word w op _) => headValue p k ls (.word w op)
      | some (.csimp g vs _) => later k fun k => eval p k ls [] (.const g vs)
      | some (.eqn _ body) => later k fun k => eval p k ls [] body
      | some (.case _) => headValue p k ls (.cases c)
      | none =>
        match p.decl? c with
        | some (.ctor ..) => headValue p k ls (.ctor c)
        | some (.recr ..) => headValue p k ls (.recr c)
        | some (.quot .ctor ..) => headValue p k ls (.quotMk c)
        | some (.quot .lift ..) => headValue p k ls (.quotLift c)
        | some (.defn .defn .safe _ _ v) => later k fun k => eval p k ls [] v
        | some (.defn .opaq .safe _ _ v) =>
          if p.table.isOpaqueByValue c then later k fun k => eval p k ls [] v else .stuck
        | _ => .stuck := by
  rw [evalConst.eq_def]
  cases k <;> rfl

theorem headValue_eq (h : Head) :
    headValue p k ls h = if p.headArity h == 0 then fire p k h ls [] else .ok (.pap h ls []) := by
  rw [headValue]

/-! ## Application -/

theorem apply_clo (b : Binder) (d body : Term) (ρ' : Env) (ls' : Levels) (s : Slot) :
    apply p k (.clo b d body ρ' ls') s =
      if b.propWhen.allowsBeta ls' then later k fun k => eval p k ls' (s :: ρ') body
      else .stuck := by
  rw [apply.eq_def]
  cases k <;> rfl

theorem apply_pap (h : Head) (ls' : Levels) (args : List Slot) (s : Slot) :
    apply p k (.pap h ls' args) s =
      if (args ++ [s]).length == p.headArity h then fire p k h ls' (args ++ [s])
      else if (args ++ [s]).length < p.headArity h then .ok (.pap h ls' (args ++ [s]))
      else .stuck := by
  rw [apply.eq_def]

theorem apply_other (f : Value) (s : Slot) (h₁ : ∀ b d body ρ' ls', f ≠ .clo b d body ρ' ls')
    (h₂ : ∀ h ls' args, f ≠ .pap h ls' args) : apply p k f s = .stuck := by
  rw [apply.eq_def]
  split
  · next b d body ρ' ls' => exact absurd rfl (h₁ b d body ρ' ls')
  · next h ls' args => exact absurd rfl (h₂ h ls' args)
  · rfl

theorem applyAll_nil (f : Value) : applyAll p k f [] = .ok f := by
  rw [applyAll]

theorem applyAll_cons (f : Value) (s : Slot) (ss : List Slot) :
    applyAll p k f (s :: ss) = (apply p k f s).bind fun v => applyAll p k v ss := by
  rw [applyAll]; cases apply p k f s <;> rfl

/-! ## Slots -/

theorem force_val (v : Value) : force p k (.val v) = .ok v := by
  rw [force]

theorem force_name (t : Term) (ρ' : Env) (ls' : Levels) :
    force p k (.name t ρ' ls') = later k fun k => eval p k ls' ρ' t := by
  rw [force.eq_def]; cases k <;> rfl

theorem forceAll_nil : forceAll p k [] = .ok [] := by
  rw [forceAll]

theorem forceAll_cons (s : Slot) (ss : List Slot) :
    forceAll p k (s :: ss) = (force p k s).bind fun v =>
      (forceAll p k ss).bind fun vs => .ok (v :: vs) := by
  rw [forceAll]
  cases force p k s <;> (try cases forceAll p k ss) <;> rfl

/-! ## Firing special heads -/

/-- F1's result on the forced fields. -/
def ctorResult (c : CId) (ls : Levels) (params : List Slot) (fields : List Value) :
    Result Value :=
  if some c == p.known.natZero then .ok (.lit 0)
  else if some c == p.known.natSucc then
    match fields with
    | [.lit n] => .ok (.lit (n + 1))
    | _ => .stuck
  else .ok (.con c ls params fields)

/-- F6's result on the forced arguments. -/
def primValue (op : PrimOp) (vs : List Value) : Result Value :=
  match litArgs vs with
  | some ns =>
    match op.evalLits ns with
    | some (.nat n) => .ok (.lit n)
    | some (.bool b) => p.boolValue b
    | none => .stuck
  | none => .stuck

/-- The rule and field slots a recursor chooses (F2–F4), at the clock after
its charge. -/
def recChosen (kind : RecKind) (ind np : CId) (majorIdx : Nat) (indices : List Slot)
    (args : List Slot) : Result (Nat × List Slot) :=
  match kind with
  | .empty => .trap
  | .ordinary =>
    (force p k (args.getD majorIdx default)).bind fun major =>
      Result.ofOption (p.selectRule ind np major)
  | .subsingleton _ srcs =>
    .ok (0, srcs.map fun
      | .index i => indices.getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls)

theorem fire_ctor (c : CId) (args : List Slot) :
    fire p k (.ctor c) ls args =
      match p.decl? c with
      | some (.ctor _ _ _ _ np _ _) =>
        (forceAll p k (args.drop np)).bind (ctorResult p c ls (args.take np))
      | _ => .stuck := by
  rw [fire.eq_def]
  simp only
  cases p.decl? c with
  | none => rfl
  | some d =>
    cases d with
    | ctor _ _ _ _ np _ _ => dsimp only; cases forceAll p k (args.drop np) <;> rfl
    | _ => rfl

theorem fire_quotMk (c : CId) (args : List Slot) :
    fire p k (.quotMk c) ls args =
      match args with
      | [α, r, a] => (force p k a).bind fun v => .ok (.con c ls [α, r] [v])
      | _ => .stuck := by
  rw [fire.eq_def]
  simp only
  match args with
  | [_, _, a] => dsimp only; cases force p k a <;> rfl
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

theorem fire_quotLift (c : CId) (args : List Slot) :
    fire p k (.quotLift c) ls args =
      later k fun k =>
        match args with
        | [_, _, _, f, _, q] =>
          (force p k q).bind fun qv =>
            match qv with
            | .con c' _ _ [a] =>
              if p.isQuotCtor c' then (force p k f).bind fun fv => apply p k fv (.val a)
              else .stuck
            | _ => .stuck
        | _ => .stuck := by
  rw [fire.eq_def]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [later_succ]
    match args with
    | [_, _, _, f, _, q] =>
      dsimp only
      cases force p k q with
      | ok qv =>
        simp only [Result.bind]
        match qv with
        | .con c' _ _ [a] =>
          dsimp only
          cases p.isQuotCtor c' with
          | true => cases force p k f <;> rfl
          | false => rfl
        | .con _ _ _ [] | .con _ _ _ (_ :: _ :: _) | .lit _ | .str _ | .clo .. | .pap .. | .irr .. =>
          rfl
      | _ => rfl
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem fire_recr (r : CId) (args : List Slot) :
    fire p k (.recr r) ls args =
      later k fun k =>
        match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
        | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind =>
          (recChosen p k ls kind ind np (np + nmot + nmin + ni)
              ((args.drop (np + nmot + nmin)).take ni) args).bind fun (j, fields) =>
            match rules[j]? with
            | some rule =>
              match peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs with
              | some body => eval p k ls (args.take (np + nmot + nmin) ++ fields).reverse body
              | none => .stuck
            | none => .stuck
        | _, _ => .stuck := by
  rw [fire.eq_def]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [later_succ]
    cases p.decl? r with
    | none => rfl
    | some d =>
      cases d with
      | recr _ _ _ np nmot nmin ni ind rules _ =>
        try dsimp only
        cases (p.table.recKindOf r).map (·.atLevels ls) with
        | none => rfl
        | some kind =>
          cases kind with
          | empty => rfl
          | ordinary =>
            simp only [recChosen]
            cases force p k (args.getD (np + nmot + nmin + ni) default) with
            | ok major =>
              simp only [Result.bind]
              cases p.selectRule ind np major <;> rfl
            | _ => rfl
          | subsingleton w srcs => rfl
      | _ => cases (p.table.recKindOf r).map (·.atLevels ls) <;> rfl

theorem fire_cases (c : CId) (args : List Slot) :
    fire p k (.cases c) ls args =
      later k fun k =>
        match p.table.resolveOf c with
        | some (.case r) =>
          match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
          | some (.recr _ _ _ np _ _ ni ind _ _), some kind =>
            (recChosen p k ls kind ind np (np + 1 + ni) (args.drop (np + 1)) args).bind
              fun (j, fields) =>
                (force p k (args.getD (np + 1 + ni + 1 + j) default)).bind fun minor =>
                  applyAll p k minor fields
          | _, _ => .stuck
        | _ => .stuck := by
  rw [fire.eq_def]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [later_succ]
    cases p.table.resolveOf c with
    | none => rfl
    | some res =>
      cases res with
      | case r =>
        simp only
        cases p.decl? r with
        | none => rfl
        | some d =>
          cases d with
          | recr _ _ _ np nmot nmin ni ind rules _ =>
            try dsimp only
            cases (p.table.recKindOf r).map (·.atLevels ls) with
            | none => rfl
            | some kind =>
              cases kind with
              | empty => rfl
              | ordinary =>
                simp only [recChosen]
                cases force p k (args.getD (np + 1 + ni) default) with
                | ok major =>
                  simp only [Result.bind]
                  cases p.selectRule ind np major with
                  | none => rfl
                  | some jf =>
                    simp only [Result.ofOption]
                    cases force p k (args.getD (np + 1 + ni + 1 + jf.1) default) <;> rfl
                | _ => rfl
              | subsingleton w srcs =>
                simp only [recChosen, Result.bind]
                cases force p k (args.getD (np + 1 + ni + 1 + 0) default) with
                | ok minor =>
                  dsimp only
                  congr 1
                  apply List.map_congr_left
                  intro s _
                  cases s with
                  | index i => simp [List.getD_eq_getElem?_getD]
                  | proof => rfl
                | _ => rfl
          | _ => cases (p.table.recKindOf r).map (·.atLevels ls) <;> rfl
      | _ => rfl

theorem fire_prim (op : PrimOp) (args : List Slot) :
    fire p k (.prim op) ls args = (forceAll p k args).bind (primValue p op) := by
  rw [fire.eq_def]
  simp only
  cases forceAll p k args <;> rfl

/-- F6w: a word operation on its forced arguments. -/
theorem fire_word (w : Width) (op : WordOp) (args : List Slot) :
    fire p k (.word w op) ls args = (forceAll p k args).bind (p.wordValue w op) := by
  rw [fire.eq_def]
  simp only
  cases forceAll p k args <;> rfl

theorem run_eq (root : CId) (xs : List Value) :
    run p k root xs = (evalConst p k [] root).bind fun f => applyAll p k f (xs.map .val) := by
  unfold run
  cases evalConst p k [] root <;> rfl

end IxCC.Src
