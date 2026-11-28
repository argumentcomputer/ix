import IxCC.Own.Plain.Proof.Owned.Context

/-! # The primitive step under a signature, as the checker computes it

Facts about `primStep` that need no heap: its definition unfolded (`primStep_eq`), what it is
when the signature consumes nothing (`primStep_noConsume`), and **conservativity**
(`primStep_conservative`): under `lamSig`, the signature of every primitive of today, the step is
`bindCtx`'s primitive case, the rule it replaces. So `bindStep`, what `checkCode` runs, is
`bindCtx` (`bindStep_eq_bindCtx`), and the checker accepts and refuses what it did, with the same
message. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var Arg)

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- The context after a primitive's result is bound, as `primStep` computes it. -/
def bindResult (Γ : Ctx) (x : Var) : ResUse → Ctx
  | .imm => Γ.setImmUniq x
  | .fresh true => Γ.addUniqOwn x
  | .fresh false => Γ.addOwn x 1
  | .borrowed _ => Γ.setBorrow x

/-- `primStep`, its `do` block written out. -/
theorem primStep_eq (Γ : Ctx) (sig : PrimSig) (x : Var) (args : List Arg) :
    primStep Γ sig x args =
      (Γ.needArgs args >>= fun _ =>
        takeConsumed Γ sig.args args >>= fun Γ₁ =>
          checkRead Γ₁ sig.args args >>= fun _ =>
            pure (bindResult
              (if sig.release then (markImm Γ₁ sig.args args).release
                else markImm Γ₁ sig.args args) x sig.result)) := by
  obtain ⟨uses, result, release⟩ := sig
  cases result with
  | imm => rfl
  | fresh unique => cases unique <;> rfl
  | borrowed ofArg => rfl

/-! ## The parts of the step -/

/-- **Today's rule is the scalar signature**: the mask of immediates the old rule applies is the
one `lamSig` gives. -/
theorem primImmArgs_eq_sig (op : Lam.Prim) (arity : Nat) :
    primImmArgs op arity = (lamSig op arity).args.map ArgUse.isImm := by
  cases op <;> simp [primImmArgs, lamSig, PrimSig.scalar, ArgUse.isImm]

/-- `markImm` is `Ctx.immArgs` over the signature's uses. -/
theorem markImm_eq_immArgs : ∀ (Γ : Ctx) (us : List ArgUse) (args : List Arg),
    markImm Γ us args = Ctx.immArgs Γ (us.map ArgUse.isImm) args
  | Γ, [], args => by cases args <;> rfl
  | Γ, u :: us, [] => by cases u <;> rfl
  | Γ, u :: us, a :: as => by
    cases u <;> cases a <;>
      simp only [markImm, Ctx.immArgs, List.map_cons, ArgUse.isImm] <;>
      exact markImm_eq_immArgs _ us as

/-- A signature that consumes no argument takes no token. -/
theorem takeConsumed_noConsume : ∀ (Γ : Ctx) {us : List ArgUse} (args : List Arg),
    (∀ u, u ∈ us → u ≠ .consume) → takeConsumed Γ us args = .ok Γ
  | Γ, [], args, _ => by cases args <;> rfl
  | Γ, u :: us, [], _ => by cases u <;> rfl
  | Γ, u :: us, a :: as, h => by
    have ih := takeConsumed_noConsume Γ as (fun v hv => h v (List.mem_cons_of_mem _ hv))
    cases u with
    | consume => exact absurd rfl (h .consume List.mem_cons_self)
    | imm => cases a <;> simp only [takeConsumed] <;> exact ih
    | read => cases a <;> simp only [takeConsumed] <;> exact ih

/-- What `checkRead` asks of a variable is that it is available: held as an immediate, by a
token, by the caller, or still borrowed in this epoch. -/
theorem Ctx.held_eq_avail (Γ : Ctx) (x : Var) : (Γ.borrowable x || Γ.borrowed x) = Γ.avail x := by
  rw [Ctx.borrowable_eq, Ctx.avail_eq]
  generalize Γ.isImm x = a
  generalize Γ.isPbrw x = b
  generalize decide (0 < Γ.tokens x) = c
  generalize Γ.borrowed x = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Arguments that are available pass `checkRead`, whatever the signature. -/
theorem checkRead_of_avail (Γ : Ctx) : ∀ (us : List ArgUse) (args : List Arg),
    (∀ x, Arg.var x ∈ args → Γ.avail x = true) → checkRead Γ us args = .ok ()
  | [], args, _ => by cases args <;> rfl
  | u :: us, [], _ => by cases u <;> rfl
  | u :: us, a :: as, h => by
    have ih := checkRead_of_avail Γ us as (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases a with
    | var x =>
      have hx : (Γ.borrowable x || Γ.borrowed x) = true := by
        rw [Ctx.held_eq_avail]; exact h x List.mem_cons_self
      cases u <;> simp only [checkRead, hx, ↓reduceIte] <;> exact ih
    | lit l => cases u <;> simp only [checkRead] <;> exact ih
    | erased => cases u <;> simp only [checkRead] <;> exact ih

/-- What `checkRead` established: a variable in a position the signature does not consume is
still available after the consumed arguments were taken. -/
theorem checkRead_held {Γ : Ctx} : ∀ {us : List ArgUse} {args : List Arg},
    checkRead Γ us args = .ok () →
    ∀ (i : Nat) (u : ArgUse) (y : Var), us[i]? = some u → u ≠ .consume →
      args[i]? = some (.var y) → Γ.avail y = true
  | [], _, _, i, u, y, hu, _, _ => by simp at hu
  | _ :: _, [], _, i, u, y, _, _, hy => by simp at hy
  | u₀ :: us, a :: as, h, i, u, y, hu, hne, hy => by
    cases i with
    | zero =>
      have hu0 : u₀ = u := by simpa using hu
      have ha : a = .var y := by simpa using hy
      subst hu0; subst ha
      rw [← Ctx.held_eq_avail]
      cases u₀ with
      | consume => exact absurd rfl hne
      | imm =>
        simp only [checkRead] at h
        split at h
        · assumption
        · cases h
      | read =>
        simp only [checkRead] at h
        split at h
        · assumption
        · cases h
    | succ i =>
      have hu' : us[i]? = some u := by simpa using hu
      have hy' : as[i]? = some (.var y) := by simpa using hy
      have h' : checkRead Γ us as = .ok () := by
        cases u₀ <;> cases a <;> simp only [checkRead] at h <;>
          first
          | exact h
          | (split at h
             · exact h
             · cases h)
      exact checkRead_held h' i u y hu' hne hy'

/-! ## The step when nothing is consumed, and conservativity -/

/-- With no consumed argument the step is: the arguments available, the marked ones immediates,
a release if the signature says so, the result bound. -/
theorem primStep_noConsume (Γ : Ctx) {sig : PrimSig} (x : Var) (args : List Arg)
    (hno : ∀ u, u ∈ sig.args → u ≠ .consume) :
    primStep Γ sig x args =
      (Γ.needArgs args >>= fun _ =>
        pure (bindResult
          (if sig.release then (markImm Γ sig.args args).release else markImm Γ sig.args args)
          x sig.result)) := by
  rw [primStep_eq]
  cases hneed : Γ.needArgs args with
  | error e => rfl
  | ok u =>
    cases u
    rw [except_ok_bind, except_ok_bind, takeConsumed_noConsume Γ args hno, except_ok_bind,
      checkRead_of_avail Γ sig.args args (Ctx.needArgs_avail hneed), except_ok_bind]

/-- **`PrimStepConservative`.** The step under a signature is today's `bindCtx` case on today's
primitives: the checker run on signatures accepts exactly the candidates it accepted, and
refuses the others with the same message, until a primitive has a signature other than
`PrimSig.scalar`. -/
theorem primStep_conservative (Γ : Ctx) (op : Lam.Prim) (x : Var) (args : List Arg) :
    primStep Γ (lamSig op args.length) x args = bindCtx Γ x (.prim op args) := by
  rw [primStep_noConsume Γ x args (fun u hu => by
    have : u = .imm := List.eq_of_mem_replicate hu
    subst this
    exact fun h => by cases h)]
  rw [markImm_eq_immArgs, ← primImmArgs_eq_sig]
  rfl

/-- An accepted primitive step: the primitive is not an array one (`own.arrays`), and the step
was `primStep` under `lamSig`. -/
theorem bindStep_prim {Γ Γ' : Ctx} {x : Var} {op : Lam.Prim} {args : List Arg}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {ctors : List Lam.CtorInfo}
    (h : bindStep Γ x (.prim op args) borrows uniqs ctors = .ok Γ') :
    op.isArr = false ∧ primStep Γ (lamSig op args.length) x args = .ok Γ' := by
  unfold bindStep at h
  cases hp : op.isArr
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨rfl, h⟩
  · simp [hp, throw, throwThe, MonadExceptOf.throw] at h

/-- An accepted binding binds no array primitive. -/
theorem bindStep_isArrPrim {Γ Γ' : Ctx} {x : Var} {r : Fir.Rhs} {borrows : BorrowSigs}
    {uniqs : UniqSigs} {ctors : List Lam.CtorInfo}
    (h : bindStep Γ x r borrows uniqs ctors = .ok Γ') : r.isArrPrim = false := by
  cases r <;> first | exact (bindStep_prim h).1 | rfl

/-- **The checker's binding step is `bindCtx`**, on every right-hand side but an array primitive
(which it declines). -/
theorem bindStep_eq_bindCtx (Γ : Ctx) (x : Var) (r : Fir.Rhs) (borrows : BorrowSigs)
    (uniqs : UniqSigs) (ctors : List Lam.CtorInfo) (hr : r.isArrPrim = false) :
    bindStep Γ x r borrows uniqs ctors = bindCtx Γ x r borrows uniqs ctors := by
  cases r with
  | prim op args =>
    have hp : op.isArr = false := hr
    simp only [bindStep, hp, Bool.false_eq_true, ↓reduceIte]
    exact primStep_conservative Γ op x args
  | arg a => rfl
  | ctor c args => rfl
  | call f args => rfl
  | proj y key idx => rfl

end IxCC.Own.Plain
