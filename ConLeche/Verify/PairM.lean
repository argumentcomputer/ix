module

public import ConLeche.Verify.Knot

public section

/-!
# A generic relational pair monad over the checker core

The core bodies are monad-polymorphic, so relational proofs about two
instantiations (fuel monotonicity, the cache-refinement bridge) need
not walk the bodies: instantiate them **once** at a monad of pairs
carrying the relation (`PairM`), whose `bind`/`pure`/`throw` preserve
it — the instantiated body's subtype proof *is* the per-body lemma.
The projection equations relating the pair instantiation's components
back to the plain instantiations are `rfl` up to a small tactic
cascade; the three structurally recursive list helpers get hand-rolled
commute lemmas.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A binary relation between two checker monads, closed under the
monadic operations the bodies use. -/
structure MonadRel (M₁ M₂ : Type → Type)
    [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂] where
  R : ∀ {α : Type}, M₁ α → M₂ α → Prop
  pure_rel : ∀ {α : Type} (a : α), R (pure a) (pure a)
  bind_rel : ∀ {α β : Type} {x₁ : M₁ α} {x₂ : M₂ α}
    {f₁ : α → M₁ β} {f₂ : α → M₂ β},
    R x₁ x₂ → (∀ a, R (f₁ a) (f₂ a)) → R (x₁ >>= f₁) (x₂ >>= f₂)
  throw_rel : ∀ {α : Type} (e : CheckError),
    R (throw e : M₁ α) (throw e : M₂ α)

variable {M₁ M₂ : Type → Type}
  [Monad M₁] [Monad M₂]
  [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]

/-- Pairs of computations related by `rel`. -/
@[expose] def PairM (rel : MonadRel M₁ M₂) (α : Type) : Type :=
  {pq : M₁ α × M₂ α // rel.R pq.1 pq.2}

namespace PairM

variable {rel : MonadRel M₁ M₂}

instance : Monad (PairM rel) where
  pure a := ⟨(pure a, pure a), rel.pure_rel a⟩
  bind x f :=
    ⟨(x.val.1 >>= fun a => (f a).val.1, x.val.2 >>= fun a => (f a).val.2),
      rel.bind_rel x.property (fun a => (f a).property)⟩

instance : MonadExceptOf CheckError (PairM rel) where
  throw e := ⟨(throw e, throw e), rel.throw_rel e⟩
  -- the bodies never catch; a related stub keeps the instance total
  tryCatch _ _ :=
    ⟨(throw (.internal "tryCatch unsupported"),
      throw (.internal "tryCatch unsupported")),
      rel.throw_rel _⟩

@[simp] theorem fst_bind {α β : Type} (x : PairM rel α)
    (f : α → PairM rel β) :
    (x >>= f).val.1 = x.val.1 >>= fun a => (f a).val.1 := rfl

@[simp] theorem snd_bind {α β : Type} (x : PairM rel α)
    (f : α → PairM rel β) :
    (x >>= f).val.2 = x.val.2 >>= fun a => (f a).val.2 := rfl

@[simp] theorem fst_pure {α : Type} (a : α) :
    (pure a : PairM rel α).val.1 = pure a := rfl

@[simp] theorem snd_pure {α : Type} (a : α) :
    (pure a : PairM rel α).val.2 = pure a := rfl

@[simp] theorem fst_throw {α : Type} (e : CheckError) :
    (throw e : PairM rel α).val.1 = throw e := rfl

@[simp] theorem snd_throw {α : Type} (e : CheckError) :
    (throw e : PairM rel α).val.2 = throw e := rfl

@[simp] theorem fst_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.1 = if c then x.val.1 else y.val.1 := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem snd_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.2 = if c then x.val.2 else y.val.2 := by
  by_cases hc : c <;> simp [hc]

end PairM

/-- Componentwise relatedness of two core records.  (Task #172 B4: the
io slot joins as the sixth component.) -/
@[expose] def FnsRel (rel : MonadRel M₁ M₂) (r₁ : CoreFns M₁) (r₂ : CoreFns M₂) :
    Prop :=
  (∀ d e, rel.R (r₁.whnfCore d e) (r₂.whnfCore d e)) ∧
  (∀ d e, rel.R (r₁.whnf d e) (r₂.whnf d e)) ∧
  (∀ d e, rel.R (r₁.infer d e) (r₂.infer d e)) ∧
  (∀ d a b, rel.R (r₁.defeq d a b) (r₂.defeq d a b)) ∧
  (∀ d e, rel.R (r₁.annotate d e) (r₂.annotate d e)) ∧
  (∀ d e, rel.R (r₁.inferIO d e) (r₂.inferIO d e))

/-- Relatedness transports along the io-grade view: the view only
permutes fields. -/
theorem FnsRel.ioView {rel : MonadRel M₁ M₂} {r₁ : CoreFns M₁}
    {r₂ : CoreFns M₂} (h : FnsRel rel r₁ r₂) :
    FnsRel rel r₁.ioView r₂.ioView :=
  ⟨h.1, h.2.1, h.2.2.2.2.2, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The paired record. -/
def pairFns {rel : MonadRel M₁ M₂} (r₁ : CoreFns M₁) (r₂ : CoreFns M₂)
    (h : FnsRel rel r₁ r₂) : CoreFns (PairM rel) where
  whnfCore d e := ⟨(r₁.whnfCore d e, r₂.whnfCore d e), h.1 d e⟩
  whnf d e := ⟨(r₁.whnf d e, r₂.whnf d e), h.2.1 d e⟩
  infer d e := ⟨(r₁.infer d e, r₂.infer d e), h.2.2.1 d e⟩
  defeq d a b := ⟨(r₁.defeq d a b, r₂.defeq d a b), h.2.2.2.1 d a b⟩
  annotate d e := ⟨(r₁.annotate d e, r₂.annotate d e), h.2.2.2.2.1 d e⟩
  inferIO d e := ⟨(r₁.inferIO d e, r₂.inferIO d e), h.2.2.2.2.2 d e⟩

section Commute

variable {rel : MonadRel M₁ M₂} {r₁ : CoreFns M₁} {r₂ : CoreFns M₂}
  {h : FnsRel rel r₁ r₂} {env : Env}

theorem iotaCerts_fst (d : Nat) (lic : Bool) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (pairFns r₁ r₂ h) env d lic ty args).val.1 =
        iotaCerts r₁ env d lic ty args
  | _, [] => rfl
  | .forallE ty body mb, arg :: rest => by
    show (if lic && mb.pw.isNever then
        iotaCerts (pairFns r₁ r₂ h) env d lic (body.instantiate1 arg) rest
      else (do
        let ta ← (pairFns r₁ r₂ h).inferIO d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCerts (pairFns r₁ r₂ h) env d lic (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.1 = (if lic && mb.pw.isNever then
        iotaCerts r₁ env d lic (body.instantiate1 arg) rest
      else do
        let ta ← r₁.inferIO d arg
        if ← r₁.defeq d ta ty then
          iotaCerts r₁ env d lic (body.instantiate1 arg) rest
        else pure false)
    by_cases hg : (lic && mb.pw.isNever) = true
    · rw [if_pos hg, if_pos hg]
      exact iotaCerts_fst d lic (body.instantiate1 arg) rest
    · rw [if_neg hg, if_neg hg]
      rw [PairM.fst_bind]
      congr 1
      funext ta
      rw [PairM.fst_bind]
      congr 1
      funext b
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact iotaCerts_fst d lic (body.instantiate1 arg) rest
      | false => rfl
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem iotaCerts_snd (d : Nat) (lic : Bool) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (pairFns r₁ r₂ h) env d lic ty args).val.2 =
        iotaCerts r₂ env d lic ty args
  | _, [] => rfl
  | .forallE ty body mb, arg :: rest => by
    show (if lic && mb.pw.isNever then
        iotaCerts (pairFns r₁ r₂ h) env d lic (body.instantiate1 arg) rest
      else (do
        let ta ← (pairFns r₁ r₂ h).inferIO d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCerts (pairFns r₁ r₂ h) env d lic (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.2 = (if lic && mb.pw.isNever then
        iotaCerts r₂ env d lic (body.instantiate1 arg) rest
      else do
        let ta ← r₂.inferIO d arg
        if ← r₂.defeq d ta ty then
          iotaCerts r₂ env d lic (body.instantiate1 arg) rest
        else pure false)
    by_cases hg : (lic && mb.pw.isNever) = true
    · rw [if_pos hg, if_pos hg]
      exact iotaCerts_snd d lic (body.instantiate1 arg) rest
    · rw [if_neg hg, if_neg hg]
      rw [PairM.snd_bind]
      congr 1
      funext ta
      rw [PairM.snd_bind]
      congr 1
      funext b
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact iotaCerts_snd d lic (body.instantiate1 arg) rest
      | false => rfl
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem defEqList_fst (d : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (pairFns r₁ r₂ h) env d as bs).val.1 =
        defEqList r₁ env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (pairFns r₁ r₂ h).defeq d a b then
          defEqList (pairFns r₁ r₂ h) env d as bs
        else pure false : PairM rel Bool)).val.1 = (do
        if ← r₁.defeq d a b then
          defEqList r₁ env d as bs
        else pure false)
    rw [PairM.fst_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_fst d as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem defEqList_snd (d : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (pairFns r₁ r₂ h) env d as bs).val.2 =
        defEqList r₂ env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (pairFns r₁ r₂ h).defeq d a b then
          defEqList (pairFns r₁ r₂ h) env d as bs
        else pure false : PairM rel Bool)).val.2 = (do
        if ← r₂.defeq d a b then
          defEqList r₂ env d as bs
        else pure false)
    rw [PairM.snd_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_snd d as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem iotaIndexOk_fst (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : List Expr) :
    (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs idx).val.1 =
      iotaIndexOk r₁ env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, if_pos hmr]; rfl
  · simp only [iotaIndexOk, if_neg hmr]
    cases piResidual tyCtor margs with
    | none => rfl
    | some residual => exact defEqList_fst d _ _

theorem iotaIndexOk_snd (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : List Expr) :
    (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs idx).val.2 =
      iotaIndexOk r₂ env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, if_pos hmr]; rfl
  · simp only [iotaIndexOk, if_neg hmr]
    cases piResidual tyCtor margs with
    | none => rfl
    | some residual => exact defEqList_snd d _ _

theorem defeqSpine_fst (d : Nat) (a b : Expr) :
    (defeqSpine (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqSpine r₁ env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_fst])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem defeqSpine_snd (d : Nat) (a b : Expr) :
    (defeqSpine (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqSpine r₂ env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_snd])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem structEtaProjCerts_fst (d : Nat) (T : Name) (us' : List Level)
    (targs : List Expr) (b : Expr) (lpsT : List Name) :
    ∀ (idxs : List Nat),
      (structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b lpsT
        idxs).val.1 =
      structEtaProjCerts r₁ env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pairFns r₁ r₂ h) env d false
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : PairM rel Bool)).val.1 = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts r₁ env d false
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts r₁ env d T us' targs b lpsT rest
            else pure false
          else pure false
        | _ => pure false)
    cases hf : env.find? (projFnName T i) with
    | none => rfl
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · rw [PairM.fst_bind, iotaCerts_fst]
          congr 1
          funext r
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCerts_fst d T us' targs b lpsT rest
          | false => rfl
        · rfl
      | axiomInfo cv => rfl
      | projInfo entry => rfl
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

theorem structEtaProjCerts_snd (d : Nat) (T : Name) (us' : List Level)
    (targs : List Expr) (b : Expr) (lpsT : List Name) :
    ∀ (idxs : List Nat),
      (structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b lpsT
        idxs).val.2 =
      structEtaProjCerts r₂ env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pairFns r₁ r₂ h) env d false
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : PairM rel Bool)).val.2 = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts r₂ env d false
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts r₂ env d T us' targs b lpsT rest
            else pure false
          else pure false
        | _ => pure false)
    cases hf : env.find? (projFnName T i) with
    | none => rfl
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · rw [PairM.snd_bind, iotaCerts_snd]
          congr 1
          funext r
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCerts_snd d T us' targs b lpsT rest
          | false => rfl
        · rfl
      | axiomInfo cv => rfl
      | projInfo entry => rfl
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

theorem liftFueled_fst_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.1 = liftFueled what o := by
  cases o <;> rfl

theorem liftFueled_snd_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.2 = liftFueled what o := by
  cases o <;> rfl

macro "fst_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac" : tactic =>
  `(tactic| fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step)

macro "snd_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac" : tactic =>
  `(tactic| snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step)

theorem reduceNat_fst_proj (d : Nat) (e : Expr) :
    (reduceNat (pairFns r₁ r₂ h) env d e).val.1 =
      reduceNat r₁ env d e := by
  unfold reduceNat
  fst_tac

theorem reduceNat_snd_proj (d : Nat) (e : Expr) :
    (reduceNat (pairFns r₁ r₂ h) env d e).val.2 =
      reduceNat r₂ env d e := by
  unfold reduceNat
  snd_tac

theorem boolTrueShortcut_fst_proj (d : Nat) (e : Expr) :
    (boolTrueShortcut (pairFns r₁ r₂ h) d e).val.1 =
      boolTrueShortcut r₁ d e := by
  unfold boolTrueShortcut
  fst_tac

theorem boolTrueShortcut_snd_proj (d : Nat) (e : Expr) :
    (boolTrueShortcut (pairFns r₁ r₂ h) d e).val.2 =
      boolTrueShortcut r₂ d e := by
  unfold boolTrueShortcut
  snd_tac

theorem ensureSort_fst_proj (d : Nat) (e : Expr) :
    (ensureSort (pairFns r₁ r₂ h) env d e).val.1 =
      ensureSort r₁ env d e := by
  unfold ensureSort
  fst_tac

theorem ensureSort_snd_proj (d : Nat) (e : Expr) :
    (ensureSort (pairFns r₁ r₂ h) env d e).val.2 =
      ensureSort r₂ env d e := by
  unfold ensureSort
  snd_tac

theorem proofIrrel_fst_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) env d a b).val.1 =
      proofIrrel r₁ env d a b := by
  unfold proofIrrel
  fst_tac

theorem proofIrrel_snd_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) env d a b).val.2 =
      proofIrrel r₂ env d a b := by
  unfold proofIrrel
  snd_tac

theorem propIrrel_fst_proj (d : Nat) (a b : Expr) :
    (propIrrel (pairFns r₁ r₂ h) env d a b).val.1 =
      propIrrel r₁ env d a b := by
  unfold propIrrel
  fst_tac

theorem propIrrel_snd_proj (d : Nat) (a b : Expr) :
    (propIrrel (pairFns r₁ r₂ h) env d a b).val.2 =
      propIrrel r₂ env d a b := by
  unfold propIrrel
  snd_tac

theorem structEtaCertWith_fst_proj (d : Nat) (a b wtb : Expr) :
    (structEtaCertWith mode (pairFns r₁ r₂ h) env d a b wtb).val.1 =
      structEtaCertWith mode r₁ env d a b wtb := by
  unfold structEtaCertWith
  fst_tac

theorem structEtaCertWith_snd_proj (d : Nat) (a b wtb : Expr) :
    (structEtaCertWith mode (pairFns r₁ r₂ h) env d a b wtb).val.2 =
      structEtaCertWith mode r₂ env d a b wtb := by
  unfold structEtaCertWith
  snd_tac

theorem structUnitCert_fst_proj (d : Nat) (a b : Expr) :
    (structUnitCert (pairFns r₁ r₂ h) env d a b).val.1 =
      structUnitCert r₁ env d a b := by
  unfold structUnitCert
  fst_tac

theorem structUnitCert_snd_proj (d : Nat) (a b : Expr) :
    (structUnitCert (pairFns r₁ r₂ h) env d a b).val.2 =
      structUnitCert r₂ env d a b := by
  unfold structUnitCert
  snd_tac

theorem etaCert_fst_proj (d : Nat) (ty body : Expr) (mb : BinderMeta) (b : Expr) :
    (etaCert mode (pairFns r₁ r₂ h) env d ty body mb b).val.1 =
      etaCert mode r₁ env d ty body mb b := by
  unfold etaCert
  fst_tac

theorem etaCert_snd_proj (d : Nat) (ty body : Expr) (mb : BinderMeta) (b : Expr) :
    (etaCert mode (pairFns r₁ r₂ h) env d ty body mb b).val.2 =
      etaCert mode r₂ env d ty body mb b := by
  unfold etaCert
  snd_tac

theorem projCert_fst_proj (d : Nat) (lic : Bool) (c : Name) (us : List Level)
    (args : List Expr) :
    (projCert (pairFns r₁ r₂ h) env d lic c us args).val.1 =
      projCert r₁ env d lic c us args := by
  unfold projCert
  split
  · exact iotaCerts_fst d lic _ _
  · rfl

theorem projCert_snd_proj (d : Nat) (lic : Bool) (c : Name) (us : List Level)
    (args : List Expr) :
    (projCert (pairFns r₁ r₂ h) env d lic c us args).val.2 =
      projCert r₂ env d lic c us args := by
  unfold projCert
  split
  · exact iotaCerts_snd d lic _ _
  · rfl

theorem projCertAt_fst_proj (d : Nat) (v lic : Bool) (c : Name) (us : List Level)
    (args : List Expr) :
    (projCertAt (pairFns r₁ r₂ h) env d v lic c us args).val.1 =
      projCertAt r₁ env d v lic c us args := by
  unfold projCertAt
  split
  · exact projCert_fst_proj d lic c us args
  · rfl

theorem projCertAt_snd_proj (d : Nat) (v lic : Bool) (c : Name) (us : List Level)
    (args : List Expr) :
    (projCertAt (pairFns r₁ r₂ h) env d v lic c us args).val.2 =
      projCertAt r₂ env d v lic c us args := by
  unfold projCertAt
  split
  · exact projCert_snd_proj d lic c us args
  · rfl

macro "fst_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [boolTrueShortcut_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [propIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCertAt_fst_proj])
    | (rw [projCert_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac2" : tactic =>
  `(tactic| fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2)

macro "snd_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [boolTrueShortcut_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [propIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCertAt_snd_proj])
    | (rw [projCert_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac2" : tactic =>
  `(tactic| snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2)

theorem structEtaCert_fst_proj (d : Nat) (a b : Expr) :
    (structEtaCert mode (pairFns r₁ r₂ h) env d a b).val.1 =
      structEtaCert mode r₁ env d a b := by
  unfold structEtaCert
  fst_tac2

theorem structEtaCert_snd_proj (d : Nat) (a b : Expr) :
    (structEtaCert mode (pairFns r₁ r₂ h) env d a b).val.2 =
      structEtaCert mode r₂ env d a b := by
  unfold structEtaCert
  snd_tac2

-- The `majorToCtor` body outgrew the split-driven macros (the
-- splitter's internal simp hits its step ceiling on the full match
-- tower), so the outer casing is peeled by hand and the macro closes
-- each rescue branch separately.
set_option maxHeartbeats 800000 in
theorem majorToCtor_fst_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (majorToCtor mode (pairFns r₁ r₂ h) env d c rules e).val.1 =
      majorToCtor mode r₁ env d c rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [if_pos hca, if_pos hca]; rfl
  rw [if_neg hca, if_neg hca]
  match rules with
  | [] => rfl
  | _ :: _ :: _ => rfl
  | [rl] =>
    dsimp only
    cases hfr : env.find? rl.ctor <;> try rfl
    case some ci =>
    cases ci <;> try rfl
    case ctorInfo cvj cnP cnF =>
    dsimp only
    cases (cvj.type.piResult).getAppFn <;> try rfl
    case const T us₀ =>
    dsimp only
    cases env.find? T <;> try rfl
    case some ciT =>
    cases ciT <;> try rfl
    case indInfo cvT caps =>
    dsimp only
    by_cases hK : rl.k = true
    · rw [if_pos hK, if_pos hK]
      fst_tac2
    rw [if_neg hK, if_neg hK]
    by_cases hE : rl.eta = true
    · rw [if_pos hE, if_pos hE]
      fst_tac2
    rw [if_neg hE, if_neg hE]
    by_cases hA : T = andName
    · rw [if_pos hA, if_pos hA]
      fst_tac2
    rw [if_neg hA, if_neg hA]
    rfl

set_option maxHeartbeats 800000 in
theorem majorToCtor_snd_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (majorToCtor mode (pairFns r₁ r₂ h) env d c rules e).val.2 =
      majorToCtor mode r₂ env d c rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [if_pos hca, if_pos hca]; rfl
  rw [if_neg hca, if_neg hca]
  match rules with
  | [] => rfl
  | _ :: _ :: _ => rfl
  | [rl] =>
    dsimp only
    cases hfr : env.find? rl.ctor <;> try rfl
    case some ci =>
    cases ci <;> try rfl
    case ctorInfo cvj cnP cnF =>
    dsimp only
    cases (cvj.type.piResult).getAppFn <;> try rfl
    case const T us₀ =>
    dsimp only
    cases env.find? T <;> try rfl
    case some ciT =>
    cases ciT <;> try rfl
    case indInfo cvT caps =>
    dsimp only
    by_cases hK : rl.k = true
    · rw [if_pos hK, if_pos hK]
      snd_tac2
    rw [if_neg hK, if_neg hK]
    by_cases hE : rl.eta = true
    · rw [if_pos hE, if_pos hE]
      snd_tac2
    rw [if_neg hE, if_neg hE]
    by_cases hA : T = andName
    · rw [if_pos hA, if_pos hA]
      snd_tac2
    rw [if_neg hA, if_neg hA]
    rfl

theorem litMajorToCtor_fst_proj (d : Nat) (e : Expr) :
    (litMajorToCtor (pairFns r₁ r₂ h) env d e).val.1 =
      litMajorToCtor r₁ env d e := by
  unfold litMajorToCtor
  fst_tac2

theorem litMajorToCtor_snd_proj (d : Nat) (e : Expr) :
    (litMajorToCtor (pairFns r₁ r₂ h) env d e).val.2 =
      litMajorToCtor r₂ env d e := by
  unfold litMajorToCtor
  snd_tac2

theorem prepareMajor_fst_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (prepareMajor mode (pairFns r₁ r₂ h) env d c rules e).val.1 =
      prepareMajor mode r₁ env d c rules e := by
  unfold prepareMajor
  split <;> (repeat (first
    | rfl
    | (rw [majorToCtor_fst_proj])
    | (rw [litMajorToCtor_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])))

theorem prepareMajor_snd_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (prepareMajor mode (pairFns r₁ r₂ h) env d c rules e).val.2 =
      prepareMajor mode r₂ env d c rules e := by
  unfold prepareMajor
  split <;> (repeat (first
    | rfl
    | (rw [majorToCtor_snd_proj])
    | (rw [litMajorToCtor_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])))

theorem projLitToCtor_fst_proj (d : Nat) (e : Expr) :
    (projLitToCtor (pairFns r₁ r₂ h) env d e).val.1 =
      projLitToCtor r₁ env d e := by
  unfold projLitToCtor
  fst_tac2

theorem projLitToCtor_snd_proj (d : Nat) (e : Expr) :
    (projLitToCtor (pairFns r₁ r₂ h) env d e).val.2 =
      projLitToCtor r₂ env d e := by
  unfold projLitToCtor
  snd_tac2

macro "fst_step3" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [boolTrueShortcut_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCertAt_fst_proj])
    | (rw [projCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [litMajorToCtor_fst_proj])
    | (rw [prepareMajor_fst_proj])
    | (rw [projLitToCtor_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac3" : tactic =>
  `(tactic| fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3)

macro "snd_step3" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [boolTrueShortcut_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCertAt_snd_proj])
    | (rw [projCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [litMajorToCtor_snd_proj])
    | (rw [prepareMajor_snd_proj])
    | (rw [projLitToCtor_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac3" : tactic =>
  `(tactic| snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3)

theorem stuckIrrel_fst_proj (d : Nat) (a b : Expr) :
    (stuckIrrel mode (pairFns r₁ r₂ h) env d a b).val.1 =
      stuckIrrel mode r₁ env d a b := by
  unfold stuckIrrel
  fst_tac3

theorem stuckIrrel_snd_proj (d : Nat) (a b : Expr) :
    (stuckIrrel mode (pairFns r₁ r₂ h) env d a b).val.2 =
      stuckIrrel mode r₂ env d a b := by
  unfold stuckIrrel
  snd_tac3

theorem iotaRec_fst_proj (d : Nat) (e : Expr) :
    (iotaRec mode (pairFns r₁ r₂ h) env d e).val.1 =
      iotaRec mode r₁ env d e := by
  unfold iotaRec
  fst_tac3

theorem iotaRec_snd_proj (d : Nat) (e : Expr) :
    (iotaRec mode (pairFns r₁ r₂ h) env d e).val.2 =
      iotaRec mode r₂ env d e := by
  unfold iotaRec
  snd_tac3

/-- The level-4 cascade, parameterized over one extra alternative so
that loop-body lemmas can feed in their continuation hypothesis
(`fst_step4k`) without duplicating the rewrite list. -/
macro "fst_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [boolTrueShortcut_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [propIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCertAt_fst_proj])
    | (rw [projCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [stuckIrrel_fst_proj])
    | (rw [iotaRec_fst_proj])
    | (rw [projLitToCtor_fst_proj])
    | (rw [defeqSpine_fst])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- task #161: the β gate's dead branch — unfolding the *one* gate
    -- primitive hands both arms back to the cascade's own `split`
    | ((rw [PairM.fst_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "fst_step4" : tactic => `(tactic| fst_core4 (fail))

macro "fst_step4k" hk:ident : tactic =>
  `(tactic| fst_core4 (rw [$hk:ident]))

macro "fst_tac4k" hk:ident : tactic =>
  `(tactic| fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk)

macro "fst_tac4" : tactic =>
  `(tactic| fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4)

/-- The level-4 cascade, parameterized over one extra alternative so
that loop-body lemmas can feed in their continuation hypothesis
(`snd_step4k`) without duplicating the rewrite list. -/
macro "snd_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [boolTrueShortcut_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [propIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCertAt_snd_proj])
    | (rw [projCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [stuckIrrel_snd_proj])
    | (rw [iotaRec_snd_proj])
    | (rw [projLitToCtor_snd_proj])
    | (rw [defeqSpine_snd])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- task #161: the β gate's dead branch — unfolding the *one* gate
    -- primitive hands both arms back to the cascade's own `split`
    | ((rw [PairM.snd_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "snd_step4" : tactic => `(tactic| snd_core4 (fail))

macro "snd_step4k" hk:ident : tactic =>
  `(tactic| snd_core4 (rw [$hk:ident]))

macro "snd_tac4k" hk:ident : tactic =>
  `(tactic| snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk)

macro "snd_tac4" : tactic =>
  `(tactic| snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4)

theorem whnfCoreBody_fst_proj (d : Nat) (e : Expr) :
    (whnfCoreBody mode (pairFns r₁ r₂ h) env d e).val.1 =
      whnfCoreBody mode r₁ env d e := by
  unfold whnfCoreBody
  fst_tac4

theorem whnfCoreBody_snd_proj (d : Nat) (e : Expr) :
    (whnfCoreBody mode (pairFns r₁ r₂ h) env d e).val.2 =
      whnfCoreBody mode r₂ env d e := by
  unfold whnfCoreBody
  snd_tac4

/-! The reduction-loop and lazy-delta-loop bodies (task #106) are
parameterized over their continuation exactly as over the record, so
each gets one projection lemma with a continuation hypothesis and the
loop lemma is a plain induction on the step budget. -/

theorem whnfStep_fst_proj (d : Nat) (k : Expr → PairM rel Expr)
    (k₁ : Expr → M₁ Expr) (hk : ∀ e, (k e).val.1 = k₁ e) (e : Expr) :
    (whnfStep (pairFns r₁ r₂ h) env d k e).val.1 =
      whnfStep r₁ env d k₁ e := by
  unfold whnfStep
  fst_tac4k hk

theorem whnfStep_snd_proj (d : Nat) (k : Expr → PairM rel Expr)
    (k₂ : Expr → M₂ Expr) (hk : ∀ e, (k e).val.2 = k₂ e) (e : Expr) :
    (whnfStep (pairFns r₁ r₂ h) env d k e).val.2 =
      whnfStep r₂ env d k₂ e := by
  unfold whnfStep
  snd_tac4k hk

theorem whnfLoop_fst_proj (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (pairFns r₁ r₂ h) env d n e).val.1 = whnfLoop r₁ env d n e
  | 0, _ => rfl
  | n + 1, e =>
    whnfStep_fst_proj d _ _ (fun e' => whnfLoop_fst_proj d n e') e

theorem whnfLoop_snd_proj (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (pairFns r₁ r₂ h) env d n e).val.2 = whnfLoop r₂ env d n e
  | 0, _ => rfl
  | n + 1, e =>
    whnfStep_snd_proj d _ _ (fun e' => whnfLoop_snd_proj d n e') e

theorem whnfBody_fst_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.1 =
      whnfBody r₁ env d e :=
  whnfLoop_fst_proj d whnfLoopFuel e

theorem whnfBody_snd_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.2 =
      whnfBody r₂ env d e :=
  whnfLoop_snd_proj d whnfLoopFuel e

theorem inferBody_fst_proj (d : Nat) (e : Expr) :
    (inferBody mode (pairFns r₁ r₂ h) env d e).val.1 =
      inferBody mode r₁ env d e := by
  unfold inferBody
  fst_tac4

theorem inferBody_snd_proj (d : Nat) (e : Expr) :
    (inferBody mode (pairFns r₁ r₂ h) env d e).val.2 =
      inferBody mode r₂ env d e := by
  unfold inferBody
  snd_tac4

/-! The io inference body (task #172 B4): same walk, one clause's gate
more.  The pairing of the io-grade views is definitionally the io-grade
view of the pairing on the fields the body reads, so the walks go
through the plain `pairFns` of the viewed records. -/

theorem inferBodyIO_fst_proj (d : Nat) (e : Expr) :
    (inferBodyIO mode (pairFns r₁ r₂ h) env d e).val.1 =
      inferBodyIO mode r₁ env d e := by
  unfold inferBodyIO
  fst_tac4

theorem inferBodyIO_snd_proj (d : Nat) (e : Expr) :
    (inferBodyIO mode (pairFns r₁ r₂ h) env d e).val.2 =
      inferBodyIO mode r₂ env d e := by
  unfold inferBodyIO
  snd_tac4

theorem defeqStep_fst_proj (d : Nat) (k : Bool → Expr → Expr → PairM rel Bool)
    (k₁ : Bool → Expr → Expr → M₁ Bool)
    (hk : ∀ pi a b, (k pi a b).val.1 = k₁ pi a b) (pi : Bool) (a b : Expr) :
    (defeqStep mode (pairFns r₁ r₂ h) env d k pi a b).val.1 =
      defeqStep mode r₁ env d k₁ pi a b := by
  unfold defeqStep
  fst_tac4k hk

theorem defeqStep_snd_proj (d : Nat) (k : Bool → Expr → Expr → PairM rel Bool)
    (k₂ : Bool → Expr → Expr → M₂ Bool)
    (hk : ∀ pi a b, (k pi a b).val.2 = k₂ pi a b) (pi : Bool) (a b : Expr) :
    (defeqStep mode (pairFns r₁ r₂ h) env d k pi a b).val.2 =
      defeqStep mode r₂ env d k₂ pi a b := by
  unfold defeqStep
  snd_tac4k hk

theorem defeqLoop_fst_proj (d : Nat) :
    ∀ (n : Nat) (pi : Bool) (a b : Expr),
      (defeqLoop mode (pairFns r₁ r₂ h) env d n pi a b).val.1 =
        defeqLoop mode r₁ env d n pi a b
  | 0, _, _, _ => rfl
  | n + 1, pi, a, b =>
    defeqStep_fst_proj d _ _ (fun pi' x y => defeqLoop_fst_proj d n pi' x y)
      pi a b

theorem defeqLoop_snd_proj (d : Nat) :
    ∀ (n : Nat) (pi : Bool) (a b : Expr),
      (defeqLoop mode (pairFns r₁ r₂ h) env d n pi a b).val.2 =
        defeqLoop mode r₂ env d n pi a b
  | 0, _, _, _ => rfl
  | n + 1, pi, a, b =>
    defeqStep_snd_proj d _ _ (fun pi' x y => defeqLoop_snd_proj d n pi' x y)
      pi a b

theorem defeqBody_fst_proj (d : Nat) (a b : Expr) :
    (defeqBody mode (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqBody mode r₁ env d a b :=
  defeqLoop_fst_proj d defeqLoopFuel true a b

theorem defeqBody_snd_proj (d : Nat) (a b : Expr) :
    (defeqBody mode (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqBody mode r₂ env d a b :=
  defeqLoop_snd_proj d defeqLoopFuel true a b

-- Task #161 P5: the ∀/λ clauses' untrusted `pw` write is one more
-- inference call under the same cascade (`annotPwPi` = infer +
-- `ensureSort`; `annotPwLam` = the chain read, else infer + infer +
-- `ensureSort`).  Unfolding them alongside `annotateBody` puts their
-- binds in front of the level-4 rewrites — no new lemma is needed, the
-- calls are exactly the kind the `letE`/`proj` clauses already make.
theorem annotateBody_fst_proj (d : Nat) (e : Expr) :
    (annotateBody (pairFns r₁ r₂ h) env d e).val.1 =
      annotateBody r₁ env d e := by
  unfold annotateBody annotPwPi annotPwLam
  fst_tac4

theorem annotateBody_snd_proj (d : Nat) (e : Expr) :
    (annotateBody (pairFns r₁ r₂ h) env d e).val.2 =
      annotateBody r₂ env d e := by
  unfold annotateBody annotPwPi annotPwLam
  snd_tac4

end Commute

end ConLeche
