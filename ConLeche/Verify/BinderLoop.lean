module

public import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Abstract
import ConLeche.Verify.AbstractRange
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Leaves

public section

/-!
# Binder-telescope loops and their identification with the chained
bodies (task #72; task #100 stage 6 shapes)

The interned twins' binder cases (`annotatePisI`/`annotateLamsI`/
`inferLamsI`/`inferPisI`, `ConLeche/Kernel/CoreI.lean`) peel a whole
binder telescope in one loop — bulk-opening with an fvar accumulator,
substituting only each binder's domain on the way in, and rebuilding
with one `abstractRange` per domain and one over the leaf.  This file
provides the pure mirrors (generic over the core record, like
`BetaSpine`'s) and proves the **soundness of each loop against the
chained spec**: a successful mirror run at the pure fueled knot is
reproduced by the original one-binder-at-a-time body at some fuel
(`inferLams_sound`, `inferPis_sound`, `annotatePis_sound`,
`annotateLams_sound`).  The interned walks
(`ConLeche/Verify/BinderLoopI.lean`) compose their simulation against
the mirrors with these theorems, so the `Expr`-level specification —
and everything above it — is unchanged.

Post-erasure (task #100 stage 6) the loops are far simpler than their
task-#72 ancestors: the annotation pass computes nothing at binders,
the λ-rule has no body-type re-check, and the ∀-rule infers its
codomain sort — so every *rebuild* phase is a pure fold (no knot
calls), and the only reproduction obligations are the peel phase's
domain checks, the leaf runs, and — for the ∀-loop — the chained
rule's per-level `ensureSort` on an already-built sort (`whnf_sort`).
The rebuild/chain identification is the pure `abstractRange`/
`abstract1` algebra (`abstractRange_succ`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace ConLeche

variable {mode : CheckMode}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The pure mirrors -/

/-- Mirror stack entry of `inferLamsI`: opened domain, binder meta. -/
abbrev InferLamEntryX := Expr × BinderMeta

/-- Mirror stack entry of the annotation loops: annotated opened
domain, binder meta. -/
abbrev AnnotBinderEntryX := Expr × BinderMeta

/-- Pure mirror of `inferLamsOutI` (a pure rebuild fold). -/
@[expose] def inferLamsOut (mode : CheckMode) (d : Nat) :
    List InferLamEntryX → Nat → Expr → PropWhen → m Expr
  | [], _j, cur, _prevPw => pure cur
  | (tyo, mb) :: rest, j, cur, prevPw => do
    if mode.verifiedChecks && !(mb.pw == prevPw) then
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    inferLamsOut mode d rest (j - 1)
      (Expr.forallE (tyo.abstractRange d j) cur mb) mb.pw

/-- Instantiating with free variables does not change a term's head
shape — the λ-chain guard (task #152) reads the same on the peel's
residual and on its bulk-opened form. -/
theorem isLam_instantiateList_fvars {vs : List Expr}
    (hv : ∀ x ∈ vs, ∃ i ty, x = Expr.fvar i ty) :
    ∀ (e : Expr) (dd : Nat), (e.instantiateList vs dd).isLam = e.isLam := by
  intro e dd
  cases e
  case bvar j =>
    rw [Expr.instantiateList]
    split
    · simp only [Expr.isLam]
    · split
      · obtain ⟨i, ty', hx⟩ := hv vs[j - dd] (List.getElem_mem _)
        rw [hx, Expr.instantiateList]
        simp only [Expr.isLam]
      · simp only [Expr.isLam]
  all_goals (rw [Expr.instantiateList]; try simp only [Expr.isLam])

/-- Instantiating with free variables does not change the λ-meta head
reading (task #161's chain rule): the substituted values are `fvar`s,
never λs. -/
theorem lamPw_instantiateList_fvars {vs : List Expr}
    (hv : ∀ x ∈ vs, ∃ i ty, x = Expr.fvar i ty) :
    ∀ (e : Expr) (dd : Nat),
      (e.instantiateList vs dd).lamPw = e.lamPw := by
  intro e dd
  cases e
  case bvar j =>
    rw [Expr.instantiateList]
    split
    · simp only [Expr.lamPw]
    · split
      · obtain ⟨i, ty', hx⟩ := hv vs[j - dd] (List.getElem_mem _)
        rw [hx, Expr.instantiateList]
        simp only [Expr.lamPw]
      · simp only [Expr.lamPw]
  all_goals (rw [Expr.instantiateList]; try simp only [Expr.lamPw])

/-- Pure mirror of `inferLamsLeafI` (task #152: the chain's body-type
sort check, at the verified modes, on a non-λ residual). -/
@[expose] def inferLamsLeaf (mode : CheckMode) (r : CoreFns m) (d : Nat)
    (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  match t with
  | .lam .. => pure ()
  | _ =>
    if mode.verifiedChecks then
      -- task #172 B4: the type-of-a-type leaf at the io grade
      let btt ← r.inferIO (d + k) bt
      match ← r.whnf (d + k) btt with
      | .sort vb =>
        match stk with
        | (_, mb₀) :: _ =>
          unless Level.zeronessOf vb == mb₀.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
        | [] => pure ()
      | _ => throw (.invalid "expected a sort")
  inferLamsOut mode d stk (k - 1) (bt.abstractRange d k)
    (match t.lamPw with
     | some pwT => pwT
     | none =>
       match stk with
       | (_, mb₀) :: _ => mb₀.pw
       | [] => .never)

/-- Pure mirror of `inferLamsI`. -/
@[expose] def inferLams (mode : CheckMode) (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List InferLamEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam ty body mb => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort _ =>
        inferLams mode r d fuel body (k + 1)
          (Expr.fvar (d + k) tyo :: fvs) ((tyo, mb) :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferLamsLeaf mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeaf mode r d t k fvs stk

/-- Pure mirror of `inferPisOutI` (the `imax` fold, pure). -/
@[expose] def inferPisOut (mode : CheckMode) :
    List (Level × PropWhen) → Level → m Level
  | [], v => pure v
  | (u, pw) :: rest, v => do
    if mode.verifiedChecks && !(Level.zeronessOf v == pw) then
      throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    inferPisOut mode rest (.imax u v)

/-- Pure mirror of `inferPisLeafI` (task #161: the fold validates each
node's prop-ness annotation against its codomain sort). -/
@[expose] def inferPisLeaf (mode : CheckMode) (r : CoreFns m) (d : Nat)
    (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List (Level × PropWhen)) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  match ← r.whnf (d + k) bt with
  | .sort v => do
    let iv ← inferPisOut mode stk v
    pure (Expr.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `inferPisI`. -/
@[expose] def inferPis (mode : CheckMode) (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List (Level × PropWhen) → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE ty body mb => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort u =>
        inferPis mode r d fuel body (k + 1)
          (Expr.fvar (d + k) tyo :: fvs) ((u, mb.pw) :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferPisLeaf mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeaf mode r d t k fvs stk

/-- The datum invariant the rebuild fold carries: the threaded datum is
exactly what the chained tail's write returns on the node built so far.
Since 2026-09-06 the write is UNGATED (both modes annotate), so the
`none` alternative — "no datum" — is unreachable and the invariant says
so.  Written as a `def` by pattern match so that consumers never face a
dependent `match` motive. -/
def AnnotPwOk (x : CheckM PropWhen) : Option PropWhen → Prop
  | some pw => x = .ok pw
  | none => False

/-- Pure mirror of `annotateBindersOutI` (a pure rebuild fold, generic
in the rebuilt binder kind).  Task #161 P5: `pw?` is the datum written
just below — each node takes it unless it carries a real input
annotation, and passes on whatever it ended up with (the chain rule
`annotPwPi`/`annotPwLam` read on the spec side).  `none` = no write. -/

@[expose] def annotateBindersOut (mk : Expr → Expr → BinderMeta → Expr)
    (d : Nat) (pw? : Option PropWhen) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, cur => pure cur
  | (ty', mb) :: rest, j, cur =>
    annotateBindersOut mk d (pw?.map fun _ => (annotBinderMeta pw? mb).pw)
      rest (j - 1)
      (mk (ty'.abstractRange d j) cur (annotBinderMeta pw? mb))

/-- Pure mirror of `annotatePisLeafI` (task #161 P5: the telescope's
datum, computed once here — the leaf's own if the residual annotates to
a ∀, else the leaf codomain sort's zero-ness). -/
@[expose] def annotatePisPw (r : CoreFns m) (env : Env) (d k : Nat)
    (leaf' : Expr) : m (Option PropWhen) := do
  let p ← annotPwPi r env (d + k) leaf'
  pure (some p)

/-- Pure mirror of `annotatePisLeafI`'s rebuild. -/
@[expose] def annotatePisLeaf (r : CoreFns m) (env : Env)
    (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  let pw? ← annotatePisPw r env d k leaf'
  annotateBindersOut (fun ty b mb => .forallE ty b mb) d pw?
    stk (k - 1) (leaf'.abstractRange d k)

/-- Pure mirror of `annotatePisI`. -/
@[expose] def annotatePis (r : CoreFns m) (env : Env) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotatePis r env d fuel body (k + 1)
        (Expr.fvar (d + k) ty' :: fvs) ((ty', mb) :: stk)
    | t => annotatePisLeaf r env d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeaf r env d t k fvs stk

/-- Pure mirror of `annotateLamsLeafI` (the λ twin: the chain's datum
is the innermost λ's own, else the sort of the body's type). -/
@[expose] def annotateLamsPw (r : CoreFns m) (env : Env) (d k : Nat)
    (leaf' : Expr) : m (Option PropWhen) := do
  let p ← annotPwLam r env (d + k) leaf'
  pure (some p)

/-- Pure mirror of `annotateLamsLeafI`'s rebuild. -/
@[expose] def annotateLamsLeaf (r : CoreFns m) (env : Env)
    (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  let pw? ← annotateLamsPw r env d k leaf'
  annotateBindersOut (fun ty b mb => .lam ty b mb) d pw?
    stk (k - 1) (leaf'.abstractRange d k)

/-- Pure mirror of `annotateLamsI`. -/
@[expose] def annotateLams (r : CoreFns m) (env : Env) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotateLams r env d fuel body (k + 1)
        (Expr.fvar (d + k) ty' :: fvs) ((ty', mb) :: stk)
    | t => annotateLamsLeaf r env d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeaf r env d t k fvs stk

/-! ## The chained tails (wraps) -/

/-- The chained `inferBody` λ-tail folded over the peeled binders
(innermost first, `j` the head entry's binder level): every wrapped
level's body is a λ, so the λ-rule performs no runs there (its
codomain check is chain-guarded, task #152) and the fold is pure. -/
@[expose] def inferLamsWrap (mode : CheckMode) (d : Nat) :
    List InferLamEntryX → Nat → Expr → PropWhen → m Expr
  | [], _j, bt, _prevPw => pure bt
  | (tyo, mb) :: rest, j, bt, prevPw => do
    if mode.verifiedChecks && !(mb.pw == prevPw) then
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    inferLamsWrap mode d rest (j - 1)
      (.forallE tyo (bt.abstract1 (d + j)) mb) mb.pw

/-- The chained λ-tail *at the peel's residual*: the innermost λ node's
own codomain-sort check (task #152 — it fires exactly when the residual
`t` is not a λ, which is when the peel stopped on it), then the pure
wrap of the peeled binders. -/
@[expose] def inferLamsTail (mode : CheckMode) (r : CoreFns m) (env : Env)
    (d : Nat) (t : Expr) (k : Nat) (stk : List InferLamEntryX)
    (bt : Expr) : m Expr := do
  if mode.verifiedChecks && !t.isLam then
    let btt ← r.inferIO (d + k) bt
    let vb ← ensureSort r env (d + k) btt
    match stk with
    | (_, mb₀) :: _ =>
      unless Level.zeronessOf vb == mb₀.pw do
        throw (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")
    | [] => pure ()
  inferLamsWrap mode d stk (k - 1) bt
    (match t.lamPw with
     | some pwT => pwT
     | none =>
       match stk with
       | (_, mb₀) :: _ => mb₀.pw
       | [] => .never)

/-- The chained `inferBody` ∀-tail folded over the peeled binders: per
level, the chained rule's `ensureSort` of the freshly built inner sort
(reproduced by `whnf_sort`), then the `imax`. -/
@[expose] def inferPisWrap (mode : CheckMode) (r : CoreFns m) (env : Env)
    (d : Nat) :
    List (Level × PropWhen) → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | (u, pw) :: rest, j, bt => do
    let v ← ensureSort r env (d + j + 1) bt
    if mode.verifiedChecks then
      unless Level.zeronessOf v == pw do
        throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    inferPisWrap mode r env d rest (j - 1) (.sort (.imax u v))

/-- The chained `annotateBody` ∀-tail folded over the peeled binders.
Task #161 P5: each level runs the pass's own write (`annotPwPi`), which
on a ∀ body is the chain read — so only the innermost level, whose body
is the leaf, ever infers. -/
def annotatePisWrap (r : CoreFns m) (env : Env) (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (ty', mb) :: rest, j, body' => do
    let pw ← if !pwWritten mb.pw then
        annotPwPi r env (d + j + 1) body'
      else pure mb.pw
    annotatePisWrap r env d rest (j - 1)
      (.forallE ty' (body'.abstract1 (d + j)) ⟨pw⟩)

/-- The chained `annotateBody` λ-tail folded over the peeled binders. -/
def annotateLamsWrap (r : CoreFns m) (env : Env) (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (ty', mb) :: rest, j, body' => do
    let pw ← if !pwWritten mb.pw then
        annotPwLam r env (d + j + 1) body'
      else pure mb.pw
    annotateLamsWrap r env d rest (j - 1)
      (.lam ty' (body'.abstract1 (d + j)) ⟨pw⟩)

/-! ## Unfolding equations -/

section Unfold

variable {r : CoreFns m} {env : Env} {d : Nat}

theorem inferLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams mode r d 0 t k fvs stk
      = inferLamsLeaf mode r d t k fvs stk := by rfl

theorem inferLams_succ_lam (fuel : Nat) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams mode r d (fuel + 1) (.lam ty body mb) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort _ =>
          inferLams mode r d fuel body (k + 1)
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs)
            ((ty.instantiateList fvs, mb) :: stk)
        | _ => throw (.invalid "expected a sort")) := by rfl

theorem inferLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ ty body mb, t ≠ .lam ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) :
    inferLams mode r d (fuel + 1) t k fvs stk
      = inferLamsLeaf mode r d t k fvs stk := by
  cases t with
  | lam ty body mb => exact absurd rfl (ht ty body mb)
  | _ => rw [inferLams] <;> exact fun _ _ _ h => nomatch h

theorem inferPis_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List (Level × PropWhen)) :
    inferPis mode r d 0 t k fvs stk
      = inferPisLeaf mode r d t k fvs stk := by rfl

theorem inferPis_succ_pi (fuel : Nat) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List (Level × PropWhen)) :
    inferPis mode r d (fuel + 1) (.forallE ty body mb) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort u =>
          inferPis mode r d fuel body (k + 1)
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs)
            ((u, mb.pw) :: stk)
        | _ => throw (.invalid "expected a sort")) := by rfl

theorem inferPis_succ_ne_pi (fuel : Nat) {t : Expr}
    (ht : ∀ ty body mb, t ≠ .forallE ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List (Level × PropWhen)) :
    inferPis mode r d (fuel + 1) t k fvs stk
      = inferPisLeaf mode r d t k fvs stk := by
  cases t with
  | forallE ty body mb => exact absurd rfl (ht ty body mb)
  | _ => rw [inferPis] <;> exact fun _ _ _ h => nomatch h

theorem annotatePis_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotatePis r env d 0 t k fvs stk = annotatePisLeaf r env d t k fvs stk := by rfl

theorem annotatePis_succ_pi (fuel : Nat) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotatePis r env d (fuel + 1) (.forallE ty body mb) k fvs stk
      = (do
        let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
        annotatePis r env d fuel body (k + 1)
          (Expr.fvar (d + k) ty' :: fvs) ((ty', mb) :: stk)) := by rfl

theorem annotatePis_succ_ne_pi (fuel : Nat) {t : Expr}
    (ht : ∀ ty body mb, t ≠ .forallE ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) :
    annotatePis r env d (fuel + 1) t k fvs stk
      = annotatePisLeaf r env d t k fvs stk := by
  cases t with
  | forallE ty body mb => exact absurd rfl (ht ty body mb)
  | _ => rw [annotatePis] <;> exact fun _ _ _ h => nomatch h

theorem annotateLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotateLams r env d 0 t k fvs stk = annotateLamsLeaf r env d t k fvs stk := by rfl

theorem annotateLams_succ_lam (fuel : Nat) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotateLams r env d (fuel + 1) (.lam ty body mb) k fvs stk
      = (do
        let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
        annotateLams r env d fuel body (k + 1)
          (Expr.fvar (d + k) ty' :: fvs) ((ty', mb) :: stk)) := by rfl

theorem annotateLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ ty body mb, t ≠ .lam ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) :
    annotateLams r env d (fuel + 1) t k fvs stk
      = annotateLamsLeaf r env d t k fvs stk := by
  cases t with
  | lam ty body mb => exact absurd rfl (ht ty body mb)
  | _ => rw [annotateLams] <;> exact fun _ _ _ h => nomatch h

/-! Shape equations of the fueled bodies on binder nodes (definitional;
the fuel steps once). -/

theorem inferTypeCore_forallE_eq (env : Env) (F d : Nat)
    (ty body : Expr) (mb : BinderMeta) :
    inferTypeCore mode env (F + 1) d (.forallE ty body mb)
      = (inferTypeCore mode env F d ty >>= fun tty =>
         whnf mode env F d tty >>= fun w =>
         match w with
         | .sort u =>
           inferTypeCore mode env F (d + 1)
               (body.instantiate1 (.fvar d ty)) >>= fun bt =>
             ensureSortCore mode env F (d + 1) bt >>= fun v => do
               if mode.verifiedChecks then
                 unless Level.zeronessOf v == mb.pw do
                   throw (.notImplemented
                     "sort-annotation mismatch (forall-cod)")
               pure (Expr.sort (.imax u v))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem inferTypeCore_lam_eq (env : Env) (F d : Nat)
    (ty body : Expr) (mb : BinderMeta) :
    inferTypeCore mode env (F + 1) d (.lam ty body mb)
      = (inferTypeCore mode env F d ty >>= fun tty =>
         whnf mode env F d tty >>= fun w =>
         match w with
         | .sort _ =>
           inferTypeCore mode env F (d + 1)
               (body.instantiate1 (.fvar d ty)) >>= fun bt =>
             (do
               if mode.verifiedChecks then
                 match body.lamPw with
                 | some pwI =>
                   unless mb.pw == pwI do
                     throw (.notImplemented
                       "sort-annotation mismatch (lam-cod-chain)")
                 | none => do
                   let btt ← inferTypeIO mode env F (d + 1) bt
                   let vb ← ensureSortCore mode env F (d + 1) btt
                   unless Level.zeronessOf vb == mb.pw do
                     throw (.notImplemented
                       "sort-annotation mismatch (lam-cod-leaf)")
               pure (Expr.forallE ty (bt.abstract1 d) mb))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem annotateCore_forallE_eq (env : Env) (F d : Nat)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore mode env (F + 1) d (.forallE ty body mb)
      = (annotateCore mode env F d ty >>= fun ty' =>
         annotateCore mode env F (d + 1)
             (body.instantiate1 (.fvar d ty')) >>= fun body' =>
           if !pwWritten mb.pw then
             annotPwPi (pureFns mode env F) env (d + 1) body' >>= fun pw =>
               pure (Expr.forallE ty' (body'.abstract1 d) ⟨pw⟩)
           else pure (Expr.forallE ty' (body'.abstract1 d) ⟨mb.pw⟩)) := rfl

theorem annotateCore_lam_eq (env : Env) (F d : Nat)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore mode env (F + 1) d (.lam ty body mb)
      = (annotateCore mode env F d ty >>= fun ty' =>
         annotateCore mode env F (d + 1)
             (body.instantiate1 (.fvar d ty')) >>= fun body' =>
           if !pwWritten mb.pw then
             annotPwLam (pureFns mode env F) env (d + 1) body' >>= fun pw =>
               pure (Expr.lam ty' (body'.abstract1 d) ⟨pw⟩)
           else pure (Expr.lam ty' (body'.abstract1 d) ⟨mb.pw⟩)) := rfl

theorem ensureSortCore_eq (env : Env) (F d : Nat) (e : Expr) :
    ensureSortCore mode env F d e
      = (whnf mode env F d e >>= fun w =>
         match w with
         | .sort u => pure u
         | _ => throw (.invalid "expected a sort")) := rfl

theorem bind_okB {α β : Type} {x : Except CheckError α}
    {g : α → Except CheckError β} {res : β}
    (h : (x >>= g) = .ok res) : ∃ a, x = .ok a ∧ g a = .ok res := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem okB_bind {α β : Type} (a : α)
    {g : α → Except CheckError β} :
    ((Except.ok a : Except CheckError α) >>= g) = g a := rfl

/-- `whnf` is the identity on sorts (two fuel steps in). -/
theorem whnf_sort (env : Env) (F d : Nat) (u : Level) :
    whnf mode env (F + 2) d (.sort u) = .ok (.sort u) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode env (F + 1)) env d whnfLoopFuel _ = _
  rw [hk]
  rfl

end Unfold

/-! ## Fixed-fuel (`atF`) spellings -/

section AtF

variable {env : Env}

theorem inferLamsOut_atF (d : Nat) :
    ∀ (stk : List InferLamEntryX) (j : Nat) (cur : Expr)
      (prevPw : PropWhen) (F : Nat),
      (inferLamsOut (m := FueledM) mode d stk j cur prevPw).val F
        = inferLamsOut (m := CheckM) mode d stk j cur prevPw
  | [], _, _, _, _ => rfl
  | (_tyo, mb) :: rest, j, _cur, prevPw, F => by
    unfold inferLamsOut
    dsimp only
    by_cases hg : (mode.verifiedChecks && !(mb.pw == prevPw)) = true
    · simp only [if_pos hg]
      rfl
    · simp only [if_neg hg]
      exact inferLamsOut_atF d rest (j - 1) _ _ F

theorem inferLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) (F : Nat) :
    (inferLamsLeaf mode (fueledFns mode env) d t k fvs stk).val F
      = inferLamsLeaf mode (pureFns mode env F) d t k fvs stk := by
  unfold inferLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  cases t <;>
    try exact inferLamsOut_atF d stk (k - 1) _ _ F
  all_goals
    dsimp only
    by_cases hv : mode.verifiedChecks = true
    case neg =>
      simp only [if_neg hv]
      exact inferLamsOut_atF d stk (k - 1) _ _ F
    simp only [if_pos hv]
    rw [FueledM.atF_bind]
    congr 1
    funext btt
    rw [FueledM.atF_bind]
    congr 1
    funext w
    cases w
    case sort vb =>
      dsimp only
      cases stk with
      | nil => exact inferLamsOut_atF d [] (k - 1) _ _ F
      | cons e rest =>
        obtain ⟨ty0, mb0⟩ := e
        dsimp only
        by_cases hz : (Level.zeronessOf vb == mb0.pw) = true
        · simp only [if_pos hz]
          exact inferLamsOut_atF d _ (k - 1) _ _ F
        · simp only [if_neg hz]
          rfl
    all_goals rfl

theorem inferLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat),
      (inferLams mode (fueledFns mode env) d fuel t k fvs stk).val F
        = inferLams mode (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [inferLams_succ_lam, inferLams_succ_lam]
      rw [FueledM.atF_bind]
      congr 1
      funext tty
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w <;> first
        | rfl
        | exact inferLams_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [inferLams_succ_ne_lam _ ht, inferLams_succ_ne_lam _ ht]
      exact inferLamsLeaf_atF d t k fvs stk F

theorem inferPisOut_atF :
    ∀ (stk : List (Level × PropWhen)) (v : Level) (F : Nat),
      (inferPisOut (m := FueledM) mode stk v).val F
        = inferPisOut (m := CheckM) mode stk v
  | [], _, _ => rfl
  | (u, pw) :: rest, v, F => by
    unfold inferPisOut
    dsimp only
    by_cases hg : (mode.verifiedChecks && !(Level.zeronessOf v == pw))
        = true
    · simp only [if_pos hg]
      rfl
    · simp only [if_neg hg]
      exact inferPisOut_atF rest (.imax u v) F

theorem inferPisLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List (Level × PropWhen)) (F : Nat) :
    (inferPisLeaf mode (fueledFns mode env) d t k fvs stk).val F
      = inferPisLeaf mode (pureFns mode env F) d t k fvs stk := by
  unfold inferPisLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind]
  congr 1
  funext w
  cases w <;> try rfl
  case sort v =>
    dsimp only
    rw [FueledM.atF_bind]
    congr 1
    exact inferPisOut_atF stk v F

theorem inferPis_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List (Level × PropWhen)) (F : Nat),
      (inferPis mode (fueledFns mode env) d fuel t k fvs stk).val F
        = inferPis mode (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferPisLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hpi : ∃ ty body mb, t = Expr.forallE ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hpi
      rw [inferPis_succ_pi, inferPis_succ_pi]
      rw [FueledM.atF_bind]
      congr 1
      funext tty
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w <;> first
        | rfl
        | exact inferPis_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body mb, t ≠ Expr.forallE ty body mb :=
        fun ty b mb hh => hpi ⟨ty, b, mb, hh⟩
      rw [inferPis_succ_ne_pi _ ht, inferPis_succ_ne_pi _ ht]
      exact inferPisLeaf_atF d t k fvs stk F

theorem annotateBindersOut_atF (mk : Expr → Expr → BinderMeta → Expr)
    (d : Nat) :
    ∀ (pw? : Option PropWhen) (stk : List AnnotBinderEntryX) (j : Nat)
      (cur : Expr) (F : Nat),
      (annotateBindersOut (m := FueledM) mk d pw? stk j cur).val F
        = annotateBindersOut (m := CheckM) mk d pw? stk j cur
  | _, [], _, _, _ => rfl
  | _pw?, (_ty', _mb) :: rest, j, _cur, F =>
    annotateBindersOut_atF mk d _ rest (j - 1) _ F

theorem annotatePisLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) (F : Nat) :
    (annotatePisLeaf (fueledFns mode env) env d t k fvs stk).val F
      = annotatePisLeaf (pureFns mode env F) env d t k fvs stk := by
  unfold annotatePisLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext leaf'
  rw [FueledM.atF_bind]
  congr 1
  · unfold annotatePisPw
    rw [FueledM.atF_bind, annotPwPi_atF]
    rfl
  · funext pw?
    exact annotateBindersOut_atF _ d _ stk (k - 1) _ F

theorem annotatePis_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat),
      (annotatePis (fueledFns mode env) env d fuel t k fvs stk).val F
        = annotatePis (pureFns mode env F) env d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => annotatePisLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hpi : ∃ ty body mb, t = Expr.forallE ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hpi
      rw [annotatePis_succ_pi, annotatePis_succ_pi]
      rw [FueledM.atF_bind]
      congr 1
      funext ty'
      exact annotatePis_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body mb, t ≠ Expr.forallE ty body mb :=
        fun ty b mb hh => hpi ⟨ty, b, mb, hh⟩
      rw [annotatePis_succ_ne_pi _ ht, annotatePis_succ_ne_pi _ ht]
      exact annotatePisLeaf_atF d t k fvs stk F

theorem annotateLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) (F : Nat) :
    (annotateLamsLeaf (fueledFns mode env) env d t k fvs stk).val F
      = annotateLamsLeaf (pureFns mode env F) env d t k fvs stk := by
  unfold annotateLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext leaf'
  rw [FueledM.atF_bind]
  congr 1
  · unfold annotateLamsPw
    rw [FueledM.atF_bind, annotPwLam_atF]
    rfl
  · funext pw?
    exact annotateBindersOut_atF _ d _ stk (k - 1) _ F

theorem annotateLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat),
      (annotateLams (fueledFns mode env) env d fuel t k fvs stk).val F
        = annotateLams (pureFns mode env F) env d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => annotateLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [annotateLams_succ_lam, annotateLams_succ_lam]
      rw [FueledM.atF_bind]
      congr 1
      funext ty'
      exact annotateLams_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [annotateLams_succ_ne_lam _ ht, annotateLams_succ_ne_lam _ ht]
      exact annotateLamsLeaf_atF d t k fvs stk F

end AtF

/-! ## Rebuild/wrap identification (pure) and peel soundness -/

section InferSound

variable {env : Env}

/-- The rebuild fold equals the chained `abstract1` fold — pure
`abstractRange` algebra (`abstractRange_succ`), stated at the rebuild
cursor the leaf phase enters with (`stk.length = j + 1`). -/
theorem inferLamsOut_wrap {d : Nat} :
    ∀ (stk : List InferLamEntryX) (j : Nat) (bt : Expr)
      (prevPw : PropWhen),
      stk.length = j + 1 →
      inferLamsOut (m := CheckM) mode d stk j
          (bt.abstractRange d (j + 1)) prevPw
        = inferLamsWrap (m := CheckM) mode d stk j bt prevPw := by
  intro stk
  induction stk with
  | nil => intro j bt prevPw hlen; exact nomatch hlen
  | cons e rest ih =>
    obtain ⟨tyo, mb⟩ := e
    intro j bt prevPw hlen
    unfold inferLamsOut inferLamsWrap
    dsimp only
    by_cases hg : (mode.verifiedChecks && !(mb.pw == prevPw)) = true
    · simp only [if_pos hg]
      rfl
    simp only [if_neg hg]
    show inferLamsOut (m := CheckM) mode d rest (j - 1)
        (Expr.forallE (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1)) mb) mb.pw
      = inferLamsWrap (m := CheckM) mode d rest (j - 1)
          (Expr.forallE tyo (bt.abstract1 (d + j)) mb) mb.pw
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      show Except.ok _ = Except.ok _
      congr 2
      · exact abstractRange_zero ..
      · rw [abstractRange_succ, abstractRange_zero]
    | cons e' rest' =>
      have hj1 : 1 ≤ j := by
        simp only [List.length_cons] at hlen
        omega
      have hnode : Expr.forallE (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1)) mb
          = (Expr.forallE tyo (bt.abstract1 (d + j)) mb).abstractRange
              d ((j - 1) + 1) := by
        have hj : (j - 1) + 1 = j := by omega
        rw [hj]
        show _ = Expr.forallE (tyo.abstractRange d j 0)
          ((bt.abstract1 (d + j) 0).abstractRange d j 1) mb
        rw [abstractRange_succ]
      rw [hnode]
      exact ih (j - 1) _ mb.pw (by
        simp only [List.length_cons] at hlen ⊢
        omega)

/-- Leaf-phase soundness: the mirror's leaf run is the chained
inference of the bulk-opened residual, the innermost λ node's own
codomain check (task #152) and the (pure) tails. -/
theorem inferLamsLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List InferLamEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : inferLamsLeaf mode (pureFns mode env F) d t k fvs stk = .ok res) :
    ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferLamsTail (m := CheckM) mode (pureFns mode env F')
        env d t k stk bt) = .ok res := by
  unfold inferLamsLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  refine ⟨F, ?_⟩
  rw [hbt, okB_bind]
  unfold inferLamsTail
  -- the guard, and the check it guards, are the leaf's own
  have hout : ∀ {res' : Expr} {prevPw : PropWhen},
      inferLamsOut (m := CheckM) mode d stk (k - 1)
          (bt.abstractRange d k) prevPw = .ok res' →
        inferLamsWrap (m := CheckM) mode d stk (k - 1) bt prevPw
          = .ok res' := by
    intro res' prevPw h
    cases stk with
    | nil =>
      obtain rfl : k = 0 := by simpa using hlen.symm
      unfold inferLamsOut at h
      rw [abstractRange_zero] at h
      exact h
    | cons e rest =>
      have hk1 : 1 ≤ k := by rw [← hlen]; simp
      have hkeq : (k - 1) + 1 = k := by omega
      rw [← inferLamsOut_wrap (e :: rest) (k - 1) bt prevPw
        (by simp only [List.length_cons] at hlen ⊢; omega), hkeq]
      exact h
  revert hrun
  cases t
  case lam ty' body' mb' =>
    intro hrun
    simp only [Expr.isLam, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    exact hout hrun
  all_goals
    intro hrun
    dsimp only at hrun ⊢
    simp only [Expr.isLam, Bool.not_false, Bool.and_true]
    by_cases hv : mode.verifiedChecks = true
    case neg =>
      rw [if_neg hv] at hrun ⊢
      exact hout hrun
    rw [if_pos hv] at hrun ⊢
    rw [inferTypeIO_def] at hrun ⊢
    obtain ⟨btt, hbtt, hrun⟩ := bind_okB hrun
    rw [hbtt, okB_bind]
    obtain ⟨w, hw, hrun⟩ := bind_okB hrun
    rw [whnf_def] at hw
    rw [ensureSort_def, ensureSortCore_eq, hw, okB_bind]
    revert hrun
    cases w with
    | sort v =>
      intro hrun
      dsimp only at hrun ⊢
      cases stk with
      | nil =>
        try rw [pure_bind] at hrun
        try rw [pure_bind]
        exact hout hrun
      | cons e rest =>
        obtain ⟨ty0, mb0⟩ := e
        dsimp only at hrun ⊢
        try rw [pure_bind]
        by_cases hz : (Level.zeronessOf v == mb0.pw) = true
        · simp only [if_pos hz] at hrun ⊢
          exact hout hrun
        · simp only [if_neg hz] at hrun
          exact nomatch hrun
    | bvar _ | fvar _ _ | const _ _ | app _ _ | lam _ _ _
    | forallE _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      intro hrun
      exact nomatch hrun

/-- A successful peel run is reproduced by the chained inference of the
bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferLams_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      (∀ x ∈ fvs, ∃ i ty, x = Expr.fvar i ty) →
      inferLams mode (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferLamsTail (m := CheckM) mode (pureFns mode env F')
          env d t k stk bt) = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hfv hrun
    rw [inferLams_zero] at hrun
    exact inferLamsLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hfv hrun
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [inferLams_succ_lam] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam tt b mm => exact nomatch hrun
        | forallE tt b mm => exact nomatch hrun
        | letE tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      have hfv' : ∀ x ∈ (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs),
          ∃ i ty', x = Expr.fvar i ty' := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨_, _, rfl⟩
        · exact hfv x hx'
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hfv' hrun
      obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
      have hlamL : (Expr.lam ty body mb).instantiateList fvs
          = Expr.lam (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hlamL, inferTypeCore_lam_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind]
      -- the outer level's own tail skips the leaf guard (it is a λ)
      unfold inferLamsTail at htail ⊢
      rw [show (Expr.lam ty body mb).isLam = true from rfl]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      rw [show (k + 1 : Nat) - 1 = k from rfl] at htail
      -- htail's guard is the spec node's own check: correlate by the
      -- body's λ-meta head reading (instantiation with fvars
      -- preserves it)
      rw [show ((body.instantiateList fvs 1).lamPw) = body.lamPw
        from lamPw_instantiateList_fvars hfv body 1]
      have hisl := isLam_instantiateList_fvars hfv body 1
      revert htail
      have hlampw : (Expr.lam ty body mb).lamPw = some mb.pw := rfl
      rw [hlampw]
      cases hbp : body.lamPw with
      | some pwI =>
        intro htail
        have hbl : body.isLam = true := by
          cases body <;> first
            | rfl
            | exact nomatch hbp
        simp only [hbl, Bool.not_true, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte] at htail
        unfold inferLamsWrap at htail
        by_cases hg : (mode.verifiedChecks && !(mb.pw == pwI)) = true
        · rw [if_pos hg] at htail
          exact nomatch htail
        rw [if_neg hg] at htail
        dsimp only
        by_cases hv : mode.verifiedChecks = true
        · rw [if_pos hv]
          have hpw : (mb.pw == pwI) = true := by
            by_cases hc : (mb.pw == pwI) = true
            · exact hc
            · exact absurd (by simp [hv, hc]) hg
          rw [if_pos hpw, pure_bind]
          exact htail
        · rw [if_neg hv, pure_bind]
          exact htail
      | none =>
        intro htail
        have hbl : body.isLam = false := by
          cases body <;> first
            | rfl
            | exact nomatch hbp
        simp only [hbl, Bool.not_false, Bool.and_true] at htail
        dsimp only
        by_cases hv : mode.verifiedChecks = true
        case neg =>
          rw [if_neg hv] at htail ⊢
          rw [pure_bind]
          unfold inferLamsWrap at htail
          rw [if_neg (by simp [hv])] at htail
          exact htail
        rw [if_pos hv] at htail ⊢
        rw [inferTypeIO_def] at htail
        obtain ⟨btt, hbtt, htail⟩ := bind_okB htail
        rw [inferTypeIO_mono (Nat.le_max_right F F') hbtt, okB_bind]
        rw [ensureSort_def] at htail
        obtain ⟨v, hv2, htail⟩ := bind_okB htail
        rw [ensureSortCore_mono (Nat.le_max_right F F') hv2, okB_bind]
        try dsimp only at htail ⊢
        by_cases hz : (Level.zeronessOf v == mb.pw) = true
        case neg =>
          rw [if_neg hz] at htail
          exact nomatch htail
        rw [if_pos hz] at htail ⊢
        rw [pure_bind]
        unfold inferLamsWrap at htail
        rw [if_neg (by simp)] at htail
        exact htail
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [inferLams_succ_ne_lam _ ht] at hrun
      exact inferLamsLeaf_sound hlen hrun

/-- The ∀-wrap is fuel monotone (its only runs are `ensureSort`s). -/
theorem inferPisWrap_mono {d : Nat} :
    ∀ {stk : List (Level × PropWhen)} {j : Nat} {bt : Expr} {F F' : Nat},
      F ≤ F' → ∀ {res : Expr},
      inferPisWrap mode (pureFns mode env F) env d stk j bt = .ok res →
      inferPisWrap mode (pureFns mode env F') env d stk j bt = .ok res := by
  intro stk
  induction stk with
  | nil => intro j bt F F' hle res h; exact h
  | cons upw rest ih =>
    obtain ⟨u, pw⟩ := upw
    intro j bt F F' hle res h
    unfold inferPisWrap at h ⊢
    obtain ⟨v, hv, h⟩ := bind_okB h
    rw [ensureSort_def] at hv
    rw [ensureSort_def, ensureSortCore_mono hle hv, okB_bind]
    dsimp only at h ⊢
    by_cases hver : mode.verifiedChecks = true
    case neg =>
      rw [if_neg hver] at h ⊢
      exact ih hle h
    rw [if_pos hver] at h ⊢
    by_cases hz : (Level.zeronessOf v == pw) = true
    · rw [if_pos hz] at h ⊢
      exact ih hle h
    · rw [if_neg hz] at h
      exact nomatch h

/-- The `imax`-fold wrap on an explicit sort is the fold mirror's own
run (the chained per-level `ensureSort`s reduce by `whnf_sort`; the
per-node validations are the fold's). -/
theorem inferPisWrap_sort {d : Nat} :
    ∀ (stk : List (Level × PropWhen)) (j : Nat) (v : Level) {F : Nat},
      2 ≤ F →
      inferPisWrap mode (pureFns mode env F) env d stk j (.sort v)
        = (inferPisOut (m := CheckM) mode stk v).map Expr.sort := by
  intro stk
  induction stk with
  | nil => intro j v F hF; rfl
  | cons upw rest ih =>
    obtain ⟨u, pw⟩ := upw
    intro j v F hF
    show (ensureSort (pureFns mode env F) env (d + j + 1) (.sort v) >>=
      fun v' => (do
        if mode.verifiedChecks then
          unless Level.zeronessOf v' == pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        inferPisWrap mode (pureFns mode env F) env d rest (j - 1)
          (.sort (.imax u v')))) = _
    rw [ensureSort_def, ensureSortCore_eq]
    have hw : whnf mode env F (d + j + 1) (.sort v) = .ok (.sort v) := by
      obtain ⟨F₂, rfl⟩ : ∃ F₂, F = F₂ + 2 := ⟨F - 2, by omega⟩
      exact whnf_sort env F₂ (d + j + 1) v
    rw [hw, okB_bind]
    dsimp only
    rw [pure_bind]
    unfold inferPisOut
    dsimp only
    by_cases hg : (mode.verifiedChecks && !(Level.zeronessOf v == pw))
        = true
    · have hver : mode.verifiedChecks = true := by
        rcases Bool.and_eq_true .. |>.mp hg with ⟨h1, -⟩
        exact h1
      have hz : ¬ ((Level.zeronessOf v == pw) = true) := by
        rcases Bool.and_eq_true .. |>.mp hg with ⟨-, h2⟩
        simpa using h2
      rw [if_pos hg, if_pos hver, if_neg hz]
      rfl
    · rw [if_neg hg]
      by_cases hver : mode.verifiedChecks = true
      · have hz : (Level.zeronessOf v == pw) = true := by
          by_cases hc : (Level.zeronessOf v == pw) = true
          · exact hc
          · exact absurd (by simp [hver, hc]) hg
        rw [if_pos hver, if_pos hz]
        exact ih (j - 1) (.imax u v) hF
      · rw [if_neg hver]
        exact ih (j - 1) (.imax u v) hF

/-- Leaf-phase soundness for the ∀-loop. -/
theorem inferPisLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List (Level × PropWhen)} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k) (hk : 1 ≤ k)
    (hrun : inferPisLeaf mode (pureFns mode env F) d t k fvs stk
      = .ok res) :
    ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferPisWrap mode (pureFns mode env F') env d stk
        (k - 1) bt) = .ok res := by
  unfold inferPisLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  obtain ⟨w, hww, hrun⟩ := bind_okB hrun
  rw [whnf_def] at hww
  obtain ⟨v, rfl⟩ : ∃ v, w = Expr.sort v := by
    cases w with
    | sort v' => exact ⟨v', rfl⟩
    | bvar i => exact nomatch hrun
    | fvar idx tt => exact nomatch hrun
    | const nm us => exact nomatch hrun
    | app f a => exact nomatch hrun
    | lam tt b mm => exact nomatch hrun
    | forallE tt b mm => exact nomatch hrun
    | letE tt vv b => exact nomatch hrun
    | lit l => exact nomatch hrun
    | proj sp i e => exact nomatch hrun
  dsimp only at hrun
  obtain ⟨iv, hout, hres⟩ := bind_okB hrun
  injection hres with hres
  cases stk with
  | nil =>
    exact absurd hlen (by simp; omega)
  | cons upw rest =>
    obtain ⟨u, pw⟩ := upw
    have hkeq : d + (k - 1) + 1 = d + k := by omega
    refine ⟨max F 2, ?_⟩
    rw [inferTypeCore_mono (Nat.le_max_left F 2) hbt, okB_bind]
    show (ensureSort (pureFns mode env (max F 2)) env (d + (k - 1) + 1)
        bt >>= fun v' => (do
      if mode.verifiedChecks then
        unless Level.zeronessOf v' == pw do
          throw (.notImplemented "sort-annotation mismatch (forall-cod)")
      inferPisWrap mode (pureFns mode env (max F 2)) env d rest
        ((k - 1) - 1) (.sort (.imax u v')))) = _
    rw [ensureSort_def, ensureSortCore_eq, hkeq]
    rw [whnf_mono (Nat.le_max_left F 2) hww, okB_bind]
    dsimp only
    rw [pure_bind]
    unfold inferPisOut at hout
    dsimp only at hout
    by_cases hg : (mode.verifiedChecks && !(Level.zeronessOf v == pw))
        = true
    · rw [if_pos hg] at hout
      exact nomatch hout
    rw [if_neg hg] at hout
    have hrest : inferPisWrap mode (pureFns mode env (max F 2)) env d
        rest ((k - 1) - 1) (.sort (.imax u v))
        = .ok res := by
      rw [inferPisWrap_sort rest ((k - 1) - 1) (.imax u v)
        (Nat.le_max_right F 2), hout]
      rw [← hres]
      rfl
    by_cases hver : mode.verifiedChecks = true
    · have hz : (Level.zeronessOf v == pw) = true := by
        by_cases hc : (Level.zeronessOf v == pw) = true
        · exact hc
        · exact absurd (by simp [hver, hc]) hg
      rw [if_pos hver, if_pos hz]
      exact hrest
    · rw [if_neg hver]
      exact hrest

/-- A successful ∀-peel run is reproduced by the chained inference of
the bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferPis_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List (Level × PropWhen)) (F : Nat) (res : Expr),
      stk.length = k → 1 ≤ k →
      inferPis mode (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferPisWrap mode (pureFns mode env F') env d stk
          (k - 1) bt) = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hk hrun
    rw [inferPis_zero] at hrun
    exact inferPisLeaf_sound hlen hk hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hk hrun
    by_cases hpi : ∃ ty body mb, t = Expr.forallE ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hpi
      rw [inferPis_succ_pi] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam tt b mm => exact nomatch hrun
        | forallE tt b mm => exact nomatch hrun
        | letE tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) (by omega) hrun
      obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
      have hpiL : (Expr.forallE ty body mb).instantiateList fvs
          = Expr.forallE (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hpiL, inferTypeCore_forallE_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind]
      -- the chained level's `ensureSort` + `imax` is the wrap's head
      -- step (at `(k+1) - 1 = k`), and the suffix continues
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      unfold inferPisWrap at hwrap
      obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
      rw [ensureSort_def] at hv
      rw [show d + k + 1 = d + (k + 1) from by omega] at hv
      rw [ensureSortCore_mono (Nat.le_max_right F F') hv, okB_bind]
      dsimp only at hwrap ⊢
      by_cases hver : mode.verifiedChecks = true
      case neg =>
        rw [if_neg hver] at hwrap ⊢
        rw [pure_bind]
        exact inferPisWrap_mono (Nat.le_trans (Nat.le_max_right F F')
          (Nat.le_succ _)) hwrap
      rw [if_pos hver] at hwrap ⊢
      by_cases hz : (Level.zeronessOf v == mb.pw) = true
      case neg =>
        rw [if_neg hz] at hwrap
        exact nomatch hwrap
      rw [if_pos hz] at hwrap ⊢
      rw [pure_bind]
      exact inferPisWrap_mono (Nat.le_trans (Nat.le_max_right F F')
        (Nat.le_succ _)) hwrap
    · have ht : ∀ ty body mb, t ≠ Expr.forallE ty body mb :=
        fun ty b mb hh => hpi ⟨ty, b, mb, hh⟩
      rw [inferPis_succ_ne_pi _ ht] at hrun
      exact inferPisLeaf_sound hlen hk hrun

end InferSound

/-! ## Annotation loops: rebuild/wrap identification and peel
soundness -/

section AnnotSound

variable {env : Env}

/-- The generic rebuild fold equals the chained `abstract1` fold
(instantiated at ∀- and λ-rebuilds; `hmkR` is the constructor's
`abstractRange`/`abstract1` commutation, definitional for both).

**Task #161 P5.**  Both folds now write the prop-ness datum, by the
same *local* rule: the loop threads outward the datum it just wrote,
the chained tail re-reads it off the node it just built (`annotPwPi`'s
and `annotPwLam`'s chain read).  `hpwf_read` is exactly that
coincidence, and `hinv` carries it along the fold — so the telescope
collapse never has to be re-derived here: the leaf computes once
(`annotatePisLeaf`), and every level above reads. -/
theorem annotateBindersOut_wrap
    {mk : Expr → Expr → BinderMeta → Expr}
    (hmkR : ∀ ty b bi d k c, (mk ty b bi).abstractRange d k c
      = mk (ty.abstractRange d k c) (b.abstractRange d k (c + 1)) bi)
    {d : Nat}
    (rdOf : Expr → Option PropWhen)
    (pwf : Nat → Expr → CheckM PropWhen)
    (hmkRd : ∀ ty b mb, rdOf (mk ty b mb) = some mb.pw)
    (hpwf_read : ∀ (D : Nat) (e : Expr) (p : PropWhen),
      rdOf e = some p → pwf D e = pure p)
    (wrap : List AnnotBinderEntryX → Nat → Expr → CheckM Expr)
    (hwrap_nil : ∀ j bt, wrap [] j bt = pure bt)
    (hwrap_cons : ∀ ty' mb rest j bt,
      wrap ((ty', mb) :: rest) j bt
        = (if !pwWritten mb.pw then
            pwf (d + j + 1) bt >>= fun pw =>
              wrap rest (j - 1) (mk ty' (bt.abstract1 (d + j)) ⟨pw⟩)
          else wrap rest (j - 1)
              (mk ty' (bt.abstract1 (d + j)) ⟨mb.pw⟩))) :
    ∀ (stk : List AnnotBinderEntryX) (j : Nat) (bt : Expr)
      (pw? : Option PropWhen),
      stk.length = j + 1 →
      AnnotPwOk (pwf (d + j + 1) bt) pw? →
      annotateBindersOut (m := CheckM) mk d pw? stk j
          (bt.abstractRange d (j + 1))
        = wrap stk j bt := by
  intro stk
  induction stk with
  | nil => intro j bt pw? hlen _; exact nomatch hlen
  | cons e rest ih =>
    obtain ⟨ty', mb⟩ := e
    intro j bt pw? hlen hinv
    rw [hwrap_cons]
    -- the datum both sides settle on at this level
    have hq : ∃ q : PropWhen,
        (if !pwWritten mb.pw then
            pwf (d + j + 1) bt >>= fun pw =>
              wrap rest (j - 1) (mk ty' (bt.abstract1 (d + j)) ⟨pw⟩)
          else wrap rest (j - 1)
              (mk ty' (bt.abstract1 (d + j)) ⟨mb.pw⟩))
          = wrap rest (j - 1) (mk ty' (bt.abstract1 (d + j)) ⟨q⟩) ∧
        annotBinderMeta pw? mb = (⟨q⟩ : BinderMeta) := by
      simp only [annotBinderMeta]
      cases pw? with
      | none => exact (hinv : False).elim
      | some pw =>
        have hpw : _ = Except.ok pw := hinv
        by_cases hw : pwWritten mb.pw
        · exact ⟨mb.pw, by simp [hw], by simp [hw]⟩
        · refine ⟨pw, ?_, by simp [hw]⟩
          simp only [hw, Bool.not_false, if_true, ↓reduceIte, hpw, okB_bind]
    obtain ⟨q, hqf, hqm⟩ := hq
    rw [hqf]
    show annotateBindersOut (m := CheckM) mk d
        (pw?.map fun _ => (annotBinderMeta pw? mb).pw)
        rest (j - 1)
        (mk (ty'.abstractRange d j) (bt.abstractRange d (j + 1))
          (annotBinderMeta pw? mb))
      = wrap rest (j - 1) (mk ty' (bt.abstract1 (d + j)) ⟨q⟩)
    rw [hqm]
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      rw [hwrap_nil]
      show (pure (mk (ty'.abstractRange d 0)
          (bt.abstractRange d (0 + 1)) ⟨q⟩) : CheckM Expr)
        = pure (mk ty' (bt.abstract1 (d + 0)) ⟨q⟩)
      rw [abstractRange_zero, abstractRange_succ, abstractRange_zero]
    | cons e' rest' =>
      have hj1 : 1 ≤ j := by
        simp only [List.length_cons] at hlen
        omega
      have hnode : mk (ty'.abstractRange d j)
          (bt.abstractRange d (j + 1)) ⟨q⟩
          = (mk ty' (bt.abstract1 (d + j)) ⟨q⟩).abstractRange
              d ((j - 1) + 1) := by
        have hj : (j - 1) + 1 = j := by omega
        rw [hj, hmkR]
        congr 1
        rw [abstractRange_succ]
      rw [hnode]
      refine ih (j - 1) _ _ (by
        simp only [List.length_cons] at hlen ⊢
        omega) ?_
      -- the threaded datum is what the chain read returns on the node
      -- just built: `hmkRd` then `hpwf_read`
      have hj : d + (j - 1) + 1 = d + j := by omega
      cases pw? with
      | none => exact (hinv : False).elim
      | some pw =>
        show _ = Except.ok _
        rw [hj]
        exact hpwf_read _ _ _ (hmkRd ty' (bt.abstract1 (d + j)) ⟨q⟩)

/-! ### The write's fuel monotonicity and the leaf bridge (task #161 P5) -/


theorem annotatePisWrap_nil (r : CoreFns CheckM) (env : Env) (d j : Nat)
    (bt : Expr) :
    annotatePisWrap r env d [] j bt = pure bt := by rfl

theorem annotatePisWrap_cons (r : CoreFns CheckM) (env : Env) (d : Nat)
    (ty' : Expr) (mb : BinderMeta)
    (rest : List AnnotBinderEntryX) (j : Nat) (bt : Expr) :
    annotatePisWrap r env d ((ty', mb) :: rest) j bt
      = (if !pwWritten mb.pw then
          annotPwPi r env (d + j + 1) bt >>= fun pw =>
            annotatePisWrap r env d rest (j - 1)
              (.forallE ty' (bt.abstract1 (d + j)) ⟨pw⟩)
        else annotatePisWrap r env d rest (j - 1)
              (.forallE ty' (bt.abstract1 (d + j)) ⟨mb.pw⟩)) := by
  simp only [annotatePisWrap]
  split <;> rfl

theorem annotateLamsWrap_nil (r : CoreFns CheckM) (env : Env) (d j : Nat)
    (bt : Expr) :
    annotateLamsWrap r env d [] j bt = pure bt := by rfl

theorem annotateLamsWrap_cons (r : CoreFns CheckM) (env : Env) (d : Nat)
    (ty' : Expr) (mb : BinderMeta)
    (rest : List AnnotBinderEntryX) (j : Nat) (bt : Expr) :
    annotateLamsWrap r env d ((ty', mb) :: rest) j bt
      = (if !pwWritten mb.pw then
          annotPwLam r env (d + j + 1) bt >>= fun pw =>
            annotateLamsWrap r env d rest (j - 1)
              (.lam ty' (bt.abstract1 (d + j)) ⟨pw⟩)
        else annotateLamsWrap r env d rest (j - 1)
              (.lam ty' (bt.abstract1 (d + j)) ⟨mb.pw⟩)) := by
  simp only [annotateLamsWrap]
  split <;> rfl


/-- The ∀ write is fuel-monotone: it is one `infer` and one
`ensureSort`, or a pure chain read. -/
theorem annotPwPi_mono {env : Env} {F F' : Nat} (hle : F ≤ F')
    {d : Nat} {e : Expr} {pw : PropWhen}
    (h : annotPwPi (pureFns mode env F) env d e = .ok pw) :
    annotPwPi (pureFns mode env F') env d e = .ok pw := by
  revert h
  unfold annotPwPi
  cases typeSortPW env.find? e with
  | some p => exact id
  | none =>
    dsimp only
    intro h
    obtain ⟨bt, hbt, h⟩ := bind_okB h
    rw [inferTypeIO_def] at hbt
    rw [show ((pureFns mode env F').inferIO d e) =
      inferTypeIO mode env F' d e from rfl,
      inferTypeIO_mono hle hbt, okB_bind]
    obtain ⟨v, hv, h⟩ := bind_okB h
    rw [show ensureSort (pureFns mode env F') env d bt =
      ensureSortCore mode env F' d bt from rfl,
      ensureSortCore_mono hle
        (show ensureSortCore mode env F d bt = .ok v from hv), okB_bind]
    exact h

/-- The λ twin of `annotPwPi_mono`. -/
theorem annotPwLam_mono {env : Env} {F F' : Nat} (hle : F ≤ F')
    {d : Nat} {e : Expr} {pw : PropWhen}
    (h : annotPwLam (pureFns mode env F) env d e = .ok pw) :
    annotPwLam (pureFns mode env F') env d e = .ok pw := by
  revert h
  unfold annotPwLam
  cases proofPW env.find? e with
  | some p => exact id
  | none =>
    dsimp only
    intro h
    obtain ⟨bt, hbt, h⟩ := bind_okB h
    rw [inferTypeIO_def] at hbt
    rw [show ((pureFns mode env F').inferIO d e) =
      inferTypeIO mode env F' d e from rfl,
      inferTypeIO_mono hle hbt, okB_bind]
    obtain ⟨btt, hbtt, h⟩ := bind_okB h
    rw [inferTypeIO_def] at hbtt
    rw [show ((pureFns mode env F').inferIO d bt) =
      inferTypeIO mode env F' d bt from rfl,
      inferTypeIO_mono hle hbtt, okB_bind]
    obtain ⟨v, hv, h⟩ := bind_okB h
    rw [show ensureSort (pureFns mode env F') env d btt =
      ensureSortCore mode env F' d btt from rfl,
      ensureSortCore_mono hle
        (show ensureSortCore mode env F d btt = .ok v from hv), okB_bind]
    exact h

/-- The chained ∀-tail is fuel-monotone (its only knot calls are the
per-level writes). -/
theorem annotatePisWrap_mono {env : Env} {F F' : Nat} (hle : F ≤ F')
    {d : Nat} :
    ∀ (stk : List AnnotBinderEntryX) (j : Nat) (bt res : Expr),
      annotatePisWrap (m := CheckM) (pureFns mode env F) env d stk j bt
        = .ok res →
      annotatePisWrap (m := CheckM) (pureFns mode env F') env d stk j bt
        = .ok res
  | [], _, _, _, h => h
  | (ty', mb) :: rest, j, bt, res, h => by
    rw [annotatePisWrap_cons] at h ⊢
    revert h
    split
    · intro h
      obtain ⟨pw, hpw, h⟩ := bind_okB h
      rw [annotPwPi_mono hle hpw, okB_bind]
      exact annotatePisWrap_mono hle rest (j - 1) _ res h
    · intro h
      exact annotatePisWrap_mono hle rest (j - 1) _ res h

/-- The λ twin of `annotatePisWrap_mono`. -/
theorem annotateLamsWrap_mono {env : Env} {F F' : Nat} (hle : F ≤ F')
    {d : Nat} :
    ∀ (stk : List AnnotBinderEntryX) (j : Nat) (bt res : Expr),
      annotateLamsWrap (m := CheckM) (pureFns mode env F) env d stk j bt
        = .ok res →
      annotateLamsWrap (m := CheckM) (pureFns mode env F') env d stk j bt
        = .ok res
  | [], _, _, _, h => h
  | (ty', mb) :: rest, j, bt, res, h => by
    rw [annotateLamsWrap_cons] at h ⊢
    revert h
    split
    · intro h
      obtain ⟨pw, hpw, h⟩ := bind_okB h
      rw [annotPwLam_mono hle hpw, okB_bind]
      exact annotateLamsWrap_mono hle rest (j - 1) _ res h
    · intro h
      exact annotateLamsWrap_mono hle rest (j - 1) _ res h

/-- The peel's datum, in the form `annotateBindersOut_wrap` consumes. -/
theorem annotatePisPw_inv {env : Env} {F d k : Nat}
    {leaf' : Expr} {pw? : Option PropWhen}
    (h : annotatePisPw (pureFns mode env F) env d k leaf' = .ok pw?) :
    AnnotPwOk (annotPwPi (pureFns mode env F) env (d + k) leaf') pw? := by
  unfold annotatePisPw at h
  revert h
  cases hp : annotPwPi (pureFns mode env F) env (d + k) leaf' with
  | error e => intro h; exact nomatch h
  | ok pw =>
    intro h
    simp only [okB_bind, pure, Except.pure, Except.ok.injEq] at h
    exact (h ▸ (rfl : (Except.ok pw : CheckM PropWhen) = .ok pw))

/-- The λ twin of `annotatePisPw_inv`. -/
theorem annotateLamsPw_inv {env : Env} {F d k : Nat}
    {leaf' : Expr} {pw? : Option PropWhen}
    (h : annotateLamsPw (pureFns mode env F) env d k leaf' = .ok pw?) :
    AnnotPwOk (annotPwLam (pureFns mode env F) env (d + k) leaf') pw? := by
  unfold annotateLamsPw at h
  revert h
  cases hp : annotPwLam (pureFns mode env F) env (d + k) leaf' with
  | error e => intro h; exact nomatch h
  | ok pw =>
    intro h
    simp only [okB_bind, pure, Except.pure, Except.ok.injEq] at h
    exact (h ▸ (rfl : (Except.ok pw : CheckM PropWhen) = .ok pw))

/-- Leaf-phase soundness for the annotate ∀-loop. -/
theorem annotatePisLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List AnnotBinderEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : annotatePisLeaf (pureFns mode env F) env d t k fvs stk = .ok res) :
    ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun leaf' => annotatePisWrap (m := CheckM) (pureFns mode env F')
        env d stk (k - 1) leaf')
        = .ok res := by
  unfold annotatePisLeaf at hrun
  obtain ⟨leaf', hleaf, hrun⟩ := bind_okB hrun
  rw [annotate_def] at hleaf
  obtain ⟨pw?, hpw?, hrun⟩ := bind_okB hrun
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold annotateBindersOut at hrun
    rw [abstractRange_zero] at hrun
    exact ⟨F, by rw [hleaf, okB_bind]; exact hrun⟩
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    refine ⟨F, ?_⟩
    rw [hleaf, okB_bind]
    rw [← annotateBindersOut_wrap (mk := fun ty b mb => .forallE ty b mb)
      (fun ty b bi d k c => rfl)
      (fun e => typeSortPW env.find? e)
      (fun D e => annotPwPi (pureFns mode env F) env D e)
      (fun ty b mb => rfl)
      (fun D e p hp => by unfold annotPwPi; rw [hp])
      (annotatePisWrap (m := CheckM) (pureFns mode env F) env d)
      (fun j bt => rfl)
      (fun ty' mb rest j bt => annotatePisWrap_cons _ _ _ _ _ _ _ _)
      (e :: rest) (k - 1) leaf' pw?
      (by simp only [List.length_cons] at hlen ⊢; omega)
      (by rw [show d + (k - 1) + 1 = d + k from by omega]
          exact annotatePisPw_inv hpw?)]
    rw [hkeq]
    exact hrun

/-- A successful annotate-∀-peel run is reproduced by the chained
annotation of the bulk-opened residual followed by the (pure) tails. -/
theorem annotatePis_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      annotatePis (pureFns mode env F) env d fuel t k fvs stk = .ok res →
      ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun leaf' => annotatePisWrap (m := CheckM) (pureFns mode env F')
          env d stk (k - 1) leaf')
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [annotatePis_zero] at hrun
    exact annotatePisLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hpi : ∃ ty body mb, t = Expr.forallE ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hpi
      rw [annotatePis_succ_pi] at hrun
      obtain ⟨ty', hty', hrun⟩ := bind_okB hrun
      rw [annotate_def] at hty'
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨leaf', hleaf, hwrap⟩ := bind_okB hchain
      have hpiL : (Expr.forallE ty body mb).instantiateList fvs
          = Expr.forallE (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hpiL, annotateCore_forallE_eq]
      rw [annotateCore_mono (Nat.le_max_left F F') hty', okB_bind]
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) ty')
          = body.instantiateList (Expr.fvar (d + k) ty' :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [annotateCore_mono (Nat.le_max_right F F') hleaf, okB_bind]
      -- task #161 P5: the tail's own write at this level.  `hwrap`
      -- already ran it at fuel `F'`; both it and the continuation lift
      -- to the ambient fuel by monotonicity.
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      rw [annotatePisWrap_cons] at hwrap
      revert hwrap
      split
      · intro hwrap
        obtain ⟨pw, hpw, hwrap⟩ := bind_okB hwrap
        rw [show d + k + 1 = d + (k + 1) from by omega] at hpw
        rw [annotPwPi_mono (Nat.le_max_right F F') hpw, okB_bind]
        exact annotatePisWrap_mono
          (Nat.le_succ_of_le (Nat.le_max_right F F')) _ _ _ _ hwrap
      · intro hwrap
        exact annotatePisWrap_mono
          (Nat.le_succ_of_le (Nat.le_max_right F F')) _ _ _ _ hwrap
    · have ht : ∀ ty body mb, t ≠ Expr.forallE ty body mb :=
        fun ty b mb hh => hpi ⟨ty, b, mb, hh⟩
      rw [annotatePis_succ_ne_pi _ ht] at hrun
      exact annotatePisLeaf_sound hlen hrun

/-- Leaf-phase soundness for the annotate λ-loop. -/
theorem annotateLamsLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List AnnotBinderEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : annotateLamsLeaf (pureFns mode env F) env d t k fvs stk = .ok res) :
    ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun leaf' => annotateLamsWrap (m := CheckM) (pureFns mode env F')
        env d stk (k - 1) leaf')
        = .ok res := by
  unfold annotateLamsLeaf at hrun
  obtain ⟨leaf', hleaf, hrun⟩ := bind_okB hrun
  rw [annotate_def] at hleaf
  obtain ⟨pw?, hpw?, hrun⟩ := bind_okB hrun
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold annotateBindersOut at hrun
    rw [abstractRange_zero] at hrun
    exact ⟨F, by rw [hleaf, okB_bind]; exact hrun⟩
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    refine ⟨F, ?_⟩
    rw [hleaf, okB_bind]
    rw [← annotateBindersOut_wrap (mk := fun ty b mb => .lam ty b mb)
      (fun ty b bi d k c => rfl)
      (fun e => proofPW env.find? e)
      (fun D e => annotPwLam (pureFns mode env F) env D e)
      (fun ty b mb => rfl)
      (fun D e p hp => by unfold annotPwLam; rw [hp])
      (annotateLamsWrap (m := CheckM) (pureFns mode env F) env d)
      (fun j bt => rfl)
      (fun ty' mb rest j bt => annotateLamsWrap_cons _ _ _ _ _ _ _ _)
      (e :: rest) (k - 1) leaf' pw?
      (by simp only [List.length_cons] at hlen ⊢; omega)
      (by rw [show d + (k - 1) + 1 = d + k from by omega]
          exact annotateLamsPw_inv hpw?)]
    rw [hkeq]
    exact hrun

/-- A successful annotate-λ-peel run is reproduced by the chained
annotation of the bulk-opened residual followed by the (pure) tails. -/
theorem annotateLams_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      annotateLams (pureFns mode env F) env d fuel t k fvs stk = .ok res →
      ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun leaf' => annotateLamsWrap (m := CheckM) (pureFns mode env F')
          env d stk (k - 1) leaf')
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [annotateLams_zero] at hrun
    exact annotateLamsLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [annotateLams_succ_lam] at hrun
      obtain ⟨ty', hty', hrun⟩ := bind_okB hrun
      rw [annotate_def] at hty'
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨leaf', hleaf, hwrap⟩ := bind_okB hchain
      have hlamL : (Expr.lam ty body mb).instantiateList fvs
          = Expr.lam (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hlamL, annotateCore_lam_eq]
      rw [annotateCore_mono (Nat.le_max_left F F') hty', okB_bind]
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) ty')
          = body.instantiateList (Expr.fvar (d + k) ty' :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [annotateCore_mono (Nat.le_max_right F F') hleaf, okB_bind]
      -- task #161 P5: the tail's own write at this level.  `hwrap`
      -- already ran it at fuel `F'`; both it and the continuation lift
      -- to the ambient fuel by monotonicity.
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      rw [annotateLamsWrap_cons] at hwrap
      revert hwrap
      split
      · intro hwrap
        obtain ⟨pw, hpw, hwrap⟩ := bind_okB hwrap
        rw [show d + k + 1 = d + (k + 1) from by omega] at hpw
        rw [annotPwLam_mono (Nat.le_max_right F F') hpw, okB_bind]
        exact annotateLamsWrap_mono
          (Nat.le_succ_of_le (Nat.le_max_right F F')) _ _ _ _ hwrap
      · intro hwrap
        exact annotateLamsWrap_mono
          (Nat.le_succ_of_le (Nat.le_max_right F F')) _ _ _ _ hwrap
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [annotateLams_succ_ne_lam _ ht] at hrun
      exact annotateLamsLeaf_sound hlen hrun

end AnnotSound

end ConLeche
