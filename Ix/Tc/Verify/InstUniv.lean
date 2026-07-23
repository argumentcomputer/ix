import Ix.Tc.Verify.Subst
import Ix.Tc.Verify.Monad
import Ix.Tc.Verify.Level

/-!
# `instantiateUnivParams` memo-soundness

The last of the five expression walkers: universe-parameter substitution
with per-call address-keyed memoization (`TcM.instUnivInner`,
`Ix/Tc/Monad.lean`). Unlike the four `WalkM` siblings this one runs over
`TcM` — `StateT (HashMap Address (KExpr m)) (TcM m)` — so its soundness
statement is the first composition of the walker kit with the EStateM
Hoare kernel (`TcM.WF`): the intern table lives inside `TcState.env`,
results are interned via `TcM.intern`, and level substitution can THROW
(`univParamOutOfRange`), so the run has genuine error outcomes.

Structural differences from the `WalkM` walkers:
- the memo key is the bare address (`us` is fixed for the whole call and
  universe substitution never changes binder structure — no depth in the
  key), so the scratch invariant drops the depth index;
- there is no `lbr` fast path: every subterm is visited, so no
  `Constructed`/no-wrap side conditions are needed anywhere;
- the pure spec is `Except`-valued (mirroring `substUniv`'s
  defense-in-depth range check). The master states partial correctness:
  on success the result is the spec value; on error only the state
  invariants and the frame are claimed (consumers validate arity at
  const-infer time, so the error branch is dead in well-formed use).

Scope: anon mode, matching the sibling masters (`internKey = addr`,
`eraseMeta = id`, exact spec equality).
-/

namespace Ix.Tc

open Std (HashMap)
open EStateM (Result)
open Lean4Lean (VLevel)

/-! ### The pure spec -/

namespace KExpr

/-- Pure, memo-free, intern-free universe instantiation: `substUniv` at
    every level position, rebuilt with the smart constructors — mirrors
    the rebuild arms of `TcM.instUnivInner` exactly. `Except`-valued: an
    out-of-range `param` surfaces `univParamOutOfRange` (the walker's
    `TcM.ofExcept` throw). -/
def instUnivSpec (e : KExpr .anon) (us : Array (KUniv .anon)) :
    Except (TcError .anon) (KExpr .anon) :=
  match e with
  | .sort u _ => return mkSort (← TcM.substUniv u us)
  | .const id curUs _ =>
    return mkConst id (← curUs.mapM (TcM.substUniv · us))
  | .app f a _ => return mkApp (← instUnivSpec f us) (← instUnivSpec a us)
  | .lam n bi ty body _ =>
    return mkLam n bi (← instUnivSpec ty us) (← instUnivSpec body us)
  | .all n bi ty body _ =>
    return mkAll n bi (← instUnivSpec ty us) (← instUnivSpec body us)
  | .letE n ty val body nd _ =>
    return mkLet n (← instUnivSpec ty us) (← instUnivSpec val us)
      (← instUnivSpec body us) nd
  | .prj id field val _ => return mkPrj id field (← instUnivSpec val us)
  | e => .ok e
termination_by structural e

/-- Spec partner of `TcM.instantiateUnivParams`. The `us.isEmpty` fast
    path returns the expression untouched WITHOUT the range check (a
    parameter-free constant's body mentions no `param`s in well-formed
    environments; the defense-in-depth check is skipped on this path in
    production and Rust alike). -/
def instantiateUnivParamsSpec (e : KExpr .anon)
    (us : Array (KUniv .anon)) : Except (TcError .anon) (KExpr .anon) :=
  if us.isEmpty then .ok e else instUnivSpec e us

/-- Reach set of the walk on `e`: the nodes whose addresses can be
    memo-keyed (every subterm — there is no fast path) plus the rebuilt
    spec images (the intern candidates). Spec-determined and finite —
    never closed under constructors (that would be pigeonhole-false). -/
def InstUnivReach (us : Array (KUniv .anon)) :
    KExpr .anon → KExpr .anon → Prop
  | e, x =>
    x = e ∨ instUnivSpec e us = .ok x ∨
      match e with
      | .app f a _ => InstUnivReach us f x ∨ InstUnivReach us a x
      | .lam _ _ ty body _ =>
        InstUnivReach us ty x ∨ InstUnivReach us body x
      | .all _ _ ty body _ =>
        InstUnivReach us ty x ∨ InstUnivReach us body x
      | .letE _ ty val body _ _ =>
        InstUnivReach us ty x ∨ InstUnivReach us val x ∨
          InstUnivReach us body x
      | .prj _ _ val _ => InstUnivReach us val x
      | _ => False

theorem InstUnivReach.self (us : Array (KUniv .anon)) (e : KExpr .anon) :
    InstUnivReach us e e := by
  cases e <;> exact .inl rfl

theorem InstUnivReach.spec {us : Array (KUniv .anon)} {e r : KExpr .anon}
    (h : instUnivSpec e us = .ok r) : InstUnivReach us e r := by
  cases e <;> exact .inr (.inl h)

end KExpr

/-! ### Scratch, state invariant, frame -/

/-- Memo-map invariant: every entry is the successful spec image of a
    support witness stored at its own address. A hit at `e.addr` then
    converts to the spec image of `e` itself via collision-freedom. -/
def InstUnivScratchInv (S : KExpr .anon → Prop) (us : Array (KUniv .anon))
    (sc : HashMap Address (KExpr .anon)) : Prop :=
  ∀ (a : Address) (r : KExpr .anon), sc[a]? = some r →
    ∃ w, S w ∧ w.addr = a ∧ KExpr.instUnivSpec w us = .ok r

theorem InstUnivScratchInv.empty (S : KExpr .anon → Prop)
    (us : Array (KUniv .anon)) : InstUnivScratchInv S us {} := by
  intro a r hr
  simp at hr

theorem InstUnivScratchInv.insert {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} {sc : HashMap Address (KExpr .anon)}
    (hsc : InstUnivScratchInv S us sc) {e r : KExpr .anon}
    (hSe : S e) (hr : KExpr.instUnivSpec e us = .ok r) :
    InstUnivScratchInv S us (sc.insert e.addr r) := by
  intro a v hv
  rw [Std.HashMap.getElem?_insert] at hv
  split at hv
  · next hbeq =>
    cases hv
    cases eq_of_beq hbeq
    exact ⟨e, hSe, rfl, hr⟩
  · exact hsc _ _ hv

/-- Intern-side invariant plus the frame: the table is key-coherent with
    support inside `S`, and the rest of the checker state is untouched
    relative to the entry state `s₀` — the walker writes exactly
    `env.intern` (and the `StateT` memo layer, which is not part of
    `TcState`). -/
def InstUnivStateOK (S : KExpr .anon → Prop) (s₀ s : TcState .anon) :
    Prop :=
  s.env.intern.WF ∧ (∀ x, s.env.intern.ExprSupport x → S x) ∧
    s = { s₀ with env := { s₀.env with intern := s.env.intern } }

theorem InstUnivStateOK.refl {S : KExpr .anon → Prop} {s : TcState .anon}
    (hwf : s.env.intern.WF) (hsup : ∀ x, s.env.intern.ExprSupport x → S x) :
    InstUnivStateOK S s s :=
  ⟨hwf, hsup, rfl⟩

theorem InstUnivStateOK.trans {S : KExpr .anon → Prop}
    {s₀ s₁ s₂ : TcState .anon} (h₁ : InstUnivStateOK S s₀ s₁)
    (h₂ : InstUnivStateOK S s₁ s₂) : InstUnivStateOK S s₀ s₂ := by
  refine ⟨h₂.1, h₂.2.1, ?_⟩
  rw [h₂.2.2, h₁.2.2]

/-! ### The post-relation -/

/-- What a finished walker run means, on both outcomes: on success the
    result is the spec value and every threaded invariant survives; on
    error the state invariants and the frame still hold (EStateM is
    non-backtracking — the partially extended intern table survives the
    throw, and it is still key-coherent inside `S`). -/
def InstUnivPost (S : KExpr .anon → Prop) (us : Array (KUniv .anon))
    (e : KExpr .anon) (s₀ : TcState .anon)
    (out : Result (TcError .anon) (TcState .anon)
      (KExpr .anon × HashMap Address (KExpr .anon))) : Prop :=
  match out with
  | .ok (r, sc') s' =>
    KExpr.instUnivSpec e us = .ok r ∧ InstUnivStateOK S s₀ s' ∧
      InstUnivScratchInv S us sc'
  | .error _ s' => InstUnivStateOK S s₀ s'

/-! ### The run-equation kit

`StateT (HashMap Address (KExpr .anon)) (TcM .anon)` runs are functions
`sc → s → Result`; each combinator's applied form reduces by `rfl` (or a
`cases` on the scrutinee). Same discipline as the `WalkM` kit in
`Verify/Subst.lean`, one monad layer richer. -/

section RunKit

variable {α β : Type} {sc : HashMap Address (KExpr .anon)}
  {s : TcState .anon}

private theorem run_pure_bind (a : α)
    (k : α → StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (pure a >>= k) sc s = k a sc s := rfl

private theorem run_pure (a : α) :
    (pure a : StateT (HashMap Address (KExpr .anon)) (TcM .anon) α) sc s =
      .ok (a, sc) s := rfl

private theorem run_get_bind
    (k : HashMap Address (KExpr .anon) →
      StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (get >>= k) sc s = k sc sc s := rfl

private theorem run_modify_bind
    (g : HashMap Address (KExpr .anon) → HashMap Address (KExpr .anon))
    (k : PUnit → StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (modify g >>= k) sc s = k ⟨⟩ (g sc) s := rfl

/-- The generic bind splitter: expose the head computation's `Result`
    so a `cases hrec : x sc s` can drive the continuation. -/
private theorem run_bind
    (x : StateT (HashMap Address (KExpr .anon)) (TcM .anon) α)
    (k : α → StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (x >>= k) sc s = match x sc s with
      | .ok a s' => k a.1 a.2 s'
      | .error e s' => .error e s' := by
  show EStateM.bind (x sc) _ s = _
  unfold EStateM.bind
  cases x sc s with
  | ok v s' =>
    obtain ⟨a, sc'⟩ := v
    rfl
  | error e s' => rfl

private theorem run_liftM_ofExcept_bind (x : Except (TcError .anon) α)
    (k : α → StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (liftM (TcM.ofExcept x) >>= k) sc s = match x with
      | .ok a => k a sc s
      | .error e => .error e s := by
  cases x <;> rfl

private theorem run_liftM_intern_bind (e : KExpr .anon)
    (k : KExpr .anon →
      StateT (HashMap Address (KExpr .anon)) (TcM .anon) β) :
    (liftM (TcM.intern e) >>= k) sc s =
      k (s.env.intern.internExpr e).1 sc
        { s with env :=
          { s.env with intern := (s.env.intern.internExpr e).2 } } := rfl

/-- `StateT.run'` from an empty scratch, at the `Result` level. -/
private theorem run_run'
    (x : StateT (HashMap Address (KExpr .anon)) (TcM .anon) α) :
    (x.run' {}) s = match x {} s with
      | .ok a s' => .ok a.1 s'
      | .error e s' => .error e s' := by
  show EStateM.map _ _ s = _
  unfold EStateM.map
  cases x {} s with
  | ok v s' => rfl
  | error e s' => rfl

end RunKit

/-! ### The `const`-arm loop bridge

The elaborated `for u in curUs do newUs := newUs.push (← ofExcept …)`
loop, run against `(sc, s)`, computes exactly the pure `Except`-valued
`mapM` — the loop body is stateless (it can only throw), so neither the
memo scratch nor the checker state moves. -/

private theorem run_substUnivLoop (us : Array (KUniv .anon)) :
    ∀ (l : List (KUniv .anon)) (acc : Array (KUniv .anon))
      (sc : HashMap Address (KExpr .anon)) (s : TcState .anon),
      (forIn (m := StateT (HashMap Address (KExpr .anon)) (TcM .anon))
        l acc (fun u r => do
          let v ← liftM (TcM.ofExcept (TcM.substUniv u us))
          pure PUnit.unit
          pure (ForInStep.yield (r.push v)))) sc s
      = match l.foldlM (fun bs u => bs.push <$> TcM.substUniv u us) acc with
        | .ok arr => .ok (arr, sc) s
        | .error err => .error err s
  | [], acc, sc, s => by
    rw [List.forIn_nil, List.foldlM_nil]
    rfl
  | u :: l, acc, sc, s => by
    rw [List.forIn_cons, List.foldlM_cons]
    rw [run_bind]
    have hbody : (do
        let v ← liftM (TcM.ofExcept (TcM.substUniv u us))
        pure PUnit.unit
        pure (ForInStep.yield (acc.push v)) :
        StateT (HashMap Address (KExpr .anon)) (TcM .anon) _) sc s
        = match TcM.substUniv u us with
          | .ok v => .ok (ForInStep.yield (acc.push v), sc) s
          | .error err => .error err s := by
      rw [run_liftM_ofExcept_bind]
      cases TcM.substUniv u us <;> rfl
    rw [hbody]
    cases hu : TcM.substUniv u us with
    | ok v =>
      simp only []
      rw [run_substUnivLoop us l (acc.push v) sc s]
      rfl
    | error err => rfl

/-- The array-level corollary in the exact shape the walker's `const`
    arm exposes. -/
private theorem run_substUnivLoopArray (us curUs : Array (KUniv .anon))
    (sc : HashMap Address (KExpr .anon)) (s : TcState .anon) :
    (forIn (m := StateT (HashMap Address (KExpr .anon)) (TcM .anon))
      curUs (Array.mkEmpty curUs.size) (fun u r => do
        let v ← liftM (TcM.ofExcept (TcM.substUniv u us))
        pure PUnit.unit
        pure (ForInStep.yield (r.push v)))) sc s
    = match curUs.mapM (TcM.substUniv · us) with
      | .ok arr => .ok (arr, sc) s
      | .error err => .error err s := by
  rw [← Array.forIn_toList, run_substUnivLoop us curUs.toList]
  rw [Array.mapM_eq_foldlM, ← Array.foldlM_toList]
  rfl

/-! ### Tail helpers -/

/-- Memo hit: the stored entry converts to the spec image of the current
    node via collision-freedom on the support. -/
private theorem instUnivPost_hit {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} {e r : KExpr .anon}
    {sc : HashMap Address (KExpr .anon)} {s : TcState .anon}
    (hcf : KExpr.CollisionFree S) (hSe : S e)
    (hget : sc[e.addr]? = some r)
    (hwf : s.env.intern.WF)
    (hsup : ∀ x, s.env.intern.ExprSupport x → S x)
    (hsc : InstUnivScratchInv S us sc) :
    InstUnivPost S us e s (.ok (r, sc) s) := by
  refine ⟨?_, .refl hwf hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hwspec⟩ := hsc _ _ hget
  have hwe : w = e := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  rw [← hwe]
  exact hwspec

/-- Pass-through store: memoize the node itself and return it,
    un-interned (the `var`/`fvar`/`nat`/`str` arms). -/
private theorem instUnivPost_store_self {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} {e : KExpr .anon}
    {sc : HashMap Address (KExpr .anon)} {s : TcState .anon}
    (hspec : KExpr.instUnivSpec e us = .ok e) (hSe : S e)
    (hwf : s.env.intern.WF)
    (hsup : ∀ x, s.env.intern.ExprSupport x → S x)
    (hsc : InstUnivScratchInv S us sc) :
    InstUnivPost S us e s (.ok (e, sc.insert e.addr e) s) :=
  ⟨hspec, .refl hwf hsup, hsc.insert hSe hspec⟩

/-- Rebuild tail (the intern-then-memoize join point): from any
    mid-walk state `s₁` reached from `s₀`, interning the rebuilt
    candidate and memoizing the canonical result lands in the post. -/
private theorem instUnivPost_jp {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} {e cand : KExpr .anon}
    {sc₁ : HashMap Address (KExpr .anon)} {s₀ s₁ : TcState .anon}
    (hcf : KExpr.CollisionFree S)
    (hok : InstUnivStateOK S s₀ s₁)
    (hsc : InstUnivScratchInv S us sc₁)
    (hSe : S e) (hScand : S cand)
    (hcand : KExpr.instUnivSpec e us = .ok cand) :
    InstUnivPost S us e s₀
      (.ok ((s₁.env.intern.internExpr cand).1,
          sc₁.insert e.addr (s₁.env.intern.internExpr cand).1)
        { s₁ with env :=
          { s₁.env with intern := (s₁.env.intern.internExpr cand).2 } }) := by
  obtain ⟨hwf, hsup, hframe⟩ := hok
  have hkcf : KExpr.KeyCollisionFree
      (fun v => s₁.env.intern.ExprSupport v ∨ v = cand) :=
    KExpr.keyCollisionFree_anon.mpr
      (hcf.mono fun x hx => hx.elim (hsup x) fun hxe => hxe ▸ hScand)
  have hcanon : (s₁.env.intern.internExpr cand).1 = cand := by
    have h := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  refine ⟨by rw [hcanon]; exact hcand, ?_,
    hsc.insert hSe (by rw [hcanon]; exact hcand)⟩
  refine InstUnivStateOK.trans ⟨hwf, hsup, hframe⟩
    ⟨hwf.internExpr cand, ?_, rfl⟩
  intro x hx
  rcases InternTable.ExprSupport.of_internExpr hx with h | h
  · exact hsup x h
  · exact h ▸ hScand

/-! ### The master theorem -/

/-- **Memo-soundness for `instUnivInner`**: under collision-freedom of an
    abstract support `S` covering `InstUnivReach ∪ intern-support`, the
    memoized, interning, throwing walker satisfies `InstUnivPost` — on
    success it computes exactly the pure `Except` spec; on either outcome
    the intern table stays key-coherent inside `S` and everything outside
    `env.intern` is frame-preserved. -/
theorem TcM.instUnivInner_spec {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} (hcf : KExpr.CollisionFree S) :
    ∀ {e : KExpr .anon} {sc : HashMap Address (KExpr .anon)}
      {s : TcState .anon},
      (∀ x, KExpr.InstUnivReach us e x → S x) →
      s.env.intern.WF → (∀ x, s.env.intern.ExprSupport x → S x) →
      InstUnivScratchInv S us sc →
      InstUnivPost S us e s (TcM.instUnivInner e us sc s) := by
  intro e
  induction e with
  | var idx name info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.var idx name info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.var idx name info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have hrun : TcM.instUnivInner (KExpr.var idx name info) us sc s
          = .ok (KExpr.var idx name info,
              sc.insert (KExpr.var idx name info).addr
                (KExpr.var idx name info)) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        try rfl
      rw [hrun]
      exact instUnivPost_store_self rfl (hreach _ (.self ..)) hwf hsup hsc
  | fvar id name info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.fvar id name info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.fvar id name info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have hrun : TcM.instUnivInner (KExpr.fvar id name info) us sc s
          = .ok (KExpr.fvar id name info,
              sc.insert (KExpr.fvar id name info).addr
                (KExpr.fvar id name info)) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        try rfl
      rw [hrun]
      exact instUnivPost_store_self rfl (hreach _ (.self ..)) hwf hsup hsc
  | nat v blob info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.nat v blob info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.nat v blob info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have hrun : TcM.instUnivInner (KExpr.nat v blob info) us sc s
          = .ok (KExpr.nat v blob info,
              sc.insert (KExpr.nat v blob info).addr
                (KExpr.nat v blob info)) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        try rfl
      rw [hrun]
      exact instUnivPost_store_self rfl (hreach _ (.self ..)) hwf hsup hsc
  | str v blob info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.str v blob info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.str v blob info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have hrun : TcM.instUnivInner (KExpr.str v blob info) us sc s
          = .ok (KExpr.str v blob info,
              sc.insert (KExpr.str v blob info).addr
                (KExpr.str v blob info)) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        try rfl
      rw [hrun]
      exact instUnivPost_store_self rfl (hreach _ (.self ..)) hwf hsup hsc
  | sort u info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.sort u info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.sort u info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      cases hu : TcM.substUniv u us with
      | error err =>
        have hrun : TcM.instUnivInner (KExpr.sort u info) us sc s
            = .error err s := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_liftM_ofExcept_bind, hu]
          try rfl
        rw [hrun]
        exact .refl hwf hsup
      | ok v =>
        have hrun : TcM.instUnivInner (KExpr.sort u info) us sc s
            = .ok ((s.env.intern.internExpr (KExpr.mkSort v)).1,
                sc.insert (KExpr.sort u info).addr
                  (s.env.intern.internExpr (KExpr.mkSort v)).1)
              { s with env := { s.env with
                  intern := (s.env.intern.internExpr (KExpr.mkSort v)).2 } } := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_liftM_ofExcept_bind, hu]
          try rfl
        have hspec : KExpr.instUnivSpec (KExpr.sort u info) us
            = .ok (KExpr.mkSort v) := by
          rw [KExpr.instUnivSpec, hu]
          try rfl
        rw [hrun]
        exact instUnivPost_jp hcf (.refl hwf hsup) hsc
          (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | const id curUs info =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.const id curUs info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.const id curUs info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      cases hmus : curUs.mapM (TcM.substUniv · us) with
      | error err =>
        have hrun : TcM.instUnivInner (KExpr.const id curUs info) us sc s
            = .error err s := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, run_substUnivLoopArray, hmus]
          try rfl
        rw [hrun]
        exact .refl hwf hsup
      | ok arr =>
        have hrun : TcM.instUnivInner (KExpr.const id curUs info) us sc s
            = .ok ((s.env.intern.internExpr (KExpr.mkConst id arr)).1,
                sc.insert (KExpr.const id curUs info).addr
                  (s.env.intern.internExpr (KExpr.mkConst id arr)).1)
              { s with env := { s.env with
                  intern := (s.env.intern.internExpr (KExpr.mkConst id arr)).2 } } := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, run_substUnivLoopArray, hmus]
          try rfl
        have hspec : KExpr.instUnivSpec (KExpr.const id curUs info) us
            = .ok (KExpr.mkConst id arr) := by
          rw [KExpr.instUnivSpec, hmus]
          try rfl
        rw [hrun]
        exact instUnivPost_jp hcf (.refl hwf hsup) hsc
          (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | app f a info ihf iha =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.app f a info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.app f a info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have postf := ihf (sc := sc) (s := s)
        (fun x hx => hreach x (.inr (.inr (.inl hx)))) hwf hsup hsc
      cases hrecf : TcM.instUnivInner f us sc s with
      | error err sf =>
        rw [hrecf] at postf
        have hrun : TcM.instUnivInner (KExpr.app f a info) us sc s
            = .error err sf := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecf]
          try rfl
        rw [hrun]
        exact postf
      | ok vf sf =>
        obtain ⟨rf, scf⟩ := vf
        rw [hrecf] at postf
        obtain ⟨hspecf, hokf, hscf⟩ := postf
        have posta := iha (sc := scf) (s := sf)
          (fun x hx => hreach x (.inr (.inr (.inr hx)))) hokf.1 hokf.2.1 hscf
        cases hreca : TcM.instUnivInner a us scf sf with
        | error err sa =>
          rw [hreca] at posta
          have hrun : TcM.instUnivInner (KExpr.app f a info) us sc s
              = .error err sa := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecf]
            try simp only []
            rw [run_bind, hreca]
            try rfl
          rw [hrun]
          exact hokf.trans posta
        | ok va sa =>
          obtain ⟨ra, sca⟩ := va
          rw [hreca] at posta
          obtain ⟨hspeca, hoka, hsca⟩ := posta
          have hrun : TcM.instUnivInner (KExpr.app f a info) us sc s
              = .ok ((sa.env.intern.internExpr (KExpr.mkApp rf ra)).1,
                  sca.insert (KExpr.app f a info).addr
                    (sa.env.intern.internExpr (KExpr.mkApp rf ra)).1)
                { sa with env := { sa.env with
                    intern := (sa.env.intern.internExpr (KExpr.mkApp rf ra)).2 } } := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecf]
            try simp only []
            rw [run_bind, hreca]
            try rfl
          have hspec : KExpr.instUnivSpec (KExpr.app f a info) us
              = .ok (KExpr.mkApp rf ra) := by
            rw [KExpr.instUnivSpec, hspecf]
            try simp only []
            rw [hspeca]
            try rfl
          rw [hrun]
          exact instUnivPost_jp hcf (hokf.trans hoka) hsca
            (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | lam n bi ty body info ihty ihbody =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.lam n bi ty body info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.lam n bi ty body info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have postty := ihty (sc := sc) (s := s)
        (fun x hx => hreach x (.inr (.inr (.inl hx)))) hwf hsup hsc
      cases hrecty : TcM.instUnivInner ty us sc s with
      | error err st =>
        rw [hrecty] at postty
        have hrun : TcM.instUnivInner (KExpr.lam n bi ty body info) us sc s
            = .error err st := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecty]
          try rfl
        rw [hrun]
        exact postty
      | ok vt st =>
        obtain ⟨rt, sct⟩ := vt
        rw [hrecty] at postty
        obtain ⟨hspect, hokt, hsct⟩ := postty
        have postbody := ihbody (sc := sct) (s := st)
          (fun x hx => hreach x (.inr (.inr (.inr hx)))) hokt.1 hokt.2.1 hsct
        cases hrecbody : TcM.instUnivInner body us sct st with
        | error err sb =>
          rw [hrecbody] at postbody
          have hrun : TcM.instUnivInner (KExpr.lam n bi ty body info) us sc s
              = .error err sb := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecty]
            try simp only []
            rw [run_bind, hrecbody]
            try rfl
          rw [hrun]
          exact hokt.trans postbody
        | ok vb sb =>
          obtain ⟨rb, scb⟩ := vb
          rw [hrecbody] at postbody
          obtain ⟨hspecb, hokb, hscb⟩ := postbody
          have hrun : TcM.instUnivInner (KExpr.lam n bi ty body info) us sc s
              = .ok ((sb.env.intern.internExpr (KExpr.mkLam n bi rt rb)).1,
                  scb.insert (KExpr.lam n bi ty body info).addr
                    (sb.env.intern.internExpr (KExpr.mkLam n bi rt rb)).1)
                { sb with env := { sb.env with
                    intern := (sb.env.intern.internExpr (KExpr.mkLam n bi rt rb)).2 } } := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecty]
            try simp only []
            rw [run_bind, hrecbody]
            try rfl
          have hspec : KExpr.instUnivSpec (KExpr.lam n bi ty body info) us
              = .ok (KExpr.mkLam n bi rt rb) := by
            rw [KExpr.instUnivSpec, hspect]
            try simp only []
            rw [hspecb]
            try rfl
          rw [hrun]
          exact instUnivPost_jp hcf (hokt.trans hokb) hscb
            (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | all n bi ty body info ihty ihbody =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.all n bi ty body info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.all n bi ty body info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have postty := ihty (sc := sc) (s := s)
        (fun x hx => hreach x (.inr (.inr (.inl hx)))) hwf hsup hsc
      cases hrecty : TcM.instUnivInner ty us sc s with
      | error err st =>
        rw [hrecty] at postty
        have hrun : TcM.instUnivInner (KExpr.all n bi ty body info) us sc s
            = .error err st := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecty]
          try rfl
        rw [hrun]
        exact postty
      | ok vt st =>
        obtain ⟨rt, sct⟩ := vt
        rw [hrecty] at postty
        obtain ⟨hspect, hokt, hsct⟩ := postty
        have postbody := ihbody (sc := sct) (s := st)
          (fun x hx => hreach x (.inr (.inr (.inr hx)))) hokt.1 hokt.2.1 hsct
        cases hrecbody : TcM.instUnivInner body us sct st with
        | error err sb =>
          rw [hrecbody] at postbody
          have hrun : TcM.instUnivInner (KExpr.all n bi ty body info) us sc s
              = .error err sb := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecty]
            try simp only []
            rw [run_bind, hrecbody]
            try rfl
          rw [hrun]
          exact hokt.trans postbody
        | ok vb sb =>
          obtain ⟨rb, scb⟩ := vb
          rw [hrecbody] at postbody
          obtain ⟨hspecb, hokb, hscb⟩ := postbody
          have hrun : TcM.instUnivInner (KExpr.all n bi ty body info) us sc s
              = .ok ((sb.env.intern.internExpr (KExpr.mkAll n bi rt rb)).1,
                  scb.insert (KExpr.all n bi ty body info).addr
                    (sb.env.intern.internExpr (KExpr.mkAll n bi rt rb)).1)
                { sb with env := { sb.env with
                    intern := (sb.env.intern.internExpr (KExpr.mkAll n bi rt rb)).2 } } := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecty]
            try simp only []
            rw [run_bind, hrecbody]
            try rfl
          have hspec : KExpr.instUnivSpec (KExpr.all n bi ty body info) us
              = .ok (KExpr.mkAll n bi rt rb) := by
            rw [KExpr.instUnivSpec, hspect]
            try simp only []
            rw [hspecb]
            try rfl
          rw [hrun]
          exact instUnivPost_jp hcf (hokt.trans hokb) hscb
            (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | letE n ty val body nd info ihty ihval ihbody =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.letE n ty val body nd info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.letE n ty val body nd info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have postty := ihty (sc := sc) (s := s)
        (fun x hx => hreach x (.inr (.inr (.inl hx)))) hwf hsup hsc
      cases hrecty : TcM.instUnivInner ty us sc s with
      | error err st =>
        rw [hrecty] at postty
        have hrun : TcM.instUnivInner (KExpr.letE n ty val body nd info) us sc s
            = .error err st := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecty]
          try rfl
        rw [hrun]
        exact postty
      | ok vt st =>
        obtain ⟨rt, sct⟩ := vt
        rw [hrecty] at postty
        obtain ⟨hspect, hokt, hsct⟩ := postty
        have postval := ihval (sc := sct) (s := st)
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          hokt.1 hokt.2.1 hsct
        cases hrecval : TcM.instUnivInner val us sct st with
        | error err sv =>
          rw [hrecval] at postval
          have hrun : TcM.instUnivInner (KExpr.letE n ty val body nd info) us sc s
              = .error err sv := by
            rw [TcM.instUnivInner, run_get_bind, hget]
            simp (config := { proj := false }) only []
            rw [run_pure_bind, run_bind, hrecty]
            try simp only []
            rw [run_bind, hrecval]
            try rfl
          rw [hrun]
          exact hokt.trans postval
        | ok vv sv =>
          obtain ⟨rv, scv⟩ := vv
          rw [hrecval] at postval
          obtain ⟨hspecv, hokv, hscv⟩ := postval
          have postbody := ihbody (sc := scv) (s := sv)
            (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
            hokv.1 hokv.2.1 hscv
          cases hrecbody : TcM.instUnivInner body us scv sv with
          | error err sb =>
            rw [hrecbody] at postbody
            have hrun : TcM.instUnivInner (KExpr.letE n ty val body nd info) us sc s
                = .error err sb := by
              rw [TcM.instUnivInner, run_get_bind, hget]
              simp (config := { proj := false }) only []
              rw [run_pure_bind, run_bind, hrecty]
              try simp only []
              rw [run_bind, hrecval]
              try simp only []
              rw [run_bind, hrecbody]
              try rfl
            rw [hrun]
            exact (hokt.trans hokv).trans postbody
          | ok vb sb =>
            obtain ⟨rb, scb⟩ := vb
            rw [hrecbody] at postbody
            obtain ⟨hspecb, hokb, hscb⟩ := postbody
            have hrun : TcM.instUnivInner (KExpr.letE n ty val body nd info) us sc s
                = .ok ((sb.env.intern.internExpr (KExpr.mkLet n rt rv rb nd)).1,
                    scb.insert (KExpr.letE n ty val body nd info).addr
                      (sb.env.intern.internExpr (KExpr.mkLet n rt rv rb nd)).1)
                  { sb with env := { sb.env with
                      intern := (sb.env.intern.internExpr (KExpr.mkLet n rt rv rb nd)).2 } } := by
              rw [TcM.instUnivInner, run_get_bind, hget]
              simp (config := { proj := false }) only []
              rw [run_pure_bind, run_bind, hrecty]
              try simp only []
              rw [run_bind, hrecval]
              try simp only []
              rw [run_bind, hrecbody]
              try rfl
            have hspec : KExpr.instUnivSpec (KExpr.letE n ty val body nd info) us
                = .ok (KExpr.mkLet n rt rv rb nd) := by
              rw [KExpr.instUnivSpec, hspect]
              try simp only []
              rw [hspecv]
              try simp only []
              rw [hspecb]
              try rfl
            rw [hrun]
            exact instUnivPost_jp hcf ((hokt.trans hokv).trans hokb) hscb
              (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec
  | prj id field val info ihval =>
    intro sc s hreach hwf hsup hsc
    cases hget : sc[(KExpr.prj id field val info).addr]? with
    | some r =>
      have hrun : TcM.instUnivInner (KExpr.prj id field val info) us sc s
          = .ok (r, sc) s := by
        rw [TcM.instUnivInner, run_get_bind, hget]
        rfl
      rw [hrun]
      exact instUnivPost_hit hcf (hreach _ (.self ..)) hget hwf hsup hsc
    | none =>
      have postval := ihval (sc := sc) (s := s)
        (fun x hx => hreach x (.inr (.inr hx))) hwf hsup hsc
      cases hrecval : TcM.instUnivInner val us sc s with
      | error err sv =>
        rw [hrecval] at postval
        have hrun : TcM.instUnivInner (KExpr.prj id field val info) us sc s
            = .error err sv := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecval]
          try rfl
        rw [hrun]
        exact postval
      | ok vv sv =>
        obtain ⟨rv, scv⟩ := vv
        rw [hrecval] at postval
        obtain ⟨hspecv, hokv, hscv⟩ := postval
        have hrun : TcM.instUnivInner (KExpr.prj id field val info) us sc s
            = .ok ((sv.env.intern.internExpr (KExpr.mkPrj id field rv)).1,
                scv.insert (KExpr.prj id field val info).addr
                  (sv.env.intern.internExpr (KExpr.mkPrj id field rv)).1)
              { sv with env := { sv.env with
                  intern := (sv.env.intern.internExpr (KExpr.mkPrj id field rv)).2 } } := by
          rw [TcM.instUnivInner, run_get_bind, hget]
          simp (config := { proj := false }) only []
          rw [run_pure_bind, run_bind, hrecval]
          try rfl
        have hspec : KExpr.instUnivSpec (KExpr.prj id field val info) us
            = .ok (KExpr.mkPrj id field rv) := by
          rw [KExpr.instUnivSpec, hspecv]
          try rfl
        rw [hrun]
        exact instUnivPost_jp hcf hokv hscv
          (hreach _ (.self ..)) (hreach _ (.spec hspec)) hspec

/-! ### The Hoare-triple interface -/

/-- **`instantiateUnivParams` correctness through the Hoare kernel** —
    the first walker × `TcM.WF` composition. From any state whose intern
    table is key-coherent with support inside a collision-free `S`
    covering the walk's reach set: on success the result is exactly the
    pure spec and only `env.intern` moved; on error, likewise only
    `env.intern` moved (EStateM is non-backtracking). The `us.isEmpty`
    fast path returns `e` untouched, matching the spec's guard. -/
theorem TcM.instantiateUnivParams_wf {S : KExpr .anon → Prop}
    {us : Array (KUniv .anon)} {e : KExpr .anon} {s : TcState .anon}
    (hcf : KExpr.CollisionFree S)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → S x) :
    TcM.WF (fun s => s.env.intern.WF ∧
        ∀ x, s.env.intern.ExprSupport x → S x) s
      (TcM.instantiateUnivParams e us)
      (fun r s' => KExpr.instantiateUnivParamsSpec e us = .ok r ∧
        s' = { s with env := { s.env with intern := s'.env.intern } })
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hI
  obtain ⟨hwf, hsup⟩ := hI
  by_cases hemp : us.isEmpty
  · have hrun : TcM.instantiateUnivParams e us s = .ok e s := by
      rw [TcM.instantiateUnivParams, if_pos hemp]
      try rfl
    rw [hrun]
    exact ⟨⟨hwf, hsup⟩,
      by rw [KExpr.instantiateUnivParamsSpec, if_pos hemp], rfl⟩
  · have post := TcM.instUnivInner_spec hcf (e := e) (sc := {}) (s := s)
      hreach hwf hsup (InstUnivScratchInv.empty S us)
    cases hrec : TcM.instUnivInner e us {} s with
    | ok v s' =>
      obtain ⟨r, sc'⟩ := v
      rw [hrec] at post
      obtain ⟨hspec, ⟨hwf', hsup', hframe⟩, -⟩ := post
      have hrun : TcM.instantiateUnivParams e us s = .ok r s' := by
        rw [TcM.instantiateUnivParams, if_neg hemp]
        show ((TcM.instUnivInner e us).run' {}) s = _
        rw [run_run', hrec]
        try rfl
      rw [hrun]
      exact ⟨⟨hwf', hsup'⟩,
        by rw [KExpr.instantiateUnivParamsSpec, if_neg hemp]; exact hspec,
        hframe⟩
    | error err s' =>
      rw [hrec] at post
      obtain ⟨hwf', hsup', hframe⟩ := post
      have hrun : TcM.instantiateUnivParams e us s = .error err s' := by
        rw [TcM.instantiateUnivParams, if_neg hemp]
        show ((TcM.instUnivInner e us).run' {}) s = _
        rw [run_run', hrec]
        try rfl
      rw [hrun]
      exact ⟨⟨hwf', hsup'⟩, hframe⟩

/-! ### `substUniv` Theory correspondence (level side)

`substUniv` rebuilds with the SIMPLIFYING `mkMax`/`mkIMax` (Lean/Rust
parity), so its correspondence with `VLevel.inst` is an equivalence
`≈`, composed from the `toVLevel_mkMax`/`toVLevel_mkIMax` masters
(Verify/Level.lean). Hypotheses follow the finite-support discipline:
addr-faithfulness and no-wrap size bounds over `SubstUnivReach` — the
subterm closure of the results of sub-calls, spec-determined and
finite. The `VLevel.WF` transport needs neither (guard-free
`mk*_cases`). Mode-generic: no interning is involved. -/

namespace KUniv

variable {m : Mode}

/-- Reach set of `substUniv us` on `u`: everything under the result of
    any sub-call. The `==`-branches of the simplifying constructors
    compare exactly these. -/
def SubstUnivReach (us : Array (KUniv m)) (u x : KUniv m) : Prop :=
  ∃ w r, Sub w u ∧ TcM.substUniv w us = .ok r ∧ Sub x r

theorem SubstUnivReach.mono {us : Array (KUniv m)} {u u' x : KUniv m}
    (hu : Sub u u') (h : SubstUnivReach us u x) :
    SubstUnivReach us u' x := by
  obtain ⟨w, r, hw, hr, hx⟩ := h
  exact ⟨w, r, hw.trans hu, hr, hx⟩

end KUniv

/-- **`substUniv` ↔ `VLevel.inst`** — the level-side Theory
    correspondence for universe instantiation: on success, the
    substituted level is `≈`-equivalent to the theory-side
    instantiation of the translation. -/
theorem TcM.substUniv_toVLevel {m : Mode} {us : Array (KUniv m)} :
    ∀ {u v : KUniv m}, TcM.substUniv u us = .ok v →
      (∀ x y, KUniv.SubstUnivReach us u x →
        KUniv.SubstUnivReach us u y → x.AddrFaithful y) →
      (∀ x, KUniv.SubstUnivReach us u x → x.size < UInt64.size) →
      v.toVLevel
        ≈ (KUniv.toVLevel u).inst (us.toList.map KUniv.toVLevel) := by
  intro u
  induction u with
  | zero ad =>
    intro v h hinj hsz
    have hb : TcM.substUniv (KUniv.zero ad) us
        = .ok (KUniv.zero (m := m) ad) := rfl
    rw [hb] at h
    cases h
    exact VLevel.equiv_def.mpr fun ρ => rfl
  | param idx nm ad =>
    intro v h hinj hsz
    have hb : TcM.substUniv (KUniv.param idx nm ad) us
        = (match us[idx.toNat]? with
           | some w => .ok w
           | none => .error (.univParamOutOfRange idx us.size)) := rfl
    rw [hb] at h
    cases hus : us[idx.toNat]? with
    | none =>
      rw [hus] at h
      cases h
    | some w =>
      rw [hus] at h
      cases h
      refine VLevel.equiv_def.mpr fun ρ => ?_
      have hget : (us.toList.map KUniv.toVLevel).getD idx.toNat .zero
          = KUniv.toVLevel v := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map,
          Array.getElem?_toList, hus]
      show (KUniv.toVLevel v).eval ρ
          = ((us.toList.map KUniv.toVLevel).getD idx.toNat .zero).eval ρ
      rw [hget]
  | succ inner ad ih =>
    intro v h hinj hsz
    have hb : TcM.substUniv (KUniv.succ inner ad) us
        = (TcM.substUniv inner us >>= fun vi =>
            pure (KUniv.mkSucc vi)) := rfl
    rw [hb] at h
    cases hs : TcM.substUniv inner us with
    | error e =>
      rw [hs] at h
      cases h
    | ok vi =>
      rw [hs] at h
      cases h
      have ihh := ih hs
        (fun x y hx hy => hinj x y (hx.mono (.succ .refl))
          (hy.mono (.succ .refl)))
        (fun x hx => hsz x (hx.mono (.succ .refl)))
      refine VLevel.equiv_def.mpr fun ρ => ?_
      have h2 := VLevel.equiv_def.mp ihh ρ
      show (KUniv.mkSucc vi).toVLevel.eval ρ
          = ((KUniv.toVLevel inner).inst
              (us.toList.map KUniv.toVLevel)).eval ρ + 1
      rw [KUniv.toVLevel_mkSucc]
      show vi.toVLevel.eval ρ + 1 = _
      rw [h2]
  | max a b ad iha ihb =>
    intro v h hinj hsz
    have hb : TcM.substUniv (KUniv.max a b ad) us
        = (TcM.substUniv a us >>= fun ra =>
            TcM.substUniv b us >>= fun rb =>
              pure (KUniv.mkMax ra rb)) := rfl
    rw [hb] at h
    cases hsa : TcM.substUniv a us with
    | error e =>
      rw [hsa] at h
      cases h
    | ok ra =>
      cases hsb : TcM.substUniv b us with
      | error e =>
        rw [hsa, hsb] at h
        cases h
      | ok rb =>
        rw [hsa, hsb] at h
        cases h
        have ihha := iha hsa
          (fun x y hx hy => hinj x y (hx.mono (.max_l .refl))
            (hy.mono (.max_l .refl)))
          (fun x hx => hsz x (hx.mono (.max_l .refl)))
        have ihhb := ihb hsb
          (fun x y hx hy => hinj x y (hx.mono (.max_r .refl))
            (hy.mono (.max_r .refl)))
          (fun x hx => hsz x (hx.mono (.max_r .refl)))
        have hmk := KUniv.toVLevel_mkMax (a := ra) (b := rb)
          (fun x y hx hy => hinj x y
            (hx.elim (fun hx => ⟨a, ra, .max_l .refl, hsa, hx⟩)
              (fun hx => ⟨b, rb, .max_r .refl, hsb, hx⟩))
            (hy.elim (fun hy => ⟨a, ra, .max_l .refl, hsa, hy⟩)
              (fun hy => ⟨b, rb, .max_r .refl, hsb, hy⟩)))
          (hsz ra ⟨a, ra, .max_l .refl, hsa, .refl⟩)
          (hsz rb ⟨b, rb, .max_r .refl, hsb, .refl⟩)
        refine VLevel.equiv_def.mpr fun ρ => ?_
        have h1 := VLevel.equiv_def.mp hmk ρ
        have h2 := VLevel.equiv_def.mp ihha ρ
        have h3 := VLevel.equiv_def.mp ihhb ρ
        rw [h1]
        show Nat.max (ra.toVLevel.eval ρ) (rb.toVLevel.eval ρ)
            = Nat.max
                (((KUniv.toVLevel a).inst
                  (us.toList.map KUniv.toVLevel)).eval ρ)
                (((KUniv.toVLevel b).inst
                  (us.toList.map KUniv.toVLevel)).eval ρ)
        rw [h2, h3]
  | imax a b ad iha ihb =>
    intro v h hinj hsz
    have hb : TcM.substUniv (KUniv.imax a b ad) us
        = (TcM.substUniv a us >>= fun ra =>
            TcM.substUniv b us >>= fun rb =>
              pure (KUniv.mkIMax ra rb)) := rfl
    rw [hb] at h
    cases hsa : TcM.substUniv a us with
    | error e =>
      rw [hsa] at h
      cases h
    | ok ra =>
      cases hsb : TcM.substUniv b us with
      | error e =>
        rw [hsa, hsb] at h
        cases h
      | ok rb =>
        rw [hsa, hsb] at h
        cases h
        have ihha := iha hsa
          (fun x y hx hy => hinj x y (hx.mono (.imax_l .refl))
            (hy.mono (.imax_l .refl)))
          (fun x hx => hsz x (hx.mono (.imax_l .refl)))
        have ihhb := ihb hsb
          (fun x y hx hy => hinj x y (hx.mono (.imax_r .refl))
            (hy.mono (.imax_r .refl)))
          (fun x hx => hsz x (hx.mono (.imax_r .refl)))
        have hmk := KUniv.toVLevel_mkIMax (a := ra) (b := rb)
          (fun x y hx hy => hinj x y
            (hx.elim (fun hx => ⟨a, ra, .imax_l .refl, hsa, hx⟩)
              (fun hx => ⟨b, rb, .imax_r .refl, hsb, hx⟩))
            (hy.elim (fun hy => ⟨a, ra, .imax_l .refl, hsa, hy⟩)
              (fun hy => ⟨b, rb, .imax_r .refl, hsb, hy⟩)))
          (hsz ra ⟨a, ra, .imax_l .refl, hsa, .refl⟩)
          (hsz rb ⟨b, rb, .imax_r .refl, hsb, .refl⟩)
        refine VLevel.equiv_def.mpr fun ρ => ?_
        have h1 := VLevel.equiv_def.mp hmk ρ
        have h2 := VLevel.equiv_def.mp ihha ρ
        have h3 := VLevel.equiv_def.mp ihhb ρ
        rw [h1]
        show Nat.imax (ra.toVLevel.eval ρ) (rb.toVLevel.eval ρ)
            = Nat.imax
                (((KUniv.toVLevel a).inst
                  (us.toList.map KUniv.toVLevel)).eval ρ)
                (((KUniv.toVLevel b).inst
                  (us.toList.map KUniv.toVLevel)).eval ρ)
        rw [h2, h3]

/-- `VLevel.WF` transport for `substUniv`: if every element of `us`
    translates well-formed at `n` parameters, so does the result — no
    collision-freedom or size bounds needed (guard-free `mk*_cases`). -/
theorem TcM.substUniv_wf {m : Mode} {us : Array (KUniv m)} {n : Nat}
    (hus : ∀ w ∈ us, (KUniv.toVLevel w).WF n) :
    ∀ {u v : KUniv m}, TcM.substUniv u us = .ok v →
      (KUniv.toVLevel v).WF n := by
  intro u
  induction u with
  | zero ad =>
    intro v h
    have hb : TcM.substUniv (KUniv.zero ad) us
        = .ok (KUniv.zero (m := m) ad) := rfl
    rw [hb] at h
    cases h
    trivial
  | param idx nm ad =>
    intro v h
    have hb : TcM.substUniv (KUniv.param idx nm ad) us
        = (match us[idx.toNat]? with
           | some w => .ok w
           | none => .error (.univParamOutOfRange idx us.size)) := rfl
    rw [hb] at h
    cases hget : us[idx.toNat]? with
    | none =>
      rw [hget] at h
      cases h
    | some w =>
      rw [hget] at h
      cases h
      exact hus _ (Array.mem_of_getElem? hget)
  | succ inner ad ih =>
    intro v h
    have hb : TcM.substUniv (KUniv.succ inner ad) us
        = (TcM.substUniv inner us >>= fun vi =>
            pure (KUniv.mkSucc vi)) := rfl
    rw [hb] at h
    cases hs : TcM.substUniv inner us with
    | error e =>
      rw [hs] at h
      cases h
    | ok vi =>
      rw [hs] at h
      cases h
      exact KUniv.toVLevel_mkSucc_wf (ih hs)
  | max a b ad iha ihb =>
    intro v h
    have hb : TcM.substUniv (KUniv.max a b ad) us
        = (TcM.substUniv a us >>= fun ra =>
            TcM.substUniv b us >>= fun rb =>
              pure (KUniv.mkMax ra rb)) := rfl
    rw [hb] at h
    cases hsa : TcM.substUniv a us with
    | error e =>
      rw [hsa] at h
      cases h
    | ok ra =>
      cases hsb : TcM.substUniv b us with
      | error e =>
        rw [hsa, hsb] at h
        cases h
      | ok rb =>
        rw [hsa, hsb] at h
        cases h
        exact KUniv.toVLevel_mkMax_wf (iha hsa) (ihb hsb)
  | imax a b ad iha ihb =>
    intro v h
    have hb : TcM.substUniv (KUniv.imax a b ad) us
        = (TcM.substUniv a us >>= fun ra =>
            TcM.substUniv b us >>= fun rb =>
              pure (KUniv.mkIMax ra rb)) := rfl
    rw [hb] at h
    cases hsa : TcM.substUniv a us with
    | error e =>
      rw [hsa] at h
      cases h
    | ok ra =>
      cases hsb : TcM.substUniv b us with
      | error e =>
        rw [hsa, hsb] at h
        cases h
      | ok rb =>
        rw [hsa, hsb] at h
        cases h
        exact KUniv.toVLevel_mkIMax_wf (iha hsa) (ihb hsb)
