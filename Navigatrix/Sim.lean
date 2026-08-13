import Navigatrix.Ixon.Eval
import Navigatrix.IxIR0.Mono
import Navigatrix.Erase

/-!
# The erasure simulation, stages 1 + 2a

Stage 1 proved the theorem on the pure λ-fragment. Stage 2a extends
it to **literals, zero-parameter constructors, projections, and
reference resolution** — the relation becomes frame-aware and gains a
program-level correspondence:

- `PErase` is indexed by the evaluation contexts and by the **refs
  table** of the frame the source expression is read against; a `ref`
  is in the relation only when its address is `Covered` — the
  per-address program correspondence (mutually defined with `PErase`,
  since a covered definition's body must itself be a related
  erasure). Covered shapes in 2a: unfoldable definitions, projection
  constants of zero-parameter constructors, and inductive-type
  constants (which erase to `defn ◻`).
- `ValRel` gains: literal values; constructor values (fields related
  pointwise via `ValsRel`, identity pinned by `CtorShape`); partial
  constructor applications (pap-to-pap, arities tied to the field
  count); and **type-former neutrals relate to `◻`** — the source
  neutral accumulates arguments while the target's `◻` absorbs them,
  which is exactly why `defn ◻` is the right erasure for type
  constants.

Still outside the relation (stage 2b): recursors and ι (the
rule-transformation correspondence plus ghost-argument positions),
constructors with parameters (the argument-dropping alignment — List
lives there), shares, and the remaining constant shapes (quotients,
axioms/externs — the latter await the oracle/ledger correspondence).
The differential suite in `Erase.lean` already witnesses those
behaviors; this file is the theorem catching up.

Fuel handling is unchanged: strong induction on source fuel,
`IxIR0.eval_mono` to combine target sub-derivations.
-/

namespace Navigatrix.Sim

open Navigatrix.Ixon (Uses)

/-- Syntactic type-scheme test — share-free restriction of
`Erase.sortLike`. -/
def sortLikeP : Ixon.Expr → Bool
  | .sort _ => true
  | .all _ _ _ cod => sortLikeP cod
  | _ => false

/-- Is a binder with this mode and domain erased? Mirrors
`Erase.dropBinder` on the fragment. -/
def dropB (u : Uses) (dom : Ixon.Expr) : Bool :=
  u == .erased || sortLikeP dom

/-- Constructor identity resolved through the source context: a
zero-parameter constructor (stage 2a) with the given field count. -/
def CtorShape (ectx : Ixon.Eval.EvalCtx) (block : Ixon.Address)
    (indIdx cidx fields : Nat) : Prop :=
  ∃ bc ind ct,
    Ixon.Eval.resolveMut ectx block indIdx = .ok (bc, .indc ind) ∧
    ind.ctors[cidx]? = some ct ∧
    ind.params.toNat = 0 ∧ ct.params.toNat = 0 ∧ ct.fields.toNat = fields

mutual
  /-- Relational erasure, read against a refs table. The mask records,
  per context slot, whether the binder was kept. -/
  inductive PErase : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Array Ixon.Address → List Bool → Ixon.Expr → IxIR0.Expr → Prop where
    | var {ectx ictx refs} {mask : List Bool} {i : UInt64} :
        mask[i.toNat]? = some true →
        PErase ectx ictx refs mask (.var i) (.var i.toNat)
    | sortE {ectx ictx refs} {mask : List Bool} {u : UInt64} :
        PErase ectx ictx refs mask (.sort u) .erased
    | allE {ectx ictx refs} {mask : List Bool} {u : Uses}
        {o : Navigatrix.Ixon.Owned} {dom cod : Ixon.Expr} :
        PErase ectx ictx refs mask (.all u o dom cod) .erased
    | lamK {ectx ictx refs} {mask : List Bool} {u : Uses}
        {dom body : Ixon.Expr} {body' : IxIR0.Expr} :
        dropB u dom = false →
        PErase ectx ictx refs (true :: mask) body body' →
        PErase ectx ictx refs mask (.lam u dom body) (.lam u body')
    | lamD {ectx ictx refs} {mask : List Bool} {u : Uses}
        {dom body : Ixon.Expr} {body' : IxIR0.Expr} :
        dropB u dom = true →
        PErase ectx ictx refs (false :: mask) body body' →
        PErase ectx ictx refs mask (.lam u dom body) (.lam .many body')
    | app {ectx ictx refs} {mask : List Bool} {f a : Ixon.Expr}
        {f' a' : IxIR0.Expr} :
        PErase ectx ictx refs mask f f' →
        PErase ectx ictx refs mask a a' →
        PErase ectx ictx refs mask (.app f a) (.app f' a')
    | appE {ectx ictx refs} {mask : List Bool} {u : Uses}
        {dom body a : Ixon.Expr} {f' : IxIR0.Expr} :
        dropB u dom = true →
        PErase ectx ictx refs mask (.lam u dom body) f' →
        PErase ectx ictx refs mask (.app (.lam u dom body) a)
          (.app f' .erased)
    | letE {ectx ictx refs} {mask : List Bool} {nd : Bool}
        {ty val body : Ixon.Expr} {val' body' : IxIR0.Expr} :
        PErase ectx ictx refs mask val val' →
        PErase ectx ictx refs (true :: mask) body body' →
        PErase ectx ictx refs mask (.letE nd ty val body)
          (.letE .many val' body')
    | ref {ectx ictx refs} {mask : List Bool} {refIdx : UInt64}
        {univIdxs : Array UInt64} {a : Ixon.Address} :
        refs[refIdx.toNat]? = some a →
        Covered ectx ictx a →
        PErase ectx ictx refs mask (.ref refIdx univIdxs) (.ref a)
    | natE {ectx ictx refs} {mask : List Bool} {idx : UInt64}
        {a : Ixon.Address} {n : Nat} :
        refs[idx.toNat]? = some a →
        ectx.blobs a = some (.natB n) →
        PErase ectx ictx refs mask (.nat idx) (.lit (.nat n))
    | strE {ectx ictx refs} {mask : List Bool} {idx : UInt64}
        {a : Ixon.Address} {s : String} :
        refs[idx.toNat]? = some a →
        ectx.blobs a = some (.strB s) →
        PErase ectx ictx refs mask (.str idx) (.lit (.str s))
    | prjE {ectx ictx refs} {mask : List Bool} {tyRef fieldIdx : UInt64}
        {val : Ixon.Expr} {val' : IxIR0.Expr} :
        PErase ectx ictx refs mask val val' →
        PErase ectx ictx refs mask (.prj tyRef fieldIdx val)
          (.proj fieldIdx.toNat val')

  /-- The program correspondence at one address. -/
  inductive Covered : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Ixon.Address → Prop where
    | defn {ectx ictx} {a : Ixon.Address} {c : Navigatrix.Ixon.Constant}
        {d : Navigatrix.Ixon.Definition} {body' : IxIR0.Expr} :
        ectx.resolve a = some c →
        c.info = .defn d →
        Ixon.Eval.unfoldable d = true →
        ictx.env a = some (.defn body') →
        PErase ectx ictx c.refs [] d.value body' →
        Covered ectx ictx a
    | ctor {ectx ictx} {a : Ixon.Address} {c : Navigatrix.Ixon.Constant}
        {p : Navigatrix.Ixon.ConstructorProj} {fields : Nat} :
        ectx.resolve a = some c →
        c.info = .cPrj p →
        CtorShape ectx p.block p.idx.toNat p.cidx.toNat fields →
        ictx.env a = some (.ctor p.cidx.toNat fields) →
        Covered ectx ictx a
    | tyf {ectx ictx} {a : Ixon.Address} {c : Navigatrix.Ixon.Constant}
        {p : Navigatrix.Ixon.InductiveProj} :
        ectx.resolve a = some c →
        c.info = .iPrj p →
        ictx.env a = some (.defn .erased) →
        Covered ectx ictx a
end

mutual
  /-- Source and target values related by erasure. -/
  inductive ValRel : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Ixon.Eval.Value → IxIR0.Value → Prop where
    | sort {ectx ictx l} : ValRel ectx ictx (.sortV l) .erased
    | pi {ectx ictx u o F env dom cod} :
        ValRel ectx ictx (.piV u o F env dom cod) .erased
    | clos {ectx ictx} {mask : List Bool} {b : Bool} {u : Uses}
        {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value}
        {dom body : Ixon.Expr} {u' : Uses} {ρ : List IxIR0.Value}
        {body' : IxIR0.Expr} :
        EnvRel ectx ictx mask env ρ →
        PErase ectx ictx F.refs (b :: mask) body body' →
        ValRel ectx ictx (.closV u F env dom body) (.clos u' ρ body')
    | litNat {ectx ictx} {n : Nat} :
        ValRel ectx ictx (.litV (.natL n)) (.lit (.nat n))
    | litStr {ectx ictx} {s : String} :
        ValRel ectx ictx (.litV (.strL s)) (.lit (.str s))
    | ctorV {ectx ictx} {block : Ixon.Address} {indIdx cidx fields : Nat}
        {cargs : List Ixon.Eval.Value} {a : Ixon.Address}
        {fargs : List IxIR0.Value} :
        CtorShape ectx block indIdx cidx fields →
        ValsRel ectx ictx cargs fargs →
        ValRel ectx ictx (.ctorV block indIdx cidx cargs)
          (.ctor a cidx fargs)
    | papCtor {ectx ictx} {block : Ixon.Address}
        {indIdx cidx fields arity tarity : Nat}
        {sargs : List Ixon.Eval.Value} {a : Ixon.Address}
        {targs : List IxIR0.Value} :
        CtorShape ectx block indIdx cidx fields →
        arity = fields → tarity = fields →
        ValsRel ectx ictx sargs targs →
        ValRel ectx ictx (.papV (.ctorH block indIdx cidx arity) sargs)
          (.pap (.ctor a cidx tarity) targs)
    | neu {ectx ictx} {id : Ixon.Eval.NeutralId}
        {args : List Ixon.Eval.Value} :
        ValRel ectx ictx (.papV (.neuH id) args) .erased

  /-- Environments related slot-wise along the mask; dropped slots are
  unconstrained on both sides. -/
  inductive EnvRel : Ixon.Eval.EvalCtx → IxIR0.Ctx → List Bool →
      List Ixon.Eval.Value → List IxIR0.Value → Prop where
    | nil {ectx ictx} : EnvRel ectx ictx [] [] []
    | keep {ectx ictx mask env ρ v v'} :
        ValRel ectx ictx v v' → EnvRel ectx ictx mask env ρ →
        EnvRel ectx ictx (true :: mask) (v :: env) (v' :: ρ)
    | drop {ectx ictx mask env ρ v v'} :
        EnvRel ectx ictx mask env ρ →
        EnvRel ectx ictx (false :: mask) (v :: env) (v' :: ρ)

  /-- Pointwise-related value lists (constructor fields, pap args). -/
  inductive ValsRel : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      List Ixon.Eval.Value → List IxIR0.Value → Prop where
    | nil {ectx ictx} : ValsRel ectx ictx [] []
    | cons {ectx ictx v v' vs vs'} :
        ValRel ectx ictx v v' → ValsRel ectx ictx vs vs' →
        ValsRel ectx ictx (v :: vs) (v' :: vs')
end

private theorem bindOk {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem bindErr {ε α β : Type} (er : ε) (f : α → Except ε β) :
    ((Except.error er : Except ε α) >>= f) = Except.error er := rfl

private theorem bind_ok_iff {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bindErr]
  | ok a => simp [bindOk]

section Lemmas

variable {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}

private theorem envRel_lookup : ∀ (i : Nat) {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value},
    EnvRel ectx ictx mask env ρ →
    ∀ (v : Ixon.Eval.Value), mask[i]? = some true →
      env[i]? = some v →
      ∃ v', ρ[i]? = some v' ∧ ValRel ectx ictx v v' := by
  intro i
  induction i with
  | zero =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_zero] at he ⊢
      injection he with he'
      subst he'
      exact ⟨_, rfl, hv⟩
    | drop henv => simp at hm
  | succ j ihj =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he
    | drop henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he

private theorem valsRel_length : ∀ {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value}, ValsRel ectx ictx vs vs' →
    vs.length = vs'.length := by
  intro vs
  induction vs with
  | nil => intro vs' h; cases h; rfl
  | cons v rest ih =>
    intro vs' h
    cases h with
    | cons hv hrest => simp [ih hrest]

private theorem valsRel_append : ∀ {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value} {v v'},
    ValsRel ectx ictx vs vs' → ValRel ectx ictx v v' →
    ValsRel ectx ictx (vs ++ [v]) (vs' ++ [v']) := by
  intro vs
  induction vs with
  | nil =>
    intro vs' v v' h hv
    cases h
    exact .cons hv .nil
  | cons w rest ih =>
    intro vs' v v' h hv
    cases h with
    | cons hw hrest => exact .cons hw (ih hrest hv)

private theorem valsRel_lookup : ∀ (i : Nat) {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value}, ValsRel ectx ictx vs vs' →
    ∀ v, vs[i]? = some v →
    ∃ v', vs'[i]? = some v' ∧ ValRel ectx ictx v v' := by
  intro i
  induction i with
  | zero =>
    intro vs vs' h v he
    cases h with
    | nil => simp at he
    | cons hv hrest =>
      simp only [List.getElem?_cons_zero] at he ⊢
      injection he with he'
      subst he'
      exact ⟨_, rfl, hv⟩
  | succ j ihj =>
    intro vs vs' h v he
    cases h with
    | nil => simp at he
    | cons hv hrest =>
      simp only [List.getElem?_cons_succ] at he ⊢
      exact ihj hrest v he

end Lemmas

private theorem strongNat {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have aux : ∀ k n, n < k → P n := by
    intro k
    induction k with
    | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
    | succ k ihk =>
      intro n hn
      exact step n fun m hm =>
        ihk m (Nat.lt_of_lt_of_le hm (Nat.lt_succ_iff.mp hn))
  exact fun n => aux (n + 1) n (Nat.lt_succ_self n)

private def SimAt (fuel : Nat) : Prop :=
  ∀ (ectx : Ixon.Eval.EvalCtx) (F : Ixon.Eval.Frame)
    (env : List Ixon.Eval.Value) (e : Ixon.Expr) (v : Ixon.Eval.Value)
    (mask : List Bool) (ρ : List IxIR0.Value) (e' : IxIR0.Expr)
    (ictx : IxIR0.Ctx),
    Ixon.Eval.eval ectx fuel F env e = .ok v →
    PErase ectx ictx F.refs mask e e' →
    EnvRel ectx ictx mask env ρ →
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧ ValRel ectx ictx v v'

private theorem simAt : ∀ fuel, SimAt fuel := by
  refine strongNat ?_
  intro fuel ih
  cases fuel with
  | zero =>
    intro ectx F env e v mask ρ e' ictx hev hpe henv
    rw [Ixon.Eval.eval.eq_def] at hev
    simp at hev
  | succ n =>
    intro ectx F env e v mask ρ e' ictx hev hpe henv
    cases hpe with
    | var hm =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i w heq
        injection hev with hv
        subst hv
        obtain ⟨v', hρ, hrel⟩ := envRel_lookup _ henv _ hm heq
        refine ⟨1, v', ?_, hrel⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hρ]
      · simp at hev
    | sortE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i u heq
        injection hev with hv
        subst hv
        exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .sort⟩
      · simp at hev
    | allE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .pi⟩
    | lamK hnd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .clos henv hpb⟩
    | lamD hd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .clos henv hpb⟩
    | letE hpv hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i nd ty val body val' body'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW⟩ :=
          ih n (by omega) ectx F env val w mask ρ val' ictx hval hpv henv
        obtain ⟨n₂, v', hv', hrel⟩ :=
          ih n (by omega) ectx F (w :: env) body v (true :: mask)
            (w' :: ρ) body' ictx hev hpb (.keep hrelW henv)
        refine ⟨n₁ + n₂ + 1, v', ?_, hrel⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ by omega) hw', bindOk]
        exact IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ by omega) hv'
    | natE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litNat⟩
    | strE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litStr⟩
    | prjE hpv =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i tyRef fieldIdx val val'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW⟩ :=
          ih n (by omega) ectx F env val w mask ρ val' ictx hval hpv henv
        cases hrelW with
        | sort => dsimp only at hev; simp at hev
        | pi => dsimp only at hev; simp at hev
        | clos _ _ => dsimp only at hev; simp at hev
        | litNat => dsimp only at hev; simp at hev
        | litStr => dsimp only at hev; simp at hev
        | neu => dsimp only at hev; simp at hev
        | papCtor _ _ _ _ => dsimp only at hev; simp at hev
        | ctorV hshape hargs =>
          rename_i block indIdx cidx fields cargs a fargs
          obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          cases hidx : cargs[ind.params.toNat + fieldIdx.toNat]? with
          | none => rw [hidx] at hev; simp at hev
          | some w0 =>
            rw [hidx] at hev
            dsimp only at hev
            injection hev with hv
            subst hv
            rw [hip, Nat.zero_add] at hidx
            obtain ⟨w0', hidx', hrel0⟩ := valsRel_lookup _ hargs _ hidx
            refine ⟨n₁ + 1, w0', ?_, hrel0⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [IxIR0.eval_mono (Nat.le_refl n₁) hw', bindOk]
            dsimp only
            rw [hidx']
    | ref hrefs hcov =>
      rename_i refIdx univIdxs a
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      cases n with
      | zero => rw [Ixon.Eval.evalRef.eq_def] at hev; simp at hev
      | succ g =>
        rw [Ixon.Eval.evalRef.eq_def] at hev
        dsimp only at hev
        cases hcov with
        | defn hres hinfo hunf hidecl hpe' =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          simp at hev
          obtain ⟨n₁, v', hv', hrel⟩ :=
            ih g (by omega) ectx _ [] _ v [] [] _ ictx hev hpe' .nil
          refine ⟨n₁ + 1, v', ?_, hrel⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          exact hv'
        | ctor hres hinfo hshape hidecl =>
          rename_i c p fields
          obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [hct] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          cases g with
          | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.saturate.eq_def] at hev
            simp only [Ixon.Eval.Head.arity?] at hev
            rw [hcp, hcf] at hev
            simp only [List.length_nil, Nat.zero_add] at hev
            cases fields with
            | zero =>
              simp at hev
              cases g' with
              | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
              | succ g'' =>
                rw [Ixon.Eval.fire.eq_def] at hev
                dsimp only at hev
                injection hev with hv
                subst hv
                refine ⟨3, .ctor a p.cidx.toNat [], ?_,
                  .ctorV ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ .nil⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [hidecl]
                dsimp only
                rw [IxIR0.saturate.eq_def]
                dsimp only
                simp [IxIR0.Head.arity]
                rw [IxIR0.fire.eq_def]
            | succ f' =>
              simp at hev
              subst hev
              refine ⟨2, .pap (.ctor a p.cidx.toNat (f' + 1)) [], ?_,
                .papCtor ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ rfl rfl .nil⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hidecl]
              dsimp only
              rw [IxIR0.saturate.eq_def]
              dsimp only
              simp [IxIR0.Head.arity]
        | tyf hres hinfo hidecl =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          split at hev
          · rw [bind_ok_iff] at hev
            obtain ⟨_, _, hev⟩ := hev
            injection hev with hv
            subst hv
            refine ⟨3, .erased, ?_, .neu⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hidecl]
            dsimp only
            rw [IxIR0.eval.eq_def]
          · simp at hev
          · simp at hev
    | app hpf hpa =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i fS aS fT aT
      cases hf : Ixon.Eval.eval ectx n F env fS with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, fv', hfv', hrelF⟩ :=
            ih n (by omega) ectx F env fS fv mask ρ fT ictx hf hpf henv
          obtain ⟨n₂, av', hav', hrelA⟩ :=
            ih n (by omega) ectx F env aS av mask ρ aT ictx ha hpa henv
          cases hrelF with
          | sort =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | pi =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | litNat =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | litStr =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | ctorV _ _ =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | clos henvC hbodyC =>
            rename_i maskC bC uC FC envC domC bodyC uC' ρC bodyC'
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              have henv' : EnvRel ectx ictx (bC :: maskC) (av :: envC)
                  (av' :: ρC) := by
                cases bC
                · exact .drop henvC
                · exact .keep hrelA henvC
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx FC (av :: envC) bodyC v (bC :: maskC)
                  (av' :: ρC) bodyC' ictx hev hbodyC henv'
              refine ⟨n₁ + n₂ + n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact IxIR0.eval_mono (show n₃ ≤ n₁ + n₂ + n₃ by omega) hv'
          | neu =>
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                injection hev with hv
                subst hv
                refine ⟨n₁ + n₂ + 3, .erased, ?_, .neu⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 2 by omega)
                  hfv', bindOk]
                rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 2 by omega)
                  hav', bindOk]
                rw [IxIR0.apply.eq_def]
          | papCtor hshape harity htarity hargs =>
            rename_i block indIdx cidx fields arity tarity sargs a targs
            subst harity htarity
            have hlen := valsRel_length hargs
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                cases hcmp : (sargs ++ [av]).length == tarity with
                | false =>
                  rw [hcmp] at hev
                  simp at hev
                  subst hev
                  refine ⟨n₁ + n₂ + 4,
                    .pap (.ctor a cidx tarity) (targs ++ [av']), ?_,
                    .papCtor hshape rfl rfl (valsRel_append hargs hrelA)⟩
                  rw [IxIR0.eval.eq_def]
                  dsimp only
                  rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 3 by omega)
                    hfv', bindOk]
                  rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 3 by omega)
                    hav', bindOk]
                  rw [IxIR0.apply.eq_def]
                  dsimp only
                  rw [IxIR0.saturate.eq_def]
                  dsimp only
                  have hl2 : (targs ++ [av']).length =
                      (sargs ++ [av]).length := by simp [hlen]
                  have hc2 : ((targs ++ [av']).length == tarity) = false := by
                    rw [hl2]; exact hcmp
                  simp only [IxIR0.Head.arity.eq_def, hc2]
                  simp
                | true =>
                  rw [hcmp] at hev
                  simp at hev
                  cases g' with
                  | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                  | succ g'' =>
                    rw [Ixon.Eval.fire.eq_def] at hev
                    dsimp only at hev
                    injection hev with hv
                    subst hv
                    refine ⟨n₁ + n₂ + 5,
                      .ctor a cidx (targs ++ [av']), ?_,
                      .ctorV hshape (valsRel_append hargs hrelA)⟩
                    rw [IxIR0.eval.eq_def]
                    dsimp only
                    rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 4 by omega)
                      hfv', bindOk]
                    rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 4 by omega)
                      hav', bindOk]
                    rw [IxIR0.apply.eq_def]
                    dsimp only
                    rw [IxIR0.saturate.eq_def]
                    dsimp only
                    have hl2 : (targs ++ [av']).length =
                        (sargs ++ [av]).length := by simp [hlen]
                    have hc2 : ((targs ++ [av']).length == tarity) = true := by
                      rw [hl2]; exact hcmp
                    simp only [IxIR0.Head.arity.eq_def, hc2]
                    simp only [if_true]
                    rw [IxIR0.fire.eq_def]
    | appE hd hlam =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i u dom body aS fT
      cases hf : Ixon.Eval.eval ectx n F env (.lam u dom body) with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          cases n with
          | zero => rw [Ixon.Eval.eval.eq_def] at hf; simp at hf
          | succ g =>
            rw [Ixon.Eval.eval.eq_def] at hf
            dsimp only at hf
            injection hf with hfv
            subst hfv
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases hlam with
            | lamK hnd hpb => rw [hd] at hnd; simp at hnd
            | lamD hd' hpb =>
              rename_i bodyT
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx F (av :: env) body v (false :: mask)
                  (.erased :: ρ) bodyT ictx hev hpb (.drop henv)
              have hlamT : IxIR0.eval ictx (n₃ + 1) ρ (.lam .many bodyT) =
                  .ok (.clos .many ρ bodyT) := by rw [IxIR0.eval.eq_def]
              have hboxT : IxIR0.eval ictx (n₃ + 1) ρ .erased =
                  .ok .erased := by rw [IxIR0.eval.eq_def]
              refine ⟨n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hlamT, bindOk, hboxT, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact hv'

/-- **The erasure simulation (stages 1 + 2a).** If a source term
terminates with a value under the Ixon reference semantics, its
erasure terminates under the IxIR₀ semantics with a related value.
The relation covers the pure λ-fragment plus literals, zero-parameter
constructors, projections, and references to covered constants. -/
theorem erasure_sim {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value} {e : Ixon.Expr}
    {v : Ixon.Eval.Value} {mask : List Bool} {ρ : List IxIR0.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx F.refs mask e e')
    (henv : EnvRel ectx ictx mask env ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧
      ValRel ectx ictx v v' :=
  simAt fuel ectx F env e v mask ρ e' ictx hev hpe henv

/-- Closed-term corollary. -/
theorem erasure_sim_closed {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx ictx F.refs [] e e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧
      ValRel ectx ictx v v' :=
  erasure_sim hev hpe .nil

/-! Executable-pass agreement spot checks on fragment terms. -/

private def ectx₀ : Erase.EraseCtx := { resolve := fun _ => none }

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.var 9) (.var 0)) with
  | .ok (.lam .many (.var 0)) => true
  | _ => false)

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0))) with
  | .ok (.lam .many (.lam .many (.var 0))) => true
  | _ => false)

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.app (.lam .many (.sort 0) (.sort 1)) (.sort 0)) with
  | .ok (.app (.lam .many .erased) .erased) => true
  | _ => false)

example {ectx ictx refs} :
    PErase ectx ictx refs [] (.lam .many (.var 9) (.var 0))
      (.lam .many (.var 0)) :=
  .lamK rfl (.var rfl)

example {ectx ictx refs} :
    PErase ectx ictx refs []
      (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0)))
      (.lam .many (.lam .many (.var 0))) :=
  .lamD rfl (.lamK rfl (.var rfl))

end Navigatrix.Sim
