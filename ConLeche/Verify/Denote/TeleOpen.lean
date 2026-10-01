module

public import ConLeche.Verify.Denote.Rename
public import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InferLemmas

public section

/-!
# Opening a telescope, and substituting a spine into what is left

The phase's shared piece, named in `ConLeche/TTVerify/DeclInd.lean`:
**the thing that moves a spine between two descriptions of the same
telescope.**  Both folds and both bottoms need the *residual* of a
`∀`-telescope after `k` arguments, and the two sides describe it
differently:

* the pins describe it **syntactically**, as `stripPis`' body with `k`
  loose bvars;
* the laws consume it **semantically**, as a `Term` with the use
  site's spine `xs` already substituted.

Composing the two is: open the `k` binders at fresh variables
(`Expr.instSeq` at `openFvars`, so the existing `instSeq_*` algebra
applies verbatim), denote, then substitute `xs` — which is
`Term.instSeq`, the missing half.

**Why `Term.instSeq` mirrors `Expr.instSeq` clause for clause**
(descending cuts, the same `t - 1`): the two are applied to the *same*
telescope, one before and one after `denote`, and every index fact is
then a transcription rather than a re-derivation.  The one place they
differ is `instSeq_bvar`, and the difference is instructive:
`Expr.instantiate1` does **not** lift, so the `Expr` lemma needs
`looseBVarsBounded 0` on every argument; `Term.inst` does, so the
`Term` lemma needs nothing and pays instead by producing
`liftN c x` — the lifts the consumer's own `inst` then absorbs.
-/

namespace ConLeche.Term
namespace Term

/-! ## `Term.instSeq` -/

/-- Instantiate a spine at descending cuts, outermost argument first —
the term-side counterpart of `ConLeche.Expr.instSeq`. -/
@[expose] def instSeq : List Term → Nat → Term → Term
  | [], _, e => e
  | a :: as, t, e => instSeq as (t - 1) (e.inst a t)

@[simp] theorem instSeq_nil (t : Nat) (e : Term) : instSeq [] t e = e := rfl

theorem instSeq_cons (a : Term) (as : List Term) (t : Nat) (e : Term) :
    instSeq (a :: as) t e = instSeq as (t - 1) (e.inst a t) := rfl

/-- A closed term is untouched. -/
theorem instSeq_eq_self_of_closed {e : Term} (h : Closed e) :
    ∀ (as : List Term) (t : Nat), instSeq as t e = e := by
  intro as
  induction as with
  | nil => intro t; rfl
  | cons a as ih => intro t; rw [instSeq_cons, inst_eq_self_of_closed h, ih]

@[simp] theorem instSeq_sort (as : List Term) (t u : Nat) :
    instSeq as t (.sort u) = .sort u :=
  instSeq_eq_self_of_closed (e := .sort u) trivial as t

@[simp] theorem instSeq_const (as : List Term) (t : Nat) (c : BConst)
    (us : List Nat) : instSeq as t (.const c us) = .const c us :=
  instSeq_eq_self_of_closed (e := .const c us) trivial as t

theorem instSeq_app : ∀ (as : List Term) (t : Nat) (f a : Term),
    instSeq as t (.app f a) = .app (instSeq as t f) (instSeq as t a) := by
  intro as
  induction as with
  | nil => intro t f a; rfl
  | cons x xs ih => intro t f a; rw [instSeq_cons, inst_app, ih]; rfl

theorem instSeq_mkAppN : ∀ (as : List Term) (t : Nat) (f : Term)
    (args : List Term),
    instSeq as t (mkAppN f args) =
      mkAppN (instSeq as t f) (args.map (instSeq as t ·)) := by
  intro as t f args
  induction args generalizing f with
  | nil => rfl
  | cons a args ih =>
    rw [mkAppN_cons, ih, instSeq_app]
    rfl

/-- Under a binder the cut steps up — the transcription of
`Expr.instSeq_forallE`, with the same side condition. -/
theorem instSeq_pi : ∀ (as : List Term) (t : Nat) (A B : Term),
    as.length ≤ t + 1 →
    instSeq as t (.pi A B) = .pi (instSeq as t A) (instSeq as (t + 1) B) := by
  intro as
  induction as with
  | nil => intro t A B _; rfl
  | cons x xs ih =>
    intro t A B hlen
    simp only [List.length_cons] at hlen
    rw [instSeq_cons, inst_pi,
      ih (t - 1) (A.inst x t) (B.inst x (t + 1)) (by omega)]
    rw [instSeq_cons (t := t) (e := A), instSeq_cons (t := t + 1) (e := B)]
    cases xs with
    | nil => rfl
    | cons y ys => rw [show t - 1 + 1 = t + 1 - 1 from by simp at hlen; omega]

/-- A variable below the substituted range is untouched. -/
theorem instSeq_bvar_lt : ∀ (as : List Term) (t j : Nat),
    j + as.length ≤ t → instSeq as t (.bvar j) = .bvar j := by
  intro as
  induction as with
  | nil => intro t j _; rfl
  | cons x xs ih =>
    intro t j hlen
    simp only [List.length_cons] at hlen
    rw [instSeq_cons, inst_bvar, if_pos (by omega)]
    exact ih (t - 1) j (by omega)

end Term
end ConLeche.Term

namespace ConLeche.Verify

open ConLeche.Term

/-! ## Opening a telescope's binders

The `Expr` half.  Opening is `Expr.instSeq` at a run of fresh
variables, so `instSeq_forallE`, `instSeq_mkAppN`, `instSeq_bvar` and
`instSeq_eq_self` all apply unchanged; the only fact this section adds
is the one the `Expr` side was missing — that an instantiation *below*
the substituted range passes through (`instSeq_instantiate1_in`, the
dual of `Expr.instSeq_instantiate1_out`). -/

/-- **An instantiation below the substituted range passes through.**
The dual of `Expr.instSeq_instantiate1_out`, and the fact that lets a
residual's *own* binders be opened by `denote` after the telescope's
have been opened by `instSeq`. -/
theorem instSeq_instantiate1_in {b : Expr}
    (hbb : b.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      args.length ≤ t →
      (Expr.instSeq args t e).instantiate1 b 0 =
        Expr.instSeq args (t - 1) (e.instantiate1 b 0) := by
  intro args
  induction args with
  | nil => intro t e _ _; rfl
  | cons a as ih =>
    intro t e hb hlen
    simp only [List.length_cons] at hlen
    show (Expr.instSeq as (t - 1) (e.instantiate1 a t)).instantiate1 b 0 = _
    rw [ih (t - 1) (fun x hx => hb x (List.mem_cons_of_mem _ hx)) (by omega)]
    show _ = Expr.instSeq as (t - 1 - 1) ((e.instantiate1 b 0).instantiate1 a (t - 1))
    rw [show t = (t - 1) + 1 from by omega]
    rw [Expr.instantiate1_instantiate1 (hb a List.mem_cons_self) hbb e 0 (t - 1)
      (Nat.zero_le _)]
    simp

/-! ## The checker's opener, tied to the fold machinery

`openPisAtFvars` is how every *iota* pin is stated — the checked
`iota_j` theorem's telescope is opened at free variables and the
statement's parts are read off with `getAppFn`/`getAppArgs` — while the
capability pins use `stripPis` and the folds were built on
`Expr.instSeq (openFvars d k)`.  The two openers agree: both peel
outermost-first, giving the `j`-th binder the variable at index
`d + j`.  This section is that agreement, so the bottoms inherit
`piTower_of_stripPis`, `denote_paramTuple` and everything else the
folds built rather than re-deriving them against a second opener.

`openPisAtFvars` opens with the binder's *own* name and domain and
`openFvars` with canonical ones; `denote` reads neither
(`ConLeche/Verify/Denote.lean`), so the two bodies are `ErasedEq` and
that is exactly the tolerance `denote_erasedEq` consumes. -/

/-- A telescope that opens at a free variable strips.  **The `fvar`
restriction is not cosmetic**: for a general `v` the statement is
false, since `(.bvar 0).instantiate1 v 0 = v` may be a `∀` while
`.bvar 0` is not.  Sibling of `stripLams_instantiate1_fvar_isSome_rev`,
and the checker only ever opens at variables. -/
theorem stripPis_instantiate1_fvar_isSome_rev {i : Nat}
    {ty : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat),
      ((e.instantiate1 (.fvar i ty) j).stripPis k).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro e j _; rfl
  | succ k ih =>
    intro e j h
    cases e with
    | forallE ty' body m =>
      simp only [Expr.instantiate1, Expr.stripPis, Option.isSome_map] at h ⊢
      exact ih (j + 1) h
    | bvar l =>
      simp only [Expr.instantiate1] at h
      split at h
      · simp only [Expr.stripPis] at h; exact nomatch h
      · split at h <;> (simp only [Expr.stripPis] at h; exact nomatch h)
    | _ => simp only [Expr.instantiate1, Expr.stripPis] at h; exact nomatch h

/-- **The checker's opener, read as a strip plus a canonical
opening.**  `openPisAtFvars` succeeding gives the `stripPis` the fold
machinery wants, an opened body `ErasedEq` to the canonical one, and
the opening variables at their expected indices. -/
theorem openPisAtFvars_stripPis :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      ∃ bs body₀, e.stripPis k = some (bs, body₀) ∧
        fvs.length = k ∧
        (∀ j, j < k → ∃ ty, fvs[j]? = some (.fvar (d + j) ty)) ∧
        Expr.ErasedEq body
          (Expr.instSeq (openFvars d k) (k - 1) body₀) := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl, fun j hj => absurd hj (by omega),
      Expr.ErasedEq.rfl _⟩
  | succ k ih =>
    intro e d fvs body h
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨bs', body₀', hstrip', hlen', hidx', herased'⟩ := ih hop
        have hsome : (bodyE.stripPis k).isSome = true :=
          stripPis_instantiate1_fvar_isSome_rev k 0 (by rw [hstrip']; rfl)
        obtain ⟨⟨bs, body₀⟩, hstrip⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨hbody0, -⟩ := Expr.stripPis_instantiate1_eq k 0 hstrip hstrip'
        refine ⟨(dom, mb) :: bs, body₀, by simp [Expr.stripPis, hstrip],
          by simp [hlen'], ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => exact ⟨dom, by simp⟩
          | succ j =>
            obtain ⟨ty', hj'⟩ := hidx' j (by omega)
            refine ⟨ty', ?_⟩
            rw [List.getElem?_cons_succ, hj']
            congr 2
            omega
        · rw [openFvars_succ, Nat.add_sub_cancel, Expr.instSeq]
          refine Expr.ErasedEq.trans herased' ?_
          rw [hbody0]
          simp only [Nat.zero_add]
          exact Expr.instSeq_erasedEq _ (k - 1)
            (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl _)
              (show Expr.ErasedEq (Expr.fvar d dom)
                (Expr.fvar d (.sort .zero)) from rfl))

/-! ## The opened statement -/

/-- The opened body is the strip body instantiated at the collected
openers — *exactly*, annotations included (the ErasedEq form is
`openPisAtFvars_stripPis`; the pinned-spine transfers need
equality). -/
theorem openPisAtFvars_instSeq :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr}
      {bs : List (Expr × BinderMeta)} {body₀ : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      e.stripPis k = some (bs, body₀) →
      body = Expr.instSeq fvs (k - 1) body₀ := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body bs body₀ h hs
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := hs
    rfl
  | succ k ih =>
    intro e d fvs body bs body₀ h hs
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.stripPis] at hs
        cases hs1 : bodyE.stripPis k with
        | none => rw [hs1] at hs; exact nomatch hs
        | some p1 =>
          rw [hs1] at hs
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hs
          obtain ⟨-, rfl⟩ := hs
          obtain ⟨q1, hq1⟩ := Option.isSome_iff_exists.mp
            (Expr.stripPis_instantiate1_isSome
              (v := .fvar d dom) k 0 (by rw [hs1]; rfl))
          obtain ⟨hbody1, -⟩ := Expr.stripPis_instantiate1_eq k 0 hs1 hq1
          have hihb := ih hop (show Expr.stripPis k
            (bodyE.instantiate1 (Expr.fvar d dom)) =
              some (q1.1, q1.2) from by rw [hq1])
          rw [Nat.zero_add] at hbody1
          rw [hihb, hbody1]
          show _ = Expr.instSeq (Expr.fvar d dom :: p.1) (k + 1 - 1) _
          rw [show Expr.instSeq (Expr.fvar d dom :: p.1) (k + 1 - 1)
              p1.2 = Expr.instSeq p.1 (k + 1 - 1 - 1)
              (p1.2.instantiate1 (.fvar d dom) (k + 1 - 1)) from rfl,
            Nat.add_sub_cancel]

/-- Indexing a prefix of a list by `range`. -/
theorem range_map_getD_prefix {α : Type _} [Inhabited α] (xs : List α)
    (nP : Nat) (h : nP ≤ xs.length) :
    (List.range nP).map (fun k => xs.getD k default) = xs.take nP := by
  refine List.ext_getElem? ?_
  intro j
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge j nP with hj | hj
  · rw [List.getElem?_range hj, List.getElem?_take_of_lt hj,
      List.getElem?_eq_getElem (show j < xs.length from by omega)]
    simp [List.getD, List.getElem?_eq_getElem
      (show j < xs.length from by omega)]
  · rw [List.getElem?_eq_none (by simpa using hj),
      List.getElem?_eq_none (by simp; omega)]
    rfl

/-- Indexing a suffix of a list by `range`. -/
theorem range_map_getD_suffix {α : Type _} [Inhabited α] (xs : List α)
    (nP nF : Nat) (h : xs.length = nP + nF) :
    (List.range nF).map (fun k => xs.getD (nP + k) default) =
      xs.drop nP := by
  refine List.ext_getElem? ?_
  intro j
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge j nF with hj | hj
  · rw [List.getElem?_range hj, List.getElem?_drop,
      List.getElem?_eq_getElem (show nP + j < xs.length from by omega)]
    simp [List.getD, List.getElem?_eq_getElem
      (show nP + j < xs.length from by omega)]
  · rw [List.getElem?_eq_none (by simpa using hj),
      List.getElem?_eq_none (by simp; omega)]
    rfl

set_option maxHeartbeats 3200000 in
/-- **The pinned projection statement, opened.**  `checkProjIota` pins
the strip-form body; the bottom consumes the opened form; the pinned
spine computes through `Expr.instSeq` at the openers. -/
theorem projStmtParts {sty : Expr} {nP nF i : Nat}
    {fvsO : List Expr} {sbodyO : Expr}
    {sbinders : List (Expr × BinderMeta)}
    {tySlot : Expr} {ℓA : Level} {Pm Cm : Name}
    {lpsE cusE : List Level}
    (hilt : i < nF)
    (_hSb : sty.looseBVarsBounded 0 = true)
    (hopenO : openPisAtFvars (nP + nF) sty 0 = some (fvsO, sbodyO))
    (hS_strip : sty.stripPis (nP + nF) = some (sbinders,
      .app (.app (.app (.const eqName [ℓA]) tySlot)
        (Expr.mkAppN (.const Pm lpsE)
          (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
           [Expr.mkAppN (.const Cm cusE)
             (((List.range nP).map fun k =>
                 Expr.bvar (nP + nF - 1 - k)) ++
              ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])))
        (.bvar (nF - 1 - i)))) :
    fvsO.length = nP + nF ∧
    sbodyO.getAppFn = .const eqName [ℓA] ∧
    ∃ αS, sbodyO.getAppArgs = [αS,
      Expr.mkAppN (.const Pm lpsE)
        (fvsO.take nP ++
         [Expr.mkAppN (.const Cm cusE) (fvsO.take nP ++ fvsO.drop nP)]),
      fvsO.getD (nP + i) default] := by
  have hbody := openPisAtFvars_instSeq (nP + nF) hopenO hS_strip
  obtain ⟨bsS, body₀S, hstripO, hlenO, hIdx, -⟩ :=
    openPisAtFvars_stripPis (nP + nF) hopenO
  have hfvsB : ∀ a ∈ fvsO, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hjlt, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨ty, hfj⟩ := hIdx j (by rw [← hlenO]; exact hjlt)
    rw [List.getElem?_eq_getElem hjlt] at hfj
    rw [Option.some.inj hfj]
    rfl
  have hbv : ∀ j, j < nP + nF →
      Expr.instSeq fvsO (nP + nF - 1) (.bvar j) =
        fvsO.getD (nP + nF - 1 - j) default := by
    intro j hj
    have hb := Expr.instSeq_bvar fvsO (nP + nF - 1) j hfvsB (by omega)
      (by rw [hlenO]; omega)
    have hklt : nP + nF - 1 - j < fvsO.length := by rw [hlenO]; omega
    rw [List.getElem?_eq_getElem hklt] at hb
    rw [show fvsO.getD (nP + nF - 1 - j) default =
      fvsO[nP + nF - 1 - j] from by
        simp [List.getD, List.getElem?_eq_getElem hklt]]
    exact (Option.some.inj hb).symm
  have hpre : ((List.range nP).map fun k =>
      Expr.bvar (nP + nF - 1 - k)).map
      (Expr.instSeq fvsO (nP + nF - 1)) = fvsO.take nP := by
    rw [List.map_map,
      show ((Expr.instSeq fvsO (nP + nF - 1)) ∘ fun k =>
          Expr.bvar (nP + nF - 1 - k)) = fun k =>
          Expr.instSeq fvsO (nP + nF - 1) (.bvar (nP + nF - 1 - k))
        from rfl]
    rw [List.map_congr_left (fun k hk => by
      have hklt : k < nP := List.mem_range.mp hk
      rw [hbv (nP + nF - 1 - k) (by omega),
        show nP + nF - 1 - (nP + nF - 1 - k) = k from by omega])]
    exact range_map_getD_prefix fvsO nP (by rw [hlenO]; omega)
  have hsuf : ((List.range nF).map fun k =>
      Expr.bvar (nF - 1 - k)).map
      (Expr.instSeq fvsO (nP + nF - 1)) = fvsO.drop nP := by
    rw [List.map_map,
      show ((Expr.instSeq fvsO (nP + nF - 1)) ∘ fun k =>
          Expr.bvar (nF - 1 - k)) = fun k =>
          Expr.instSeq fvsO (nP + nF - 1) (.bvar (nF - 1 - k))
        from rfl]
    rw [List.map_congr_left (fun k hk => by
      have hklt : k < nF := List.mem_range.mp hk
      rw [hbv (nF - 1 - k) (by omega),
        show nP + nF - 1 - (nF - 1 - k) = nP + k from by omega])]
    exact range_map_getD_suffix fvsO nP nF hlenO
  -- the strip body is a three-argument spine over the equality head
  rw [show (Expr.app (.app (.app (.const eqName [ℓA]) tySlot)
      (Expr.mkAppN (.const Pm lpsE)
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const Cm cusE)
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])))
      (.bvar (nF - 1 - i))) = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const Pm lpsE)
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const Cm cusE)
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)] from rfl,
    Expr.instSeq_mkAppN,
    Expr.instSeq_eq_self _ _ (show (Expr.const eqName
      [ℓA]).looseBVarsBounded 0 = true from rfl)] at hbody
  refine ⟨hlenO, ?_, ?_⟩
  · rw [hbody, Expr.getAppFn_mkAppN]
    rfl
  · refine ⟨Expr.instSeq fvsO (nP + nF - 1) tySlot, ?_⟩
    rw [hbody, Expr.getAppArgs_mkAppN]
    rw [show (Expr.const eqName [ℓA]).getAppArgs = [] from rfl,
      List.nil_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (show (Expr.const Pm
        lpsE).looseBVarsBounded 0 = true from rfl),
      List.map_append, hpre]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (show (Expr.const Cm
        cusE).looseBVarsBounded 0 = true from rfl),
      List.map_append, hpre, hsuf,
      hbv (nF - 1 - i) (by omega),
      show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega]

end ConLeche.Verify
