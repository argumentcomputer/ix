module

public import ConLeche.Verify.Inductives.StructBody
import ConLeche.Verify.ProjSlots

public section

/-!
# The generated recursor, opened (task #175 S2)

The direct install stores the recursor it *generates* (`structRecTy`,
`structRecRhs`, `ConLeche/Kernel/Inductives/StructParts.lean`): the type former's
parameter binders re-emitted with the elimination datum, the motive,
one minor premise per constructor — the constructor's field telescope
lifted under the motive (and the earlier minors), its data reset —
the major, and `motive t`; the rule is the same telescope as a `λ`
over `minor f⃗`.  The reading side (`Model/Inductives/StructRecRead.lean`)
opens these binder by binder as `denoteMeta` does, and what it needs
from the syntax is collected here:

* the two binder walks commute with instantiation
  (`replacePisPw_instSeq`, `pisToLamsPw_instSeq`) and strip
  (`replacePisPw_stripPis`);
* the lifted field telescope, instantiated at the parameter variables
  and the extra binders' variables, is the constructor telescope's
  residual at the parameter variables alone
  (`instSeq_liftLooseBVars_prefix`, packaged as
  `instSeq_minorTele`), and that residual is the `instPisAt` peel's
  (`instPisAt_of_stripPis`);
* the closed spellings — the family spine `T p⃗`, the constructor
  spine `C p⃗ f⃗`, the rule body `minor f⃗` — instantiate to the
  variables (`map_instSeq_structPsAt`, `instSeq_minorBody`,
  `instSeq_ruleBody`);
* no generated node is a `.proj` node
  (`Expr.NoProjAt.structRecTy`/`.structRecRhs`), for the tower law's
  `NoProjEnv` invariant.
-/

namespace ConLeche

open Expr

/-! ## The binder walks -/

theorem replacePisPw_instantiate1 {pw : PropWhen} {v : Expr} :
    ∀ (k : Nat) {e b r : Expr} (j : Nat),
      Expr.replacePisPw pw k e b = some r →
      Expr.replacePisPw pw k (e.instantiate1 v j) (b.instantiate1 v (j + k))
        = some (r.instantiate1 v j)
  | 0, e, b, r, j, h => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    subst h
    simp [Expr.replacePisPw]
  | k + 1, e, b, r, j, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      simp only [Expr.instantiate1, Expr.replacePisPw]
      rw [show j + (k + 1) = j + 1 + k from by omega,
        replacePisPw_instantiate1 k (j + 1) hr']
      rfl
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.replacePisPw] at h

theorem pisToLamsPw_instantiate1 {pw : PropWhen} {v : Expr} :
    ∀ (k : Nat) {e b r : Expr} (j : Nat),
      Expr.pisToLamsPw pw k e b = some r →
      Expr.pisToLamsPw pw k (e.instantiate1 v j) (b.instantiate1 v (j + k))
        = some (r.instantiate1 v j)
  | 0, e, b, r, j, h => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at h
    subst h
    simp [Expr.pisToLamsPw]
  | k + 1, e, b, r, j, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      simp only [Expr.instantiate1, Expr.pisToLamsPw]
      rw [show j + (k + 1) = j + 1 + k from by omega,
        pisToLamsPw_instantiate1 k (j + 1) hr']
      rfl
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.pisToLamsPw] at h

/-- An instantiation sequence pushes through the walk: the telescope
is instantiated at the sequence's own index, the body `k` deeper. -/
theorem replacePisPw_instSeq {pw : PropWhen} :
    ∀ (sp : List Expr) (t : Nat) {k : Nat} {e b r : Expr},
      sp.length ≤ t + 1 →
      Expr.replacePisPw pw k e b = some r →
      Expr.replacePisPw pw k (instSeq sp t e) (instSeq sp (t + k) b)
        = some (instSeq sp t r)
  | [], _, _, _, _, _, _, h => h
  | a :: sp, t, k, e, b, r, hlen, h => by
    simp only [List.length_cons] at hlen
    show Expr.replacePisPw pw k (instSeq sp (t - 1) (e.instantiate1 a t))
      (instSeq sp (t + k - 1) (b.instantiate1 a (t + k))) = some (instSeq sp (t - 1) (r.instantiate1 a t))
    have h1 := replacePisPw_instantiate1 (v := a) k t h
    cases sp with
    | nil => exact h1
    | cons a' sp' =>
      have := replacePisPw_instSeq (a' :: sp') (t - 1) (by simp at hlen ⊢; omega) h1
      rwa [show t - 1 + k = t + k - 1 from by simp at hlen; omega] at this

theorem pisToLamsPw_instSeq {pw : PropWhen} :
    ∀ (sp : List Expr) (t : Nat) {k : Nat} {e b r : Expr},
      sp.length ≤ t + 1 →
      Expr.pisToLamsPw pw k e b = some r →
      Expr.pisToLamsPw pw k (instSeq sp t e) (instSeq sp (t + k) b)
        = some (instSeq sp t r)
  | [], _, _, _, _, _, _, h => h
  | a :: sp, t, k, e, b, r, hlen, h => by
    simp only [List.length_cons] at hlen
    show Expr.pisToLamsPw pw k (instSeq sp (t - 1) (e.instantiate1 a t))
      (instSeq sp (t + k - 1) (b.instantiate1 a (t + k))) = some (instSeq sp (t - 1) (r.instantiate1 a t))
    have h1 := pisToLamsPw_instantiate1 (v := a) k t h
    cases sp with
    | nil => exact h1
    | cons a' sp' =>
      have := pisToLamsPw_instSeq (a' :: sp') (t - 1) (by simp at hlen ⊢; omega) h1
      rwa [show t - 1 + k = t + k - 1 from by simp at hlen; omega] at this

/-- The walk keeps the telescope's binders (data reset) over the new
body. -/
theorem replacePisPw_stripPis {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      Expr.replacePisPw pw k e b = some r → e.stripPis k = some (bs, body) →
      r.stripPis k = some (bs.map fun x => (x.1, (⟨pw⟩ : BinderMeta)), b)
  | 0, e, b, r, bs, body, h, hs => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    subst h
    rw [← hs.1]
    rfl
  | k + 1, e, b, r, bs, body, h, hs => by
    match e, h, hs with
    | .forallE ty rest m, h, hs =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      simp only [stripPis] at hs
      cases hs' : rest.stripPis k with
      | none => rw [hs'] at hs; exact nomatch hs
      | some q =>
        rw [hs'] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [stripPis, replacePisPw_stripPis k hr' hs', Option.map_some, List.map_cons]
    | .bvar _, h, _ | .fvar _ _, h, _ | .sort _, h, _ | .const _ _, h, _
    | .app _ _, h, _ | .lam _ _ _, h, _ | .letE _ _ _, h, _ | .lit _, h, _
    | .proj _ _ _, h, _ => simp [Expr.replacePisPw] at h

/-- Two strips compose. -/
theorem stripPis_append :
    ∀ (k : Nat) {m : Nat} {e : Expr} {bs bs' : List (Expr × BinderMeta)}
      {mid body : Expr},
      e.stripPis k = some (bs, mid) → mid.stripPis m = some (bs', body) →
      e.stripPis (k + m) = some (bs ++ bs', body)
  | 0, m, e, bs, bs', mid, body, h, h' => by
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | k + 1, m, e, bs, bs', mid, body, h, h' => by
    match e, h with
    | .forallE ty rest mb, h =>
      simp only [stripPis] at h
      cases hs : rest.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [show k + 1 + m = (k + m) + 1 from by omega]
        simp only [stripPis, stripPis_append k hs h', Option.map_some, List.cons_append]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [stripPis] at h

/-- The `instPisAt` peel at a spine is the strip's body instantiated
along the spine (the `∀` twin of `instLamsAt_rest_of_stripLams`). -/
theorem instPisAt_of_stripPis :
    ∀ (sp : List Expr) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis sp.length = some (bs, body) →
      ∃ ds, Expr.instPisAt sp e = some (ds, instSeq sp (sp.length - 1) body)
  | [], e, bs, body, h => by
    simp only [List.length_nil, stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | a :: sp, e, bs, body, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [List.length_cons, stripPis] at h
      cases hs : rest.stripPis sp.length with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', hs', -⟩ := stripPis_instantiate1_full (v := a) sp.length 0 hs
        rw [Nat.zero_add] at hs'
        obtain ⟨ds, hds⟩ := instPisAt_of_stripPis sp hs'
        refine ⟨ty :: ds, ?_⟩
        simp only [Expr.instPisAt, hds, Option.map_some, List.length_cons, Nat.add_sub_cancel]
        rfl
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [stripPis] at h

/-- An instantiation sequence pushes through a `λ` (the twin of
`instSeq_forallE`). -/
theorem instSeq_lam :
    ∀ (args : List Expr) (t : Nat) (d b : Expr)
      (m : BinderMeta), args.length ≤ t + 1 →
      instSeq args t (.lam d b m) =
        .lam (instSeq args t d) (instSeq args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    show instSeq as (t - 1)
      (.lam (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.lam (instSeq as (t - 1) (d.instantiate1 a t))
        (instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) m =
      Expr.lam (instSeq as (t - 1) (d.instantiate1 a t))
        (instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

/-! ## The closed spellings, instantiated -/

/-- A bound variable below every cut of a closed-argument sequence is
untouched. -/
theorem instSeq_bvar_lt (args : List Expr) (t j : Nat) (h : j + args.length ≤ t) :
    instSeq args t (.bvar j) = .bvar j :=
  instSeq_eq_self_of_bounded args t (k := j + 1) (by simp [looseBVarsBounded]) (by omega)

/-- The parameter spine `p⃗`, as seen from under `o` binders,
instantiated at a sequence whose first `nP` entries are the
parameters' values. -/
theorem map_instSeq_structPsAt (sp : List Expr) (o nP : Nat)
    (hcl : ∀ a ∈ sp, a.looseBVarsBounded 0 = true) (hlen : nP ≤ sp.length) :
    (structPsAt o nP).map (instSeq sp (o + nP - 1)) = sp.take nP := by
  apply List.ext_getElem
  · simp [structPsAt, hlen]
  · intro k h1 h2
    have hk : k < nP := by simpa [structPsAt] using h1
    simp only [structPsAt, List.getElem_map, List.getElem_range, List.getElem_take]
    have := instSeq_bvar sp (o + nP - 1) (o + nP - 1 - k) hcl (by omega) (by omega)
    rw [show o + nP - 1 - (o + nP - 1 - k) = k from by omega,
      List.getElem?_eq_getElem (by omega)] at this
    exact (Option.some.inj this).symm

/-- The field spine `f⃗`, instantiated at the field variables. -/
theorem map_instSeq_fieldBvars (xFvs : List Expr) (nF : Nat)
    (hcl : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true) (hlen : xFvs.length = nF) :
    ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)).map (instSeq xFvs (nF - 1)) = xFvs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k h1 h2
    have hk : k < nF := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    have := instSeq_bvar xFvs (nF - 1) (nF - 1 - k) hcl (by omega) (by omega)
    rw [show nF - 1 - (nF - 1 - k) = k from by omega,
      List.getElem?_eq_getElem (by omega)] at this
    exact (Option.some.inj this).symm

/-- The field spine is untouched by a sequence whose cuts all sit
above it. -/
theorem map_instSeq_fieldBvars_above (sp : List Expr) (t nF : Nat)
    (h : nF + sp.length ≤ t + 1) :
    ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)).map (instSeq sp t)
      = (List.range nF).map fun j => Expr.bvar (nF - 1 - j) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk' : k < nF := List.mem_range.mp hk
  simp only [Function.comp_def]
  exact instSeq_bvar_lt sp t (nF - 1 - k) (by omega)

/-- **The constructor telescope under the motive**: the field
telescope of `cty` (`cty.stripPis nP`'s body), lifted under `o`
binders, instantiated at the parameter variables followed by the
`o` extra variables, is the field telescope instantiated at the
parameter variables alone (`instSeq_liftLooseBVars_prefix`). -/
theorem instSeq_minorTele (tfvs extras : List Expr) {nP : Nat} {crest0 : Expr}
    (hlenT : tfvs.length = nP) (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hb : crest0.looseBVarsBounded nP = true) :
    instSeq (tfvs ++ extras) (nP + extras.length - 1) (crest0.liftLooseBVars extras.length 0)
      = instSeq tfvs (nP - 1) crest0 := by
  have := instSeq_liftLooseBVars_prefix tfvs extras hclT (by rw [hlenT]; exact hb)
  rwa [hlenT] at this

/-! ## The generated forms at one constructor -/

/-! ## No projection nodes -/

namespace Expr

variable {T : Name} {i : Nat}

theorem NoProjAt.liftLooseBVars {k : Nat} :
    ∀ {e : Expr} {c : Nat}, NoProjAt T i e → NoProjAt T i (e.liftLooseBVars k c) := by
  intro e
  induction e with
  | bvar j => intro c _; simp only [Expr.liftLooseBVars]; split <;> simp
  | fvar idx ty ih => intro c h; simpa [Expr.liftLooseBVars] using h
  | sort u => intro c _; simp [Expr.liftLooseBVars]
  | const n us => intro c _; simp [Expr.liftLooseBVars]
  | lit l => intro c _; simp [Expr.liftLooseBVars]
  | app f a ihf iha =>
    intro c h
    rw [noProjAt_app] at h
    simp only [Expr.liftLooseBVars, noProjAt_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro c h
    rw [noProjAt_lam] at h
    simp only [Expr.liftLooseBVars, noProjAt_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro c h
    rw [noProjAt_forallE] at h
    simp only [Expr.liftLooseBVars, noProjAt_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro c h
    rw [noProjAt_letE] at h
    simp only [Expr.liftLooseBVars, noProjAt_letE]
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s j e ih =>
    intro c h
    rw [noProjAt_proj] at h
    simp only [Expr.liftLooseBVars, noProjAt_proj]
    exact ⟨h.1, ih h.2⟩

theorem NoProjAt.mkAppN :
    ∀ {as : List Expr} {f : Expr}, NoProjAt T i f → (∀ a ∈ as, NoProjAt T i a) →
      NoProjAt T i (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    simp only [Expr.mkAppN]
    exact NoProjAt.mkAppN (by rw [noProjAt_app]; exact ⟨hf, has a List.mem_cons_self⟩)
      (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))

theorem NoProjAt.stripPis :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis k = some (bs, body) → NoProjAt T i e → NoProjAt T i body
  | 0, e, bs, body, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact he
  | k + 1, e, bs, body, h, he => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.stripPis] at h
      cases hs : rest.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rw [noProjAt_forallE] at he
        exact NoProjAt.stripPis k hs he.2
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

theorem NoProjAt.replacePisPw {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr}, Expr.replacePisPw pw k e b = some r →
      NoProjAt T i e → NoProjAt T i b → NoProjAt T i r
  | 0, e, b, r, h, _, hb => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    rw [← h]; exact hb
  | k + 1, e, b, r, h, he, hb => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      rw [noProjAt_forallE] at he ⊢
      exact ⟨he.1, NoProjAt.replacePisPw k hr' he.2 hb⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.replacePisPw] at h

theorem NoProjAt.pisToLamsPw {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr}, Expr.pisToLamsPw pw k e b = some r →
      NoProjAt T i e → NoProjAt T i b → NoProjAt T i r
  | 0, e, b, r, h, _, hb => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at h
    rw [← h]; exact hb
  | k + 1, e, b, r, h, he, hb => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      rw [noProjAt_forallE] at he
      rw [noProjAt_lam]
      exact ⟨he.1, NoProjAt.pisToLamsPw k hr' he.2 hb⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.pisToLamsPw] at h

theorem NoProjAt.structPsAt (o nP : Nat) : ∀ a ∈ structPsAt o nP, NoProjAt T i a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  simp

theorem NoProjAt.structCtorSpineAt (C : Name) (lps : List Name) (o nP nF : Nat) :
    NoProjAt T i (structCtorSpineAt C lps o nP nF) := by
  unfold ConLeche.structCtorSpineAt
  refine NoProjAt.mkAppN (by simp) ?_
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact NoProjAt.structPsAt _ _ a h
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
    simp

end Expr

end ConLeche
