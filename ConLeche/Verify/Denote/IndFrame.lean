module

public import ConLeche.Verify.Denote.Tele
public import ConLeche.Verify.Denote.TeleOpen
public import ConLeche.Verify.InferLeaves

public section

/-!
# The opened-statement frame: towers, spines, and the cross-frame walk

Relocated verbatim from `ConLeche/TTVerify/IndBottom.lean` (task #148,
T5): the pure denote/`Term` tier of the modeled-iota bottoms' frame
machinery — `PiTele` (a `.pi` tower's domains as a de Bruijn context),
`ctxInstAt`, the opened-telescope walks (`openPisAtFvars_leaves`,
`openPisAtFvars_denoteTele`), the `instSeq`/`instRevChain` algebra,
the cross-frame instantiation (`instPisAt_denote_cross` — the
load-bearing "instantiate-then-denote = denote-then-instantiate"
identity), the spine-reading lemmas, and `lamCtx`.  All V-free and
`Deq`- and judgment-free; both verification lanes' bottoms consume them.
The namespace stays `ConLeche.Verify` so no call site moves.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- Indexing a list by its own `range` is mapping it. -/
theorem map_range_getD {α β : Type} [Inhabited α] (xs : List α)
    (g : α → β) :
    (List.range xs.length).map (fun l => g (xs.getD l default)) = xs.map g := by
  refine List.ext_getElem? ?_
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem?_range h, List.getElem?_eq_getElem h]
    simp [List.getD, List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
    rfl

/-- A closed inhabitant of... nothing — a closed **term of type
`Prop`**: `∀ p : Prop, p`.  (`False`, in fact, which is fine: only its
*typing* is consumed.) -/
@[expose] def dummyPropT : Term := .pi (.sort 0) (.bvar 0)


/-- The first `k` domains of a `.pi` tower, as a de Bruijn context —
innermost binder first, so the *outermost* domain is the last entry —
with the body after `k` binders.  Each entry is as written in the
tower, its dependencies pointing at the entries after it, which is
exactly how a de Bruijn variable rule reads a context. -/
inductive PiTele : Nat → Term → List Term → Term → Prop
  | nil {T : Term} : PiTele 0 T [] T
  | cons {k : Nat} {A B R : Term} {Γ : List Term} :
      PiTele k B Γ R → PiTele (k + 1) (.pi A B) (Γ ++ [A]) R

theorem PiTele.length : ∀ {k : Nat} {T : Term} {Γ : List Term}
    {R : Term}, PiTele k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A context's entries, instantiated after a variable *below* all of
them is substituted: the entry `i` places above the substituted slot is
instantiated at cut `j + i` (`j` counts binders below the substituted
slot that remain).  The entry adjacent to the slot — the list's last —
gets cut `j`. -/
@[expose] def ctxInstAt (v : Term) (j : Nat) : List Term → List Term
  | [] => []
  | B :: Γ => B.inst v (j + Γ.length) :: ctxInstAt v j Γ

@[simp] theorem ctxInstAt_nil (v : Term) (j : Nat) :
    ctxInstAt v j [] = [] := rfl

theorem ctxInstAt_cons (v : Term) (j : Nat) (B : Term) (Γ : List Term) :
    ctxInstAt v j (B :: Γ) = B.inst v (j + Γ.length) :: ctxInstAt v j Γ := by rfl

/-- `ctxInstAt` over an append: the left block's cuts shift by the
right block's length. -/
theorem ctxInstAt_append (v : Term) (j : Nat) :
    ∀ (Γ₁ Γ₂ : List Term),
      ctxInstAt v j (Γ₁ ++ Γ₂) =
        ctxInstAt v (j + Γ₂.length) Γ₁ ++ ctxInstAt v j Γ₂
  | [], Γ₂ => rfl
  | B :: Γ₁, Γ₂ => by
    simp only [List.cons_append, ctxInstAt_cons, ctxInstAt_append v j Γ₁ Γ₂,
      List.length_append, List.cons.injEq]
    exact ⟨by congr 1; omega, trivial⟩

/-- The snoc form `PiTele.cons` and `CtxSpine.cons` decompose along. -/
theorem ctxInstAt_snoc (v : Term) (j : Nat) (Γ : List Term) (A : Term) :
    ctxInstAt v j (Γ ++ [A]) = ctxInstAt v (j + 1) Γ ++ [A.inst v j] := by
  rw [ctxInstAt_append]
  rfl

/-- A substituted tower is a tower over the substituted context — the
`PiTele` transcription of `PiTower.inst`. -/
theorem PiTele.inst : ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
    PiTele k T Γ R → ∀ (v : Term) (j : Nat),
      PiTele k (T.inst v j) (ctxInstAt v j Γ) (R.inst v (j + k)) := by
  intro k T Γ R h
  induction h with
  | nil => intro v j; simpa using PiTele.nil
  | @cons k A B R Γ _ ih =>
    intro v j
    rw [Term.inst_pi, ctxInstAt_snoc]
    have h1 := ih v (j + 1)
    rw [show j + 1 + k = j + (k + 1) from by omega] at h1
    exact PiTele.cons h1

/-- Every free-variable leaf reachable from an opened telescope — from
the opened body or from any opener's own annotation — is either a leaf
of the unopened expression or exactly one of the openers.  With the
subject closed, the openers are a *leaf-closed* set: annotations
mention only earlier openers, which are openers again. -/
theorem openPisAtFvars_leaves :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
        l ∈ e.fvarLeaves ∨ Expr.fvar l.1 l.2 ∈ fvs := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h l hl
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with hl | ⟨x, hx, -⟩
    · exact Or.inl hl
    · exact nomatch hx
  | succ k ih =>
    intro e d fvs body h l hl
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
        -- a leaf of the head opener resolves directly
        have head : l ∈ (Expr.fvar d dom).fvarLeaves →
            l ∈ (Expr.forallE dom bodyE mb).fvarLeaves ∨
              Expr.fvar l.1 l.2 ∈
                Expr.fvar d dom :: p.1 := by
          intro hl'
          rw [Expr.fvarLeaves] at hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact Or.inr (List.mem_cons_self ..)
          · refine Or.inl ?_
            rw [Expr.fvarLeaves]
            exact List.mem_append_left _ hl'
        rcases hl with hl | ⟨x, hx, hlx⟩
        · rcases ih hop l (Or.inl hl) with hl' | hl'
          · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
            · refine Or.inl ?_
              rw [Expr.fvarLeaves]
              exact List.mem_append_right _ h1
            · exact head h1
          · exact Or.inr (List.mem_cons_of_mem _ hl')
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact head hlx
          · rcases ih hop l (Or.inr ⟨x, hx', hlx⟩) with hl' | hl'
            · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
              · refine Or.inl ?_
                rw [Expr.fvarLeaves]
                exact List.mem_append_right _ h1
              · exact head h1
            · exact Or.inr (List.mem_cons_of_mem _ hl')

/-- **The opening walk, denoted.**  Opening a telescope whose denote
succeeds yields the `.pi` tower's context, the denoted opened body, and
each opener's annotation denoted *at its own depth* to its tower
entry.  (Consumers lift with `denote_lift`; the entry `Γ.getD (k-1-i)`
is the `i`-th binder's domain as written, which is where a variable
rule wants it.) -/
theorem openPisAtFvars_denoteTele {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} :
    ∀ (k : Nat) {e : Expr} {j : Nat} {fvs : List Expr} {body : Expr}
      {T : Term},
      openPisAtFvars k e j = some (fvs, body) →
      denote cval env ψ j e = some T →
      ∃ (Γ : List Term) (R : Term),
        PiTele k T Γ R ∧
        denote cval env ψ (j + k) body = some R ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          denote cval env ψ (j + i) (Expr.fvarTypeD x) =
            some (Γ.getD (k - 1 - i) default) := by
  intro k
  induction k with
  | zero =>
    intro e j fvs body T h hT
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], T, .nil, hT, fun i x hx => nomatch hx⟩
  | succ k ih =>
    intro e j fvs body T h hT
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar j dom))
          (j + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [denote_forallE] at hT
        cases hA : denote cval env ψ j dom with
        | none => rw [hA] at hT; exact nomatch hT
        | some A => ?_
        rw [hA] at hT
        cases hB : denote cval env ψ (j + 1)
            (bodyE.instantiate1 (.fvar j dom)) with
        | none => rw [hB] at hT; exact nomatch hT
        | some B => ?_
        rw [hB] at hT
        obtain rfl : T = .pi A B := (Option.some.inj hT).symm
        obtain ⟨Γ', R, htele, hbody, hdoms⟩ := ih hop hB
        have hΓlen : Γ'.length = k := htele.length
        refine ⟨Γ' ++ [A], R, .cons htele, ?_, ?_⟩
        · rw [show j + (k + 1) = j + 1 + k from by omega]
          exact hbody
        · intro i x hx
          cases i with
          | zero =>
            obtain rfl : Expr.fvar j dom = x := by
              simpa using hx
            show denote cval env ψ (j + 0) dom = _
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
              simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
              rw [List.getElem?_append_right (by omega), hΓlen,
                Nat.sub_self]
              rfl]
            exact hA
          | succ i =>
            rw [List.getElem?_cons_succ] at hx
            have h1 := hdoms i x hx
            have hik : i < k := by
              rcases Nat.lt_or_ge i k with h' | h'
              · exact h'
              · exfalso
                rw [List.getElem?_eq_none (by
                  have := openPisAtFvars_stripPis k hop
                  obtain ⟨-, -, -, hlen, -, -⟩ := this
                  omega)] at hx
                exact nomatch hx
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default =
                Γ'.getD (k - 1 - i) default from by
              simp only [List.getD]
              rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
                List.getElem?_append_left (by omega)]]
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h1

/-- `ctxInstAt`, per entry: the entry at index `i` is instantiated at
its own residual depth. -/
theorem ctxInstAt_getD (v : Term) (j : Nat) :
    ∀ (Γ : List Term) (i : Nat), i < Γ.length →
      (ctxInstAt v j Γ).getD i default =
        (Γ.getD i default).inst v (j + Γ.length - 1 - i)
  | [], i, h => absurd h (by simp)
  | B :: Γ, 0, _ => by
    simp only [ctxInstAt_cons, List.getD_cons_zero, List.length_cons,
      Nat.sub_zero]
    congr 1
  | B :: Γ, i + 1, h => by
    simp only [ctxInstAt_cons, List.getD_cons_succ, List.length_cons]
    rw [ctxInstAt_getD v j Γ i (by simpa using h)]
    congr 1
    omega

/-- The tower, truncated: the first `n` binders with the inner tower as
their body. -/
theorem PiTele.prefix :
    ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
      PiTele k T Γ R → ∀ n, n ≤ k →
      ∃ mid, PiTele n T (Γ.drop (k - n)) mid ∧
        PiTele (k - n) mid (Γ.take (k - n)) R := by
  intro k T Γ R h
  induction h with
  | nil =>
    intro n hn
    obtain rfl : n = 0 := by omega
    exact ⟨_, .nil, .nil⟩
  | @cons k A B R Γ hp ih =>
    intro n hn
    cases n with
    | zero =>
      refine ⟨.pi A B, ?_, ?_⟩
      · rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp [hp.length])]
        exact .nil
      · rw [Nat.sub_zero, List.take_of_length_le (by simp [hp.length])]
        exact .cons hp
    | succ n =>
      obtain ⟨mid, h1, h2⟩ := ih n (by omega)
      have he : k + 1 - (n + 1) = k - n := by omega
      refine ⟨mid, ?_, ?_⟩
      · rw [he, List.drop_append_of_le_length (by rw [hp.length]; omega)]
        exact .cons h1
      · rw [he, List.take_append_of_le_length (by rw [hp.length]; omega)]
        exact h2

/-- The context's λ-tower over a subject: the outermost binder is the
context's last entry, matching `CtxSpine`'s peel. -/
@[expose] def lamCtx (Γ : List Term) (C : Term) : Term :=
  Γ.foldl (fun acc A => .lam A acc) C

theorem lamCtx_cons (B : Term) (Γ : List Term) (C : Term) :
    lamCtx (B :: Γ) C = lamCtx Γ (.lam B C) := by rfl

theorem lamCtx_snoc (Γ : List Term) (A C : Term) :
    lamCtx (Γ ++ [A]) C = .lam A (lamCtx Γ C) := by
  unfold lamCtx
  rw [List.foldl_append]
  rfl

theorem lamCtx_inst : ∀ (Γ : List Term) (C v : Term) (j : Nat),
    (lamCtx Γ C).inst v j =
      lamCtx (ctxInstAt v j Γ) (C.inst v (j + Γ.length))
  | [], C, v, j => by simp [lamCtx, ctxInstAt]
  | B :: Γ, C, v, j => by
    rw [lamCtx_cons, lamCtx_inst Γ (.lam B C) v j, ctxInstAt_cons,
      lamCtx_cons, Term.inst_lam]
    congr 2

/-- The checker's opener, read as an `instPisAt` at its own variables:
the returned domains are the opened annotations. -/
theorem openPisAtFvars_instPisAt :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      Expr.instPisAt fvs e = some (fvs.map Expr.fvarTypeD, body) := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
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
        show (Expr.instPisAt p.1 (bodyE.instantiate1
          (Expr.fvar d dom))).map _ = _
        rw [ih hop]
        rfl

/-- `instPisAt` outputs at `RenEqT`-related inputs are `RenEqT`-related,
pointwise on the domains and on the residual. -/
theorem instPisAt_renEq {f : Name → Name} :
    ∀ (as as' : List Expr) {ty ty' : Expr} {ds ds' : List Expr}
      {rs rs' : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt as' ty' = some (ds', rs') →
      RenEqT f ty ty' →
      (∀ (i : Nat) (a a' : Expr), as[i]? = some a → as'[i]? = some a' →
        RenEqT f a a') →
      as.length = as'.length →
      (∀ (i : Nat) (x x' : Expr), ds[i]? = some x → ds'[i]? = some x' →
        RenEqT f x x') ∧ RenEqT f rs rs' := by
  intro as
  induction as with
  | nil =>
    intro as' ty ty' ds ds' rs rs' h h' hty _ hlen
    obtain rfl : as' = [] := by
      cases as' with
      | nil => rfl
      | cons _ _ => exact nomatch hlen
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨(fun i x x' hx _ => nomatch hx), hty⟩
  | cons a as ih =>
    intro as' ty ty' ds ds' rs rs' h h' hty hargs hlen
    cases as' with
    | nil => exact nomatch hlen
    | cons a' as'' => ?_
    match ty, h with
    | .forallE d₁ b₁ m₁, h => ?_
    match ty', h' with
    | .forallE d₂ b₂ m₂, h' => ?_
    have hty' : (m₁ = m₂ ∧ Expr.ErasedEq (d₁.renameConsts f) d₂ ∧
        Expr.ErasedEq (b₁.renameConsts f) b₂) := by
      have h0 : Expr.ErasedEq
          (Expr.forallE (d₁.renameConsts f) (b₁.renameConsts f) m₁)
          (.forallE d₂ b₂ m₂) := hty
      simpa [Expr.ErasedEq] using h0
    obtain ⟨-, hdom, hbody⟩ := hty'
    simp only [Expr.instPisAt] at h h'
    cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    cases h2 : Expr.instPisAt as'' (b₂.instantiate1 a') with
    | none => rw [h2] at h'; exact nomatch h'
    | some p2 => ?_
    rw [h1] at h
    rw [h2] at h'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    have hrec : RenEqT f (b₁.instantiate1 a) (b₂.instantiate1 a') :=
      RenEqT.instantiate1 hbody (hargs 0 a a' rfl rfl)
    obtain ⟨hds, hrs⟩ := ih as'' h1 h2 hrec
      (fun i x x' hx hx' => hargs (i + 1) x x' (by simpa using hx)
        (by simpa using hx'))
      (by simpa using hlen)
    refine ⟨?_, hrs⟩
    intro i x x' hx hx'
    cases i with
    | zero =>
      obtain rfl : d₁ = x := by simpa using hx
      obtain rfl : d₂ = x' := by simpa using hx'
      exact hdom
    | succ i =>
      exact hds i x x' (by simpa using hx) (by simpa using hx')

/-- Every leaf reachable from an `instPisAt` run — from any returned
domain or from the residual — is a leaf of the subject or of a spine
entry. -/
theorem instPisAt_leaves :
    ∀ (as : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      ∀ l, ((∃ x ∈ ds, l ∈ x.fvarLeaves) ∨ l ∈ rs.fvarLeaves) →
        l ∈ ty.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil =>
    intro ty ds rs h l hl
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with ⟨x, hx, -⟩ | hl
    · exact nomatch hx
    · exact Or.inl hl
  | cons a as ih =>
    intro ty ds rs h l hl
    match ty, h with
    | .forallE d₁ b₁ m₁, h => ?_
    simp only [Expr.instPisAt] at h
    cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    rw [h1] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have step : l ∈ (b₁.instantiate1 a).fvarLeaves ∨
        (l ∈ (Expr.forallE d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves) → _ := fun h => h
    have push : l ∈ (b₁.instantiate1 a).fvarLeaves →
        l ∈ (Expr.forallE d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves := by
      intro hb
      rcases Expr.fvarLeaves_instantiate1 b₁ 0 hb with hb' | hb'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_right _ hb'
      · exact Or.inr ⟨a, List.mem_cons_self .., hb'⟩
    rcases hl with ⟨x, hx, hlx⟩ | hl
    · rcases List.mem_cons.mp hx with rfl | hx'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_left _ hlx
      · rcases ih h1 l (Or.inl ⟨x, hx', hlx⟩) with h2 | ⟨b, hb, hlb⟩
        · exact push h2
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩
    · rcases ih h1 l (Or.inr hl) with h2 | ⟨b, hb, hlb⟩
      · exact push h2
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩

/-- Opening keeps everything at loose-bvar level zero: the body and
each opener's annotation. -/
theorem openPisAtFvars_bounded :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      e.looseBVarsBounded 0 = true →
      body.looseBVarsBounded 0 = true ∧
        ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h hb
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hb, fun x hx => nomatch hx⟩
  | succ k ih =>
    intro e d fvs body h hb
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
        have hb' : dom.looseBVarsBounded 0 = true ∧
            bodyE.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        obtain ⟨hbody, hanns⟩ := ih hop
          (looseBVarsBounded_instantiate1 bodyE 0 hb'.2)
        refine ⟨hbody, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hanns x hx'

/-- `instPisAt`, truncated at a spine prefix: the first `n` domains and
the telescope that remains. -/
theorem instPisAt_take :
    ∀ (sp : List Expr) (n : Nat) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∃ mid, Expr.instPisAt (sp.take n) ty = some (ds.take n, mid) ∧
        Expr.instPisAt (sp.drop n) mid = some (ds.drop n, rs) := by
  intro sp
  induction sp with
  | nil =>
    intro n ty ds rs h
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ty, by simp [Expr.instPisAt], by simp [Expr.instPisAt]⟩
  | cons a sp ih =>
    intro n ty ds rs h
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases n with
        | zero =>
          refine ⟨.forallE dom body mb, by simp [Expr.instPisAt], ?_⟩
          simp only [List.drop_zero, Expr.instPisAt, h1]
          rfl
        | succ n =>
          obtain ⟨mid, h2, h3⟩ := ih n h1
          refine ⟨mid, ?_, by simpa using h3⟩
          simp only [List.take_succ_cons, Expr.instPisAt, h2]
          rfl

/-- `instPisAt` keeps everything at loose-bvar level zero. -/
theorem instPisAt_bounded :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ty.looseBVarsBounded 0 = true →
      (∀ a ∈ sp, a.looseBVarsBounded 0 = true) →
      (∀ x ∈ ds, x.looseBVarsBounded 0 = true) ∧
        rs.looseBVarsBounded 0 = true := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h hb _
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hb⟩
  | cons a sp ih =>
    intro ty ds rs h hb hsp
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb' : dom.looseBVarsBounded 0 = true ∧
            body.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        obtain ⟨hds, hrs⟩ := ih h1
          (Expr.looseBVarsBounded_instantiate1_gen
            (hsp a List.mem_cons_self) hb'.2)
          (fun b hb2 => hsp b (List.mem_cons_of_mem _ hb2))
        refine ⟨?_, hrs⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hds x hx'

/-- A subject with only low bound variables passes through `instSeq`
untouched: every cut is above its range. -/
theorem Term.instSeq_eq_self_of_bvarsBelow :
    ∀ (vs : List Term) (t : Nat) {X : Term} {m : Nat},
      Term.bvarsBelow m X → m + vs.length ≤ t + 1 →
      Term.instSeq vs t X = X
  | [], _, _, _, _, _ => rfl
  | a :: vs, t, X, m, hb, h => by
    show Term.instSeq vs (t - 1) (X.inst a t) = _
    rw [Term.inst_eq_self (Term.bvarsBelow.mono (by
      simp only [List.length_cons] at h
      omega) hb)]
    cases t with
    | zero =>
      obtain rfl : vs = [] := by
        simp only [List.length_cons] at h
        exact List.eq_nil_of_length_eq_zero (by omega)
      rfl
    | succ t' =>
      exact Term.instSeq_eq_self_of_bvarsBelow vs t' hb (by
        simp only [List.length_cons] at h
        omega)

/-- Equal applications of equal arity have equal heads and spines. -/
theorem Term.mkAppN_inj :
    ∀ {as bs : List Term} {f g : Term},
      Term.mkAppN f as = Term.mkAppN g bs → as.length = bs.length →
      f = g ∧ as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs f g h hlen
    obtain rfl : bs = [] :=
      List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨h, rfl⟩
  | cons a as ih =>
    intro bs f g h hlen
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      rw [Term.mkAppN_cons, Term.mkAppN_cons] at h
      obtain ⟨h1, rfl⟩ := ih h (by simpa using hlen)
      injection h1 with h2 h3
      exact ⟨h2, by rw [h3]⟩

/-- Substituting a *variable* never changes an application's arity: the
inserted value is atomic, so no application node is created or
absorbed. -/
theorem Expr.getAppArgs_length_instantiate1_fvar {i : Nat}
    {t : Expr} :
    ∀ (e : Expr) (k : Nat),
      ((e.instantiate1 (.fvar i t) k).getAppArgs).length =
        e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    simp only [Expr.instantiate1, Expr.getAppArgs, List.length_append]
    rw [ihg k]
    rfl
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; first | rfl | (simp only [Expr.instantiate1]; rfl)

/-- Renaming constants never changes an application's arity. -/
theorem Expr.getAppArgs_length_renameConsts (f : Name → Name) :
    ∀ (e : Expr),
      ((e.renameConsts f).getAppArgs).length = e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.renameConsts, Expr.getAppArgs, List.length_append]
    rw [ihg]
    rfl
  | _ => first | rfl | (simp only [Expr.renameConsts]; rfl)

/-- An `instPisAt` run at variables lands at the raw telescope
residual's arity. -/
theorem instPisAt_fvar_residual_arity :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      (∀ x ∈ sp, ∃ i t, x = Expr.fvar i t) →
      ∀ {bs : List (Expr × BinderMeta)} {body : Expr},
        ty.stripPis sp.length = some (bs, body) →
        rs.getAppArgs.length = body.getAppArgs.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h _ bs body hstrip
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip' : (some ([], ty) :
        Option (List (Expr × BinderMeta) × Expr)) = some (bs, body) :=
      hstrip
    simp only [Option.some.injEq, Prod.mk.injEq] at hstrip'
    rw [hstrip'.2]
  | cons a sp ih =>
    intro ty ds rs h hsp bs body hstrip
    obtain ⟨i, t, rfl⟩ := hsp a List.mem_cons_self
    match ty, h with
    | .forallE dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1 (.fvar i t)) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons, Expr.stripPis] at hstrip
      cases h2 : bodyE.stripPis sp.length with
      | none => rw [h2] at hstrip; exact nomatch hstrip
      | some q => ?_
      rw [h2] at hstrip
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨-, rfl⟩ := hstrip
      -- the instantiated body strips to the instantiated residual
      have h3 : ((bodyE.instantiate1
          (.fvar i t)).stripPis sp.length).isSome = true :=
        Expr.stripPis_instantiate1_isSome sp.length 0 (by rw [h2]; rfl)
      obtain ⟨⟨bs', body'⟩, h4⟩ := Option.isSome_iff_exists.mp h3
      obtain ⟨hbody', -⟩ := Expr.stripPis_instantiate1_eq sp.length 0 h2 h4
      have h5 := ih h1 (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) h4
      rw [h5, hbody', Nat.zero_add,
        Expr.getAppArgs_length_instantiate1_fvar]

/-- Substituting under a constant-headed application never changes its
arity (the head cannot be hit, so no application node is created or
absorbed). -/
theorem Expr.getAppArgs_length_instantiate1_const {c : Name}
    {cus : List Level} {v : Expr} :
    ∀ (e : Expr) (k : Nat), e.getAppFn = .const c cus →
      ((e.instantiate1 v k).getAppArgs).length = e.getAppArgs.length ∧
      (e.instantiate1 v k).getAppFn = .const c cus := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k hh
    have hgh : g.getAppFn = .const c cus := by
      simpa [Expr.getAppFn] using hh
    obtain ⟨h1, h2⟩ := ihg k hgh
    simp only [Expr.instantiate1, Expr.getAppArgs, List.length_append]
    refine ⟨by rw [h1]; rfl, ?_⟩
    simpa [Expr.getAppFn] using h2
  | const n us =>
    intro k hh
    exact ⟨rfl, hh⟩
  | bvar j =>
    intro k hh
    exact nomatch hh
  | _ =>
    intro k hh
    first
    | exact nomatch hh
    | exact ⟨rfl, hh⟩

/-- Level instantiation never changes an application's arity. -/
theorem Expr.getAppArgs_length_instantiateLevelParams
    (ks : List Name) (us : List Level) :
    ∀ (e : Expr),
      ((e.instantiateLevelParams ks us).getAppArgs).length =
        e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs,
      List.length_append]
    rw [ihg]
    rfl
  | _ => first | rfl | (simp only [Expr.instantiateLevelParams]; rfl)

/-- An `instPisAt` run over any spine lands at the raw telescope
residual's arity, provided the residual is constant-headed (the
nested runs' spines hold pin instantiations, not variables). -/
theorem instPisAt_residual_arity_const {c : Name} {cus : List Level} :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {bs : List (Expr × BinderMeta)} {body : Expr},
        ty.stripPis sp.length = some (bs, body) →
        body.getAppFn = .const c cus →
        rs.getAppArgs.length = body.getAppArgs.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h bs body hstrip hhead
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip' : (some ([], ty) :
        Option (List (Expr × BinderMeta) × Expr)) = some (bs, body) :=
      hstrip
    simp only [Option.some.injEq, Prod.mk.injEq] at hstrip'
    rw [hstrip'.2]
  | cons a sp ih =>
    intro ty ds rs h bs body hstrip hhead
    match ty, h with
    | .forallE dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons, Expr.stripPis] at hstrip
      cases h2 : bodyE.stripPis sp.length with
      | none => rw [h2] at hstrip; exact nomatch hstrip
      | some q => ?_
      rw [h2] at hstrip
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨-, rfl⟩ := hstrip
      have h3 : ((bodyE.instantiate1 a).stripPis sp.length).isSome
          = true :=
        Expr.stripPis_instantiate1_isSome sp.length 0 (by rw [h2]; rfl)
      obtain ⟨⟨bs', body'⟩, h4⟩ := Option.isSome_iff_exists.mp h3
      obtain ⟨hbody', -⟩ := Expr.stripPis_instantiate1_eq sp.length 0 h2 h4
      have hhead' : body'.getAppFn = .const c cus := by
        rw [hbody', Nat.zero_add]
        exact (Expr.getAppArgs_length_instantiate1_const _ _ hhead).2
      have h5 := ih h1 h4 hhead'
      rw [h5, hbody', Nat.zero_add,
        (Expr.getAppArgs_length_instantiate1_const _ _ hhead).1]

/-- The application head under constant renaming. -/
theorem Expr.getAppFn_renameConsts (f : Name → Name) :
    ∀ (e : Expr),
      (e.renameConsts f).getAppFn = (e.getAppFn).renameConsts f := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.renameConsts, Expr.getAppFn]
    exact ihg
  | _ => rfl

/-- The application head under level instantiation. -/
theorem Expr.getAppFn_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr),
      (e.instantiateLevelParams ks us).getAppFn =
        (e.getAppFn).instantiateLevelParams ks us := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppFn]
    exact ihg
  | _ => rfl

/-- Renaming constants never changes loose-bvar levels. -/
theorem Expr.looseBVarsBounded_renameConsts (f : Name → Name) :
    ∀ (e : Expr) (k : Nat),
      Expr.looseBVarsBounded k (e.renameConsts f) =
        Expr.looseBVarsBounded k e := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.renameConsts, Expr.looseBVarsBounded]

/-- One domain per argument. -/
theorem instPisAt_length :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) → ds.length = sp.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | cons a sp ih =>
    intro ty ds rs h
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ih h1]

/-- An `instPisAt` run at frame variables of a denoting subject has a
denoting residual — the definedness half of
`instPisAt_denote_cross`. -/
theorem instPisAt_fvar_denote_defined {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} (hcl : ∀ n ψ', Term.Closed (cval n ψ')) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat},
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        (∃ w, denote cval env ψ D x = some w) ∧ Expr.WScoped D x ∧
          x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : Term}, denote cval env ψ D ty = some T →
      ∃ vRs, denote cval env ψ D rs = some vRs := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D _ _ _ T hT
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨T, hT⟩
  | cons a sp ih =>
    intro ty ds rs h D hsp hfb hb T hT
    obtain ⟨⟨w0, hw0⟩, hwsa, hba⟩ := hsp 0 a rfl
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp
          (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denote_forallE] at hT
      cases hA : denote cval env ψ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denote cval env ψ (D + 1)
          (body.instantiate1 (.fvar D dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      have hTI : denote cval env ψ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [denote_beta (ty := dom) hcl hfb'.2 hwsa hba
          hw0 0, hB]
        rfl
      exact ih h1
        (fun j x hx => hsp (j + 1) x (by simpa using hx))
        (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
        (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2) hTI

/-- Renaming constants preserves scoping: it touches `const` heads and
`proj` structure names, never `fvar` indices or `bvar`s (task #148,
T6, prospective relocation — the TT lane's renamed walks want this
too). -/
theorem wscoped_renameConsts {f : Name → Name} :
    ∀ (e : Expr) {d : Nat},
      Expr.WScoped d e → Expr.WScoped d (e.renameConsts f) := by
  intro e
  induction e <;> intro d h <;>
    simp_all [Expr.renameConsts, Expr.WScoped]

/-- Renaming rewrites each leaf's *annotation* and nothing else — the
indices are untouched. -/
theorem fvarLeaves_renameConstsE {f : Name → Name} :
    ∀ (e : Expr), (e.renameConsts f).fvarLeaves
      = e.fvarLeaves.map
        (fun l => (l.1, l.2.renameConsts f)) := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.fvarLeaves]

/-- …so renaming preserves the leaf-annotation bound, by
`looseBVarsBounded_renameConsts` at each leaf. -/
theorem leavesBounded_renameConsts {f : Name → Name} (e : Expr)
    (h : Expr.LeavesBounded e) :
    Expr.LeavesBounded (e.renameConsts f) := by
  intro l hl
  rw [fvarLeaves_renameConstsE] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
  rw [Expr.looseBVarsBounded_renameConsts]
  exact h l₀ hl₀

/-- **Every domain an `instPisAt` run collects denotes**, when the
subject does — the list half of `instPisAt_fvar_denote_defined`, and
what the `iota_j` statement walks need per element (task #148, T6:
`DefEqAtW` asserts its two denotations exist, where `DefEqClaimsR`
takes them as inputs). -/
theorem instPisAt_denote_doms {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} (hcl : ∀ n ψ', Term.Closed (cval n ψ')) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat},
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        (∃ w, denote cval env ψ D x = some w) ∧ Expr.WScoped D x ∧
          x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : Term}, denote cval env ψ D ty = some T →
      ∀ d ∈ ds, ∃ v, denote cval env ψ D d = some v := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D _ _ _ T hT
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun d hd => nomatch hd
  | cons a sp ih =>
    intro ty ds rs h D hsp hfb hb T hT
    obtain ⟨⟨w0, hw0⟩, hwsa, hba⟩ := hsp 0 a rfl
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denote_forallE] at hT
      cases hA : denote cval env ψ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denote cval env ψ (D + 1)
          (body.instantiate1 (.fvar D dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      have hTI : denote cval env ψ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [denote_beta (ty := dom) hcl hfb'.2 hwsa hba
          hw0 0, hB]
        rfl
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact ⟨A, hA⟩
      · refine ih h1
          (fun j x hx => hsp (j + 1) x (by simpa using hx))
          (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0
            hfb'.2)
          (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2) hTI d hd'

/-- **The `instPisAt` residual denotes** whenever the subject and the
spine do — `instPisAt_denote_doms`' other half.  `instPisAt_walk_pack`
discards the residual component of every frame lemma it calls; the
λ-row of `IotaWalksR` opens exactly that residual, so it needs the
denotation too (task #148 T6). -/
theorem instPisAt_denote_res {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} (hcl : ∀ n ψ', Term.Closed (cval n ψ')) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat},
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        (∃ w, denote cval env ψ D x = some w) ∧ Expr.WScoped D x ∧
          x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : Term}, denote cval env ψ D ty = some T →
      ∃ v, denote cval env ψ D rs = some v := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D _ _ _ T hT
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨T, hT⟩
  | cons a sp ih =>
    intro ty ds rs h D hsp hfb hb T hT
    obtain ⟨⟨w0, hw0⟩, hwsa, hba⟩ := hsp 0 a rfl
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denote_forallE] at hT
      cases hA : denote cval env ψ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denote cval env ψ (D + 1)
          (body.instantiate1 (.fvar D dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      have hTI : denote cval env ψ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [denote_beta (ty := dom) hcl hfb'.2 hwsa hba
          hw0 0, hB]
        rfl
      exact ih h1 (fun j x hx => hsp (j + 1) x (by simpa using hx))
        (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
        (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2) hTI

/-- **`instLamsAt` preserves `looseBVarsBounded 0`** — the λ-side
mirror of `instPisAt_bounded`, which the λ-row's domain package
needs and which no lane had yet. -/
theorem instLamsAt_bounded :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instLamsAt sp ty = some (ds, rs) →
      ty.looseBVarsBounded 0 = true →
      (∀ a ∈ sp, a.looseBVarsBounded 0 = true) →
      (∀ x ∈ ds, x.looseBVarsBounded 0 = true) ∧
        rs.looseBVarsBounded 0 = true := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h hb _
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hb⟩
  | cons a sp ih =>
    intro ty ds rs h hb hsp
    match ty, h with
    | .lam dom body mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb' : dom.looseBVarsBounded 0 = true ∧
            body.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        obtain ⟨hds, hrs⟩ := ih h1
          (Expr.looseBVarsBounded_instantiate1_gen
            (hsp a List.mem_cons_self) hb'.2)
          (fun b hb2 => hsp b (List.mem_cons_of_mem _ hb2))
        refine ⟨?_, hrs⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hds x hx'

/-- **`instLamsAt`'s domains are scoped at their own index** — the
λ-side mirror of `instPisAt_index_WScoped`.  Domain `i` has only the
spine's first `i` entries substituted into it, so it is scoped at
`d + i` and not merely at the telescope's full height; that grading is
what lets each domain's denotation be *lifted* to a common walk depth
(task #148 T6, `IotaWalksR`'s λ-row). -/
theorem instLamsAt_index_WScoped :
    ∀ (sp : List Expr) {d : Nat} {ty : Expr} {ds : List Expr}
      {rs : Expr},
      Expr.instLamsAt sp ty = some (ds, rs) → Expr.WScoped d ty →
      (∀ (i : Nat) (a : Expr), sp[i]? = some a →
        Expr.WScoped (d + i + 1) a) →
      ∀ (i : Nat) (x : Expr), ds[i]? = some x → Expr.WScoped (d + i) x
  | [], d, ty, ds, rs, h, _, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i x hx
    exact nomatch hx
  | a :: as, d, ty, ds, rs, h, hty, hsp => by
    cases ty with
    | lam dom body mb =>
      simp only [Expr.instLamsAt, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      have hty' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
        simpa [Expr.WScoped] using hty
      have haw : Expr.WScoped (d + 1) a := by
        have h0 := hsp 0 a rfl
        rwa [Nat.add_zero] at h0
      intro i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, Nat.add_zero]
        exact hty'.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have hrec := instLamsAt_index_WScoped as (d := d + 1) hq
          (Expr.WScoped.instantiate1_gen haw 0
            (hty'.2.mono (Nat.le_succ d)))
          (fun k b hb => by
            have h0 := hsp (k + 1) b (by simpa using hb)
            rw [show d + (k + 1) + 1 = d + 1 + k + 1 from by omega]
              at h0
            exact h0) i x hx
        rw [show d + (i + 1) = d + 1 + i from by omega]
        exact hrec
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | forallE _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h

/-- A nonempty tower's head domain is its context's outermost entry. -/
theorem PiTele.head : ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
    PiTele (k + 1) T Γ R →
    ∃ B, T = .pi (Γ.getD k default) B ∧ PiTele k B (Γ.take k) R := by
  intro k T Γ R h
  cases h with
  | @cons _ A B _ Γ' hp =>
    have hlen : Γ'.length = k := hp.length
    refine ⟨B, ?_, ?_⟩
    · have hget : (Γ' ++ [A]).getD k default = A := by
        simp only [List.getD]
        rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        rfl
      rw [hget]
    · rw [List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      exact hp

/-- A denoted spine, built pointwise. -/
theorem DenoteSpine.of_getElem {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List Term}, as.length = vs.length →
      (∀ (q : Nat), q < as.length →
        denote cval env φ d (as.getD q default) =
          some (vs.getD q default)) →
      DenoteSpine cval env φ d as vs := by
  intro as
  induction as with
  | nil =>
    intro vs hlen _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | cons a as ih =>
    intro vs hlen hget
    cases vs with
    | nil => exact nomatch hlen
    | cons v vs =>
      refine DenoteSpine.cons ?_ (ih (by simpa using hlen) ?_)
      · have h0 := hget 0 (by simp)
        simpa using h0
      · intro q hq
        have h1 := hget (q + 1) (by simpa using hq)
        simpa using h1


/-- **The λ-tower, denoted** (`openPisAtFvars_denoteTele`'s mirror for
`stripLams`): a denoting λ-tower is `lamCtx` of its domains' values,
with the body and each raw domain denoted under the anonymous openers
(`openFvars`) — annotations are denote-irrelevant, so any same-index
opener family produces the same values. -/
theorem stripLams_denoteTele {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} :
    ∀ (k : Nat) {e : Expr} {j : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr} {V : Term},
      e.stripLams k = some (bs, body) →
      denote cval env ψ j e = some V →
      ∃ (Γ : List Term) (C : Term),
        V = lamCtx Γ C ∧ Γ.length = k ∧
        denote cval env ψ (j + k)
          (Expr.instSeq (openFvars j k) (k - 1) body) = some C ∧
        ∀ (i0 : Nat) (b : Expr × BinderMeta), bs[i0]? = some b →
          denote cval env ψ (j + i0)
            (Expr.instSeq (openFvars j i0) (i0 - 1) b.1) =
            some (Γ.getD (k - 1 - i0) default) := by
  intro k
  induction k with
  | zero =>
    intro e j bs body V h hV
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], V, rfl, rfl, hV, fun i0 b hb => nomatch hb⟩
  | succ k ih =>
    intro e j bs body V h hV
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [Expr.stripLams] at h
      cases hs : bodyE.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p => ?_
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denote_lam] at hV
      cases hA : denote cval env ψ j dom with
      | none => rw [hA] at hV; exact nomatch hV
      | some A => ?_
      rw [hA] at hV
      cases hB : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hV; exact nomatch hV
      | some Bv => ?_
      rw [hB] at hV
      obtain rfl : V = .lam A Bv := (Option.some.inj hV).symm
      -- re-open at the anonymous opener (denote-irrelevant)
      have hB' : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar j (.sort .zero)))
          = some Bv := by
        rw [denote_erasedEq (Expr.ErasedEq.instantiate1
          (Expr.ErasedEq.rfl bodyE)
          (show Expr.ErasedEq (.fvar j (.sort .zero))
            (.fvar j dom) from by constructor)) (j + 1)]
        exact hB
      have hsI : ((bodyE.instantiate1 (.fvar j
          (.sort .zero))).stripLams k).isSome :=
        Expr.stripLams_instantiate1_isSome k 0 (by rw [hs]; rfl)
      obtain ⟨bs', body', hsI2⟩ : ∃ bs' body',
          (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripLams k = some (bs', body') := by
        cases hq : (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripLams k with
        | none => rw [hq] at hsI; exact nomatch hsI
        | some q => exact ⟨q.1, q.2, rfl⟩
      obtain ⟨hbody', hdoms'⟩ :=
        Expr.stripLams_instantiate1_eq k 0 hs hsI2
      obtain ⟨Γ', C, rfl, hΓlen, hbody, hdoms⟩ := ih hsI2 hB'
      have hbslen : p.1.length = k := Expr.stripLams_length k hs
      have hbslen' : bs'.length = k := Expr.stripLams_length k hsI2
      refine ⟨Γ' ++ [A], C, ?_, ?_, ?_, ?_⟩
      · rw [lamCtx_snoc]
      · simp [hΓlen]
      · show denote cval env ψ (j + (k + 1))
          (Expr.instSeq (openFvars j (k + 1)) (k + 1 - 1) p.2)
          = some C
        rw [show openFvars j (k + 1) = .fvar j
            (.sort .zero) :: openFvars (j + 1) k from rfl,
          show Expr.instSeq (.fvar j (.sort .zero)
              :: openFvars (j + 1) k) (k + 1 - 1) p.2 =
            Expr.instSeq (openFvars (j + 1) k) (k - 1)
              (p.2.instantiate1 (.fvar j (.sort .zero))
                k) from by
            simp [Expr.instSeq],
          show j + (k + 1) = j + 1 + k from by omega,
          show p.2.instantiate1 (.fvar j (.sort .zero))
              k = body' from by
            rw [hbody']
            simp only [Nat.zero_add]]
        exact hbody
      · intro i0 b hb
        cases i0 with
        | zero =>
          obtain rfl : (dom, mb) = b := by simpa using hb
          show denote cval env ψ (j + 0)
            (Expr.instSeq (openFvars j 0) (0 - 1) dom) = _
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
            simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
            rw [List.getElem?_append_right (by omega), hΓlen,
              Nat.sub_self]
            rfl]
          exact hA
        | succ i0 =>
          rw [List.getElem?_cons_succ] at hb
          have hik : i0 < k := by
            rcases Nat.lt_or_ge i0 k with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none (by omega)] at hb
              exact nomatch hb
          have hb' : bs'[i0]? = some (bs'[i0]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          have hdomEq := hdoms' i0 b (bs'[i0]'(by omega)) hb hb'
          have h1 := hdoms i0 _ hb'
          rw [hdomEq] at h1
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i0 + 1)) default =
              Γ'.getD (k - 1 - i0) default from by
            simp only [List.getD]
            rw [show k + 1 - 1 - (i0 + 1) = k - 1 - i0 from by omega,
              List.getElem?_append_left (by omega)]]
          show denote cval env ψ (j + (i0 + 1))
            (Expr.instSeq (openFvars j (i0 + 1)) (i0 + 1 - 1) b.1)
            = _
          rw [show openFvars j (i0 + 1) = .fvar j
              (.sort .zero) :: openFvars (j + 1) i0 from rfl,
            show Expr.instSeq (.fvar j (.sort .zero)
                :: openFvars (j + 1) i0) (i0 + 1 - 1) b.1 =
              Expr.instSeq (openFvars (j + 1) i0) (i0 - 1)
                (b.1.instantiate1 (.fvar j
                  (.sort .zero)) i0) from by
              simp [Expr.instSeq],
            show j + (i0 + 1) = j + 1 + i0 from by omega]
          rw [show (0 : Nat) + i0 = i0 from by omega] at h1
          exact h1

/-- **A tower's domains are bounded by their own depth**: the `i`-th
domain of a `∀`-tower over a subject bounded by `d` mentions no de
Bruijn index at or above `d + i`.  (Task #148, T5 c5: what lets a
context's interpretation be transported across two valuations that
agree only *below* the context's depth — the unit law fires at a
valuation extended by its two members.) -/
theorem PiTele.bvarsBelow :
    ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
      PiTele k T Γ R → ∀ {d : Nat}, Term.bvarsBelow d T →
      ∀ i, i < k → Term.bvarsBelow (d + i)
        (Γ.getD (k - 1 - i) default) := by
  intro k T Γ R h
  induction h with
  | nil => intro d _ i hi; exact nomatch hi
  | @cons k A B R Γ hp ih =>
    intro d hb i hi
    have hbA : Term.bvarsBelow d A := hb.1
    have hbB : Term.bvarsBelow (d + 1) B := hb.2
    have hΓlen : Γ.length = k := hp.length
    cases i with
    | zero =>
      rw [show k + 1 - 1 - 0 = k from by omega, List.getD,
        List.getElem?_append_right (by rw [hΓlen]; omega), hΓlen,
        Nat.sub_self]
      exact hbA
    | succ j =>
      have hjk : j < k := by omega
      rw [show k + 1 - 1 - (j + 1) = k - 1 - j from by omega, List.getD,
        List.getElem?_append_left (by rw [hΓlen]; omega)]
      have h1 := ih hbB j hjk
      rw [List.getD] at h1
      rw [show d + (j + 1) = d + 1 + j from by omega]
      exact h1

/-- A `PiTele` is determined by its arity and tower. -/
theorem PiTele.det : ∀ {k : Nat} {T : Term} {Γ Γ' : List Term}
    {R R' : Term}, PiTele k T Γ R → PiTele k T Γ' R' →
    Γ = Γ' ∧ R = R' := by
  intro k
  induction k with
  | zero =>
    intro T Γ Γ' R R' h h'
    cases h
    cases h'
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro T Γ Γ' R R' h h'
    cases h with
    | @cons _ A B _ Γ0 h0 =>
      cases h' with
      | @cons _ A' B' _ Γ0' h0' =>
        obtain ⟨h1, h2⟩ := ih h0 h0'
        exact ⟨by rw [h1], h2⟩

/-- **The Π-tower, denoted canonically** (`stripLams_denoteTele`'s twin):
a denoting Π-tower is `PiTele` at its domains' values,
with the body and each raw domain denoted under the anonymous openers
(`openFvars`) — annotations are denote-irrelevant, so any same-index
opener family produces the same values. -/
theorem stripPis_denoteTele {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} :
    ∀ (k : Nat) {e : Expr} {j : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr} {V : Term},
      e.stripPis k = some (bs, body) →
      denote cval env ψ j e = some V →
      ∃ (Γ : List Term) (C : Term),
        PiTele k V Γ C ∧ Γ.length = k ∧
        denote cval env ψ (j + k)
          (Expr.instSeq (openFvars j k) (k - 1) body) = some C ∧
        ∀ (i0 : Nat) (b : Expr × BinderMeta), bs[i0]? = some b →
          denote cval env ψ (j + i0)
            (Expr.instSeq (openFvars j i0) (i0 - 1) b.1) =
            some (Γ.getD (k - 1 - i0) default) := by
  intro k
  induction k with
  | zero =>
    intro e j bs body V h hV
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], V, .nil, rfl, hV, fun i0 b hb => nomatch hb⟩
  | succ k ih =>
    intro e j bs body V h hV
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [Expr.stripPis] at h
      cases hs : bodyE.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p => ?_
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denote_forallE] at hV
      cases hA : denote cval env ψ j dom with
      | none => rw [hA] at hV; exact nomatch hV
      | some A => ?_
      rw [hA] at hV
      cases hB : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hV; exact nomatch hV
      | some Bv => ?_
      rw [hB] at hV
      obtain rfl : V = .pi A Bv := (Option.some.inj hV).symm
      -- re-open at the anonymous opener (denote-irrelevant)
      have hB' : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar j (.sort .zero)))
          = some Bv := by
        rw [denote_erasedEq (Expr.ErasedEq.instantiate1
          (Expr.ErasedEq.rfl bodyE)
          (show Expr.ErasedEq (.fvar j (.sort .zero))
            (.fvar j dom) from by constructor)) (j + 1)]
        exact hB
      have hsI : ((bodyE.instantiate1 (.fvar j
          (.sort .zero))).stripPis k).isSome :=
        Expr.stripPis_instantiate1_isSome k 0 (by rw [hs]; rfl)
      obtain ⟨bs', body', hsI2⟩ : ∃ bs' body',
          (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripPis k = some (bs', body') := by
        cases hq : (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripPis k with
        | none => rw [hq] at hsI; exact nomatch hsI
        | some q => exact ⟨q.1, q.2, rfl⟩
      obtain ⟨hbody', hdoms'⟩ :=
        Expr.stripPis_instantiate1_eq k 0 hs hsI2
      obtain ⟨Γ', C, htele, hΓlen, hbody, hdoms⟩ := ih hsI2 hB'
      have hbslen : p.1.length = k := by
        have h0 := Expr.stripPis_length k hs
        exact h0
      have hbslen' : bs'.length = k := Expr.stripPis_length k hsI2
      refine ⟨Γ' ++ [A], C, ?_, ?_, ?_, ?_⟩
      · exact .cons htele
      · simp [hΓlen]
      · show denote cval env ψ (j + (k + 1))
          (Expr.instSeq (openFvars j (k + 1)) (k + 1 - 1) p.2)
          = some C
        rw [show openFvars j (k + 1) = .fvar j
            (.sort .zero) :: openFvars (j + 1) k from rfl,
          show Expr.instSeq (.fvar j (.sort .zero)
              :: openFvars (j + 1) k) (k + 1 - 1) p.2 =
            Expr.instSeq (openFvars (j + 1) k) (k - 1)
              (p.2.instantiate1 (.fvar j (.sort .zero))
                k) from by
            simp [Expr.instSeq],
          show j + (k + 1) = j + 1 + k from by omega,
          show p.2.instantiate1 (.fvar j (.sort .zero))
              k = body' from by
            rw [hbody']
            simp only [Nat.zero_add]]
        exact hbody
      · intro i0 b hb
        cases i0 with
        | zero =>
          obtain rfl : (dom, mb) = b := by simpa using hb
          show denote cval env ψ (j + 0)
            (Expr.instSeq (openFvars j 0) (0 - 1) dom) = _
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
            simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
            rw [List.getElem?_append_right (by omega), hΓlen,
              Nat.sub_self]
            rfl]
          exact hA
        | succ i0 =>
          rw [List.getElem?_cons_succ] at hb
          have hik : i0 < k := by
            rcases Nat.lt_or_ge i0 k with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none (by omega)] at hb
              exact nomatch hb
          have hb' : bs'[i0]? = some (bs'[i0]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          have hdomEq := hdoms' i0 b (bs'[i0]'(by omega)) hb hb'
          have h1 := hdoms i0 _ hb'
          rw [hdomEq] at h1
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i0 + 1)) default =
              Γ'.getD (k - 1 - i0) default from by
            simp only [List.getD]
            rw [show k + 1 - 1 - (i0 + 1) = k - 1 - i0 from by omega,
              List.getElem?_append_left (by omega)]]
          show denote cval env ψ (j + (i0 + 1))
            (Expr.instSeq (openFvars j (i0 + 1)) (i0 + 1 - 1) b.1)
            = _
          rw [show openFvars j (i0 + 1) = .fvar j
              (.sort .zero) :: openFvars (j + 1) i0 from rfl,
            show Expr.instSeq (.fvar j (.sort .zero)
                :: openFvars (j + 1) i0) (i0 + 1 - 1) b.1 =
              Expr.instSeq (openFvars (j + 1) i0) (i0 - 1)
                (b.1.instantiate1 (.fvar j
                  (.sort .zero)) i0) from by
              simp [Expr.instSeq],
            show j + (i0 + 1) = j + 1 + i0 from by omega]
          rw [show (0 : Nat) + i0 = i0 from by omega] at h1
          exact h1

/-- The projection rule's opened body denotes to the field's bound
variable (sealed: the `instSeq`-of-`bvar` computation in a small
context; DESIGN §22). -/
theorem projBodyValue {cval : TConstVal} {env : Env} {ψ : Name → Nat}
    {cnP cnF i : Nat} (hilt : i < cnF) {Cβ : Term}
    (hCβden : denote cval env ψ (0 + (cnP + cnF))
      (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        (.bvar (cnF - 1 - i))) = some Cβ) :
    Cβ = .bvar (cnP + cnF - 1 - (cnP + i)) := by
  have hhit := Expr.instSeq_bvar (openFvars 0 (cnP + cnF))
    (cnP + cnF - 1) (cnF - 1 - i)
    (openFvars_bounded 0 (cnP + cnF)) (by omega)
    (by rw [openFvars_length]; omega)
  rw [openFvars_getElem? (d := 0) (k := cnP + cnF)
    (i := cnP + cnF - 1 - (cnF - 1 - i)) (by omega)] at hhit
  have hidxeq : cnP + cnF - 1 - (cnF - 1 - i) = cnP + i := by omega
  rw [hidxeq] at hhit
  have h2 := hCβden
  rw [← Option.some.inj hhit] at h2
  rw [denote_fvar] at h2
  have h3 := Option.some.inj h2
  rw [← h3]
  simp only [Nat.zero_add]

/-- Two canonically-opened towers whose raw domains **denote equally**
at their own depths have the same denoted context.  The denote-level
form is what a *renamed* domain pin needs (the projection statement's
telescope is the constructor's renamed, not equal to it — task #148,
T5 c4); `towerCtxEq` is the syntactic corollary. -/
theorem towerCtxEqD {cval : TConstVal} {env : Env} {ψ : Name → Nat}
    {k : Nat} {Γβ Γc : List Term}
    {rbinders cbinders : List (Expr × BinderMeta)}
    (hrblen : rbinders.length = k) (hcblen : cbinders.length = k)
    (hΓβlen : Γβ.length = k) (hΓclen : Γc.length = k)
    (hβdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      rbinders[i0]? = some b →
      denote cval env ψ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γβ.getD (k - 1 - i0) default))
    (hcdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      cbinders[i0]? = some b →
      denote cval env ψ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γc.getD (k - 1 - i0) default))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < k → rbinders[i0]? = some b →
      cbinders[i0]? = some b' →
      denote cval env ψ (0 + i0)
          (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        denote cval env ψ (0 + i0)
          (Expr.instSeq (openFvars 0 i0) (i0 - 1) b'.1)) :
    Γβ = Γc := by
  refine List.ext_getElem (by omega) ?_
  intro q h1 h2
  have hq : q < k := by omega
  have hbβlt : k - 1 - q < rbinders.length := by omega
  have hbclt : k - 1 - q < cbinders.length := by omega
  obtain ⟨bβ, hbβ⟩ : ∃ b, rbinders[k - 1 - q]? = some b :=
    ⟨rbinders[k - 1 - q]'hbβlt, List.getElem?_eq_getElem hbβlt⟩
  obtain ⟨bc, hbc⟩ : ∃ b, cbinders[k - 1 - q]? = some b :=
    ⟨cbinders[k - 1 - q]'hbclt, List.getElem?_eq_getElem hbclt⟩
  have hβq := hβdoms (k - 1 - q) bβ hbβ
  have hcq := hcdoms (k - 1 - q) bc hbc
  have hdomeq := hrdomsEq (k - 1 - q) bβ bc (by omega) hbβ hbc
  rw [hdomeq] at hβq
  have h3 : Γβ.getD (k - 1 - (k - 1 - q)) default =
      Γc.getD (k - 1 - (k - 1 - q)) default :=
    Option.some.inj (hβq.symm.trans hcq)
  rw [show k - 1 - (k - 1 - q) = q from by omega] at h3
  rw [show Γβ[q] = Γβ.getD q default from by
      simp [List.getD, List.getElem?_eq_getElem h1],
    show Γc[q] = Γc.getD q default from by
      simp [List.getD, List.getElem?_eq_getElem h2]]
  exact h3

/-- Two canonically-opened towers with pointwise-equal raw domains
have the same denoted context (sealed for the same reason). -/
theorem towerCtxEq {cval : TConstVal} {env : Env} {ψ : Name → Nat}
    {k : Nat} {Γβ Γc : List Term}
    {rbinders cbinders : List (Expr × BinderMeta)}
    (hrblen : rbinders.length = k) (hcblen : cbinders.length = k)
    (hΓβlen : Γβ.length = k) (hΓclen : Γc.length = k)
    (hβdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      rbinders[i0]? = some b →
      denote cval env ψ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γβ.getD (k - 1 - i0) default))
    (hcdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      cbinders[i0]? = some b →
      denote cval env ψ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γc.getD (k - 1 - i0) default))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < k → rbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.1 = b'.1) :
    Γβ = Γc :=
  towerCtxEqD hrblen hcblen hΓβlen hΓclen hβdoms hcdoms
    (fun i0 b b' hi hb hb' => by rw [hrdomsEq i0 b b' hi hb hb'])

/-! ## The stored levels' arity (the nested bottom's `hlvlsLen`)

The checker never compares `lvls.length` against the constructor's
level arity — the fact is forced *semantically*: the checked
statement's major applies `f ctor` at `lvls`, the statement denotes
(it is a stored, checked theorem), and `denote`'s `.const` clause is
guarded on the stored arity.  Sealed per the house rule: the walk
rewrites under `denote` terms.

Relocated verbatim from `ConLeche/TTVerify/DeclIndRecs.lean` (task #148,
T5 stage 3b): the statement is about `denote` and a `TConstVal`, so
both verified lanes' nested bottoms read it. -/
theorem nestedLvlsLength {cval : TConstVal} {env₀ : Env} {ψ : Name → Nat}
    {stmtTy : Expr} {K : Nat} {fvs : List Expr} {tbody : Expr}
    {ℓA : Level} {αS lhsS rhsS : Expr} {fRn fCtor : Name}
    {lpsE lvls : List Level} {mI : Nat} {spN : List Expr}
    {ciCm : ConstantInfo} {Tstmt : Term}
    (hTstmt : denote cval env₀ ψ 0 stmtTy = some Tstmt)
    (hopen : openPisAtFvars K stmtTy 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const fRn lpsE)
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const fCtor lvls) spN))
    (hfCmE : env₀.find? fCtor = some ciCm) :
    lvls.length = ciCm.toConstantVal.levelParams.length := by
  obtain ⟨Γs, Rbody, htowerS, hRbody, -⟩ :=
    openPisAtFvars_denoteTele K hopen hTstmt
  rw [← Expr.mkAppN_getApp tbody, hheadEq, hargs3] at hRbody
  obtain ⟨vf, vs, -, hsp, -⟩ := denote_mkAppN_inv hRbody
  obtain ⟨vl, hvl⟩ : ∃ vl, denote cval env₀ ψ (0 + K) lhsS = some vl := by
    cases hsp with
    | cons hα hsp1 =>
      cases hsp1 with
      | cons hl hsp2 => exact ⟨_, hl⟩
  rw [← Expr.mkAppN_getApp lhsS, hlhead] at hvl
  obtain ⟨vh, vsl, -, hspL, -⟩ := denote_mkAppN_inv hvl
  have hlt : mI < lhsS.getAppArgs.length := by omega
  have hlast : lhsS.getAppArgs.getLastD (.bvar 0) =
      lhsS.getAppArgs[mI]'hlt := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlarity,
      Nat.add_sub_cancel]
    simp [List.getElem?_eq_getElem hlt]
  have hmajden := hspL.get ⟨mI, hlt⟩
  simp only [Fin.getElem_fin] at hmajden
  rw [← hlast, denote_erasedEq hmaj] at hmajden
  obtain ⟨vc, vspn, hvc, -, -⟩ := denote_mkAppN_inv hmajden
  rw [denote_const, hfCmE] at hvc
  dsimp only at hvc
  split at hvc
  · next hlen => exact hlen
  · exact nomatch hvc

/-- The projection statement's right side denotes to the field's
frame variable (sealed). -/
theorem projRhsValue {cval : TConstVal} {env : Env} {ψ : Name → Nat}
    {fvs : List Expr} {rP cnF i : Nat} {vR : Term}
    (hshapeS : ∀ (i0 : Nat) (x : Expr), fvs[i0]? = some x →
      ∃ ty, x = Expr.fvar i0 ty)
    (hfvslen : fvs.length = rP + cnF) (hilt : i < cnF)
    (hRden : denote cval env ψ (rP + cnF) (fvs.getD (rP + i) default)
      = some vR) :
    vR = .bvar (rP + cnF - 1 - (rP + i)) := by
  obtain ⟨t, hsh⟩ := hshapeS (rP + i) fvs[rP + i]
    (List.getElem?_eq_getElem (show rP + i < fvs.length from by omega))
  rw [show fvs.getD (rP + i) default = fvs[rP + i] from by
      simp [List.getD, List.getElem?_eq_getElem
        (show rP + i < fvs.length from by omega)],
    hsh, denote_fvar] at hRden
  exact (Option.some.inj hRden).symm


/-- `instLamsAt` returns one domain per argument. -/
theorem instLamsAt_length :
    ∀ (sp : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instLamsAt sp e = some (ds, rest) → ds.length = sp.length := by
  intro sp
  induction sp with
  | nil =>
    intro e ds rest h
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a sp ih =>
    intro e ds rest h
    match e, h with
    | .lam dom body mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih h1]

/-- Composition of two `instPisAt` runs: walking `as ++ bs` is walking
`as`, then `bs` on the residual. -/
theorem Expr.instPisAt_append :
    ∀ (as : List Expr) {bs : List Expr} {ty : Expr} {ds ds2 : List Expr}
      {rs rs2 : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt bs rs = some (ds2, rs2) →
      Expr.instPisAt (as ++ bs) ty = some (ds ++ ds2, rs2) := by
  intro as
  induction as with
  | nil =>
    intro bs ty ds ds2 rs rs2 h h2
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h2
  | cons a as ih =>
    intro bs ty ds ds2 rs rs2 h h2
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt as (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show (Expr.instPisAt (as ++ bs) (body.instantiate1 a)).map _ = _
        rw [ih h1 h2]
        rfl

/-- **The λ-telescope's denotation, read through an `instLamsAt` run at
shaped openers**: the value is a `lamCtx` tower whose layers are the
run's progressively-instantiated domains, denoted at their own depths,
and whose core is the residual's denotation — `denote` reads neither an
opener's name nor its annotation, so any same-index opener spine
produces the same tower. -/
theorem instLamsAt_denoteTele {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} :
    ∀ (sp : List Expr) {e : Expr} {j : Nat} {ds : List Expr}
      {rest : Expr} {Vv : Term},
      Expr.instLamsAt sp e = some (ds, rest) →
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        ∃ ty, x = Expr.fvar (j + i) ty) →
      denote cval env ψ j e = some Vv →
      ∃ (Γ : List Term) (C : Term),
        Vv = lamCtx Γ C ∧ Γ.length = sp.length ∧
        denote cval env ψ (j + sp.length) rest = some C ∧
        ∀ (i0 : Nat) (x : Expr), ds[i0]? = some x →
          denote cval env ψ (j + i0) x =
            some (Γ.getD (sp.length - 1 - i0) default) := by
  intro sp
  induction sp with
  | nil =>
    intro e j ds rest Vv h _ hV
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], Vv, rfl, rfl, hV, fun i0 x hx => nomatch hx⟩
  | cons a sp ih =>
    intro e j ds rest Vv h hshape hV
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (bodyE.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denote_lam] at hV
      cases hA : denote cval env ψ j dom with
      | none => rw [hA] at hV; exact nomatch hV
      | some A => ?_
      rw [hA] at hV
      cases hB : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hV; exact nomatch hV
      | some Bv => ?_
      rw [hB] at hV
      obtain rfl : Vv = .lam A Bv := (Option.some.inj hV).symm
      -- the head opener's shape
      obtain ⟨tyA, rfl⟩ := hshape 0 a rfl
      -- re-open at the run's opener (denote-irrelevant)
      have hB' : denote cval env ψ (j + 1)
          (bodyE.instantiate1 (.fvar (j + 0) tyA)) = some Bv := by
        rw [denote_erasedEq (Expr.ErasedEq.instantiate1
          (Expr.ErasedEq.rfl bodyE)
          (show Expr.ErasedEq (.fvar (j + 0) tyA)
            (.fvar j dom) from by constructor)) (j + 1)]
        exact hB
      have hshape' : ∀ (i : Nat) (x : Expr), sp[i]? = some x →
          ∃ ty', x = Expr.fvar (j + 1 + i) ty' := by
        intro i x hx
        obtain ⟨ty', hx'⟩ := hshape (i + 1) x (by simpa using hx)
        exact ⟨ty', by rw [hx']; congr 1; omega⟩
      obtain ⟨Γ', C, rfl, hΓlen, hrest, hdoms⟩ := ih h1 hshape' hB'
      have hdslen : p.1.length = sp.length := instLamsAt_length sp h1
      refine ⟨Γ' ++ [A], C, ?_, ?_, ?_, ?_⟩
      · rw [lamCtx_snoc]
      · simp [hΓlen]
      · simp only [List.length_cons]
        rw [show j + (sp.length + 1) = j + 1 + sp.length from by omega]
        exact hrest
      · intro i0 x hx
        simp only [List.length_cons]
        cases i0 with
        | zero =>
          obtain rfl : dom = x := Option.some.inj hx
          rw [Nat.add_zero, hA]
          congr 1
          rw [show sp.length + 1 - 1 - 0 = Γ'.length from by
            rw [hΓlen]; omega]
          rw [List.getD, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]
          rfl
        | succ i =>
          have hx' : p.1[i]? = some x := by simpa using hx
          have hi : i < sp.length := by
            have := (List.getElem?_eq_some_iff.mp hx').1
            rw [instLamsAt_length sp h1] at this
            exact this
          have h2 := hdoms i x hx'
          rw [show j + (i + 1) = j + 1 + i from by omega]
          rw [h2]
          congr 1
          rw [List.getD, List.getD,
            show sp.length + 1 - 1 - (i + 1) = sp.length - 1 - i from by
              omega,
            List.getElem?_append_left (by rw [hΓlen]; omega)]


/-- Leaves of an `instLamsAt` run come from the telescope or the
spine (the λ mirror of `instPisAt_leaves`). -/
theorem instLamsAt_leaves :
    ∀ (as : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instLamsAt as ty = some (ds, rs) →
      ∀ l, ((∃ x ∈ ds, l ∈ x.fvarLeaves) ∨ l ∈ rs.fvarLeaves) →
        l ∈ ty.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil =>
    intro ty ds rs h l hl
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with ⟨x, hx, -⟩ | hl
    · exact nomatch hx
    · exact Or.inl hl
  | cons a as ih =>
    intro ty ds rs h l hl
    match ty, h with
    | .lam d₁ b₁ m₁, h => ?_
    simp only [Expr.instLamsAt] at h
    cases h1 : Expr.instLamsAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    rw [h1] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have push : l ∈ (b₁.instantiate1 a).fvarLeaves →
        l ∈ (Expr.lam d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves := by
      intro hb
      rcases Expr.fvarLeaves_instantiate1 b₁ 0 hb with hb' | hb'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_right _ hb'
      · exact Or.inr ⟨a, List.mem_cons_self .., hb'⟩
    rcases hl with ⟨x, hx, hlx⟩ | hl
    · rcases List.mem_cons.mp hx with rfl | hx'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_left _ hlx
      · rcases ih h1 l (Or.inl ⟨x, hx', hlx⟩) with h2 | ⟨b, hb, hlb⟩
        · exact push h2
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩
    · rcases ih h1 l (Or.inr hl) with h2 | ⟨b, hb, hlb⟩
      · exact push h2
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩


/-- The opener returns one variable per binder. -/
theorem openPisAtFvars_length :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) → fvs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e d fvs body h
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases h1 : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih h1]


/-- Constant renaming leaves the loose-bvar bound unchanged. -/
theorem looseBVarsBounded_renameConsts {f : Name → Name} :
    ∀ (e : Expr) (k : Nat),
      (e.renameConsts f).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.renameConsts, Expr.looseBVarsBounded]


/-- `stripPis` commutes with constant renaming (renaming touches no
binder structure). -/
theorem stripPis_renameConsts {f : Name → Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr},
      e.stripPis n = some (bs, body) →
      (e.renameConsts f).stripPis n =
        some (bs.map (fun b => (b.1.renameConsts f, b.2)),
          body.renameConsts f) := by
  intro n
  induction n with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro e bs body h
    match e, h with
    | .forallE dom b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hbs, hbody⟩ : (dom, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbs hbody
        show ((b.renameConsts f).stripPis n).map _ = _
        rw [ih hs]
        rfl

/-- Constant renaming keeps the application-spine arity. -/
theorem getAppArgs_length_renameConsts {f : Name → Name} :
    ∀ (e : Expr),
      (e.renameConsts f).getAppArgs.length = e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg _ =>
    show ((g.renameConsts f).getAppArgs ++ [a.renameConsts f]).length
      = (g.getAppArgs ++ [a]).length
    rw [List.length_append, List.length_append, ihg]
    rfl
  | bvar i => rfl
  | fvar i ty => rfl
  | sort u => rfl
  | const n us => rfl
  | lam ty b m => rfl
  | forallE ty b m => rfl
  | letE ty v b => rfl
  | lit l => rfl
  | proj s i e => rfl

end ConLeche.Verify
