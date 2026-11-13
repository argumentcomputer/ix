import IxVMRefinement.Iota.Basic
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.StrLitExpr

/-! # Reducts and inferred types add no free-variable leaves; full-grade inference is io-grade

Two facts of the rules tier over an environment whose stored terms are closed
(`Ix.Kernel.StoreClosed`):

* **no new leaves**: a reduct's free-variable leaves (`Expr.fvarLeaves`, hereditarily through
  annotations) are the term's (`red_leaves`), and so are an inferred type's (`infer_leaves`).
  Every move copies material from its input; δ, ι and the projection rule add closed stored
  terms; the η/K/`And` rescues carry the guard as a premise; a `λ`'s type closes the opened
  variable again (`abstract1`), so the variable's own leaf goes.
* **grades**: a full-grade inference is an io-grade one (`infer_toIo`): the io rules drop
  premises, and the full-grade application rule is also an io rule.

The rescues' scope guard `fab.fvarLeaves ⊆ major.fvarLeaves` follows from the first, for a
fabrication built from the major's inferred, reduced type. -/

namespace IxVM.Refinement.Core

open Ix.Kernel.Rules (Red DefEq Infer Certs DefEqList EtaProjCerts Grade)
open Ix.Kernel.Expr (fvarLeaves fvarLeaves_eq_nil_of_not_hasFvar fvarLeaves_instantiate1
  hasFvar_instantiateLevelParams)

set_option linter.unusedVariables false

/-! ## Leaves of the operations the rules apply -/

theorem leaves_closed {e : KExpr} (h : e.hasFvar = false) {l : Nat × KExpr}
    (hl : l ∈ e.fvarLeaves) : False := by
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  cases hl

/-- The leaves of an annotation are leaves of the term. -/
theorem leaves_annot : ∀ {e : KExpr} {j : Nat} {y : KExpr}, (j, y) ∈ e.fvarLeaves →
    ∀ l ∈ y.fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro j y h l hl
    simp only [fvarLeaves, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .inr hl
    · exact .inr (ih h l hl)
  | app f a ihf iha =>
    intro j y h l hl
    simp only [fvarLeaves, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (ihf h l hl)
    · exact .inr (iha h l hl)
  | lam ty b m iht ihb =>
    intro j y h l hl
    simp only [fvarLeaves, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (iht h l hl)
    · exact .inr (ihb h l hl)
  | forallE ty b m iht ihb =>
    intro j y h l hl
    simp only [fvarLeaves, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (iht h l hl)
    · exact .inr (ihb h l hl)
  | letE ty v b m iht ihv ihb =>
    intro j y h l hl
    simp only [fvarLeaves, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (iht h l hl))
    · exact .inl (.inr (ihv h l hl))
    · exact .inr (ihb h l hl)
  | proj s i e ih =>
    intro j y h l hl
    simp only [fvarLeaves] at h ⊢
    exact ih h l hl
  | _ => intro j y h; simp [fvarLeaves] at h

/-- **Closing an opened variable** keeps leaves of the term only; one at the variable's index
survives only inside the annotation of another variable's leaf. -/
theorem leaves_abstract1 (D : Nat) : ∀ (e : KExpr) (k : Nat) (l : Nat × KExpr),
    l ∈ (e.abstract1 D k).fvarLeaves →
      l ∈ e.fvarLeaves ∧
        (l.1 ≠ D ∨ ∃ j y, (j, y) ∈ e.fvarLeaves ∧ j ≠ D ∧ l ∈ y.fvarLeaves) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl ⊢
      rcases hl with rfl | hl
      · exact ⟨.inl rfl, .inl hne⟩
      · exact ⟨.inr hl, .inr ⟨idx, ty, by simp [fvarLeaves], hne, hl⟩⟩
  | app f a ihf iha =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k l hl
      refine ⟨.inl h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inl h, hj, hy⟩⟩
    · obtain ⟨h1, h2⟩ := iha k l hl
      refine ⟨.inr h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inr h, hj, hy⟩⟩
  | lam ty b m iht ihb =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := iht k l hl
      refine ⟨.inl h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inl h, hj, hy⟩⟩
    · obtain ⟨h1, h2⟩ := ihb (k + 1) l hl
      refine ⟨.inr h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inr h, hj, hy⟩⟩
  | forallE ty b m iht ihb =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := iht k l hl
      refine ⟨.inl h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inl h, hj, hy⟩⟩
    · obtain ⟨h1, h2⟩ := ihb (k + 1) l hl
      refine ⟨.inr h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inr h, hj, hy⟩⟩
  | letE ty v b m iht ihv ihb =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := iht k l hl
      refine ⟨.inl (.inl h1), h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inl (.inl h), hj, hy⟩⟩
    · obtain ⟨h1, h2⟩ := ihv k l hl
      refine ⟨.inl (.inr h1), h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inl (.inr h), hj, hy⟩⟩
    · obtain ⟨h1, h2⟩ := ihb (k + 1) l hl
      refine ⟨.inr h1, h2.imp id fun ⟨j, y, h, hj, hy⟩ => ⟨j, y, .inr h, hj, hy⟩⟩
  | proj s i e ih =>
    intro k l hl
    simp only [Ix.Kernel.Expr.abstract1, fvarLeaves] at hl ⊢
    exact ih k l hl
  | _ => intro k l hl; simp [Ix.Kernel.Expr.abstract1, fvarLeaves] at hl

/-- Instantiating bound variables only introduces the substituted terms' leaves. -/
theorem leaves_instantiateList : ∀ (vs : List KExpr) (e : KExpr) (d : Nat) (l : Nat × KExpr),
    l ∈ (e.instantiateList vs d).fvarLeaves → l ∈ e.fvarLeaves ∨ ∃ v ∈ vs, l ∈ v.fvarLeaves
  | [], e, d, l, hl => by
    rw [Ix.Kernel.Expr.instantiateList_nil] at hl
    exact .inl hl
  | v :: vs, e, d, l, hl => by
    rw [Ix.Kernel.Expr.instantiateList_cons] at hl
    rcases fvarLeaves_instantiate1 _ d hl with h | h
    · rcases leaves_instantiateList vs e (d + 1) l h with h' | ⟨w, hw, h'⟩
      · exact .inl h'
      · exact .inr ⟨w, List.mem_cons_of_mem _ hw, h'⟩
    · exact .inr ⟨v, List.mem_cons_self .., h⟩

/-- An argument read with the default `bvar 0` is one of the arguments, or has no leaf. -/
theorem leaves_getD {xs : List KExpr} {n : Nat} {l : Nat × KExpr}
    (hl : l ∈ (xs.getD n (.bvar 0)).fvarLeaves) : ∃ x ∈ xs, l ∈ x.fvarLeaves := by
  rw [List.getD_eq_getElem?_getD] at hl
  cases hx : xs[n]? with
  | none => rw [hx] at hl; simp [fvarLeaves] at hl
  | some x => rw [hx] at hl; exact ⟨x, List.mem_of_getElem? hx, hl⟩

/-- A term every renaming fixes has no leaf. -/
theorem leaves_nil_of_renFV_fix {r : KExpr} (h : r.renFV Nat.succ = r) : r.fvarLeaves = [] := by
  have e := congrArg Ix.Kernel.Expr.fvarLeaves h
  rw [Ix.Kernel.Expr.fvarLeaves_renFV] at e
  cases hl : r.fvarLeaves with
  | nil => rfl
  | cons l ls =>
    rw [hl, List.map_cons] at e
    have := congrArg Prod.fst (List.cons.inj e).1
    simp at this

/-- **Unfolding a definition** adds a closed value. -/
theorem leaves_unfold {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) {e e' : KExpr}
    (hu : Ix.Kernel.unfoldDefinition env e = some e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
  unfold Ix.Kernel.unfoldDefinition at hu
  split at hu
  · rename_i n us hfn
    cases hf : env.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some c =>
      rw [hf] at hu
      cases c with
      | defnInfo cv value hint =>
        dsimp only at hu
        split at hu
        · obtain rfl := Option.some.inj hu
          intro l hl
          rcases Ix.Kernel.fvarLeaves_mkAppN hl with h | ⟨x, hx, h⟩
          · exact (leaves_closed (by rw [hasFvar_instantiateLevelParams]; exact hs.defn hf) h).elim
          · exact Ix.Kernel.fvarLeaves_getAppArgs hx l h
        · exact nomatch hu
      | _ => exact nomatch hu
  · exact nomatch hu

/-! ## No new leaves -/

mutual

/-- **A reduct's leaves are the term's.** -/
theorem red_leaves {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {d : Nat} {e e' : KExpr}, Red env d e e' → ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves
  | _, _, _, .refl => fun _ h => h
  | _, _, _, .trans h₁ h₂ => fun l hl => red_leaves hs h₁ l (red_leaves hs h₂ l hl)
  | _, _, _, .appFn h => fun l hl => by
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact .inl (red_leaves hs h l hl)
    · exact .inr hl
  | _, _, _, .projArg h => fun l hl => by
    simp only [fvarLeaves] at hl ⊢
    exact red_leaves hs h l hl
  | _, _, _, .appArg h => fun l hl => by
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact .inl hl
    · exact .inr (red_leaves hs h l hl)
  | _, _, _, .betaGate _ => fun l hl => by
    simp only [fvarLeaves, List.mem_append]
    rcases fvarLeaves_instantiate1 _ 0 hl with h | h
    · exact .inl (.inr h)
    · exact .inr h
  | _, _, _, .beta _ _ => fun l hl => by
    simp only [fvarLeaves, List.mem_append]
    rcases fvarLeaves_instantiate1 _ 0 hl with h | h
    · exact .inl (.inr h)
    · exact .inr h
  | _, _, _, .delta hu => leaves_unfold hs hu
  | _, _, _, .deltaThm _ _ hvf _ _ _ _ _ _ => fun l hl =>
    (leaves_closed (by rw [hasFvar_instantiateLevelParams]; exact hvf) hl).elim
  | _, _, _, .eqProof _ _ hp _ _ hlp _ _ _ _ _ _ _ => fun l hl =>
    hlp l (infer_leaves hs hp l (by simp only [fvarLeaves, List.mem_append]; exact .inr hl))
  | _, _, _, .natLit _ => fun l hl => by
    rw [Ix.Kernel.natLitToConstructor_fvarLeaves] at hl
    cases hl
  | _, _, _, .natZeroLit _ => fun l hl => by simp [fvarLeaves] at hl
  | _, _, _, .strLit _ => fun l hl => by
    rw [Ix.Kernel.strLitToConstructor_fvarLeaves] at hl
    cases hl
  | _, _, _, .natSucc _ _ _ => fun l hl => by simp [fvarLeaves] at hl
  | _, _, _, .natOp _ _ _ _ _ _ hr => fun l hl => by
    rw [leaves_nil_of_renFV_fix (Ix.Kernel.Expr.renFV_of_natOpResult hr)] at hl
    cases hl
  | _, _, _, .natAddSucc _ _ => fun l hl => by
    unfold Ix.Kernel.Rules.natAddLit at hl
    split at hl <;> simp_all [fvarLeaves]
  | _, _, _, .natAddZero _ _ _ _ => fun l hl => by
    simp only [fvarLeaves, List.mem_append]
    exact .inl (.inr hl)
  | _, _, _, .proj _ _ _ _ _ _ _ _ => fun l hl => by
    obtain ⟨x, hx, hlx⟩ := leaves_getD hl
    simp only [fvarLeaves]
    exact Ix.Kernel.fvarLeaves_getAppArgs hx l hlx
  | _, _, _, .iota _ hfind _ _ hmaj _ _ hrl _ _ _ _ _ _ _ _ => fun l hl => by
    rcases Ix.Kernel.fvarLeaves_mkAppN hl with h | ⟨x, hx, hlx⟩
    · exact (leaves_closed (by
        rw [hasFvar_instantiateLevelParams]
        exact (hs.rhs hfind _ (List.mem_of_find?_eq_some hrl)).1) h).elim
    · rcases List.mem_append.mp hx with hx | hx
      · exact Ix.Kernel.fvarLeaves_getAppArgs (List.mem_of_mem_take hx) l hlx
      · have h1 := Ix.Kernel.fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hlx
        obtain ⟨y, hy, hly⟩ := leaves_getD (red_leaves hs hmaj l h1)
        exact Ix.Kernel.fvarLeaves_getAppArgs hy l hly
  | _, _, _, .rescueK _ _ _ _ _ _ _ _ _ _ _ _ _ hl _ _ _ _ => fun l h =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hl l h)
  | _, _, _, .rescueEta _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl _ _ _ => fun l h =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hl l h)
  | _, _, _, .rescueAnd _ _ _ _ _ _ _ _ _ _ _ _ _ hl _ _ _ _ => fun l h =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hl l h)

theorem defEq_leaves_aux {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {d : Nat} {a b : KExpr}, DefEq env d a b → True
  | _, _, _, _ => trivial

/-- **An inferred type's leaves are the term's.** -/
theorem infer_leaves {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer env g d e t →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | _, _, _, _, .sort => fun l hl => by simp [fvarLeaves] at hl
  | _, _, _, _, .fvar _ => fun l hl => by
    simp only [fvarLeaves, List.mem_cons]
    exact .inr hl
  | _, _, _, _, .const hf _ _ => fun l hl =>
    (leaves_closed (by rw [hasFvar_instantiateLevelParams]; exact hs.type hf) hl).elim
  | _, _, _, _, .natLit _ => fun l hl => by simp [fvarLeaves] at hl
  | _, _, _, _, .strLit _ => fun l hl => by simp [fvarLeaves] at hl
  | _, _, _, _, .forallE _ _ _ _ _ => fun l hl => by simp [fvarLeaves] at hl
  | _, d, _, _, .lam (ty := ty) (body := body) (bt := bt) _ _ hbt _ _ _ _ => fun l hl => by
    have ih := infer_leaves hs hbt
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact .inl hl
    · obtain ⟨hlb, hcase⟩ := leaves_abstract1 d bt 0 l hl
      rcases fvarLeaves_instantiate1 body 0 (ih l hlb) with h1 | h1
      · exact .inr h1
      · simp only [fvarLeaves, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · rcases hcase with hne | ⟨j, y, hjy, hjd, hly⟩
          · exact absurd rfl hne
          · rcases fvarLeaves_instantiate1 body 0 (ih _ hjy) with h2 | h2
            · exact .inr (leaves_annot h2 _ hly)
            · simp only [fvarLeaves, List.mem_cons] at h2
              rcases h2 with h2 | h2
              · exact absurd (congrArg Prod.fst h2) hjd
              · exact .inl (leaves_annot h2 _ hly)
        · exact .inl h1
  | _, _, _, _, .app htf hw _ _ => fun l hl => by
    simp only [fvarLeaves, List.mem_append]
    rcases fvarLeaves_instantiate1 _ 0 hl with h | h
    · refine .inl (infer_leaves hs htf l (red_leaves hs hw l ?_))
      simp only [fvarLeaves, List.mem_append]
      exact .inr h
    · exact .inr h
  | _, _, _, _, .appSkip htf hw _ => fun l hl => by
    simp only [fvarLeaves, List.mem_append]
    rcases fvarLeaves_instantiate1 _ 0 hl with h | h
    · refine .inl (infer_leaves hs htf l (red_leaves hs hw l ?_))
      simp only [fvarLeaves, List.mem_append]
      exact .inr h
    · exact .inr h
  | _, _, _, _, .proj htpe hte _ hent _ _ _ => fun l hl => by
    simp only [fvarLeaves]
    unfold Ix.Kernel.ProjEntry.typeAt at hl
    rcases leaves_instantiateList _ _ _ l hl with h | ⟨v, hv, hlv⟩
    · exact (leaves_closed (by rw [hasFvar_instantiateLevelParams]; exact hs.proj hent) h).elim
    · simp only [List.mem_cons, List.mem_reverse] at hv
      rcases hv with rfl | hv
      · exact hlv
      · exact infer_leaves hs htpe l (red_leaves hs hte l (Ix.Kernel.fvarLeaves_getAppArgs hv l hlv))

theorem certs_leaves_aux {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {d : Nat} {lic : Bool} {T : KExpr} {as : List KExpr}, Certs env d lic T as → True
  | _, _, _, _, _ => trivial

theorem defEqList_leaves_aux {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {d : Nat} {as bs : List KExpr}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem etaProjCerts_leaves_aux {env : Ix.Kernel.Env .anon} (hs : Ix.Kernel.StoreClosed env) :
    ∀ {d : Nat} {T : KKey} {us : List KLevel} {targs : List KExpr} {b : KExpr}
      {lps : List Ix.Kernel.LevelParam} {is : List Nat},
      EtaProjCerts env d T us targs b lps is → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-! ## Grades -/

mutual

theorem red_toIo_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {e e' : KExpr}, Red env d e e' → True
  | _, _, _, _ => trivial

theorem defEq_toIo_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {a b : KExpr}, DefEq env d a b → True
  | _, _, _, _ => trivial

/-- **A full-grade inference is an io-grade one** (at every grade). -/
theorem infer_toIo {env : Ix.Kernel.Env .anon} :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer env g d e t → Infer env .io d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar h => .fvar h
  | _, _, _, _, .const hf ht hus => .const hf ht hus
  | _, _, _, _, .natLit h => .natLit h
  | _, _, _, _, .strLit h => .strLit h
  | _, _, _, _, .forallE hs hu hbs hv hz => .forallE (infer_toIo hs) hu (infer_toIo hbs) hv hz
  | _, _, _, _, .lam _ _ hbt hpw h5 h6 h7 =>
    .lam (s := .sort .zero) (u := .zero) (fun h => nomatch h) (fun h => nomatch h) (infer_toIo hbt) hpw h5 h6 h7
  | _, _, _, _, .app htf hw hta hde => .app (infer_toIo htf) hw (infer_toIo hta) hde
  | _, _, _, _, .appSkip htf hw hnev => .appSkip htf hw hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    .proj (infer_toIo htpe) hte hhead hent hlen hus hprop

theorem certs_toIo_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {lic : Bool} {T : KExpr} {as : List KExpr}, Certs env d lic T as → True
  | _, _, _, _, _ => trivial

theorem defEqList_toIo_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {as bs : List KExpr}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem etaProjCerts_toIo_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {T : KKey} {us : List KLevel} {targs : List KExpr} {b : KExpr}
      {lps : List Ix.Kernel.LevelParam} {is : List Nat},
      EtaProjCerts env d T us targs b lps is → True
  | _, _, _, _, _, _, _, _ => trivial

end

end IxVM.Refinement.Core
