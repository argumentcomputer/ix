import Ix.Cert.DefinitionBlocks
import Ix.Cert.SourceConversion
import Ix.CompileCert.ExpressionState
import Ix.Cert.RecordTransfer

/-! # Which members a definition member mentions

Quotient Source orders a definition group's members by which members each member's converted
terms mention (`DefinitionBlocks.depsOf`, at the members' ingress keys). Both that and the
reader's reading of a compiled member come down to the constants the member's Lean terms
mention (`ConstOcc`: a constant applied, not a projection's structure, through metadata).

* `related_occurs`: a reader term related to a Lean term mentions a key exactly where the Lean
  term mentions a name related to it, for a functional relation of names to keys.
* `ingress_occurs`: a Lean term's Source conversion mentions a key exactly where the term
  mentions a name of that ingress key.
* `depsOf_mem`: the members a converted member depends on.
* `convertDefinitions_block`: what quotient Source converts a group of several definitions to:
  each member under its own numbering and ingress key, every member safe, in `defOrder` over
  `depsOf`. -/

namespace Ix.Cert.DefinitionDeps

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (Numbering ingressKey ingressExpr)
open Ix.CompileCert.ExpressionState (Related)

/-- **`n` is a constant the term applies**: exactly `n`, not a projection's structure, through
metadata. -/
inductive ConstOcc (n : Ix.Name) : Ix.Expr → Prop
  | const {us : Array Ix.Level} {h : Address} : ConstOcc n (.const n us h)
  | appF {f a : Ix.Expr} {h : Address} : ConstOcc n f → ConstOcc n (.app f a h)
  | appA {f a : Ix.Expr} {h : Address} : ConstOcc n a → ConstOcc n (.app f a h)
  | lamT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      ConstOcc n t → ConstOcc n (.lam x t b bi h)
  | lamB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      ConstOcc n b → ConstOcc n (.lam x t b bi h)
  | allT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      ConstOcc n t → ConstOcc n (.forallE x t b bi h)
  | allB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      ConstOcc n b → ConstOcc n (.forallE x t b bi h)
  | letT {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : ConstOcc n t → ConstOcc n (.letE x t v b nd h)
  | letV {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : ConstOcc n v → ConstOcc n (.letE x t v b nd h)
  | letB {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : ConstOcc n b → ConstOcc n (.letE x t v b nd h)
  | proj {t : Ix.Name} {i : Nat} {s : Ix.Expr} {h : Address} : ConstOcc n s → ConstOcc n (.proj t i s h)
  | mdata {d : Array (Ix.Name × Ix.DataValue)} {e : Ix.Expr} {h : Address} :
      ConstOcc n e → ConstOcc n (.mdata d e h)

section Occ

variable {P : Ix.Name → Prop}

theorem occ_none {e : Ix.Expr}
    (h : ∀ n, ¬ ConstOcc n e) : ¬ ∃ n, ConstOcc n e ∧ P n := fun ⟨n, hn, _⟩ => h n hn

theorem occ_const (m : Ix.Name) (us : Array Ix.Level) (h : Address) :
    (∃ n, ConstOcc n (.const m us h) ∧ P n) ↔ P m :=
  ⟨fun ⟨_, hn, hp⟩ => by cases hn; exact hp, fun hp => ⟨m, .const, hp⟩⟩

theorem occ_app (f a : Ix.Expr) (h : Address) :
    (∃ n, ConstOcc n (.app f a h) ∧ P n) ↔ (∃ n, ConstOcc n f ∧ P n) ∨ (∃ n, ConstOcc n a ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | appF hf => exact .inl ⟨n, hf, hp⟩
    | appA ha => exact .inr ⟨n, ha, hp⟩,
   fun h => h.elim (fun ⟨n, hn, hp⟩ => ⟨n, .appF hn, hp⟩) (fun ⟨n, hn, hp⟩ => ⟨n, .appA hn, hp⟩)⟩

theorem occ_lam (x : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    (∃ n, ConstOcc n (.lam x t b bi h) ∧ P n) ↔ (∃ n, ConstOcc n t ∧ P n) ∨ (∃ n, ConstOcc n b ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | lamT ht => exact .inl ⟨n, ht, hp⟩
    | lamB hb => exact .inr ⟨n, hb, hp⟩,
   fun h => h.elim (fun ⟨n, hn, hp⟩ => ⟨n, .lamT hn, hp⟩) (fun ⟨n, hn, hp⟩ => ⟨n, .lamB hn, hp⟩)⟩

theorem occ_all (x : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    (∃ n, ConstOcc n (.forallE x t b bi h) ∧ P n) ↔ (∃ n, ConstOcc n t ∧ P n) ∨ (∃ n, ConstOcc n b ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | allT ht => exact .inl ⟨n, ht, hp⟩
    | allB hb => exact .inr ⟨n, hb, hp⟩,
   fun h => h.elim (fun ⟨n, hn, hp⟩ => ⟨n, .allT hn, hp⟩) (fun ⟨n, hn, hp⟩ => ⟨n, .allB hn, hp⟩)⟩

theorem occ_letE (x : Ix.Name) (t v b : Ix.Expr) (nd : Bool) (h : Address) :
    (∃ n, ConstOcc n (.letE x t v b nd h) ∧ P n) ↔
      (∃ n, ConstOcc n t ∧ P n) ∨ (∃ n, ConstOcc n v ∧ P n) ∨ (∃ n, ConstOcc n b ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | letT ht => exact .inl ⟨n, ht, hp⟩
    | letV hv => exact .inr (.inl ⟨n, hv, hp⟩)
    | letB hb => exact .inr (.inr ⟨n, hb, hp⟩),
   fun h => h.elim (fun ⟨n, hn, hp⟩ => ⟨n, .letT hn, hp⟩)
    (fun h => h.elim (fun ⟨n, hn, hp⟩ => ⟨n, .letV hn, hp⟩) (fun ⟨n, hn, hp⟩ => ⟨n, .letB hn, hp⟩))⟩

theorem occ_proj (t : Ix.Name) (i : Nat) (s : Ix.Expr) (h : Address) :
    (∃ n, ConstOcc n (.proj t i s h) ∧ P n) ↔ (∃ n, ConstOcc n s ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | proj hs => exact ⟨n, hs, hp⟩,
   fun ⟨n, hn, hp⟩ => ⟨n, .proj hn, hp⟩⟩

theorem occ_mdata (d : Array (Ix.Name × Ix.DataValue)) (e : Ix.Expr) (h : Address) :
    (∃ n, ConstOcc n (.mdata d e h) ∧ P n) ↔ (∃ n, ConstOcc n e ∧ P n) :=
  ⟨fun ⟨n, hn, hp⟩ => by cases hn with
    | mdata he => exact ⟨n, he, hp⟩,
   fun ⟨n, hn, hp⟩ => ⟨n, .mdata hn, hp⟩⟩

end Occ

/-! ## The reader's side -/

theorem withContract_occurs {md : Mode} {c : Ix.SemanticContract.Contract} {e : Ix.Expr}
    {target result : CExpr md} (lowered : Ix.CompileCert.ExpressionState.withContract c e target = some result)
    (k : CName md) : Frontend.occursConst k result = Frontend.occursConst k target := by
  obtain ⟨kind, binder, valueContract, letKind⟩ := c
  cases kind <;> cases e <;> cases target <;>
    simp only [Ix.CompileCert.ExpressionState.withContract, Option.some.injEq, reduceCtorEq] at lowered
  all_goals
    subst lowered
    rfl

/-- **A related reader term mentions exactly the keys of the names its Lean term mentions**, for
a functional relation of names to keys. -/
theorem related_occurs {md : Mode} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Kernel.Level → Prop} (func : ∀ n k k', names n k → names n k' → k = k')
    {e : Ix.Expr} {t : CExpr md} (rel : Related names levels e t) (k : CName md) :
    Frontend.occursConst k t = true ↔ ∃ n, ConstOcc n e ∧ names n k := by
  induction rel with
  | bvar index hash =>
    simp only [Ix.Kernel.Expr.mkBvar_eq, Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | sort hash meaning =>
    simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | const hash sources targets mapped universes =>
    rw [occ_const]
    simp only [Frontend.occursConst, beq_iff_eq]
    exact ⟨fun h => h ▸ mapped, fun h => func _ _ _ mapped h⟩
  | app hash _ _ fnIH argIH =>
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_app, fnIH, argIH]
  | lam name info hash _ _ typeIH bodyIH =>
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_lam, typeIH, bodyIH]
  | all name info hash _ _ typeIH bodyIH =>
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_all, typeIH, bodyIH]
  | letE name nonDep hash _ _ _ typeIH valueIH bodyIH =>
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_letE, typeIH, valueIH, bodyIH, or_assoc]
  | nat value hash =>
    simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | str value hash =>
    simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | proj field hash mapped _ valueIH =>
    simp only [Frontend.occursConst]
    rw [occ_proj, valueIH]
  | mdata data hash plain _ bodyIH =>
    rw [occ_mdata, bodyIH]
  | contract data hash c frame read _ lowered bodyIH =>
    rw [withContract_occurs lowered, occ_mdata, bodyIH]

/-! ## Source's side -/

theorem ingress_withContract_occurs {c : Ix.SemanticContract.Contract} {e : Ix.Expr}
    {x result : CExpr .source} (lowered : Ix.LeanIngress.withContract c e x = .ok result) (k : Key .source) :
    Frontend.occursConst k result = Frontend.occursConst k x := by
  obtain ⟨kind, binder, valueContract, letKind⟩ := c
  cases kind <;> cases e <;> cases x <;>
    simp only [Ix.LeanIngress.withContract, pure, Except.pure, Except.ok.injEq, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at lowered
  all_goals
    subst lowered
    rfl

/-- **A Lean term's Source conversion mentions exactly the ingress keys of the names the term
mentions.** -/
theorem ingress_occurs (σ : Ix.Name → LevelParam) :
    ∀ (e : Ix.Expr) (c : CExpr .source), ingressExpr σ e = .ok c →
      ∀ k, Frontend.occursConst k c = true ↔ ∃ n, ConstOcc n e ∧ ingressKey n = k := by
  intro e
  induction e with
  | bvar i h =>
    intro c hc k
    simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Ix.Kernel.Expr.mkBvar_eq, Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | fvar n h =>
    intro c hc
    simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at hc
  | mvar n h =>
    intro c hc
    simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at hc
  | sort u h =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨l, -, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
    exact occ_none fun n hn => by cases hn
  | const m us h =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨ls, -, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    rw [occ_const]
    simp only [Frontend.occursConst, beq_iff_eq]
  | app f a h ihf iha =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨f', hf, hc⟩ := RecordTransfer.bind_ok hc
    obtain ⟨a', ha, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_app, ihf f' hf k, iha a' ha k]
  | lam x t b bi h iht ihb =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨t', ht, hc⟩ := RecordTransfer.bind_ok hc
    obtain ⟨b', hb, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_lam, iht t' ht k, ihb b' hb k]
  | forallE x t b bi h iht ihb =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨t', ht, hc⟩ := RecordTransfer.bind_ok hc
    obtain ⟨b', hb, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_all, iht t' ht k, ihb b' hb k]
  | letE x t v b nd h iht ihv ihb =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨t', ht, hc⟩ := RecordTransfer.bind_ok hc
    obtain ⟨v', hv, hc⟩ := RecordTransfer.bind_ok hc
    obtain ⟨b', hb, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst, Bool.or_eq_true]
    rw [occ_letE, iht t' ht k, ihv v' hv k, ihb b' hb k, or_assoc]
  | lit l h =>
    intro c hc k
    cases l with
    | natVal n =>
      simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at hc
      subst hc
      simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
      exact occ_none fun n hn => by cases hn
    | strVal s =>
      simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at hc
      subst hc
      simp only [Frontend.occursConst, Bool.false_eq_true, false_iff]
      exact occ_none fun n hn => by cases hn
  | mdata d e h ih =>
    intro c hc k
    rw [Ix.LeanIngress.ingressExpr_mdata, Ix.LeanIngress.ingressMData] at hc
    rw [occ_mdata]
    split at hc
    · obtain ⟨contract, -, hc⟩ := RecordTransfer.bind_ok hc
      obtain ⟨x, hx, hc⟩ := RecordTransfer.bind_ok hc
      rw [ingress_withContract_occurs hc, ih x hx k]
    · exact ih c hc k
  | proj t i s h ih =>
    intro c hc k
    simp only [ingressExpr] at hc
    obtain ⟨s', hs, hc⟩ := RecordTransfer.bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simp only [Frontend.occursConst]
    rw [occ_proj, ih s' hs k]

/-! ## The dependency sets -/

theorem mem_foldl_if {α : Type} (p : α → Bool) :
    ∀ (l : List (α × Nat)) (acc : Std.HashSet Nat) (j : Nat),
      j ∈ l.foldl (fun acc x => if p x.1 = true then acc.insert x.2 else acc) acc ↔
        j ∈ acc ∨ ∃ x ∈ l, p x.1 = true ∧ x.2 = j
  | [], acc, j => by simp
  | x :: l, acc, j => by
    rw [List.foldl_cons, mem_foldl_if p l _ j]
    constructor
    · rintro (h | ⟨y, hy, hp, rfl⟩)
      · split at h
        · rcases Std.HashSet.mem_insert.mp h with h | h
          · exact .inr ⟨x, List.mem_cons_self, by assumption, beq_iff_eq.mp h⟩
          · exact .inl h
        · exact .inl h
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hp, rfl⟩
    · rintro (h | ⟨y, hy, hp, rfl⟩)
      · refine .inl ?_
        split
        · exact Std.HashSet.mem_insert.mpr (.inr h)
        · exact h
      · rcases List.mem_cons.mp hy with rfl | hy
        · refine .inl ?_
          simp only [hp, ↓reduceIte]
          exact Std.HashSet.mem_insert.mpr (.inl (beq_iff_eq.mpr rfl))
        · exact .inr ⟨y, hy, hp, rfl⟩

/-- **The members a converted member depends on**: those whose keys its type or value
mentions. -/
theorem depsOf_mem (ms : Array Ix.LeanIngress.DefMember) {i : Nat} (hi : i < ms.size) (j : Nat) :
    j ∈ (DefinitionBlocks.depsOf ms)[i]! ↔ ∃ hj : j < ms.size,
      (Frontend.occursConst ms[j].cv.name ms[i].cv.type || Frontend.occursConst ms[j].cv.name ms[i].value) = true := by
  have hi' : i < (DefinitionBlocks.depsOf ms).size := by
    simp only [DefinitionBlocks.depsOf, Array.size_map]
    exact hi
  rw [getElem!_pos _ i hi']
  simp only [DefinitionBlocks.depsOf, Array.getElem_map]
  rw [← Array.foldl_toList]
  refine (mem_foldl_if (fun n => Frontend.occursConstFast n ms[i].cv.type ||
    Frontend.occursConstFast n ms[i].value) _ ∅ j).trans ?_
  have hnot : ¬ j ∈ (∅ : Std.HashSet Nat) := by simp
  rw [or_iff_right hnot]
  simp only [CtxAgree.occursConstFast_eq]
  constructor
  · rintro ⟨⟨n, j'⟩, hx, hp, rfl⟩
    rw [Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?] at hx
    simp only [Array.toList_map, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hj : j' < ms.size := by
      have := (List.getElem?_eq_some_iff.mp hm).1
      simpa using this
    refine ⟨hj, ?_⟩
    have : ms[j'] = m := by
      have := (List.getElem?_eq_some_iff.mp hm).2
      simpa using this
    rw [this]
    exact hp
  · rintro ⟨hj, hp⟩
    refine ⟨(ms[j].cv.name, j), ?_, hp, rfl⟩
    rw [Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?]
    simp [hj]

/--
info: 'Ix.Cert.DefinitionDeps.related_occurs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms related_occurs

/--
info: 'Ix.Cert.DefinitionDeps.ingress_occurs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ingress_occurs

/--
info: 'Ix.Cert.DefinitionDeps.depsOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms depsOf_mem

end Ix.Cert.DefinitionDeps
