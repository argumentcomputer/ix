import Ix.CompileCert.SourceConstructorPositions

/-! # Quotient Source's conversion of a group, exactly

`Ix.LeanIngress.exprsOf` converts a group's terms in runs of one numbering; a run's numbering
compares structurally equal to each of its items' (`numbering_eq_of_beq`), so every item is
converted under its own numbering (`exprsOf_exact`). `convertInductive_exact` states what an
inductive group converts to: a block whose every type, constructor and recursor is converted
under its own numbering, under its ingress key, in the group's order, with the recursors'
rules and the motive their names give (`motiveOf`). -/

namespace Ix.Cert.SourceConversion

open Ix.LeanIngress (Numbering ingressExpr ingressExprs nameExprs exprsOf)
open Ix.Kernel.Reader (CExpr ReadError)
open Ix.CompileCert.Loop (forall₂_append mapM_forall₂ forIn_inv_array)

/-- An item converted under its own numbering. -/
def ConvertsExactly (item : Numbering × Ix.Expr) (k : CExpr .source) : Prop :=
  ingressExpr item.1.pos item.2 = .ok k

theorem numbering_eq_of_beq {σ τ : Numbering} (h : (σ == τ) = true) : σ = τ := by
  have h' : (σ.large == τ.large && σ.names.isEqv τ.names Ix.Name.beqRaw) = true := h
  rw [Bool.and_eq_true, beq_iff_eq, Array.isEqv_iff_rel] at h'
  obtain ⟨hl, hsize, hall⟩ := h'
  obtain ⟨σn, σl⟩ := σ
  obtain ⟨τn, τl⟩ := τ
  simp only at hl hsize hall
  subst hl
  congr 1
  exact Array.ext hsize fun i h₁ h₂ => Ix.Name.beqRaw_iff.mp (hall i h₁)

/-- `exprsOf`'s loop invariant: the conversions written so far are of the items before the
pending run, and the pending run's items are under its numbering. -/
def ExactInv (pre : List (Numbering × Ix.Expr))
    (s : Array (CExpr .source) × Option (Numbering × Array Ix.Expr)) : Prop :=
  ∃ done pend, pre = done ++ pend ∧ List.Forall₂ ConvertsExactly done s.1.toList ∧
    match s.2 with
    | none => pend = []
    | some (τ, es) => pend.map Prod.snd = es.toList ∧ ∀ p ∈ pend, p.1 = τ

theorem flush_exact {τ : Numbering} {es : Array Ix.Expr} {out out' : Array (CExpr .source)}
    {done pend : List (Numbering × Ix.Expr)} (prior : List.Forall₂ ConvertsExactly done out.toList)
    (terms : pend.map Prod.snd = es.toList) (same : ∀ p ∈ pend, p.1 = τ)
    (ran : (match ingressExprs τ.pos es.toList with
      | .ok ks => Except.ok (out ++ (nameExprs es.toList ks).toArray)
      | .error e => Except.error (ReadError.malformed (toString "source term: " ++ toString e))) = .ok out') :
    List.Forall₂ ConvertsExactly (done ++ pend) out'.toList := by
  split at ran
  · rename_i ks converted
    cases ran
    rw [Ix.LeanIngress.nameExprs_eq, Array.toList_append, List.toList_toArray]
    refine forall₂_append prior ?_
    have each := mapM_forall₂ (ingressExpr τ.pos) converted
    rw [← terms] at each
    clear terms converted
    induction pend generalizing ks with
    | nil => cases each; exact .nil
    | cons item pend ih =>
      cases each with
      | cons head tail =>
        refine .cons ?_ (ih (fun p hp => same p (List.mem_cons_of_mem _ hp)) _ tail)
        show ingressExpr item.1.pos item.2 = _
        rw [same item List.mem_cons_self]
        exact head
  · cases ran

/-- **`exprsOf` converts every item under its own numbering.** -/
theorem exprsOf_exact {items : Array (Numbering × Ix.Expr)} {ks : Array (CExpr .source)}
    (ran : exprsOf items = .ok ks) : List.Forall₂ ConvertsExactly items.toList ks.toList := by
  unfold exprsOf at ran
  simp only at ran
  obtain ⟨s, loop, final⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
  have inv := forIn_inv_array ExactInv _ items ?step ⟨[], [], rfl, .nil, rfl⟩ loop
  · obtain ⟨done, pend, whole, prior, pending⟩ := inv
    split at final
    · rename_i τ es run
      rw [run] at pending
      obtain ⟨out, flushed, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok final
      cases returned
      rw [whole]
      exact flush_exact prior pending.1 pending.2 flushed
    · rename_i none_
      cases run : s.2 with
      | some p => exact absurd run (by rcases p with ⟨τ, es⟩; exact none_ τ es)
      | none =>
        rw [run] at pending
        cases final
        rw [whole, pending, List.append_nil]
        exact prior
  · intro pre x post st r _ holds stepped
    obtain ⟨done, pend, whole, prior, pending⟩ := holds
    split at stepped
    · rename_i τ es run
      rw [run] at pending
      split at stepped
      · rename_i hbeq
        cases stepped
        refine ⟨_, rfl, done, pend ++ [x], by rw [whole, List.append_assoc], prior, ?_, ?_⟩
        · show (pend ++ [x]).map Prod.snd = (es.push x.2).toList
          rw [List.map_append, pending.1]
          simp
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact pending.2 p hp
          · rw [List.mem_singleton] at hp
            subst hp
            exact numbering_eq_of_beq hbeq
      · obtain ⟨out, flushed, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
        cases returned
        refine ⟨_, rfl, done ++ pend, [x], by rw [whole], flush_exact prior pending.1 pending.2 flushed,
          rfl, by simp⟩
    · rename_i run
      rw [run] at pending
      cases stepped
      refine ⟨_, rfl, done, [x], by rw [whole, pending, List.append_nil], prior, rfl, by simp⟩

/-! ## An inductive group's conversion -/

open Ix.LeanIngress (ingressKey Converted convertInductive)
open Ix.Kernel.Reader (CVal CName RecCounts BlockRead)
open Ix.CompileCert.SourceConstructorPositions (drop_cons drop_of_append forall₂_getElem?)

/-- A constructor's own numbering. -/
abbrev ownNum (cv : Ix.ConstantVal) : Numbering := ⟨cv.levelParams, false⟩

/-- A recursor's numbering, against its block's first type. -/
abbrev recNum (first : Ix.InductiveVal) (r : Ix.RecursorVal) : Numbering :=
  ⟨r.cnst.levelParams, r.cnst.levelParams.size == first.cnst.levelParams.size + 1⟩

/-- The motive quotient Source reads a recursor eliminates, by its name. -/
def motiveOf (types : Array Ix.InductiveVal) (r : Ix.RecursorVal) : Option Nat :=
  match r.cnst.name with
  | .str T "rec" _ => types.findIdx? (Ix.Name.beqRaw ·.cnst.name T)
  | _ => none

def TypeRel (v : Ix.InductiveVal) (e : CVal .source × Nat × Nat) : Prop :=
  e.1.name = ingressKey v.cnst.name ∧ e.1.levelParams = (ownNum v.cnst).params ∧
    ingressExpr (ownNum v.cnst).pos v.cnst.type = .ok e.1.type ∧ e.2.1 = v.numParams ∧ e.2.2 = v.numIndices

def CtorRel (nPd : Nat) (c : Ix.ConstructorVal) (e : CVal .source × Nat × Nat) : Prop :=
  e.1.name = ingressKey c.cnst.name ∧ e.1.levelParams = (ownNum c.cnst).params ∧
    ingressExpr (ownNum c.cnst).pos c.cnst.type = .ok e.1.type ∧ e.2.1 = c.numParams ∧ e.2.2 = c.numFields ∧
    nPd + c.numFields = Ix.Kernel.Reader.piTeleLen e.1.type

def RuleRel (σ : Numbering) (rule : Ix.RecursorRule) (rr : Ix.Kernel.RecRule .source) : Prop :=
  rr = ⟨ingressKey rule.ctor, rule.nfields, 0, .inert, rr.rhs, false, false, false⟩ ∧
    ingressExpr σ.pos rule.rhs = .ok rr.rhs

def RecRel (types : Array Ix.InductiveVal) (first : Ix.InductiveVal) (r : Ix.RecursorVal)
    (e : CVal .source × RecCounts × List (Ix.Kernel.RecRule .source)) : Prop :=
  e.1.name = ingressKey r.cnst.name ∧ e.1.levelParams = (recNum first r).params ∧
    ingressExpr (recNum first r).pos r.cnst.type = .ok e.1.type ∧
    e.2.1 = ⟨r.numParams, r.numMotives, r.numMinors, r.numIndices, r.k, motiveOf types r⟩ ∧
    List.Forall₂ (RuleRel (recNum first r)) r.rules.toList e.2.2

theorem cursor {items : List (Numbering × Ix.Expr)} {ks : Array (CExpr .source)}
    (K : List.Forall₂ ConvertsExactly items ks.toList) {i : Nat} {x : Numbering × Ix.Expr}
    {rest : List (Numbering × Ix.Expr)} (h : items.drop i = x :: rest) :
    ConvertsExactly x ks[i]! ∧ items.drop (i + 1) = rest := by
  obtain ⟨hx, hrest⟩ := drop_cons h
  obtain ⟨k, hk, hc⟩ := forall₂_getElem? K hx
  refine ⟨?_, hrest⟩
  rw [Array.getElem?_toList] at hk
  simp only [getElem!_def, hk]
  exact hc

/-- A type's item. -/
abbrev typeItem (v : Ix.InductiveVal) : Numbering × Ix.Expr := (ownNum v.cnst, v.cnst.type)
/-- A constructor's item. -/
abbrev ctorItem (c : Ix.ConstructorVal) : Numbering × Ix.Expr := (ownNum c.cnst, c.cnst.type)
/-- A recursor's items: its type, then its rules' right-hand sides. -/
def recItems (first : Ix.InductiveVal) (r : Ix.RecursorVal) : List (Numbering × Ix.Expr) :=
  (recNum first r, r.cnst.type) :: r.rules.toList.map fun x => (recNum first r, x.rhs)

/-- **What quotient Source's conversion of an inductive group is**: a block of the first
type's parameter count, each type, constructor and recursor converted under its own
numbering under its ingress key, in order, the recursors' rules after them. -/
theorem convertInductive_exact {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Converted} (ran : convertInductive types ctors recs = .ok conv) :
    ∃ first rb, types[0]? = some first ∧ conv = .inductive rb ∧ rb.numParams = first.numParams ∧
      List.Forall₂ TypeRel types.toList rb.types.toList ∧
      List.Forall₂ (CtorRel first.numParams) (ctors.toList.flatMap (·.toList)) rb.ctors.toList ∧
      rb.ctorNames.toList = ctors.toList.map (fun cs => cs.toList.map (ingressKey ·.cnst.name)) ∧
      List.Forall₂ (RecRel types first) recs.toList rb.recs.toList := by
  unfold convertInductive at ran
  split at ran
  · rename_i first firstEq
    simp only at ran
    split at ran
    · cases ran
    · split at ran
      · obtain ⟨ks, convertedEq, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
        have K := exprsOf_exact convertedEq
        replace K : List.Forall₂ ConvertsExactly (types.toList.map typeItem ++
            (ctors.toList.flatMap fun cs => cs.toList.map ctorItem) ++ recs.toList.flatMap (recItems first))
            ks.toList := by
          have e : ∀ L L' : List (Numbering × Ix.Expr), L = L' → List.Forall₂ ConvertsExactly L ks.toList →
              List.Forall₂ ConvertsExactly L' ks.toList := fun _ _ h k => h ▸ k
          refine e _ _ ?_ K
          simp [Array.toList_flatMap]
          rfl
        generalize hL : types.toList.map typeItem ++ (ctors.toList.flatMap fun cs => cs.toList.map ctorItem) ++
          recs.toList.flatMap (recItems first) = L at K
        obtain ⟨s₁, typesLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        obtain ⟨s₂, ctorsLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        obtain ⟨s₃, recsLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        -- the types
        have T := forIn_inv_array (fun (pre : List Ix.InductiveVal) (s : Nat × Array (CVal .source × Nat × Nat)) =>
            L.drop s.1 = (types.toList.drop pre.length).map typeItem ++
              ((ctors.toList.flatMap fun cs => cs.toList.map ctorItem) ++ recs.toList.flatMap (recItems first)) ∧
            List.Forall₂ TypeRel pre s.2.toList) _ types ?tstep ⟨by rw [← hL]; simp, .nil⟩ typesLoop
        case tstep =>
          intro pre v post st r whole holds stepped
          simp only [pure, Except.pure, Except.ok.injEq] at stepped
          subst stepped
          obtain ⟨cur, rel⟩ := holds
          rw [drop_of_append whole, List.map_cons, List.cons_append] at cur
          obtain ⟨conv, next⟩ := cursor K cur
          refine ⟨_, rfl, ?_, ?_⟩
          · rw [next, List.length_append, List.length_singleton, ← List.drop_drop, drop_of_append whole]
            rfl
          · rw [Array.toList_push]
            exact forall₂_append rel (.cons ⟨rfl, rfl, conv, rfl, rfl⟩ .nil)
        obtain ⟨tcur, trel⟩ := T
        rw [List.drop_length, List.map_nil, List.nil_append] at tcur
        -- the constructors
        have C := forIn_inv_array (fun (pre : List (Array Ix.ConstructorVal))
            (s : Nat × Array (CVal .source × Nat × Nat) × Array (List (CName .source))) =>
            L.drop s.1 = (ctors.toList.drop pre.length).flatMap (fun cs => cs.toList.map ctorItem) ++
              recs.toList.flatMap (recItems first) ∧
            List.Forall₂ (CtorRel first.numParams) (pre.flatMap (·.toList)) s.2.1.toList ∧
            s.2.2.toList = pre.map (fun cs => cs.toList.map (ingressKey ·.cnst.name))) _ ctors ?cstep
            ⟨by simpa using tcur, .nil, rfl⟩ ctorsLoop
        case cstep =>
          intro pre cs post st r whole holds stepped
          obtain ⟨cur, rel, names⟩ := holds
          rw [drop_of_append whole, List.flatMap_cons] at cur
          obtain ⟨inner, innerLoop, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
          cases returned
          have I := forIn_inv_array (fun (pre' : List Ix.ConstructorVal)
              (s : Nat × Array (CVal .source × Nat × Nat) × List (CName .source)) =>
              L.drop s.1 = (cs.toList.drop pre'.length).map ctorItem ++
                (post.flatMap (fun cs => cs.toList.map ctorItem) ++ recs.toList.flatMap (recItems first)) ∧
              List.Forall₂ (CtorRel first.numParams) (pre.flatMap (·.toList) ++ pre') s.2.1.toList ∧
              s.2.2 = pre'.map (ingressKey ·.cnst.name)) _ cs ?istep
              ⟨by simpa [List.append_assoc] using cur, by simpa using rel, rfl⟩ innerLoop
          case istep =>
            intro pre' c post' st' r' whole' holds' stepped'
            obtain ⟨cur', rel', names'⟩ := holds'
            rw [drop_of_append whole', List.map_cons, List.cons_append] at cur'
            obtain ⟨conv, next⟩ := cursor K cur'
            split at stepped'
            · rename_i hcheck
              simp only [pure, Except.pure, Except.ok.injEq] at stepped'
              subst stepped'
              refine ⟨_, rfl, ?_, ?_, ?_⟩
              · rw [next, List.length_append, List.length_singleton, ← List.drop_drop, drop_of_append whole']
                rfl
              · rw [Array.toList_push, ← List.append_assoc]
                exact forall₂_append rel' (.cons ⟨rfl, rfl, conv, rfl, rfl, beq_iff_eq.mp hcheck⟩ .nil)
              · simp [names']
            · cases stepped'
          obtain ⟨icur, irel, inames⟩ := I
          refine ⟨_, rfl, ?_, ?_, ?_⟩
          · show L.drop inner.1 = _
            rw [icur, List.drop_length, List.map_nil, List.nil_append, List.length_append,
              List.length_singleton, ← List.drop_drop, drop_of_append whole]
            rfl
          · show List.Forall₂ (CtorRel first.numParams) _ inner.2.1.toList
            simpa using irel
          · show (st.2.2.push inner.2.2).toList = _
            simp [names, inames]
        obtain ⟨ccur, crel, cnames⟩ := C
        -- the recursors
        have Rc := forIn_inv_array (fun (pre : List Ix.RecursorVal)
            (s : Nat × Array (CVal .source × RecCounts × List (Ix.Kernel.RecRule .source))) =>
            L.drop s.1 = (recs.toList.drop pre.length).flatMap (recItems first) ∧
            List.Forall₂ (RecRel types first) pre s.2.toList) _ recs ?rstep
            ⟨by rw [List.drop_length, List.flatMap_nil, List.nil_append] at ccur; simpa using ccur, .nil⟩ recsLoop
        case rstep =>
          intro pre r post st res whole holds stepped
          obtain ⟨cur, rel⟩ := holds
          rw [drop_of_append whole, List.flatMap_cons, recItems, List.cons_append] at cur
          obtain ⟨tconv, next⟩ := cursor K cur
          obtain ⟨inner, innerLoop, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
          cases returned
          have I := forIn_inv_array (fun (pre' : List Ix.RecursorRule)
              (s : Nat × List (Ix.Kernel.RecRule .source)) =>
              L.drop s.1 = (r.rules.toList.drop pre'.length).map (fun x => (recNum first r, x.rhs)) ++
                post.flatMap (recItems first) ∧
              List.Forall₂ (RuleRel (recNum first r)) pre' s.2) _ r.rules ?ustep
              ⟨by simpa using next, .nil⟩ innerLoop
          case ustep =>
            intro pre' rule post' st' r' whole' holds' stepped'
            obtain ⟨cur', rel'⟩ := holds'
            rw [drop_of_append whole', List.map_cons, List.cons_append] at cur'
            obtain ⟨conv, next'⟩ := cursor K cur'
            simp only [pure, Except.pure, Except.ok.injEq] at stepped'
            subst stepped'
            refine ⟨_, rfl, ?_, ?_⟩
            · rw [next', List.length_append, List.length_singleton, ← List.drop_drop, drop_of_append whole']
              rfl
            · exact forall₂_append rel' (.cons ⟨rfl, conv⟩ .nil)
          obtain ⟨icur, irel⟩ := I
          refine ⟨_, rfl, ?_, ?_⟩
          · show L.drop inner.1 = _
            rw [icur, List.drop_length, List.map_nil, List.nil_append, List.length_append,
              List.length_singleton, ← List.drop_drop, drop_of_append whole]
            rfl
          · rw [Array.toList_push]
            exact forall₂_append rel (.cons ⟨rfl, rfl, tconv, rfl, irel⟩ .nil)
        obtain ⟨-, rrel⟩ := Rc
        exact ⟨first, _, firstEq, rfl, rfl, trel, crel, cnames, rrel⟩
      · cases ran
  · cases ran

/--
info: 'Ix.Cert.SourceConversion.convertInductive_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms convertInductive_exact

end Ix.Cert.SourceConversion
