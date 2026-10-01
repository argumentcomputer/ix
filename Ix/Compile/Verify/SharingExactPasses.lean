import Ix.Compile.Verify.SharingExact

/-!
# Exact sharing: tie order and table materialization

* The uniform optimizer's tie order `setPrec` is a strict total order.
* Loop-level backwardness and expansion correctness of `materializeTable`
  (each entry built against the dictionary of the entries before it) and of
  `Prep.materializeDependent` (one dictionary, table in dependency order):
  entry `k` only references Share indices below `k`, the roots only indices
  below the table size (the Share part of `DecodeCtx.SharingWF`), and every
  output expands to its term.
-/

namespace Ix.Compile.Verify.SharingExact

open Ix.Sharing.Exact

/-! ## The uniform tie order -/

section TieOrder

instance compareDesc_trans : Std.TransCmp compareDesc :=
  inferInstanceAs (Std.TransCmp fun x y : Nat => compare y x)

instance compareDesc_lawfulEq : Std.LawfulEqCmp compareDesc :=
  inferInstanceAs (Std.LawfulEqCmp fun x y : Nat => compare y x)

theorem setPrec_iff (a b : Array Nat) :
    setPrec a b = true ↔ Array.compareLex compareDesc a b = .lt := by
  unfold setPrec
  cases Array.compareLex compareDesc a b <;> decide

/-- `setPrec` is irreflexive. -/
theorem setPrec_irrefl (a : Array Nat) : setPrec a a = false := by
  unfold setPrec
  rw [Std.ReflCmp.compare_self (cmp := Array.compareLex compareDesc)]
  rfl

/-- `setPrec` is asymmetric. -/
theorem setPrec_asymm {a b : Array Nat} (h : setPrec a b = true) : setPrec b a = false := by
  rw [setPrec_iff] at h
  unfold setPrec
  rw [Std.OrientedCmp.eq_swap (cmp := Array.compareLex compareDesc), h]
  rfl

/-- `setPrec` is transitive. -/
theorem setPrec_trans {a b c : Array Nat} (h₁ : setPrec a b = true)
    (h₂ : setPrec b c = true) : setPrec a c = true := by
  rw [setPrec_iff] at *
  exact Std.TransCmp.lt_trans h₁ h₂

/-- `setPrec` is total on distinct arrays. -/
theorem setPrec_total {a b : Array Nat} (h : a ≠ b) :
    setPrec a b = true ∨ setPrec b a = true := by
  rw [setPrec_iff, setPrec_iff]
  cases hc : Array.compareLex compareDesc a b
  · exact Or.inl rfl
  · exact absurd (Std.LawfulEqCmp.eq_of_compare hc) h
  · right
    rw [Std.OrientedCmp.eq_swap (cmp := Array.compareLex compareDesc), hc]
    rfl

end TieOrder

/-! ## Helpers -/

section Helpers

theorem SharesIn.mono {P Q : Nat → Prop} (hPQ : ∀ i, P i → Q i) (e : Ixon.Expr)
    (h : SharesIn P e) : SharesIn Q e := by
  induction e with
  | share i => exact hPQ _ h
  | prj _ _ v ih => exact ih h
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b iht ihb => exact ⟨iht h.1, ihb h.2⟩
  | all _ _ t b iht ihb => exact ⟨iht h.1, ihb h.2⟩
  | letE _ t v b iht ihv ihb => exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | _ => trivial

theorem foldl_some_mem {α : Type} (f : Option α → α → Option α)
    (hf : ∀ b o r, f b o = some r → r = o ∨ b = some r) :
    ∀ (l : List α) (init : Option α) (r : α),
      l.foldl f init = some r → r ∈ l ∨ init = some r := by
  intro l
  induction l with
  | nil => intro init r h; exact Or.inr h
  | cons x xs ih =>
    intro init r h
    rcases ih (f init x) r h with hm | hm
    · exact Or.inl (List.mem_cons_of_mem x hm)
    · rcases hf init x r hm with rfl | h'
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h'

/-- `pickOption` picks one of the offered options. -/
theorem pickOption_mem (opts : Array (Choice × Nat × ByteArray)) {ch : Choice} {c : Nat}
    (h : pickOption opts = some (ch, c)) : ∃ b, (ch, c, b) ∈ opts.toList := by
  unfold pickOption at h
  rw [← Array.foldl_toList] at h
  cases hr : List.foldl _ none opts.toList with
  | none => rw [hr] at h; cases h
  | some o =>
    rw [hr] at h
    obtain ⟨ch', c', b'⟩ := o
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨b', ?_⟩
    have key := foldl_some_mem _ (by
      intro b o r hb
      cases b with
      | none => simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
      | some b =>
        simp only at hb
        split at hb
        · simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
        · split at hb
          · simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
          · exact Or.inr hb) _ _ _ hr
    rcases key with hm | hm
    · exact hm
    · cases hm

/-- With the `Share` options filtered out, the pick is not a `Share`. -/
theorem pickOption_filter_ne_share (opts : Array (Choice × Nat × ByteArray))
    {ch : Choice} {c : Nat}
    (h : pickOption (opts.filter (·.1 != .share)) = some (ch, c)) : ch ≠ .share := by
  obtain ⟨b, hb⟩ := pickOption_mem _ h
  rw [Array.toList_filter, List.mem_filter] at hb
  intro hch
  subst hch
  have h2 : ((Choice.share, c, b).1 != Choice.share) = false := rfl
  rw [h2] at hb
  exact Bool.false_ne_true hb.2

end Helpers

/-! ## Descendants in the DAG -/

section Desc

/-- Every node has exactly `head.arity` children (the interner's arity
invariant). -/
def DagArity (dag : Dag) : Prop :=
  ∀ t, (dag.node t).children.size = (dag.node t).head.arity

/-- `u` is `t` or lies below it through child edges. -/
inductive Desc (dag : Dag) : Nat → Nat → Prop
  | refl (t : Nat) : Desc dag t t
  | child {t u : Nat} (k : Nat) (hk : k < (dag.node t).children.size)
      (h : Desc dag ((dag.node t).child k) u) : Desc dag t u

/-- `u` lies strictly below `t`. -/
def Below (dag : Dag) (t u : Nat) : Prop :=
  ∃ k, k < (dag.node t).children.size ∧ Desc dag ((dag.node t).child k) u

theorem Below.desc {dag : Dag} {t u : Nat} (h : Below dag t u) : Desc dag t u :=
  let ⟨k, hk, hd⟩ := h
  .child k hk hd

theorem Desc.trans {dag : Dag} {t v u : Nat} (h₁ : Desc dag t v) (h₂ : Desc dag v u) :
    Desc dag t u := by
  induction h₁ with
  | refl => exact h₂
  | child k hk _ ih => exact .child k hk (ih h₂)

theorem Below.trans_desc {dag : Dag} {t v u : Nat} (h₁ : Below dag t v) (h₂ : Desc dag v u) :
    Below dag t u :=
  let ⟨k, hk, hd⟩ := h₁
  ⟨k, hk, hd.trans h₂⟩

theorem Desc.trans_below {dag : Dag} {t v u : Nat} (h₁ : Desc dag t v) (h₂ : Below dag v u) :
    Below dag t u := by
  cases h₁ with
  | refl => exact h₂
  | child k hk hd => exact ⟨k, hk, hd.trans h₂.desc⟩

theorem below_child {dag : Dag} {t k : Nat} (hk : k < (dag.node t).children.size) :
    Below dag t ((dag.node t).child k) :=
  ⟨k, hk, .refl _⟩

/-- A telescope node. -/
def IsSpine (n : Node) : Prop :=
  match n.head with
  | .app | .lam _ | .all .. => True
  | _ => False

theorem spine_children {dag : Dag} (harity : DagArity dag) (v : Nat)
    (hs : IsSpine (dag.node v)) :
    Below dag v (dag.node v).spineNext ∧ Below dag v (dag.node v).sideChild := by
  have ha := harity v
  unfold IsSpine at hs
  unfold Node.spineNext Node.sideChild
  cases hh : (dag.node v).head <;> simp only [hh, Head.arity] at ha hs ⊢ <;>
    first | exact hs.elim | exact ⟨below_child (by omega), below_child (by omega)⟩

theorem spineFold_spine (buildSide : Node → Except SharingError Ixon.Expr) :
    ∀ (ns : List Node) (tail res : Ixon.Expr),
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok res → ∀ n ∈ ns, IsSpine n := by
  intro ns
  induction ns with
  | nil => intro _ _ _ n hn; cases hn
  | cons m ns ih =>
    intro tail res h n hn
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := bind_eq_ok h
    obtain ⟨side, _, hre⟩ := bind_eq_ok hstep
    rcases List.mem_cons.mp hn with rfl | hn
    · unfold IsSpine
      cases hh : n.head <;> simp only [rebuildSpineNode, hh] at hre <;> first | trivial | cases hre
    · exact ih tail acc hacc n hn

theorem spineFold_shares_mem (P : Nat → Prop)
    (buildSide : Node → Except SharingError Ixon.Expr) :
    ∀ (ns : List Node) (tail res : Ixon.Expr),
      (∀ n ∈ ns, ∀ e, buildSide n = .ok e → SharesIn P e) → SharesIn P tail →
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok res → SharesIn P res := by
  intro ns
  induction ns with
  | nil => intro tail res _ ht h; simp only [List.foldrM_nil] at h; cases h; exact ht
  | cons n ns ih =>
    intro tail res hside ht h
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := bind_eq_ok h
    have hinner := ih tail acc (fun m hm => hside m (List.mem_cons_of_mem n hm)) ht hacc
    obtain ⟨side, hs, hre⟩ := bind_eq_ok hstep
    have hside' := hside n List.mem_cons_self side hs
    cases hh : n.head <;> simp only [rebuildSpineNode, hh] at hre <;> cases hre <;>
      exact ⟨by assumption, by assumption⟩

/-- The nodes collected by a walk of telescope nodes lie on the walk below
`t`, and a nonempty walk ends strictly below `t`. -/
theorem spineWalk_desc (p : Prep) (harity : DagArity p.dag) :
    ∀ (j t : Nat), (∀ n ∈ (p.spineWalk j t).1, IsSpine n) →
      (∀ n ∈ (p.spineWalk j t).1, ∃ v, Desc p.dag t v ∧ n = p.dag.node v) ∧
      (0 < j → Below p.dag t (p.spineWalk j t).2) ∧ Desc p.dag t (p.spineWalk j t).2 := by
  intro j
  induction j with
  | zero =>
    intro t _
    refine ⟨fun n hn => ?_, fun h => absurd h (Nat.lt_irrefl 0), Desc.refl t⟩
    simp [Prep.spineWalk] at hn
  | succ j ih =>
    intro t hs
    simp only [Prep.spineWalk] at hs ⊢
    have hst : IsSpine (p.dag.node t) := hs _ List.mem_cons_self
    have hnext := (spine_children harity t hst).1
    obtain ⟨hns, _, hend⟩ := ih (p.dag.node t).spineNext
      (fun n hn => hs n (List.mem_cons_of_mem _ hn))
    refine ⟨?_, fun _ => hnext.trans_desc hend, hnext.desc.trans hend⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨t, .refl t, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hns n hn
      exact ⟨v, hnext.desc.trans hv, rfl⟩

end Desc

/-! ## Descendant-tracking build -/

section Build

/-- `Share(i)` names a dictionary term that is `t` itself (only outside an
entry body) or lies strictly below `t`. -/
def ShareFrom (dag : Dag) (index : Array (Option Nat)) (entry : Bool) (t i : Nat) : Prop :=
  ∃ u, index[u]?.getD none = some i ∧ ((entry = false ∧ u = t) ∨ Below dag t u)

theorem shareFrom_lift {dag : Dag} {index : Array (Option Nat)} {entry : Bool} {t c : Nat}
    (hc : Below dag t c) (i : Nat) (h : ShareFrom dag index false c i) :
    ShareFrom dag index entry t i := by
  obtain ⟨u, hu, hor⟩ := h
  refine ⟨u, hu, Or.inr ?_⟩
  rcases hor with ⟨_, rfl⟩ | hb
  · exact hc
  · exact hc.trans_desc hb.desc

/-- Every `Share` emitted while building `t` names a dictionary term below
`t`, or `t` itself when `t` is not being built as its own entry body. -/
theorem build_shares_below (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (harity : DagArity p.dag)
    (hidx : ∀ (u i : Nat), index[u]?.getD none = some i → i < UInt64.size) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr),
      p.build ev index width entry fuel t = .ok e →
        SharesIn (ShareFrom p.dag index entry t) e := by
  intro fuel
  induction fuel with
  | zero => intro entry t e h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e h
    have lift : ∀ c e', Below p.dag t c → p.build ev index width false fuel c = .ok e' →
        SharesIn (ShareFrom p.dag index entry t) e' := fun c e' hc h' =>
      SharesIn.mono (shareFrom_lift hc) _ (ih false c e' h')
    have hshare : ∀ u i, index[u]?.getD none = some i →
        ((entry = false ∧ u = t) ∨ Below p.dag t u) →
        SharesIn (ShareFrom p.dag index entry t) (.share i.toUInt64) := by
      intro u i hi hu
      simp only [SharesIn, toNat_toUInt64_of_lt (hidx u i hi)]
      exact ⟨u, hi, hu⟩
    have ha := harity t
    simp only [Prep.build] at h
    split at h
    · rename_i choice c hpick
      split at h
      · split at h
        · -- Share
          split at h
          · rename_i i hi
            cases h
            refine hshare t i hi (Or.inl ⟨?_, rfl⟩)
            cases entry
            · rfl
            · exact absurd rfl (pickOption_filter_ne_share _ (by simpa using hpick))
          · cases h
        · -- inline node
          cases hh : (p.dag.node t).head <;> simp only [hh] at h
          case prj ti f =>
            obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
            cases hpure
            exact lift _ v (below_child (by rw [ha, hh]; simp [Head.arity])) hv
          case letE lc =>
            obtain ⟨ty, hty, h2⟩ := bind_eq_ok h
            obtain ⟨v, hv, h3⟩ := bind_eq_ok h2
            obtain ⟨b, hb, hpure⟩ := bind_eq_ok h3
            cases hpure
            exact ⟨lift _ ty (below_child (by rw [ha, hh]; simp [Head.arity])) hty,
              lift _ v (below_child (by rw [ha, hh]; simp [Head.arity])) hv,
              lift _ b (below_child (by rw [ha, hh]; simp [Head.arity])) hb⟩
          all_goals first
            | (cases h; simp only [SharesIn, Node.toExpr, hh])
            | cases h
        · -- telescope cut
          split at h
          · cases h
          rename_i hj0
          split at h
          · split at h
            · rename_i i hi
              simp only [pure_bind] at h
              have hsp := spineFold_spine _ _ _ _ h
              obtain ⟨hns, hcur, -⟩ := spineWalk_desc p harity _ t hsp
              refine spineFold_shares_mem _ _ _ _ _ ?_
                (hshare _ i hi (Or.inr (hcur (Nat.pos_of_ne_zero hj0)))) h
              intro n hn e' he'
              obtain ⟨v, hv, rfl⟩ := hns n hn
              exact lift _ e' (hv.trans_below (spine_children harity v (hsp _ hn)).2) he'
            · cases h
          · obtain ⟨tail, htail, hfold⟩ := bind_eq_ok h
            have hsp := spineFold_spine _ _ _ _ hfold
            obtain ⟨hns, hcur, -⟩ := spineWalk_desc p harity _ t hsp
            refine spineFold_shares_mem _ _ _ _ _ ?_
              (lift _ tail (hcur (Nat.pos_of_ne_zero hj0)) htail) hfold
            intro n hn e' he'
            obtain ⟨v, hv, rfl⟩ := hns n hn
            exact lift _ e' (hv.trans_below (spine_children harity v (hsp _ hn)).2) he'
      · cases h
    · cases h

end Build

/-! ## Dictionaries and lists -/

section Dictionaries

theorem indexOfPairs_mem (size : Nat) (pairs : List (Nat × Nat)) :
    ∀ (u i : Nat), (indexOfPairs size pairs)[u]?.getD none = some i → (u, i) ∈ pairs := by
  unfold indexOfPairs
  suffices hs : ∀ (l : List (Nat × Nat)) (acc : Array (Option Nat)), (∀ x ∈ l, x ∈ pairs) →
      (∀ (u i : Nat), acc[u]?.getD none = some i → (u, i) ∈ pairs) →
      ∀ (u i : Nat), (l.foldl (fun acc (t, i) => acc.set! t (some i)) acc)[u]?.getD none =
        some i → (u, i) ∈ pairs by
    refine hs pairs _ (fun x hx => hx) (fun u i hu => ?_)
    simp only [Array.getElem?_replicate] at hu
    split at hu <;> simp at hu
  intro l
  induction l with
  | nil => intro acc _ hacc; simpa using hacc
  | cons x xs ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    apply ih _ (fun y hy => hl y (List.mem_cons_of_mem x hy))
    intro u i hu
    obtain ⟨t, j⟩ := x
    simp only [Array.set!, Array.getElem?_setIfInBounds] at hu
    split at hu
    · rename_i htu
      split at hu
      · simp only [Option.getD_some, Option.some.injEq] at hu
        subst hu htu
        exact hl _ List.mem_cons_self
      · simp at hu
    · exact hacc u i hu

/-- The dictionary of the first `k` entries maps `u` to `i` only if entry
`i < k` is `u`. -/
theorem indexOfPrefix_spec (size : Nat) (table : Array Nat) (k u i : Nat)
    (h : (indexOfPrefix size table k)[u]?.getD none = some i) :
    i < k ∧ table[i]? = some u := by
  have hm := indexOfPairs_mem size _ u i h
  rw [List.mem_zipIdx_iff_getElem?] at hm
  simp only [List.getElem?_take] at hm
  split at hm
  · rename_i hik
    refine ⟨hik, ?_⟩
    simpa using hm
  · cases hm

/-- The dictionary of a whole table maps `u` to `i` only if entry `i` is `u`. -/
theorem indexOfTable_spec (size : Nat) (table : Array Nat) (u i : Nat)
    (h : (indexOfPairs size table.toList.zipIdx)[u]?.getD none = some i) :
    table[i]? = some u := by
  have hm := indexOfPairs_mem size _ u i h
  rw [List.mem_zipIdx_iff_getElem?] at hm
  simpa using hm

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      xs.length = ys.length ∧
        ∀ (k : Nat) (h₁ : k < xs.length) (h₂ : k < ys.length), R xs[k] ys[k]
  | _, _, .nil => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | _, _, .cons hr hs => by
    obtain ⟨hl, hk⟩ := forall₂_getElem hs
    refine ⟨by simp [hl], fun k h₁ h₂ => ?_⟩
    cases k with
    | zero => exact hr
    | succ k => exact hk k (by simpa using h₁) (by simpa using h₂)

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x, R x y
  | _, _, .nil => fun _ h => by cases h
  | _, _, .cons hr hs => fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, hr⟩
    · exact forall₂_mem_right hs y hy

theorem array_mapM_forall₂ {α β ε : Type} (f : α → Except ε β) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error err => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h
    have : ys = l.toArray := by cases h; rfl
    subst this
    exact mapM_ok_forall₂ f _ _ hm

end Dictionaries

/-! ## Table materialization -/

section Table

/-- A successful `materializeWith` builds every target standalone. -/
theorem materializeWith_forall₂ (p : Prep) (index width : Array (Option Nat))
    (targets : Array Nat) (limits : Limits) {out : Array Ixon.Expr} {cost : Array Nat}
    {work : Nat} (h : p.materializeWith index width targets limits = .ok (out, cost, work)) :
    List.Forall₂ (fun t e =>
      p.build (p.evalAll width) index width false (p.dag.size + 1) t = .ok e)
      targets.toList out.toList := by
  unfold Prep.materializeWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  simp only at h
  split at h
  · cases h
  · obtain ⟨out', hout, hret⟩ := bind_eq_ok h
    cases hret
    exact array_mapM_forall₂ _ _ _ hout

/-- A materialized entry is the standalone build of `table[i]` against the
dictionary of the entries before it. -/
theorem materializeEntry_build (p : Prep) (table : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) (i : Nat) {e : Ixon.Expr} {c w : Nat}
    (h : materializeEntry p table limits widthAt i = .ok (e, c, w)) :
    ∃ ev width, p.build ev (indexOfPrefix p.dag.size table i) width false
      (p.dag.size + 1) table[i]! = .ok e := by
  unfold materializeEntry at h
  obtain ⟨⟨es, cost, w'⟩, hm, h⟩ := bind_eq_ok h
  simp only at h
  split at h
  · rename_i e' he'
    cases h
    have hf := forall₂_getElem (materializeWith_forall₂ p _ _ _ limits hm)
    have h0 : 0 < es.toList.length := by
      rw [Array.length_toList]
      exact (Array.getElem?_eq_some_iff.mp he').1
    have := hf.2 0 (by simp) h0
    have he0 : es.toList[0] = e := by
      rw [Array.getElem_toList]
      simpa using (Array.getElem?_eq_some_iff.mp he').2
    change p.build _ _ _ false _ table[i]! = .ok es.toList[0] at this
    rw [he0] at this
    exact ⟨_, _, this⟩
  · cases h

/-- The entry pass builds each listed entry in order. -/
theorem materializeEntries_spec (p : Prep) (table : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) :
    ∀ (is : List Nat) (entries : Array Ixon.Expr) (pr wk : Nat) {out : Array Ixon.Expr}
      {pr' wk' : Nat},
      materializeEntries p table limits widthAt is entries pr wk = .ok (out, pr', wk') →
      ∃ es : List Ixon.Expr, out = entries ++ es.toArray ∧
        List.Forall₂ (fun i e => ∃ c w, materializeEntry p table limits widthAt i = .ok (e, c, w))
          is es := by
  intro is
  induction is with
  | nil =>
    intro entries pr wk out pr' wk' h
    simp only [materializeEntries] at h
    cases h
    exact ⟨[], by simp, .nil⟩
  | cons i is ih =>
    intro entries pr wk out pr' wk' h
    simp only [materializeEntries] at h
    obtain ⟨⟨e, c, w⟩, he, h⟩ := bind_eq_ok h
    simp only at h
    split at h
    · cases h
    · obtain ⟨es, rfl, hes⟩ := ih _ _ _ h
      exact ⟨e :: es, by simp, .cons ⟨c, w, he⟩ hes⟩

/-- The parts of a successful `materializeTable`: the entry pass over
`0, …, size − 1` and the roots built against the whole table. -/
theorem materializeTable_parts (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (h : materializeTable p table roots limits widthAt = .ok (entries, rs, predicted, work)) :
    (∃ es : List Ixon.Expr, entries = es.toArray ∧
      List.Forall₂ (fun i e => ∃ c w, materializeEntry p table limits widthAt i = .ok (e, c, w))
        (List.range table.size) es) ∧
    ∃ cost w, p.materializeWith (indexOfPrefix p.dag.size table table.size)
      ((indexOfPrefix p.dag.size table table.size).map (·.map widthAt)) roots limits =
        .ok (rs, cost, w) := by
  unfold materializeTable at h
  obtain ⟨⟨entries', pr, wk⟩, hE, h⟩ := bind_eq_ok h
  simp only at h
  obtain ⟨⟨rs', cost, w⟩, hR, h⟩ := bind_eq_ok h
  simp only at h
  split at h
  · cases h
  · cases h
    obtain ⟨es, hes, hfor⟩ := materializeEntries_spec p table limits widthAt _ _ _ _ hE
    exact ⟨⟨es, by simpa using hes, hfor⟩, cost, w, hR⟩

theorem getElem!_of_getElem? {table : Array Nat} {i u : Nat} (h : table[i]? = some u) :
    table[i]! = u := by
  simp [getElem!_def, h]

/-- The prefix dictionary of a table is modelled by the table's terms. -/
theorem indexModel_prefix (size : Nat) (table : Array Nat) (k : Nat)
    (hk : k ≤ UInt64.size) (E : Nat → Ixon.Expr) :
    IndexModel (indexOfPrefix size table k) E (fun i => E table[i]!) := by
  intro u i h
  obtain ⟨hik, hsome⟩ := indexOfPrefix_spec size table k u i h
  exact ⟨by omega, by simp only [getElem!_of_getElem? hsome]⟩

/-- Loop-level backwardness of `materializeTable`: entry `k` only references
Share indices below `k`, and the roots only indices below the table size
(the Share part of `DecodeCtx.SharingWF`). -/
theorem materializeTable_backward (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) (hsize : table.size ≤ UInt64.size)
    {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (h : materializeTable p table roots limits widthAt = .ok (entries, rs, predicted, work)) :
    entries.size = table.size ∧
      (∀ (k : Nat) (hk : k < entries.size), SharesIn (· < k) entries[k]) ∧
      ∀ r ∈ rs.toList, SharesIn (· < table.size) r := by
  obtain ⟨⟨es, rfl, hes⟩, cost, w, hroots⟩ := materializeTable_parts p table roots limits widthAt h
  obtain ⟨hlen, hget⟩ := forall₂_getElem hes
  simp only [List.length_range] at hlen
  refine ⟨by simp [hlen], fun k hk => ?_, fun r hr => ?_⟩
  · have hk' : k < es.length := by simpa using hk
    obtain ⟨c, w, he⟩ := hget k (by simp; omega) hk'
    simp only [List.getElem_range] at he
    obtain ⟨ev, width, hb⟩ := materializeEntry_build p table limits widthAt k he
    simpa using build_prefix_backward p ev table k (by omega) width _ false _ _ hb
  · obtain ⟨t, ht⟩ := forall₂_mem_right (materializeWith_forall₂ p _ _ roots limits hroots) r hr
    exact build_prefix_backward p _ table table.size hsize _ _ false _ _ ht

/-- Expansion correctness of `materializeTable`: with every `Share(i)`
replaced by the term of entry `i`, entry `k` is the term `table[k]` and each
root is its term. -/
theorem materializeTable_correct (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) (hsize : table.size ≤ UInt64.size)
    {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (h : materializeTable p table roots limits widthAt = .ok (entries, rs, predicted, work))
    (E : Nat → Ixon.Expr) (hE : DagModel p.dag E) :
    (∀ (k : Nat) (hk : k < entries.size),
        substShares (fun i => E table[i]!) entries[k] = E table[k]!) ∧
      List.Forall₂ (fun r e => substShares (fun i => E table[i]!) e = E r)
        roots.toList rs.toList := by
  obtain ⟨⟨es, rfl, hes⟩, cost, w, hroots⟩ := materializeTable_parts p table roots limits widthAt h
  obtain ⟨hlen, hget⟩ := forall₂_getElem hes
  simp only [List.length_range] at hlen
  refine ⟨fun k hk => ?_, ?_⟩
  · have hk' : k < es.length := by simpa using hk
    obtain ⟨c, w, he⟩ := hget k (by simp; omega) hk'
    simp only [List.getElem_range] at he
    obtain ⟨ev, width, hb⟩ := materializeEntry_build p table limits widthAt k he
    simpa using build_correct p ev _ width E _ hE
      (indexModel_prefix p.dag.size table k (by omega) E) _ false _ _ hb
  · exact materializeWith_correct p _ _ roots limits rs cost w hroots E _ hE
      (indexModel_prefix p.dag.size table table.size hsize E)

/-- The parts of a successful `materializeDependent`: the table fits the
Share word, entries are built as entry bodies and roots standalone, all
against the dictionary of the whole table. -/
theorem materializeDependent_parts (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (limits : Limits) {es rs : Array Ixon.Expr} {total work : Nat}
    (h : p.materializeDependent table roots width limits = .ok (es, rs, total, work)) :
    table.size < UInt64.size ∧
      List.Forall₂ (fun t e => p.build (p.evalAll width)
        (indexOfPairs p.dag.size table.toList.zipIdx) width true (p.dag.size + 1) t = .ok e)
        table.toList es.toList ∧
      List.Forall₂ (fun r e => p.build (p.evalAll width)
        (indexOfPairs p.dag.size table.toList.zipIdx) width false (p.dag.size + 1) r = .ok e)
        roots.toList rs.toList := by
  unfold Prep.materializeDependent at h
  split at h
  · cases h
  rename_i hword
  simp only at h
  split at h
  · cases h
  obtain ⟨es', hes, h⟩ := bind_eq_ok h
  obtain ⟨rs', hrs, h⟩ := bind_eq_ok h
  cases h
  refine ⟨by unfold wordBound at hword; omega, array_mapM_forall₂ _ _ _ hes,
    array_mapM_forall₂ _ _ _ hrs⟩

/-- Loop-level backwardness of `materializeDependent`: if the table is in
dependency order (a stored term below entry `k` is stored at an index below
`k`), entry `k` only references Share indices below `k` and the roots only
indices below the table size (the Share part of `DecodeCtx.SharingWF`). -/
theorem materializeDependent_backward (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (limits : Limits) (harity : DagArity p.dag)
    (horder : ∀ (k j : Nat) (hk : k < table.size) (hj : j < table.size),
      Below p.dag table[k] table[j] → j < k)
    {es rs : Array Ixon.Expr} {total work : Nat}
    (h : p.materializeDependent table roots width limits = .ok (es, rs, total, work)) :
    es.size = table.size ∧
      (∀ (k : Nat) (hk : k < es.size), SharesIn (· < k) es[k]) ∧
      ∀ r ∈ rs.toList, SharesIn (· < table.size) r := by
  obtain ⟨hword, hes, hrs⟩ := materializeDependent_parts p table roots width limits h
  have hspec := indexOfTable_spec p.dag.size table
  have hidx : ∀ (u i : Nat), (indexOfPairs p.dag.size table.toList.zipIdx)[u]?.getD none =
      some i → i < UInt64.size := fun u i hi => by
    have := (Array.getElem?_eq_some_iff.mp (hspec u i hi)).1
    omega
  obtain ⟨hlen, hget⟩ := forall₂_getElem hes
  simp only [Array.length_toList] at hlen
  refine ⟨hlen.symm, fun k hk => ?_, fun r hr => ?_⟩
  · have hb := hget k (by simp; omega) (by simpa using hk)
    simp only [Array.getElem_toList] at hb
    refine SharesIn.mono ?_ _
      (build_shares_below p _ _ width harity hidx _ true _ _ hb)
    rintro i ⟨u, hu, hor⟩
    rcases hor with ⟨hf, _⟩ | hbelow
    · cases hf
    · obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp (hspec u i hu)
      exact horder k i (by omega) hi hbelow
  · obtain ⟨t, ht⟩ := forall₂_mem_right hrs r hr
    refine SharesIn.mono ?_ _ (build_shares_below p _ _ width harity hidx _ false _ _ ht)
    rintro i ⟨u, hu, -⟩
    exact (Array.getElem?_eq_some_iff.mp (hspec u i hu)).1

/-- Expansion correctness of `materializeDependent`: with every `Share(i)`
replaced by the term of entry `i`, entry `k` is the term `table[k]` and each
root is its term. -/
theorem materializeDependent_correct (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (limits : Limits)
    {es rs : Array Ixon.Expr} {total work : Nat}
    (h : p.materializeDependent table roots width limits = .ok (es, rs, total, work))
    (E : Nat → Ixon.Expr) (hE : DagModel p.dag E) :
    List.Forall₂ (fun t e => substShares (fun i => E table[i]!) e = E t)
        table.toList es.toList ∧
      List.Forall₂ (fun r e => substShares (fun i => E table[i]!) e = E r)
        roots.toList rs.toList := by
  obtain ⟨hword, hes, hrs⟩ := materializeDependent_parts p table roots width limits h
  have hσ : IndexModel (indexOfPairs p.dag.size table.toList.zipIdx) E
      (fun i => E table[i]!) := by
    intro u i hi
    have hsome := indexOfTable_spec p.dag.size table u i hi
    have := (Array.getElem?_eq_some_iff.mp hsome).1
    exact ⟨by omega, by simp only [getElem!_of_getElem? hsome]⟩
  exact ⟨forall₂_imp (fun t e he => build_correct p _ _ width E _ hE hσ _ true t e he) hes,
    forall₂_imp (fun r e he => build_correct p _ _ width E _ hE hσ _ false r e he) hrs⟩

end Table

end Ix.Compile.Verify.SharingExact
