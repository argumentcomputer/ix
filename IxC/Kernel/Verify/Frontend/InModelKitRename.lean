module

public import IxC.Kernel.Verify.Frontend.InModelScope
public import IxC.Kernel.Verify.Rename.Shape

@[expose] public section

/-!
# The kit's walks under a renaming injective on a scope (parametricity, step 3)

The memo-free readings of the kit's DAG walks (`Verify/Frontend/InModelMemo.lean`)
under `Expr.mapKeys f`: `mentionsAnyP` compares keys (`List.contains`), so it
commutes where `f` is injective on the good keys (`contains_map_ren`); `specFamP`
looks members up (`find? (·.1 == n)`), likewise; `maxHeightP` reads the heights at
the keys it meets; `substParamsP` compares no key. With each, the goodness of
what it returns.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode} {P : KeyScope md} {f : md.Id → md'.Id}

/-! ## Keyed lookups -/

/-- A list keyed by its first components, renamed. -/
def keyMap {β : Type} (f : md.Id → md'.Id) (l : List (Key md × β)) : List (Key md' × β) :=
  l.map fun x => (x.1.map f, x.2)

@[simp] theorem keyMap_nil {β : Type} : keyMap f ([] : List (Key md × β)) = [] := rfl
@[simp] theorem keyMap_cons {β : Type} (x : Key md × β) (l : List (Key md × β)) :
    keyMap f (x :: l) = (x.1.map f, x.2) :: keyMap f l := rfl
@[simp] theorem keyMap_length {β : Type} (l : List (Key md × β)) : (keyMap f l).length = l.length :=
  List.length_map _

/-- **A lookup by a good key in a renamed list of good keys** finds the renamed
entry. -/
theorem find?_keyMap {β : Type} (hf : InjOn f P) {l : List (Key md × β)}
    (hl : ∀ x ∈ l, x.1.Good P) {n : Key md} (hn : n.Good P) :
    (keyMap f l).find? (·.1 == n.map f) = (l.find? (·.1 == n)).map fun x => (x.1.map f, x.2) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [keyMap_cons, List.find?_cons]
    rw [Key.map_beq hf (hl a List.mem_cons_self) hn]
    cases a.1 == n
    · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    · rfl

/-- `==` on renamed lists of good terms is `==` on the lists. -/
theorem list_mapKeys_beq (hf : InjOn f P) {as bs : List (Expr md)} (ha : Expr.GoodList P as)
    (hb : Expr.GoodList P bs) : (as.map (Expr.mapKeys f) == bs.map (Expr.mapKeys f)) = (as == bs) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨Expr.mapKeys_list_inj hf ha hb, fun h => h ▸ rfl⟩

theorem getD_mapKeys_default (l : List (Expr md)) (i : Nat) :
    (l.map (Expr.mapKeys f)).getD i default = (l.getD i default).mapKeys f := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem Expr.GoodList.getD_default {l : List (Expr md)} (h : Expr.GoodList P l) (i : Nat) :
    (l.getD i default).Good P := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => trivial
  | some e => exact h e (List.mem_of_getElem? hl)

theorem Expr.goodList_map {α : Type} {l : List α} {g : α → Expr md} (h : ∀ x ∈ l, (g x).Good P) :
    Expr.GoodList P (l.map g) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact h x hx

/-! ## `mentionsAny` -/

theorem mentionsAnyP_mapKeys (hf : InjOn f P) {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P) :
    ∀ {e : Expr md}, e.Good P → mentionsAnyP (ns.map (Key.map f)) (e.mapKeys f) = mentionsAnyP ns e := by
  intro e he
  induction e with
  | const n us => simp only [Expr.mapKeys, mentionsAnyP]; exact contains_map_ren hf hns he
  | proj s i x ih =>
    simp only [Expr.Good] at he
    simp only [Expr.mapKeys, mentionsAnyP, contains_map_ren hf hns he.1, ih he.2]
  | lit l => cases l <;> rfl
  | _ => simp_all [Expr.mapKeys, mentionsAnyP]

theorem mentionsAny_mapKeys (hf : InjOn f P) {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P)
    {e : Expr md} (he : e.Good P) :
    mentionsAny (ns.map (Key.map f)) (e.mapKeys f) = mentionsAny ns e := by
  rw [mentionsAny_eq, mentionsAny_eq, mentionsAnyP_mapKeys hf hns he]

/-! ## Heights -/

theorem maxHeightP_mapKeys {h : Key md → Nat} {h' : Key md' → Nat}
    (hh : ∀ k : Key md, k.Good P → h' (k.map f) = h k) :
    ∀ {e : Expr md}, e.Good P → maxHeightP h' (e.mapKeys f) = maxHeightP h e := by
  intro e he
  induction e with
  | const n us => exact hh n he
  | lit l => cases l <;> rfl
  | _ => simp_all [Expr.mapKeys, maxHeightP]

theorem maxHeight_mapKeys {h : Key md → Nat} {h' : Key md' → Nat}
    (hh : ∀ k : Key md, k.Good P → h' (k.map f) = h k) {e : Expr md} (he : e.Good P) :
    maxHeight h' (e.mapKeys f) = maxHeight h e := by
  rw [maxHeight_eq, maxHeight_eq, maxHeightP_mapKeys hh he]

theorem hintFor_mapKeys {h : Key md → Nat} {h' : Key md' → Nat}
    (hh : ∀ k : Key md, k.Good P → h' (k.map f) = h k) {e : Expr md} (he : e.Good P) :
    hintFor h' (e.mapKeys f) = hintFor h e := by
  simp only [hintFor, maxHeight_mapKeys hh he]

/-! ## `substParams` -/

theorem substParamsP_mapKeys (d n : Nat) (vals : List (Expr md)) :
    ∀ (k : Nat) (e : Expr md),
      substParamsP d n (vals.map (Expr.mapKeys f)) k (e.mapKeys f) =
        (substParamsP d n vals k e).mapKeys f := by
  intro k e
  induction e generalizing k with
  | bvar i =>
    simp only [Expr.mapKeys, substParamsP]
    split
    · rfl
    · split
      · rw [getD_mapKeys_default, Expr.mapKeys_liftLooseBVars]
      · rfl
  | _ => simp_all [Expr.mapKeys, substParamsP]

theorem substParamsP_good {d n : Nat} {vals : List (Expr md)} (hv : Expr.GoodList P vals) :
    ∀ (k : Nat) {e : Expr md}, e.Good P → (substParamsP d n vals k e).Good P := by
  intro k e he
  induction e generalizing k with
  | bvar i =>
    simp only [substParamsP]
    split
    · trivial
    · split
      · exact Expr.Good.liftLooseBVars (Expr.GoodList.getD_default hv _) _ _
      · trivial
  | lit l => cases l <;> simp_all [substParamsP]
  | _ => simp_all [substParamsP]

theorem substParams_mapKeys (d n : Nat) (vals : List (Expr md)) (e : Expr md) :
    substParams d n (vals.map (Expr.mapKeys f)) (e.mapKeys f) = (substParams d n vals e).mapKeys f := by
  rw [substParams_eq, substParams_eq, substParamsP_mapKeys]

theorem substParams_good {d n : Nat} {vals : List (Expr md)} (hv : Expr.GoodList P vals)
    {e : Expr md} (he : e.Good P) : (substParams d n vals e).Good P := by
  rw [substParams_eq]; exact substParamsP_good hv 0 he

/-! ## Small builders: goodness -/

theorem Expr.good_mkPis {bs : List (Expr md)} {body : Expr md} (hbs : Expr.GoodList P bs)
    (hb : body.Good P) : (mkPis bs body).Good P := by
  induction bs with
  | nil => exact hb
  | cons a as ih =>
    simp only [Expr.goodList_cons] at hbs
    exact ⟨hbs.1, ih hbs.2⟩

theorem Expr.good_mkLams {bs : List (Expr md)} {body : Expr md} (hbs : Expr.GoodList P bs)
    (hb : body.Good P) : (mkLams bs body).Good P := by
  induction bs with
  | nil => exact hb
  | cons a as ih =>
    simp only [Expr.goodList_cons] at hbs
    exact ⟨hbs.1, ih hbs.2⟩

@[simp] theorem Expr.good_constP {n : Key md} {lps : List LevelParam} :
    (constP n lps).Good P ↔ n.Good P := Iff.rfl

theorem Expr.goodList_varsAt (o n : Nat) : Expr.GoodList P (varsAt o n : List (Expr md)) := by
  intro e he
  simp only [varsAt, structPsAt, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  trivial

theorem Expr.goodList_structProjPs (nP : Nat) :
    Expr.GoodList P (structProjPs nP : List (Expr md)) := by
  intro e he
  simp only [structProjPs, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  trivial

theorem Expr.goodList_piBinders {bs : List (Expr md × BinderMeta)} (h : ∀ b ∈ bs, b.1.Good P) :
    Expr.GoodList P (piBinders bs) := by
  intro e he
  simp only [piBinders, List.mem_map] at he
  obtain ⟨b, hb, rfl⟩ := he
  exact h b hb

/-! ## `specFam` -/

section SpecFam

variable (T : Key md) (lps : List LevelParam) (nP : Nat) (members : List (Key md × Nat × Nat))

theorem specFamP_mapKeys (hf : InjOn f P) (hm : ∀ x ∈ members, x.1.Good P) :
    ∀ e : Expr md, e.Good P →
      specFamP (T.map f) lps nP (keyMap f members) (e.mapKeys f) =
        (specFamP T lps nP members e).mapKeys f
  | .bvar i, _ => by rw [Expr.mapKeys, specFamP, specFamP]; rfl
  | .sort u, _ => by rw [Expr.mapKeys, specFamP, specFamP]; rfl
  | .fvar i t, _ => by rw [Expr.mapKeys, specFamP, specFamP]; rfl
  | .lit l, _ => by rw [Expr.mapKeys, specFamP, specFamP]; rfl
  | .const n us, hn => by
    rw [Expr.mapKeys, specFamP, specFamP, find?_keyMap hf hm hn]
    cases members.find? (·.1 == n) with
    | none => rfl
    | some x =>
      obtain ⟨x, m, nIdx⟩ := x
      simp only [Option.map_some]
      split <;> rfl
  | .app g x, he => by
    have hargs : Expr.GoodList P (Expr.app g x).getAppArgs := Expr.Good.getAppArgs he
    have IH : ∀ y ∈ (Expr.app g x).getAppArgs,
        specFamP (T.map f) lps nP (keyMap f members) (y.mapKeys f) =
          (specFamP T lps nP members y).mapKeys f := fun y hy =>
      have : sizeOf y < sizeOf (Expr.app g x) := sizeOf_lt_of_mem_getAppArgs hy
      specFamP_mapKeys hf hm y (hargs y hy)
    have IHf : specFamP (T.map f) lps nP (keyMap f members) ((Expr.app g x).getAppFn.mapKeys f) =
        (specFamP T lps nP members (Expr.app g x).getAppFn).mapKeys f :=
      have : sizeOf (Expr.app g x).getAppFn < sizeOf (Expr.app g x) := sizeOf_getAppFn_app g x
      specFamP_mapKeys hf hm _ (Expr.Good.getAppFn he)
    have hF : (Expr.app (g.mapKeys f) (x.mapKeys f)).getAppFn = (Expr.app g x).getAppFn.mapKeys f :=
      (Expr.mapKeys_getAppFn (Expr.app g x)).symm
    have hA : (Expr.app (g.mapKeys f) (x.mapKeys f)).getAppArgs =
        (Expr.app g x).getAppArgs.map (Expr.mapKeys f) := Expr.getAppArgs_mapKeys (Expr.app g x)
    have hFg : (Expr.app g x).getAppFn.Good P := Expr.Good.getAppFn he
    rw [Expr.mapKeys]
    conv => lhs; rw [specFamP]
    conv => rhs; rw [specFamP]
    simp only [mapMemo_unit_map]
    rw [hF, hA]
    generalize (Expr.app g x).getAppArgs = A at IH hargs ⊢
    have hmapA : ∀ B : List (Expr md), (∀ y ∈ B, y ∈ A) →
        (B.map (Expr.mapKeys f)).map (specFamP (T.map f) lps nP (keyMap f members)) =
          (B.map (specFamP T lps nP members)).map (Expr.mapKeys f) := by
      intro B hB
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun y hy => IH y (hB y hy)
    generalize (Expr.app g x).getAppFn = F at IHf hFg ⊢
    cases F with
    | const n us =>
      simp only [Expr.mapKeys]
      rw [find?_keyMap hf hm hFg]
      cases members.find? (·.1 == n) with
      | none =>
        simp only [Option.map_none, Expr.mapKeys_mkAppN, hmapA A (fun _ h => h)]; rfl
      | some y =>
        obtain ⟨y, m, nIdx⟩ := y
        simp only [Option.map_some, List.length_map]
        split
        · simp only [Expr.mapKeys_mkAppN, List.map_append, List.map_cons, List.map_nil,
            ← List.map_take, ← List.map_drop, hmapA _ (fun _ h => List.mem_of_mem_take h),
            hmapA _ (fun _ h => List.mem_of_mem_drop h)]
          rfl
        · simp only [Expr.mapKeys_mkAppN, hmapA A (fun _ h => h)]
          simp only [Expr.mapKeys] at IHf
          rw [IHf]
    | _ =>
      simp only [Expr.mapKeys] at IHf ⊢
      simp only [Expr.mapKeys_mkAppN, hmapA A (fun _ h => h), IHf]
  | .lam d b m, he => by
    simp only [Expr.Good] at he
    rw [Expr.mapKeys, specFamP, specFamP, specFamP_mapKeys hf hm d he.1,
      specFamP_mapKeys hf hm b he.2]
    rfl
  | .forallE d b m, he => by
    simp only [Expr.Good] at he
    rw [Expr.mapKeys, specFamP, specFamP, specFamP_mapKeys hf hm d he.1,
      specFamP_mapKeys hf hm b he.2]
    rfl
  | .letE t v b l, he => by
    simp only [Expr.Good] at he
    rw [Expr.mapKeys, specFamP, specFamP, specFamP_mapKeys hf hm t he.1,
      specFamP_mapKeys hf hm v he.2.1, specFamP_mapKeys hf hm b he.2.2]
    rfl
  | .proj s i x, he => by
    simp only [Expr.Good] at he
    rw [Expr.mapKeys, specFamP, specFamP, specFamP_mapKeys hf hm x he.2]
    rfl
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | assumption
    | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec, Expr.letE.sizeOf_spec,
        Expr.proj.sizeOf_spec]; omega)
    | omega

theorem specFamP_good (hT : T.Good P) : ∀ e : Expr md, e.Good P → (specFamP T lps nP members e).Good P
  | .bvar i, h => by rw [specFamP]; exact h
  | .sort u, h => by rw [specFamP]; exact h
  | .fvar i t, h => by rw [specFamP]; exact h
  | .lit l, h => by rw [specFamP]; exact h
  | .const n us, hn => by
    rw [specFamP]
    cases members.find? (·.1 == n) with
    | none => exact hn
    | some x =>
      obtain ⟨x, m, nIdx⟩ := x
      dsimp only
      split
      · exact Expr.Good.mkAppN hT (Expr.goodList_cons.mpr ⟨hT, Expr.goodList_nil⟩)
      · exact hn
  | .app g x, he => by
    have hargs : Expr.GoodList P (Expr.app g x).getAppArgs := Expr.Good.getAppArgs he
    have IH : ∀ y ∈ (Expr.app g x).getAppArgs, (specFamP T lps nP members y).Good P := fun y hy =>
      have : sizeOf y < sizeOf (Expr.app g x) := sizeOf_lt_of_mem_getAppArgs hy
      specFamP_good hT y (hargs y hy)
    have IHf : (specFamP T lps nP members (Expr.app g x).getAppFn).Good P :=
      have : sizeOf (Expr.app g x).getAppFn < sizeOf (Expr.app g x) := sizeOf_getAppFn_app g x
      specFamP_good hT _ (Expr.Good.getAppFn he)
    have hFg : (Expr.app g x).getAppFn.Good P := Expr.Good.getAppFn he
    rw [specFamP]
    simp only [mapMemo_unit_map]
    generalize (Expr.app g x).getAppArgs = A at IH hargs ⊢
    have hmapA : ∀ B : List (Expr md), (∀ y ∈ B, y ∈ A) →
        Expr.GoodList P (B.map (specFamP T lps nP members)) :=
      fun B hB => Expr.goodList_map fun y hy => IH y (hB y hy)
    generalize (Expr.app g x).getAppFn = F at IHf hFg ⊢
    cases F with
    | const n us =>
      dsimp only
      cases members.find? (·.1 == n) with
      | none => exact Expr.Good.mkAppN hFg (hmapA A fun _ h => h)
      | some y =>
        obtain ⟨y, m, nIdx⟩ := y
        dsimp only
        split
        · refine Expr.Good.mkAppN hT ?_
          simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil, and_true]
          have h1 := hmapA (A.take nP) (fun _ h => List.mem_of_mem_take h)
          refine ⟨h1, Expr.Good.mkAppN hT ?_⟩
          simp only [Expr.goodList_append]
          exact ⟨h1, hmapA (A.drop nP) (fun _ h => List.mem_of_mem_drop h)⟩
        · exact Expr.Good.mkAppN IHf (hmapA A fun _ h => h)
    | _ => exact Expr.Good.mkAppN IHf (hmapA A fun _ h => h)
  | .lam d b m, he => by
    simp only [Expr.Good] at he
    rw [specFamP]
    exact ⟨specFamP_good hT d he.1, specFamP_good hT b he.2⟩
  | .forallE d b m, he => by
    simp only [Expr.Good] at he
    rw [specFamP]
    exact ⟨specFamP_good hT d he.1, specFamP_good hT b he.2⟩
  | .letE t v b l, he => by
    simp only [Expr.Good] at he
    rw [specFamP]
    exact ⟨specFamP_good hT t he.1, specFamP_good hT v he.2.1, specFamP_good hT b he.2.2⟩
  | .proj s i x, he => by
    simp only [Expr.Good] at he
    rw [specFamP]
    exact ⟨he.1, specFamP_good hT x he.2⟩
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | assumption
    | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec, Expr.letE.sizeOf_spec,
        Expr.proj.sizeOf_spec]; omega)
    | omega

theorem specFam_mapKeys (hf : InjOn f P) (hm : ∀ x ∈ members, x.1.Good P) {e : Expr md}
    (he : e.Good P) :
    specFam (T.map f) lps nP (keyMap f members) (e.mapKeys f) = (specFam T lps nP members e).mapKeys f := by
  rw [specFam_eq, specFam_eq, specFamP_mapKeys T lps nP members hf hm e he]

theorem specFam_good (hT : T.Good P) {e : Expr md} (he : e.Good P) :
    (specFam T lps nP members e).Good P := by
  rw [specFam_eq]; exact specFamP_good T lps nP members hT e he

end SpecFam

end Ix.Kernel.Frontend.InModel
