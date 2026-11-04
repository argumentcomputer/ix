module

public import IxC.Kernel.Verify.Frontend.InModelProjRec

@[expose] public section

/-!
# The mutual rung under a renaming injective on a scope (parametricity, step 3)

`genMutual_mapKeys`: the mutual rung run on the renamed block, at a context
agreeing with the original's on the scope (`CtxAgree`), fails exactly when the
original run fails, and otherwise returns the original's records renamed
(`ExRel`, up to the error messages, which name keys).

The proof walks the rung's elaborated `do` block in order: the member checks,
the constructor classification (`classifyCtor_mapKeys`), the recursor shape
checks, the tag universe (`idxSort_mapKeysOn`), the tag and auxiliary blocks
(`recTy_map`, `recRhs_map`), the member, constructor and recursor models (the
block renaming `rn` through `rn_map`, the heights through `hint_eq`), the iota
theorems, and the projection artifacts (the rung's local constant table through
`tblOn_local`, `projRecValue_mapKeys`). Every comparison of keys or terms is
between good ones, so `InjOn` gives it the same answer on both sides.

Two techniques recur. The generator's `if b = true` conditions carry
`Decidable` instances that mention the condition, so the proof turns them into
`cond` first (`Bool.cond_eq_ite`) and compares conditions syntactically
(`ExRel.cond`). A `match` of the generator cannot be restated in a lemma (a new
matcher is a different constant), so a discriminant is generalized in place and
its renamed counterpart rewritten through an equation transported from it.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode} {P : KeyScope md} {f : md.Id → md'.Id}

theorem except_throw_bind {ε α β : Type} (e : ε) (g : α → Except ε β) :
    (throw e : Except ε α) >>= g = throw e := rfl

theorem ExRel.cond {ε ε' α β : Type} {R : α → β → Prop} {c c' : Bool} (hc : c = c')
    {x y : Except ε α} {x' y' : Except ε' β} (ht : c = true → ExRel R x x')
    (he : c = false → ExRel R y y') : ExRel R (cond c x y) (cond c' x' y') := by
  subst hc; cases c
  · exact he rfl
  · exact ht rfl

theorem ListRel.of_map {α β : Type} {g : α → β} {G : α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, G x) → ListRel (fun x x' => x' = g x ∧ G x) l (l.map g)
  | [], _ => .nil
  | a :: _, h => .cons ⟨rfl, h a List.mem_cons_self⟩
      (ListRel.of_map fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem ListRel.refl_mem {α : Type} : ∀ {l : List α}, ListRel (fun x x' => x' = x ∧ x ∈ l) l l := by
  intro l
  suffices H : ∀ l₀ : List α, (∀ x ∈ l₀, x ∈ l) → ListRel (fun x x' => x' = x ∧ x ∈ l) l₀ l₀ from
    H l fun _ h => h
  intro l₀ h
  induction l₀ with
  | nil => exact .nil
  | cons a as ih => exact .cons ⟨rfl, h a List.mem_cons_self⟩ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem getD_map_of_lt {α β : Type} {l : List α} {g : α → β} {i : Nat} (h : i < l.length) (d : α)
    (d' : β) : (l.map g).getD i d' = g (l.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some]

theorem getD_mem_of_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem find?_map_congr {α β : Type} {l : List α} {g : α → β} {p : α → Bool} {p' : β → Bool}
    (h : ∀ x ∈ l, p' (g x) = p x) : (l.map g).find? p' = (l.find? p).map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.find?_cons, h a List.mem_cons_self]
    cases p a
    · exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    · rfl

theorem members_map (types : List (IndTypeRec md)) :
    (types.map (IndTypeRec.mapKeys f)).zipIdx.map (fun x => (x.1.cv.name, x.2, x.1.nIdx)) =
      keyMap f (types.zipIdx.map fun x => (x.1.cv.name, x.2, x.1.nIdx)) := by
  simp [List.zipIdx_map, keyMap, List.map_map, Function.comp_def]

theorem minors_map (n : Nat) (rbs : List (Expr md × BinderMeta)) :
    (List.drop n (Expr.mapBinders f rbs)).map (fun x => x.1) =
      ((List.drop n rbs).map fun x => x.1).map (Expr.mapKeys f) := by
  simp [Expr.mapBinders, ← List.map_drop, List.map_map, Function.comp_def]

theorem classifyCtor_minors (hf : InjOn f P) (T : Key md) (hT : T.Good P)
    {members : List (Key md × Nat × Nat)} (hm : ∀ x ∈ members, x.1.Good P) (lps : List LevelParam)
    (nP k J : Nat) {minors : List (Expr md)} (hmin : Expr.GoodList P minors) (m j : Nat)
    {c : IndCtorRec md} (hc : c.Good P) :
    ExRel (fun mc mc' => mc' = mc.mapKeys f ∧ mc.Good P)
      (classifyCtor T members lps nP k J minors[J]? m j c)
      (classifyCtor (T.map f) (keyMap f members) lps nP k J (minors.map (Expr.mapKeys f))[J]? m j
        (c.mapKeys f)) := by
  rw [List.getElem?_map]
  exact classifyCtor_mapKeys hf T hT hm lps nP k J (fun e he => hmin e (List.mem_of_getElem? he)) m j hc

theorem own_map (ms : List (MCtor md)) (m : Nat) :
    (ms.map (MCtor.mapKeys f)).filter (fun x => x.m == m) =
      (ms.filter fun x => x.m == m).map (MCtor.mapKeys f) := by
  rw [List.filter_map]
  rfl

theorem rulesOk_map (hf : InjOn f P) (rules : List (RecRule md)) (own : List (MCtor md))
    (hr : ∀ x ∈ rules, x.Good P) (ho : ∀ mc ∈ own, mc.Good P) :
    ((rules.map (RecRule.mapKeys f)).length == (own.map (MCtor.mapKeys f)).length &&
      (List.range (own.map (MCtor.mapKeys f)).length).all fun j =>
        ((rules.map (RecRule.mapKeys f)).getD j default).ctor ==
          ((own.map (MCtor.mapKeys f)).getD j default).c.cv.name) =
    (rules.length == own.length &&
      (List.range own.length).all fun j => (rules.getD j default).ctor == (own.getD j default).c.cv.name) := by
  simp only [List.length_map]
  cases hl : rules.length == own.length with
  | false => rfl
  | true =>
    have hl' : rules.length = own.length := by simpa using hl
    simp only [Bool.true_and]
    refine all_congr_mem fun j hj => ?_
    have hj' : j < own.length := List.mem_range.mp hj
    rw [getD_map_of_lt (hl' ▸ hj') default default, getD_map_of_lt hj' default default]
    simp only [MCtor.mapKeys_c, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
    exact Key.map_beq hf (hr _ (getD_mem_of_lt (hl' ▸ hj') default)).1
      (ho _ (getD_mem_of_lt hj' default)).1.1

theorem ExRel.refl {ε ε' α : Type} {x : Except ε α} {x' : Except ε' α}
    (h : x.toOption = x'.toOption) : ExRel Eq x x' := by
  cases x <;> cases x' <;> simp_all [Except.toOption, ExRel]

theorem ExRel.need {α β : Type} {G : α → Prop} {g : α → β} {o : Option α} (s s' : String)
    (hG : ∀ a, o = some a → G a) :
    ExRel (fun a b => b = g a ∧ G a) (need s o) (need s' (o.map g)) := by
  cases o with
  | none => exact ExRel.throw'
  | some a => exact ExRel.pure' ⟨rfl, hG a rfl⟩

theorem idxSort_mapKeysOn' (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) {ctx₂ : List (Expr md')} {e₂ : Expr md'} (h1 : ctx₂ = ctx.map (Expr.mapKeys f))
    (h2 : e₂ = e.mapKeys f) : idxSort tbl' ctx₂ e₂ = idxSort tbl ctx e := by
  subst h1 h2; exact idxSort_mapKeysOn hP htbl hctx he

theorem replacePiBody_sort_mapKeys (k : Nat) (e : Expr md) (u : Level) :
    Expr.replacePiBody k (e.mapKeys f) (.sort u) = (Expr.replacePiBody k e (.sort u)).map (Expr.mapKeys f) :=
  Expr.replacePiBody_mapKeys k e (.sort u)

theorem tagCtorTy_map (nP n nIdx : Nat) (former ty : Expr md) (T : Key md) (lps : List LevelParam) :
    ((overFirstParams nP (former.mapKeys f) (ty.mapKeys f)).bind fun ty' =>
        Expr.replacePiBody n ty' ((constP (tagName (T.map f)) lps).mkAppN (varsAt nIdx nP))) =
      ((overFirstParams nP former ty).bind fun ty' =>
        Expr.replacePiBody n ty' ((constP (tagName T) lps).mkAppN (varsAt nIdx nP))).map
          (Expr.mapKeys f) := by
  rw [overFirstParams_mapKeys]
  cases overFirstParams nP former ty with
  | none => rfl
  | some ty' =>
    have h : (constP (tagName (T.map f)) lps).mkAppN (varsAt nIdx nP : List (Expr md')) =
        ((constP (tagName T) lps).mkAppN (varsAt nIdx nP)).mapKeys f := by
      simp [Expr.mapKeys_mkAppN]
    simp only [Option.map_some, Option.bind_some, h, Expr.replacePiBody_mapKeys]

/-- The renaming of a generated constructor list (`ctors4Map`, spelled as the proof's relation). -/
abbrev c4m (f : md.Id → md'.Id) (cs : List (Key md × Nat × Expr md × List Nat)) :
    List (Key md' × Nat × Expr md' × List Nat) :=
  cs.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)

theorem recTy_tag_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat)) :
    recTy (tagName (T.map f)) lps elim large nP nIdx (tty.mapKeys f) (c4m f ctors) =
      (recTy (tagName T) lps elim large nP nIdx tty ctors).map (Expr.mapKeys f) :=
  recTy_map (tagName T) lps elim large nP nIdx tty ctors

theorem recTy_aux_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat)) :
    recTy (auxName (T.map f)) lps elim large nP nIdx (tty.mapKeys f) (c4m f ctors) =
      (recTy (auxName T) lps elim large nP nIdx tty ctors).map (Expr.mapKeys f) :=
  recTy_map (auxName T) lps elim large nP nIdx tty ctors

theorem recRhs_tag_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat))
    (rlvls : List Level) (j : Nat) :
    recRhs (tagName (T.map f)) lps elim large nP nIdx (tty.mapKeys f) (c4m f ctors)
        (auxKey (tagName (T.map f)) .recursor) rlvls j =
      (recRhs (tagName T) lps elim large nP nIdx tty ctors (auxKey (tagName T) .recursor) rlvls j).map
        (Expr.mapKeys f) :=
  recRhs_map (tagName T) lps elim large nP nIdx tty ctors (auxKey (tagName T) .recursor) rlvls j

theorem recRhs_aux_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat))
    (rlvls : List Level) (j : Nat) :
    recRhs (auxName (T.map f)) lps elim large nP nIdx (tty.mapKeys f) (c4m f ctors)
        (auxKey (auxName (T.map f)) .recursor) rlvls j =
      (recRhs (auxName T) lps elim large nP nIdx tty ctors (auxKey (auxName T) .recursor) rlvls j).map
        (Expr.mapKeys f) :=
  recRhs_map (auxName T) lps elim large nP nIdx tty ctors (auxKey (auxName T) .recursor) rlvls j

theorem auxTyBody_map (T : Key md) (lps : List LevelParam) (nP : Nat) (u : Level) :
    ((constP (tagName (T.map f)) lps).mkAppN (varsAt 0 nP : List (Expr md'))).forallE (.sort u) bm =
      (((constP (tagName T) lps).mkAppN (varsAt 0 nP)).forallE (.sort u) bm).mapKeys f := by
  simp [Expr.mapKeys_mkAppN]

theorem c4m_getD {cs : List (Key md × Nat × Expr md × List Nat)} {j : Nat} (h : j < cs.length) :
    (c4m f cs).getD j default = ((cs.getD j default).1.map f, (cs.getD j default).2.1,
      (cs.getD j default).2.2.1.mapKeys f, (cs.getD j default).2.2.2) :=
  getD_map_of_lt h default default

/-- **`mapM` over related lists**, with the length of the result. -/
theorem ExRel.mapM_len {ε ε' α β γ δ : Type} {R : α → β → Prop} {Q : γ → δ → Prop}
    {f : γ → Except ε α} {f' : δ → Except ε' β} :
    ∀ {l : List γ} {l' : List δ}, ListRel Q l l' →
      (∀ x x', Q x x' → ExRel R (f x) (f' x')) →
      ExRel (fun r r' => ListRel R r r' ∧ r.length = l.length) (l.mapM f) (l'.mapM f')
  | [], [], .nil, _ => ⟨ListRel.nil, rfl⟩
  | x :: xs, x' :: xs', .cons hq hl, hf => by
    rw [List.mapM_cons, List.mapM_cons]
    refine ExRel.bind (hf x x' hq) fun a b hab => ?_
    refine ExRel.bind (ExRel.mapM_len hl hf) fun as bs habs => ?_
    exact ⟨ListRel.cons hab habs.1, by simp [habs.2]⟩

theorem ExRel.need_pis {G : Expr md → Prop} (s s' : String) (k : Nat) {ty body : Expr md}
    {body' : Expr md'} (hb : body' = body.mapKeys f) (hG : ∀ a, Expr.pisToLams k ty body = some a → G a) :
    ExRel (fun a b => b = a.mapKeys f ∧ G a) (InModel.need s (Expr.pisToLams k ty body))
      (InModel.need s' (Expr.pisToLams k (ty.mapKeys f) body')) := by
  subst hb; rw [Expr.pisToLams_mapKeys]; exact ExRel.need s s' hG

@[simp] theorem Expr.good_mkAppN_iff {g : Expr md} {as : List (Expr md)} :
    (Expr.mkAppN g as).Good P ↔ g.Good P ∧ Expr.GoodList P as := by
  induction as generalizing g with
  | nil => simp [Expr.mkAppN]
  | cons a as ih => simp [Expr.mkAppN, ih, and_assoc]

@[simp] theorem Expr.goodList_varsAt' (o n : Nat) : Expr.GoodList P (varsAt o n : List (Expr md)) :=
  Expr.goodList_varsAt o n

theorem rn_map (hf : InjOn f P) {bn : List (Key md)} (hbn : ∀ k ∈ bn, k.Good P) {e : Expr md}
    (he : e.Good P) :
    (e.mapKeys f).renameConsts (fun x => if (bn.map (Key.map f)).contains x = true then modelName x else x) =
      (e.renameConsts (fun x => bif bn.contains x then modelName x else x)).mapKeys f := by
  refine (mapKeys_renameConsts_good (fun k hk => ?_) he).symm
  simp only [contains_map_ren hf hbn hk]
  cases bn.contains k <;> rfl

theorem rn_good {bn : List (Key md)} {e : Expr md} (he : e.Good P) :
    (e.renameConsts (fun x => bif bn.contains x then modelName x else x)).Good P := by
  refine Expr.Good.renameConsts (fun k hk => ?_) he
  cases bn.contains k <;> exact hk

theorem hint_eq (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'} (hctx : CtxAgree f P ctx ctx')
    {hs : List (Key md × Nat)} (hsG : ∀ x ∈ hs, x.1.Good P) {v : Expr md} (hv : v.Good P) :
    hintFor (fun x => match List.find? (fun y => y.1 == x) (keyMap f hs) with
        | some (_, h) => h
        | none => ctx'.heights x) (v.mapKeys f) =
      hintFor (fun x => match List.find? (fun y => y.1 == x) hs with
        | some (_, h) => h
        | none => ctx.heights x) v := by
  refine hintFor_mapKeys (fun k hk => ?_) hv
  rw [find?_keyMap hf hsG hk]
  cases List.find? (fun y => y.1 == k) hs with
  | none => exact hctx.heights k hk
  | some y => rfl

@[simp] theorem good_implKey {T : Key md} : (implKey T).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_tagName {T : Key md} : (tagName T).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_tagCtorName {T : Key md} {k : Nat} : (tagCtorName T k).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_auxName {T : Key md} : (auxName T).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_auxCtorName {T : Key md} {k j : Nat} : (auxCtorName T k j).Good P ↔ T.Good P :=
  Iff.rfl
@[simp] theorem good_modelName {T : Key md} : (modelName T).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_iotaName {T : Key md} {j : Nat} : (iotaName T j).Good P ↔ T.Good P := Iff.rfl
@[simp] theorem good_projModelName {T : Key md} {i : Nat} : (projModelName T i).Good P ↔ T.Good P :=
  Iff.rfl
@[simp] theorem good_auxKey {T : Key md} {d : Derived} : (auxKey T d).Good P ↔ T.Good P := Iff.rfl

theorem findIdx?_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.findIdx? p = l.findIdx? q
  | [], _ => rfl
  | a :: as, h => by
    rw [List.findIdx?_cons, List.findIdx?_cons, h a List.mem_cons_self,
      findIdx?_congr_mem (l := as) fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem findIdx?_name_map (hf : InjOn f P) {ms : List (MCtor md)} (hms : ∀ mc ∈ ms, mc.Good P)
    {mc : MCtor md} (hmc : mc.Good P) :
    (ms.map (MCtor.mapKeys f)).findIdx? (fun x => x.c.cv.name == (mc.mapKeys f).c.cv.name) =
      ms.findIdx? (fun x => x.c.cv.name == mc.c.cv.name) := by
  rw [List.findIdx?_map]
  refine findIdx?_congr_mem fun x hx => ?_
  simp only [Function.comp_apply, MCtor.mapKeys_c, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
  exact Key.map_beq hf (hms x hx).1.1 hmc.1.1

theorem ExRel.need_pis' {G : Expr md → Prop} (s s' : String) (k : Nat) {ty body : Expr md}
    {ty' body' : Expr md'} (ht : ty' = ty.mapKeys f) (hb : body' = body.mapKeys f)
    (hG : ∀ a, Expr.pisToLams k ty body = some a → G a) :
    ExRel (fun a b => b = a.mapKeys f ∧ G a) (InModel.need s (Expr.pisToLams k ty body))
      (InModel.need s' (Expr.pisToLams k ty' body')) := by
  subst ht; exact ExRel.need_pis s s' k hb hG

theorem fst_getD_mapBinders (bs : List (Expr md × BinderMeta)) (i : Nat) :
    (List.map (fun (x : Expr md' × BinderMeta) => x.1) (Expr.mapBinders f bs)).getD i default =
      ((List.map (fun (x : Expr md × BinderMeta) => x.1) bs).getD i default).mapKeys f := by
  rw [← getD_mapKeys_default]
  simp [Expr.mapBinders, List.map_map, Function.comp_def]

@[simp] theorem varsAt_map_mapKeys {β : Type} (g : Expr md' → β) (o n : Nat) :
    (varsAt o n : List (Expr md)).map (fun x => g (x.mapKeys f)) = (varsAt o n : List (Expr md')).map g := by
  rw [← varsAt_mapKeys (f := f) o n, List.map_map]; rfl

@[simp] theorem iotaName_map (R : Key md) (j : Nat) : (iotaName R j).map f = iotaName (R.map f) j := rfl

theorem sortOf_mapKeysOn' (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) {ctx₂ : List (Expr md')} {e₂ : Expr md'} (h1 : ctx₂ = ctx.map (Expr.mapKeys f))
    (h2 : e₂ = e.mapKeys f) : sortOf tbl' ctx₂ e₂ = sortOf tbl ctx e := by
  subst h1 h2; exact sortOf_mapKeysOn hP htbl hctx he

theorem tblOn_local (hf : InjOn f P) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {gt : List (Key md × List LevelParam × Expr md)}
    {gt' : List (Key md' × List LevelParam × Expr md')}
    (hgt : gt' = gt.map fun x => (x.1.map f, x.2.1, x.2.2.mapKeys f))
    (hG : ∀ x ∈ gt, x.1.Good P ∧ x.2.2.Good P) :
    TblOn P f (fun x => match gt.find? (fun y => y.1 == x) with
        | some (_, l, ty) => some (l, ty)
        | none => tbl x)
      (fun x => match gt'.find? (fun y => y.1 == x) with
        | some (_, l, ty) => some (l, ty)
        | none => tbl' x) := by
  subst hgt
  refine ⟨fun k hk => ?_, fun k hk p hp => ?_⟩
  · rw [find?_map_congr (p := fun y => y.1 == k) fun y hy => Key.map_beq hf (hG y hy).1 hk]
    cases List.find? (fun y => y.1 == k) gt with
    | none => exact htbl.agree k hk
    | some y => rfl
  · revert hp
    cases hfd : List.find? (fun y => y.1 == k) gt with
    | none => exact htbl.good k hk p
    | some y => intro hp; cases hp; exact (hG y (List.mem_of_find?_eq_some hfd)).2

theorem append_congr' {α : Type} {l1 l1' l2 l2' : List α} (h1 : l1 = l1') (h2 : l2 = l2') :
    l1 ++ l2 = l1' ++ l2' := by rw [h1, h2]

theorem cons_congr' {α : Type} {a b : α} {l l' : List α} (h1 : a = b) (h2 : l = l') :
    a :: l = b :: l' := by rw [h1, h2]

/-- **The mutual rung commutes with renaming keys**: on a good block, at a context agreeing on
the scope, the renamed run fails exactly when the original does, and otherwise returns its
records renamed. -/
theorem genMutual_mapKeys (hP : P.Pre) (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {b : BlockRec md} (hb : b.Good P) :
    ExRel (fun ds ds' => ds' = ds.map (Declaration.mapKeys f))
      (genMutual ctx b) (genMutual ctx' (b.mapKeys f)) := by
  obtain ⟨types, ctors, recs⟩ := b
  obtain ⟨hty, hct, hrc⟩ := hb
  unfold genMutual
  simp only [← Bool.cond_eq_ite, except_throw_bind, BlockRec.mapKeys_types, BlockRec.mapKeys_ctors,
    BlockRec.mapKeys_recs, List.length_map]
  cases types with
  | nil => exact ExRel.throw'
  | cons t0 rest =>
  have ht0 := hty t0 List.mem_cons_self
  simp only [List.map_cons, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type, IndTypeRec.mapKeys_nP,
    IndTypeRec.mapKeys_nIdx, List.length_cons]
  refine ExRel.ite Iff.rfl (fun hk => ?_) (fun _ => ExRel.throw')
  have hl : ListRel (fun x x' => x' = IndTypeRec.mapKeys f x ∧ x.Good P) (t0 :: rest)
      (t0.mapKeys f :: rest.map (IndTypeRec.mapKeys f)) := ListRel.of_map (l := t0 :: rest) hty
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_list hl trivial fun t t' _ _ ht _ => ?_)
    fun _ _ _ => ?_
  · obtain ⟨rfl, htg⟩ := ht
    simp only [IndTypeRec.mapKeys_numNested, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_levelParams,
      IndTypeRec.mapKeys_nP]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
    exact ExRel.cond rfl (fun _ => ExRel.pure' trivial) (fun _ => ExRel.throw')
  simp only [Expr.stripPis_mapKeys]
  cases hs : Expr.stripPis (t0.nP + t0.nIdx) t0.cv.type with
  | none => exact ExRel.throw'
  | some q =>
  obtain ⟨pbs, body⟩ := q
  have hpbs := Expr.stripPis_good ht0.1.2 hs
  cases body with
  | sort u => ?_
  | _ => exact ExRel.throw'
  simp only [Option.map_some, Expr.mapTele, Expr.mapKeys]
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_list hl trivial fun t t' _ _ ht _ => ?_)
    fun _ _ _ => ?_
  · obtain ⟨rfl, htg⟩ := ht
    simp only [IndTypeRec.mapKeys_nIdx, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_type,
      Expr.stripPis_mapKeys]
    cases Expr.stripPis (t0.nP + t.nIdx) t.cv.type with
    | none => exact ExRel.throw'
    | some q =>
      obtain ⟨_, body⟩ := q
      cases body <;> first | exact ExRel.throw' | exact ExRel.pure' trivial
  have hmemG : ∀ x ∈ (t0 :: rest).zipIdx.map (fun x => (x.1.cv.name, x.2, x.1.nIdx)), x.1.Good P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (hty _ (List.fst_mem_of_mem_zipIdx hy)).1.1
  rw [← List.map_cons, members_map]
  refine ExRel.bind (S := fun (ms : List (MCtor md)) ms' => ms' = ms.map (MCtor.mapKeys f) ∧ ∀ mc ∈ ms, mc.Good P)
    (ExRel.forIn_same ⟨rfl, fun _ h => nomatch h⟩ fun m ms ms' hm hms => ?_) fun ms ms' hms => ?_
  · have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
    have hT := hty _ (getD_mem_of_lt hm' default)
    rw [getD_map_of_lt hm' default default]
    simp only [IndTypeRec.mapKeys_ctors, List.zipIdx_map, IndTypeRec.mapKeys_cv,
      ConstantVal.mapKeys_name]
    refine ExRel.bind (S := fun (ms : List (MCtor md)) ms' => ms' = ms.map (MCtor.mapKeys f) ∧ ∀ mc ∈ ms, mc.Good P)
      (ExRel.forIn_list (ListRel.of_map (G := fun x => x.1.Good P)
        fun x hx => hT.2 _ (List.fst_mem_of_mem_zipIdx hx)) hms ?_) fun ms ms' h => ExRel.pure' h
    intro x x' ms ms' hx hms
    obtain ⟨rfl, hxg⟩ := hx
    obtain ⟨cn, j⟩ := x
    obtain ⟨rfl, hmsg⟩ := hms
    simp only [Prod.map, id_eq]
    rw [find?_map_congr (p := fun c => c.cv.name == cn) fun c hc => by
      simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
      exact Key.map_beq hf (hct c hc).1 hxg]
    cases hcf : ctors.find? (fun c => c.cv.name == cn) with
    | none => exact ExRel.throw'
    | some c =>
    have hc := hct c (List.mem_of_find?_eq_some hcf)
    simp only [Option.map_some, IndCtorRec.mapKeys_nP, IndCtorRec.mapKeys_cv,
      ConstantVal.mapKeys_levelParams, List.length_map, List.head?_map]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
    have hcont : ∀ mc mc', mc' = mc.mapKeys f ∧ mc.Good P →
        ExRel (StepRel fun (ms : List (MCtor md)) ms' =>
            ms' = ms.map (MCtor.mapKeys f) ∧ ∀ mc ∈ ms, mc.Good P)
          (pure (ForInStep.yield (ms ++ [mc])) : Except String _)
          (pure (ForInStep.yield (ms.map (MCtor.mapKeys f) ++ [mc'])) : Except String _) := by
      intro mc mc' hmc
      refine ExRel.pure' ⟨by rw [hmc.1, List.map_append, List.map_cons, List.map_nil], ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hmsg x hx
      · rw [List.mem_singleton.mp hx]; exact hmc.2
    cases hR : recs.head? with
    | none =>
      exact ExRel.bind (classifyCtor_minors (minors := []) hf _ ht0.1.1 hmemG _ _ _ _
        (fun _ h => nomatch h) m j hc) hcont
    | some r =>
    have hr := hrc r (List.mem_of_head? hR)
    simp only [Option.map_some, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
    cases hrs : Expr.stripPis (t0.nP + (rest.length + 1) + ctors.length) r.cv.type with
    | none =>
      exact ExRel.bind (classifyCtor_minors (minors := []) hf _ ht0.1.1 hmemG _ _ _ _
        (fun _ h => nomatch h) m j hc) hcont
    | some q =>
    obtain ⟨rbs, _⟩ := q
    have hrbs := (Expr.stripPis_good hr.1.2 hrs).1
    simp only [Option.map_some, Expr.mapTele, minors_map]
    exact ExRel.bind (classifyCtor_minors hf _ ht0.1.1 hmemG _ _ _ _
      (Expr.goodList_map fun x hx => hrbs x (List.mem_of_mem_drop hx)) m j hc) hcont
  · obtain ⟨rfl, hmsg⟩ := hms
    simp only [List.length_map, List.getElem?_map]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
    refine ExRel.cond rfl (fun hrl => ?_) (fun _ => ExRel.throw')
    cases hr0 : recs[0]? with
    | none => exact ExRel.throw_bind
    | some r0 =>
    have hr0g := hrc r0 (List.mem_of_getElem? hr0)
    simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_levelParams]
    refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_same trivial fun m _ _ hm _ => ?_)
      fun _ _ _ => ?_
    · cases hrm : recs[m]? with
      | none => exact ExRel.throw_bind
      | some r =>
      have hrg := hrc r (List.mem_of_getElem? hrm)
      have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
      simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_nP, IndRecRec.mapKeys_nM,
        IndRecRec.mapKeys_nm, IndRecRec.mapKeys_nI, IndRecRec.mapKeys_cv,
        ConstantVal.mapKeys_levelParams, IndRecRec.mapKeys_rules, own_map,
        getD_map_of_lt hm' default default, IndTypeRec.mapKeys_nIdx]
      refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
      refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
      rw [rulesOk_map hf _ _ hrg.2 (fun mc hmc => hmsg mc (List.mem_filter.mp hmc).1)]
      exact ExRel.cond rfl (fun _ => ExRel.pure' trivial) (fun _ => ExRel.throw')
    ·
      refine ExRel.cond rfl (fun _ => ExRel.throw') (fun _ => ?_)
      have hl2 : ListRel (fun x x' => x' = IndTypeRec.mapKeys f x ∧ x.Good P) (t0 :: rest)
          ((t0 :: rest).map (IndTypeRec.mapKeys f)) := ListRel.of_map hty
      refine ExRel.bind (S := Eq) (ExRel.forIn_list hl2 rfl fun t t' W W' ht hW => ?_)
        fun W W' hW => ?_
      · obtain ⟨rfl, htg⟩ := ht
        subst hW
        simp only [IndTypeRec.mapKeys_nIdx, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_type,
          Expr.stripPis_mapKeys]
        cases hti : Expr.stripPis (t0.nP + t.nIdx) t.cv.type with
        | none => exact ExRel.throw'
        | some q =>
        obtain ⟨ibs, _⟩ := q
        have hibs := (Expr.stripPis_good htg.1.2 hti).1
        simp only [Option.map_some, Expr.mapTele]
        refine ExRel.bind (S := Eq) (ExRel.forIn_same rfl fun j W W' _ hW => ?_)
          fun W W' hW => ExRel.pure' hW
        subst hW
        rw [idxSort_mapKeysOn' hP hctx.tbl
          (ctx := (piBinders (List.take t0.nP pbs) ++ List.take j (piBinders (List.drop t0.nP ibs))).reverse)
          (e := (piBinders (List.drop t0.nP ibs)).getD j default) ?g1 ?g2 ?g3 ?g4]
        case g1 =>
          intro x hx
          simp only [List.mem_reverse, List.mem_append] at hx
          rcases hx with hx | hx
          · exact Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _) x hx
          · exact Expr.goodList_piBinders (Expr.BindersGood.drop hibs _) x (List.mem_of_mem_take hx)
        case g2 => exact Expr.GoodList.getD_default (Expr.goodList_piBinders (Expr.BindersGood.drop hibs _)) j
        case g3 => simp only [← mapBinders_drop, ← mapBinders_take, piBinders_mapBinders', List.map_reverse, List.map_append, List.map_take]
        case g4 => simp only [← mapBinders_drop, piBinders_mapBinders', getD_mapKeys_default]
        refine ExRel.bind (S := Eq) (ExRel.refl rfl) fun x x' hx => ?_
        subst hx
        cases x with
        | none => exact ExRel.throw'
        | some ℓ => exact ExRel.pure' rfl
      · subst hW
        rw [replacePiBody_sort_mapKeys]
        refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
          fun tagTy tagTy' htt => ?_
        obtain ⟨rfl, -⟩ := htt
        refine ExRel.bind (R := fun ds ds' => ds' = List.map (Declaration.mapKeys f) ds)
          (S := ListRel fun c c' => c' = (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2) ∧ True)
          (ExRel.mapM_same fun m hm => ?_) fun tagCtors tagCtors' htc => ?_
        · have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
          simp only [getD_map_of_lt hm' default default, IndTypeRec.mapKeys_cv,
            ConstantVal.mapKeys_type, IndTypeRec.mapKeys_nIdx, tagCtorTy_map]
          refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
            fun ty ty' hty' => ?_
          obtain ⟨rfl, -⟩ := hty'
          exact ExRel.pure' ⟨rfl, trivial⟩
        · obtain ⟨rfl, -⟩ := forall₂_map_eq htc
          rw [show (tagCtors.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)) =
            c4m f tagCtors from rfl]
          simp only [recTy_tag_map, recRhs_tag_map]
          refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
            fun tagRecTy tagRecTy' htr => ?_
          obtain ⟨rfl, -⟩ := htr
          refine ExRel.bind (S := ListRel fun r r' => r' = RecRule.mapKeys f r ∧ True)
            (ExRel.mapM_same fun m hm => ?_) fun tagRules tagRules' htru => ?_
          · have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
            simp only [getD_map_of_lt hm' default default, IndTypeRec.mapKeys_nIdx]
            refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
              fun rhs rhs' hrh => ?_
            obtain ⟨rfl, -⟩ := hrh
            exact ExRel.pure' ⟨rfl, trivial⟩
          · obtain ⟨rfl, -⟩ := forall₂_map_eq htru
            rw [auxTyBody_map, Expr.replacePiBody_mapKeys]
            refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
              fun auxTy auxTy' hat => ?_
            obtain ⟨rfl, -⟩ := hat
            refine ExRel.bind
              (S := fun cs cs' => ListRel (fun c c' =>
                c' = (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2) ∧ True) cs cs' ∧
                cs.length = ms.length)
              (ExRel.mapM_len (ListRel.of_map hmsg) fun mc mc' hmc => ?_) fun auxCtors auxCtors' hac => ?_
            · obtain ⟨rfl, hmcg⟩ := hmc
              simp only [MCtor.mapKeys_nty, MCtor.mapKeys_m, MCtor.mapKeys_j, MCtor.mapKeys_c,
                IndCtorRec.mapKeys_nF, MCtor.mapKeys_recFields,
                specFam_mapKeys _ _ _ _ hf hmemG hmcg.2, overFirstParams_mapKeys]
              refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
                fun ty ty' hty' => ?_
              obtain ⟨rfl, -⟩ := hty'
              exact ExRel.pure' ⟨rfl, trivial⟩
            · obtain ⟨hac, hlen⟩ := hac
              obtain ⟨rfl, -⟩ := forall₂_map_eq hac
              rw [show (auxCtors.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)) =
                c4m f auxCtors from rfl]
              simp only [recTy_aux_map, recRhs_aux_map]
              refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
                fun auxRecTy auxRecTy' har => ?_
              obtain ⟨rfl, -⟩ := har
              refine ExRel.bind (S := ListRel fun r r' => r' = RecRule.mapKeys f r ∧ True)
                (ExRel.mapM_same fun j hj => ?_) fun auxRules auxRules' haru => ?_
              · refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
                  fun rhs rhs' hrh => ?_
                obtain ⟨rfl, -⟩ := hrh
                have hj' : j < auxCtors.length := by
                  have := List.mem_range.mp hj
                  omega
                rw [c4m_getD hj']
                exact ExRel.pure' ⟨rfl, trivial⟩
              · obtain ⟨rfl, -⟩ := forall₂_map_eq haru
                have hbnG : ∀ k ∈ (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
                    List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs), k.Good P := by
                  intro k hk
                  simp only [List.mem_append, List.mem_cons, List.mem_map] at hk
                  rcases hk with ((rfl | ⟨t, ht, rfl⟩) | ⟨c, hc, rfl⟩) | ⟨r, hr, rfl⟩
                  · exact ht0.1.1
                  · exact (hty t (List.mem_cons_of_mem _ ht)).1.1
                  · exact (hct c hc).1
                  · exact (hrc r hr).1.1
                have hbn : (Key.map f t0.cv.name ::
                    List.map (fun x => x.cv.name) (List.map (IndTypeRec.mapKeys f) rest) ++
                    List.map (fun x => x.cv.name) (List.map (IndCtorRec.mapKeys f) ctors) ++
                    List.map (fun x => x.cv.name) (List.map (IndRecRec.mapKeys f) recs)) =
                    (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
                      List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs).map
                      (Key.map f) := by
                  simp [List.map_map, Function.comp_def]
                rw [hbn]
                refine ExRel.bind (S := fun (s : Array (Declaration md) × List (Key md × Nat)) s' =>
                    s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2 = keyMap f s.2 ∧ ∀ x ∈ s.2, x.1.Good P)
                  (ExRel.forIn_same ⟨?init, rfl, fun _ h => nomatch h⟩ fun m s s' hm hs => ?_)
                  fun s s' hs => ?_
                case init =>
                  simp [Declaration.mapKeys, ConstantInfo.mapKeys, ConstantVal.mapKeys, IndCaps.mapKeys,
                    List.map_append, List.map_map, Function.comp_def]
                · obtain ⟨out, hs⟩ := s
                  obtain ⟨out', hs'⟩ := s'
                  obtain ⟨h1, h2, hsG⟩ := hs
                  simp only at h1 h2 hsG
                  subst h1 h2
                  have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
                  have hT := hty _ (getD_mem_of_lt hm' default)
                  simp only [getD_map_of_lt hm' default default, IndTypeRec.mapKeys_nIdx,
                    IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_type, ConstantVal.mapKeys_name]
                  refine ExRel.bind (ExRel.need_pis (G := fun a => a.Good P) _ _ _ ?hb ?hG)
                    fun v v' hv => ?_
                  case hb => simp [Expr.mapKeys_mkAppN]
                  case hG =>
                    intro a ha
                    exact Expr.pisToLams_good hT.1.2 (by simp [ht0.1.1]) ha
                  obtain ⟨rfl, hvG⟩ := hv
                  refine ExRel.pure' ⟨?_, ?_, ?_⟩
                  · simp only [Array.map_push, Declaration.mapKeys]
                    exact congrArg (fun h => (Array.map (Declaration.mapKeys f) out).push
                      (Declaration.defnDecl _ (Expr.mapKeys f v) h)) (hint_eq hf hctx hsG hvG)
                  · simp only [keyMap_cons]
                    exact congrArg (fun h => (modelName (Key.map f _), hintHeight h) :: keyMap f hs)
                      (hint_eq hf hctx hsG hvG)
                  · intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hT.1.1
                    · exact hsG x hx
                · obtain ⟨out, hs⟩ := s
                  obtain ⟨out', hs'⟩ := s'
                  obtain ⟨h1, h2, hsG⟩ := hs
                  simp only at h1 h2 hsG
                  subst h1 h2
                  refine ExRel.bind (S := fun (s : Array (Declaration md) × List (Key md × Nat)) s' =>
                      s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2 = keyMap f s.2 ∧ ∀ x ∈ s.2, x.1.Good P)
                    (ExRel.forIn_list (ListRel.of_map hmsg) ⟨rfl, rfl, hsG⟩
                      fun mc mc' s s' hmc hs => ?_) fun s s' hs => ?_
                  · obtain ⟨rfl, hmcg⟩ := hmc
                    obtain ⟨out, hs⟩ := s
                    obtain ⟨out', hs'⟩ := s'
                    obtain ⟨h1, h2, hsG⟩ := hs
                    simp only at h1 h2 hsG
                    subst h1 h2
                    simp only [MCtor.mapKeys_c, IndCtorRec.mapKeys_nF, IndCtorRec.mapKeys_cv,
                      ConstantVal.mapKeys_type, ConstantVal.mapKeys_name, MCtor.mapKeys_m,
                      MCtor.mapKeys_j, rn_map hf hbnG hmcg.1.2]
                    refine ExRel.bind (ExRel.need_pis (G := fun a => a.Good P) _ _ _ ?hb ?hG)
                      fun v v' hv => ?_
                    case hb => simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def]
                    case hG =>
                      intro a ha
                      refine Expr.pisToLams_good (rn_good hmcg.1.2) ?_ ha
                      simp only [Expr.good_mkAppN_iff, Expr.good_constP, good_auxCtorName,
                        Expr.goodList_append, Expr.goodList_varsAt', true_and]
                      exact ⟨ht0.1.1, Expr.goodList_map fun _ _ => trivial⟩
                    obtain ⟨rfl, hvG⟩ := hv
                    refine ExRel.pure' ⟨?_, ?_, ?_⟩
                    · simp only [Array.map_push, Declaration.mapKeys]
                      exact congrArg (fun h => (Array.map (Declaration.mapKeys f) out).push
                        (Declaration.defnDecl _ (Expr.mapKeys f v) h)) (hint_eq hf hctx hsG hvG)
                    · simp only [keyMap_cons]
                      exact congrArg (fun h => (modelName (Key.map f _), hintHeight h) :: keyMap f hs)
                        (hint_eq hf hctx hsG hvG)
                    · intro x hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hmcg.1.1
                      · exact hsG x hx
                  · obtain ⟨out, hs⟩ := s
                    obtain ⟨out', hs'⟩ := s'
                    obtain ⟨h1, h2, hsG⟩ := hs
                    simp only at h1 h2 hsG
                    subst h1 h2
                    refine ExRel.bind (S := fun (s : Array (Declaration md) × List (Key md × Nat)) s' =>
                        s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2 = keyMap f s.2 ∧
                          ∀ x ∈ s.2, x.1.Good P)
                      (ExRel.forIn_same ⟨rfl, rfl, hsG⟩ fun m s s' hm hs => ?_) fun s s' hs => ?_
                    · obtain ⟨out, hs⟩ := s
                      obtain ⟨out', hs'⟩ := s'
                      obtain ⟨h1, h2, hsG⟩ := hs
                      simp only at h1 h2 hsG
                      subst h1 h2
                      have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
                      cases hrm : recs[m]? with
                      | none => exact ExRel.throw_bind
                      | some r =>
                      have hrg := hrc r (List.mem_of_getElem? hrm)
                      simp only [Option.map_some, pure_bind, getD_map_of_lt hm' default default,
                        IndTypeRec.mapKeys_nIdx, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_type,
                        ConstantVal.mapKeys_name, rn_map hf hbnG hrg.1.2]
                      refine ExRel.bind (ExRel.need_pis (G := fun a => a.Good P) _ _ _ ?hb ?hG)
                        fun v v' hv => ?_
                      case hb => simp [Expr.mapKeys_mkAppN]
                      case hG =>
                        intro a ha
                        refine Expr.pisToLams_good (rn_good hrg.1.2) ?_ ha
                        simp [ht0.1.1]
                      obtain ⟨rfl, hvG⟩ := hv
                      refine ExRel.pure' ⟨?_, ?_, ?_⟩
                      · simp only [Array.map_push, Declaration.mapKeys]
                        exact congrArg (fun h => (Array.map (Declaration.mapKeys f) out).push
                          (Declaration.defnDecl _ (Expr.mapKeys f v) h)) (hint_eq hf hctx hsG hvG)
                      · simp only [keyMap_cons]
                        exact congrArg (fun h => (modelName (Key.map f _), hintHeight h) :: keyMap f hs)
                          (hint_eq hf hctx hsG hvG)
                      · intro x hx
                        rcases List.mem_cons.mp hx with rfl | hx
                        · exact hrg.1.1
                        · exact hsG x hx
                    · obtain ⟨out, hs⟩ := s
                      obtain ⟨out', hs'⟩ := s'
                      obtain ⟨h1, h2, hsG⟩ := hs
                      simp only at h1 h2 hsG
                      subst h1 h2
                      refine ExRel.bind (S := fun (o : Array (Declaration md)) o' =>
                          o' = o.map (Declaration.mapKeys f))
                        (ExRel.forIn_same rfl fun m o o' hm ho => ?_) fun o o' ho => ?_
                      · subst ho
                        cases hrm : recs[m]? with
                        | none => exact ExRel.throw_bind
                        | some r =>
                        have hrg := hrc r (List.mem_of_getElem? hrm)
                        simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_cv,
                          ConstantVal.mapKeys_type, ConstantVal.mapKeys_name,
                          rn_map hf hbnG hrg.1.2, Expr.stripPis_mapKeys]
                        cases hpre : Expr.stripPis (t0.nP + (rest.length + 1) + ms.length)
                            (Expr.renameConsts (fun x => bif (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
                              List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs).contains x
                              then modelName x else x) r.cv.type) with
                        | none => exact ExRel.throw'
                        | some q =>
                        obtain ⟨prefixBs, _⟩ := q
                        have hpreG := (Expr.stripPis_good (rn_good hrg.1.2) hpre).1
                        simp only [Option.map_some, Expr.mapTele, own_map, List.length_map]
                        refine ExRel.bind (S := fun (o : Array (Declaration md)) o' =>
                            o' = o.map (Declaration.mapKeys f))
                          (ExRel.forIn_same rfl fun j o o' hj ho => ?_) fun o o' ho => ExRel.pure' ho
                        subst ho
                        have hj' := List.mem_range.mp hj
                        have hmcG : (List.filter (fun x => x.m == m) ms |>.getD j default).Good P :=
                          hmsg _ (List.mem_filter.mp (getD_mem_of_lt hj' default)).1
                        simp only [getD_map_of_lt hj' default default, MCtor.mapKeys_c, MCtor.mapKeys_nty,
                          MCtor.mapKeys_recFields, IndCtorRec.mapKeys_cv, IndCtorRec.mapKeys_nF,
                          ConstantVal.mapKeys_type, ConstantVal.mapKeys_name, rn_map hf hbnG hmcG.1.2,
                          rn_map hf hbnG hmcG.2, Expr.stripPis_mapKeys]
                        generalize (List.filter (fun x => x.m == m) ms).getD j default = mc at hmcG ⊢
                        generalize (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
                          List.map (fun x => x.cv.name) ctors ++
                          List.map (fun x => x.cv.name) recs) = bn at hbnG hpre ⊢
                        cases hc1 : Expr.stripPis t0.nP
                            (Expr.renameConsts (fun x => bif bn.contains x then modelName x else x)
                              mc.c.cv.type) with
                        | none => exact ExRel.throw'
                        | some q =>
                        obtain ⟨_, ctele⟩ := q
                        have hcteleG := (Expr.stripPis_good (rn_good hmcG.1.2) hc1).2
                        simp only [Option.map_some, Expr.mapTele]
                        rw [← Expr.mapKeys_liftLooseBVars, Expr.stripPis_mapKeys]
                        cases hc2 : Expr.stripPis mc.c.nF
                            (Expr.liftLooseBVars (rest.length + 1 + ms.length) 0 ctele) with
                        | none => exact ExRel.throw'
                        | some q =>
                        obtain ⟨fieldBs, cresid⟩ := q
                        have hc2G := Expr.stripPis_good (Expr.Good.liftLooseBVars hcteleG _ _) hc2
                        simp only [Option.map_some, Expr.mapTele]
                        cases hc3 : Expr.stripPis t0.nP
                            (Expr.renameConsts (fun x => bif bn.contains x then modelName x else x)
                              mc.nty) with
                        | none => exact ExRel.throw'
                        | some q =>
                        obtain ⟨_, nctele⟩ := q
                        have hncG := (Expr.stripPis_good (rn_good hmcG.2) hc3).2
                        simp only [Option.map_some, Expr.mapTele]
                        rw [← Expr.mapKeys_liftLooseBVars, Expr.stripPis_mapKeys]
                        cases hc4 : Expr.stripPis mc.c.nF
                            (Expr.liftLooseBVars (rest.length + 1 + ms.length) 0 nctele) with
                        | none => exact ExRel.throw'
                        | some q =>
                        obtain ⟨nfieldBs, _⟩ := q
                        have hc4G := (Expr.stripPis_good (Expr.Good.liftLooseBVars hncG _ _) hc4).1
                        simp only [Option.map_some, Expr.mapTele]
                        refine ExRel.bind (S := ListRel fun a b => b = a.mapKeys f ∧ True)
                          (ExRel.mapM_same fun x hx => ?_) fun ihs ihs' hih => ?_
                        · obtain ⟨i, tgt⟩ := x
                          cases hrt : recs[tgt]? with
                          | none => exact ExRel.throw_bind
                          | some rt =>
                          simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_cv,
                            ConstantVal.mapKeys_name, fst_getD_mapBinders, ← Expr.mapKeys_liftLooseBVars,
                            Expr.piBinders_mapKeys]
                          generalize (Expr.liftLooseBVars (mc.c.nF - i) 0
                            ((List.map (fun x => x.fst) nfieldBs).getD i default)).piBinders = q
                          obtain ⟨tele, body⟩ := q
                          simp only [Expr.mapTele, mapBinders_length]
                          refine ExRel.pure' ⟨?_, trivial⟩
                          rw [← Expr.mkLamsOf_mapKeys]
                          simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def]
                        · obtain ⟨rfl, -⟩ := forall₂_map_eq hih
                          have hfi : List.findIdx? (fun x => Key.map f x.c.cv.name == Key.map f mc.c.cv.name) ms =
                              List.findIdx? (fun x => x.c.cv.name == mc.c.cv.name) ms :=
                            findIdx?_congr_mem fun x hx => Key.map_beq hf (hmsg x hx).1.1 hmcG.1.1
                          refine ExRel.bind (ExRel.need_pis' (f := f) (G := fun _ => True) _ _ _ ?ht ?hb
                            (fun _ _ => trivial)) fun v v' hv => ?_
                          case ht => simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def, hfi, eqName, roleKey]
                          case hb => simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def, eqReflName, roleKey]
                          obtain ⟨rfl, -⟩ := hv
                          refine ExRel.pure' ?_
                          simp [StepRel, Array.map_push, Declaration.mapKeys, ConstantVal.mapKeys,
                            Expr.mapKeys_mkAppN, List.map_map, Function.comp_def, hfi, eqName, roleKey]
                      · subst ho
                        generalize (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
                          List.map (fun x => x.cv.name) ctors ++
                          List.map (fun x => x.cv.name) recs) = bn at hbnG ⊢
                        refine ExRel.cond rfl (fun _ => ?_)
                          (fun _ => ExRel.pure' (by rw [Array.toList_map]))
                        refine ExRel.bind (S := fun (s : Array (Declaration md) × List (Key md × Nat)) s' =>
                            s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2 = keyMap f s.2 ∧
                              ∀ x ∈ s.2, x.1.Good P)
                          (ExRel.forIn_same ⟨rfl, rfl, hsG⟩ fun m s s' hm hs => ?_)
                          fun s s' hs => ExRel.pure' (by rw [hs.1, Array.toList_map])
                        obtain ⟨out, hs⟩ := s
                        obtain ⟨out', hs'⟩ := s'
                        obtain ⟨h1, h2, hsG⟩ := hs
                        simp only at h1 h2 hsG
                        subst h1 h2
                        have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
                        rw [own_map]
                        cases hown : List.filter (fun x => x.m == m) ms with
                        | nil => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
                        | cons mc tl =>
                        cases tl with
                        | cons _ _ => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
                        | nil =>
                        have hmcG : mc.Good P := by
                          have : mc ∈ List.filter (fun x => x.m == m) ms := by
                            rw [hown]; exact List.mem_singleton_self mc
                          exact hmsg mc (List.mem_filter.mp this).1
                        have hT := hty _ (getD_mem_of_lt hm' default)
                        simp only [List.map_singleton, getD_map_of_lt hm' default default,
                          IndTypeRec.mapKeys_nIdx]
                        refine ExRel.cond rfl (fun _ => ?_) (fun _ => ?_)
                        · exact ExRel.pure' ⟨rfl, rfl, hsG⟩
                        cases hrm : recs[m]? with
                        | none => exact ExRel.throw_bind
                        | some r =>
                        have hrg := hrc r (List.mem_of_getElem? hrm)
                        simp only [Option.map_some, pure_bind, MCtor.mapKeys_c, IndCtorRec.mapKeys_nF,
                          IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_type, rn_map hf hbnG hmcG.1.2,
                          Expr.stripPis_mapKeys]
                        cases hcbs : Expr.stripPis (t0.nP + mc.c.nF)
                            (Expr.renameConsts (fun x => bif bn.contains x then modelName x else x)
                              mc.c.cv.type) with
                        | none => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
                        | some q =>
                        obtain ⟨cbs, _⟩ := q
                        have hcbsG := (Expr.stripPis_good (rn_good hmcG.1.2) hcbs).1
                        simp only [Option.map_some, Expr.mapTele]
                        refine ExRel.bind
                          (S := fun (s : Array (Declaration md) × List (Key md × Nat) × Bool) s' =>
                            s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2.1 = keyMap f s.2.1 ∧
                              s'.2.2 = s.2.2 ∧ ∀ x ∈ s.2.1, x.1.Good P)
                          (ExRel.forIn_same ⟨rfl, rfl, rfl, hsG⟩ fun i s s' hi hs => ?_)
                          fun s s' hs => ExRel.pure' ⟨hs.1, hs.2.1, hs.2.2.2⟩
                        obtain ⟨out, hs, stop⟩ := s
                        obtain ⟨out', hs', stop'⟩ := s'
                        obtain ⟨h1, h2, h3, hsG⟩ := hs
                        simp only at h1 h2 h3 hsG
                        subst h1 h2 h3
                        refine ExRel.cond rfl (fun _ => ?_) (fun _ => ?_)
                        · exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        have hi' := List.mem_range.mp hi
                        refine ExRel.bind (S := Eq) (ExRel.refl (congrArg Except.toOption
                          (Eq.symm (sortOf_mapKeysOn' hP (tblOn_local hf hctx.tbl ?hgt ?hgtG) ?hC ?hE ?h1 ?h2))))
                          fun x x' hx => ?_
                        case hgt =>
                          simp only [List.map_cons, List.map_append, List.map_map]
                          refine append_congr' (cons_congr' rfl (List.map_congr_left fun t _ => rfl))
                            (List.map_congr_left fun c hc => ?_)
                          simp only [Function.comp_apply, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name,
                            ConstantVal.mapKeys_type, rn_map hf hbnG (hct c hc).2]
                          rfl
                        case hgtG =>
                          intro x hx
                          simp only [List.mem_cons, List.mem_append, List.mem_map] at hx
                          rcases hx with (rfl | ⟨t, ht, rfl⟩) | ⟨c, hc, rfl⟩
                          · exact ⟨ht0.1.1, ht0.1.2⟩
                          · exact (hty t (List.mem_cons_of_mem _ ht)).1
                          · exact ⟨(hct c hc).1, rn_good (hct c hc).2⟩
                        case hC =>
                          intro x hx
                          simp only [List.mem_reverse, List.mem_map] at hx
                          obtain ⟨b, hb, rfl⟩ := hx
                          exact hcbsG b (List.mem_of_mem_take hb)
                        case hE => exact Expr.BindersGood.getD_fst hcbsG _
                        case h1 =>
                          simp only [Expr.mapBinders, List.map_map, List.map_reverse, ← List.map_take,
                            Function.comp_def]
                        case h2 => rw [mapBinders_getD]
                        subst hx
                        cases x with
                        | none => exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        | some ℓi =>
                        simp only []
                        generalize hip : Expr.instPisAtLift _ (Expr.renameConsts _ mc.c.cv.type) = ip
                        have hipG : ∀ e, ip = some e → e.Good P := by
                          intro e he
                          refine Expr.instPisAtLift_good ?_ (rn_good hmcG.1.2) (hip ▸ he)
                          intro x hx
                          simp only [List.mem_append, List.mem_map] at hx
                          rcases hx with hx | ⟨j, _, rfl⟩
                          · exact Expr.goodList_structProjPs _ x hx
                          · simp only [Expr.good_mkAppN_iff, Expr.goodList_append, Expr.goodList_cons,
                              Expr.goodList_nil]
                            exact ⟨hT.1.1, Expr.goodList_structProjPs _, trivial, trivial⟩
                        have h2 := congrArg (Option.map (Expr.mapKeys f)) hip
                        rw [← Expr.instPisAtLift_mapKeys] at h2
                        simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
                          Function.comp_def, structProjPs_mapKeys, Expr.mapKeys_mkAppN, constP_mapKeys,
                          projModelName_map, Expr.mapKeys, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name,
                          ConstantVal.mapKeys_type] at h2 ⊢
                        rw [h2]
                        cases ip with
                        | none => exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        | some e =>
                        have heG := hipG e rfl
                        cases e with
                        | forallE fdom fbody fm => ?_
                        | _ => exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        simp only [Option.map_some, Expr.mapKeys]
                        generalize hrp : Expr.replacePiBody t0.nP _ (Expr.forallE _ fdom bm) = rp
                        have hrpG : ∀ e, rp = some e → e.Good P := by
                          intro e he
                          refine Expr.replacePiBody_good hT.1.2 ?_ (hrp ▸ he)
                          exact ⟨Expr.good_mkAppN_iff.mpr ⟨hT.1.1, Expr.goodList_varsAt _ _⟩, heG.1⟩
                        have h3 := congrArg (Option.map (Expr.mapKeys f)) hrp
                        rw [← Expr.replacePiBody_mapKeys] at h3
                        simp only [Expr.mapKeys, Expr.mapKeys_mkAppN, constP_mapKeys, modelName_map,
                          varsAt_mapKeys] at h3
                        rw [h3]
                        cases rp with
                        | none => exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        | some pty =>
                        have hptyG := hrpG pty rfl
                        simp only [Option.map_some, Expr.stripPis_mapKeys]
                        generalize hsp : Expr.stripPis (t0.nP + 1) pty = sp
                        cases sp with
                        | none => exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        | some q =>
                        obtain ⟨pbs', _⟩ := q
                        have hpbs'G := (Expr.stripPis_good hptyG hsp).1
                        simp only [Option.map_some, Expr.mapTele]
                        have hD : (mkLams (piBinders pbs')
                            (Expr.proj (modelName ((t0 :: rest).getD m default).cv.name) i (Expr.bvar 0))).Good P :=
                          Expr.good_mkLams (Expr.goodList_piBinders hpbs'G) ⟨hT.1.1, trivial⟩
                        simp only [IndRecRec.mapKeys_cv, ConstantVal.mapKeys_type, ConstantVal.mapKeys_name,
                          rn_map hf hbnG hrg.1.2, piBinders_mapBinders']
                        generalize hpv : projRecValue _ ℓi pty _ i = pv
                        cases pv with
                        | none =>
                          have h4 := projRecValue_map_none hP hf hpv ⟨hT.1.1, hmcG.1.1, hrg.1.1, rn_good hrg.1.2⟩
                            hptyG hD
                          simp only [Frontend.ProjRecOwner.mapKeys, modelName_map, mkLams_mapKeys,
                            Expr.mapKeys] at h4
                          rw [h4]
                          exact ExRel.pure' ⟨rfl, rfl, rfl, hsG⟩
                        | some pval =>
                        obtain ⟨h4, hpvG⟩ := projRecValue_map_some hP hf hpv
                          ⟨hT.1.1, hmcG.1.1, hrg.1.1, rn_good hrg.1.2⟩ hptyG hD
                        simp only [Frontend.ProjRecOwner.mapKeys, modelName_map, mkLams_mapKeys,
                          Expr.mapKeys] at h4
                        rw [h4]
                        simp only []
                        generalize hpf : Expr.pisToLams (t0.nP + mc.c.nF) (mkPis (piBinders cbs) _) _ = pfo
                        have h5 := congrArg (Option.map (Expr.mapKeys f)) hpf
                        rw [← Expr.pisToLams_mapKeys] at h5
                        simp only [mkPis_mapKeys, List.map_append, List.map_cons,
                          List.map_nil, List.map_map, Function.comp_def, Expr.mapKeys_mkAppN, Expr.mapKeys,
                          Expr.mapKeys_liftLooseBVars, mapBinders_getD, constP_mapKeys, projModelName_map,
                          modelName_map, varsAt_mapKeys, eqName, eqReflName, roleKey,
                          Key.map_role] at h5 ⊢
                        rw [h5]
                        generalize hh : hintFor _ pval = hv
                        generalize hh' : hintFor _ (Expr.mapKeys f pval) = hv'
                        have hhv : hv' = hv := hh'.symm.trans ((hint_eq hf hctx hsG hpvG).trans hh)
                        subst hhv
                        have hheights : ∀ x ∈ (projModelName ((t0 :: rest).getD m default).cv.name i,
                            hintHeight hv') :: hs, x.1.Good P := by
                          intro x hx
                          rcases List.mem_cons.mp hx with rfl | hx
                          · exact hT.1.1
                          · exact hsG x hx
                        cases pfo with
                        | none =>
                          refine ExRel.pure' ⟨?_, ?_, rfl, hheights⟩
                          · simp [Array.map_push, Declaration.mapKeys, ConstantVal.mapKeys]
                          · simp [keyMap_cons]
                        | some pf =>
                        simp only [Option.map_some]
                        refine ExRel.pure' ⟨?_, ?_, rfl, hheights⟩
                        · simp [Array.map_push, Declaration.mapKeys, ConstantVal.mapKeys, Expr.mapKeys_mkAppN,
                            List.map_map, Function.comp_def]
                        · simp [keyMap_cons]

end Ix.Kernel.Frontend.InModel
