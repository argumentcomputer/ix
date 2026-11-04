module

public import IxC.Kernel.Verify.Frontend.InModelKitRename
public import IxC.Kernel.Verify.Rename.Decl1
public import IxC.Kernel.Verify.Rename.Ind2
public import IxC.Kernel.Verify.Rename.Ind3
public import IxC.Kernel.Verify.Rename.Native3
public import IxC.Kernel.Verify.Rename.Modeled1

@[expose] public section

/-!
# The mutual rung's pieces under a renaming injective on a scope (parametricity, step 3)

The parsed block renamed (`BlockRec.mapKeys`) and what the generator reads
besides it (`CtxAgree`: the constant table, the heights and the parsed blocks
agree at every good key, and hold good values there); then the mutual rung's
helpers: `replacePiDomAt`, `noBVarsIn`, `memberApp?` (a lookup by key and a
comparison of terms, so under `InjOn`), `minorIH?`.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode}

/-! ## The parsed block, renamed -/

section Maps

variable (f : md.Id → md'.Id) (P : KeyScope md)

/-- Rename an inductive type of a parsed block. -/
def IndTypeRec.mapKeys (t : IndTypeRec md) : IndTypeRec md' :=
  ⟨t.cv.mapKeys f, t.nP, t.nIdx, t.ctors.map (Key.map f), t.isRec, t.isReflexive, t.numNested⟩

/-- A good inductive type: its header and its constructor names. -/
def IndTypeRec.Good (t : IndTypeRec md) : Prop := t.cv.Good P ∧ ∀ k ∈ t.ctors, k.Good P

/-- Rename a constructor of a parsed block. -/
def IndCtorRec.mapKeys (c : IndCtorRec md) : IndCtorRec md' := ⟨c.cv.mapKeys f, c.nP, c.nF⟩

/-- A good constructor: its header. -/
def IndCtorRec.Good (c : IndCtorRec md) : Prop := c.cv.Good P

/-- Rename a recursor of a parsed block. -/
def IndRecRec.mapKeys (r : IndRecRec md) : IndRecRec md' :=
  ⟨r.cv.mapKeys f, r.nP, r.nM, r.nm, r.nI, r.rules.map (RecRule.mapKeys f)⟩

/-- A good recursor: its header and its rules. -/
def IndRecRec.Good (r : IndRecRec md) : Prop := r.cv.Good P ∧ ∀ x ∈ r.rules, x.Good P

/-- **Rename a parsed block.** -/
def BlockRec.mapKeys (b : BlockRec md) : BlockRec md' :=
  ⟨b.types.map (IndTypeRec.mapKeys f), b.ctors.map (IndCtorRec.mapKeys f),
   b.recs.map (IndRecRec.mapKeys f)⟩

/-- **A good parsed block**: every key it carries is good. -/
def BlockRec.Good (b : BlockRec md) : Prop :=
  (∀ t ∈ b.types, t.Good P) ∧ (∀ c ∈ b.ctors, c.Good P) ∧ ∀ r ∈ b.recs, r.Good P

/-- **The generator's context agrees on the scope**: at every renamed good key
the renamed declared type, the same height, the renamed parsed block; and the
types and blocks at good keys are good. -/
structure CtxAgree (ctx : Ctx md) (ctx' : Ctx md') : Prop where
  tbl : TblOn P f ctx.tbl ctx'.tbl
  heights : ∀ k : Key md, k.Good P → ctx'.heights (k.map f) = ctx.heights k
  blocks : ∀ k : Key md, k.Good P → ctx'.blocks (k.map f) = (ctx.blocks k).map (BlockRec.mapKeys f)
  blocksGood : ∀ k : Key md, k.Good P → ∀ b, ctx.blocks k = some b → b.Good P

/-- Rename a classified constructor. -/
def MCtor.mapKeys (mc : MCtor md) : MCtor md' :=
  ⟨mc.m, mc.j, mc.c.mapKeys f, mc.recFields, mc.nty.mapKeys f⟩

/-- A good classified constructor. -/
def MCtor.Good (mc : MCtor md) : Prop := mc.c.Good P ∧ mc.nty.Good P

end Maps

variable {P : KeyScope md} {f : md.Id → md'.Id}

@[simp] theorem IndTypeRec.mapKeys_cv (t : IndTypeRec md) : (t.mapKeys f).cv = t.cv.mapKeys f := rfl
@[simp] theorem IndTypeRec.mapKeys_nP (t : IndTypeRec md) : (t.mapKeys f).nP = t.nP := rfl
@[simp] theorem IndTypeRec.mapKeys_nIdx (t : IndTypeRec md) : (t.mapKeys f).nIdx = t.nIdx := rfl
@[simp] theorem IndTypeRec.mapKeys_ctors (t : IndTypeRec md) :
    (t.mapKeys f).ctors = t.ctors.map (Key.map f) := rfl
@[simp] theorem IndTypeRec.mapKeys_numNested (t : IndTypeRec md) :
    (t.mapKeys f).numNested = t.numNested := rfl
@[simp] theorem IndCtorRec.mapKeys_cv (c : IndCtorRec md) : (c.mapKeys f).cv = c.cv.mapKeys f := rfl
@[simp] theorem IndCtorRec.mapKeys_nP (c : IndCtorRec md) : (c.mapKeys f).nP = c.nP := rfl
@[simp] theorem IndCtorRec.mapKeys_nF (c : IndCtorRec md) : (c.mapKeys f).nF = c.nF := rfl
@[simp] theorem IndRecRec.mapKeys_cv (r : IndRecRec md) : (r.mapKeys f).cv = r.cv.mapKeys f := rfl
@[simp] theorem IndRecRec.mapKeys_nP (r : IndRecRec md) : (r.mapKeys f).nP = r.nP := rfl
@[simp] theorem IndRecRec.mapKeys_nM (r : IndRecRec md) : (r.mapKeys f).nM = r.nM := rfl
@[simp] theorem IndRecRec.mapKeys_nm (r : IndRecRec md) : (r.mapKeys f).nm = r.nm := rfl
@[simp] theorem IndRecRec.mapKeys_nI (r : IndRecRec md) : (r.mapKeys f).nI = r.nI := rfl
@[simp] theorem IndRecRec.mapKeys_rules (r : IndRecRec md) :
    (r.mapKeys f).rules = r.rules.map (RecRule.mapKeys f) := rfl
@[simp] theorem BlockRec.mapKeys_types (b : BlockRec md) :
    (b.mapKeys f).types = b.types.map (IndTypeRec.mapKeys f) := rfl
@[simp] theorem BlockRec.mapKeys_ctors (b : BlockRec md) :
    (b.mapKeys f).ctors = b.ctors.map (IndCtorRec.mapKeys f) := rfl
@[simp] theorem BlockRec.mapKeys_recs (b : BlockRec md) :
    (b.mapKeys f).recs = b.recs.map (IndRecRec.mapKeys f) := rfl
@[simp] theorem MCtor.mapKeys_m (mc : MCtor md) : (mc.mapKeys f).m = mc.m := rfl
@[simp] theorem MCtor.mapKeys_j (mc : MCtor md) : (mc.mapKeys f).j = mc.j := rfl
@[simp] theorem MCtor.mapKeys_c (mc : MCtor md) : (mc.mapKeys f).c = mc.c.mapKeys f := rfl
@[simp] theorem MCtor.mapKeys_recFields (mc : MCtor md) : (mc.mapKeys f).recFields = mc.recFields :=
  rfl
@[simp] theorem MCtor.mapKeys_nty (mc : MCtor md) : (mc.mapKeys f).nty = mc.nty.mapKeys f := rfl

/-! ## Telescope pieces -/

theorem mapBinders_getD (bs : List (Expr md × BinderMeta)) (i : Nat) :
    (Expr.mapBinders f bs).getD i default = ((bs.getD i default).1.mapKeys f, (bs.getD i default).2) := by
  simp only [Expr.mapBinders, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bs[i]? <;> rfl

theorem Expr.BindersGood.getD_fst {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs)
    (i : Nat) : (bs.getD i default).1.Good P := by
  rw [List.getD_eq_getElem?_getD]
  cases hb : bs[i]? with
  | none => trivial
  | some b => exact h b (List.mem_of_getElem? hb)

@[simp] theorem piBinders_mapBinders' (bs : List (Expr md × BinderMeta)) :
    piBinders (Expr.mapBinders f bs) = (piBinders bs).map (Expr.mapKeys f) := by
  simp [piBinders, Expr.mapBinders]

theorem Expr.goodList_piBinders' {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs) :
    Expr.GoodList P (piBinders bs) :=
  Expr.goodList_piBinders h

theorem Expr.BindersGood.take {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs) (n : Nat) :
    Expr.BindersGood P (bs.take n) := fun b hb => h b (List.mem_of_mem_take hb)

theorem Expr.BindersGood.drop {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs) (n : Nat) :
    Expr.BindersGood P (bs.drop n) := fun b hb => h b (List.mem_of_mem_drop hb)

@[simp] theorem mapBinders_take (bs : List (Expr md × BinderMeta)) (n : Nat) :
    Expr.mapBinders f (bs.take n) = (Expr.mapBinders f bs).take n := by
  simp [Expr.mapBinders, List.map_take]

@[simp] theorem mapBinders_drop (bs : List (Expr md × BinderMeta)) (n : Nat) :
    Expr.mapBinders f (bs.drop n) = (Expr.mapBinders f bs).drop n := by
  simp [Expr.mapBinders, List.map_drop]

@[simp] theorem mapBinders_length (bs : List (Expr md × BinderMeta)) :
    (Expr.mapBinders f bs).length = bs.length := by
  simp [Expr.mapBinders]

theorem Expr.replacePiBody_good : ∀ {k : Nat} {e b r : Expr md}, e.Good P → b.Good P →
    Expr.replacePiBody k e b = some r → r.Good P
  | 0, _, b, r, _, hb, h => by
    simp only [Expr.replacePiBody, Option.some.injEq] at h; subst h; exact hb
  | k + 1, e, b, r, he, hb, h => by
    cases e with
    | forallE t body m =>
      simp only [Expr.replacePiBody, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      exact ⟨he.1, Expr.replacePiBody_good he.2 hb hr'⟩
    | _ => simp [Expr.replacePiBody] at h

theorem overFirstParams_mapKeys (nP : Nat) (former ty : Expr md) :
    overFirstParams nP (former.mapKeys f) (ty.mapKeys f) =
      (overFirstParams nP former ty).map (Expr.mapKeys f) := by
  simp only [overFirstParams, Expr.stripPis_mapKeys]
  cases ty.stripPis nP with
  | none => rfl
  | some q => simp [Expr.mapTele, Expr.replacePiBody_mapKeys]

theorem overFirstParams_good {nP : Nat} {former ty r : Expr md} (hf : former.Good P) (ht : ty.Good P)
    (h : overFirstParams nP former ty = some r) : r.Good P := by
  simp only [overFirstParams, Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, hr⟩ := h
  exact Expr.replacePiBody_good hf (Expr.stripPis_good ht hq).2 hr

/-! ## `replacePiDomAt` -/

theorem replacePiDomAt_mapKeys : ∀ (n : Nat) (e d : Expr md),
    replacePiDomAt n (e.mapKeys f) (d.mapKeys f) = (replacePiDomAt n e d).map (Expr.mapKeys f)
  | 0, .forallE _ b mt, d => rfl
  | n + 1, .forallE t b mt, d => by
    simp only [Expr.mapKeys, replacePiDomAt, replacePiDomAt_mapKeys n b d, Option.map_map]
    rfl
  | 0, .bvar _, _ | 0, .fvar _ _, _ | 0, .sort _, _ | 0, .const _ _, _ | 0, .app _ _, _
  | 0, .lam _ _ _, _ | 0, .letE _ _ _ _, _ | 0, .lit _, _ | 0, .proj _ _ _, _ => rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem replacePiDomAt_good : ∀ {n : Nat} {e d r : Expr md}, e.Good P → d.Good P →
    replacePiDomAt n e d = some r → r.Good P
  | 0, .forallE _ b mt, d, r, he, hd, h => by
    simp only [replacePiDomAt, Option.some.injEq] at h; subst h; exact ⟨hd, he.2⟩
  | n + 1, .forallE t b mt, d, r, he, hd, h => by
    simp only [replacePiDomAt, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact ⟨he.1, replacePiDomAt_good he.2 hd hr'⟩
  | 0, .bvar _, _, _, _, _, h | 0, .fvar _ _, _, _, _, _, h | 0, .sort _, _, _, _, _, h
  | 0, .const _ _, _, _, _, _, h | 0, .app _ _, _, _, _, _, h | 0, .lam _ _ _, _, _, _, _, h
  | 0, .letE _ _ _ _, _, _, _, _, h | 0, .lit _, _, _, _, _, h | 0, .proj _ _ _, _, _, _, _, h
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h | _ + 1, .sort _, _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, _, h | _ + 1, .app _ _, _, _, _, _, h
  | _ + 1, .lam _ _ _, _, _, _, _, h | _ + 1, .letE _ _ _ _, _, _, _, _, h
  | _ + 1, .lit _, _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

/-! ## `noBVarsIn` -/

theorem noBVarsIn_mapKeys (hf : InjOn f P) {e : Expr md} (he : e.Good P) (lo n : Nat) :
    noBVarsIn (e.mapKeys f) lo n = noBVarsIn e lo n := by
  simp only [noBVarsIn, ← Expr.mapKeys_lowerBVars, ← Expr.mapKeys_liftLooseBVars]
  exact Expr.mapKeys_beq hf (Expr.Good.liftLooseBVars (Expr.Good.lowerBVars he _ _) _ _) he

/-! ## `memberApp?` -/

theorem memberApp?_mapKeys (hf : InjOn f P) {members : List (Key md × Nat × Nat)}
    (hm : ∀ x ∈ members, x.1.Good P) (lps : List LevelParam) (nP o : Nat) {e : Expr md}
    (he : e.Good P) :
    memberApp? (keyMap f members) lps nP o (e.mapKeys f) = memberApp? members lps nP o e := by
  unfold memberApp?
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hfn := Expr.Good.getAppFn he
  have hargs := Expr.Good.getAppArgs he
  generalize e.getAppFn = F at hfn ⊢
  cases F with
  | const x us =>
    simp only [Expr.mapKeys]
    rw [find?_keyMap hf hm hfn]
    cases members.find? (·.1 == x) with
    | none => rfl
    | some y =>
      obtain ⟨y, m', nIdx⟩ := y
      simp only [Option.map_some, List.length_map, ← List.map_take]
      rw [← varsAt_mapKeys (f := f) o nP,
        list_mapKeys_beq hf (fun _ h => hargs _ (List.mem_of_mem_take h)) (Expr.goodList_varsAt o nP)]
  | _ => rfl

theorem memberApp?_mapKeys' (hf : InjOn f P) {members : List (Key md × Nat × Nat)}
    (hm : ∀ x ∈ members, x.1.Good P) (lps : List LevelParam) (nP o : Nat) {e : Expr md}
    (he : e.Good P) :
    memberApp? (keyMap f members) lps nP o (e.mapKeys f) = memberApp? members lps nP o e :=
  memberApp?_mapKeys hf hm lps nP o he

/-! ## `minorIH?` -/

/-- A search over a renamed list, each element's answer the renamed one. -/
theorem findSome?_map_rel {α α' β β' : Type} {g : α → Option β} {g' : α' → Option β'} {h : α → α'}
    {φ : β → β'} {l : List α} (hg : ∀ x ∈ l, g' (h x) = (g x).map φ) :
    (l.map h).findSome? g' = (l.findSome? g).map φ := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.findSome?_cons, hg a List.mem_cons_self]
    cases g a with
    | none => exact ih fun x hx => hg x (List.mem_cons_of_mem _ hx)
    | some b => rfl

/-- `List.all` at two predicates agreeing on the list's elements. -/
theorem all_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.all p = l.all q
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, h a List.mem_cons_self,
      all_congr_mem (l := as) fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem minorIH?_mapKeys (hf : InjOn f P) (k J nF i : Nat) {minor : Expr md} (hmin : minor.Good P) :
    minorIH? k J nF i (minor.mapKeys f) =
      (minorIH? k J nF i minor).map fun p => (p.1, p.2.map (Expr.mapKeys f)) := by
  unfold minorIH?
  simp only [← Bool.cond_eq_ite]
  rw [Expr.piBinders_mapKeys]
  have hbs := (Expr.piBinders_good hmin).1
  generalize minor.piBinders = q at hbs ⊢
  obtain ⟨bs, _⟩ := q
  simp only [Expr.mapTele, mapBinders_length]
  generalize (decide (bs.length < nF) || decide (i ≥ nF)) = c
  cases c with
  | true => rfl
  | false =>
    simp only [cond_false]
    rw [← mapBinders_drop, Expr.mapBinders, List.zipIdx_map]
    refine findSome?_map_rel fun x hx => ?_
    obtain ⟨⟨ty, mt⟩, k'⟩ := x
    have hty : ty.Good P := hbs _ (List.mem_of_mem_drop (List.fst_mem_of_mem_zipIdx hx))
    dsimp only [Function.comp_apply, Prod.map, id_eq]
    rw [Expr.piBinders_mapKeys]
    have hb := (Expr.piBinders_good hty).2
    generalize ty.piBinders = q2 at hb ⊢
    obtain ⟨tele, body⟩ := q2
    simp only [Expr.mapTele, Expr.mapBinders, List.isEmpty_map]
    generalize (!tele.isEmpty) = c2
    cases c2 with
    | true => rfl
    | false =>
      simp only [cond_false]
      rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys, List.getLast?_map]
      have hargs := Expr.Good.getAppArgs hb
      generalize body.getAppArgs = A at hargs ⊢
      generalize body.getAppFn = F
      cases F with
      | bvar mv =>
        cases hl : A.getLast? with
        | none => rfl
        | some z =>
          cases z with
          | bvar fv =>
            simp only [Option.map_some, Expr.mapKeys, List.length_map, ← List.map_take,
              List.all_map]
            have hidx : ∀ e ∈ A.take (A.length - 1), e.Good P :=
              fun e he => hargs e (List.mem_of_mem_take he)
            have hall : ((A.take (A.length - 1)).all ((fun e =>
                noBVarsIn e 0 (k' + nF - i) && noBVarsIn e (k' + nF) (k + J)) ∘ Expr.mapKeys f)) =
                (A.take (A.length - 1)).all fun e =>
                  noBVarsIn e 0 (k' + nF - i) && noBVarsIn e (k' + nF) (k + J) := by
              refine all_congr_mem fun e he => ?_
              simp only [Function.comp_apply]
              rw [noBVarsIn_mapKeys hf (hidx e he), noBVarsIn_mapKeys hf (hidx e he)]
            rw [hall]
            generalize (fv != k' + (nF - 1 - i)) = c3
            cases c3 with
            | true => rfl
            | false =>
              simp only [cond_false]
              generalize (decide (mv < k' + nF + J) || decide (mv ≥ k' + nF + J + k)) = c4
              cases c4 with
              | true => rfl
              | false =>
                simp only [cond_false]
                generalize ((A.take (A.length - 1)).all fun e =>
                  noBVarsIn e 0 (k' + nF - i) && noBVarsIn e (k' + nF) (k + J)) = c5
                cases c5 with
                | true =>
                  simp only [cond_true, Option.map_some, List.map_map, Function.comp_def,
                    Expr.mapKeys_lowerBVars]
                | false => rfl
          | _ => rfl
      | _ => rfl

theorem minorIH?_good (k J nF i : Nat) {minor : Expr md} (hmin : minor.Good P) {m' : Nat}
    {idx : List (Expr md)} (h : minorIH? k J nF i minor = some (m', idx)) : Expr.GoodList P idx := by
  unfold minorIH? at h
  simp only [← Bool.cond_eq_ite] at h
  have hbs := (Expr.piBinders_good hmin).1
  generalize minor.piBinders = q at hbs h
  obtain ⟨bs, _⟩ := q
  generalize (decide (bs.length < nF) || decide (i ≥ nF)) = c at h
  cases c with
  | true => exact nomatch h
  | false =>
    simp only [cond_false] at h
    obtain ⟨⟨⟨ty, mt⟩, k'⟩, hx, hy⟩ := List.exists_of_findSome?_eq_some h
    have hty : ty.Good P := hbs _ (List.mem_of_mem_drop (List.fst_mem_of_mem_zipIdx hx))
    dsimp only at hy
    have hb := (Expr.piBinders_good hty).2
    generalize ty.piBinders = q2 at hb hy
    obtain ⟨tele, body⟩ := q2
    dsimp only at hy
    generalize (!tele.isEmpty) = c2 at hy
    cases c2 with
    | true => exact nomatch hy
    | false =>
      simp only [cond_false] at hy
      have hargs := Expr.Good.getAppArgs hb
      generalize body.getAppArgs = A at hargs hy
      generalize body.getAppFn = F at hy
      cases F with
      | bvar mv =>
        cases hl : A.getLast? with
        | none => rw [hl] at hy; exact nomatch hy
        | some z =>
          rw [hl] at hy
          cases z with
          | bvar fv =>
            dsimp only at hy
            generalize (fv != k' + (nF - 1 - i)) = c3 at hy
            cases c3 with
            | true => exact nomatch hy
            | false =>
              simp only [cond_false] at hy
              generalize (decide (mv < k' + nF + J) || decide (mv ≥ k' + nF + J + k)) = c4 at hy
              cases c4 with
              | true => exact nomatch hy
              | false =>
                simp only [cond_false] at hy
                generalize ((A.take (A.length - 1)).all fun e =>
                  noBVarsIn e 0 (k' + nF - i) && noBVarsIn e (k' + nF) (k + J)) = c5 at hy
                cases c5 with
                | true =>
                  simp only [cond_true, Option.some.injEq, Prod.mk.injEq] at hy
                  obtain ⟨-, rfl⟩ := hy
                  exact Expr.goodList_map fun e he => Expr.Good.lowerBVars (Expr.Good.lowerBVars
                    (Expr.Good.lowerBVars (hargs e (List.mem_of_mem_take he)) _ _) _ _) _ _
                | false => exact nomatch hy
          | _ => exact nomatch hy
      | _ => exact nomatch hy

/-! ## `classifyCtor` -/

theorem ExRel.throw_bind {ε ε' α β γ δ : Type} {R : α → β → Prop} {e : ε} {e' : ε'}
    {g : γ → Except ε α} {g' : δ → Except ε' β} :
    ExRel R (throw (m := Except ε) e >>= g) (throw (m := Except ε') e' >>= g') :=
  trivial

@[simp] theorem keyMap_fst {β : Type} (l : List (Key md × β)) :
    (keyMap f l).map (fun x => x.1) = (l.map fun x => x.1).map (Key.map f) := by
  simp [keyMap]

theorem keyMap_getElem? {β : Type} (l : List (Key md × β)) (i : Nat) :
    (keyMap f l)[i]? = l[i]?.map fun x => (x.1.map f, x.2) := by
  simp [keyMap]

@[simp] theorem isEmpty_mapBinders (bs : List (Expr md × BinderMeta)) :
    (Expr.mapBinders f bs).isEmpty = bs.isEmpty := by
  simp [Expr.mapBinders]

theorem any_mentions_mapBinders (hf : InjOn f P) {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P)
    {bs : List (Expr md × BinderMeta)} (hbs : Expr.BindersGood P bs) :
    ((Expr.mapBinders f bs).any fun b => mentionsAny (ns.map (Key.map f)) b.1) =
      bs.any fun b => mentionsAny ns b.1 := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨t, mt⟩ := a
    simp only [Expr.mapBinders_cons, List.any_cons]
    rw [mentionsAny_mapKeys hf hns (hbs _ List.mem_cons_self),
      ih fun b hb => hbs b (List.mem_cons_of_mem _ hb)]

theorem classifyCtor_mapKeys (hf : InjOn f P) (T : Key md) (hT : T.Good P)
    {members : List (Key md × Nat × Nat)} (hm : ∀ x ∈ members, x.1.Good P) (lps : List LevelParam)
    (nP k J : Nat) {minor : Option (Expr md)} (hmin : ∀ e, minor = some e → e.Good P) (m j : Nat)
    {c : IndCtorRec md} (hc : c.Good P) :
    ExRel (fun mc mc' => mc' = mc.mapKeys f ∧ mc.Good P)
      (classifyCtor T members lps nP k J minor m j c)
      (classifyCtor (T.map f) (keyMap f members) lps nP k J (minor.map (Expr.mapKeys f)) m j
        (c.mapKeys f)) := by
  have hns : ∀ n ∈ members.map (fun x => x.1), n.Good P := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hn
    exact hm x hx
  unfold classifyCtor
  simp only [← Bool.cond_eq_ite, IndCtorRec.mapKeys_cv, IndCtorRec.mapKeys_nF,
    ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
  have hst := fun bs resid (h : c.cv.type.stripPis (nP + c.nF) = some (bs, resid)) =>
    Expr.stripPis_good hc.2 h
  cases hs : c.cv.type.stripPis (nP + c.nF) with
  | none => exact ExRel.throw'
  | some q =>
  obtain ⟨bs, resid⟩ := q
  obtain ⟨hbs, hres⟩ := hst bs resid hs
  simp only [Option.map_some, Expr.mapTele, memberApp?_mapKeys hf hm lps nP c.nF hres]
  generalize (memberApp? members lps nP c.nF resid == some m) = c0
  cases c0 with
  | false => exact ExRel.throw_bind
  | true =>
  simp only [cond_true]
  refine ExRel.bind (S := fun s s' => s'.1 = s.1 ∧ s'.2 = s.2.mapKeys f ∧ s.2.Good P)
    (ExRel.forIn_same ⟨rfl, rfl, hc.2⟩ ?_) ?_
  · intro i s s' _ hs
    obtain ⟨rf, nty⟩ := s
    obtain ⟨rf', nty'⟩ := s'
    obtain ⟨h1, h2, hnty⟩ := hs
    simp only at h1 h2 hnty
    subst h1 h2
    have hd := Expr.BindersGood.getD_fst hbs (nP + i)
    have hpb := Expr.piBinders_good hd
    simp only [keyMap_fst, mapBinders_getD, mentionsAny_mapKeys hf hns hd, Expr.piBinders_mapKeys,
      Expr.mapTele, any_mentions_mapBinders hf hns hpb.1, mapBinders_length,
      memberApp?_mapKeys hf hm lps nP _ hpb.2, specFam_mapKeys T lps nP members hf hm hd,
      mentionsAny_mapKeys hf hns (specFam_good T lps nP members hT hd), isEmpty_mapBinders]
    generalize (bs.getD (nP + i) default).1 = d at hd hpb ⊢
    generalize d.piBinders = q at hpb ⊢
    obtain ⟨tele, body⟩ := q
    simp only at hpb ⊢
    cases mentionsAny (members.map fun x => x.1) d with
    | false => exact ExRel.pure' ⟨rfl, rfl, hnty⟩
    | true =>
    simp only [cond_true]
    cases (tele.any fun b => mentionsAny (members.map fun x => x.1) b.1) with
    | true => exact ExRel.throw_bind
    | false =>
    simp only [cond_false]
    cases memberApp? members lps nP (i + tele.length) body with
    | some m' => exact ExRel.pure' ⟨rfl, rfl, hnty⟩
    | none =>
    simp only []
    cases mentionsAny (members.map fun x => x.1) (specFam T lps nP members d) with
    | true => exact ExRel.throw_bind
    | false =>
    simp only [cond_false]
    cases tele.isEmpty with
    | false => exact ExRel.pure' ⟨rfl, rfl, hnty⟩
    | true =>
    simp only [cond_true]
    cases minor with
    | none => exact ExRel.pure' ⟨rfl, rfl, hnty⟩
    | some e =>
    have he := hmin e rfl
    simp only [Option.map_some, Option.bind_some, minorIH?_mapKeys hf k J c.nF i he]
    cases hmi : minorIH? k J c.nF i e with
    | none => exact ExRel.pure' ⟨rfl, rfl, hnty⟩
    | some p =>
    obtain ⟨m', idx⟩ := p
    have hidx := minorIH?_good k J c.nF i he hmi
    simp only [Option.map_some, keyMap_getElem?]
    cases hmm : members[m']? with
    | none => exact ExRel.throw_bind
    | some y =>
    obtain ⟨x, a, b⟩ := y
    have hx : x.Good P := hm _ (List.mem_of_getElem? hmm)
    simp only [Option.map_some]
    have hdom : (Expr.const (x.map f) (lps.map Level.param)).mkAppN
        (varsAt i nP ++ idx.map (Expr.mapKeys f)) =
        ((Expr.const x (lps.map Level.param)).mkAppN (varsAt i nP ++ idx)).mapKeys f := by
      simp [Expr.mapKeys_mkAppN, Expr.mapKeys]
    rw [hdom, replacePiDomAt_mapKeys]
    cases hr : replacePiDomAt (nP + i) nty
        ((Expr.const x (lps.map Level.param)).mkAppN (varsAt i nP ++ idx)) with
    | none => exact ExRel.throw_bind
    | some nty'' =>
      refine ExRel.pure' ⟨rfl, rfl, replacePiDomAt_good hnty (Expr.Good.mkAppN (g := Expr.const x _) hx ?_) hr⟩
      simp only [Expr.goodList_append]
      exact ⟨Expr.goodList_varsAt i nP, hidx⟩
  · intro s s' hs
    obtain ⟨rf, nty⟩ := s
    obtain ⟨rf', nty'⟩ := s'
    obtain ⟨h1, h2, hnty⟩ := hs
    simp only at h1 h2 hnty
    subst h1 h2
    exact ExRel.pure' ⟨rfl, hc, hnty⟩

end Ix.Kernel.Frontend.InModel
