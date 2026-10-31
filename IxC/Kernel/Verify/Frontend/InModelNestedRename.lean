module

public import IxC.Kernel.Verify.Frontend.InModelGenMutual

@[expose] public section

/-!
# The nested rung's pieces under a renaming injective on a scope (parametricity, step 3)

The nested rung's family (`Mem`, `ACtor`, `Group`, `Family`) renamed, and its
helpers under `Expr.mapKeys f`: the carriers (`carrierAt`, `auxAt`), the carrier
match (`matchCarrier`, which compares keys and terms, so under `InjOn`), the
family rewrite (`specAllP`), the readers (`readMems`, `readCtors`), the
congruence chain and the small emission helpers.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode}

/-! ## The family, renamed -/

section Maps

variable (f : md.Id → md'.Id) (P : KeyScope md)

/-- Rename a member of the auxiliary family. -/
def Mem.mapKeys (mem : Mem md) : Mem md' :=
  ⟨mem.tag, mem.real?, mem.j, mem.I.map f, mem.lv, mem.pins.map (Expr.mapKeys f), mem.nIdx,
   mem.idxBs.map (Expr.mapKeys f)⟩

/-- A good member: its carrier head, pins and index telescope. -/
def Mem.Good (mem : Mem md) : Prop :=
  mem.I.Good P ∧ Expr.GoodList P mem.pins ∧ Expr.GoodList P mem.idxBs

/-- Rename a constructor of the auxiliary family. -/
def ACtor.mapKeys (c : ACtor md) : ACtor md' :=
  ⟨c.mem, c.cname.map f, c.clv, c.nF, c.doms.map (Expr.mapKeys f), c.kinds,
   c.idx.map (Expr.mapKeys f), c.J, c.jIn⟩

/-- A good constructor: its name, field domains and index expressions. -/
def ACtor.Good (c : ACtor md) : Prop :=
  c.cname.Good P ∧ Expr.GoodList P c.doms ∧ Expr.GoodList P c.idx

/-- Rename a container group. -/
def Group.mapKeys (g : Group md) : Group md' :=
  ⟨g.tags, g.recNames.map (Key.map f), g.lv, g.pins.map (Expr.mapKeys f), g.nPI, g.large⟩

/-- A good container group. -/
def Group.Good (g : Group md) : Prop :=
  (∀ k ∈ g.recNames, k.Good P) ∧ Expr.GoodList P g.pins

/-- **Rename the family.** -/
def Family.mapKeys (fam : Family md) : Family md' :=
  ⟨fam.T.map f, fam.lps, fam.nP, fam.pbs.map (Expr.mapKeys f), fam.u, fam.r,
   fam.mems.map (Mem.mapKeys f), fam.ctors.map (ACtor.mapKeys f), fam.large, fam.elim⟩

/-- **A good family**: every key it carries is good. -/
def Family.Good (fam : Family md) : Prop :=
  fam.T.Good P ∧ Expr.GoodList P fam.pbs ∧ (∀ mem ∈ fam.mems, mem.Good P) ∧
    ∀ c ∈ fam.ctors, c.Good P

end Maps

variable {P : KeyScope md} {f : md.Id → md'.Id}

@[simp] theorem Mem.mapKeys_tag (mem : Mem md) : (mem.mapKeys f).tag = mem.tag := rfl
@[simp] theorem Mem.mapKeys_real? (mem : Mem md) : (mem.mapKeys f).real? = mem.real? := rfl
@[simp] theorem Mem.mapKeys_j (mem : Mem md) : (mem.mapKeys f).j = mem.j := rfl
@[simp] theorem Mem.mapKeys_I (mem : Mem md) : (mem.mapKeys f).I = mem.I.map f := rfl
@[simp] theorem Mem.mapKeys_lv (mem : Mem md) : (mem.mapKeys f).lv = mem.lv := rfl
@[simp] theorem Mem.mapKeys_pins (mem : Mem md) :
    (mem.mapKeys f).pins = mem.pins.map (Expr.mapKeys f) := rfl
@[simp] theorem Mem.mapKeys_nIdx (mem : Mem md) : (mem.mapKeys f).nIdx = mem.nIdx := rfl
@[simp] theorem Mem.mapKeys_idxBs (mem : Mem md) :
    (mem.mapKeys f).idxBs = mem.idxBs.map (Expr.mapKeys f) := rfl
@[simp] theorem ACtor.mapKeys_mem (c : ACtor md) : (c.mapKeys f).mem = c.mem := rfl
@[simp] theorem ACtor.mapKeys_cname (c : ACtor md) : (c.mapKeys f).cname = c.cname.map f := rfl
@[simp] theorem ACtor.mapKeys_clv (c : ACtor md) : (c.mapKeys f).clv = c.clv := rfl
@[simp] theorem ACtor.mapKeys_nF (c : ACtor md) : (c.mapKeys f).nF = c.nF := rfl
@[simp] theorem ACtor.mapKeys_doms (c : ACtor md) :
    (c.mapKeys f).doms = c.doms.map (Expr.mapKeys f) := rfl
@[simp] theorem ACtor.mapKeys_kinds (c : ACtor md) : (c.mapKeys f).kinds = c.kinds := rfl
@[simp] theorem ACtor.mapKeys_idx (c : ACtor md) :
    (c.mapKeys f).idx = c.idx.map (Expr.mapKeys f) := rfl
@[simp] theorem ACtor.mapKeys_J (c : ACtor md) : (c.mapKeys f).J = c.J := rfl
@[simp] theorem ACtor.mapKeys_jIn (c : ACtor md) : (c.mapKeys f).jIn = c.jIn := rfl
@[simp] theorem Group.mapKeys_tags (g : Group md) : (g.mapKeys f).tags = g.tags := rfl
@[simp] theorem Group.mapKeys_recNames (g : Group md) :
    (g.mapKeys f).recNames = g.recNames.map (Key.map f) := rfl
@[simp] theorem Group.mapKeys_lv (g : Group md) : (g.mapKeys f).lv = g.lv := rfl
@[simp] theorem Group.mapKeys_pins (g : Group md) :
    (g.mapKeys f).pins = g.pins.map (Expr.mapKeys f) := rfl
@[simp] theorem Group.mapKeys_nPI (g : Group md) : (g.mapKeys f).nPI = g.nPI := rfl
@[simp] theorem Group.mapKeys_large (g : Group md) : (g.mapKeys f).large = g.large := rfl
@[simp] theorem Family.mapKeys_T (fam : Family md) : (fam.mapKeys f).T = fam.T.map f := rfl
@[simp] theorem Family.mapKeys_lps (fam : Family md) : (fam.mapKeys f).lps = fam.lps := rfl
@[simp] theorem Family.mapKeys_nP (fam : Family md) : (fam.mapKeys f).nP = fam.nP := rfl
@[simp] theorem Family.mapKeys_pbs (fam : Family md) :
    (fam.mapKeys f).pbs = fam.pbs.map (Expr.mapKeys f) := rfl
@[simp] theorem Family.mapKeys_u (fam : Family md) : (fam.mapKeys f).u = fam.u := rfl
@[simp] theorem Family.mapKeys_r (fam : Family md) : (fam.mapKeys f).r = fam.r := rfl
@[simp] theorem Family.mapKeys_mems (fam : Family md) :
    (fam.mapKeys f).mems = fam.mems.map (Mem.mapKeys f) := rfl
@[simp] theorem Family.mapKeys_ctors (fam : Family md) :
    (fam.mapKeys f).ctors = fam.ctors.map (ACtor.mapKeys f) := rfl
@[simp] theorem Family.mapKeys_large (fam : Family md) : (fam.mapKeys f).large = fam.large := rfl
@[simp] theorem Family.mapKeys_elim (fam : Family md) : (fam.mapKeys f).elim = fam.elim := rfl

/-! ## Carriers -/

theorem auxAt_mapKeys (fam : Family md) (tag o : Nat) (idx : List (Expr md)) :
    auxAt (fam.mapKeys f) tag o (idx.map (Expr.mapKeys f)) = (auxAt fam tag o idx).mapKeys f := by
  simp [auxAt, Expr.mapKeys_mkAppN]

theorem auxAt_good {fam : Family md} (hfam : fam.Good P) {tag o : Nat} {idx : List (Expr md)}
    (hidx : Expr.GoodList P idx) : (auxAt fam tag o idx).Good P := by
  simp only [auxAt, Expr.good_mkAppN_iff, Expr.good_constP, good_auxName, Expr.goodList_append,
    Expr.goodList_cons, Expr.goodList_nil, good_tagCtorName, Expr.goodList_varsAt', and_true,
    true_and]
  exact ⟨hfam.1, hfam.1, hidx⟩

/-- `List.any` at two predicates agreeing on the list's elements. -/
theorem any_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.any p = l.any q
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.any_cons, h a List.mem_cons_self,
      any_congr_mem (l := as) fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The model renaming of a mimic's pins, under the renaming. -/
theorem pinRn_map (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) :
    ∀ k : Key md, k.Good P →
      ((fun x => if fam.mems.any (fun m => m.real?.isSome && m.I == x) then modelName x else x) k).map f =
        (fun x => if (fam.mapKeys f).mems.any (fun m => m.real?.isSome && m.I == x) then modelName x
          else x) (k.map f) := by
  intro k hk
  have h : ((fam.mapKeys f).mems.any fun m => m.real?.isSome && m.I == k.map f) =
      fam.mems.any fun m => m.real?.isSome && m.I == k := by
    simp only [Family.mapKeys_mems, List.any_map]
    refine any_congr_mem fun m hm => ?_
    simp only [Function.comp_apply, Mem.mapKeys_real?, Mem.mapKeys_I]
    rw [Key.map_beq hf (hfam.2.2.1 m hm).1 hk]
  simp only [h]
  split <;> rfl

theorem carrierAt_mapKeys (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) {mem : Mem md}
    (hmem : mem.Good P) (o : Nat) (idx : List (Expr md)) (model : Bool) :
    carrierAt (fam.mapKeys f) (mem.mapKeys f) o (idx.map (Expr.mapKeys f)) model =
      (carrierAt fam mem o idx model).mapKeys f := by
  unfold carrierAt
  simp only [Mem.mapKeys_real?]
  cases mem.real? with
  | some _ => cases model <;> simp [Expr.mapKeys_mkAppN]
  | none =>
    cases model
    · simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def]
    · simp only [Expr.mapKeys_mkAppN, Mem.mapKeys_I, Mem.mapKeys_lv, Mem.mapKeys_pins, Expr.mapKeys,
        List.map_append, List.map_map, if_true]
      congr 2
      refine List.map_congr_left fun p hp => ?_
      simp only [Function.comp_apply, ← Expr.mapKeys_liftLooseBVars]
      exact (mapKeys_renameConsts_good (pinRn_map hf hfam)
        (Expr.Good.liftLooseBVars (hmem.2.1 p hp) o 0)).symm

theorem carrierAt_good {fam : Family md} {mem : Mem md} (hmem : mem.Good P)
    {o : Nat} {idx : List (Expr md)} (hidx : Expr.GoodList P idx) (model : Bool) :
    (carrierAt fam mem o idx model).Good P := by
  unfold carrierAt
  cases mem.real? with
  | some _ =>
    refine Expr.good_mkAppN_iff.mpr ⟨?_, ?_⟩
    · cases model
      · exact hmem.1
      · exact hmem.1
    · simp only [Expr.goodList_append]; exact ⟨Expr.goodList_varsAt _ _, hidx⟩
  | none =>
    refine Expr.good_mkAppN_iff.mpr ⟨hmem.1, ?_⟩
    simp only [Expr.goodList_append]
    refine ⟨Expr.goodList_map fun p hp => ?_, hidx⟩
    cases model
    · exact Expr.Good.liftLooseBVars (hmem.2.1 p hp) _ _
    · refine Expr.Good.renameConsts (fun k hk => ?_) (Expr.Good.liftLooseBVars (hmem.2.1 p hp) _ _)
      split
      · exact hk
      · exact hk

/-! ## The carrier match -/

theorem matchCarrier_mapKeys (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (o : Nat)
    {e : Expr md} (he : e.Good P) :
    matchCarrier (fam.mapKeys f) o (e.mapKeys f) =
      (matchCarrier fam o e).map fun p => (p.1, p.2.map (Expr.mapKeys f)) := by
  unfold matchCarrier
  simp only [← Bool.cond_eq_ite]
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hfn := Expr.Good.getAppFn he
  have hargs := Expr.Good.getAppArgs he
  generalize e.getAppArgs = A at hargs ⊢
  generalize e.getAppFn = F at hfn ⊢
  cases F with
  | const x us =>
    simp only [Expr.mapKeys, Family.mapKeys_mems, Family.mapKeys_nP]
    refine findSome?_map_rel fun mem hmem => ?_
    have hmG := hfam.2.2.1 mem hmem
    simp only [Mem.mapKeys_I, Mem.mapKeys_lv, Mem.mapKeys_real?, Mem.mapKeys_nIdx, Mem.mapKeys_pins,
      Mem.mapKeys_tag, Key.map_beq hf hmG.1 hfn, List.length_map, ← List.map_take, ← List.map_drop]
    generalize (mem.I == x && us == mem.lv) = c
    cases c with
    | false => rfl
    | true =>
      simp only [cond_true]
      cases mem.real? with
      | some _ =>
        simp only []
        rw [← varsAt_mapKeys (f := f) o fam.nP,
          list_mapKeys_beq hf (fun _ h => hargs _ (List.mem_of_mem_take h)) (Expr.goodList_varsAt o _)]
        generalize (A.length == fam.nP + mem.nIdx && A.take fam.nP == varsAt o fam.nP) = c2
        cases c2 <;> rfl
      | none =>
        simp only [List.map_map, Function.comp_def]
        rw [show (mem.pins.map fun x => (x.mapKeys f).liftLooseBVars o 0) =
            (mem.pins.map fun x => x.liftLooseBVars o 0).map (Expr.mapKeys f) by
          simp [List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars],
          list_mapKeys_beq hf (fun _ h => hargs _ (List.mem_of_mem_take h))
            (Expr.goodList_map fun p hp => Expr.Good.liftLooseBVars (hmG.2.1 p hp) _ _)]
        generalize (A.length == mem.pins.length + mem.nIdx &&
          A.take mem.pins.length == mem.pins.map fun x => x.liftLooseBVars o 0) = c2
        cases c2 <;> rfl
  | _ => rfl

/-! ## The family rewrite -/

theorem specAllP_mapKeysN (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) :
    ∀ (n o : Nat) (e : Expr md), sizeOf e < n → e.Good P →
      specAllP (fam.mapKeys f) o (e.mapKeys f) = (specAllP fam o e).mapKeys f
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, o, e, hn, he => by
    cases hc : matchCarrier fam o e with
    | some p =>
      obtain ⟨tag, idx⟩ := p
      have hc' : matchCarrier (fam.mapKeys f) o (e.mapKeys f) = some (tag, idx.map (Expr.mapKeys f)) := by
        rw [matchCarrier_mapKeys hf hfam o he, hc]; rfl
      have hidx := matchCarrier_args hc
      rw [specAllP_some hc', specAllP_some hc, ← auxAt_mapKeys, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun y hy => ?_
      have hy' : sizeOf y < sizeOf e := sizeOf_lt_of_mem_getAppArgs (hidx y hy)
      exact specAllP_mapKeysN hf hfam n o y (by omega) (Expr.Good.getAppArgs he y (hidx y hy))
    | none =>
      have hc' : matchCarrier (fam.mapKeys f) o (e.mapKeys f) = none := by
        rw [matchCarrier_mapKeys hf hfam o he, hc]; rfl
      rw [specAllP_none hc', specAllP_none hc]
      have IH := specAllP_mapKeysN hf hfam n
      cases e with
      | app g a =>
        simp only [Expr.app.sizeOf_spec] at hn
        simp only [Expr.mapKeys, IH o g (by omega) he.1, IH o a (by omega) he.2]
      | lam d b m =>
        simp only [Expr.lam.sizeOf_spec] at hn
        simp only [Expr.mapKeys, IH o d (by omega) he.1, IH (o + 1) b (by omega) he.2]
      | forallE d b m =>
        simp only [Expr.forallE.sizeOf_spec] at hn
        simp only [Expr.mapKeys, IH o d (by omega) he.1, IH (o + 1) b (by omega) he.2]
      | letE t v b l =>
        simp only [Expr.letE.sizeOf_spec] at hn
        simp only [Expr.mapKeys, IH o t (by omega) he.1, IH o v (by omega) he.2.1,
          IH (o + 1) b (by omega) he.2.2]
      | proj s i x =>
        simp only [Expr.proj.sizeOf_spec] at hn
        simp only [Expr.mapKeys, IH o x (by omega) he.2]
      | _ => rfl

theorem specAllP_mapKeys (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (o : Nat)
    {e : Expr md} (he : e.Good P) :
    specAllP (fam.mapKeys f) o (e.mapKeys f) = (specAllP fam o e).mapKeys f :=
  specAllP_mapKeysN hf hfam _ o e (Nat.lt_succ_self _) he

theorem specAllP_goodN {fam : Family md} (hfam : fam.Good P) :
    ∀ (n o : Nat) (e : Expr md), sizeOf e < n → e.Good P → (specAllP fam o e).Good P
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, o, e, hn, he => by
    cases hc : matchCarrier fam o e with
    | some p =>
      obtain ⟨tag, idx⟩ := p
      have hidx := matchCarrier_args hc
      rw [specAllP_some hc]
      refine auxAt_good hfam (Expr.goodList_map fun y hy => ?_)
      have hy' : sizeOf y < sizeOf e := sizeOf_lt_of_mem_getAppArgs (hidx y hy)
      exact specAllP_goodN hfam n o y (by omega) (Expr.Good.getAppArgs he y (hidx y hy))
    | none =>
      rw [specAllP_none hc]
      have IH := specAllP_goodN hfam n
      cases e with
      | app g a =>
        simp only [Expr.app.sizeOf_spec] at hn
        exact ⟨IH o g (by omega) he.1, IH o a (by omega) he.2⟩
      | lam d b m =>
        simp only [Expr.lam.sizeOf_spec] at hn
        exact ⟨IH o d (by omega) he.1, IH (o + 1) b (by omega) he.2⟩
      | forallE d b m =>
        simp only [Expr.forallE.sizeOf_spec] at hn
        exact ⟨IH o d (by omega) he.1, IH (o + 1) b (by omega) he.2⟩
      | letE t v b l =>
        simp only [Expr.letE.sizeOf_spec] at hn
        exact ⟨IH o t (by omega) he.1, IH o v (by omega) he.2.1, IH (o + 1) b (by omega) he.2.2⟩
      | proj s i x =>
        simp only [Expr.proj.sizeOf_spec] at hn
        exact ⟨he.1, IH o x (by omega) he.2⟩
      | _ => exact he

theorem specAllP_good {fam : Family md} (hfam : fam.Good P) (o : Nat) {e : Expr md} (he : e.Good P) :
    (specAllP fam o e).Good P :=
  specAllP_goodN hfam _ o e (Nat.lt_succ_self _) he

theorem specAll_mapKeys (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (o : Nat)
    {e : Expr md} (he : e.Good P) :
    specAll (fam.mapKeys f) o (e.mapKeys f) = (specAll fam o e).mapKeys f := by
  rw [specAll_eq, specAll_eq, specAllP_mapKeys hf hfam o he]

theorem specAll_good {fam : Family md} (hfam : fam.Good P) (o : Nat) {e : Expr md} (he : e.Good P) :
    (specAll fam o e).Good P := by
  rw [specAll_eq]; exact specAllP_good hfam o he

/-! ## Reading the family -/

theorem stripAllPis_mapKeys : ∀ e : Expr md,
    stripAllPis (e.mapKeys f) = Expr.mapTele f (stripAllPis e)
  | .forallE t b m => by
    rw [Expr.mapKeys, stripAllPis, stripAllPis, stripAllPis_mapKeys b]
    rfl
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ _
  | .lit _ | .proj _ _ _ => rfl

theorem stripAllPis_good : ∀ {e : Expr md}, e.Good P →
    Expr.BindersGood P (stripAllPis e).1 ∧ (stripAllPis e).2.Good P
  | .forallE t b m, he => by
    have ih := stripAllPis_good he.2
    rw [stripAllPis]
    refine ⟨fun x hx => ?_, ih.2⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.1
    · exact ih.1 x hx
  | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he | .lam _ _ _, he
  | .letE _ _ _ _, he | .lit _, he | .proj _ _ _, he => ⟨(fun _ h => nomatch h), he⟩

theorem optKey_map_beq (hf : InjOn f P) {o : Option (Key md)} (ho : ∀ k, o = some k → k.Good P)
    {k : Key md} (hk : k.Good P) : (o.map (Key.map f) == some (k.map f)) = (o == some k) := by
  cases o with
  | none => rfl
  | some k' =>
    simp only [Option.map_some]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Option.some.injEq, Option.some.injEq]
    exact Key.map_eq_map_iff hf (ho k' rfl) hk

/-- `==` between a renamed list's image and the renamed list, at a function that
commutes with the renaming on the list. -/
theorem list_beq_map_comm (hf : InjOn f P) {L : List (Expr md)} (hL : Expr.GoodList P L)
    {g : Expr md → Expr md} {g' : Expr md' → Expr md'}
    (hg : ∀ x ∈ L, g' (x.mapKeys f) = (g x).mapKeys f) (hgG : ∀ x ∈ L, (g x).Good P) :
    ((L.map (Expr.mapKeys f)).map g' == L.map (Expr.mapKeys f)) = (L.map g == L) := by
  rw [List.map_map, show L.map (g' ∘ Expr.mapKeys f) = (L.map g).map (Expr.mapKeys f) by
    rw [List.map_map]; exact List.map_congr_left fun x hx => hg x hx]
  exact list_mapKeys_beq hf (Expr.goodList_map hgG) hL

theorem readMems_mapKeys (hf : InjOn f P) (lps : List LevelParam) (nP : Nat)
    {types : List (IndTypeRec md)} (hty : ∀ t ∈ types, t.Good P) {motives : List (Expr md)}
    (hmot : Expr.GoodList P motives) :
    ExRel (fun ms ms' => ms' = ms.map (Mem.mapKeys f) ∧ ∀ m ∈ ms, m.Good P)
      (readMems lps nP types motives)
      (readMems lps nP (types.map (IndTypeRec.mapKeys f)) (motives.map (Expr.mapKeys f))) := by
  unfold readMems
  simp only [← Bool.cond_eq_ite, List.length_map]
  refine ExRel.bind (S := fun (ms : List (Mem md)) ms' => ms' = ms.map (Mem.mapKeys f) ∧ ∀ m ∈ ms, m.Good P)
    (ExRel.forIn_same ⟨rfl, fun _ h => nomatch h⟩ fun m s s' hm hs => ?_) fun s s' hs => ExRel.pure' hs
  obtain ⟨rfl, hsG⟩ := hs
  rw [getD_mapKeys_default, ← Expr.mapKeys_lowerBVars, stripAllPis_mapKeys]
  have hdom := Expr.Good.lowerBVars (Expr.GoodList.getD_default hmot m) m 0
  have hsp := stripAllPis_good hdom
  generalize stripAllPis (Expr.lowerBVars m 0 (motives.getD m default)) = q at hsp ⊢
  obtain ⟨bs, body⟩ := q
  simp only [Expr.mapTele]
  cases body with
  | sort u => ?_
  | _ => exact ExRel.throw'
  simp only [Expr.mapKeys, Expr.mapBinders, List.getLast?_map]
  cases hl : bs.getLast? with
  | none => exact ExRel.throw'
  | some p =>
  obtain ⟨carr, bm⟩ := p
  have hcarr : carr.Good P := hsp.1 _ (List.mem_of_getLast? hl)
  simp only [Option.map_some]
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hfn := Expr.Good.getAppFn hcarr
  have hargs := Expr.Good.getAppArgs hcarr
  generalize carr.getAppArgs = A at hargs ⊢
  generalize carr.getAppFn = F at hfn ⊢
  have hmemN : ∀ k, (types.map fun x => x.cv.name)[m]? = some k → k.Good P := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hk)
    exact (hty t ht).1.1
  have hidxBs : (piBinders (List.take (bs.length - 1) (bs.map fun x => (x.1.mapKeys f, x.2)))) =
      (piBinders (List.take (bs.length - 1) bs)).map (Expr.mapKeys f) := by
    simp [piBinders, ← List.map_take, List.map_map, Function.comp_def]
  have hidxG : Expr.GoodList P (piBinders (List.take (bs.length - 1) bs)) :=
    Expr.goodList_piBinders (Expr.BindersGood.take hsp.1 _)
  have hnames : ∀ k ∈ types.map (fun x => x.cv.name), k.Good P := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
    exact (hty t ht).1.1
  cases F with
  | const I us =>
    simp only [Expr.mapKeys, List.length_map, List.getElem?_map]
    refine ExRel.ite Iff.rfl (fun hmr => ?_) (fun hmr => ?_)
    · simp only [getD_map_of_lt hmr default default, IndTypeRec.mapKeys_nIdx]
      refine ExRel.cond ?c1 (fun _ => ?_) (fun _ => ExRel.throw_bind)
      case c1 =>
        cases ht : types[m]? with
        | none => rfl
        | some t =>
          have htG := hty t (List.mem_of_getElem? ht)
          simp only [Option.map_some]
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Option.some.injEq, Option.some.injEq]
          exact (Key.map_eq_map_iff hf htG.1.1 hfn).symm
      refine ExRel.cond ?c2 (fun _ => ?_) (fun _ => ExRel.throw_bind)
      case c2 =>
        rw [show (varsAt (bs.length - 1) nP ++ varsAt 0 (bs.length - 1) : List (Expr md')) =
            (varsAt (bs.length - 1) nP ++ varsAt 0 (bs.length - 1) : List (Expr md)).map
              (Expr.mapKeys f) by simp,
          list_mapKeys_beq hf hargs (by simp)]
      refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw_bind)
      refine ExRel.pure' ⟨?_, fun x hx => ?_⟩
      · simp [Mem.mapKeys, piBinders, ← List.map_take, List.map_map, Function.comp_def]
      · rcases List.mem_append.mp hx with hx | hx
        · exact hsG x hx
        · rw [List.mem_singleton.mp hx]
          exact ⟨hfn, (fun _ h => nomatch h), hidxG⟩
    · refine ExRel.cond ?c0 (fun _ => ExRel.throw_bind) (fun _ => ?_)
      case c0 =>
        rw [List.map_map, show ((fun x => x.cv.name) ∘ IndTypeRec.mapKeys f) =
          (Key.map f ∘ fun (x : IndTypeRec md) => x.cv.name) from rfl, ← List.map_map,
          contains_map_ren hf hnames hfn]
      have hdropG : Expr.GoodList P (A.drop (A.length - (bs.length - 1))) :=
        fun x hx => hargs x (List.mem_of_mem_drop hx)
      have htakeG : Expr.GoodList P (A.take (A.length - (bs.length - 1))) :=
        fun x hx => hargs x (List.mem_of_mem_take hx)
      refine ExRel.cond ?c3 (fun _ => ?_) (fun _ => ExRel.throw_bind)
      case c3 =>
        rw [← List.map_drop, ← varsAt_mapKeys (f := f) 0 (bs.length - 1),
          list_mapKeys_beq hf hdropG (Expr.goodList_varsAt _ _)]
      refine ExRel.cond ?c4 (fun _ => ?_) (fun _ => ExRel.throw_bind)
      case c4 =>
        rw [← List.map_take, List.map_map, List.map_map]
        exact (list_beq_map_comm hf htakeG
          (fun x _ => by simp [Expr.mapKeys_lowerBVars, Expr.mapKeys_liftLooseBVars])
          (fun x hx => Expr.Good.liftLooseBVars (Expr.Good.lowerBVars (htakeG x hx) _ _) _ _)).symm
      refine ExRel.cond ?c5 (fun _ => ExRel.throw_bind) (fun _ => ?_)
      case c5 => simp only [Bool.and_false, ← List.map_take, List.any_map]; rfl
      refine ExRel.pure' ⟨?_, fun x hx => ?_⟩
      · simp [Mem.mapKeys, piBinders, ← List.map_take, List.map_map, Function.comp_def]
      · rcases List.mem_append.mp hx with hx | hx
        · exact hsG x hx
        · rw [List.mem_singleton.mp hx]
          exact ⟨hfn, Expr.goodList_map fun x hx => Expr.Good.lowerBVars (htakeG x hx) _ _, hidxG⟩
  | _ => exact ExRel.throw'

theorem ExRel.of_map {ε α β : Type} {g : α → β} {G : α → Prop} {x : Except ε α} {x' : Except ε β}
    (h : x' = x.map g) (hG : ∀ a, x = .ok a → G a) : ExRel (fun a b => b = g a ∧ G a) x x' := by
  subst h; cases x
  · trivial
  · exact ⟨rfl, hG _ rfl⟩

theorem memberNames_map (fam : Family md) :
    (fam.mapKeys f).mems.filterMap (fun m => bif m.real?.isSome then some m.I else none) =
      (fam.mems.filterMap fun m => bif m.real?.isSome then some m.I else none).map (Key.map f) := by
  simp only [Family.mapKeys_mems]
  induction fam.mems with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.filterMap_cons, Mem.mapKeys_real?, Mem.mapKeys_I]
    cases m.real? with
    | none => simp only [Option.isSome_none, cond_false]; exact ih
    | some _ => simp only [Option.isSome_some, cond_true, List.map_cons, ih]

theorem readCtors_mapKeys (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (M : Nat)
    {minors : List (Expr md)} (hmin : Expr.GoodList P minors)
    {nFOf : Key md → Nat → Except String Nat} {nFOf' : Key md' → Nat → Except String Nat}
    (hnF : ∀ k, k.Good P → ∀ mem, ExRel Eq (nFOf k mem) (nFOf' (k.map f) mem)) :
    ExRel (fun cs cs' => cs' = cs.map (ACtor.mapKeys f) ∧ ∀ c ∈ cs, c.Good P)
      (readCtors fam M minors nFOf) (readCtors (fam.mapKeys f) M (minors.map (Expr.mapKeys f)) nFOf') := by
  unfold readCtors
  simp only [← Bool.cond_eq_ite, List.length_map, Family.mapKeys_mems, List.map_map]
  have hmN : ∀ k ∈ fam.mems.filterMap (fun m => bif m.real?.isSome then some m.I else none), k.Good P := by
    intro k hk
    obtain ⟨m, hm, hmk⟩ := List.mem_filterMap.mp hk
    cases h : m.real?.isSome
    · rw [h] at hmk; exact nomatch hmk
    · rw [h] at hmk; cases hmk; exact (hfam.2.2.1 m hm).1
  refine ExRel.bind (S := fun (s : List (ACtor md) × List Nat) s' =>
      s'.1 = s.1.map (ACtor.mapKeys f) ∧ s'.2 = s.2 ∧ ∀ c ∈ s.1, c.Good P)
    (ExRel.forIn_same ⟨rfl, rfl, (fun _ h => nomatch h)⟩ fun J s s' hJ hs => ?_)
    fun s s' hs => ExRel.pure' ⟨hs.1, hs.2.2⟩
  obtain ⟨out, pm⟩ := s
  obtain ⟨out', pm'⟩ := s'
  obtain ⟨h1, h2, hsG⟩ := hs
  simp only at h1 h2 hsG
  subst h1 h2
  rw [getD_mapKeys_default, stripAllPis_mapKeys]
  have hsp := stripAllPis_good (Expr.GoodList.getD_default hmin J)
  generalize stripAllPis (minors.getD J default) = q at hsp ⊢
  obtain ⟨bs, body⟩ := q
  simp only [Expr.mapTele, Expr.mapBinders, List.length_map]
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hfn := Expr.Good.getAppFn hsp.2
  have hargs := Expr.Good.getAppArgs hsp.2
  generalize body.getAppArgs = A at hargs ⊢
  generalize body.getAppFn = F at hfn ⊢
  cases F with
  | bvar mv => ?_
  | _ => exact ExRel.throw'
  simp only [Expr.mapKeys]
  refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw_bind)
  simp only [List.getLast?_map]
  cases hl : A.getLast? with
  | none => exact ExRel.throw'
  | some capp =>
  have hcapp := hargs _ (List.mem_of_getLast? hl)
  simp only [Option.map_some, ← Expr.mapKeys_getAppFn]
  have hcfn := Expr.Good.getAppFn hcapp
  generalize capp.getAppFn = C at hcfn ⊢
  cases C with
  | const cname clv => ?_
  | _ => exact ExRel.throw'
  simp only [Expr.mapKeys]
  refine ExRel.bind (S := Eq) (hnF cname hcfn _) fun nF nF' hnF' => ?_
  subst hnF'
  refine ExRel.ite Iff.rfl (fun _ => ?_) (fun _ => ExRel.throw_bind)
  refine ExRel.bind (S := ListRel fun a b => b = a.mapKeys f ∧ a.Good P)
    (ExRel.mapM_same fun i _ => ?_) fun doms doms' hd => ?_
  · have hgd : ((bs.map fun x => (x.1.mapKeys f, x.2)).getD i default).1 =
        (bs.getD i default).1.mapKeys f := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases bs[i]? <;> rfl
    rw [hgd, ← Expr.mapKeys_lowerBVars, betaHeadE_mapKeys]
    exact ExRel.of_map rfl fun a ha =>
      betaHeadE_good (Expr.Good.lowerBVars (Expr.BindersGood.getD_fst hsp.1 i) _ _) ha
  obtain ⟨rfl, hdG⟩ := forall₂_map_eq hd
  have hdG' : Expr.GoodList P doms := hdG
  have hk : ∀ i, Option.map (fun x => x.1)
      (matchCarrier (fam.mapKeys f) i ((doms.map (Expr.mapKeys f)).getD i default)) =
      Option.map (fun x => x.1) (matchCarrier fam i (doms.getD i default)) := by
    intro i
    rw [getD_mapKeys_default, matchCarrier_mapKeys hf hfam i (Expr.GoodList.getD_default hdG' i),
      Option.map_map]
    rfl
  have hm1 : ∀ i, mentionsAny ((fam.mapKeys f).mems.filterMap
        (fun m => bif m.real?.isSome then some m.I else none)) ((doms.map (Expr.mapKeys f)).getD i default) =
      mentionsAny (fam.mems.filterMap (fun m => bif m.real?.isSome then some m.I else none))
        (doms.getD i default) := by
    intro i
    rw [memberNames_map, getD_mapKeys_default, mentionsAny_mapKeys hf hmN (Expr.GoodList.getD_default hdG' i)]
  have hm2 : ∀ i, mentionsAny ((fam.mapKeys f).mems.filterMap
        (fun m => bif m.real?.isSome then some m.I else none))
        (specAll (fam.mapKeys f) i ((doms.map (Expr.mapKeys f)).getD i default)) =
      mentionsAny (fam.mems.filterMap (fun m => bif m.real?.isSome then some m.I else none))
        (specAll fam i (doms.getD i default)) := by
    intro i
    rw [memberNames_map, getD_mapKeys_default, specAll_mapKeys hf hfam i (Expr.GoodList.getD_default hdG' i),
      mentionsAny_mapKeys hf hmN (specAll_good hfam i (Expr.GoodList.getD_default hdG' i))]
  simp only [← Family.mapKeys_mems, hk, hm1, hm2]
  refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw_bind)
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_same trivial fun i _ _ _ _ => ?_)
    fun _ _ _ => ?_
  · exact ExRel.cond rfl (fun _ => ExRel.throw_bind) (fun _ => ExRel.pure' trivial)
  refine ExRel.pure' ⟨?_, rfl, fun x hx => ?_⟩
  · simp [ACtor.mapKeys, ← List.map_take, List.map_map, Function.comp_def]
  · rcases List.mem_append.mp hx with hx | hx
    · exact hsG x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨hcfn, hdG', Expr.goodList_map fun e he =>
        Expr.Good.lowerBVars (Expr.Good.lowerBVars (hargs e (List.mem_of_mem_take he)) _ _) _ _⟩

/-! ## Emission helpers and the congruence chain -/

@[simp] theorem mkEq_mapKeys (ℓ : Level) (α a b : Expr md) :
    (mkEq ℓ α a b).mapKeys f = mkEq ℓ (α.mapKeys f) (a.mapKeys f) (b.mapKeys f) := by
  simp [mkEq, Expr.mapKeys_mkAppN, eqName, roleKey]

@[simp] theorem mkRefl_mapKeys (ℓ : Level) (α a : Expr md) :
    (mkRefl ℓ α a).mapKeys f = mkRefl ℓ (α.mapKeys f) (a.mapKeys f) := by
  simp [mkRefl, Expr.mapKeys_mkAppN, eqReflName, roleKey]

@[simp] theorem mkEqRec_mapKeys (ℓm ℓα : Level) (α a motive refl b h : Expr md) :
    (mkEqRec ℓm ℓα α a motive refl b h).mapKeys f =
      mkEqRec ℓm ℓα (α.mapKeys f) (a.mapKeys f) (motive.mapKeys f) (refl.mapKeys f) (b.mapKeys f)
        (h.mapKeys f) := by
  simp [mkEqRec, Expr.mapKeys_mkAppN, eqRecName, roleKey]

@[simp] theorem liftAll_mapKeys (n : Nat) (es : List (Expr md)) :
    (liftAll n es).map (Expr.mapKeys f) = liftAll n (es.map (Expr.mapKeys f)) := by
  simp [liftAll, List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars]

/-- A congruence chain's moved positions, renamed. -/
def movedMap (f : md.Id → md'.Id) (moved : List (Nat × Expr md × Expr md × Level)) :
    List (Nat × Expr md' × Expr md' × Level) :=
  moved.map fun x => (x.1, x.2.1.mapKeys f, x.2.2.1.mapKeys f, x.2.2.2)

theorem movedMap_drop_any (moved : List (Nat × Expr md × Expr md × Level)) (k i : Nat) :
    ((movedMap f moved).drop k).any (fun x => x.1 == i) = (moved.drop k).any (fun x => x.1 == i) := by
  simp [movedMap, ← List.map_drop, List.any_map, Function.comp_def]

theorem mid_map (moved : List (Nat × Expr md × Expr md × Level)) (ls rs : List (Expr md)) (k : Nat) :
    (List.range ls.length).map (fun i =>
        if ((movedMap f moved).drop k).any (fun x => x.1 == i) = true then
          (rs.map (Expr.mapKeys f)).getD i default
        else (ls.map (Expr.mapKeys f)).getD i default) =
      ((List.range ls.length).map (fun i =>
        if ((moved.drop k).any fun x => x.1 == i) = true then rs.getD i default
        else ls.getD i default)).map (Expr.mapKeys f) := by
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, movedMap_drop_any, getD_mapKeys_default]
  split
  · rfl
  · rfl

theorem congrChain_go_mapKeys (ℓα : Level) (α : Expr md) {F : Nat → List (Expr md) → Expr md}
    {F' : Nat → List (Expr md') → Expr md'} (hF : ∀ o l, F' o (l.map (Expr.mapKeys f)) = (F o l).mapKeys f)
    (ls rs : List (Expr md)) (moved : List (Nat × Expr md × Expr md × Level)) :
    ∀ n k, moved.length - k = n →
      congrChain.go ℓα (α.mapKeys f) F' (ls.map (Expr.mapKeys f)) (rs.map (Expr.mapKeys f))
          (movedMap f moved) k =
        (congrChain.go ℓα α F ls rs moved k).mapKeys f := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hnone : moved[k]? = none := List.getElem?_eq_none (by omega)
    have hnone' : (movedMap f moved)[k]? = none := by simp [movedMap, hnone]
    unfold congrChain.go
    split
    · rename_i h'
      split
      · simp [hF]
      · rename_i h; rw [hnone] at h; exact nomatch h
    · rename_i h; rw [hnone'] at h; exact nomatch h
  | succ n ih =>
    intro k hk
    unfold congrChain.go
    split
    · rename_i h'
      have : moved[k]? = none := by simpa [movedMap] using h'
      split
      · simp [hF]
      · rename_i h; rw [this] at h; exact nomatch h
    · rename_i pos' e' ty' ℓ' h'
      split
      · rename_i h; simp [movedMap, h] at h'
      · rename_i pos e ty ℓ h
        have hh : (movedMap f moved)[k]? = some (pos, e.mapKeys f, ty.mapKeys f, ℓ) := by
          simp [movedMap, h]
        rw [hh] at h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
        have hk1 : k < moved.length := (List.getElem?_eq_some_iff.mp h).1
        simp only [List.length_map]
        rw [ih (k + 1) (by omega), mid_map]
        simp only [mkEqRec_mapKeys, Expr.mapKeys, mkEq_mapKeys, Expr.mapKeys_liftLooseBVars,
          getD_mapKeys_default, ← liftAll_mapKeys, hF]
        rw [show (Expr.bvar 1 : Expr md') = (Expr.bvar 1 : Expr md).mapKeys f from rfl, ← List.map_set, hF]


theorem congrChain_mapKeys (ℓα : Level) (α : Expr md) {F : Nat → List (Expr md) → Expr md}
    {F' : Nat → List (Expr md') → Expr md'} (hF : ∀ o l, F' o (l.map (Expr.mapKeys f)) = (F o l).mapKeys f)
    (ls rs : List (Expr md)) (moved : List (Nat × Expr md × Expr md × Level)) :
    congrChain ℓα (α.mapKeys f) F' (ls.map (Expr.mapKeys f)) (rs.map (Expr.mapKeys f)) (movedMap f moved) =
      (congrChain ℓα α F ls rs moved).mapKeys f :=
  congrChain_go_mapKeys ℓα α hF ls rs moved _ 0 rfl

end Ix.Kernel.Frontend.InModel
