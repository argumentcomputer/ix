module

public import IxC.Kernel.Verify.Frontend.InModelMutualRename

@[expose] public section

/-!
# The projection rewrite's value under a renaming injective on a scope (parametricity, step 3)

`Frontend.projRecValue` builds a projection's value as the owner's recursor at a
constant motive. The mutual rung emits it for a structure-like member's
`T._model.proj_i` artifact. Under a renaming injective on a scope it commutes with
`Expr.mapKeys f` (`projRecValue_mapKeys`): it compares the value's body with a
projection term (`Expr.mapKeys_beq`) and heads with the owner's names
(`headIs`, `Key.map_beq`), all of them good.

`ORel` relates two optional results (both `none`, or both `some` and related),
the `Option` twin of `ExRel`.
-/

namespace Ix.Kernel.Frontend

open Ix.Kernel

variable {md md' : Mode} {P : KeyScope md} {f : md.Id → md'.Id}

/-! ## Related optional results -/

/-- **Two optional results agree**: both absent, or both present and related. -/
def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

namespace ORel

variable {α β γ δ : Type} {R : α → β → Prop}

theorem some' {a : α} {b : β} (h : R a b) : ORel R (some a) (some b) := h

theorem none' : ORel R (none : Option α) (none : Option β) := trivial

theorem bind {S : γ → δ → Prop} {x : Option γ} {x' : Option δ} {g : γ → Option α}
    {g' : δ → Option β} (hx : ORel S x x') (hg : ∀ a b, S a b → ORel R (g a) (g' b)) :
    ORel R (x >>= g) (x' >>= g') := by
  cases x <;> cases x' <;> first | exact hx.elim | exact trivial | exact hg _ _ hx

theorem guard {c c' : Prop} [Decidable c] [Decidable c'] (hc : c ↔ c') :
    ORel (fun (_ : Unit) (_ : Unit) => True) (_root_.guard c : Option Unit) (_root_.guard c') := by
  unfold _root_.guard
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact trivial
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact trivial

theorem map_eq {g : α → β} {x : Option α} {x' : Option β} (h : ORel (fun a b => b = g a) x x') :
    x' = x.map g := by
  cases x <;> cases x' <;> first | exact h.elim | rfl | (subst h; rfl)

theorem of_eq {g : α → β} {G : α → Prop} {x : Option α} {x' : Option β} (h : x' = x.map g)
    (hG : ∀ a, x = some a → G a) : ORel (fun a b => b = g a ∧ G a) x x' := by
  subst h; cases x
  · trivial
  · exact ⟨rfl, hG _ rfl⟩

end ORel

/-! ## The rewrite's pieces -/

/-- Rename a projection rewrite's owner. -/
def ProjRecOwner.mapKeys (f : md.Id → md'.Id) (o : ProjRecOwner md) : ProjRecOwner md' :=
  ⟨o.T.map f, o.lps, o.nP, o.ctor.map f, o.nF, o.recName.map f, o.recLps, o.recType.mapKeys f,
   o.numMotives, o.numMinors⟩

/-- A good owner: its names and its recursor's type are good. -/
def ProjRecOwner.Good (P : KeyScope md) (o : ProjRecOwner md) : Prop :=
  o.T.Good P ∧ o.ctor.Good P ∧ o.recName.Good P ∧ o.recType.Good P

theorem stripPisAll_mapKeys : ∀ e : Expr md,
    stripPisAll (e.mapKeys f) = Expr.mapTele f (stripPisAll e)
  | .forallE t b m => by
    simp only [Expr.mapKeys, stripPisAll, stripPisAll_mapKeys b, Expr.mapTele, Expr.mapBinders_cons]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ _
  | .lit _ | .proj _ _ _ => rfl

theorem stripPisAll_good : ∀ {e : Expr md}, e.Good P →
    Expr.BindersGood P (stripPisAll e).1 ∧ (stripPisAll e).2.Good P
  | .forallE t b m, he => by
    have ih := stripPisAll_good he.2
    simp only [stripPisAll]
    refine ⟨fun x hx => ?_, ih.2⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.1
    · exact ih.1 x hx
  | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he | .lam _ _ _, he
  | .letE _ _ _ _, he | .lit _, he | .proj _ _ _, he => ⟨(fun _ h => nomatch h), he⟩

theorem mkLams_mapKeys (bs : List (Expr md × BinderMeta)) (b : Expr md) :
    mkLams (Expr.mapBinders f bs) (b.mapKeys f) = (mkLams bs b).mapKeys f := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨t, m⟩ := a
    simp only [Expr.mapBinders_cons, mkLams, List.foldr_cons] at ih ⊢
    rw [ih]; rfl

theorem mkLams_good {bs : List (Expr md × BinderMeta)} {b : Expr md} (hbs : Expr.BindersGood P bs)
    (hb : b.Good P) : (mkLams bs b).Good P := by
  induction bs with
  | nil => exact hb
  | cons a as ih =>
    simp only [mkLams, List.foldr_cons] at ih ⊢
    exact ⟨hbs a List.mem_cons_self, ih fun x hx => hbs x (List.mem_cons_of_mem _ hx)⟩

theorem headIs_mapKeys (hf : InjOn f P) {T : Key md} (hT : T.Good P) {e : Expr md} (he : e.Good P) :
    headIs (T.map f) (e.mapKeys f) = headIs T e := by
  unfold headIs
  rw [← Expr.mapKeys_getAppFn]
  have hfn := Expr.Good.getAppFn he
  generalize e.getAppFn = F at hfn ⊢
  cases F with
  | const n us => exact Key.map_beq hf hfn hT
  | _ => rfl

theorem instPisOpen_mapKeys : ∀ (e : Expr md) (as : List (Expr md)),
    instPisOpen (e.mapKeys f) (as.map (Expr.mapKeys f)) = (instPisOpen e as).map (Expr.mapKeys f)
  | e, [] => rfl
  | .forallE _ body _, a :: as => by
    simp only [Expr.mapKeys, List.map_cons, instPisOpen, ← Expr.mapKeys_instantiate1Lift]
    exact instPisOpen_mapKeys _ as
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _ | .const _ _, _ :: _ | .app _ _, _ :: _
  | .lam _ _ _, _ :: _ | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem instPisOpen_good : ∀ {e : Expr md} {as : List (Expr md)} {r : Expr md}, e.Good P →
    Expr.GoodList P as → instPisOpen e as = some r → r.Good P
  | e, [], r, he, _, h => by simp only [instPisOpen, Option.some.injEq] at h; subst h; exact he
  | .forallE _ body _, a :: as, r, he, has, h => by
    simp only [instPisOpen] at h
    simp only [Expr.goodList_cons] at has
    exact instPisOpen_good (Expr.Good.instantiate1Lift he.2 has.1 0) has.2 h
  | .bvar _, _ :: _, _, _, _, h | .fvar _ _, _ :: _, _, _, _, h | .sort _, _ :: _, _, _, _, h
  | .const _ _, _ :: _, _, _, _, h | .app _ _, _ :: _, _, _, _, h | .lam _ _ _, _ :: _, _, _, _, h
  | .letE _ _ _ _, _ :: _, _, _, _, h | .lit _, _ :: _, _, _, _, h
  | .proj _ _ _, _ :: _, _, _, _, h => nomatch h

/-- **`buildBinders` at related builders**: related telescopes and terms. -/
theorem buildBinders_rel {mk : Expr md → Option (Expr md)} {mk' : Expr md' → Option (Expr md')}
    (hmk : ∀ d, d.Good P → ORel (fun r r' => r' = r.mapKeys f ∧ r.Good P) (mk d) (mk' (d.mapKeys f))) :
    ∀ (k : Nat) (e : Expr md), e.Good P →
      ORel (fun p p' => p' = (p.1.map (Expr.mapKeys f), p.2.mapKeys f) ∧ Expr.GoodList P p.1 ∧
          p.2.Good P)
        (buildBinders mk k e) (buildBinders mk' k (e.mapKeys f))
  | 0, e, he => ⟨rfl, Expr.goodList_nil, he⟩
  | k + 1, .forallE dom body m, he => by
    simp only [Expr.mapKeys, buildBinders]
    refine ORel.bind (hmk dom he.1) fun t t' ht => ?_
    obtain ⟨rfl, htG⟩ := ht
    rw [← Expr.mapKeys_instantiate1Lift]
    refine ORel.bind (buildBinders_rel hmk k _ (Expr.Good.instantiate1Lift he.2 htG 0))
      fun p p' hp => ?_
    obtain ⟨rfl, hpG, hrG⟩ := hp
    exact ⟨rfl, Expr.goodList_cons.mpr ⟨htG, hpG⟩, hrG⟩
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => trivial

theorem projRecValue_mapKeys (hP : P.All) (hf : InjOn f P) {o : ProjRecOwner md} (ho : o.Good P)
    (ℓ : Level) {ty val : Expr md} (hty : ty.Good P) (hval : val.Good P) (i : Nat) :
    ORel (fun v v' => v' = v.mapKeys f ∧ v.Good P) (projRecValue o ℓ ty val i)
      (projRecValue (o.mapKeys f) ℓ (ty.mapKeys f) (val.mapKeys f) i) := by
  unfold projRecValue
  simp only [ProjRecOwner.mapKeys, Expr.stripLams_mapKeys, Expr.stripPis_mapKeys]
  obtain ⟨hT, hC, hR, hRT⟩ := ho
  refine ORel.bind (S := fun p p' => p' = Expr.mapTele f p ∧ Expr.BindersGood P p.1 ∧ p.2.Good P)
    (ORel.of_eq rfl fun a ha => by obtain ⟨bs, b⟩ := a; exact Expr.stripLams_good hval ha)
    fun p p' hp => ?_
  obtain ⟨rfl, hlbs, hbody⟩ := hp
  obtain ⟨lbs, body⟩ := p
  simp only [Expr.mapTele]
  refine ORel.bind (ORel.guard ?_) fun _ _ _ => ?_
  · rw [show (Expr.proj (Key.map f o.T) i (Expr.bvar 0) : Expr md') =
      (Expr.proj o.T i (Expr.bvar 0)).mapKeys f from rfl,
      Expr.mapKeys_beq hf hbody (show (Expr.proj o.T i (Expr.bvar 0) : Expr md).Good P from ⟨hT, trivial⟩)]
  refine ORel.bind (ORel.guard Iff.rfl) fun _ _ _ => ?_
  refine ORel.bind (S := fun p p' => p' = Expr.mapTele f p ∧ Expr.BindersGood P p.1 ∧ p.2.Good P)
    (ORel.of_eq rfl fun a ha => by obtain ⟨bs, b⟩ := a; exact Expr.stripPis_good hty ha)
    fun p p' hp => ?_
  obtain ⟨rfl, -, hRg⟩ := hp
  obtain ⟨_, R⟩ := p
  simp only [Expr.mapTele]
  have hpar : (List.map (fun k => Expr.bvar (o.nP - k)) (List.range o.nP) : List (Expr md')) =
      (List.map (fun k => Expr.bvar (o.nP - k)) (List.range o.nP) : List (Expr md)).map
        (Expr.mapKeys f) := by
    simp [List.map_map, Function.comp_def]
  have hparG : Expr.GoodList P
      (List.map (fun k => Expr.bvar (o.nP - k)) (List.range o.nP) : List (Expr md)) :=
    InModel.Expr.goodList_map fun _ _ => trivial
  rw [hpar, ← Expr.mapKeys_instantiateLevelParams, instPisOpen_mapKeys]
  refine ORel.bind (S := fun r r' => r' = r.mapKeys f ∧ r.Good P)
    (ORel.of_eq rfl fun a ha => instPisOpen_good (Expr.Good.instantiateLevelParams hRT _ _) hparG ha)
    fun rty rty' hrty => ?_
  obtain ⟨rfl, hrtyG⟩ := hrty
  refine ORel.bind (buildBinders_rel ?hmk _ _ hrtyG) fun q q' hq => ?_
  case hmk =>
    intro d hd
    simp only [stripPisAll_mapKeys]
    obtain ⟨hbsG, hbG⟩ := stripPisAll_good hd
    generalize stripPisAll d = q at hbsG hbG ⊢
    obtain ⟨bs, b⟩ := q
    simp only [Expr.mapTele]
    cases b with
    | sort u =>
      simp only [Expr.mapKeys]
      match bs, hbsG with
      | [(d0, m)], hbsG =>
        have hd0 : d0.Good P := hbsG _ List.mem_cons_self
        simp only [Expr.mapBinders_cons, Expr.mapBinders_nil, headIs_mapKeys hf hT hd0]
        split
        · exact ⟨by simp [Expr.mapKeys, Expr.mapKeys_liftLooseBVars], hd0,
            Expr.Good.liftLooseBVars hRg _ _⟩
        · exact ⟨rfl, hd0, hP _⟩
      | [], _ => exact ⟨rfl, hP _⟩
      | x :: y :: zs, hbsG =>
        refine ⟨?_, mkLams_good hbsG (hP _)⟩
        rw [← mkLams_mapKeys]; rfl
    | _ => rcases bs with _ | ⟨x, _ | ⟨y, zs⟩⟩ <;> exact trivial
  obtain ⟨rfl, hmotG, hq2G⟩ := hq
  obtain ⟨motives, q2⟩ := q
  simp only
  refine ORel.bind (buildBinders_rel ?hmk2 _ _ hq2G) fun q q' hq => ?_
  case hmk2 =>
    intro d hd
    simp only [stripPisAll_mapKeys, Expr.mapTele, InModel.mapBinders_length,
      Expr.getAppArgs_mapKeys, List.getLast?_map]
    obtain ⟨hbsG, hbG⟩ := stripPisAll_good hd
    have hargs := Expr.Good.getAppArgs hbG
    cases hl : (stripPisAll d).2.getAppArgs.getLast? with
    | none => exact trivial
    | some major =>
      have hmaj : major.Good P := hargs _ (List.mem_of_getLast? hl)
      simp only [Option.map_some, headIs_mapKeys hf hC hmaj]
      split
      · split
        · refine ⟨?_, mkLams_good hbsG trivial⟩
          rw [← mkLams_mapKeys]; rfl
        · exact trivial
      · refine ⟨?_, mkLams_good hbsG (hP _)⟩
        rw [← mkLams_mapKeys]; rfl
  obtain ⟨rfl, hminG, hq3G⟩ := hq
  obtain ⟨minors, q3⟩ := q
  simp only
  cases q3 with
  | forallE majDom body m =>
    simp only [Expr.mapKeys]
    refine ORel.bind (ORel.guard ?_) fun _ _ _ => ?_
    · rw [headIs_mapKeys hf hT hq3G.1]
    refine ⟨?_, mkLams_good hlbs ?_⟩
    · rw [← mkLams_mapKeys]
      simp [Expr.mapKeys_mkAppN]
    · refine Expr.Good.mkAppN (g := Expr.const _ _) hR ?_
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with ((hx | hx) | hx) | rfl
      · exact hparG x hx
      · exact hmotG x hx
      · exact hminG x hx
      · trivial
  | _ => exact trivial


theorem projRecValue_map_some (hP : P.All) (hf : InjOn f P) {o : ProjRecOwner md} {ℓ : Level}
    {ty val v : Expr md} {i : Nat} (h : projRecValue o ℓ ty val i = some v) (ho : o.Good P)
    (hty : ty.Good P) (hval : val.Good P) :
    projRecValue (o.mapKeys f) ℓ (ty.mapKeys f) (val.mapKeys f) i = some (v.mapKeys f) ∧ v.Good P := by
  have hr := projRecValue_mapKeys (f := f) hP hf ho ℓ hty hval i
  rw [h] at hr
  revert hr
  cases projRecValue (o.mapKeys f) ℓ (ty.mapKeys f) (val.mapKeys f) i with
  | none => intro hr; exact hr.elim
  | some v' => intro hr; obtain ⟨rfl, hv⟩ := hr; exact ⟨rfl, hv⟩

theorem projRecValue_map_none (hP : P.All) (hf : InjOn f P) {o : ProjRecOwner md} {ℓ : Level}
    {ty val : Expr md} {i : Nat} (h : projRecValue o ℓ ty val i = none) (ho : o.Good P)
    (hty : ty.Good P) (hval : val.Good P) :
    projRecValue (o.mapKeys f) ℓ (ty.mapKeys f) (val.mapKeys f) i = none := by
  have hr := projRecValue_mapKeys (f := f) hP hf ho ℓ hty hval i
  rw [h] at hr
  revert hr
  cases projRecValue (o.mapKeys f) ℓ (ty.mapKeys f) (val.mapKeys f) i with
  | none => intro _; rfl
  | some v' => intro hr; exact hr.elim

end Ix.Kernel.Frontend
