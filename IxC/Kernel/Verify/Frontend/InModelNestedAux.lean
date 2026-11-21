module

public import IxC.Kernel.Verify.Frontend.InModelNestedRename
public import IxC.Kernel.Verify.Rename.Install2
public import IxC.Kernel.Verify.Rename.Core1

@[expose] public section

/-!
# The auxiliary members' derivation under a renaming injective on a scope

`nestedAuxOk` (`Frontend/InModel/Nested.lean`) answers alike at a block and at its renaming
(`nestedAuxOk_mapKeys`): each piece compares keys and terms, so under `InjOn`, and reads the
context's blocks, which agree on the scope (`CtxAgree`). This is the nested rung's
parametricity at its auxiliary-member check (`genNested_mapKeys`).
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode} {P : KeyScope md} {f : md.Id → md'.Id}

/-! ## Entries -/

/-- Rename an auxiliary entry. -/
def AuxEntry.mapKeys (f : md.Id → md'.Id) (x : AuxEntry md) : AuxEntry md' :=
  (x.1.map f, x.2.1.map (Expr.mapKeys f), x.2.2)

/-- A good auxiliary entry: its type and parameters. -/
def AuxEntry.Good (P : KeyScope md) (x : AuxEntry md) : Prop :=
  x.1.Good P ∧ Expr.GoodList P x.2.1

/-- Good entries, where there are any. -/
def AuxGood (P : KeyScope md) (o : Option (List (AuxEntry md))) : Prop :=
  ∀ l, o = some l → ∀ y ∈ l, y.Good P

theorem auxEntryEq_mapKeys (hf : InjOn f P) {x y : AuxEntry md} (hx : x.Good P) (hy : y.Good P) :
    auxEntryEq (x.mapKeys f) (y.mapKeys f) = auxEntryEq x y := by
  obtain ⟨k, ps, us⟩ := x
  obtain ⟨k', ps', us'⟩ := y
  simp only [auxEntryEq, AuxEntry.mapKeys]
  rw [Key.map_beq hf hx.1 hy.1, list_beq_mapKeys hf hx.2 hy.2]

theorem any_auxEntryEq_mapKeys (hf : InjOn f P) {x : AuxEntry md} (hx : x.Good P) :
    ∀ {acc : List (AuxEntry md)}, (∀ y ∈ acc, y.Good P) →
      (acc.map (AuxEntry.mapKeys f)).any (auxEntryEq (x.mapKeys f)) = acc.any (auxEntryEq x)
  | [], _ => rfl
  | y :: ys, h => by
    simp only [List.map_cons, List.any_cons]
    rw [auxEntryEq_mapKeys hf hx (h y List.mem_cons_self),
      any_auxEntryEq_mapKeys hf hx (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem contains_map_key (hf : InjOn f P) {k : Key md} (hk : k.Good P) :
    ∀ {ns : List (Key md)}, (∀ n ∈ ns, n.Good P) →
      (ns.map (Key.map f)).contains (k.map f) = ns.contains k
  | [], _ => rfl
  | n :: ns, h => by
    simp only [List.map_cons, List.contains_cons]
    rw [Key.map_beq hf hk (h n List.mem_cons_self),
      contains_map_key hf hk (fun m hm => h m (List.mem_cons_of_mem _ hm))]

/-! ## Adding a block's members -/

theorem addAuxMembers_mapKeys (hf : InjOn f P) {ps : List (Expr md)} {us : List Level}
    (hps : Expr.GoodList P ps) :
    ∀ {ts : List (IndTypeRec md)} {acc : List (AuxEntry md)}, (∀ t ∈ ts, t.Good P) →
      (∀ y ∈ acc, y.Good P) →
      addAuxMembers (ps.map (Expr.mapKeys f)) us (ts.map (IndTypeRec.mapKeys f))
          (acc.map (AuxEntry.mapKeys f)) =
        (addAuxMembers ps us ts acc).map (AuxEntry.mapKeys f) ∧
      ∀ y ∈ addAuxMembers ps us ts acc, y.Good P
  | [], acc, _, hacc => ⟨rfl, hacc⟩
  | t :: ts, acc, hts, hacc => by
    have ht := hts t List.mem_cons_self
    have hts' : ∀ t' ∈ ts, t'.Good P := fun t' h => hts t' (List.mem_cons_of_mem _ h)
    have hx : AuxEntry.Good P (t.cv.name, ps, us) := ⟨ht.1.1, hps⟩
    have hent : (((t.mapKeys f).cv.name, ps.map (Expr.mapKeys f), us) : AuxEntry md') =
        AuxEntry.mapKeys f (t.cv.name, ps, us) := rfl
    simp only [List.map_cons, addAuxMembers]
    rw [hent, any_auxEntryEq_mapKeys hf hx hacc]
    cases hany : acc.any (auxEntryEq (t.cv.name, ps, us)) with
    | true =>
      simp only [↓reduceIte]
      exact addAuxMembers_mapKeys hf hps hts' hacc
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hacc' : ∀ y ∈ acc ++ [(t.cv.name, ps, us)], y.Good P := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hacc y hy
        · rw [List.mem_singleton.mp hy]; exact hx
      have h2 := addAuxMembers_mapKeys hf (us := us) (ts := ts) (acc := acc ++ [(t.cv.name, ps, us)])
        hps hts' hacc'
      rw [List.map_append] at h2
      exact h2

/-! ## The nested occurrence of a spine -/

theorem nestedOcc?_good {ctx : Ctx md} {ctx' : Ctx md'} (hctx : CtxAgree f P ctx ctx')
    {ns : List (Key md)} {e : Expr md} (he : e.Good P)
    {q : List Level × List (Expr md) × BlockRec md} (h : nestedOcc? ctx ns e = some q) :
    Expr.GoodList P q.2.1 ∧ q.2.2.Good P := by
  unfold nestedOcc? at h
  have hfn := Expr.Good.getAppFn he
  have hargs := Expr.Good.getAppArgs he
  generalize e.getAppFn = g at h hfn
  cases g with
  | const c us =>
    have hc : c.Good P := hfn
    try simp only at h
    revert h
    cases ns.contains c with
    | true => intro h; simp at h
    | false =>
      intro h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      revert h
      cases hb : ctx.blocks c with
      | none => intro h; simp at h
      | some cb =>
        intro h
        try simp only at h
        revert h
        cases cb.types.find? (fun x => x.cv.name == c) with
        | none => intro h; simp at h
        | some t =>
          intro h
          try simp only at h
          split at h
          · obtain rfl := Option.some.inj h
            exact ⟨hargs.take _, hctx.blocksGood c hc cb hb⟩
          · exact nomatch h
  | _ => simp at h

theorem nestedOcc?_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P)
    {e : Expr md} (he : e.Good P) :
    nestedOcc? ctx' (ns.map (Key.map f)) (e.mapKeys f) =
      (nestedOcc? ctx ns e).map
        (fun q => (q.1, q.2.1.map (Expr.mapKeys f), q.2.2.mapKeys f)) := by
  unfold nestedOcc?
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hfn := Expr.Good.getAppFn he
  have hargs := Expr.Good.getAppArgs he
  revert hfn
  cases e.getAppFn with
  | const c us =>
    intro hc
    simp only [Expr.mapKeys]
    rw [contains_map_key hf hc hns]
    cases hmem : ns.contains c with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hctx.blocks c hc]
      cases hb : ctx.blocks c with
      | none => rfl
      | some cb =>
        have hcb := hctx.blocksGood c hc cb hb
        simp only [Option.map_some, BlockRec.mapKeys_types]
        rw [find?_map_congr (p := fun x : IndTypeRec md => x.cv.name == c) fun t ht => by
          simp only [IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name]
          exact Key.map_beq hf (hcb.1 t ht).1.1 hc]
        cases ht : cb.types.find? (fun x => x.cv.name == c) with
        | none => rfl
        | some t =>
          simp only [Option.map_some, IndTypeRec.mapKeys_nP, List.length_map]
          rw [← List.map_take, List.any_map]
          have hany : (List.take t.nP e.getAppArgs).any
              ((mentionsAny (ns.map (Key.map f))) ∘ Expr.mapKeys f) =
              (List.take t.nP e.getAppArgs).any (mentionsAny ns) :=
            any_congr_mem fun x hx => mentionsAny_mapKeys hf hns (hargs.take _ x hx)
          rw [hany]
          split <;> rfl
  | _ => intro _; rfl

/-! ## The scan -/

/-- The scan's statement at one term: the renamed scan is the renamed scan's result, and good
entries stay good. -/
def ScanRel (ctx : Ctx md) (ctx' : Ctx md') (ns : List (Key md)) (e : Expr md) : Prop :=
  ∀ (d : Nat) (acc : Option (List (AuxEntry md))), AuxGood P acc →
    nestedScan ctx' (ns.map (Key.map f)) (e.mapKeys f) d
        (acc.map (List.map (AuxEntry.mapKeys f))) =
      (nestedScan ctx ns e d acc).map (List.map (AuxEntry.mapKeys f)) ∧
    AuxGood P (nestedScan ctx ns e d acc)

theorem auxGood_some {l : List (AuxEntry md)} (h : ∀ y ∈ l, y.Good P) : AuxGood P (some l) := by
  intro l' hl
  obtain rfl := Option.some.inj hl
  exact h

theorem nestedScan_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P) :
    ∀ (e : Expr md), e.Good P → ScanRel (f := f) (P := P) ctx ctx' ns e := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro he d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc =>
      have hacc' : ∀ y ∈ acc, y.Good P := hacc acc rfl
      have hme := mentionsAny_mapKeys hf hns (e := .app g a) he
      simp only [Expr.mapKeys] at hme
      simp only [Option.map_some, Expr.mapKeys, nestedScan, hme]
      cases hm : mentionsAny ns (.app g a) with
      | false => exact ⟨rfl, auxGood_some hacc'⟩
      | true =>
        simp only [↓reduceIte]
        have hocc := nestedOcc?_mapKeys hf hctx hns (e := .app g a) he
        simp only [Expr.mapKeys] at hocc
        rw [hocc]
        cases ho : nestedOcc? ctx ns (.app g a) with
        | some q =>
          obtain ⟨us, ps, cb⟩ := q
          obtain ⟨hps, hcb⟩ := nestedOcc?_good hctx he ho
          simp only [Option.map_some]
          have hlow : (ps.map (Expr.mapKeys f)).map (Expr.lowerBVars d 0) =
              (ps.map (Expr.lowerBVars d 0)).map (Expr.mapKeys f) := by
            simp [List.map_map, Function.comp_def, Expr.mapKeys_lowerBVars]
          have hlowG : Expr.GoodList P (ps.map (Expr.lowerBVars d 0)) := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact Expr.Good.lowerBVars (hps y hy) d 0
          have hliftG : Expr.GoodList P ((ps.map (Expr.lowerBVars d 0)).map
              (Expr.liftLooseBVars d 0)) := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact Expr.Good.liftLooseBVars (hlowG y hy) d 0
          have hlift : ((ps.map (Expr.lowerBVars d 0)).map (Expr.mapKeys f)).map
              (Expr.liftLooseBVars d 0) =
              ((ps.map (Expr.lowerBVars d 0)).map (Expr.liftLooseBVars d 0)).map
                (Expr.mapKeys f) := by
            simp [List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars]
          rw [hlow, hlift, list_beq_mapKeys hf hliftG hps]
          cases hbeq : ((ps.map (Expr.lowerBVars d 0)).map (Expr.liftLooseBVars d 0) == ps) with
          | false => exact ⟨rfl, fun l h => by simp at h⟩
          | true =>
            simp only [↓reduceIte, Option.map_some, BlockRec.mapKeys_types]
            obtain ⟨heq, hgood⟩ := addAuxMembers_mapKeys hf (us := us) hlowG hcb.1 hacc'
            exact ⟨by rw [heq], auxGood_some hgood⟩
        | none =>
          simp only [Option.map_none]
          have hg := ihg he.1 d (some acc) hacc
          have hg1 : nestedScan ctx' (ns.map (Key.map f)) (g.mapKeys f) d
              (some (acc.map (AuxEntry.mapKeys f))) =
              (nestedScan ctx ns g d (some acc)).map (List.map (AuxEntry.mapKeys f)) := hg.1
          rw [hg1]
          exact iha he.2 d _ hg.2
  | lam t b m iht ihb =>
    intro he d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc =>
      have hacc' : ∀ y ∈ acc, y.Good P := hacc acc rfl
      have hme := mentionsAny_mapKeys hf hns (e := .lam t b m) he
      simp only [Expr.mapKeys] at hme
      simp only [Option.map_some, Expr.mapKeys, nestedScan, hme]
      cases hm : mentionsAny ns (.lam t b m) with
      | false => exact ⟨rfl, auxGood_some hacc'⟩
      | true =>
        simp only [↓reduceIte]
        have ht := iht he.1 d (some acc) hacc
        have ht1 : nestedScan ctx' (ns.map (Key.map f)) (t.mapKeys f) d
            (some (acc.map (AuxEntry.mapKeys f))) =
            (nestedScan ctx ns t d (some acc)).map (List.map (AuxEntry.mapKeys f)) := ht.1
        rw [ht1]
        exact ihb he.2 (d + 1) _ ht.2
  | forallE t b m iht ihb =>
    intro he d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc =>
      have hacc' : ∀ y ∈ acc, y.Good P := hacc acc rfl
      have hme := mentionsAny_mapKeys hf hns (e := .forallE t b m) he
      simp only [Expr.mapKeys] at hme
      simp only [Option.map_some, Expr.mapKeys, nestedScan, hme]
      cases hm : mentionsAny ns (.forallE t b m) with
      | false => exact ⟨rfl, auxGood_some hacc'⟩
      | true =>
        simp only [↓reduceIte]
        have ht := iht he.1 d (some acc) hacc
        have ht1 : nestedScan ctx' (ns.map (Key.map f)) (t.mapKeys f) d
            (some (acc.map (AuxEntry.mapKeys f))) =
            (nestedScan ctx ns t d (some acc)).map (List.map (AuxEntry.mapKeys f)) := ht.1
        rw [ht1]
        exact ihb he.2 (d + 1) _ ht.2
  | letE t v b m iht ihv ihb =>
    intro he d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc =>
      have hacc' : ∀ y ∈ acc, y.Good P := hacc acc rfl
      have hme := mentionsAny_mapKeys hf hns (e := .letE t v b m) he
      simp only [Expr.mapKeys] at hme
      simp only [Option.map_some, Expr.mapKeys, nestedScan, hme]
      cases hm : mentionsAny ns (.letE t v b m) with
      | false => exact ⟨rfl, auxGood_some hacc'⟩
      | true =>
        simp only [↓reduceIte]
        have ht := iht he.1 d (some acc) hacc
        have ht1 : nestedScan ctx' (ns.map (Key.map f)) (t.mapKeys f) d
            (some (acc.map (AuxEntry.mapKeys f))) =
            (nestedScan ctx ns t d (some acc)).map (List.map (AuxEntry.mapKeys f)) := ht.1
        rw [ht1]
        have hv := ihv he.2.1 d _ ht.2
        rw [hv.1]
        exact ihb he.2.2 (d + 1) _ hv.2
  | proj s i x ihx =>
    intro he d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc =>
      have hacc' : ∀ y ∈ acc, y.Good P := hacc acc rfl
      have hme := mentionsAny_mapKeys hf hns (e := .proj s i x) he
      simp only [Expr.mapKeys] at hme
      simp only [Option.map_some, Expr.mapKeys, nestedScan, hme]
      cases hm : mentionsAny ns (.proj s i x) with
      | false => exact ⟨rfl, auxGood_some hacc'⟩
      | true =>
        simp only [↓reduceIte]
        exact ihx he.2 d (some acc) hacc
  | bvar _ | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro _ d acc hacc
    cases acc with
    | none => exact ⟨rfl, fun l h => by simp [nestedScan] at h⟩
    | some acc => exact ⟨rfl, auxGood_some (hacc acc rfl)⟩

theorem nestedScanAll_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P) :
    ∀ {bodies : List (Expr md)}, Expr.GoodList P bodies →
      ∀ {acc : Option (List (AuxEntry md))}, AuxGood P acc →
      nestedScanAll ctx' (ns.map (Key.map f)) (bodies.map (Expr.mapKeys f))
          (acc.map (List.map (AuxEntry.mapKeys f))) =
        (nestedScanAll ctx ns bodies acc).map (List.map (AuxEntry.mapKeys f)) ∧
      AuxGood P (nestedScanAll ctx ns bodies acc)
  | [], _, _, hacc => ⟨rfl, hacc⟩
  | body :: bodies, hb, acc, hacc => by
    simp only [List.map_cons, nestedScanAll]
    have h1 := nestedScan_mapKeys hf hctx hns body (hb body List.mem_cons_self) 0 acc hacc
    rw [h1.1]
    exact nestedScanAll_mapKeys hf hctx hns (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h1.2

/-! ## An auxiliary member's constructors -/

theorem auxCtorBody_mapKeys (hf : InjOn f P) {cb : BlockRec md} (hcb : cb.Good P)
    {t : IndTypeRec md} {ps : List (Expr md)} (hps : Expr.GoodList P ps) {us : List Level}
    {cn : Key md} (hcn : cn.Good P) :
    auxCtorBody (cb.mapKeys f) (t.mapKeys f) (ps.map (Expr.mapKeys f)) us (cn.map f) =
      (auxCtorBody cb t ps us cn).map (Expr.mapKeys f) ∧
    ∀ body, auxCtorBody cb t ps us cn = some body → body.Good P := by
  unfold auxCtorBody
  simp only [BlockRec.mapKeys_ctors]
  rw [find?_map_congr (p := fun x : IndCtorRec md => x.cv.name == cn) fun c hc => by
    simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
    exact Key.map_beq hf (hcb.2.1 c hc).1 hcn]
  cases hc : cb.ctors.find? (fun x => x.cv.name == cn) with
  | none => exact ⟨rfl, fun _ h => nomatch h⟩
  | some c =>
    have hcG : c.cv.type.Good P := (hcb.2.1 c (List.mem_of_find?_eq_some hc)).2
    simp only [Option.map_some, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_type,
      IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_levelParams, IndTypeRec.mapKeys_nP]
    rw [← Expr.mapKeys_instantiateLevelParams, Expr.stripPis_mapKeys]
    cases hs : (c.cv.type.instantiateLevelParams t.cv.levelParams us).stripPis t.nP with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some q =>
      obtain ⟨bs, body⟩ := q
      have hbody := (Expr.stripPis_good (Expr.Good.instantiateLevelParams hcG _ _) hs).2
      simp only [Option.map_some, Expr.mapTele]
      refine ⟨by rw [substParams_mapKeys], ?_⟩
      intro b h
      obtain rfl := Option.some.inj h
      exact substParams_good hps hbody

theorem mapM_option_mapKeys {α β : Type} {g : α → Option (Expr md)} {g' : β → Option (Expr md')}
    {h : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, g' (h x) = (g x).map (Expr.mapKeys f) ∧
        ∀ e, g x = some e → e.Good P) →
      (l.map h).mapM g' = (l.mapM g).map (List.map (Expr.mapKeys f)) ∧
      ∀ es, l.mapM g = some es → Expr.GoodList P es
  | [], _ => ⟨rfl, fun es hes => by simp at hes; subst hes; exact fun _ h => nomatch h⟩
  | x :: xs, hx => by
    obtain ⟨hgx, hgood⟩ := hx x List.mem_cons_self
    obtain ⟨ihe, ihg⟩ := mapM_option_mapKeys (g := g) (g' := g') (h := h)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.mapM_cons, hgx, ihe]
    cases hgx' : g x with
    | none => exact ⟨rfl, fun es hes => by simp at hes⟩
    | some e =>
      cases hxs : xs.mapM g with
      | none => exact ⟨by simp, fun es hes => by simp at hes⟩
      | some es =>
        refine ⟨by simp, ?_⟩
        intro es' hes'
        simp at hes'
        subst hes'
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hgood _ hgx'
        · exact ihg es hxs y hy

theorem auxCtorBodies_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {x : AuxEntry md} (hx : x.Good P) :
    auxCtorBodies ctx' (x.mapKeys f) = (auxCtorBodies ctx x).map (List.map (Expr.mapKeys f)) ∧
    ∀ bodies, auxCtorBodies ctx x = some bodies → Expr.GoodList P bodies := by
  obtain ⟨I, ps, us⟩ := x
  obtain ⟨hI, hps⟩ := hx
  unfold auxCtorBodies
  dsimp only [AuxEntry.mapKeys]
  rw [hctx.blocks I hI]
  cases hb : ctx.blocks I with
  | none => exact ⟨rfl, fun _ h => nomatch h⟩
  | some cb =>
    have hcb := hctx.blocksGood I hI cb hb
    simp only [Option.map_some, BlockRec.mapKeys_types]
    rw [find?_map_congr (p := fun x : IndTypeRec md => x.cv.name == I) fun t ht => by
      simp only [IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name]
      exact Key.map_beq hf (hcb.1 t ht).1.1 hI]
    cases ht : cb.types.find? (fun x => x.cv.name == I) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some t =>
      have htG := hcb.1 t (List.mem_of_find?_eq_some ht)
      simp only [Option.map_some, IndTypeRec.mapKeys_ctors]
      exact mapM_option_mapKeys (P := P) (f := f) (g := auxCtorBody cb t ps us)
        (g' := auxCtorBody (cb.mapKeys f) (t.mapKeys f) (ps.map (Expr.mapKeys f)) us)
        (h := Key.map f) fun cn hcn => auxCtorBody_mapKeys hf hcb hps (htG.2 cn hcn)

/-! ## The worklist and the check -/

theorem nestedWalk_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {ns : List (Key md)} (hns : ∀ n ∈ ns, n.Good P) :
    ∀ (fuel i : Nat) {acc : List (AuxEntry md)}, (∀ y ∈ acc, y.Good P) →
      nestedWalk ctx' (ns.map (Key.map f)) fuel i (acc.map (AuxEntry.mapKeys f)) =
        (nestedWalk ctx ns fuel i acc).map (List.map (AuxEntry.mapKeys f)) ∧
      AuxGood P (nestedWalk ctx ns fuel i acc)
  | 0, _, _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | fuel + 1, i, acc, hacc => by
    simp only [nestedWalk, List.getElem?_map]
    cases hi : acc[i]? with
    | none => exact ⟨rfl, auxGood_some hacc⟩
    | some x =>
      have hx : x.Good P := hacc x (List.mem_of_getElem? hi)
      simp only [Option.map_some]
      obtain ⟨hbe, hbg⟩ := auxCtorBodies_mapKeys hf hctx hx
      rw [hbe]
      cases hb : auxCtorBodies ctx x with
      | none => exact ⟨rfl, fun _ h => nomatch h⟩
      | some bodies =>
        simp only [Option.map_some]
        have hs := nestedScanAll_mapKeys hf hctx hns (hbg bodies hb) (acc := some acc)
          (auxGood_some hacc)
        simp only [Option.map_some] at hs
        rw [hs.1]
        cases hsc : nestedScanAll ctx ns bodies (some acc) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some acc' =>
          simp only [Option.map_some]
          exact nestedWalk_mapKeys hf hctx hns fuel (i + 1) (hs.2 acc' hsc)

/-- **The auxiliary-member check under a renaming**: it answers alike at a good block, its
good members and its renaming. -/
theorem nestedAuxOk_mapKeys (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') (nP : Nat) {types : List (IndTypeRec md)}
    (hty : ∀ t ∈ types, t.Good P) {ctors : List (IndCtorRec md)} (hct : ∀ c ∈ ctors, c.Good P)
    {recs : List (IndRecRec md)} (hrc : ∀ r ∈ recs, r.Good P) {mems : List (Mem md)}
    (hmem : ∀ m ∈ mems, m.Good P) :
    nestedAuxOk ctx' nP (types.map (IndTypeRec.mapKeys f)) (ctors.map (IndCtorRec.mapKeys f))
        (recs.map (IndRecRec.mapKeys f)) (mems.map (Mem.mapKeys f)) =
      nestedAuxOk ctx nP types ctors recs mems := by
  have hns : ∀ n ∈ types.map (·.cv.name) ++ ctors.map (·.cv.name) ++ recs.map (·.cv.name),
      n.Good P := by
    intro n hn
    simp only [List.mem_append, List.mem_map] at hn
    rcases hn with (⟨t, ht, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨r, hr, rfl⟩
    · exact (hty t ht).1.1
    · exact (hct c hc).1
    · exact (hrc r hr).1.1
  have hnsEq : (types.map (IndTypeRec.mapKeys f)).map (·.cv.name) ++
      (ctors.map (IndCtorRec.mapKeys f)).map (·.cv.name) ++
      (recs.map (IndRecRec.mapKeys f)).map (·.cv.name) =
      (types.map (·.cv.name) ++ ctors.map (·.cv.name) ++ recs.map (·.cv.name)).map
        (Key.map f) := by
    simp [List.map_map, Function.comp_def]
  have hauxEq : ((mems.map (Mem.mapKeys f)).filter (·.real?.isNone)).map
      (fun m => ((m.I, m.pins, m.lv) : AuxEntry md')) =
      ((mems.filter (·.real?.isNone)).map
        (fun m => ((m.I, m.pins, m.lv) : AuxEntry md))).map (AuxEntry.mapKeys f) := by
    rw [List.filter_map]
    simp [List.map_map, Function.comp_def, AuxEntry.mapKeys, Mem.mapKeys]
  have hauxG : ∀ y ∈ (mems.filter (·.real?.isNone)).map
      (fun m => ((m.I, m.pins, m.lv) : AuxEntry md)), AuxEntry.Good P y := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
    have hmG := hmem m (List.mem_filter.mp hm).1
    exact ⟨hmG.1, hmG.2.1⟩
  unfold nestedAuxOk
  simp only []
  rw [hnsEq, hauxEq]
  simp only [List.length_map]
  obtain ⟨hbe, hbg⟩ := mapM_option_mapKeys (P := P) (f := f) (l := ctors)
    (g := fun c : IndCtorRec md => (c.cv.type.stripPis nP).map (·.2))
    (g' := fun c : IndCtorRec md' => (c.cv.type.stripPis nP).map (·.2)) (h := IndCtorRec.mapKeys f)
    fun c hc => by
      have hcG := hct c hc
      refine ⟨?_, ?_⟩
      · simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
        cases c.cv.type.stripPis nP with
        | none => rfl
        | some q => obtain ⟨_, _⟩ := q; rfl
      · intro e he
        cases hs : c.cv.type.stripPis nP with
        | none => rw [hs] at he; exact nomatch he
        | some q =>
          rw [hs] at he
          obtain rfl := Option.some.inj he
          exact (Expr.stripPis_good hcG.2 hs).2
  rw [hbe]
  cases hb : ctors.mapM (fun c => (c.cv.type.stripPis nP).map (·.2)) with
  | none => rfl
  | some bodies =>
    simp only [Option.map_some]
    have hs := nestedScanAll_mapKeys hf hctx hns (hbg bodies hb) (acc := some [])
      (auxGood_some fun _ h => nomatch h)
    simp only [Option.map_some, List.map_nil] at hs
    rw [hs.1]
    cases hsc : nestedScanAll ctx _ bodies (some []) with
    | none => rfl
    | some acc =>
      simp only [Option.map_some]
      have hw := nestedWalk_mapKeys hf hctx hns ((mems.filter (·.real?.isNone)).length + 1) 0
        (hs.2 acc hsc)
      rw [hw.1]
      cases hwk : nestedWalk ctx _ ((mems.filter (·.real?.isNone)).length + 1) 0 acc with
      | none => rfl
      | some derived =>
        have hdG := hw.2 derived hwk
        simp only [Option.map_some, List.length_map]
        rw [List.all_map]
        congr 1
        exact all_congr_mem fun x hx => any_auxEntryEq_mapKeys hf (hdG x hx) hauxG

end Ix.Kernel.Frontend.InModel
