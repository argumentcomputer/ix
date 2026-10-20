module

public import IxC.Kernel.Verify.Rename.Decl2

@[expose] public section

/-!
# Renaming and the evidence closure condition

The key walk (`constKeysGo`) and the closure walk (`refClosureGo`) at renamed
inputs: the walks' sets answer alike at renamed good keys, and the key lists
they visit in are the renamed lists (the walks follow the terms' order, so the
renaming keeps it). Hence `evidenceLocal` answers alike at renamed inputs over
related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]

/-! ## The sets of the walks -/

/-- Two subterm sets, the second the renaming of the first on good terms. -/
def SeenRel (P : KeyScope md) (f : md.Id → md'.Id) (s : Std.HashSet (Expr md))
    (s' : Std.HashSet (Expr md')) : Prop :=
  ∀ e : Expr md, e.Good P → s'.contains (e.mapKeys f) = s.contains e

theorem SeenRel.empty : SeenRel P f (∅ : Std.HashSet (Expr md)) (∅ : Std.HashSet (Expr md')) :=
  fun _ _ => by simp

theorem SeenRel.insert (hf : InjOn f P) {s : Std.HashSet (Expr md)} {s' : Std.HashSet (Expr md')}
    (h : SeenRel P f s s') {x : Expr md} (hx : x.Good P) :
    SeenRel P f (s.insert x) (s'.insert (x.mapKeys f)) := by
  intro e he
  simp only [Std.HashSet.contains_insert, Expr.mapKeys_beq hf hx he, h e he]

/-- Two key sets, the second the renaming of the first on good keys. -/
def KeySetRel (P : KeyScope md) (f : md.Id → md'.Id) (s : Std.HashSet (Key md))
    (s' : Std.HashSet (Key md')) : Prop :=
  ∀ k : Key md, k.Good P → s'.contains (k.map f) = s.contains k

theorem KeySetRel.empty : KeySetRel P f (∅ : Std.HashSet (Key md)) (∅ : Std.HashSet (Key md')) :=
  fun _ _ => by simp

theorem KeySetRel.insert (hf : InjOn f P) {s : Std.HashSet (Key md)} {s' : Std.HashSet (Key md')}
    (h : KeySetRel P f s s') {x : Key md} (hx : x.Good P) :
    KeySetRel P f (s.insert x) (s'.insert (x.map f)) := by
  intro k hk
  simp only [Std.HashSet.contains_insert, Key.map_beq hf hx hk, h k hk]

/-- Two key accumulators, the second the renaming of the first. -/
structure AccRel (P : KeyScope md) (f : md.Id → md'.Id) (acc : KeysAcc md) (acc' : KeysAcc md') :
    Prop where
  set : KeySetRel P f acc.1 acc'.1
  list : acc'.2 = acc.2.map (Key.map f)
  good : ∀ k ∈ acc.2, k.Good P

theorem AccRel.empty : AccRel P f ((∅, []) : KeysAcc md) ((∅, []) : KeysAcc md') :=
  ⟨KeySetRel.empty, rfl, fun _ h => nomatch h⟩

theorem AccRel.add (hf : InjOn f P) {acc : KeysAcc md} {acc' : KeysAcc md'} (h : AccRel P f acc acc')
    {k : Key md} (hk : k.Good P) : AccRel P f (acc.add k) (acc'.add (k.map f)) := by
  unfold KeysAcc.add
  rw [h.set k hk]
  split
  · exact h
  · refine ⟨h.set.insert hf hk, by simp [h.list], ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hk
    · exact h.good x hx

theorem AccRel.foldl (hf : InjOn f P) :
    ∀ (ks : List (Key md)) {acc : KeysAcc md} {acc' : KeysAcc md'}, (∀ k ∈ ks, k.Good P) →
      AccRel P f acc acc' →
      AccRel P f (ks.foldl KeysAcc.add acc) ((ks.map (Key.map f)).foldl KeysAcc.add acc')
  | [], _, _, _, h => h
  | k :: ks, _, _, hks, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at hks
    exact AccRel.foldl hf ks hks.2 (h.add hf hks.1)

theorem litNatKeys_map : (litNatKeys (md := md)).map (Key.map f) = litNatKeys := rfl
theorem litStrKeys_map : (litStrKeys (md := md)).map (Key.map f) = litStrKeys := rfl

theorem litNatKeys_good (hpre : P.Pre) : ∀ k ∈ (litNatKeys (md := md)), k.Good P := by
  have h1 := hpre .nat (by decide)
  have h2 := hpre .natZero (by decide)
  have h3 := hpre .natSucc (by decide)
  simp [litNatKeys, Key.Good, h1, h2, h3]

theorem litStrKeys_good (hpre : P.Pre) (hs : P.Str) : ∀ k ∈ (litStrKeys (md := md)), k.Good P := by
  have h1 := hpre .nat (by decide)
  have h2 := hpre .natZero (by decide)
  have h3 := hpre .natSucc (by decide)
  simp only [KeyScope.Str, strRoles, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at hs
  simp [litStrKeys, litNatKeys, Key.Good, h1, h2, h3, hs]

/-! ## The key walk -/

theorem constKeysGo_ren (hf : InjOn f P) (hpre : P.Pre) :
    ∀ (n : Nat) (todo : List (Expr md)) {seen : Std.HashSet (Expr md)}
      {seen' : Std.HashSet (Expr md')} {acc : KeysAcc md} {acc' : KeysAcc md'},
      Expr.GoodList P todo → SeenRel P f seen seen' → AccRel P f acc acc' →
      AccRel P f (constKeysGo n todo seen acc)
        (constKeysGo n (todo.map (Expr.mapKeys f)) seen' acc')
  | 0, _, _, _, _, _, _, _, h => h
  | _ + 1, [], _, _, _, _, _, _, h => h
  | n + 1, e :: todo, seen, seen', acc, acc', ht, hs, ha => by
    simp only [Expr.goodList_cons] at ht
    obtain ⟨he, ht⟩ := ht
    simp only [List.map_cons, constKeysGo, hs e he]
    split
    · exact constKeysGo_ren hf hpre n todo ht hs ha
    · have hs₂ := hs.insert hf he
      cases e with
      | const k us =>
        exact constKeysGo_ren hf hpre n todo ht hs₂ (ha.add hf he)
      | proj s i x =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (x :: todo) (by simp [he.2, ht]) hs₂ (ha.add hf he.1)
      | fvar i t =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (t :: todo) (by simp [he, ht]) hs₂ ha
      | app a b =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (a :: b :: todo) (by simp [he.1, he.2, ht]) hs₂ ha
      | lam t b m =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (t :: b :: todo) (by simp [he.1, he.2, ht]) hs₂ ha
      | forallE t b m =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (t :: b :: todo) (by simp [he.1, he.2, ht]) hs₂ ha
      | letE t v b l =>
        simp only [Expr.Good] at he
        exact constKeysGo_ren hf hpre n (t :: v :: b :: todo) (by simp [he.1, he.2.1, he.2.2, ht])
          hs₂ ha
      | lit l =>
        cases l with
        | natVal _ =>
          exact constKeysGo_ren hf hpre n todo ht hs₂ (AccRel.foldl hf _ (litNatKeys_good hpre) ha)
        | strVal _ =>
          exact constKeysGo_ren hf hpre n todo ht hs₂ (AccRel.foldl hf _ (litStrKeys_good hpre he) ha)
      | bvar i => exact constKeysGo_ren hf hpre n todo ht hs₂ ha
      | sort u => exact constKeysGo_ren hf hpre n todo ht hs₂ ha

theorem constKeysOf_ren (hf : InjOn f P) (hpre : P.Pre) {es : List (Expr md)} (hes : Expr.GoodList P es) :
    constKeysOf (es.map (Expr.mapKeys f)) = (constKeysOf es).map (Key.map f) := by
  unfold constKeysOf
  rw [(constKeysGo_ren hf hpre walkFuel es hes SeenRel.empty AccRel.empty).list, List.map_reverse]

theorem constKeysOf_good (hpre : P.Pre) {es : List (Expr md)} (hes : Expr.GoodList P es) :
    ∀ k ∈ constKeysOf es, k.Good P := by
  intro k hk
  unfold constKeysOf at hk
  rw [List.mem_reverse] at hk
  exact (constKeysGo_ren (f := id) (fun _ _ _ _ h => h) hpre walkFuel es hes SeenRel.empty
    AccRel.empty).good k hk

/-! ## The closure walk -/

theorem ConstantInfo.refKeys_mapKeys (c : ConstantInfo md) :
    (c.mapKeys f).refKeys = c.refKeys.map (Key.map f) := by
  cases c with
  | indInfo v caps =>
    simp only [ConstantInfo.mapKeys.eq_4, ConstantInfo.refKeys, IndCaps.mapKeys]
    cases caps.etaCtor <;> rfl
  | recInfo v a b rules =>
    simp only [ConstantInfo.mapKeys.eq_6, ConstantInfo.refKeys, List.map_map]
    rfl
  | projInfo t => rfl
  | _ => rfl

theorem ConstantInfo.refKeys_good {c : ConstantInfo md} (hc : c.Good P) :
    ∀ k ∈ c.refKeys, k.Good P := by
  cases c with
  | indInfo v caps =>
    intro k hk
    simp only [ConstantInfo.refKeys] at hk
    exact hc.2 k (Option.mem_toList.1 hk)
  | recInfo v a b rules =>
    intro k hk
    simp only [ConstantInfo.refKeys, List.mem_map] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    exact (hc.2 r hr).1
  | projInfo t =>
    intro k hk
    simp only [ConstantInfo.refKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hc.1
    · exact hc.2.1
  | _ => intro k hk; exact nomatch hk

theorem ConstantInfo.refExprs_mapKeys (c : ConstantInfo md) :
    (c.mapKeys f).refExprs = c.refExprs.map (Expr.mapKeys f) := by
  cases c with
  | recInfo v a b rules =>
    simp only [ConstantInfo.mapKeys.eq_6, ConstantInfo.refExprs, List.map_cons,
      List.map_flatMap, List.flatMap_map]
    congr 1
    congr 1
    funext r
    simp only [RecRule.mapKeys]
    cases r.fire <;> rfl
  | projInfo t =>
    simp only [ConstantInfo.mapKeys.eq_7, ConstantInfo.refExprs, ProjTable.mapKeys,
      Array.toList_map]
  | _ => rfl

theorem ConstantInfo.refExprs_good {c : ConstantInfo md} (hc : c.Good P) :
    Expr.GoodList P c.refExprs := by
  intro e he
  cases c with
  | axiomInfo v =>
    simp only [ConstantInfo.refExprs, List.mem_singleton] at he; subst he; exact hc.2
  | ctorInfo v _ _ =>
    simp only [ConstantInfo.refExprs, List.mem_singleton] at he; subst he; exact hc.2
  | indInfo v _ =>
    simp only [ConstantInfo.refExprs, List.mem_singleton] at he; subst he; exact hc.1.2
  | defnInfo v x _ =>
    simp only [ConstantInfo.refExprs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc.1.2
    · exact hc.2
  | thmInfo v x =>
    simp only [ConstantInfo.refExprs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc.1.2
    · exact hc.2
  | recInfo v _ _ rules =>
    simp only [ConstantInfo.refExprs, List.mem_cons, List.mem_flatMap] at he
    rcases he with rfl | ⟨r, hr, he⟩
    · exact hc.1.2
    · have hrg := hc.2 r hr
      rcases he with rfl | he
      · exact hrg.2.2
      · have hfire := hrg.2.1
        revert he hfire
        cases r.fire with
        | nested _ ps => intro he hfire; exact hfire e he
        | _ => intro he _; exact nomatch he
  | projInfo t =>
    simp only [ConstantInfo.refExprs, Array.mem_toList_iff] at he
    exact hc.2.2 e he

theorem refClosureGo_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') :
    ∀ (n : Nat) (todo : List (Key md)) {seen : Std.HashSet (Key md)}
      {seen' : Std.HashSet (Key md')}, (∀ k ∈ todo, k.Good P) → KeySetRel P f seen seen' →
      KeySetRel P f (refClosureGo env.find? n todo seen)
        (refClosureGo env'.find? n (todo.map (Key.map f)) seen')
  | 0, _, _, _, _, h => h
  | _ + 1, [], _, _, _, h => h
  | n + 1, k :: todo, seen, seen', ht, hs => by
    simp only [List.mem_cons, forall_eq_or_imp] at ht
    obtain ⟨hk, ht⟩ := ht
    simp only [List.map_cons, refClosureGo, hs k hk]
    split
    · exact refClosureGo_ren hE n todo ht hs
    · have hs₂ := hs.insert hE.inj hk
      rw [hE.find k hk]
      cases hc : env.find? k with
      | none => exact refClosureGo_ren hE n todo ht hs₂
      | some c =>
        have hg := hE.good k c hk hc
        simp only [Option.map_some]
        rw [ConstantInfo.refKeys_mapKeys, ConstantInfo.refExprs_mapKeys,
          constKeysOf_ren hE.inj hE.pre (ConstantInfo.refExprs_good hg), ← List.map_append,
          ← List.map_append]
        refine refClosureGo_ren hE n _ ?_ hs₂
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact ConstantInfo.refKeys_good hg x hx
        · exact constKeysOf_good hE.pre (ConstantInfo.refExprs_good hg) x hx
        · exact ht x hx

theorem evidenceDepKeys_map (c : Key md) :
    evidenceDepKeys (c.map f) = (evidenceDepKeys c).map (Key.map f) := by
  unfold evidenceDepKeys
  rw [opRole?_map]
  cases opRole? c with
  | none => rfl
  | some r => simp only [List.map_map]; rfl

theorem evidenceDepKeys_good (hall : P.All) (c : Key md) : ∀ k ∈ evidenceDepKeys c, k.Good P := by
  unfold evidenceDepKeys
  cases opRole? c with
  | none => intro k hk; exact nomatch hk
  | some r =>
    intro k hk
    simp only [List.mem_map] at hk
    obtain ⟨_, _, rfl⟩ := hk
    exact hall _

/-- **The evidence closure condition answers alike** at renamed inputs over
related environments. -/
theorem evidenceLocal_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') (hall : P.All)
    {c : Key md} (hc : c.Good P) {annVal : Expr md} (ha : annVal.Good P)
    {proofs : List (Expr md)} (hps : Expr.GoodList P proofs) :
    evidenceLocal env'.find? (c.map f) (annVal.mapKeys f) (proofs.map (Expr.mapKeys f)) =
      evidenceLocal env.find? c annVal proofs := by
  have hal : Expr.GoodList P [annVal] := by simp [ha]
  unfold evidenceLocal Expr.constKeyList
  simp only
  have hroots : constKeysOf [annVal.mapKeys f] ++ evidenceDepKeys (c.map f) =
      (constKeysOf [annVal] ++ evidenceDepKeys c).map (Key.map f) := by
    rw [List.map_append, ← evidenceDepKeys_map, ← constKeysOf_ren hE.inj hE.pre hal]; rfl
  have hrg : ∀ k ∈ constKeysOf [annVal] ++ evidenceDepKeys c, k.Good P := by
    intro k hk
    simp only [List.mem_append] at hk
    rcases hk with hk | hk
    · exact constKeysOf_good hE.pre hal k hk
    · exact evidenceDepKeys_good hall c k hk
  rw [hroots]
  have hcl := refClosureGo_ren hE walkFuel _ hrg KeySetRel.empty
  rw [List.all_map]
  apply List.all_congr_mem
  intro p hp
  have hpg : p.Good P := hps p hp
  have hsub := substConstAll_good (n := c) ha hpg
  have hsl : Expr.GoodList P [Expr.substConstAll c annVal p] := by simp [hsub]
  simp only [Function.comp_def, substConstAll_ren hE.inj hc annVal hpg]
  have hm : constKeysOf [(Expr.substConstAll c annVal p).mapKeys f] =
      (constKeysOf [Expr.substConstAll c annVal p]).map (Key.map f) :=
    constKeysOf_ren hE.inj hE.pre hsl
  rw [hm, List.all_map]
  apply List.all_congr_mem
  intro k hk
  exact hcl k (constKeysOf_good hE.pre hsl k hk)

end Ix.Kernel
