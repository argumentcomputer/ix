import IxC.Kernel.Verify.Frontend.Prepare
import IxC.Kernel.Verify.Rename.Basic
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! # The prepared stream under a renaming

`preparePrelude` (`IxC/Kernel/Frontend/Prepare.lean`) commutes with a renaming of input
names (`Declaration.mapKeys f`) injective on the names the stream carries, when the
prelude's declarations name no input (`preparePrelude_mapKeys`).

* The front picks the stream's records by a prelude role, which a renaming fixes
  (`frontSpec_mapKeys`).
* The ground hoist computes its moves from index-level data only (`hoistTargets_from`):
  the first index declaring each name (`firstIndex_get`), read at the `Nat` operations'
  roles and at the names each record references. A renaming injective on those names
  leaves that data unchanged (`hoistTargets_mapKeys`). The guard reads only which records
  are generated (`splitsUnit_mapKeys`), and the reorder moves records by index
  (`applyHoist_mapKeys`). -/

namespace Ix.Cert.PrepareRename

open Ix.Kernel Ix.Kernel.Frontend

variable {md md' : Mode}

/-- The scope of no input id: a key good here names roles only. -/
abbrev NoInput : KeyScope md := KeyScope.ofId fun _ => False

/-! ## Keys -/

/-- A key naming no input is the only key renaming to its renaming. -/
theorem map_eq_noInput {f : md.Id → md'.Id} {k : Key md} (hk : k.Good NoInput) :
    ∀ {x : Key md}, x.map f = k.map f → x = k := by
  induction k with
  | id i => exact hk.elim
  | role r => intro x he; exact Key.map_eq_role_iff.mp he
  | aux b d ih =>
    intro x he
    cases x with
    | id _ => cases he
    | role _ => cases he
    | aux xb xd =>
      simp only [Key.map_aux, Key.aux.injEq] at he
      rw [ih (Key.good_aux.mp hk) he.1, he.2]

/-- `contains` of a renamed list at a renamed key, where the renaming identifies the key
with no other member. -/
theorem contains_map_of {g : Key md → Key md'} {l : List (Key md)} {k : Key md}
    (h : ∀ x ∈ l, g x = g k → x = k) : (l.map g).contains (g k) = l.contains k := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    exact h x hx he ▸ hx
  · exact fun hk => ⟨k, hk, rfl⟩

/-- A role key. -/
def isRoleKey : Key md → Bool
  | .role _ => true
  | _ => false

/-- `contains` of a renamed list of roles. -/
theorem contains_map_roles {f : md.Id → md'.Id} {l : List (Key md)}
    (hl : l.all isRoleKey = true) (k : Key md) :
    (l.map (Key.map f)).contains (k.map f) = l.contains k := by
  refine contains_map_of fun x hx he => ?_
  have hr := List.all_eq_true.mp hl x hx
  cases x with
  | role r =>
    have he' : (Key.role r : Key md') = k.map f := he
    exact Key.role_eq_map_iff.mp he'
  | id _ => cases hr
  | aux _ _ => cases hr

/-! ## Names -/

theorem names_mapKeys (f : md.Id → md'.Id) (d : Declaration md) :
    (d.mapKeys f).names = d.names.map (Key.map f) := by
  cases d <;> simp [Declaration.names]

theorem names_good {P : KeyScope md} {d : Declaration md} (h : d.Good P) :
    ∀ k ∈ d.names, k.Good P := by
  cases d with
  | axiomDecl cv => simp only [Declaration.names, List.mem_singleton]; rintro k rfl; exact h.1
  | defnDecl cv _ _ => simp only [Declaration.names, List.mem_singleton]; rintro k rfl; exact h.1.1
  | thmDecl cv _ => simp only [Declaration.names, List.mem_singleton]; rintro k rfl; exact h.1.1
  | opaqueDecl cv _ => simp only [Declaration.names, List.mem_singleton]; rintro k rfl; exact h.1.1
  | quotDecl _ cv => simp only [Declaration.names, List.mem_singleton]; rintro k rfl; exact h.1
  | basisDecl _ => simp [Declaration.names]
  | indDecl block _ =>
    simp only [Declaration.names, List.mem_map]
    rintro k ⟨c, hc, rfl⟩
    exact (h c hc).name

theorem preludeKey_mapKeys (f : md.Id → md'.Id) (d : Declaration md) :
    preludeKey (d.mapKeys f) = (preludeKey d).map (Key.map f) := by
  simp [preludeKey, names_mapKeys]

theorem declares_mapKeys (f : md.Id → md'.Id) {n : Option (Key md)}
    (hn : ∀ k ∈ n, k.Good NoInput) (d : Declaration md) :
    declares (n.map (Key.map f)) (d.mapKeys f) = declares n d := by
  cases n with
  | none => rfl
  | some k =>
    simp only [declares, Option.map_some, Option.any_some, names_mapKeys]
    exact contains_map_of fun x _ he => map_eq_noInput (hn k rfl) he

/-! ## The front -/

theorem pickSpec_mapKeys (f : md.Id → md'.Id) {n : Option (Key md)}
    (hn : ∀ k ∈ n, k.Good NoInput) : ∀ l : List (Declaration md),
      pickSpec (n.map (Key.map f)) (l.map (Declaration.mapKeys f)) =
        ((pickSpec n l).1.map (Declaration.mapKeys f), (pickSpec n l).2.map (Declaration.mapKeys f))
  | [] => rfl
  | d :: l => by
    simp only [List.map_cons, pickSpec, declares_mapKeys f hn d]
    by_cases h : declares n d
    · simp [h]
    · simp [h, pickSpec_mapKeys f hn l]

theorem frontSpec_mapKeys (f : md.Id → md'.Id) :
    ∀ (ps ds : List (Declaration md)), (∀ p ∈ ps, p.Good NoInput) →
      frontSpec (ps.map (Declaration.mapKeys f)) (ds.map (Declaration.mapKeys f)) =
        ((frontSpec ps ds).1.map (Declaration.mapKeys f),
          (frontSpec ps ds).2.map (Declaration.mapKeys f))
  | [], _, _ => rfl
  | p :: ps, ds, hps => by
    have hp : ∀ k ∈ preludeKey p, k.Good NoInput := fun k hk =>
      names_good (hps p List.mem_cons_self) k (List.mem_of_mem_head? hk)
    have ih := fun ds => frontSpec_mapKeys f ps ds fun q hq => hps q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, frontSpec, preludeKey_mapKeys, pickSpec_mapKeys f hp, ih]
    cases (pickSpec (preludeKey p) ds).1 <;> rfl

theorem frontSpec_rest_mem : ∀ (ps ds : List (Declaration md)) (d : Declaration md),
    d ∈ (frontSpec ps ds).2 → d ∈ ds
  | [], _, _, h => h
  | p :: ps, ds, d, h => by
    simp only [frontSpec] at h
    have h' := frontSpec_rest_mem ps _ d h
    exact (pickSpec_perm (preludeKey p) ds).subset (List.mem_append_right _ h')

theorem frontOf_mapKeys (f : md.Id → md'.Id) (ps : List (Declaration md))
    (ds : Array (Declaration md)) (hps : ∀ p ∈ ps, p.Good NoInput) :
    (frontOf #[] (ps.map (Declaration.mapKeys f)) (ds.map (Declaration.mapKeys f))).1 =
        (frontOf #[] ps ds).1.map (Declaration.mapKeys f) ∧
      (frontOf #[] (ps.map (Declaration.mapKeys f)) (ds.map (Declaration.mapKeys f))).2 =
        (frontOf #[] ps ds).2.map (Declaration.mapKeys f) := by
  obtain ⟨h₁, h₂⟩ := frontOf_toList (ps.map (Declaration.mapKeys f)) #[]
    (ds.map (Declaration.mapKeys f))
  obtain ⟨g₁, g₂⟩ := frontOf_toList ps #[] ds
  have hs := frontSpec_mapKeys f ps ds.toList hps
  simp only [Array.toList_map, hs, List.nil_append] at h₁ h₂
  simp only [List.nil_append] at g₁
  refine ⟨Array.ext' ?_, Array.ext' ?_⟩
  · rw [h₁, Array.toList_map, g₁]
  · rw [h₂, Array.toList_map, g₂]

/-! ## The ground hoist, at index level -/

/-- The first index declaring each name (the hoist's name index). -/
def firstIndex (size : Nat) (names : Nat → List (Key md)) : Std.HashMap (Key md) Nat := Id.run do
  let mut idx : Std.HashMap (Key md) Nat := {}
  for i in [0:size] do
    for n in names i do
      if !idx.contains n then idx := idx.insert n i
  return idx

/-- The hoist's moves, from its name index. -/
def hoistLook (size : Nat) (op : Nat → Option (Key md)) (idx : Std.HashMap (Key md) Nat)
    (used : Nat → Array (Key md)) : Std.HashMap Nat Nat := Id.run do
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:size] do
    let some c := op i | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      unless j > i do continue
      let mut stack : Array Nat := #[j]
      while h : stack.size > 0 do
        let k := stack[stack.size - 1]
        stack := stack.pop
        match target[k]? with
        | some t => if t ≤ i then continue
        | none => pure ()
        target := target.insert k i
        for n in used k do
          if let some m := idx[n]? then
            if m > i && m != k then stack := stack.push m
  return target

/-- The hoist's moves, from index-level data only: per operation record, the indices of
its ground; per record, the indices of the names it references. -/
def hoistFrom (size : Nat) (ops : Nat → Option (List (Option Nat)))
    (succs : Nat → List (Option Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:size] do
    let some js := ops i | continue
    for oj in js do
      let some j := oj | continue
      unless j > i do continue
      let mut stack : Array Nat := #[j]
      while h : stack.size > 0 do
        let k := stack[stack.size - 1]
        stack := stack.pop
        match target[k]? with
        | some t => if t ≤ i then continue
        | none => pure ()
        target := target.insert k i
        for om in succs k do
          if let some m := om then
            if m > i && m != k then stack := stack.push m
  return target

theorem hoistTargets_look (ds : Array (Declaration md)) :
    hoistTargets ds = hoistLook ds.size (fun i => isNatOpRecord ds[i]!)
      (firstIndex ds.size fun i => ds[i]!.names) (fun k => ds[k]!.usedConsts) := rfl

theorem hoistLook_from (size : Nat) (op : Nat → Option (Key md)) (idx : Std.HashMap (Key md) Nat)
    (used : Nat → Array (Key md)) :
    hoistLook size op idx used =
      hoistFrom size (fun i => (op i).map fun c => (natOpDeps c).map (idx[·]?))
        (fun k => (used k).toList.map (idx[·]?)) := by
  unfold hoistLook hoistFrom
  congr 1
  simp only []
  congr 1
  congr 1
  funext i s
  cases op i with
  | none => rfl
  | some c => simp only [Option.map_some, List.forIn_map, Array.forIn_toList]

/-- The name index of a stream. -/
def indexOf (ds : Array (Declaration md)) : Std.HashMap (Key md) Nat :=
  firstIndex ds.size fun i => ds[i]!.names

/-- Per operation record, the indices of its ground. -/
def opsOf (ds : Array (Declaration md)) (i : Nat) : Option (List (Option Nat)) :=
  (isNatOpRecord ds[i]!).map fun c => (natOpDeps c).map ((indexOf ds)[·]?)

/-- Per record, the indices of the names it references. -/
def succsOf (ds : Array (Declaration md)) (k : Nat) : List (Option Nat) :=
  ds[k]!.usedConsts.toList.map ((indexOf ds)[·]?)

theorem hoistTargets_from (ds : Array (Declaration md)) :
    hoistTargets ds = hoistFrom ds.size (opsOf ds) (succsOf ds) := by
  rw [hoistTargets_look, hoistLook_from]
  rfl

/-! ## The name index -/

/-- One record's names, indexed. -/
def indexStep (i : Nat) (n : Key md) (s : Std.HashMap (Key md) Nat) :
    Id (ForInStep (Std.HashMap (Key md) Nat)) :=
  if (!s.contains n) = true then pure (.yield (s.insert n i)) else pure (.yield s)

/-- One index of the stream. -/
def indexRow (names : Nat → List (Key md)) (i : Nat) (s : Std.HashMap (Key md) Nat) :
    Id (ForInStep (Std.HashMap (Key md) Nat)) := do
  let s ← forIn (names i) s (indexStep i)
  pure (.yield s)

theorem firstIndex_eq (size : Nat) (names : Nat → List (Key md)) :
    firstIndex size names = Id.run (forIn (List.range size) ∅ (indexRow names)) := by
  have h : firstIndex size names = Id.run (forIn [0:size] ∅ (indexRow names)) := rfl
  rw [h, Std.Legacy.Range.forIn_eq_forIn_range', List.range_eq_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

theorem indexStep_get (i : Nat) (k : Key md) : ∀ (ns : List (Key md)) (s : Std.HashMap (Key md) Nat),
    (Id.run (forIn ns s (indexStep i)))[k]? = s[k]?.or (if ns.contains k then some i else none)
  | [], s => by simp
  | n :: ns, s => by
    simp only [List.forIn_cons, indexStep]
    by_cases hc : s.contains n = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
      show (Id.run (forIn ns s (indexStep i)))[k]? = _
      rw [indexStep_get i k ns s]
      by_cases hk : n = k
      · subst hk
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hc
        simp [hj]
      · have hk' : k ≠ n := Ne.symm hk
        simp [hk']
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, ite_true]
      show (Id.run (forIn ns (s.insert n i) (indexStep i)))[k]? = _
      rw [indexStep_get i k ns (s.insert n i), Std.HashMap.getElem?_insert]
      by_cases hk : n = k
      · subst hk
        have hn : s[n]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          cases h : s[n]? with
          | none => rfl
          | some j => rw [h] at hc; cases hc
        simp [hn]
      · have hk' : k ≠ n := Ne.symm hk
        simp [hk', show (n == k) = false from by simpa using hk]

theorem indexRow_get (names : Nat → List (Key md)) (k : Key md) :
    ∀ (l : List Nat) (s : Std.HashMap (Key md) Nat),
      (Id.run (forIn l s (indexRow names)))[k]? =
        s[k]?.or (l.find? fun i => (names i).contains k)
  | [], s => by simp
  | i :: l, s => by
    simp only [List.forIn_cons, indexRow]
    show (Id.run (forIn l (Id.run (forIn (names i) s (indexStep i))) (indexRow names)))[k]? = _
    rw [indexRow_get names k l, indexStep_get i k (names i) s, List.find?_cons]
    cases s[k]? <;> cases (names i).contains k <;> simp

theorem firstIndex_get (size : Nat) (names : Nat → List (Key md)) (k : Key md) :
    (firstIndex size names)[k]? = (List.range size).find? fun i => (names i).contains k := by
  rw [firstIndex_eq, indexRow_get]
  simp

/-! ## A renamed stream, read by index -/

theorem default_mapKeys (f : md.Id → md'.Id) :
    (default : Declaration md).mapKeys f = (default : Declaration md') := rfl

theorem getElem!_mapKeys (f : md.Id → md'.Id) (ds : Array (Declaration md)) (k : Nat) :
    (ds.map (Declaration.mapKeys f))[k]! = (ds[k]!).mapKeys f := by
  by_cases hk : k < ds.size
  · rw [getElem!_pos _ k (by simpa using hk), getElem!_pos ds k hk]
    simp
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg ds k hk, default_mapKeys]

theorem getElem!_good {P : md.Id → Prop} {ds : Array (Declaration md)}
    (hds : ∀ d ∈ ds, d.Good P) (k : Nat) : (ds[k]!).Good P := by
  by_cases hk : k < ds.size
  · rw [getElem!_pos ds k hk]
    exact hds _ (Array.getElem_mem hk)
  · rw [getElem!_neg ds k hk]
    exact ⟨trivial, trivial⟩

/-! ## The `Nat` operations' ground -/

theorem natOpDeps_mapKeys (f : md.Id → md'.Id) (c : Key md) :
    natOpDeps (c.map f) = (natOpDeps c).map (Key.map f) := by
  cases c with
  | role r => cases r <;> rfl
  | id _ => rfl
  | aux _ _ => rfl

theorem natOpDeps_roles (c : Key md) : (natOpDeps c).all isRoleKey = true := by
  cases c with
  | role r => cases r <;> rfl
  | id _ => rfl
  | aux _ _ => rfl

theorem natNames_roles : (natDivModNames (md := md)).all isRoleKey = true ∧
    (natOpNames (md := md)).all isRoleKey = true := ⟨rfl, rfl⟩

theorem isNatOpRecord_mapKeys (f : md.Id → md'.Id) (d : Declaration md) :
    isNatOpRecord (d.mapKeys f) = (isNatOpRecord d).map (Key.map f) := by
  cases d with
  | defnDecl cv v h =>
    have h₁ : (natDivModNames (md := md')) = natDivModNames.map (Key.map f) := rfl
    have h₂ : (natOpNames (md := md')) = natOpNames.map (Key.map f) := rfl
    simp only [Declaration.mapKeys, isNatOpRecord, ConstantVal.mapKeys_name, h₁, h₂,
      contains_map_roles natNames_roles.1, contains_map_roles natNames_roles.2]
    split <;> rfl
  | _ => rfl

/-! ## The name index under a renaming -/

theorem indexOf_mapKeys {f : md.Id → md'.Id} {P : md.Id → Prop} (hf : InjOn f P)
    {ds : Array (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) {k : Key md}
    (hk : k.Good (KeyScope.ofId P)) :
    (indexOf (ds.map (Declaration.mapKeys f)))[k.map f]? = (indexOf ds)[k]? := by
  simp only [indexOf, firstIndex_get, Array.size_map, getElem!_mapKeys, names_mapKeys]
  congr 1
  funext i
  exact contains_map_of fun x hx he =>
    Key.map_inj hf (names_good (getElem!_good hds i) x hx) hk he

theorem indexOf_mapKeys_role {f : md.Id → md'.Id} (ds : Array (Declaration md)) {k : Key md}
    (hk : isRoleKey k = true) :
    (indexOf (ds.map (Declaration.mapKeys f)))[k.map f]? = (indexOf ds)[k]? := by
  simp only [indexOf, firstIndex_get, Array.size_map, getElem!_mapKeys, names_mapKeys]
  congr 1
  funext i
  refine contains_map_of fun x _ he => ?_
  cases k with
  | role r =>
    have he' : x.map f = (Key.role r : Key md') := he
    exact Key.map_eq_role_iff.mp he'
  | id _ => cases hk
  | aux _ _ => cases hk

/-! ## The names a record references, under a renaming -/

/-- The two walks over a term and its renaming: their seen sets agree on renamed good
terms, the renamed walk's names are the walk's renamed, and those are good. -/
structure Walk (f : md.Id → md'.Id) (P : KeyScope md)
    (p : Std.HashSet (Expr md) × Array (Key md)) (p' : Std.HashSet (Expr md') × Array (Key md')) :
    Prop where
  seen : ∀ e : Expr md, e.Good P → p'.1.contains (e.mapKeys f) = p.1.contains e
  acc : p'.2 = p.2.map (Key.map f)
  good : ∀ n ∈ p.2, n.Good P

theorem Walk.empty (f : md.Id → md'.Id) (P : KeyScope md) : Walk f P (∅, #[]) (∅, #[]) :=
  ⟨fun _ _ => by simp, by simp, by simp⟩

theorem Walk.insert {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) {p p'}
    (h : Walk f P p p') {e : Expr md} (he : e.Good P) :
    Walk f P (p.1.insert e, p.2) (p'.1.insert (e.mapKeys f), p'.2) := by
  refine ⟨fun x hx => ?_, h.acc, h.good⟩
  simp only [Std.HashSet.contains_insert]
  rw [Expr.mapKeys_beq hf he hx, h.seen x hx]

theorem Walk.push {f : md.Id → md'.Id} {P : KeyScope md} {s s' acc acc'}
    (h : Walk f P (s, acc) (s', acc')) {n : Key md} (hn : n.Good P) :
    Walk f P (s, acc.push n) (s', acc'.push (n.map f)) := by
  refine ⟨h.seen, ?_, ?_⟩
  · have hacc : acc' = acc.map (Key.map f) := h.acc
    rw [hacc, Array.map_push]
  · intro m hm
    rcases Array.mem_push.mp hm with hm | rfl
    · exact h.good m hm
    · exact hn

theorem walk_go {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) (e : Expr md) :
    e.Good P → ∀ {p p'}, Walk f P p p' →
      Walk f P (usedConstsGo p.1 p.2 e) (usedConstsGo p'.1 p'.2 (e.mapKeys f)) := by
  induction e with
  | bvar i =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact h.insert hf he
  | sort u =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact h.insert hf he
  | lit l =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact h.insert hf he
  | const n us =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact (h.insert hf he).push he
  | fvar i ty ih =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact ih he (h.insert hf he)
  | proj s i x ih =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · exact ih he.2 ((h.insert hf he).push he.1)
  | app a b iha ihb =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · have ha := iha he.1 (h.insert hf he)
      simp only [Expr.mapKeys] at ha ⊢
      generalize usedConstsGo _ _ a = q at ha ⊢
      generalize usedConstsGo _ _ (a.mapKeys f) = q' at ha ⊢
      exact ihb he.2 ha
  | lam ty b m iht ihb =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · have ht := iht he.1 (h.insert hf he)
      simp only [Expr.mapKeys] at ht ⊢
      generalize usedConstsGo _ _ ty = q at ht ⊢
      generalize usedConstsGo _ _ (ty.mapKeys f) = q' at ht ⊢
      exact ihb he.2 ht
  | forallE ty b m iht ihb =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · have ht := iht he.1 (h.insert hf he)
      simp only [Expr.mapKeys] at ht ⊢
      generalize usedConstsGo _ _ ty = q at ht ⊢
      generalize usedConstsGo _ _ (ty.mapKeys f) = q' at ht ⊢
      exact ihb he.2 ht
  | letE ty v b l iht ihv ihb =>
    intro he p p' h
    rw [usedConstsGo, usedConstsGo, h.seen _ he]
    split
    · exact h
    · have ht := iht he.1 (h.insert hf he)
      simp only [Expr.mapKeys] at ht ⊢
      generalize usedConstsGo _ _ ty = q at ht ⊢
      generalize usedConstsGo _ _ (ty.mapKeys f) = q' at ht ⊢
      have hv := ihv he.2.1 ht
      generalize usedConstsGo _ _ v = r at hv ⊢
      generalize usedConstsGo _ _ (v.mapKeys f) = r' at hv ⊢
      exact ihb he.2.2 hv

theorem walk_rules {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ (rules : List (RecRule md)), (∀ r ∈ rules, r.Good P) → ∀ {p p'}, Walk f P p p' →
      Walk f P (rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) p)
        ((rules.map (RecRule.mapKeys f)).foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) p')
  | [], _, _, _, h => h
  | r :: rs, hr, p, p', h => by
    simp only [List.foldl_cons, List.map_cons]
    apply walk_rules hf rs (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
    exact walk_go hf r.rhs (hr r List.mem_cons_self).2.2 h

theorem walk_block {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ (block : List (ConstantInfo md)), (∀ c ∈ block, c.Good P) → ∀ {p p'}, Walk f P p p' →
      Walk f P
        (block.foldl (fun (seen, acc) ci =>
          let (seen, acc) := usedConstsGo seen acc ci.toConstantVal.type
          match ci with
          | .recInfo _ _ _ rules =>
            rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) (seen, acc)
          | _ => (seen, acc)) p)
        ((block.map (ConstantInfo.mapKeys f)).foldl (fun (seen, acc) ci =>
          let (seen, acc) := usedConstsGo seen acc ci.toConstantVal.type
          match ci with
          | .recInfo _ _ _ rules =>
            rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) (seen, acc)
          | _ => (seen, acc)) p')
  | [], _, _, _, h => h
  | c :: cs, hcs, p, p', h => by
    simp only [List.foldl_cons, List.map_cons]
    apply walk_block hf cs (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    have hc := hcs c List.mem_cons_self
    have h₁ := walk_go hf c.toConstantVal.type hc.toConstantVal.2 h
    cases c with
    | recInfo v major pre rules => exact walk_rules hf rules hc.2 h₁
    | axiomInfo v => exact h₁
    | defnInfo v e hint => exact h₁
    | thmInfo v e => exact h₁
    | indInfo v caps => exact h₁
    | ctorInfo v nP nF => exact h₁
    | projInfo tbl => exact h₁

/-- **A renamed record references the record's names, renamed**, and those are good. -/
theorem usedConsts_mapKeys {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {d : Declaration md} (hd : d.Good P) :
    (d.mapKeys f).usedConsts = d.usedConsts.map (Key.map f) ∧ ∀ n ∈ d.usedConsts, n.Good P := by
  cases d with
  | axiomDecl cv =>
    have h := walk_go hf cv.type hd.2 (Walk.empty f P)
    exact ⟨h.acc, h.good⟩
  | defnDecl cv v hint =>
    have h := walk_go hf v hd.2 (walk_go hf cv.type hd.1.2 (Walk.empty f P))
    exact ⟨h.acc, h.good⟩
  | thmDecl cv v =>
    have h := walk_go hf v hd.2 (walk_go hf cv.type hd.1.2 (Walk.empty f P))
    exact ⟨h.acc, h.good⟩
  | opaqueDecl cv v =>
    have h := walk_go hf v hd.2 (walk_go hf cv.type hd.1.2 (Walk.empty f P))
    exact ⟨h.acc, h.good⟩
  | indDecl block nP =>
    have h := walk_block hf block hd (Walk.empty f P)
    exact ⟨h.acc, h.good⟩
  | basisDecl _ => exact ⟨by simp [Declaration.usedConsts], by simp [Declaration.usedConsts]⟩
  | quotDecl _ _ => exact ⟨by simp [Declaration.usedConsts], by simp [Declaration.usedConsts]⟩

/-! ## The hoist under a renaming -/

theorem opsOf_mapKeys (f : md.Id → md'.Id) (ds : Array (Declaration md)) (i : Nat) :
    opsOf (ds.map (Declaration.mapKeys f)) i = opsOf ds i := by
  simp only [opsOf, getElem!_mapKeys, isNatOpRecord_mapKeys]
  cases isNatOpRecord ds[i]! with
  | none => rfl
  | some c =>
    simp only [Option.map_some, natOpDeps_mapKeys, List.map_map]
    congr 1
    apply List.map_congr_left
    intro g hg
    exact indexOf_mapKeys_role ds (List.all_eq_true.mp (natOpDeps_roles c) g hg)

theorem succsOf_mapKeys {f : md.Id → md'.Id} {P : md.Id → Prop} (hf : InjOn f P)
    {ds : Array (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) (k : Nat) :
    succsOf (ds.map (Declaration.mapKeys f)) k = succsOf ds k := by
  obtain ⟨hu, hg⟩ := usedConsts_mapKeys (P := KeyScope.ofId P) hf (getElem!_good hds k)
  simp only [succsOf, getElem!_mapKeys, hu, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro n hn
  exact indexOf_mapKeys hf hds (hg n (Array.mem_toList_iff.mp hn))

/-- **The hoist's moves are the same on a renamed stream.** -/
theorem hoistTargets_mapKeys {f : md.Id → md'.Id} {P : md.Id → Prop} (hf : InjOn f P)
    {ds : Array (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) :
    hoistTargets (ds.map (Declaration.mapKeys f)) = hoistTargets ds := by
  rw [hoistTargets_from, hoistTargets_from, Array.size_map]
  have h₁ : opsOf (ds.map (Declaration.mapKeys f)) = opsOf ds := funext (opsOf_mapKeys f ds)
  have h₂ : succsOf (ds.map (Declaration.mapKeys f)) = succsOf ds :=
    funext (succsOf_mapKeys hf hds)
  rw [h₁, h₂]

theorem isGenerated_mapKeys (f : md.Id → md'.Id) (d : Declaration md) :
    (d.mapKeys f).isGenerated = d.isGenerated := by
  have h : ∀ k : Key md, (k.map f).isAux = k.isAux := fun k => by cases k <;> rfl
  simp [Declaration.isGenerated, names_mapKeys, List.all_map, Function.comp_def, h]

theorem splitsUnit_mapKeys (f : md.Id → md'.Id) (ds : Array (Declaration md))
    (target : Std.HashMap Nat Nat) :
    splitsUnit (ds.map (Declaration.mapKeys f)) target = splitsUnit ds target := by
  simp only [splitsUnit, getElem!_mapKeys, isGenerated_mapKeys]

theorem applyHoist_mapKeys (f : md.Id → md'.Id) (ds : Array (Declaration md))
    (target : Std.HashMap Nat Nat) :
    (applyHoist (ds.map (Declaration.mapKeys f)) target).1 =
      (applyHoist ds target).1.map (Declaration.mapKeys f) := by
  simp [applyHoist, getElem!_mapKeys]

/-- **The hoist commutes with a renaming injective on the stream's names.** -/
theorem hoistNatOpGround_mapKeys {f : md.Id → md'.Id} {P : md.Id → Prop} (hf : InjOn f P)
    {ds : Array (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) :
    (hoistNatOpGround (ds.map (Declaration.mapKeys f))).1 =
      (hoistNatOpGround ds).1.map (Declaration.mapKeys f) := by
  simp only [hoistNatOpGround, hoistTargets_mapKeys hf hds, splitsUnit_mapKeys]
  split
  · rfl
  · exact applyHoist_mapKeys f ds _

/-! ## The prepared stream -/

/-- **`preparePrelude` commutes with a renaming injective on the stream's names**, when the
prelude's declarations name no input and the renamed prelude is the prelude renamed. -/
theorem preparePrelude_mapKeys {f : md.Id → md'.Id} {P : md.Id → Prop} (hf : InjOn f P)
    {pre : PreludeIx md} {preA : PreludeIx md'}
    (hpre : preA.decls = pre.decls.map (Declaration.mapKeys f))
    (hpg : ∀ p ∈ pre.decls, p.Good NoInput) {ds : Array (Declaration md)}
    (hds : ∀ d ∈ ds, d.Good P) :
    preparePrelude preA (ds.map (Declaration.mapKeys f)) =
      (preparePrelude pre ds).map (Declaration.mapKeys f) := by
  rw [preparePrelude_front, preparePrelude_front, hpre, Array.toList_map]
  obtain ⟨h₁, h₂⟩ := frontOf_mapKeys f pre.decls.toList ds
    (fun p hp => hpg p (Array.mem_toList_iff.mp hp))
  have hrest : ∀ d ∈ (frontOf #[] pre.decls.toList ds).2, d.Good P := by
    intro d hd
    have hd' := Array.mem_toList_iff.mpr hd
    rw [(frontOf_toList pre.decls.toList #[] ds).2] at hd'
    exact hds d (Array.mem_toList_iff.mp (frontSpec_rest_mem _ _ d hd'))
  rw [h₁, h₂, hoistNatOpGround_mapKeys hf hrest, Array.map_append]

/--
info: 'Ix.Cert.PrepareRename.preparePrelude_mapKeys' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms preparePrelude_mapKeys

end Ix.Cert.PrepareRename
