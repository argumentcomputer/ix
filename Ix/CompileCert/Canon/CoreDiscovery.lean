import Ix.CompileCert.Canon.ExpandIndex
import Ix.CompileCert.Canon.CoreBridge

/-!
Uncompiled callback-generic discovery/ownership proof, based on the checked
cb67 growth/queue proof. It reuses IndexGrow/QInv and their shared lemmas, with the
same discovery and owner conclusions and the approved fresh-family naming
clause. Arbitrary protect/ind?/group callbacks have no validity premises.
No component-level callback restoration or paired-canonicity claim is made.
-/

namespace Ix.CompileCert.Canon.ExpansionCoreProof

open Ix.Compile.Canon
open Ix (Name Expr)

theorem replaceIfNested_grow (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name) (e : Expr) (d : Nat) (st : XSt) :
    IndexGrow cx.all0 owner st (ExpansionCore.replaceIfNested cx np owner e d st).2 := by
  unfold ExpansionCore.replaceIfNested
  dsimp only [Id.run]
  repeat' (first | exact IndexGrow.refl st | exact IndexGrow.keyError st _ | split)
  all_goals
    show IndexGrow cx.all0 owner st (forIn (m := Id) (β := XSt × Option Expr) (_ : Array (Array Name)) _ _).1
    refine forIn_id_inv_array (fun (r : XSt × Option Expr) => IndexGrow cx.all0 owner st r.1) _ ?_ _ _ (IndexGrow.refl st)
    intro cls r hr
    try dsimp only
    split
    · split
      · simp only [id_bind_eq]
        repeat' split
        all_goals
          refine IndexGrow.push hr ?_ ?_ rfl ⟨_, _, rfl⟩
          all_goals
            first
            | refine (forIn_id_inv_array (fun (q : XSt × Array XCtor) => q.1.types = r.1.types ∧
                q.1.nextAuxIdx = r.1.nextAuxIdx + 1) _ ?_ _ _ ?_).1
            | refine (forIn_id_inv_array (fun (q : XSt × Array XCtor) => q.1.types = r.1.types ∧
                q.1.nextAuxIdx = r.1.nextAuxIdx + 1) _ ?_ _ _ ?_).2
            · intro x q hq; obtain ⟨cn, ct, nf⟩ := x; exact hq
            · first
              | exact ⟨rfl, rfl⟩
              | (refine array_foldl_inv (fun (q : XSt) => q.types = r.1.types ∧
                  q.nextAuxIdx = r.1.nextAuxIdx + 1) _ ?_ _ _ ⟨rfl, rfl⟩
                 intro q k hq; try dsimp only
                 repeat' (first | exact hq | split))
      · exact hr
    · exact hr

/-- **The pre-order walk of a constructor type** only appends auxiliaries owned by the walked
entry's owner, numbered in order. -/
theorem replaceAll_grow (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name) :
    ∀ (e : Expr) (d : Nat) (st : XSt), IndexGrow cx.all0 owner st (ExpansionCore.replaceAll cx np owner e d st).2 := by
  intro e
  induction e with
  | app f a h ihf iha =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.app f a h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.app f a h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihf d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner f d st1 with
        | mk f' st2 =>
          intro h1
          have h2 := iha d st2
          revert h2
          cases ExpansionCore.replaceAll cx np owner a d st2 with
          | mk a' st3 => intro h2; exact hR.trans (h1.trans h2)
  | lam n t b bi h iht ihb =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.lam n t b bi h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.lam n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases ExpansionCore.replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | forallE n t b bi h iht ihb =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.forallE n t b bi h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.forallE n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases ExpansionCore.replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | letE n t v b nd h iht ihv ihb =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.letE n t v b nd h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.letE n t v b nd h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihv d st2
          revert h2
          cases ExpansionCore.replaceAll cx np owner v d st2 with
          | mk v' st3 =>
            intro h2
            have h3 := ihb (d + 1) st3
            revert h3
            cases ExpansionCore.replaceAll cx np owner b (d + 1) st3 with
            | mk b' st4 => intro h3; exact hR.trans (h1.trans (h2.trans h3))
  | proj n i s h ihs =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.proj n i s h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.proj n i s h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihs d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner s d st1 with
        | mk s' st2 => intro h1; exact hR.trans h1
  | mdata md x h ihx =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.mdata md x h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.mdata md x h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihx d st1
        revert h1
        cases ExpansionCore.replaceAll cx np owner x d st1 with
        | mk x' st2 => intro h1; exact hR.trans h1
  | bvar i h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.bvar i h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.bvar i h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | fvar n h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.fvar n h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.fvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | mvar n h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.mvar n h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.mvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | sort u h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.sort u h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.sort u h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | const n us h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.const n us h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.const n us h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | lit l h =>
    intro d st
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.lit l h) d st
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.lit l h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR


theorem walkCtor_grow (cx : ExpansionCore.Ctx) (qi ci : Nat) (st : XSt) {mem : XMember}
    (hm : st.types[qi]? = some mem) : IndexGrow cx.all0 mem.sourceOwner st (ExpansionCore.walkCtor cx qi ci st) := by
  unfold ExpansionCore.walkCtor
  rw [hm]
  dsimp only
  split
  · exact IndexGrow.refl st
  · rename_i c hc
    obtain ⟨L, hs, hn, hp⟩ := replaceAll_grow cx (peelForalls cx.nParams c.typ #[]).fst.size
      mem.sourceOwner (peelForalls cx.nParams c.typ #[]).snd 0 st
    refine ⟨L, ?_, hn, hp⟩
    refine (skel_modify _ qi _ ?_).trans hs
    intro m; exact ⟨rfl, rfl⟩

theorem walkCtor_none (cx : ExpansionCore.Ctx) (qi ci : Nat) (st : XSt) (hm : st.types[qi]? = none) :
    ExpansionCore.walkCtor cx qi ci st = st := by
  unfold ExpansionCore.walkCtor; rw [hm]


theorem qinv_step {cx : ExpansionCore.Ctx} {M : List (Name × Name)} {qi : Nat} {st : XSt} {mem : XMember}
    (hq : QInv cx.all0 M qi st) (hm : st.types[qi]? = some mem) :
    QInv cx.all0 M (qi + 1)
      ((List.range mem.ctors.size).foldl (fun st ci => ExpansionCore.walkCtor cx qi ci st) st) := by
  obtain ⟨A, D, hs, hAD, hn, hDs, hDq, hk⟩ := hq
  -- the walk grows the queue by auxiliaries owned by `mem`'s owner
  have hg : IndexGrow cx.all0 mem.sourceOwner st
      ((List.range mem.ctors.size).foldl (fun st ci => ExpansionCore.walkCtor cx qi ci st) st) := by
    refine list_foldl_inv (fun s => IndexGrow cx.all0 mem.sourceOwner st s) _ ?_ _ _ (IndexGrow.refl st)
    intro s ci hs'
    have hqi : s.types[qi]?.map (fun m => (m.name, m.sourceOwner)) = some (mem.name, mem.sourceOwner) := by
      obtain ⟨L, hL, -, -⟩ := hs'
      rw [← skel_getElem?, hL, List.getElem?_append_left, skel_getElem?, hm]; rfl
      rw [skel_length]
      rcases Nat.lt_or_ge qi st.types.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hm; cases hm
    cases hsq : s.types[qi]? with
    | none => rw [hsq] at hqi; cases hqi
    | some m' =>
      rw [hsq] at hqi
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hqi
      have := walkCtor_grow cx qi ci s hsq
      rw [hqi.2] at this
      exact hs'.trans this
  obtain ⟨L, hL, hnL, hpL⟩ := hg
  have hqlt : qi < st.types.size := by
    rcases Nat.lt_or_ge qi st.types.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hm; cases hm
  have hsz : st.types.size = M.length + A.length := by
    rw [← skel_length, hs, List.length_append]
  refine ⟨A ++ L, D ++ List.replicate L.length qi, by rw [hL, hs, List.append_assoc], ?_, ?_, ?_, ?_, ?_⟩
  · simp [hAD]
  · rw [hnL, hn, List.length_append]; omega
  · rw [List.pairwise_append]
    refine ⟨hDs, ?_, ?_⟩
    · exact List.pairwise_replicate.2 (.inr (Nat.le_refl qi))
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      exact Nat.le_of_lt (hDq a ha)
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact Nat.lt_succ_of_lt (hDq d hd)
    · rw [List.eq_of_mem_replicate hd]; exact Nat.lt_succ_self qi
  · intro k p d hp hd
    by_cases hkA : k < A.length
    · rw [List.getElem?_append_left hkA] at hp
      rw [List.getElem?_append_left (hAD ▸ hkA)] at hd
      obtain ⟨hJ, hdk, q, hq, hpq⟩ := hk k p d hp hd
      refine ⟨hJ, hdk, q, ?_, hpq⟩
      have hdl : d < (M ++ A).length := by rw [List.length_append]; omega
      rw [← List.append_assoc, List.getElem?_append_left hdl]; exact hq
    · have hkA' : A.length ≤ k := Nat.le_of_not_lt hkA
      rw [List.getElem?_append_right hkA'] at hp
      rw [List.getElem?_append_right (hAD ▸ hkA'), List.getElem?_replicate] at hd
      have hkl : k - A.length < L.length := by
        rcases Nat.lt_or_ge (k - A.length) L.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hp; cases hp
      rw [← hAD] at hd
      simp only [hkl, ↓reduceIte, Option.some.injEq] at hd
      subst hd
      obtain ⟨ho, J, forbidden, hJ⟩ := hpL _ p hp
      have hkk : A.length + 1 + (k - A.length) = k + 1 := by omega
      refine ⟨⟨J, forbidden, by rw [hJ, hn, hkk]⟩, by omega, (mem.name, mem.sourceOwner), ?_, ho⟩
      have hql : qi < (M ++ A).length := by rw [List.length_append]; omega
      rw [← List.append_assoc, List.getElem?_append_left hql, ← hs, skel_getElem?, hm]; rfl

/-- The queue loop keeps the invariant to its end. -/
theorem walkQueue_qinv {cx : ExpansionCore.Ctx} {M : List (Name × Name)} :
    ∀ (fuel qi : Nat) (st fin : XSt), QInv cx.all0 M qi st → ExpansionCore.walkQueue cx fuel qi st = .ok fin →
      ∃ qi', QInv cx.all0 M qi' fin
  | 0, qi, st, fin, hq, h => by
    rw [ExpansionCore.walkQueue.eq_1] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases except_pure_ok h; exact ⟨qi, hq⟩
  | fuel + 1, qi, st, fin, hq, h => by
    rw [ExpansionCore.walkQueue.eq_2] at h
    split at h
    · cases h
    · split at h
      · cases except_pure_ok h; exact ⟨qi, hq⟩
      · rename_i mem hm
        exact walkQueue_qinv fuel (qi + 1) _ fin (qinv_step hq hm) h

/-- A pending key-conversion error wins even at an empty queue or a zero
fuel boundary: no partial expansion can be returned as a success. -/
theorem walkQueue_keyError (cx : ExpansionCore.Ctx) (fuel qi : Nat) (st : XSt) (e : String)
    (h : st.keyError = some e) : ExpansionCore.walkQueue cx fuel qi st = .error e := by
  cases fuel <;> simp [ExpansionCore.walkQueue, h]


theorem expand_spec {protect : Unit → List Lean.Name} {ind? : Name → Option IndView} {dedup : Dedup} {ordered : Array Name}
    {aliasToRep : Std.HashMap Name Name} {groupOf : ExpansionCore.GroupCallback}
    {keyAddr? : Option (Name → Option Address)} {x : Expanded}
    (h : ExpansionCore.expand protect ind? dedup ordered aliasToRep groupOf keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView), ordered[0]? = some first ∧ ind? first = some fi ∧
      x.nOriginals = ordered.size ∧ x.nOriginals ≤ x.types.size ∧
      (∀ (i : Nat) (n : Name), ordered[i]? = some n → ∃ m : XMember, x.types[i]? = some m ∧ m.name = n ∧ m.sourceOwner = n) ∧
      ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k : Nat) (m : XMember), x.aux[k]? = some m →
          (∃ J forbidden, m.name = auxNameOf (fi.all[0]?.getD first) J (k + 1) forbidden) ∧
          ∃ (d : Nat) (md : XMember), D[k]? = some d ∧ d < x.nOriginals + k ∧ x.types[d]? = some md ∧
            m.sourceOwner = md.sourceOwner := by
  unfold ExpansionCore.expand at h
  dsimp only at h
  split at h
  · rename_i first hfirst
    split at h
    · rename_i fi hfi
      refine ⟨first, fi, hfirst, hfi, ?_⟩
      try dsimp only at h
      obtain ⟨st0, h0, h⟩ := except_bind_ok.1 h
      obtain ⟨fin, hfin, h⟩ := except_bind_ok.1 h
      cases except_pure_ok h
      -- the members' loop
      have hst0 := forIn_except_array _ (fun pre (st : XSt) =>
          skel st = pre.map (fun n => (n, n)) ∧ st.nextAuxIdx = 1) (by
        intro pre n st s hp hs
        split at hs
        · cases except_pure_ok hs
          refine ⟨_, rfl, ?_, hp.2⟩
          unfold skel XSt.push
          rw [Array.toList_push, List.map_append, List.map_append]
          unfold skel at hp
          rw [hp.1]; rfl
        · exact absurd hs (except_throw_bind_ne _ _ _)) ordered ⟨rfl, rfl⟩ h0
      generalize hM : ordered.toList.map (fun n => (n, n)) = M at hst0
      have hq0 : QInv (fi.all[0]?.getD first) M 0 st0 := by
        refine ⟨[], [], ?_, rfl, ?_, List.Pairwise.nil, ?_, ?_⟩
        · rw [hst0.1, List.append_nil]
        · rw [hst0.2]; rfl
        · intro d hd; cases hd
        · intro k p d hp; simp at hp
      obtain ⟨qi', A, D, hs, hAD, -, hDs, -, hk⟩ := walkQueue_qinv expansionBound 0 st0 fin hq0 hfin
      have hn0 : st0.types.size = ordered.size := by
        rw [← skel_length, hst0.1, ← hM, List.length_map, Array.length_toList]
      have hfs : fin.types.size = ordered.size + A.length := by
        rw [← skel_length, hs, List.length_append, ← hM, List.length_map, Array.length_toList]
      refine ⟨hn0, by simp only; rw [hn0, hfs]; omega, ?_, D, ?_, hDs, ?_⟩
      · intro i n hi
        have hil : i < ordered.size := by
          rcases Nat.lt_or_ge i ordered.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hi; cases hi
        have : (skel fin)[i]? = some (n, n) := by
          rw [hs, List.getElem?_append_left (by rw [← hM, List.length_map, Array.length_toList]; exact hil),
            ← hM, List.getElem?_map, Array.getElem?_toList, hi]; rfl
        rw [skel_getElem?, Option.map_eq_some_iff] at this
        obtain ⟨m, hm, he⟩ := this
        simp only [Prod.mk.injEq] at he
        exact ⟨m, hm, he.1, he.2⟩
      · show D.length = (fin.types.extract st0.types.size fin.types.size).size
        rw [Array.size_extract, Nat.min_self, hfs, hn0, ← hAD]; omega
      · intro k m hm
        rw [aux_getElem?_eq _ k (by show st0.types.size ≤ fin.types.size; rw [hn0, hfs]; omega)] at hm
        have hpk : (skel fin)[st0.types.size + k]? = some (m.name, m.sourceOwner) := by
          rw [skel_getElem?, hm]; rfl
        have hML : M.length = ordered.size := by rw [← hM, List.length_map, Array.length_toList]
        rw [hs, hn0, ← hML, List.getElem?_append_right (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left] at hpk
        have hkD : k < D.length := by
          rw [← hAD]
          rcases Nat.lt_or_ge k A.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hpk; cases hpk
        obtain ⟨hJ, hdk, q, hq, hpq⟩ := hk k _ D[k] hpk (List.getElem?_eq_getElem hkD)
        refine ⟨hJ, D[k], ?_⟩
        have hq' : (skel fin)[D[k]]? = some q := by rw [hs]; exact hq
        rw [skel_getElem?, Option.map_eq_some_iff] at hq'
        obtain ⟨md, hmd, hq''⟩ := hq'
        refine ⟨md, List.getElem?_eq_getElem hkD, ?_, hmd, ?_⟩
        · show D[k] < st0.types.size + k
          rw [hn0, ← hML]; exact hdk
        · rw [← hq''] at hpq; exact hpq
    · cases h
  · cases h

/-- **Every entry of the expansion is owned by a member.** -/
theorem expand_owner {protect : Unit → List Lean.Name} {ind? : Name → Option IndView} {dedup : Dedup} {ordered : Array Name}
    {aliasToRep : Std.HashMap Name Name} {groupOf : ExpansionCore.GroupCallback}
    {keyAddr? : Option (Name → Option Address)} {x : Expanded}
    (h : ExpansionCore.expand protect ind? dedup ordered aliasToRep groupOf keyAddr? = .ok x) :
    ∀ (i : Nat) (m : XMember), x.types[i]? = some m → m.sourceOwner ∈ ordered := by
  obtain ⟨first, fi, -, -, hn0, hle, hmem, D, hD, -, hk⟩ := expand_spec h
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro m hm
    by_cases hi : i < x.nOriginals
    · rw [hn0] at hi
      obtain ⟨m', hm', -, ho⟩ := hmem i ordered[i] (Array.getElem?_eq_getElem hi)
      rw [hm] at hm'; cases hm'
      rw [ho]; exact Array.getElem_mem hi
    · have hk' : x.aux[i - x.nOriginals]? = some m := by
        rw [aux_getElem?_eq x _ hle, Nat.add_sub_cancel' (Nat.le_of_not_lt hi)]
        exact hm
      obtain ⟨-, d, md, -, hd, hmd, ho⟩ := hk _ m hk'
      rw [ho]
      exact ih d (by omega) md hmd


end Ix.CompileCert.Canon.ExpansionCoreProof
