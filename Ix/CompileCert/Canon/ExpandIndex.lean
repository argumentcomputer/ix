import Ix.CompileCert.Canon.Loop
import Ix.CompileCert.Canon.BlockMap
import Ix.Compile.Canon.Nested
import Ix.CompileCert.Canon.ComponentBridge

/-!
# M7 L1, the nested auxiliaries in discovery order (Def 2.5)

`Ix.Compile.Canon.expandSourceSpec source dedup ordered …` is the FIFO-queue construction of design document
§2.5 (Lean's `elim_nested_inductive_fn`): the queue starts with the members `ordered`, each queue
entry's constructors are walked in turn (`walkQueue`, `walkCtor`), each constructor type in
pre-order (`replaceAll`), and a new nested occurrence appends its external group's auxiliaries to
the end of the queue (`replaceIfNested`). What the theorems state about the result
(`expand_source_index_spec`), against the code as it is:

* **the members first**: the expansion's first `nOriginals = |ordered|` entries are the members, in
  the given order, each its own owner;
* **the numbering is the discovery order**: the `k`-th auxiliary (0-based) uses
  `auxNameOf` with index `k+1`; it retains `all₀._nested.<J>_<k+1>` when that
  family is available and otherwise chooses the deterministic fresh family.
  The indices count auxiliaries in the order they were appended — the order
  Lean numbers `all₀.rec_{k+1}` by;
* **breadth-first over the queue**: every auxiliary was discovered while walking an earlier queue
  entry (`d < nOriginals + k`), the discovering entries are non-decreasing along the auxiliaries
  (so auxiliaries found inside auxiliaries come after every auxiliary found from an earlier queue
  entry, §2.5's first consequence), and an auxiliary's owner is its discovering entry's owner;
* hence **every auxiliary is owned by a member** (`expand_source_owner`).

The proofs carry two facts through the construction: the skeleton of the queue (names and
owners, `skel`) only grows, by appends numbered from `nextAuxIdx` (`IndexGrow`), and constructor
rewrites (`walkCtor`) leave it unchanged.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Expr)

/-- The queue's names and owners. -/
def skel (st : XSt) : List (Name × Name) := st.types.toList.map fun m => (m.name, m.sourceOwner)

/-- The name of an auxiliary of head `J` numbered `k`. -/
abbrev auxNameOf (all0 J : Name) (k : Nat) (forbidden : List Lean.Name := []) : Name :=
  freshFamily forbidden (all0.mkStr "_nested") s!"{(namePretty J).replace "." "_"}_{k}"

/-- `st'` extends `st`'s queue by auxiliaries owned by `owner`, numbered from `st.nextAuxIdx`. -/
def IndexGrow (all0 owner : Name) (st st' : XSt) : Prop :=
  ∃ L : List (Name × Name), skel st' = skel st ++ L ∧ st'.nextAuxIdx = st.nextAuxIdx + L.length ∧
    ∀ i p, L[i]? = some p → p.2 = owner ∧ ∃ J forbidden, p.1 = auxNameOf all0 J (st.nextAuxIdx + i) forbidden

theorem IndexGrow.refl {all0 owner : Name} (st : XSt) : IndexGrow all0 owner st st :=
  ⟨[], by simp, by simp, fun i p h => by simp at h⟩

/-- Recording a key-conversion failure does not change the queue skeleton. -/
theorem IndexGrow.keyError {all0 owner : Name} (st : XSt) (err : Option String) :
    IndexGrow all0 owner st { st with keyError := err } :=
  ⟨[], by simp [skel], by simp, fun i p h => by simp at h⟩

theorem IndexGrow.trans {all0 owner : Name} {st₁ st₂ st₃ : XSt} (h₁ : IndexGrow all0 owner st₁ st₂)
    (h₂ : IndexGrow all0 owner st₂ st₃) : IndexGrow all0 owner st₁ st₃ := by
  obtain ⟨L₁, hs₁, hn₁, hp₁⟩ := h₁
  obtain ⟨L₂, hs₂, hn₂, hp₂⟩ := h₂
  refine ⟨L₁ ++ L₂, by rw [hs₂, hs₁, List.append_assoc], by rw [hn₂, hn₁, List.length_append]; omega,
    fun i p hp => ?_⟩
  by_cases hi : i < L₁.length
  · rw [List.getElem?_append_left hi] at hp
    exact hp₁ i p hp
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hp
    obtain ⟨ho, J, forbidden, hJ⟩ := hp₂ _ p hp
    refine ⟨ho, J, forbidden, ?_⟩
    rw [hJ, hn₁]
    have : st₁.nextAuxIdx + L₁.length + (i - L₁.length) = st₁.nextAuxIdx + i := by omega
    rw [this]

/-- One auxiliary appended on top of a growth. -/
theorem IndexGrow.push {all0 owner : Name} {st₀ r T : XSt} {m : XMember} (hr : IndexGrow all0 owner st₀ r)
    (hT : T.types = r.types) (hN : T.nextAuxIdx = r.nextAuxIdx + 1) (ho : m.sourceOwner = owner)
    (hn : ∃ J forbidden, m.name = auxNameOf all0 J r.nextAuxIdx forbidden) : IndexGrow all0 owner st₀ (T.push m) := by
  refine hr.trans ⟨[(m.name, m.sourceOwner)], ?_, ?_, fun i p hp => ?_⟩
  · unfold skel XSt.push
    rw [Array.toList_push, List.map_append, hT]; rfl
  · show T.nextAuxIdx = _; rw [hN]; rfl
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      obtain ⟨J, forbidden, hJ⟩ := hn
      exact ⟨ho, J, forbidden, by rw [Nat.add_zero]; exact hJ⟩
    | succ i => simp at hp

/-- A `for` loop in `Id` keeps any property every step keeps. -/
theorem forIn_id_inv {α β : Type} (P : β → Prop) (body : α → β → Id (ForInStep β))
    (hstep : ∀ x r, P r → P (body x r).value) : ∀ (l : List α) (init : β), P init →
      P (forIn (m := Id) l init body)
  | [], _, h => h
  | x :: l, init, h => by
    rw [List.forIn_cons]
    have hx := hstep x init h
    revert hx
    generalize body x init = s
    intro hx
    cases s with
    | done v => exact hx
    | yield v => exact forIn_id_inv P body hstep l v hx

theorem forIn_id_inv_array {α β : Type} (P : β → Prop) (body : α → β → Id (ForInStep β))
    (hstep : ∀ x r, P r → P (body x r).value) (xs : Array α) (init : β) (h0 : P init) :
    P (forIn (m := Id) xs init body) := by
  rw [← Array.forIn_toList]; exact forIn_id_inv P body hstep xs.toList init h0

theorem list_foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b x, P b → P (f b x)) :
    ∀ (l : List α) (init : β), P init → P (l.foldl f init)
  | [], _, h => h
  | x :: l, init, h => list_foldl_inv P f hf l (f init x) (hf init x h)

theorem array_foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b x, P b → P (f b x))
    (xs : Array α) (init : β) (h0 : P init) : P (xs.foldl f init) := by
  rw [← Array.foldl_toList]; exact list_foldl_inv P f hf xs.toList init h0

/-! ## One occurrence, one walk, one constructor -/

/-- **`replaceIfNested` only appends auxiliaries owned by the walked entry's owner, numbered in
order.** -/
theorem replaceIfNested_grow (cx : XCtx) (np : Nat) (owner : Name) (e : Expr) (d : Nat) (st : XSt) :
    IndexGrow cx.all0 owner st (replaceIfNested cx np owner e d st).2 := by
  unfold replaceIfNested
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
theorem replaceAll_grow (cx : XCtx) (np : Nat) (owner : Name) :
    ∀ (e : Expr) (d : Nat) (st : XSt), IndexGrow cx.all0 owner st (replaceAll cx np owner e d st).2 := by
  intro e
  induction e with
  | app f a h ihf iha =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.app f a h) d st
    revert hR
    cases replaceIfNested cx np owner (.app f a h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihf d st1
        revert h1
        cases replaceAll cx np owner f d st1 with
        | mk f' st2 =>
          intro h1
          have h2 := iha d st2
          revert h2
          cases replaceAll cx np owner a d st2 with
          | mk a' st3 => intro h2; exact hR.trans (h1.trans h2)
  | lam n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.lam n t b bi h) d st
    revert hR
    cases replaceIfNested cx np owner (.lam n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | forallE n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.forallE n t b bi h) d st
    revert hR
    cases replaceIfNested cx np owner (.forallE n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | letE n t v b nd h iht ihv ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.letE n t v b nd h) d st
    revert hR
    cases replaceIfNested cx np owner (.letE n t v b nd h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihv d st2
          revert h2
          cases replaceAll cx np owner v d st2 with
          | mk v' st3 =>
            intro h2
            have h3 := ihb (d + 1) st3
            revert h3
            cases replaceAll cx np owner b (d + 1) st3 with
            | mk b' st4 => intro h3; exact hR.trans (h1.trans (h2.trans h3))
  | proj n i s h ihs =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.proj n i s h) d st
    revert hR
    cases replaceIfNested cx np owner (.proj n i s h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihs d st1
        revert h1
        cases replaceAll cx np owner s d st1 with
        | mk s' st2 => intro h1; exact hR.trans h1
  | mdata md x h ihx =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.mdata md x h) d st
    revert hR
    cases replaceIfNested cx np owner (.mdata md x h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihx d st1
        revert h1
        cases replaceAll cx np owner x d st1 with
        | mk x' st2 => intro h1; exact hR.trans h1
  | bvar i h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.bvar i h) d st
    revert hR
    cases replaceIfNested cx np owner (.bvar i h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | fvar n h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.fvar n h) d st
    revert hR
    cases replaceIfNested cx np owner (.fvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | mvar n h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.mvar n h) d st
    revert hR
    cases replaceIfNested cx np owner (.mvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | sort u h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.sort u h) d st
    revert hR
    cases replaceIfNested cx np owner (.sort u h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | const n us h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.const n us h) d st
    revert hR
    cases replaceIfNested cx np owner (.const n us h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | lit l h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_grow cx np owner (.lit l h) d st
    revert hR
    cases replaceIfNested cx np owner (.lit l h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR

theorem skel_modify (st : XSt) (qi : Nat) (f : XMember → XMember)
    (hf : ∀ m, (f m).name = m.name ∧ (f m).sourceOwner = m.sourceOwner) :
    (st.types.modify qi f).toList.map (fun m => (m.name, m.sourceOwner)) = skel st := by
  unfold skel
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList,
    Array.getElem?_modify]
  split
  · cases st.types[i]? with
    | none => rfl
    | some m => simp only [Option.map_some, (hf m).1, (hf m).2]
  · rfl

/-- **Walking one constructor of queue entry `qi`** appends auxiliaries owned by that entry's
owner, numbered in order, and changes no entry's name or owner. -/
theorem walkCtor_grow (cx : XCtx) (qi ci : Nat) (st : XSt) {mem : XMember}
    (hm : st.types[qi]? = some mem) : IndexGrow cx.all0 mem.sourceOwner st (walkCtor cx qi ci st) := by
  unfold walkCtor
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

theorem walkCtor_none (cx : XCtx) (qi ci : Nat) (st : XSt) (hm : st.types[qi]? = none) :
    walkCtor cx qi ci st = st := by
  unfold walkCtor; rw [hm]

/-! ## The queue -/

theorem skel_getElem? (st : XSt) (i : Nat) :
    (skel st)[i]? = st.types[i]?.map (fun m => (m.name, m.sourceOwner)) := by
  unfold skel; rw [List.getElem?_map, Array.getElem?_toList]

theorem skel_length (st : XSt) : (skel st).length = st.types.size := by
  unfold skel; simp

/-- The queue invariant at position `qi`: the members `M` first, then auxiliaries `A` numbered
`1, 2, …`, the `k`-th discovered from an entry `D[k]` before it, the `D[k]` non-decreasing and
below `qi`, each auxiliary sharing its discovering entry's owner. -/
def QInv (all0 : Name) (M : List (Name × Name)) (qi : Nat) (st : XSt) : Prop :=
  ∃ (A : List (Name × Name)) (D : List Nat), skel st = M ++ A ∧ A.length = D.length ∧
    st.nextAuxIdx = A.length + 1 ∧ D.Pairwise (· ≤ ·) ∧ (∀ d ∈ D, d < qi) ∧
    ∀ k p d, A[k]? = some p → D[k]? = some d →
      (∃ J forbidden, p.1 = auxNameOf all0 J (k + 1) forbidden) ∧ d < M.length + k ∧
      ∃ q, (M ++ A)[d]? = some q ∧ p.2 = q.2

/-- Walking all constructors of queue entry `qi` keeps the invariant, one position on. -/
theorem qinv_step {cx : XCtx} {M : List (Name × Name)} {qi : Nat} {st : XSt} {mem : XMember}
    (hq : QInv cx.all0 M qi st) (hm : st.types[qi]? = some mem) :
    QInv cx.all0 M (qi + 1)
      ((List.range mem.ctors.size).foldl (fun st ci => walkCtor cx qi ci st) st) := by
  obtain ⟨A, D, hs, hAD, hn, hDs, hDq, hk⟩ := hq
  -- the walk grows the queue by auxiliaries owned by `mem`'s owner
  have hg : IndexGrow cx.all0 mem.sourceOwner st
      ((List.range mem.ctors.size).foldl (fun st ci => walkCtor cx qi ci st) st) := by
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
theorem walkQueue_qinv {cx : XCtx} {M : List (Name × Name)} :
    ∀ (fuel qi : Nat) (st fin : XSt), QInv cx.all0 M qi st → walkQueue cx fuel qi st = .ok fin →
      ∃ qi', QInv cx.all0 M qi' fin
  | 0, qi, st, fin, hq, h => by
    rw [walkQueue.eq_1] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases except_pure_ok h; exact ⟨qi, hq⟩
  | fuel + 1, qi, st, fin, hq, h => by
    rw [walkQueue.eq_2] at h
    split at h
    · cases h
    · split at h
      · cases except_pure_ok h; exact ⟨qi, hq⟩
      · rename_i mem hm
        exact walkQueue_qinv fuel (qi + 1) _ fin (qinv_step hq hm) h

/-- A pending key-conversion error wins even at an empty queue or a zero
fuel boundary: no partial expansion can be returned as a success. -/
theorem walkQueue_keyError (cx : XCtx) (fuel qi : Nat) (st : XSt) (e : String)
    (h : st.keyError = some e) : walkQueue cx fuel qi st = .error e := by
  cases fuel <;> simp [walkQueue, h]

/-! ## The expansion -/

theorem aux_getElem?_eq (x : Expanded) (k : Nat) (h : x.nOriginals ≤ x.types.size) :
    x.aux[k]? = x.types[x.nOriginals + k]? := by
  unfold Expanded.aux
  rw [Array.getElem?_extract, Nat.min_self]
  split
  · rfl
  · rename_i hk; rw [Array.getElem?_eq_none]; omega

/-- **The nested expansion, in discovery order** (Def 2.5): the members first, in the given
order; the `k`-th auxiliary named with the number `k + 1`; every auxiliary discovered from an
earlier queue entry, the discovering entries non-decreasing along the auxiliaries
(breadth-first over the queue), each auxiliary owned by its discovering entry's owner. -/
theorem expand_source_index_spec {source : Ix.Environment} {dedup : Dedup} {ordered : Array Name}
    {aliasToRep : Std.HashMap Name Name} {groupOf : SourceGroups}
    {keyAddr? : Option (Name → Option Address)} {x : Expanded}
    (h : expandSourceSpec source dedup ordered aliasToRep groupOf keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView), ordered[0]? = some first ∧ IndView.ofConst? source.get? first = some fi ∧
      x.nOriginals = ordered.size ∧ x.nOriginals ≤ x.types.size ∧
      (∀ (i : Nat) (n : Name), ordered[i]? = some n → ∃ m : XMember, x.types[i]? = some m ∧ m.name = n ∧ m.sourceOwner = n) ∧
      ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k : Nat) (m : XMember), x.aux[k]? = some m →
          (∃ J forbidden, m.name = auxNameOf (fi.all[0]?.getD first) J (k + 1) forbidden) ∧
          ∃ (d : Nat) (md : XMember), D[k]? = some d ∧ d < x.nOriginals + k ∧ x.types[d]? = some md ∧
            m.sourceOwner = md.sourceOwner := by
  unfold expandSourceSpec at h
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
theorem expand_source_owner {source : Ix.Environment} {dedup : Dedup} {ordered : Array Name}
    {aliasToRep : Std.HashMap Name Name} {groupOf : SourceGroups}
    {keyAddr? : Option (Name → Option Address)} {x : Expanded}
    (h : expandSourceSpec source dedup ordered aliasToRep groupOf keyAddr? = .ok x) :
    ∀ (i : Nat) (m : XMember), x.types[i]? = some m → m.sourceOwner ∈ ordered := by
  obtain ⟨first, fi, -, -, hn0, hle, hmem, D, hD, -, hk⟩ := expand_source_index_spec h
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

/-- **A component's canonical nested auxiliaries are its canonical expansion's, in discovery order**
(Def 2.5 over the canonical block, under the discovery rule): one class per auxiliary, in the order
the expansion appends them; the `k`-th numbered `k + 1`; each owned by a class representative;
each discovered breadth-first from an earlier queue entry. -/
theorem componentNested_source_discovery {rules : Rules} (hr : rules.nested = .discovery) {env : SourceEnv}
    {all : Array Name} {classes : Array (Array Name)} {n : NestedCanon}
    (h : SourceBlock.componentNested rules env all classes = .ok (some n)) :
    ∃ (x : Expanded) (first : Name) (fi : IndView), SourceBlock.canonExpand rules env classes = .ok x ∧
      n.canonClasses = x.aux.map (fun m => #[m.name]) ∧ sigsInOrder x n.canonClasses = .ok n.canon ∧
      (repsOf classes)[0]? = some first ∧ env.ind? first = some fi ∧
      x.nOriginals = (repsOf classes).size ∧
      (∀ (k : Nat) (m : XMember), x.aux[k]? = some m →
        (∃ J forbidden, m.name = auxNameOf (fi.all[0]?.getD first) J (k + 1) forbidden) ∧ m.sourceOwner ∈ repsOf classes) ∧
      ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k := by
  have actual : componentNested rules (Env.ofSource env) all classes = .ok (some n) := by
    rw [ComponentCoreProof.componentNested_eq_core]
    change ComponentCore.componentNested (ComponentCore.Protection.ofSource env) rules
      (ComponentCore.Env.ofSource env) all classes = .ok (some n)
    rw [← SourceComponentCoreProof.componentNested_eq_core]
    exact h
  obtain ⟨x, genericExpansion, hcc, hsig, -, -, -⟩ := componentNested_source_some hr actual
  have hx : SourceBlock.canonExpand rules env classes = .ok x := by
    rw [SourceComponentCoreProof.canonExpand_eq_core]
    rw [ComponentCoreProof.canonExpand_eq_core] at genericExpansion
    exact genericExpansion
  have hx' := hx
  unfold SourceBlock.canonExpand at hx'
  obtain ⟨first, fi, hfirst, hfi, hn0, hle, -, D, hD, hDs, hk⟩ := expand_source_index_spec hx'
  refine ⟨x, first, fi, hx, hcc, hsig, hfirst, hfi, hn0, fun k m hm => ?_, D, hD, hDs, fun k d hd => ?_⟩
  · obtain ⟨hJ, -⟩ := hk k m hm
    refine ⟨hJ, expand_source_owner hx' (x.nOriginals + k) m ?_⟩
    rw [← aux_getElem?_eq x k hle]; exact hm
  · have hkl : k < x.aux.size := by
      rw [← hD]
      rcases Nat.lt_or_ge k D.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hd; cases hd
    obtain ⟨m, hm⟩ : ∃ m, x.aux[k]? = some m := ⟨x.aux[k], Array.getElem?_eq_getElem hkl⟩
    obtain ⟨-, d', md, hd', hlt, -⟩ := hk k m hm
    rw [hd] at hd'; cases hd'
    exact hlt

end Ix.CompileCert.Canon
