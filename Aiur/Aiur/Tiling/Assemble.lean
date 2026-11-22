import Aiur.Tiling.Chunks
import Aiur.Tiling.Keyed

/-!
# Whole-tuple balance from the narrow bus

A `Part` is one wide lookup as it travels on the narrow bus: an unchunked
message `[tag, sub, payload]`, or a keyed chunk group whose chunk `c` is
`[tag, chunkSub rom sub c, key, chunk_c]`. Parts may come from the tiled
system's instances or from outside it (public claims, tables).

`Part.balance`: if the narrow encodings of a finite family of parts sum to
zero, so do their wide tuples, provided

* every part is formed (an unchunked payload fits a row, a chunked one does
  not; chunks concatenate to the payload after a ROM read's address key; a
  chunked send has weight 0 or 1);
* every row key `(tag, sub_row)` of a part has the role and arity of one
  global table, so chunk rows of different channels or chunk indices never
  share a tuple, unchunked rows never meet chunk rows, and all chunk groups
  of one channel split their payloads the same way;
* chunked receivers of one channel have distinct keys;
* the family is smaller than the characteristic bound.
-/

namespace Aiur.Tiling

variable {F : Type} [Field F] [DecidableEq F]

structure Part (F : Type) where
  tag : F
  sub : F
  payload : List F
  weight : F
  recv : Bool
  key : F
  /-- Empty for an unchunked message. -/
  chunks : List (List F)
  /-- Per-chunk weights of a chunked receiver whose chunks are separate trace
  rows; empty when every chunk has `weight`. -/
  cweights : List F

namespace Part

variable (p : Part F)

def rom : Bool := p.tag == 2

def tuple : List F := p.tag :: p.sub :: p.payload

noncomputable def wide : Ledger F := Finsupp.single p.tuple p.weight

def chunkTuple (c : Nat) : List F := p.tag :: chunkSub p.rom p.sub c :: p.key :: p.chunks.getD c []

/-- The weight of chunk `c`. -/
def cweight (c : Nat) : F := p.cweights.getD c p.weight

noncomputable def narrow : Ledger F :=
  if p.chunks = [] then p.wide
  else ∑ c ∈ Finset.range p.chunks.length, Finsupp.single (p.chunkTuple c) (p.cweight c)

def Formed (W : Nat) : Prop :=
  (p.chunks = [] ∧ p.payload.length + 1 ≤ W) ∨
    (2 ≤ p.chunks.length ∧ W ≤ p.payload.length ∧
      p.payload = (if p.rom then [p.key] else []) ++ p.chunks.flatten ∧
      (p.recv = false → p.weight = 0 ∨ p.weight = 1) ∧
      (p.cweights = [] ∨ (p.recv = true ∧ p.cweight 0 = p.weight)))

/-- The part's row keys have the roles and arities of the given tables. -/
def RowsIn (role : F × F → Option (RowRole F)) (arity : F × F → Option Nat) : Prop :=
  (p.chunks = [] → ∀ r, role (p.tag, p.sub) = some r → r.2 = none) ∧
    (p.chunks ≠ [] → ∀ c < p.chunks.length,
      role (p.tag, chunkSub p.rom p.sub c) = some (p.sub, some (c, p.chunks.length, p.rom)) ∧
        arity (p.tag, chunkSub p.rom p.sub c) = some ((p.chunks.getD c []).length + 1))

variable {p}

theorem narrow_apply (cp : p.chunks ≠ []) (t : List F) :
    p.narrow t = ∑ c ∈ Finset.range p.chunks.length, if p.chunkTuple c = t then p.cweight c else 0 := by
  simp [narrow, cp, Finsupp.finsetSum_apply, Finsupp.single_apply]

variable {role : F × F → Option (RowRole F)} {arity : F × F → Option Nat}

theorem same_role {q : Part F} (hp : p.RowsIn role arity) (hq : q.RowsIn role arity)
    (cp : p.chunks ≠ []) (cq : q.chunks ≠ []) {c c' : Nat} (hc : c < p.chunks.length)
    (hc' : c' < q.chunks.length)
    (key : (p.tag, chunkSub p.rom p.sub c) = (q.tag, chunkSub q.rom q.sub c')) :
    p.sub = q.sub ∧ c = c' ∧ p.chunks.length = q.chunks.length ∧ p.rom = q.rom := by
  have a := (hp.2 cp c hc).1
  have b := (hq.2 cq c' hc').1
  rw [key, b] at a
  simp only [Option.some.injEq, Prod.mk.injEq] at a
  exact ⟨a.1.symm, a.2.1.symm, a.2.2.1.symm, a.2.2.2.symm⟩

@[simp] theorem cweight_nil {p : Part F} (h : p.cweights = []) (c : Nat) : p.cweight c = p.weight := by
  simp [cweight, h]

theorem unchunked_off {q : Part F} (hp : p.RowsIn role arity) (hq : q.RowsIn role arity)
    (cp : p.chunks = []) (cq : q.chunks ≠ []) {c : Nat} (hc : c < q.chunks.length)
    (key : (p.tag, p.sub) = (q.tag, chunkSub q.rom q.sub c)) : False := by
  have := hp.1 cp _ (key ▸ (hq.2 cq c hc).1)
  simp at this

end Part

theorem flatten_eq_iff {α : Type} : ∀ {a b : List (List α)}, a.length = b.length →
    (∀ c < a.length, (a.getD c []).length = (b.getD c []).length) →
    (a.flatten = b.flatten ↔ ∀ c < a.length, a.getD c [] = b.getD c [])
  | [], [], _, _ => by simp
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len
  | x :: a, y :: b, len, lens => by
      have h0 : x.length = y.length := by simpa using lens 0 (by simp)
      have ih := flatten_eq_iff (a := a) (b := b) (by simpa using len)
        (fun c hc => by simpa using lens (c + 1) (by simp; omega))
      simp only [List.flatten_cons]
      constructor
      · intro h
        obtain ⟨e1, e2⟩ := List.append_inj h h0
        intro c hc
        cases c with
        | zero => simpa using e1
        | succ c => simpa using (ih.mp e2) c (by simp at hc; omega)
      · intro h
        have e1 : x = y := by simpa using h 0 (by simp)
        have e2 := ih.mpr (fun c hc => by simpa using h (c + 1) (by simp; omega))
        rw [e1, e2]

section Balance

variable {ι : Type} [DecidableEq ι] {I : Finset ι} {part : ι → Part F} {W bound : Nat}
  {role : F × F → Option (RowRole F)} {arity : F × F → Option Nat}
  (formed : ∀ x ∈ I, (part x).Formed W) (rows : ∀ x ∈ I, (part x).RowsIn role arity)
  (unique : ∀ x ∈ I, ∀ y ∈ I, (part x).recv = true → (part y).recv = true →
    (part x).chunks ≠ [] → (part y).chunks ≠ [] → (part x).tag = (part y).tag →
    (part x).sub = (part y).sub → (part x).key = (part y).key → x = y)
  (small : SmallCast F bound) (short : I.card < bound)
  (zero : ∑ x ∈ I, (part x).narrow = 0)

theorem sum_narrow_apply (zero : ∑ x ∈ I, (part x).narrow = 0) (t : List F) :
    ∑ x ∈ I, (part x).narrow t = 0 := by
  have := congrArg (fun L : Ledger F => L t) zero
  simpa [Finsupp.finsetSum_apply] using this

include formed rows zero in
theorem Part.balance_short {t : List F}
    (notLong : ∀ q ∈ I, (part q).chunks ≠ [] → (part q).tuple ≠ t) :
    ∑ x ∈ I, (part x).wide t = 0 := by
  by_cases hc : ∃ y ∈ I, (part y).chunks ≠ [] ∧ ∃ c < (part y).chunks.length, (part y).chunkTuple c = t
  · obtain ⟨y, hy, cy, c, hc, eq⟩ := hc
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Part.wide, Finsupp.single_apply]
    rw [if_neg]
    intro tx
    by_cases cx : (part x).chunks = []
    · apply Part.unchunked_off (rows x hx) (rows y hy) cx cy hc
      rw [← eq] at tx
      simp only [Part.tuple, Part.chunkTuple, List.cons.injEq] at tx
      rw [tx.1, tx.2.1]
    · exact notLong x hx cx tx
  · push Not at hc
    rw [← sum_narrow_apply zero t]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases cx : (part x).chunks = []
    · simp [Part.narrow, cx]
    · rw [Part.narrow_apply cx, Finset.sum_eq_zero (fun c hc' => if_neg (hc x hx cx c (Finset.mem_range.mp hc')))]
      simp [Part.wide, Finsupp.single_apply, notLong x hx cx]

include formed rows unique small short zero in
theorem Part.balance_long {q : ι} (hq : q ∈ I) (cq : (part q).chunks ≠ []) :
    ∑ x ∈ I, (part x).wide (part q).tuple = 0 := by
  set P := part q with hP
  set J := P.chunks.length with hJ
  let K := I.filter fun x => (part x).chunks ≠ [] ∧ (part x).tag = P.tag ∧ (part x).sub = P.sub
  have inK : ∀ x ∈ K, x ∈ I ∧ (part x).chunks ≠ [] ∧ (part x).tag = P.tag ∧ (part x).sub = P.sub :=
    fun x hx => Finset.mem_filter.mp hx |> fun ⟨a, b⟩ => ⟨a, b⟩
  have romK : ∀ x ∈ K, (part x).rom = P.rom := by
    intro x hx; simp [Part.rom, (inK x hx).2.2.1]
  have lenK : ∀ x ∈ K, (part x).chunks.length = J := by
    intro x hx
    obtain ⟨hxI, cx, tg, sb⟩ := inK x hx
    exact (Part.same_role (rows x hxI) (rows q hq) cx cq (List.length_pos_iff.mpr cx)
      (List.length_pos_iff.mpr cq) (by rw [tg, sb, romK x hx])).2.2.1
  have arK : ∀ x ∈ K, ∀ c < J, ((part x).chunks.getD c []).length = (P.chunks.getD c []).length := by
    intro x hx c hc
    obtain ⟨hxI, cx, tg, sb⟩ := inK x hx
    have a := ((rows x hxI).2 cx c (by rw [lenK x hx]; exact hc)).2
    have b := ((rows q hq).2 cq c hc).2
    rw [← hP] at b
    rw [tg, sb, romK x hx, b] at a
    simp only [Option.some.injEq] at a
    omega
  have matchK : ∀ x ∈ K, (part x).tuple = P.tuple ↔
      ((P.rom = true → (part x).key = P.key) ∧
        ∀ c < J, (part x).chunks.getD c [] = P.chunks.getD c []) := by
    intro x hx
    obtain ⟨hxI, cx, tg, sb⟩ := inK x hx
    rcases formed x hxI with ⟨h, _⟩ | ⟨_, _, px, _⟩
    · exact absurd h cx
    rcases formed q hq with ⟨h, _⟩ | ⟨_, _, pq, _⟩
    · exact absurd h cq
    have flat := flatten_eq_iff (a := (part x).chunks) (b := P.chunks) (by rw [lenK x hx])
      (fun c hc => arK x hx c (by rw [lenK x hx] at hc; exact hc))
    rw [lenK x hx] at flat
    simp only [Part.tuple, tg, sb, List.cons.injEq, true_and]
    rw [← hP] at pq
    rw [px, pq, romK x hx]
    cases P.rom <;> simp [flat]
  have wideK : ∑ x ∈ I, (part x).wide P.tuple =
      ∑ x ∈ K.filter (fun x => (part x).tuple = P.tuple), (part x).weight := by
    simp only [Part.wide, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, K]
    constructor
    · rintro ⟨hx, tx⟩
      have cx : (part x).chunks ≠ [] := by
        intro cx
        rcases formed x hx with ⟨_, lx⟩ | ⟨h, _⟩
        · rcases formed q hq with ⟨h, _⟩ | ⟨_, lq, _⟩
          · exact cq h
          · rw [← hP] at lq
            have := congrArg List.length tx
            simp only [Part.tuple, List.length_cons] at this
            omega
        · simp [cx] at h
      have tx' := tx
      simp only [Part.tuple, List.cons.injEq] at tx'
      exact ⟨⟨hx, cx, tx'.1, tx'.2.1⟩, tx⟩
    · rintro ⟨⟨hx, _⟩, tx⟩; exact ⟨hx, tx⟩
  let S := K.filter fun x => (part x).recv = false
  let R := K.filter fun x => (part x).recv = true
  have splitSR : ∀ (Q : ι → Prop) [DecidablePred Q] (g : ι → F), ∑ x ∈ K.filter Q, g x =
      ∑ x ∈ S.filter Q, g x + ∑ x ∈ R.filter Q, g x := by
    intro Q _ g
    rw [← Finset.sum_filter_add_sum_filter_not (K.filter Q) (fun x => (part x).recv = true), add_comm]
    simp only [S, R, Finset.filter_filter, Bool.not_eq_true]
    congr 1 <;> apply Finset.sum_congr _ (fun _ _ => rfl) <;> ext x <;>
      simp only [Finset.mem_filter] <;> tauto
  have weightsS : ∀ x ∈ S, ∀ c, (part x).cweight c = (part x).weight := by
    intro x hx c
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hxI, cx, -, -⟩ := inK x hx'.1
    rcases formed x hxI with ⟨h, _⟩ | ⟨_, _, _, _, w⟩
    · exact absurd h cx
    · rcases w with w | ⟨r, _⟩
      · exact Part.cweight_nil w c
      · rw [hx'.2] at r; cases r
  have weightsR : ∀ x ∈ R, (part x).cweight 0 = (part x).weight := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hxI, cx, -, -⟩ := inK x hx'.1
    rcases formed x hxI with ⟨h, _⟩ | ⟨_, _, _, _, w⟩
    · exact absurd h cx
    · rcases w with w | ⟨_, w⟩
      · exact Part.cweight_nil w 0
      · exact w
  have balance : ChunkBalance S (fun x => (part x).key) (fun x c => (part x).chunks.getD c [])
      (fun x => (part x).weight) R (fun x => (part x).key) (fun x c => (part x).chunks.getD c [])
      (fun x j => -(part x).cweight j) J := by
    intro j hj k v
    let u := P.tag :: chunkSub P.rom P.sub j :: k :: v
    have zu := sum_narrow_apply zero u
    have off : ∀ x ∈ I, x ∉ K → (part x).narrow u = 0 := by
      intro x hx nk
      by_cases cx : (part x).chunks = []
      · simp only [Part.narrow, cx, if_true, Part.wide, Finsupp.single_apply]
        rw [if_neg]
        intro e
        simp only [Part.tuple, u, List.cons.injEq] at e
        exact Part.unchunked_off (rows x hx) (rows q hq) cx cq hj (by rw [e.1, e.2.1])
      · rw [Part.narrow_apply cx]
        apply Finset.sum_eq_zero
        intro c hc
        rw [if_neg]
        intro e
        simp only [Part.chunkTuple, u, List.cons.injEq] at e
        have := Part.same_role (rows x hx) (rows q hq) cx cq (Finset.mem_range.mp hc) hj
          (by rw [e.1, e.2.1])
        exact nk (Finset.mem_filter.mpr ⟨hx, cx, e.1, this.1⟩)
    have on : ∀ x ∈ K, (part x).narrow u =
        if (part x).key = k ∧ (part x).chunks.getD j [] = v then (part x).cweight j else 0 := by
      intro x hx
      obtain ⟨hxI, cx, tg, sb⟩ := inK x hx
      rw [Part.narrow_apply cx, lenK x hx, Finset.sum_eq_single j]
      · simp [Part.chunkTuple, u, tg, sb, romK x hx]
      · intro c hc ne
        rw [if_neg]
        intro e
        simp only [Part.chunkTuple, u, List.cons.injEq] at e
        have := Part.same_role (rows x hxI) (rows q hq) cx cq
          (by rw [lenK x hx]; exact Finset.mem_range.mp hc) hj (by rw [e.1, e.2.1])
        exact ne this.2.1
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    have sumK : ∑ x ∈ K.filter (fun x => (part x).key = k ∧ (part x).chunks.getD j [] = v),
        (part x).cweight j = 0 := by
      rw [← zu, Finset.sum_filter, ← Finset.sum_filter_add_sum_filter_not I (· ∈ K),
        Finset.sum_eq_zero (s := I.filter (· ∉ K))
          (fun x hx => off x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2), add_zero]
      have : I.filter (· ∈ K) = K := by
        ext x; simp only [Finset.mem_filter, K]; tauto
      rw [this]
      exact Finset.sum_congr rfl fun x hx => (on x hx).symm
    rw [splitSR] at sumK
    rw [Finset.sum_neg_distrib, ← Finset.sum_congr rfl fun x hx =>
      weightsS x (Finset.mem_filter.mp hx).1 j]
    exact eq_neg_of_add_eq_zero_left sumK
  have unique' : Set.InjOn (fun x => (part x).key) R := by
    intro x hx y hy e
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    obtain ⟨hxI, cx, tx, sx⟩ := inK x hx'.1
    obtain ⟨hyI, cy, ty, sy⟩ := inK y hy'.1
    exact unique x hxI y hyI hx'.2 hy'.2 cx cy (tx.trans ty.symm) (sx.trans sy.symm) e
  have bits : ∀ x ∈ S, (part x).weight = 0 ∨ (part x).weight = 1 := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hxI, cx, -, -⟩ := inK x hx'.1
    rcases formed x hxI with ⟨h, _⟩ | ⟨_, _, _, b, _⟩
    · exact absurd h cx
    · exact b hx'.2
  have shortS : S.card < bound :=
    lt_of_le_of_lt (Finset.card_le_card fun x hx =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) short
  have nonempty : 0 < J := List.length_pos_iff.mpr cq
  rw [wideK, Finset.filter_congr (fun x hx => matchK x hx), splitSR]
  have rw0 : ∀ (Q : ι → Prop) [DecidablePred Q], ∑ x ∈ R.filter Q, (part x).weight =
      ∑ x ∈ R.filter Q, (part x).cweight 0 :=
    fun Q _ => Finset.sum_congr rfl fun x hx => (weightsR x (Finset.mem_filter.mp hx).1).symm
  cases hrom : P.rom
  · have := chunks_total balance unique' bits small shortS nonempty (fun c => P.chunks.getD c [])
    simp only [Bool.false_eq_true, false_implies, true_and]
    rw [this, Finset.sum_neg_distrib, rw0, neg_add_cancel]
  · have := chunks_sound balance unique' bits small shortS nonempty P.key (fun c => P.chunks.getD c [])
    simp only [forall_const]
    rw [this, Finset.sum_neg_distrib, rw0, neg_add_cancel]

include formed rows unique small short zero in
/-- **Whole-tuple balance.** Balanced narrow encodings of a family of parts
give balanced wide tuples. -/
theorem Part.balance : ∑ x ∈ I, (part x).wide = 0 := by
  ext t
  simp only [Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hB : ∃ q ∈ I, (part q).chunks ≠ [] ∧ (part q).tuple = t
  · obtain ⟨q, hq, cq, rfl⟩ := hB
    exact Part.balance_long formed rows unique small short zero hq cq
  · push Not at hB
    exact Part.balance_short formed rows zero hB

end Balance

end Aiur.Tiling
