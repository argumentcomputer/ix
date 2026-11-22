import Aiur.Tiling.IxaProgram
import Aiur.Tiling.IxaTrace

/-!
# The trace section reads back what the compiler wrote

A trace section's polynomials share a node pool (`Trace.NodePool`) that the
writer builds while it writes the body and then emits ahead of it. `NodesGood
enc m E s` says that the pool `s` holds the nodes whose expansions are `E`: its
bytes are what `getNodes` reads as `E` (`getNodes_reads`), and every indexed
key is the node at its index. `node_spec` and `intern_spec` keep it through
`NodePool.node` and `internPolynomial`.

`RTP ne enc m p G x` is the pool analogue of `RT`: a successful run of the
pool writer `p` from a good pool ends at a good extension and appends bytes
that `G Ef` reads as `x` over every further extension `Ef`, since a record is
read against the final pool. `RTE` is the same with the value left
existential. The records of a trace section read back: chips exactly
(`rtp_putChip`, `rtp_chips`), plans, operations and groups up to their value
(`rte_plan`, `rte_op`, `rte_group`).

`trace_reads` assembles them over `withNodesWithEncoding`: a trace section
written as the compiler lays it out reads back with the chips its chip list
writes. `section_reads` peels a successful `exportTraceSection` to that
writer, so its chips read back as the written depth chips, and
`chips_of_decode` follows `getPackage` past the program section to the chips
of a package carrying that section.
-/

namespace Aiur.Tiling.Ixa

open Aiur.Ixon Aiur.Execution Aiur.Execution.Codec Aiur.Trace Aiur.Circuit

variable {F : Type}

section Ext

/-- `E` extends `E₀`. -/
def Ext (E₀ E : Array (ArithExpr F)) : Prop := E₀.size ≤ E.size ∧ ∀ i < E₀.size, E[i]? = E₀[i]?

theorem ext_refl (E : Array (ArithExpr F)) : Ext E E := ⟨le_refl _, fun _ _ => rfl⟩

theorem ext_trans {A B C : Array (ArithExpr F)} (h₁ : Ext A B) (h₂ : Ext B C) : Ext A C :=
  ⟨h₁.1.trans h₂.1, fun i hi => (h₂.2 i (by have := h₁.1; omega)).trans (h₁.2 i hi)⟩

theorem ext_push (E : Array (ArithExpr F)) (x : ArithExpr F) : Ext E (E.push x) :=
  ⟨by simp, fun i hi => by rw [Array.getElem?_push]; simp [show i ≠ E.size by omega]⟩

theorem ext_getD {A B : Array (ArithExpr F)} (h : Ext A B) {i : Nat} (hi : i < A.size) (d : ArithExpr F) :
    B.getD i d = A.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, h.2 i hi]

theorem ext_getElem {A B : Array (ArithExpr F)} (h : Ext A B) {i : Nat} (hi : i < A.size) :
    ∃ hb : i < B.size, B[i] = A[i] := by
  have e := h.2 i hi
  have hb : i < B.size := by have := h.1; omega
  refine ⟨hb, ?_⟩
  rw [Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hi] at e
  exact Option.some.inj e

theorem getD_of {E : Array (ArithExpr F)} {i : Nat} {hi : i < E.size} {p : ArithExpr F}
    (h : E[i] = p) (d : ArithExpr F) : E.getD i d = p := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, h]

/-- The node `i` of a pool, its expansion `p`, kept by every extension. -/
def Holds (E : Array (ArithExpr F)) (i : Nat) (p : ArithExpr F) : Prop := ∃ hi : i < E.size, E[i] = p

theorem holds_ext {A B : Array (ArithExpr F)} (h : Ext A B) {i : Nat} {p : ArithExpr F}
    (hp : Holds A i p) : Holds B i p := by
  obtain ⟨hi, e⟩ := hp
  obtain ⟨hb, e'⟩ := ext_getElem h hi
  exact ⟨hb, e'.trans e⟩

end Ext

section Pool

variable [NatCast F]

/-- The expansion of the node `(tag, a, b)` over the earlier expansions `E`, as
`getNodes` builds it. -/
def nodeExpr (E : Array (ArithExpr F)) : Nat × Nat × Nat → ArithExpr F
  | (0, a, _) => .const (a : F)
  | (1, a, _) => .var a
  | (2, a, b) => .add (E.getD a (.var 0)) (E.getD b (.var 0))
  | (3, a, b) => .sub (E.getD a (.var 0)) (E.getD b (.var 0))
  | (_, a, b) => .mul (E.getD a (.var 0)) (E.getD b (.var 0))

/-- The key `(tag, a, b)` may be node `i`: its tag is known and its operands
come before it. -/
def KeyValid (i : Nat) : Nat × Nat × Nat → Prop
  | (tag, a, b) => tag < 5 ∧ (2 ≤ tag → a < i ∧ b < i)

/-- The bytes `nb` of node `i` with key `k`, as `getNodes`' loop reads them. -/
def NodeBytes (wide : Bool) (modulus i : Nat) (k : Nat × Nat × Nat) (nb : List UInt8) : Prop :=
  match k with
  | (0, a, _) => a < modulus ∧ ∃ e, nb = 0 :: e ∧ Reads (getScalar wide) e a
  | (1, a, _) => nb = 1 :: tagBytes a ∧ a < 2 ^ 64
  | (tag, a, b) => nb = tag.toUInt8 :: (tagBytes (i - a) ++ tagBytes (i - b)) ∧
      i - a < 2 ^ 64 ∧ i - b < 2 ^ 64

/-- The pool `s` holds the nodes whose expansions are `E`. -/
structure NodesGood (encoding : FieldEncoding) (modulus : Nat) (E : Array (ArithExpr F))
    (s : NodePool) : Prop where
  enc : s.fieldEncoding = encoding
  mod : s.modulus = some modulus
  count : s.count = E.size
  bytes : ∃ nbs : List (List UInt8), nbs.length = E.size ∧ s.bytes.data.toList = nbs.flatten ∧
    ∀ i (hi : i < E.size), ∃ k nb, nbs[i]? = some nb ∧ KeyValid i k ∧ E[i] = nodeExpr E k ∧
      NodeBytes (encoding == .wide) modulus i k nb
  index : ∀ k i, s.index[k]? = some i → ∃ hi : i < E.size, KeyValid i k ∧ E[i] = nodeExpr E k

theorem st_bind_ok {σ α β : Type} {x : StateT σ PutM α} {f : α → StateT σ PutM β} {s : σ}
    {b b' : ByteArray} {r : β × σ} (h : (x >>= f) s b = .ok r b') :
    ∃ a s₁ b₁, x s b = .ok (a, s₁) b₁ ∧ f a s₁ b₁ = .ok r b' := by
  change EStateM.bind (x s) (fun p => f p.1 p.2) b = _ at h
  simp only [EStateM.bind] at h
  split at h
  · rename_i p b₁ hx
    exact ⟨p.1, p.2, b₁, hx, h⟩
  · cases h

theorem nodeExpr_ext {A B : Array (ArithExpr F)} (h : Ext A B) {n : Nat} {k : Nat × Nat × Nat}
    (valid : KeyValid n k) (hn : n ≤ A.size) : nodeExpr B k = nodeExpr A k := by
  obtain ⟨tag, a, b⟩ := k
  obtain ⟨_, ops⟩ := valid
  match tag, ops with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, ops =>
    have := ops (by omega)
    simp only [nodeExpr, ext_getD h (i := a) (by omega), ext_getD h (i := b) (by omega)]
  | 3, ops =>
    have := ops (by omega)
    simp only [nodeExpr, ext_getD h (i := a) (by omega), ext_getD h (i := b) (by omega)]
  | t + 4, ops =>
    have := ops (by omega)
    simp only [nodeExpr, ext_getD h (i := a) (by omega), ext_getD h (i := b) (by omega)]

theorem pool_throw {α : Type} {msg : String} {s : NodePool} {b b' : ByteArray} {r : α × NodePool}
    (h : (throw msg : PoolM α) s b = .ok r b') : False := by
  simp only [throw, throwThe, MonadExceptOf.throw] at h
  cases h

theorem pool_pure {α : Type} {x : α} {s : NodePool} {b b' : ByteArray} {r : α × NodePool}
    (h : (pure x : PoolM α) s b = .ok r b') : r = (x, s) ∧ b' = b := by
  simp only [pure, StateT.pure, EStateM.pure, EStateM.Result.ok.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- The bytes a successful `putNode` run writes into its own buffer. -/
theorem putNode_bytes {enc : FieldEncoding} {m i tag a b : Nat} {node : ByteArray}
    (small : tag = 0 → a < m)
    (h : Ixon.run (do
        u8 tag.toUInt8
        if (tag == 0) = true then
          match some m with
          | some modulus => enc.putScalar modulus a
          | none => enc.put a
        else if (tag == 1) = true then nat a
        else do nat (i - a); nat (i - b)) 40 = .ok node) :
    NodeBytes (enc == .wide) m i (tag, a, b) node.data.toList := by
  unfold Ixon.run at h
  split at h
  case h_2 => cases h
  rename_i u b₀ hrun
  cases h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok hrun
  have w₁ := u8_writes _ _ _ h₁
  subst w₁
  have e₀ : (ByteArray.emptyWithCapacity 40).data.toList = [] := rfl
  match tag with
  | 0 =>
      obtain ⟨e, rfl, _, r⟩ := scalarCodec_of enc m a _ _ h₂
      refine ⟨small rfl, e, ?_, r⟩
      simp [ByteArray.data_append, e₀]
  | 1 =>
      have w := nat_writes a _ _ h₂
      subst w
      refine ⟨?_, nat_ok h₂⟩
      simp [ByteArray.data_append, e₀]
  | t + 2 =>
      simp only [show ((t + 2 : Nat) == 0) = false by simp, show ((t + 2 : Nat) == 1) = false by simp,
        Bool.false_eq_true, ↓reduceIte] at h₂
      obtain ⟨b₂, h₃, h₄⟩ := bind_unit_ok h₂
      have w₃ := nat_writes _ _ _ h₃
      have w₄ := nat_writes _ _ _ h₄
      subst w₃ w₄
      refine ⟨?_, nat_ok h₃, nat_ok h₄⟩
      simp [ByteArray.data_append, e₀]

/-- One `NodePool.node` step: the UInt64 check, then the index lookup, then the
node's bytes. -/
theorem node_run (tag a b : Nat) (s : NodePool) (buf : ByteArray) :
    NodePool.node tag a b s buf =
      if (tag != 0 || s.fieldEncoding == .narrow) = true ∧ ¬ a < 2 ^ 64 then
        .error s!"integer {a} exceeds UInt64" buf
      else match s.index[(tag, a, b)]? with
        | some i => .ok (i, s) buf
        | none =>
          match Ixon.run (do
              u8 tag.toUInt8
              if (tag == 0) = true then
                match s.modulus with
                | some modulus => s.fieldEncoding.putScalar modulus a
                | none => s.fieldEncoding.put a
              else if (tag == 1) = true then nat a
              else do nat (s.count - a); nat (s.count - b)) 40 with
          | .ok node => .ok (s.count, ⟨s.bytes.append node, s.count + 1, s.index.insert (tag, a, b) s.count, s.fieldEncoding, s.modulus⟩) buf
          | .error e => .error e buf := by
  by_cases hthrow : (tag != 0 || s.fieldEncoding == .narrow) = true ∧ ¬ a < 2 ^ 64
  · obtain ⟨c, w⟩ := hthrow
    replace w : ¬ a < 18446744073709551616 := w
    simp [NodePool.node, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
      EStateM.bind, EStateM.pure, c, w, throw, throwThe, MonadExceptOf.throw, EStateM.throw, StateT.lift]
  · simp only [hthrow, ↓reduceIte]
    have hw : (tag != 0 || s.fieldEncoding == .narrow) = true → a < 18446744073709551616 :=
      fun c => Classical.byContradiction fun w => hthrow ⟨c, w⟩
    cases hi : s.index[(tag, a, b)]?
    · by_cases c : (tag != 0 || s.fieldEncoding == .narrow) = true <;>
      simp [NodePool.node, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
        EStateM.bind, EStateM.pure, hi, c, hw] <;>
      generalize Ixon.run _ 40 = r <;> cases r <;>
      simp_all [bind, MonadExcept.ofExcept, ofExcept, StateT.lift, EStateM.bind, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, EStateM.pure, pure, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, StateT.pure]
    · by_cases c : (tag != 0 || s.fieldEncoding == .narrow) = true <;>
      simp [NodePool.node, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
        EStateM.bind, EStateM.pure, hi, c, hw]

/-- A successful `NodePool.node` on a good pool leaves the outer buffer
unchanged and extends the pool to a good pool whose node `i` is the key. -/
theorem node_spec {enc : FieldEncoding} {m : Nat} {E : Array (ArithExpr F)} {s s' : NodePool}
    {buf buf' : ByteArray} {tag a b i : Nat} (good : NodesGood enc m E s) (htag : tag < 5)
    (small : tag = 0 → a < m) (ops : 2 ≤ tag → a < E.size ∧ b < E.size)
    (h : NodePool.node tag a b s buf = .ok (i, s') buf') :
    buf' = buf ∧ ∃ E', Ext E E' ∧ NodesGood enc m E' s' ∧
      ∃ hi : i < E'.size, KeyValid i (tag, a, b) ∧ E'[i] = nodeExpr E' (tag, a, b) := by
  rw [node_run] at h
  split at h
  · cases h
  split at h
  · rename_i j hj
    cases h
    obtain ⟨hi, v, e⟩ := good.index _ _ hj
    exact ⟨rfl, E, ext_refl E, good, hi, v, e⟩
  · rename_i hnone
    split at h
    · rename_i node hrun
      cases h
      rw [good.mod, good.count, good.enc] at hrun
      have nb := putNode_bytes small hrun
      have valid : KeyValid E.size (tag, a, b) := ⟨htag, ops⟩
      have ext := ext_push E (nodeExpr E (tag, a, b))
      have top : (E.push (nodeExpr E (tag, a, b)))[E.size]'(by simp) =
          nodeExpr (E.push (nodeExpr E (tag, a, b))) (tag, a, b) := by
        rw [Array.getElem_push_eq, nodeExpr_ext ext valid (le_refl _)]
      obtain ⟨nbs, len, flat, each⟩ := good.bytes
      refine ⟨rfl, _, ext, ⟨good.enc, good.mod, by simp [good.count], ?_, ?_⟩, ?_⟩
      · refine ⟨nbs ++ [node.data.toList], by simp [len], ?_, ?_⟩
        · simp [ByteArray.data_append, flat]
        · intro j hj
          by_cases lt : j < E.size
          · obtain ⟨k, nb, hk, v, e, bytes⟩ := each j lt
            refine ⟨k, nb, by rw [List.getElem?_append_left (by omega)]; exact hk, v, ?_, bytes⟩
            rw [Array.getElem_push_lt lt, e, nodeExpr_ext ext v (le_of_lt lt)]
          · have : j = E.size := by simp at hj; omega
            subst this
            refine ⟨(tag, a, b), node.data.toList, by simp [len], valid, top, ?_⟩
            exact nb
      · intro k j hk
        simp only [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i hkey
          cases hk
          have := eq_of_beq hkey
          subst this
          rw [good.count]
          exact ⟨by simp, valid, top⟩
        · obtain ⟨hj, v, e⟩ := good.index _ _ hk
          refine ⟨by simp; omega, v, ?_⟩
          rw [Array.getElem_push_lt hj, e, nodeExpr_ext ext v (le_of_lt hj)]
      · rw [good.count]
        exact ⟨by simp, valid, top⟩
    · cases h

/-- Interning `p` into a good pool leaves the outer buffer unchanged and ends at
a good pool whose node `i` expands to `p`. -/
theorem intern_spec {enc : FieldEncoding} {m : Nat} {encode : F → Nat}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m) :
    ∀ (p : ArithExpr F) (E : Array (ArithExpr F)) (s s' : NodePool) (b b' : ByteArray) (i : Nat),
      NodesGood enc m E s → internPolynomial encode p s b = .ok (i, s') b' →
      b' = b ∧ ∃ E', Ext E E' ∧ NodesGood enc m E' s' ∧ Holds E' i p
  | .const x, E, s, s', b, b', i, good, h => by
      obtain ⟨rfl, E', ext, good', hi, _, e⟩ :=
        node_spec good (by decide) (fun _ => hlt x) (by omega) h
      exact ⟨rfl, E', ext, good', hi, by rw [e]; simp [nodeExpr, hcast]⟩
  | .var x, E, s, s', b, b', i, good, h => by
      obtain ⟨rfl, E', ext, good', hi, _, e⟩ :=
        node_spec good (by decide) (by omega) (by omega) h
      exact ⟨rfl, E', ext, good', hi, by rw [e]; simp [nodeExpr]⟩
  | .add x y, E, s, s', b, b', i, good, h => by
      obtain ⟨ia, s₁, b₁, h₁, h⟩ := st_bind_ok h
      obtain ⟨ib, s₂, b₂, h₂, h₃⟩ := st_bind_ok h
      obtain ⟨rfl, E₁, x₁, g₁, hx⟩ := intern_spec hcast hlt x _ _ _ _ _ _ good h₁
      obtain ⟨rfl, E₂, x₂, g₂, hy⟩ := intern_spec hcast hlt y _ _ _ _ _ _ g₁ h₂
      have hx₂ := holds_ext x₂ hx
      obtain ⟨rfl, E₃, x₃, g₃, hi, _, e⟩ :=
        node_spec g₂ (by decide) (by omega) (fun _ => ⟨hx₂.1, hy.1⟩) h₃
      obtain ⟨_, ea⟩ := holds_ext x₃ hx₂
      obtain ⟨_, eb⟩ := holds_ext x₃ hy
      exact ⟨rfl, E₃, ext_trans x₁ (ext_trans x₂ x₃), g₃, hi, by
        rw [e]; simp only [nodeExpr, getD_of ea, getD_of eb]⟩
  | .sub x y, E, s, s', b, b', i, good, h => by
      obtain ⟨ia, s₁, b₁, h₁, h⟩ := st_bind_ok h
      obtain ⟨ib, s₂, b₂, h₂, h₃⟩ := st_bind_ok h
      obtain ⟨rfl, E₁, x₁, g₁, hx⟩ := intern_spec hcast hlt x _ _ _ _ _ _ good h₁
      obtain ⟨rfl, E₂, x₂, g₂, hy⟩ := intern_spec hcast hlt y _ _ _ _ _ _ g₁ h₂
      have hx₂ := holds_ext x₂ hx
      obtain ⟨rfl, E₃, x₃, g₃, hi, _, e⟩ :=
        node_spec g₂ (by decide) (by omega) (fun _ => ⟨hx₂.1, hy.1⟩) h₃
      obtain ⟨_, ea⟩ := holds_ext x₃ hx₂
      obtain ⟨_, eb⟩ := holds_ext x₃ hy
      exact ⟨rfl, E₃, ext_trans x₁ (ext_trans x₂ x₃), g₃, hi, by
        rw [e]; simp only [nodeExpr, getD_of ea, getD_of eb]⟩
  | .mul x y, E, s, s', b, b', i, good, h => by
      obtain ⟨ia, s₁, b₁, h₁, h⟩ := st_bind_ok h
      obtain ⟨ib, s₂, b₂, h₂, h₃⟩ := st_bind_ok h
      obtain ⟨rfl, E₁, x₁, g₁, hx⟩ := intern_spec hcast hlt x _ _ _ _ _ _ good h₁
      obtain ⟨rfl, E₂, x₂, g₂, hy⟩ := intern_spec hcast hlt y _ _ _ _ _ _ g₁ h₂
      have hx₂ := holds_ext x₂ hx
      obtain ⟨rfl, E₃, x₃, g₃, hi, _, e⟩ :=
        node_spec g₂ (by decide) (by omega) (fun _ => ⟨hx₂.1, hy.1⟩) h₃
      obtain ⟨_, ea⟩ := holds_ext x₃ hx₂
      obtain ⟨_, eb⟩ := holds_ext x₃ hy
      exact ⟨rfl, E₃, ext_trans x₁ (ext_trans x₂ x₃), g₃, hi, by
        rw [e]; simp only [nodeExpr, getD_of ea, getD_of eb]⟩

/-- Every successful run of the pool writer `p` from a good pool `E` ends at a
good pool `E' ⊒ E` and appends bytes (at least one if `ne`) that `G Ef` reads
as `x` for every `Ef ⊒ E'`. -/
def RTP {α : Type} (ne : Bool) (enc : FieldEncoding) (m : Nat) (p : PoolM Unit)
    (G : Array (ArithExpr F) → GetM α) (x : α) : Prop :=
  ∀ E s b s' b', NodesGood enc m E s → p s b = .ok ((), s') b' →
    ∃ (E' : Array (ArithExpr F)) (e : List UInt8), Ext E E' ∧ NodesGood enc m E' s' ∧ b' = b ++ ⟨e.toArray⟩ ∧
      (ne = true → e ≠ []) ∧ ∀ Ef, Ext E' Ef → Reads (G Ef) e x

section RTP

variable {α β : Type} {enc : FieldEncoding} {m : Nat}

theorem RTP.weaken {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α} {x : α}
    (h : RTP n enc m p G x) : RTP false enc m p G x := by
  intro E s b s' b' good hp
  obtain ⟨E', e, x', g', he, _, r⟩ := h E s b s' b' good hp
  exact ⟨E', e, x', g', he, by simp, r⟩

theorem rtp_bind {n₁ n₂ : Bool} {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {x : α} {y : β}
    (hp : RTP n₁ enc m p G x) (hq : RTP n₂ enc m q (fun E => K E x) y) :
    RTP (n₁ || n₂) enc m (p >>= fun _ => q) (fun E => G E >>= K E) y := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨E₁, e₁, x₁, g₁, rfl, ne₁, r₁⟩ := hp _ _ _ _ _ good h₁
  obtain ⟨E₂, e₂, x₂, g₂, rfl, ne₂, r₂⟩ := hq _ _ _ _ _ g₁ h₂
  refine ⟨E₂, e₁ ++ e₂, ext_trans x₁ x₂, g₂, append_assoc' .., ?_, fun Ef xf =>
    reads_bind (r₁ Ef (ext_trans x₂ xf)) (r₂ Ef xf)⟩
  intro hn
  rcases Bool.or_eq_true_iff.mp hn with h | h
  · simp [ne₁ h]
  · simp [ne₂ h]

theorem rtp_map {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {x : α} {y : β}
    (hp : RTP n enc m p G x) (hK : ∀ E, K E x = pure y) :
    RTP n enc m p (fun E => G E >>= K E) y := by
  intro E s b s' b' good h
  obtain ⟨E', e, x', g', he, ne, r⟩ := hp E s b s' b' good h
  refine ⟨E', e, x', g', he, ne, fun Ef xf => ?_⟩
  have := reads_bind (e₂ := []) (r Ef xf) ((hK Ef).symm ▸ reads_pure y)
  simpa using this

theorem rtp_pure_end {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α} {x : α}
    (hp : RTP n enc m p G x) : RTP n enc m (p >>= fun _ => pure ()) G x := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨he, rfl⟩ := pool_pure h₂
  cases he
  exact hp _ _ _ _ _ good h₁

theorem lift_ok {p : PutM Unit} {s : NodePool} {b b' : ByteArray} {r : Unit × NodePool}
    (h : (monadLift p : PoolM Unit) s b = .ok r b') : p b = .ok () b' ∧ r = ((), s) := by
  change (EStateM.bind p fun a => EStateM.pure (a, s)) b = _ at h
  simp only [EStateM.bind] at h
  split at h
  · rename_i u b₁ hb
    simp only [EStateM.pure, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hb, rfl⟩
  · cases h

theorem rtp_lift {p : PutM Unit} {g : GetM α} {x : α} (h : RT1 p g x) :
    RTP true enc m (monadLift p : PoolM Unit) (fun _ : Array (ArithExpr F) => g) x := by
  intro E s b s' b' good hp
  obtain ⟨hp', he⟩ := lift_ok hp
  cases he
  obtain ⟨e, rfl, ne, r⟩ := h b b' hp'
  exact ⟨E, e, ext_refl E, good, rfl, fun _ => ne, fun _ _ => r⟩

theorem rtp_unless {n : Bool} {c : Bool} {msg : String} {q : PoolM Unit}
    {G : Array (ArithExpr F) → GetM α} {x : α} (hq : c = true → RTP n enc m q G x) :
    RTP n enc m ((unless c do throw msg) >>= fun _ => q) G x := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  cases hc : c
  · rw [hc] at h₁
    exact (pool_throw h₁).elim
  · rw [hc] at h₁
    obtain ⟨he, rfl⟩ := pool_pure h₁
    cases he
    exact hq hc _ _ _ _ _ good h₂

/-- A `for` loop over `xs` whose body runs `item x` and continues. -/
theorem forIn_rtp {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β} {f : α → β} :
    ∀ (xs : List α), (∀ x ∈ xs, RTP true enc m (item x) G (f x)) →
    ∀ E s b s' b', NodesGood enc m E s →
      forIn xs PUnit.unit (fun x _ => item x >>= fun _ => pure (ForInStep.yield PUnit.unit)) s b =
        .ok ((), s') b' →
      ∃ (E' : Array (ArithExpr F)) (encs : List (List UInt8 × β)), Ext E E' ∧ NodesGood enc m E' s' ∧
        encs.map Prod.snd = xs.map f ∧ b' = b ++ ⟨(encs.flatMap Prod.fst).toArray⟩ ∧
        ∀ Ef, Ext E' Ef → ∀ q ∈ encs, q.1 ≠ [] ∧ Reads (G Ef) q.1 q.2
  | [], _, E, s, b, s', b', good, h => by
      simp only [List.forIn_nil] at h
      obtain ⟨he, rfl⟩ := pool_pure h
      cases he
      exact ⟨E, [], ext_refl E, good, rfl, by apply ByteArray.ext; simp [ByteArray.data_append],
        by simp⟩
  | x :: xs, hall, E, s, b, s', b', good, h => by
      simp only [List.forIn_cons] at h
      obtain ⟨step, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
      obtain ⟨_, s₀, b₀, h₀, h₃⟩ := st_bind_ok h₁
      obtain ⟨he, rfl⟩ := pool_pure h₃
      cases he
      obtain ⟨E₁, e, x₁, g₁, rfl, ne, r⟩ := hall x (List.mem_cons_self ..) _ _ _ _ _ good h₀
      obtain ⟨E₂, encs, x₂, g₂, hm, rfl, rs⟩ := forIn_rtp xs
        (fun y hy => hall y (List.mem_cons_of_mem _ hy)) _ _ _ _ _ g₁ h₂
      refine ⟨E₂, (e, f x) :: encs, ext_trans x₁ x₂, g₂, by simp [hm], by
        rw [List.flatMap_cons, append_assoc'], fun Ef xf q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨ne rfl, r Ef (ext_trans x₂ xf)⟩
      · exact rs Ef xf q hq

theorem rtp_listP {xs : List α} {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β}
    {f : α → β} (h : ∀ x ∈ xs, RTP true enc m (item x) G (f x)) :
    RTP true enc m (listP xs item) (fun E => getList (G E)) (xs.map f) := by
  intro E s b s' b' good hrun
  unfold listP at hrun
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok hrun
  obtain ⟨h₁', he⟩ := lift_ok h₁
  cases he
  obtain ⟨_, s₂, b₂, h₂, h₃⟩ := st_bind_ok h₂
  obtain ⟨he, rfl⟩ := pool_pure h₃
  cases he
  have len := nat_ok h₁'
  have w := nat_writes _ _ _ h₁'
  subst w
  obtain ⟨E', encs, x', g', hm, rfl, rs⟩ := forIn_rtp xs h _ _ _ _ _ good h₂
  have elen : encs.length = xs.length := by
    have := congrArg List.length hm
    simpa using this
  refine ⟨E', tagBytes xs.length ++ encs.flatMap Prod.fst, x', g', by rw [append_assoc'],
    fun _ => by simp [tagBytes_ne_nil], fun Ef xf => ?_⟩
  have r := getList_reads (g := G Ef) encs (fun q hq => (rs Ef xf q hq).2)
    (fun q hq => (rs Ef xf q hq).1) (by rw [elen]; exact len)
  rw [elen, hm] at r
  exact r

theorem rtp_arrayP {xs : Array α} {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β}
    {f : α → β} (h : ∀ x ∈ xs, RTP true enc m (item x) G (f x)) :
    RTP true enc m (arrayP xs item) (fun E => getList (G E)) (xs.toList.map f) := by
  have e : arrayP xs item = listP xs.toList item := by
    simp only [arrayP, listP, Array.length_toList, Array.forIn_toList]
  rw [e]
  exact rtp_listP fun x hx => h x (Array.mem_toList_iff.mp hx)

theorem rtp_poly {encode : F → Nat} (hcast : ∀ x, ((encode x : Nat) : F) = x)
    (hlt : ∀ x, encode x < m) (p : ArithExpr F) :
    RTP true enc m (putPolynomial encode p) getPoly p := by
  intro E s b s' b' good h
  unfold putPolynomial at h
  obtain ⟨i, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨rfl, E', x', g', hi, e⟩ := intern_spec hcast hlt p _ _ _ _ _ _ good h₁
  obtain ⟨h₂', he⟩ := lift_ok h₂
  cases he
  obtain ⟨enc', rfl, ne, r⟩ := rt1_nat i _ _ h₂'
  refine ⟨E', enc', x', g', rfl, fun _ => ne, fun Ef xf => ?_⟩
  obtain ⟨hf, ef⟩ := holds_ext xf ⟨hi, e⟩
  unfold getPoly
  refine reads_congr (reads_bind (e₂ := []) r ?_) (by simp)
  simp only [Array.getElem?_eq_getElem hf, ef]
  exact reads_pure p

theorem rtp_skip {n : Bool} {p : PoolM Unit} {g : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {z : α} {y : β}
    (hg : ∀ E, Reads (g E) [] z) (hp : RTP n enc m p (fun E => K E z) y) :
    RTP n enc m p (fun E => g E >>= K E) y := by
  intro E s b s' b' good h
  obtain ⟨E', e, x', g', he, ne, r⟩ := hp E s b s' b' good h
  exact ⟨E', e, x', g', he, ne, fun Ef xf => reads_bind (hg Ef) (r Ef xf)⟩

theorem rtp_last {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α} {x : α}
    (hp : RTP n enc m p G x) : RTP n enc m p (fun E => G E >>= fun a => pure a) x :=
  rtp_map hp fun _ => rfl

theorem rtp_cons {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {x : α} {y : β}
    (hp : RTP true enc m p G x) (hq : RTP false enc m q (fun E => K E x) y) :
    RTP true enc m (p >>= fun _ => q) (fun E => G E >>= K E) y :=
  rtp_bind hp hq

theorem rtp_then {n₁ : Bool} {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {x : α} {y : β}
    (hp : RTP n₁ enc m p G x) (hq : RTP false enc m q (fun E => K E x) y) :
    RTP false enc m (p >>= fun _ => q) (fun E => G E >>= K E) y :=
  (rtp_bind hp hq).weaken

/-- `RTP` for a reader whose value is not tracked: every successful run of `p`
appends bytes that `G Ef` reads as some value fixed by the run. -/
def RTE (ne : Bool) (enc : FieldEncoding) (m : Nat) (p : PoolM Unit)
    (G : Array (ArithExpr F) → GetM α) : Prop :=
  ∀ E s b s' b', NodesGood enc m E s → p s b = .ok ((), s') b' →
    ∃ (E' : Array (ArithExpr F)) (e : List UInt8) (x : α), Ext E E' ∧ NodesGood enc m E' s' ∧
      b' = b ++ ⟨e.toArray⟩ ∧ (ne = true → e ≠ []) ∧ ∀ Ef, Ext E' Ef → Reads (G Ef) e x

theorem RTP.rte {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α} {x : α}
    (h : RTP n enc m p G x) : RTE n enc m p G := by
  intro E s b s' b' good hp
  obtain ⟨E', e, x', g', he, ne, r⟩ := h E s b s' b' good hp
  exact ⟨E', e, x, x', g', he, ne, r⟩

theorem rte_bind {n₁ n₂ : Bool} {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β}
    (hp : RTE n₁ enc m p G) (hq : ∀ x, RTE n₂ enc m q (fun E => K E x)) :
    RTE (n₁ || n₂) enc m (p >>= fun _ => q) (fun E => G E >>= K E) := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨E₁, e₁, x, x₁, g₁, rfl, ne₁, r₁⟩ := hp _ _ _ _ _ good h₁
  obtain ⟨E₂, e₂, y, x₂, g₂, rfl, ne₂, r₂⟩ := hq x _ _ _ _ _ g₁ h₂
  refine ⟨E₂, e₁ ++ e₂, y, ext_trans x₁ x₂, g₂, append_assoc' .., ?_, fun Ef xf =>
    reads_bind (r₁ Ef (ext_trans x₂ xf)) (r₂ Ef xf)⟩
  intro hn
  rcases Bool.or_eq_true_iff.mp hn with h | h
  · simp [ne₁ h]
  · simp [ne₂ h]

theorem RTE.weaken {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    (h : RTE n enc m p G) : RTE false enc m p G := by
  intro E s b s' b' good hp
  obtain ⟨E', e, x, x', g', he, _, r⟩ := h E s b s' b' good hp
  exact ⟨E', e, x, x', g', he, by simp, r⟩

theorem rte_cons {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β}
    (hp : RTE true enc m p G) (hq : ∀ x, RTE false enc m q (fun E => K E x)) :
    RTE true enc m (p >>= fun _ => q) (fun E => G E >>= K E) :=
  rte_bind hp hq

theorem rte_then {n : Bool} {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β}
    (hp : RTE n enc m p G) (hq : ∀ x, RTE false enc m q (fun E => K E x)) :
    RTE false enc m (p >>= fun _ => q) (fun E => G E >>= K E) :=
  (rte_bind hp hq).weaken

theorem rte_map {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : α → β} (hp : RTE n enc m p G) :
    RTE n enc m p (fun E => G E >>= fun a => pure (K a)) := by
  intro E s b s' b' good h
  obtain ⟨E', e, x, x', g', he, ne, r⟩ := hp E s b s' b' good h
  refine ⟨E', e, K x, x', g', he, ne, fun Ef xf => ?_⟩
  exact reads_congr (reads_bind (e₂ := []) (r Ef xf) (reads_pure (K x))) (by simp)

theorem rte_unless {n : Bool} {c : Bool} {msg : String} {q : PoolM Unit}
    {G : Array (ArithExpr F) → GetM α} (hq : c = true → RTE n enc m q G) :
    RTE n enc m ((unless c do throw msg) >>= fun _ => q) G := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  cases hc : c
  · rw [hc] at h₁
    exact (pool_throw h₁).elim
  · rw [hc] at h₁
    obtain ⟨he, rfl⟩ := pool_pure h₁
    cases he
    exact hq hc _ _ _ _ _ good h₂

theorem forIn_rte {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β} :
    ∀ (xs : List α), (∀ x ∈ xs, RTE true enc m (item x) G) →
    ∀ E s b s' b', NodesGood enc m E s →
      forIn xs PUnit.unit (fun x _ => item x >>= fun _ => pure (ForInStep.yield PUnit.unit)) s b =
        .ok ((), s') b' →
      ∃ (E' : Array (ArithExpr F)) (encs : List (List UInt8 × β)), Ext E E' ∧ NodesGood enc m E' s' ∧
        encs.length = xs.length ∧ b' = b ++ ⟨(encs.flatMap Prod.fst).toArray⟩ ∧
        ∀ Ef, Ext E' Ef → ∀ q ∈ encs, q.1 ≠ [] ∧ Reads (G Ef) q.1 q.2
  | [], _, E, s, b, s', b', good, h => by
      simp only [List.forIn_nil] at h
      obtain ⟨he, rfl⟩ := pool_pure h
      cases he
      exact ⟨E, [], ext_refl E, good, rfl, by apply ByteArray.ext; simp [ByteArray.data_append],
        by simp⟩
  | x :: xs, hall, E, s, b, s', b', good, h => by
      simp only [List.forIn_cons] at h
      obtain ⟨step, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
      obtain ⟨_, s₀, b₀, h₀, h₃⟩ := st_bind_ok h₁
      obtain ⟨he, rfl⟩ := pool_pure h₃
      cases he
      obtain ⟨E₁, e, v, x₁, g₁, rfl, ne, r⟩ := hall x (List.mem_cons_self ..) _ _ _ _ _ good h₀
      obtain ⟨E₂, encs, x₂, g₂, hm, rfl, rs⟩ := forIn_rte xs
        (fun y hy => hall y (List.mem_cons_of_mem _ hy)) _ _ _ _ _ g₁ h₂
      refine ⟨E₂, (e, v) :: encs, ext_trans x₁ x₂, g₂, by simp [hm], by
        rw [List.flatMap_cons, append_assoc'], fun Ef xf q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨ne rfl, r Ef (ext_trans x₂ xf)⟩
      · exact rs Ef xf q hq

theorem rte_listP {xs : List α} {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β}
    (h : ∀ x ∈ xs, RTE true enc m (item x) G) :
    RTE true enc m (listP xs item) (fun E => getList (G E)) := by
  intro E s b s' b' good hrun
  unfold listP at hrun
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok hrun
  obtain ⟨h₁', he⟩ := lift_ok h₁
  cases he
  obtain ⟨_, s₂, b₂, h₂, h₃⟩ := st_bind_ok h₂
  obtain ⟨he, rfl⟩ := pool_pure h₃
  cases he
  have len := nat_ok h₁'
  have w := nat_writes _ _ _ h₁'
  subst w
  obtain ⟨E', encs, x', g', elen, rfl, rs⟩ := forIn_rte xs h _ _ _ _ _ good h₂
  refine ⟨E', tagBytes xs.length ++ encs.flatMap Prod.fst, encs.map Prod.snd, x', g',
    by rw [append_assoc'], fun _ => by simp [tagBytes_ne_nil], fun Ef xf => ?_⟩
  have r := getList_reads (g := G Ef) encs (fun q hq => (rs Ef xf q hq).2)
    (fun q hq => (rs Ef xf q hq).1) (by rw [elen]; exact len)
  rw [elen] at r
  exact r

theorem rte_arrayP {xs : Array α} {item : α → PoolM Unit} {G : Array (ArithExpr F) → GetM β}
    (h : ∀ x ∈ xs, RTE true enc m (item x) G) :
    RTE true enc m (arrayP xs item) (fun E => getList (G E)) := by
  have e : arrayP xs item = listP xs.toList item := by
    simp only [arrayP, listP, Array.length_toList, Array.forIn_toList]
  rw [e]
  exact rte_listP fun x hx => h x (Array.mem_toList_iff.mp hx)

theorem rte_consp {n : Bool} {p q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    {K : Array (ArithExpr F) → α → GetM β} {x : α}
    (hp : RTP true enc m p G x) (hq : RTE n enc m q (fun E => K E x)) :
    RTE true enc m (p >>= fun _ => q) (fun E => G E >>= K E) := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨E₁, e₁, x₁, g₁, rfl, ne₁, r₁⟩ := hp _ _ _ _ _ good h₁
  obtain ⟨E₂, e₂, y, x₂, g₂, rfl, _, r₂⟩ := hq _ _ _ _ _ g₁ h₂
  exact ⟨E₂, e₁ ++ e₂, y, ext_trans x₁ x₂, g₂, append_assoc' .., fun _ => by simp [ne₁ rfl],
    fun Ef xf => reads_bind (r₁ Ef (ext_trans x₂ xf)) (r₂ Ef xf)⟩

theorem rte_tagged {M : Array (ArithExpr F) → Nat → GetM α} {what : String} {count : Nat} {tag : UInt8}
    (htag : tag.toNat < count) {q : PoolM Unit} (hq : RTE false enc m q (fun E => M E tag.toNat)) :
    RTE true enc m ((monadLift (u8 tag) : PoolM Unit) >>= fun _ => q) (fun E => getTag what count >>= M E) :=
  rte_consp (rtp_lift (rt1_tag what tag htag)) hq

theorem rte_last {n : Bool} {p : PoolM Unit} {G : Array (ArithExpr F) → GetM α} {K : α → β}
    (hp : RTE n enc m p G) : RTE false enc m p (fun E => G E >>= fun a => pure (K a)) :=
  (rte_map hp).weaken

/-- A writer step that only checks: it leaves the pool and the buffer unchanged. -/
theorem rte_pure_bind {R : Type} {n : Bool} {w : PoolM R} {q : R → PoolM Unit}
    {G : Array (ArithExpr F) → GetM α}
    (hw : ∀ s b r s' b', w s b = .ok (r, s') b' → s' = s ∧ b' = b) (hq : ∀ r, RTE n enc m (q r) G) :
    RTE n enc m (w >>= q) G := by
  intro E s b s' b' good h
  obtain ⟨r, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨rfl, rfl⟩ := hw _ _ _ _ _ h₁
  exact hq r _ _ _ _ _ good h₂

theorem ofExcept_pool {R : Type} (x : Except String R) :
    ∀ s b r s' b', (MonadExcept.ofExcept x : PoolM R) s b = .ok (r, s') b' → s' = s ∧ b' = b := by
  intro s b r s' b' h
  cases x <;> simp_all [MonadExcept.ofExcept, pure, StateT.pure, EStateM.pure, throw, throwThe,
    MonadExceptOf.throw, StateT.lift, EStateM.throw, bind, EStateM.bind]


theorem rte_throw {n : Bool} {msg : String} {G : Array (ArithExpr F) → GetM α} :
    RTE n enc m (throw msg : PoolM Unit) G := by
  intro E s b s' b' _ h
  exact (pool_throw h).elim

theorem rte_pure_seq {n : Bool} {q : PoolM Unit} {G : Array (ArithExpr F) → GetM α}
    (hq : RTE n enc m q G) : RTE n enc m ((pure () : PoolM Unit) >>= fun _ => q) G := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
  obtain ⟨he, rfl⟩ := pool_pure h₁
  cases he
  exact hq _ _ _ _ _ good h₂

theorem rte_throw_seq {n : Bool} {msg : String} {f : PUnit → PoolM Unit}
    {G : Array (ArithExpr F) → GetM α} : RTE n enc m ((throw msg : PoolM PUnit) >>= f) G := by
  intro E s b s' b' good h
  obtain ⟨_, s₁, b₁, h₁, _⟩ := st_bind_ok h
  exact (pool_throw h₁).elim

end RTP

/-! ## Records -/

section Records

variable {enc : FieldEncoding} {m : Nat} {encode : F → Nat}

/-- A chip record whose width is its activation column plus one reads back. -/
theorem rtp_chip (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (x : IChip F) (hw : x.width = x.activation + 1) :
    RTP true enc m (putIChip encode x) getChipRecord x := by
  have poly := rtp_poly (enc := enc) hcast hlt
  unfold putIChip getChipRecord
  refine rtp_cons (rtp_lift (rt1_str _)) (rtp_then (rtp_lift (rt1_nat _)) (rtp_then (rtp_lift (rt1_nat _)) ?_))
  simp only [show (x.width == x.activation + 1) = true by simp [hw], ↓reduceIte, pure_bind]
  refine rtp_then (rtp_lift (rt1_nats _)) ?_
  refine rtp_then (rtp_listP (f := id) fun p _ => poly p) ?_
  refine rtp_then (rtp_listP (f := id) fun p _ => poly p) ?_
  refine rtp_then (rtp_listP (f := id) fun s _ => ?_) ?_
  · exact rtp_cons (rtp_lift (rt1_str _)) (rtp_then (rtp_listP (f := id) fun p _ => poly p)
      (rtp_then (rtp_lift (rt1_nats _)) (rtp_map (poly _) fun _ => by simp).weaken))
  refine (rtp_map (rtp_listP (f := id) fun c _ => ?_) fun _ => ?_).weaken
  · exact rtp_cons (rtp_lift (rt1_ty _)) (rtp_then (poly _) (rtp_then (rtp_listP (f := id) fun p _ => poly p)
      (rtp_map (poly _) fun _ => by simp).weaken))
  · simp

theorem rte_op (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (hintPCs : List Nat) (op : Operation F) :
    RTE true enc m (putOperation encode hintPCs op) (getIOp (F := F)) := by
  have poly : ∀ p, RTE true enc m (putPolynomial encode p) getPoly := fun p =>
    (rtp_poly (enc := enc) hcast hlt p).rte
  have polys : ∀ ps : List (ArithExpr F), RTE true enc m (listP ps (putPolynomial encode)) getPolys :=
    fun ps => (rtp_listP (xs := ps) (f := id) fun p _ => rtp_poly (enc := enc) hcast hlt p).rte
  have nats : ∀ xs, RTE true enc m (monadLift (nats xs) : PoolM Unit) (fun _ : Array (ArithExpr F) => getNats) := fun xs =>
    (rtp_lift (rt1_nats xs)).rte
  have nat1 : ∀ x, RTE true enc m (monadLift (nat x) : PoolM Unit) (fun _ : Array (ArithExpr F) => getNat) := fun x =>
    (rtp_lift (rt1_nat x)).rte
  have ty : ∀ t, RTE true enc m (monadLift (putTy t) : PoolM Unit) (fun _ : Array (ArithExpr F) => getTy) := fun t =>
    (rtp_lift (rt1_ty t)).rte
  have str1 : ∀ x, RTE true enc m (monadLift (str x) : PoolM Unit) (fun _ : Array (ArithExpr F) => getString) := fun x =>
    (rtp_lift (rt1_str x)).rte
  cases op with
  | assign dest values =>
      exact rte_tagged (tag := 0) (by decide) (rte_then (nats dest) fun _ => rte_last (polys _))
  | inverse dest value =>
      exact rte_tagged (tag := 1) (by decide) (rte_then (nat1 dest) fun _ => rte_last (poly _))
  | choose dest tests =>
      exact rte_tagged (tag := 2) (by decide) (rte_then (nats dest) fun _ =>
        rte_last (rte_listP fun t _ => polys t))
  | failure dest differences =>
      exact rte_tagged (tag := 3) (by decide) (rte_then (nats dest) fun _ => rte_last (polys _))
  | call name args dest =>
      exact rte_tagged (tag := 4) (by decide) (rte_then (str1 name) fun _ =>
        rte_then (polys args) fun _ => rte_last (nats dest))
  | store type values dest =>
      exact rte_tagged (tag := 5) (by decide) (rte_then (ty type) fun _ =>
        rte_then (polys values) fun _ => rte_last (nat1 dest))
  | load type address dest =>
      exact rte_tagged (tag := 6) (by decide) (rte_then (ty type) fun _ =>
        rte_then (poly address) fun _ => rte_last (nats dest))
  | hint site type keyType key dest channel =>
      cases hpc : hintPCs[site]? with
      | none => simp only [putOperation, hpc]; exact rte_throw
      | some pc =>
          simp only [putOperation, hpc]
          exact rte_tagged (tag := 7) (by decide) (rte_then (str1 channel) fun _ =>
            rte_then (nat1 pc) fun _ => rte_then (ty type) fun _ => rte_then (ty keyType) fun _ =>
            rte_then (polys key) fun _ => rte_last (nats dest))

theorem rte_group (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (g : IGroup F) : RTE true enc m (putIGroup encode g) (getIGroup (F := F)) := by
  have poly : ∀ p, RTE true enc m (putPolynomial encode p) getPoly := fun p =>
    (rtp_poly (enc := enc) hcast hlt p).rte
  have polys : ∀ ps : List (ArithExpr F), RTE true enc m (listP ps (putPolynomial encode)) getPolys :=
    fun ps => (rtp_listP (xs := ps) (f := id) fun p _ => rtp_poly (enc := enc) hcast hlt p).rte
  have nat1 : ∀ x, RTE true enc m (monadLift (nat x) : PoolM Unit)
      (fun _ : Array (ArithExpr F) => getNat) := fun x => (rtp_lift (rt1_nat x)).rte
  have str1 : ∀ x, RTE true enc m (monadLift (str x) : PoolM Unit)
      (fun _ : Array (ArithExpr F) => getString) := fun x => (rtp_lift (rt1_str x)).rte
  unfold putIGroup getIGroup
  refine rte_cons (str1 _) fun _ => rte_then (nat1 _) fun _ => rte_then (poly _) fun _ =>
    rte_then (polys _) fun _ => rte_then (polys _) fun _ => ?_
  refine rte_then (rte_listP fun se _ => ?_) fun _ => rte_last (rte_listP fun mb _ => ?_)
  · obtain ⟨en, args⟩ := se
    exact rte_cons (poly _) fun _ => rte_last (polys _)
  · refine rte_cons (str1 _) fun _ => rte_then (rtp_lift (rt1_array (f := id) fun c _ => rt1_nat c)).rte
      fun _ => rte_then (nat1 _) fun _ => rte_last (rte_listP fun w _ => ?_)
    obtain ⟨c, v⟩ := w
    exact rte_cons (nat1 _) fun _ => rte_last (poly _)

end Records

/-- The slots of `d` have kinds below 4 and a column exactly for kinds 2 and 3. -/
def IDepth.Valid (d : IDepth) : Prop :=
  ∀ s ∈ d.slots, s.1 < 4 ∧ s.2 = if 2 ≤ s.1 then some (s.2.getD 0) else none

theorem rt1_depth (d : IDepth) (hd : d.Valid) : RT1 (putIDepth d) getIDepth d := by
  unfold putIDepth getIDepth
  refine rt1_bind_l (rt1_option (f := id) fun c _ => rt1_nat c) (rt_bind (rt1_nat _).rt ?_)
  refine rt_map (rt1_list (f := id) fun s hs => ?_).rt ?_
  · obtain ⟨kind, column⟩ := s
    obtain ⟨lt, hc⟩ := hd _ hs
    have tag := rt1_tag "depth slot" (count := 4) kind.toUInt8 (by rw [u8_toNat (by omega)]; exact lt)
    rw [u8_toNat (by omega)] at tag
    refine rt1_bind_l tag ?_
    by_cases two : 2 ≤ kind
    · simp only [two, ↓reduceIte] at hc ⊢
      refine rt_map (rt1_nat _).rt ?_
      cases column
      · cases hc
      · rfl
    · simp only [two, ↓reduceIte] at hc ⊢
      subst hc
      exact rt_pure _
  · simp

omit [NatCast F] in
theorem depth_valid (cfg : Optimized.Depth.Config) (source : Chip F) :
    (IDepth.of cfg source).Valid := by
  intro s hs
  simp only [IDepth.of, List.mem_map] at hs
  obtain ⟨⟨kind, column⟩, _, rfl⟩ := hs
  cases kind <;> simp [slotCode]

/-! ## Reading the pool -/

/-- `getNodes`' loop, from node `j` on, over per-node bytes `nbs`. -/
theorem loop_idx_reads {A : Type} {f : Nat → Array A → GetM (ForInStep (Array A))} (E : Array A)
    (nbs : List (List UInt8)) (hlen : nbs.length = E.size)
    (step : ∀ j (hj : j < E.size), Reads (f j (E.extract 0 j)) (nbs[j]'(by omega))
      (.yield ((E.extract 0 j).push E[j]))) :
    ∀ d j, j + d = E.size → Reads (forIn (List.range' j d) (E.extract 0 j) f) (nbs.drop j).flatten E
  | 0, j, h => by
      have e : E.extract 0 j = E := by simp [show j = E.size by omega]
      have d : nbs.drop j = [] := by simp [hlen]; omega
      rw [e, d]
      exact reads_pure E
  | d + 1, j, h => by
      have hj : j < E.size := by omega
      have rest := loop_idx_reads E nbs hlen step d (j + 1) (by omega)
      have push : (E.extract 0 j).push E[j] = E.extract 0 (j + 1) := by
        apply Array.ext
        · simp
        · intro i h₁ h₂
          simp only [Array.size_push, Array.size_extract] at h₁
          by_cases lt : i < j
          · rw [Array.getElem_push_lt (by simp; omega)]
            simp
          · have : i = j := by simp at h₁; omega
            subst this
            simp
      have st := step j hj
      rw [push] at st
      have drop : (nbs.drop j).flatten = nbs[j]'(by omega) ++ (nbs.drop (j + 1)).flatten := by
        rw [List.drop_eq_getElem_cons (by omega), List.flatten_cons]
      rw [List.range'_succ, List.forIn_cons, drop]
      exact reads_bind st rest

theorem loop_run {A : Type} {f : Nat → Array A → GetM (ForInStep (Array A))} (E : Array A)
    (nbs : List (List UInt8)) (hlen : nbs.length = E.size)
    (step : ∀ j (hj : j < E.size), Reads (f j (E.extract 0 j)) (nbs[j]'(by omega))
      (.yield ((E.extract 0 j).push E[j]))) {bs : ByteArray} {p : Nat} (h : At bs p nbs.flatten) :
    forIn (List.range' 0 E.size) (Array.mkEmpty E.size) f ⟨bs, p⟩ = .ok E ⟨bs, p + nbs.flatten.length⟩ := by
  have := reads_run (loop_idx_reads E nbs hlen step E.size 0 (by simp)) h
  simpa using this

theorem nodeBytes_ne {wide : Bool} {m i : Nat} {k : Nat × Nat × Nat} {nb : List UInt8}
    (h : NodeBytes wide m i k nb) : nb ≠ [] := by
  obtain ⟨tag, a, b⟩ := k
  match tag, h with
  | 0, ⟨_, e, h, _⟩ => simp [h]
  | 1, ⟨h, _⟩ => simp [h]
  | t + 2, ⟨h, _⟩ => simp [h]

set_option maxRecDepth 100000 in
/-- `getNodes` reads a good pool's count and bytes back as its expansions. -/
theorem getNodes_reads {enc : FieldEncoding} {m : Nat} {E : Array (ArithExpr F)} {s : NodePool}
    (good : NodesGood enc m E s) (size : E.size < 2 ^ 64) :
    Reads (getNodes (F := F) (enc == .wide) m) (tagBytes E.size ++ s.bytes.data.toList) E := by
  obtain ⟨nbs, len, flat, each⟩ := good.bytes
  intro bs pos h
  obtain ⟨h₁, h₂⟩ := at_append h
  have r₁ := reads_run (getNat_reads size) h₁
  rw [flat] at h₂
  have room := at_le h₂
  have count : E.size ≤ nbs.flatten.length := by
    rw [← len]
    have ne : ∀ nb ∈ nbs, nb ≠ [] := by
      intro nb hm
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
      obtain ⟨k, nb', h', _, _, bytes⟩ := each i (by omega)
      rw [List.getElem?_eq_getElem hi] at h'
      cases h'
      exact nodeBytes_ne bytes
    clear each flat len h h₂ room r₁ h₁
    induction nbs with
    | nil => simp
    | cons x xs ih =>
        have := ne x (List.mem_cons_self ..)
        have := ih (fun y hy => ne y (List.mem_cons_of_mem _ hy))
        have : x.length ≠ 0 := by simpa using ne x (List.mem_cons_self ..)
        simp only [List.length_cons, List.flatten_cons, List.length_append]
        omega
  have fits : E.size ≤ bs.size - (pos + (tagBytes E.size).length) := by omega
  simp only [EStateM.run, getNodes, getCount, bind, EStateM.bind, r₁, remaining, get, getThe,
    MonadStateOf.get, EStateM.get, fits, ↓reduceIte, pure, EStateM.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [loop_run E nbs len ?step h₂]
  · simp [flat, Nat.add_assoc]
  · intro j hj
    obtain ⟨⟨tag, a, b⟩, nb, hnb, v, e, bytes⟩ := each j hj
    rw [List.getElem?_eq_getElem (by omega)] at hnb
    cases hnb
    try dsimp only
    rcases tag with _ | _ | t
    · obtain ⟨ha, e', hn, re⟩ := bytes
      rw [hn]
      refine reads_congr (reads_bind (e₁ := [0]) (getTag_reads "node" (x := 0) (count := 5) (by decide)) ?_) rfl
      simp only [show UInt8.toNat 0 = 0 from rfl, beq_self_eq_true, ↓reduceIte]
      rw [e]
      refine reads_congr (reads_bind (e₂ := []) re ?_) (by simp)
      simp only [ha, ↓reduceIte, nodeExpr]
      exact reads_pure _
    · obtain ⟨hn, ha⟩ := bytes
      rw [hn]
      refine reads_congr (reads_bind (e₁ := [1]) (getTag_reads "node" (x := 1) (count := 5) (by decide)) ?_) rfl
      simp only [show UInt8.toNat 1 = 1 from rfl, beq_self_eq_true, ↓reduceIte,
        show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true]
      rw [e]
      refine reads_congr (reads_bind (e₂ := []) (getNat_reads ha) ?_) (List.append_nil _)
      simp only [nodeExpr]
      exact reads_pure _
    · obtain ⟨hn, ha, hb⟩ := bytes
      obtain ⟨lt5, ops⟩ := v
      obtain ⟨oa, ob⟩ := ops (by omega)
      rw [hn]
      have tag := getTag_reads "node" (x := (t + 2).toUInt8) (count := 5) (by rw [u8_toNat (by omega)]; exact lt5)
      rw [u8_toNat (by omega)] at tag
      refine reads_congr (reads_bind (e₁ := [(t + 2).toUInt8]) tag ?_) rfl
      simp only [show ((t + 2 : Nat) == 0) = false by simp, show ((t + 2 : Nat) == 1) = false by simp,
        Bool.false_eq_true, ↓reduceIte]
      refine reads_bind (getNat_reads ha) (reads_congr (reads_bind (e₂ := []) (getNat_reads hb) ?_) (by simp))
      have c : (decide (1 ≤ j - a) && decide (j - a ≤ j) && decide (1 ≤ j - b) && decide (j - b ≤ j)) = true := by
        simp; omega
      simp only [c, ↓reduceIte, show j - (j - a) = a by omega, show j - (j - b) = b by omega]
      have ga : (E.extract 0 j).getD a (ArithExpr.var 0) = E.getD a (ArithExpr.var 0) := by
        simp [Array.getD_eq_getD_getElem?, oa, show a < E.size by omega]
      have gb : (E.extract 0 j).getD b (ArithExpr.var 0) = E.getD b (ArithExpr.var 0) := by
        simp [Array.getD_eq_getD_getElem?, ob, show b < E.size by omega]
      rw [ga, gb, e]
      rcases t with _ | _ | _ | t
      · exact reads_pure _
      · exact reads_pure _
      · exact reads_pure _
      · omega

/-- The pool `withNodesWithEncoding` starts from is good and empty. -/
theorem nodesGood_empty (enc : FieldEncoding) (m : Nat) :
    NodesGood (F := F) enc m #[] { fieldEncoding := enc, modulus := some m } where
  enc := rfl
  mod := rfl
  count := rfl
  bytes := ⟨[], rfl, rfl, fun i hi => by simp at hi⟩
  index := fun k i h => by simp at h

end Pool

section Plans

variable [Field F] [DecidableEq F] {enc : FieldEncoding} {m : Nat} {encode : F → Nat}

theorem rte_plan (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (config fn) (replay : Replay F) (layout representative bytecode) :
    RTE true enc m (putFunctionOf encode config fn replay layout representative bytecode)
      (getIPlan (F := F)) := by
  have poly : ∀ p, RTE true enc m (putPolynomial encode p) getPoly := fun p =>
    (rtp_poly (enc := enc) hcast hlt p).rte
  have nats : ∀ xs, RTE true enc m (monadLift (nats xs) : PoolM Unit)
      (fun _ : Array (ArithExpr F) => getNats) := fun xs => (rtp_lift (rt1_nats xs)).rte
  have nat1 : ∀ x, RTE true enc m (monadLift (nat x) : PoolM Unit)
      (fun _ : Array (ArithExpr F) => getNat) := fun x => (rtp_lift (rt1_nat x)).rte
  have str1 : ∀ x, RTE true enc m (monadLift (str x) : PoolM Unit)
      (fun _ : Array (ArithExpr F) => getString) := fun x => (rtp_lift (rt1_str x)).rte
  obtain ⟨source, degree, replayed, chip, columns⟩ := replay
  unfold putFunctionOf getIPlan
  dsimp only
  iterate 4 (split; rotate_left; exact rte_throw_seq; refine rte_pure_seq ?_)
  refine rte_cons (str1 _) fun _ => rte_then (str1 _) fun _ => rte_then (nat1 _) fun _ =>
    rte_then (nats _) fun _ => rte_then (nats _) fun _ => ?_
  refine rte_then (rte_arrayP fun step _ => rte_cons (poly _) fun _ => rte_last (rte_op hcast hlt _ _))
    fun _ => rte_last (rte_listP fun w _ => ?_)
  obtain ⟨c, i, g⟩ := w
  exact rte_cons (nat1 _) fun _ => rte_then (nat1 _) fun _ => rte_last (poly _)

/-- The compiler's chip writer reads back as `IChip.ofChip`. -/
theorem rtp_putChip (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (c : Chip F) : RTP true enc m (putChip encode c) getChipRecord (IChip.ofChip c) := by
  rw [putChip_eq]
  intro E s b s' b' good h
  dsimp only at h
  split at h
  · obtain ⟨_, s₁, b₁, h₁, h₂⟩ := st_bind_ok h
    obtain ⟨he, rfl⟩ := pool_pure h₁
    cases he
    split at h₂
    · obtain ⟨_, s₃, b₃, h₃, h₄⟩ := st_bind_ok h₂
      obtain ⟨he, rfl⟩ := pool_pure h₃
      cases he
      exact rtp_chip hcast hlt _ rfl _ _ _ _ _ good h₄
    · obtain ⟨_, _, _, h₃, _⟩ := st_bind_ok h₂
      exact (pool_throw h₃).elim
  · obtain ⟨_, _, _, h₁, _⟩ := st_bind_ok h
    exact (pool_throw h₁).elim

/-- The chip list of a trace section reads back as the written chips with
their depth metadata. -/
theorem rtp_chips (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < m)
    (cfg : Optimized.Depth.Config) (pairs : List (Chip F × Chip F)) :
    RTP true enc m (listP pairs fun (chip, source) => do putChip encode chip; putDepth cfg source)
      (fun pool => getList (do return (← getChipRecord pool, ← getIDepth)))
      (pairs.map fun (c, src) => (IChip.ofChip c, IDepth.of cfg src)) := by
  refine rtp_listP fun ⟨c, src⟩ _ => ?_
  dsimp only
  rw [putDepth_eq]
  exact rtp_cons (rtp_putChip hcast hlt c) (RTP.weaken (rtp_map (K := fun _ d => pure (IChip.ofChip c, d))
    (rtp_lift (rt1_depth _ (depth_valid cfg src))) fun _ => rfl))

end Plans

/-! ## The trace section -/

/-- A successful `withNodesWithEncoding` ran its body from the empty pool and
buffer, then wrote the pool's count and bytes ahead of the body's bytes. -/
theorem withNodes_ok {enc : FieldEncoding} {m : Nat} {body : PoolM Unit} {b b' : ByteArray}
    (h : withNodesWithEncoding enc body (some m) b = .ok () b') :
    ∃ pool inner, body { fieldEncoding := enc, modulus := some m } (ByteArray.emptyWithCapacity (1 <<< 16)) =
        .ok ((), pool) inner ∧ pool.count < 2 ^ 64 ∧
      b' = b ++ ⟨(tagBytes pool.count ++ pool.bytes.data.toList ++ inner.data.toList).toArray⟩ := by
  unfold withNodesWithEncoding at h
  simp only [bind, EStateM.bind, getThe, MonadStateOf.get, EStateM.get, modifyThe, MonadStateOf.modifyGet,
    EStateM.modifyGet, StateT.run] at h
  split at h
  · rename_i r inner hb
    obtain ⟨u, pool⟩ := r
    simp only at h
    split at h
    · rename_i hn
      split at h
      · rename_i b₂ hr
        have w₁ := nat_writes _ _ _ hn
        have w₂ := raw_writes _ _ _ hr
        have w₃ := raw_writes _ _ _ h
        subst w₁ w₂ w₃
        refine ⟨pool, inner, hb, nat_ok hn, ?_⟩
        simp only [append_assoc', List.append_assoc]
      · cases h
    · cases h
  · cases h

section Trace

variable [NatCast F]

/-- The three lists of a trace section's body read back over its final pool:
the plans and groups as some values, the chips exactly. -/
theorem body_reads {enc : FieldEncoding} {m : Nat} {P C G : PoolM Unit} {chips : List (IChip F × IDepth)}
    (hP : RTE true enc m P (fun E : Array (ArithExpr F) => getList (getIPlan E)))
    (hC : RTP true enc m C (fun E => getList (do return (← getChipRecord E, ← getIDepth))) chips)
    (hG : RTE true enc m G (fun E : Array (ArithExpr F) => getList (getIGroup E)))
    {E : Array (ArithExpr F)} {s s' : NodePool} {b b' : ByteArray} (good : NodesGood enc m E s)
    (h : (do P; C; G : PoolM Unit) s b = .ok ((), s') b') :
    ∃ (E' : Array (ArithExpr F)) (e₁ e₂ e₃ : List UInt8) (ps : List (IPlan F)) (gs : List (IGroup F)),
      NodesGood enc m E' s' ∧ b' = b ++ ⟨(e₁ ++ e₂ ++ e₃).toArray⟩ ∧
      Reads (getList (getIPlan E')) e₁ ps ∧
      Reads (getList (do return (← getChipRecord E', ← getIDepth))) e₂ chips ∧
      Reads (getList (getIGroup E')) e₃ gs := by
  obtain ⟨_, s₁, b₁, h₁, h⟩ := st_bind_ok h
  obtain ⟨_, s₂, b₂, h₂, h₃⟩ := st_bind_ok h
  obtain ⟨E₁, e₁, ps, x₁, g₁, rfl, _, r₁⟩ := hP _ _ _ _ _ good h₁
  obtain ⟨E₂, e₂, x₂, g₂, rfl, _, r₂⟩ := hC _ _ _ _ _ g₁ h₂
  obtain ⟨E₃, e₃, gs, x₃, g₃, rfl, _, r₃⟩ := hG _ _ _ _ _ g₂ h₃
  refine ⟨E₃, e₁, e₂, e₃, ps, gs, g₃, by simp only [append_assoc', List.append_assoc],
    r₁ _ (ext_trans x₂ x₃), r₂ _ x₃, r₃ _ (ext_refl _)⟩

/-- A trace section written as the compiler lays it out reads back with the
chips its chip list writes and the limbs it starts with. -/
theorem trace_reads {enc : FieldEncoding} {m : Nat} {limbs : List Nat} {P C G : PoolM Unit}
    {chips : List (IChip F × IDepth)}
    (hP : RTE true enc m P (fun E : Array (ArithExpr F) => getList (getIPlan E)))
    (hC : RTP true enc m C (fun E => getList (do return (← getChipRecord E, ← getIDepth))) chips)
    (hG : RTE true enc m G (fun E : Array (ArithExpr F) => getList (getIGroup E))) {tr : ByteArray}
    (h : Ixon.run (do
        nat planVersion
        enc.putModulus m
        nats limbs
        withNodesWithEncoding enc (modulus := some m) do P; C; G) = .ok tr) :
    ∃ t : ITrace F, Reads (getTrace (enc == .wide) m) tr.data.toList t ∧ t.chips = chips ∧
      t.limbs = limbs := by
  unfold Ixon.run at h
  split at h
  case h_2 => cases h
  rename_i u b₀ hput
  cases h
  obtain ⟨b₁, h₁, hput⟩ := bind_unit_ok hput
  obtain ⟨b₂, h₂, hput⟩ := bind_unit_ok hput
  obtain ⟨b₃, h₃, h₄⟩ := bind_unit_ok hput
  obtain ⟨pool, inner, hb, hcount, rfl⟩ := withNodes_ok h₄
  obtain ⟨E, f₁, f₂, f₃, ps, gs, good, rfl, r₁, r₂, r₃⟩ := body_reads hP hC hG (nodesGood_empty enc m) hb
  obtain ⟨v, rfl, _, rv⟩ := rt1_nat _ _ _ h₁
  obtain ⟨em, rfl, _, rm⟩ := rt1_modulus enc m _ _ h₂
  obtain ⟨el, rfl, _, rl⟩ := rt1_nats limbs _ _ h₃
  have size : E.size < 2 ^ 64 := good.count ▸ hcount
  have rn := getNodes_reads good size
  rw [good.count] at *
  refine ⟨{ wide := enc == .wide, modulus := m, limbs, plans := ps, chips, groups := gs }, ?_, rfl, rfl⟩
  unfold getTrace
  refine reads_congr (e := v ++ ([] ++ (em ++ ([] ++ (el ++ ((tagBytes E.size ++ pool.bytes.data.toList) ++
    (f₁ ++ (f₂ ++ (f₃ ++ []))))))))) ?_ ?_
  · refine reads_bind rv (reads_bind (reads_pure ()) (reads_bind rm ?_))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact reads_bind (reads_pure ()) (reads_bind rl (reads_bind rn
      (reads_bind r₁ (reads_bind r₂ (reads_bind r₃ (reads_pure _))))))
  · have e₁ : (ByteArray.emptyWithCapacity 65536).data.toList = [] := rfl
    simp [ByteArray.data_append, e₁]
end Trace

section Export

variable [Field F] [DecidableEq F]

open Aiur.Optimized

/-- The `Except` analogue of `st_bind_ok`. -/
theorem except_bind_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The trace section a successful `exportTraceSection` returns reads back with
the written depth chips, each with the depth metadata of its physical source,
and the depth limbs of `cfg`. -/
theorem section_reads {encoding : FieldEncoding} {modulus : Nat} {encode : F → Nat}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    {program : Program F} {artifact : Optimized.Artifact F} {physical : Physical.Prepared artifact}
    {original : Execution.Bytecode F} {cfg : Depth.Config} {bytecode : Execution.Bytecode F}
    {groups : List (String × List String)} {replays : Option (List (Except String (Replay F)))}
    {trace : ByteArray}
    (h : exportTraceSection encoding modulus encode program artifact physical original cfg bytecode groups
      replays = .ok trace) :
    ∃ t : ITrace F, Reads (getTrace (encoding == .wide) modulus) trace.data.toList t ∧
      (t.chips = ((Depth.system cfg physical.system).chips.zip physical.system.chips).map
        fun (c, src) => (IChip.ofChip c, IDepth.of cfg src)) ∧ t.limbs = cfg.limbs := by
  unfold exportTraceSection at h
  obtain ⟨_, _, h⟩ := except_bind_ok' h
  dsimp only at h
  obtain ⟨_, _, h⟩ := except_bind_ok' h
  obtain ⟨plan, _, h⟩ := except_bind_ok' h
  split at h
  case isFalse =>
    obtain ⟨_, h, _⟩ := except_bind_ok' h
    cases h
  obtain ⟨_, _, h⟩ := except_bind_ok' h
  obtain ⟨tr, ht, h⟩ := except_bind_ok' h
  cases h
  refine trace_reads ?_ (rtp_chips hcast hlt cfg _) ?_ ht
  · refine rte_listP fun x _ => ?_
    split
    · refine rte_pure_seq ?_
      cases replays
      · exact rte_pure_bind (ofExcept_pool _) fun r => rte_plan hcast hlt _ _ _ _ _ _
      · exact rte_pure_bind (ofExcept_pool _) fun r => rte_plan hcast hlt _ _ _ _ _ _
    · exact rte_throw_seq
  · refine rte_listP fun p _ => ?_
    rw [putGroup_eq]
    exact rte_group hcast hlt _
end Export

/-! ## The package -/

section Package

variable [NatCast F]

/-- The option byte of the trace section's presence. -/
theorem reads_some_unit : Reads (getOption (pure ())) [1] (some ()) := by
  refine reads_congr (reads_bind (e₂ := []) (getTag_reads "option" (x := 1) (count := 2) (by decide)) ?_) rfl
  exact reads_pure _

/-- `getPackage` returns the chips and limbs of the trace it read after the program
section and the option byte. -/
theorem decode_chips {bytes : ByteArray} {modulus ver p₁ p₂ p₃ p₄ : Nat} {w : Bool} {prog : Export F}
    {t : ITrace F} {s₅ c : Cursor} {pkg : Package F} (hv : (ver == 2 || ver == 3) = true) (hw : (ver == 3) = w)
    (run₁ : getRaw 8 ⟨bytes, 0⟩ = .ok Artifact.packageMagic ⟨bytes, p₁⟩)
    (run₂ : getNat ⟨bytes, p₁⟩ = .ok ver ⟨bytes, p₂⟩)
    (run₃ : getProgram w modulus ⟨bytes, p₂⟩ = .ok prog ⟨bytes, p₃⟩)
    (run₄ : getOption (pure ()) ⟨bytes, p₃⟩ = .ok (some ()) ⟨bytes, p₄⟩)
    (run₅ : getTrace w modulus ⟨bytes, p₄⟩ = .ok t s₅)
    (hrun : getPackage modulus { bytes } = .ok pkg c) : pkg.chips = (t.chips.map (·.1)).toArray ∧ pkg.limbs = t.limbs := by
  have magic : (Artifact.packageMagic.data == Artifact.packageMagic.data) = true := by simp
  unfold getPackage at hrun
  rw [show ({ bytes } : Cursor) = ⟨bytes, 0⟩ from rfl, ok_bind run₁] at hrun
  rw [ite_eq_left_of_eq_true _ _ (eq_true magic)] at hrun
  rw [ok_bind (by rfl)] at hrun
  beta_reduce at hrun
  rw [ok_bind run₂] at hrun
  rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at hrun
  rw [ok_bind (by rfl)] at hrun
  beta_reduce at hrun
  simp only [hw] at hrun
  rw [ok_bind run₃] at hrun
  rw [ok_bind run₄] at hrun
  dsimp only at hrun
  rw [ok_bind (by rfl)] at hrun
  rw [ok_bind run₅] at hrun
  obtain ⟨_, _, -, hrun⟩ := estate_bind_ok hrun
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
  rw [← hrun.1]
  exact ⟨rfl, rfl⟩

/-- A package that the compiler's writer produced with the trace section `trace`
and `decodePackage` accepts carries the chips and limbs `getTrace` reads from
`trace`. -/
theorem chips_of_decode {encoding : FieldEncoding} {exported : Export F} {modulus : Nat}
    {encode : F → Nat} {trace bytes : ByteArray} {pkg : Package F} {t : ITrace F}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodePackage modulus bytes = .ok pkg)
    (rt : Reads (getTrace (encoding == .wide) modulus) trace.data.toList t) :
    pkg.chips = (t.chips.map (·.1)).toArray ∧ pkg.limbs = t.limbs := by
  unfold Ixon.run at written
  split at written
  case h_2 => cases written
  rename_i u b₀ hput
  cases written
  have size₀ : (ByteArray.emptyWithCapacity (1 <<< 16)).size = 0 := rfl
  unfold Artifact.putPackageWithEncoding at hput
  obtain ⟨b₁, h₁, hput⟩ := bind_unit_ok hput
  obtain ⟨b₂, h₂, hput⟩ := bind_unit_ok hput
  obtain ⟨b₃, h₃, h₄⟩ := bind_unit_ok hput
  obtain ⟨e₁, rfl, _, r₁⟩ := rt1_raw8 Artifact.packageMagic rfl _ _ h₁
  obtain ⟨e₂, rfl, _, r₂⟩ := rt1_nat _ _ _ h₂
  obtain ⟨e₃, rfl, _, r₃⟩ := program_rt exported encoding modulus encode hcast hlt _ _ h₃
  obtain ⟨b₄, h₅, h₆⟩ := bind_unit_ok h₄
  have w₅ := u8_writes 1 _ _ h₅
  have w₆ := raw_writes trace _ _ h₆
  subst w₅ w₆
  simp only [append_assoc', List.append_assoc] at decoded
  generalize ByteArray.emptyWithCapacity (1 <<< 16) = b₀ at size₀ decoded
  have at₂ := at_append (at_append (at_written b₀ (e₁ ++ (e₂ ++ (e₃ ++ ([1] ++ trace.data.toList)))))).2
  have at₃ := at_append at₂.2
  have at₄ := at_append at₃.2
  have run₁ := r₁ _ _ (at_prefix b₀ e₁ (e₂ ++ (e₃ ++ ([1] ++ trace.data.toList))))
  have run₂ := r₂ _ _ at₂.1
  have run₃ := r₃ _ _ at₃.1
  have run₄ := reads_some_unit _ _ at₄.1
  have run₅ := rt _ _ at₄.2
  simp only [EStateM.run, size₀, Nat.zero_add] at run₁ run₂ run₃ run₄ run₅
  unfold decodePackage Ixon.decode at decoded
  split at decoded
  case h_2 => cases decoded
  rename_i pkg' cursor hrun
  split at decoded
  case isFalse => cases decoded
  cases decoded
  simp only [EStateM.run] at hrun
  cases encoding
  · exact decode_chips (by decide) rfl run₁ run₂ run₃ run₄ run₅ hrun
  · exact decode_chips (by decide) rfl run₁ run₂ run₃ run₄ run₅ hrun

end Package

end Aiur.Tiling.Ixa
