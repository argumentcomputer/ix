/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Activity

/-! Arithmetic for the call-order AIR. Each active function row carries a
48-bit rank. A constrained call binds the callee's rank in its function
lookup and supplies a 48-bit gap satisfying `child - parent - 1 - gap = 0`.
The bounds prevent field wraparound and force strict increase. Connecting
the byte-table lookups and native constraint emitter to these premises is
part of the remaining AIR extraction proof.
-/

namespace Aiur

theorem G.n_ofNat (n : Nat) : (G.ofNat n).n = n % gSize.toNat := by
  have hm : n % gSize.toNat < gSize.toNat := Nat.mod_lt _ (by decide)
  have hw : n % gSize.toNat < UInt64.size := Nat.lt_trans hm (by decide)
  have hv : (n % gSize.toNat).toUInt64.toNat = n % gSize.toNat := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hw]
  have h : (n % gSize.toNat).toUInt64 < gSize := by
    simpa only [UInt64.lt_iff_toNat_lt, hv] using hm
  simp only [G.ofNat, dif_pos h, G.n, hv]

theorem G.sub_eq_zero_iff (a b : G) : a - b = 0 ↔ a = b := by
  have ha : a.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp a.property
  have hb : b.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp b.property
  have hp : gSize.toNat = 18446744069414584321 := by decide
  constructor
  · intro h
    have hn := congrArg G.n h
    change (G.ofNat (a.n + gSize.toNat - b.n)).n = 0 at hn
    rw [G.n_ofNat, hp] at hn
    rw [hp] at ha hb
    have he : a.n = b.n := by omega
    apply Subtype.ext
    exact UInt64.toNat_inj.mp he
  · intro h
    subst b
    change G.ofNat (a.n + gSize.toNat - a.n) = 0
    simp only [Nat.add_sub_cancel_left]
    rfl

theorem G.n_add (a b : G) : (a + b).n = (a.n + b.n) % gSize.toNat :=
  G.n_ofNat _

theorem G.n_mul (a b : G) : (a * b).n = (a.n * b.n) % gSize.toNat :=
  G.n_ofNat _

namespace AIR

def callRankBound : Nat := 2 ^ 48

/-- The six little-endian byte expressions used by the Rust emitter. -/
def packRank (bytes : Fin 6 → G) : G :=
  bytes 0 + 256 * bytes 1 + 65536 * bytes 2 + 16777216 * bytes 3 +
    4294967296 * bytes 4 + 1099511627776 * bytes 5

theorem packRank_lt (bytes : Fin 6 → G) (bounded : ∀ i, (bytes i).n < 256) :
    (packRank bytes).n < callRankBound := by
  have h0 := bounded 0
  have h1 := bounded 1
  have h2 := bounded 2
  have h3 := bounded 3
  have h4 := bounded 4
  have h5 := bounded 5
  have c1 : (256 : G).n = 256 := rfl
  have c2 : (65536 : G).n = 65536 := rfl
  have c3 : (16777216 : G).n = 16777216 := rfl
  have c4 : (4294967296 : G).n = 4294967296 := rfl
  have c5 : (1099511627776 : G).n = 1099511627776 := rfl
  simp only [packRank, G.n_add, G.n_mul, c1, c2, c3, c4, c5]
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  rw [modulus]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]
  apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
  unfold callRankBound
  omega

/-- Exact active-call polynomial, before selector gating. -/
def callOrderConstraint (parent child gap : G) : G :=
  child - parent - 1 - gap

theorem call_order_strict {parent child gap : G}
    (hp : parent.n < callRankBound) (hc : child.n < callRankBound)
    (hg : gap.n < callRankBound)
    (satisfied : callOrderConstraint parent child gap = 0) :
    parent.n < child.n := by
  have h1 : child - parent - 1 = gap :=
    (G.sub_eq_zero_iff _ _).mp satisfied
  have h := congrArg G.n h1
  change (G.ofNat ((G.ofNat (child.n + gSize.toNat - parent.n)).n +
    gSize.toNat - 1)).n = gap.n at h
  simp only [G.n_ofNat] at h
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  rw [modulus] at h
  unfold callRankBound at hp hc hg
  omega

theorem call_order_irrefl (rank gap : G) (hr : rank.n < callRankBound)
    (hg : gap.n < callRankBound) : callOrderConstraint rank rank gap ≠ 0 := by
  intro h
  exact Nat.lt_irrefl _ (call_order_strict hr hr hg h)

theorem active_call_order_strict {selector parent child gap : G}
    (active : selector = 1)
    (hp : parent.n < callRankBound) (hc : child.n < callRankBound)
    (hg : gap.n < callRankBound)
    (satisfied : selector * callOrderConstraint parent child gap = 0) :
    parent.n < child.n := by
  rw [active, G.mul_comm, G.mul_one] at satisfied
  exact call_order_strict hp hc hg satisfied

/-- Range-checked bytes suffice for the rank bounds in an active call. -/
theorem packed_call_order_strict (parent child gap : Fin 6 → G)
    (hp : ∀ i, (parent i).n < 256) (hc : ∀ i, (child i).n < 256)
    (hg : ∀ i, (gap i).n < 256)
    (satisfied : callOrderConstraint (packRank parent) (packRank child) (packRank gap) = 0) :
    (packRank parent).n < (packRank child).n :=
  call_order_strict (packRank_lt parent hp) (packRank_lt child hc)
    (packRank_lt gap hg) satisfied

/-- Any call relation satisfying the bounded-rank constraints is well founded.
The relation is oriented `calls child parent`, as required by recursion. -/
theorem call_relation_wellFounded {α : Sort u} (rank : α → G)
    (bounded : ∀ node, (rank node).n < callRankBound) (calls : α → α → Prop)
    (ordered : ∀ child parent, calls child parent →
      ∃ gap : G, gap.n < callRankBound ∧
        callOrderConstraint (rank parent) (rank child) gap = 0) :
    WellFounded calls := by
  apply Subrelation.wf (r := fun child parent =>
    callRankBound - (rank child).n < callRankBound - (rank parent).n)
    (fun {child parent} h => ?_)
    (InvImage.wf (fun node => callRankBound - (rank node).n) Nat.lt_wfRel.wf)
  obtain ⟨gap, hg, hs⟩ := ordered child parent h
  have strict := call_order_strict (bounded parent) (bounded child) hg hs
  have limit := bounded child
  omega

end AIR
end Aiur
