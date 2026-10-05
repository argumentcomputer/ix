import IxSharingVerify.TieredIdem
import IxC.Ixon.Wire

/-!
# Tiered construction: the output is in the wire domain

For the format switch: every expression the tiered construction returns
(table entries and roots) is in the expression codec's public wire domain
(`Ixon.Expr.wireWF`: every `UInt64` count it writes is representable), the
table count fits a `UInt64` (capacity), table entry `k` references only
entries below `k`, and every root only table entries (the rule that a
`Share` refers only to an earlier table entry, which the Ixon decoders and
the certified reader check). The wire domain is established by phase 3's
`wireCounts` check over the output (`wireCounts_spec`); the other facts
are proved from the construction. For the wire layout the length the
construction reports is the serialized length of its output
(`canonicalSharingTiered_serialized`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (bind_eq_ok SharesIn materializeTable_parts
  materializeTable_backward)

/-- `wireCounts` decides the wire domain and computes the telescope counts. -/
theorem wireCounts_spec : ∀ (e : Ixon.Expr) (c : Nat × Nat × Nat), wireCounts e = some c →
    e.wireWF ∧ c = (e.appCount, e.lamCount, e.allCount) := by
  intro e
  induction e with
  | sort _ | var _ | str _ | nat _ | share _ =>
    intro c h; simp only [wireCounts, Option.some.injEq] at h; subst h
    exact ⟨trivial, rfl⟩
  | ref _ us | recur _ us =>
    intro c h
    simp only [wireCounts] at h
    split at h
    · rename_i hus; simp only [Option.some.injEq] at h; subst h; exact ⟨hus, rfl⟩
    · cases h
  | prj _ _ v ih =>
    intro c h
    simp only [wireCounts] at h
    cases hv : wireCounts v with
    | none => rw [hv] at h; cases h
    | some cv =>
      rw [hv] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨(ih cv hv).1, rfl⟩
  | app f a ihf iha =>
    intro c h
    simp only [wireCounts] at h
    cases hf : wireCounts f with
    | none => rw [hf] at h; cases h
    | some cf =>
      cases ha : wireCounts a with
      | none => rw [hf, ha] at h; cases h
      | some ca =>
        rw [hf, ha] at h
        obtain ⟨n, x, y⟩ := cf
        simp only at h
        split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hwf, hc⟩ := ihf _ hf
          simp only [Prod.mk.injEq] at hc
          refine ⟨⟨hwf, (iha ca ha).1, by rw [← hc.1]; exact hn⟩, ?_⟩
          simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount, hc.1]
        · cases h
  | lam _ ty b iht ihb =>
    intro c h
    simp only [wireCounts] at h
    cases ht : wireCounts ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases hb : wireCounts b with
      | none => rw [ht, hb] at h; cases h
      | some cb =>
        rw [ht, hb] at h
        obtain ⟨x, n, y⟩ := cb
        simp only at h
        split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hwf, hc⟩ := ihb _ hb
          simp only [Prod.mk.injEq] at hc
          refine ⟨⟨(iht ct ht).1, hwf, by rw [← hc.2.1]; exact hn⟩, ?_⟩
          simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount, hc.2.1]
        · cases h
  | all _ _ ty b iht ihb =>
    intro c h
    simp only [wireCounts] at h
    cases ht : wireCounts ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases hb : wireCounts b with
      | none => rw [ht, hb] at h; cases h
      | some cb =>
        rw [ht, hb] at h
        obtain ⟨x, y, n⟩ := cb
        simp only at h
        split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hwf, hc⟩ := ihb _ hb
          simp only [Prod.mk.injEq] at hc
          refine ⟨⟨(iht ct ht).1, hwf, by rw [← hc.2.2]; exact hn⟩, ?_⟩
          simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount, hc.2.2]
        · cases h
  | letE _ ty v b iht ihv ihb =>
    intro c h
    simp only [wireCounts] at h
    cases ht : wireCounts ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases hv : wireCounts v with
      | none => rw [ht, hv] at h; cases h
      | some cv =>
        cases hb : wireCounts b with
        | none => rw [ht, hv, hb] at h; cases h
        | some cb =>
          rw [ht, hv, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨⟨(iht ct ht).1, (ihv cv hv).1, (ihb cb hb).1⟩, rfl⟩

theorem wireWF_of_check {e : Ixon.Expr} (h : (wireCounts e).isSome = true) : e.wireWF := by
  cases hc : wireCounts e with
  | none => rw [hc] at h; cases h
  | some c => exact (wireCounts_spec e c hc).1

/-- The format facts of an encoding: wire domain, table capacity, and
backward Shares. -/
def FormatOK (sharing roots : Array Ixon.Expr) : Prop :=
  (∀ e ∈ sharing.toList, e.wireWF) ∧ (∀ e ∈ roots.toList, e.wireWF) ∧
    sharing.size < UInt64.size ∧
    (∀ k (hk : k < sharing.size), SharesIn (· < k) sharing[k]) ∧
    ∀ e ∈ roots.toList, SharesIn (· < sharing.size) e

theorem tieredAtWidth_format {layout : ShareLayout} {limits : Limits} {ex : Expanded} {w : Nat}
    {c : TieredSharingResult} (h : tieredAtWidth layout limits ex w = .ok c) :
    FormatOK c.result.sharing c.result.roots := by
  obtain ⟨u, a, m, -, -, hm, rfl⟩ := tieredAtWidth_parts h
  obtain ⟨work, hmat, -, -, hwire⟩ := rematerialize_parts hm
  obtain ⟨hsize, -, -⟩ := materializeTable_parts _ _ _ _ _ hmat
  obtain ⟨hsz, hback, hrback⟩ := materializeTable_backward _ _ _ _ _ (by omega) hmat
  rw [Array.all_eq_true] at hwire
  have hw : ∀ e ∈ (m.entries ++ m.roots).toList, e.wireWF := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    exact wireWF_of_check (hwire i (by simpa using hi))
  refine ⟨fun e he => hw e (by rw [Array.toList_append, List.mem_append]; exact Or.inl he),
    fun e he => hw e (by rw [Array.toList_append, List.mem_append]; exact Or.inr he),
    by show m.entries.size < UInt64.size; omega, hback, ?_⟩
  intro e he
  rw [show (tieredResult layout ex w u a m).result.sharing.size = a.order.size by
    show m.entries.size = a.order.size; exact hsz]
  exact hrback e he

/-- **The tiered output is in the format domain.** Every table entry and
root the tiered construction returns is in the expression codec's wire
domain, the table count fits a `UInt64`, entry `k` references only entries
below `k`, and every root only table entries. -/
theorem canonicalTiered_format {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {r : TieredSharingResult} (h : canonicalTieredExpanded layout limits ex = .ok r) :
    FormatOK r.result.sharing r.result.roots := by
  obtain ⟨r₀, hr₀, -, -, hs, hr, -, -⟩ := canonicalTiered_core h
  rw [hs, hr]
  obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, ⟨c, hc, hrc⟩, -, -⟩ := canonicalTieredCore_select hr₀
  have hres : r₀.result = c.result := by rw [hrc]
  rw [hres]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc | hc <;> rw [hc]
  · exact tieredAtWidth_format h₁
  · exact tieredAtWidth_format h₂
  · exact tieredAtWidth_format h₃

/-- `canonicalSharingTiered` (Share-free roots): the output is in the format
domain. -/
theorem canonicalSharingTiered_format {layout : ShareLayout} {roots : Array Ixon.Expr}
    {limits : Limits} {r : TieredSharingResult}
    (h : canonicalSharingTiered layout roots limits = .ok r) :
    FormatOK r.result.sharing r.result.roots := by
  unfold canonicalSharingTiered at h
  obtain ⟨ex, -, h⟩ := bind_eq_ok h
  exact canonicalTiered_format h

/-- `canonicalSharingTieredTable` (roots with an existing table): the output
is in the format domain. -/
theorem canonicalSharingTieredTable_format {layout : ShareLayout}
    {sharing roots : Array Ixon.Expr} {limits : Limits} {r : TieredSharingResult}
    (h : canonicalSharingTieredTable layout sharing roots limits = .ok r) :
    FormatOK r.result.sharing r.result.roots := by
  unfold canonicalSharingTieredTable at h
  obtain ⟨ex, -, h⟩ := bind_eq_ok h
  exact canonicalTiered_format h

/-! ## The reported length is the serialized length

On the wire domain the TagN layout length of an encoding is the length the
wire codec writes (`layoutBytes_tagN_eq_serialized`). Phase 3 records the
layout length of its output (`rematerialize_measured`) and checks that every
output expression is in the wire domain, so for the wire layout the length
the tiered construction reports is the serialized length of its output
(`canonicalSharingTiered_serialized`). -/

/-- On the wire domain the TagN layout price is the serialized length. -/
theorem layoutBytes_tagN_eq_serialized (entries roots : Array Ixon.Expr)
    (h : ((entries ++ roots).all fun e => (wireCounts e).isSome) = true) :
    layoutBytes .tagN entries roots =
      tag0Size entries.size + (entries ++ roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 := by
  have hsz : ∀ e ∈ (entries ++ roots).toList,
      (sizeInfoWith ShareLayout.tagN.widthAt e).full = (Ixon.serExpr e).size := by
    intro e he
    rw [Array.all_eq_true'] at h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (h e (Array.mem_toList_iff.mp he))
    have hser := Ix.Sharing.Verify.SharingExact.exprSize_eq_serExpr e (wireCounts_spec e c hc).1
    exact hser
  unfold layoutBytes
  simp only [Ix.Sharing.Verify.UniformModel.array_foldl_add_sum, Array.toList_append,
    List.map_append, List.sum_append] at hsz ⊢
  rw [List.map_congr_left (fun e he => hsz e (List.mem_append_left _ he)),
    List.map_congr_left (fun e he => hsz e (List.mem_append_right _ he))]
  omega

theorem tieredAtWidth_serialized {limits : Limits} {ex : Expanded} {w : Nat}
    {c : TieredSharingResult} (h : tieredAtWidth .tagN limits ex w = .ok c) :
    c.result.variableBytes = tag0Size c.result.sharing.size +
        (c.result.sharing ++ c.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      c.result.modelBytes = c.result.variableBytes := by
  obtain ⟨u, a, m, -, -, hm, rfl⟩ := tieredAtWidth_parts h
  obtain ⟨-, -, -, -, hwire⟩ := rematerialize_parts hm
  obtain ⟨hmeas, hbytes⟩ := rematerialize_measured hm
  show m.measured = tag0Size m.entries.size +
      (m.entries ++ m.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
    m.bytes = m.measured
  exact ⟨hmeas.trans (layoutBytes_tagN_eq_serialized _ _ hwire), hbytes⟩

theorem canonicalTiered_serialized {limits : Limits} {ex : Expanded} {r : TieredSharingResult}
    (h : canonicalTieredExpanded .tagN limits ex = .ok r) :
    r.result.variableBytes = tag0Size r.result.sharing.size +
        (r.result.sharing ++ r.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      r.result.modelBytes = r.result.variableBytes := by
  obtain ⟨r₀, hr₀, hrr, -, -, -, -, -⟩ := canonicalTiered_core h
  subst hrr
  obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, ⟨c, hc, hrc⟩, -, -⟩ := canonicalTieredCore_select hr₀
  subst hrc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · have hc := tieredAtWidth_serialized h₁; exact hc
  · have hc := tieredAtWidth_serialized h₂; exact hc
  · have hc := tieredAtWidth_serialized h₃; exact hc

/-- **The tiered length is the serialized length.** For the wire layout, the
length `canonicalSharingTiered` reports for its output (`variableBytes`, and
the layout price `modelBytes`) is the serialized length of the output: the
table count and every entry and root as the wire codec writes them. -/
theorem canonicalSharingTiered_serialized {roots : Array Ixon.Expr} {limits : Limits}
    {r : TieredSharingResult} (h : canonicalSharingTiered .tagN roots limits = .ok r) :
    r.result.variableBytes = tag0Size r.result.sharing.size +
        (r.result.sharing ++ r.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      r.result.modelBytes = r.result.variableBytes := by
  unfold canonicalSharingTiered at h
  obtain ⟨ex, -, h⟩ := bind_eq_ok h
  exact canonicalTiered_serialized h

/-- `canonicalSharingTiered_serialized` for roots with an existing table. -/
theorem canonicalSharingTieredTable_serialized {sharing roots : Array Ixon.Expr} {limits : Limits}
    {r : TieredSharingResult} (h : canonicalSharingTieredTable .tagN sharing roots limits = .ok r) :
    r.result.variableBytes = tag0Size r.result.sharing.size +
        (r.result.sharing ++ r.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      r.result.modelBytes = r.result.variableBytes := by
  unfold canonicalSharingTieredTable at h
  obtain ⟨ex, -, h⟩ := bind_eq_ok h
  exact canonicalTiered_serialized h

end Ix.Sharing.Verify.Tiered
