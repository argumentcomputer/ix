import Aiur.Optimized.Grouping.Certificate
import Aiur.Optimized.Grouping.Finite

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def VectorCheck (p q : List (Polynomial F)) (left right : Nat → Polynomial F) : Prop :=
  ∀ i ∈ List.range (max p.length q.length),
    ((word p i).subst left).Identical ((word q i).subst right)

instance (p q : List (Polynomial F)) (left right : Nat → Polynomial F) :
    Decidable (VectorCheck p q left right) := by unfold VectorCheck; infer_instance

theorem VectorCheck.sound {p q : List (Polynomial F)} {left right : Nat → Polynomial F}
    (checked : VectorCheck p q left right) (a : Nat → F) (i : Nat) :
    (word p i).denote (fun v => (left v).denote a) =
      (word q i).denote (fun v => (right v).denote a) := by
  by_cases bound : i < max p.length q.length
  · simpa only [Polynomial.denote_subst] using
      (checked i (List.mem_range.mpr bound)).denote a
  · have hp : p.length ≤ i := by omega
    have hq : q.length ≤ i := by omega
    simp [word, List.getElem?_eq_none hp, List.getElem?_eq_none hq,
      Scalar.Circuit.ArithExpr.denote]

def lookupAt (ls : List (Lookup F)) (i : Nat) : Lookup F := ls[i]?.getD ⟨.const 0, []⟩

/-- Whether any physical slot holds more than one logical lookup under `slotMap`. -/
def hasCompactedSlots (numSlots : Nat) (slotMap : Array Nat) (numRequired : Nat) : Bool :=
  (List.range numSlots).any fun s => (bucketOf slotMap numRequired s).length > 1

private def maxBucketWidth (slotArgsLen : Nat) (required : List (Lookup F)) (B : List Nat) : Nat :=
  B.foldl (fun acc k => max acc (lookupAt required k).args.length) slotArgsLen

private theorem le_maxBucketWidth_init (slotArgsLen : Nat) (required : List (Lookup F))
    (B : List Nat) : slotArgsLen ≤ maxBucketWidth slotArgsLen required B := by
  unfold maxBucketWidth
  induction B generalizing slotArgsLen with
  | nil => exact le_rfl
  | cons k ks ih =>
      exact le_trans (Nat.le_max_left _ _) (ih _)

private theorem le_maxBucketWidth_mem (slotArgsLen : Nat) (required : List (Lookup F))
    (B : List Nat) {k : Nat} (hk : k ∈ B) :
    (lookupAt required k).args.length ≤ maxBucketWidth slotArgsLen required B := by
  unfold maxBucketWidth
  induction B generalizing slotArgsLen with
  | nil => cases hk
  | cons x xs ih =>
      rcases List.mem_cons.mp hk with rfl | hxs
      · exact le_trans (Nat.le_max_right _ _) (le_maxBucketWidth_init _ required xs)
      · exact ih _ hxs

/-- Slot check for `PacketCheck` when no slot is compacted (`B.length ≤ 1` for all `s`). -/
def PacketCheckPlain (g : Layout F) (slotMap : Array Nat) (left : Nat → Polynomial F)
    (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) : Prop :=
  VectorCheck g.receive provided left right ∧
  (∀ k ∈ List.range required.length, slotOf slotMap k < g.sends.length) ∧
  ∀ s ∈ List.range g.sends.length,
    match bucketOf slotMap required.length s with
    | [] =>
        ((g.slot s).enable.subst left).Identical (.const 0) ∧
        VectorCheck (g.slot s).args [] left right
    | [k] =>
        ((g.slot s).enable.subst left).Identical ((lookupAt required k).enable.subst right) ∧
        VectorCheck (g.slot s).args (lookupAt required k).args left right
    | _ => False

instance (g : Layout F) (slotMap : Array Nat) (left : Nat → Polynomial F)
    (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) :
    Decidable (PacketCheckPlain g slotMap left provided required right) := by
  unfold PacketCheckPlain
  letI (s : Nat) : Decidable (match bucketOf slotMap required.length s with
      | [] => ((g.slot s).enable.subst left).Identical (.const 0) ∧
          VectorCheck (g.slot s).args [] left right
      | [k] => ((g.slot s).enable.subst left).Identical ((lookupAt required k).enable.subst right) ∧
          VectorCheck (g.slot s).args (lookupAt required k).args left right
      | _ => False) := by
    split <;> infer_instance
  infer_instance

/-- Slot check for `PacketCheck` allowing both per-member slot permutation (`C7a`)
and intra-chip mutually-exclusive bucket compaction (`C2`). -/
def PacketCheckWith (ctx : ExclCtx F) (g : Layout F) (slotMap : Array Nat)
    (left : Nat → Polynomial F) (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) : Prop :=
  VectorCheck g.receive provided left right ∧
  (∀ k ∈ List.range required.length, slotOf slotMap k < g.sends.length) ∧
  ∀ s ∈ List.range g.sends.length,
    let B := bucketOf slotMap required.length s
    match B with
    | [] =>
        ((g.slot s).enable.subst left).Identical (.const 0) ∧
        VectorCheck (g.slot s).args [] left right
    | [k] =>
        ((g.slot s).enable.subst left).Identical ((lookupAt required k).enable.subst right) ∧
        VectorCheck (g.slot s).args (lookupAt required k).args left right
    | _ =>
        (∀ k ∈ B, ctx.isBool (lookupAt required k).enable = true) ∧
        ctx.allPairwiseExcl (B.map fun k => (lookupAt required k).enable) = true ∧
        ((g.slot s).enable.subst left).Identical
          ((sum (B.map fun k => (lookupAt required k).enable)).subst right) ∧
        ∀ w ∈ List.range (maxBucketWidth (g.slot s).args.length required B),
          ((word (g.slot s).args w).subst left).Identical
            ((sum (B.map fun k => ctx.gatedWord (lookupAt required k).enable
              (word (lookupAt required k).args w))).subst right)

instance (ctx : ExclCtx F) (g : Layout F) (slotMap : Array Nat)
    (left : Nat → Polynomial F) (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) :
    Decidable (PacketCheckWith ctx g slotMap left provided required right) := by
  unfold PacketCheckWith
  letI (s : Nat) : Decidable (let B := bucketOf slotMap required.length s
      match B with
      | [] => ((g.slot s).enable.subst left).Identical (.const 0) ∧
          VectorCheck (g.slot s).args [] left right
      | [k] => ((g.slot s).enable.subst left).Identical ((lookupAt required k).enable.subst right) ∧
          VectorCheck (g.slot s).args (lookupAt required k).args left right
      | _ =>
          (∀ k ∈ B, ctx.isBool (lookupAt required k).enable = true) ∧
          ctx.allPairwiseExcl (B.map fun k => (lookupAt required k).enable) = true ∧
          ((g.slot s).enable.subst left).Identical
            ((sum (B.map fun k => (lookupAt required k).enable)).subst right) ∧
          ∀ w ∈ List.range (maxBucketWidth (g.slot s).args.length required B),
            ((word (g.slot s).args w).subst left).Identical
              ((sum (B.map fun k => ctx.gatedWord (lookupAt required k).enable
                (word (lookupAt required k).args w))).subst right)) := by
    dsimp only
    split <;> infer_instance
  infer_instance

/-- Compare every encoded channel/width tag, enabled message, argument word,
and zero-padded tail, supporting per-member slot permutation (`C7a`) and
certified mutually-exclusive intra-chip bucket compaction (`C2`). -/
def PacketCheck (g : Layout F) (cs : List (Polynomial F)) (slotMap : Array Nat)
    (left : Nat → Polynomial F) (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) : Prop :=
  if hasCompactedSlots g.sends.length slotMap required.length then
    PacketCheckWith (ExclCtx.ofConstraints cs) g slotMap left provided required right
  else
    PacketCheckPlain g slotMap left provided required right

instance (g : Layout F) (cs : List (Polynomial F)) (slotMap : Array Nat)
    (left : Nat → Polynomial F) (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) :
    Decidable (PacketCheck g cs slotMap left provided required right) := by
  unfold PacketCheck
  split <;> infer_instance

def Member.PacketCertificate (id : String → Except String Nat) (g : Layout F) (m : Member F) : Prop :=
  match messages id m.origin with
  | .error _ => False
  | .ok (provided, required) =>
      PacketCheck g m.origin.constraints m.slotMap (g.back (some m.selector)) provided required m.project ∧
      PacketCheck g m.origin.constraints m.slotMap (fun v => (restrict g.width v).subst m.embedding)
        provided required (fun v => .var v)

instance (id : String → Except String Nat) (g : Layout F) (m : Member F) :
    Decidable (m.PacketCertificate id g) := by unfold Member.PacketCertificate; split <;> infer_instance

/-- Values seen by the lookup protocol, extended with zeros in absent slots,
allowing per-member slot permutation (`C7a`) and mutually-exclusive bucket
compaction (`C2`). -/
def SamePackets (g : Layout F) (slotMap : Array Nat) (a : Nat → F)
    (provided : List (Polynomial F)) (required : List (Lookup F)) (b : Nat → F) : Prop :=
  (∀ i, (word g.receive i).denote a = (word provided i).denote b) ∧
  (∀ k < required.length, slotOf slotMap k < g.sends.length) ∧
  ∀ s,
    let B := bucketOf slotMap required.length s
    match B with
    | [] =>
        (g.slot s).enable.denote a = 0 ∧
        ∀ j, (word (g.slot s).args j).denote a = 0
    | [k] =>
        (g.slot s).enable.denote a = (lookupAt required k).enable.denote b ∧
        ∀ j, (word (g.slot s).args j).denote a = (word (lookupAt required k).args j).denote b
    | _ =>
        ((g.slot s).enable.denote a = 0 ∧
          (∀ j, (word (g.slot s).args j).denote a = 0) ∧
          ∀ k ∈ B, (lookupAt required k).enable.denote b = 0) ∨
        (∃ k ∈ B,
          (lookupAt required k).enable.denote b = 1 ∧
          (∀ k' ∈ B, k' ≠ k → (lookupAt required k').enable.denote b = 0) ∧
          (g.slot s).enable.denote a = 1 ∧
          ∀ j, (word (g.slot s).args j).denote a = (word (lookupAt required k).args j).denote b)

private theorem bucketOf_empty_of_ge {slotMap : Array Nat} {n m s : Nat}
    (hbound : ∀ k < n, slotOf slotMap k < m) (hge : m ≤ s) :
    bucketOf slotMap n s = [] := by
  unfold bucketOf
  apply List.filter_eq_nil_iff.mpr
  intro k hk
  have hlt := hbound k (List.mem_range.mp hk)
  simp [show slotOf slotMap k ≠ s by omega]

theorem PacketCheck.sound {g : Layout F} {cs : List (Polynomial F)} {slotMap : Array Nat}
    {left right : Nat → Polynomial F} {provided : List (Polynomial F)} {required : List (Lookup F)}
    (checked : PacketCheck g cs slotMap left provided required right) (a : Nat → F)
    (valid : Satisfies cs (fun v => (right v).denote a)) :
    SamePackets g slotMap (fun v => (left v).denote a) provided required (fun v => (right v).denote a) := by
  set a' := fun v => (left v).denote a
  set b := fun v => (right v).denote a
  unfold PacketCheck at checked
  split at checked
  · set ctx := ExclCtx.ofConstraints cs
    have hctx : ctx.Valid cs := ExclCtx.ofConstraints_valid cs
    obtain ⟨hrecv, hbound, hslots⟩ := checked
    have hbound' : ∀ k < required.length, slotOf slotMap k < g.sends.length :=
      fun k hk => hbound k (List.mem_range.mpr hk)
    refine ⟨fun i => hrecv.sound a i, hbound', fun s => ?_⟩
    by_cases hs : s < g.sends.length
    · have hslot := hslots s (List.mem_range.mpr hs)
      dsimp only at hslot ⊢
      generalize hB : bucketOf slotMap required.length s = B at hslot ⊢
      cases B with
      | nil =>
          refine ⟨?_, fun j => ?_⟩
          · simpa [a', Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote] using hslot.1.denote a
          · simpa [a', word, Scalar.Circuit.ArithExpr.denote] using hslot.2.sound a j
      | cons k1 rest =>
          cases rest with
          | nil =>
              refine ⟨?_, fun j => hslot.2.sound a j⟩
              simpa [a', b, Polynomial.denote_subst] using hslot.1.denote a
          | cons k2 tail =>
              set B' := k1 :: k2 :: tail
              obtain ⟨hbool, hexcl, hen, hwords⟩ := hslot
              have henEq : (g.slot s).enable.denote a' =
                  (sum (B'.map fun k => (lookupAt required k).enable)).denote b := by
                simpa [a', b, Polynomial.denote_subst] using hen.denote a
              rcases ctx.allPairwiseExcl_cases hctx hbool hexcl valid with
                ⟨hall0, hsum0, hgate0⟩ | ⟨k, hkmem, hk1, hrest0, hsum1, hgate1⟩
              · left
                refine ⟨henEq.trans hsum0, fun j => ?_, hall0⟩
                by_cases hj : j < maxBucketWidth (g.slot s).args.length required B'
                · have hw := (hwords j (List.mem_range.mpr hj)).denote a
                  simp only [Polynomial.denote_subst] at hw
                  exact hw.trans (hgate0 (fun k => word (lookupAt required k).args j))
                · have hge : (g.slot s).args.length ≤ j :=
                    le_trans (le_maxBucketWidth_init _ required B') (Nat.not_lt.mp hj)
                  simp [word, List.getElem?_eq_none hge, Scalar.Circuit.ArithExpr.denote]
              · right
                refine ⟨k, hkmem, hk1, hrest0, henEq.trans hsum1, fun j => ?_⟩
                by_cases hj : j < maxBucketWidth (g.slot s).args.length required B'
                · have hw := (hwords j (List.mem_range.mpr hj)).denote a
                  simp only [Polynomial.denote_subst] at hw
                  exact hw.trans (hgate1 (fun k' => word (lookupAt required k').args j))
                · have hge1 : (g.slot s).args.length ≤ j :=
                    le_trans (le_maxBucketWidth_init _ required B') (Nat.not_lt.mp hj)
                  have hge2 : (lookupAt required k).args.length ≤ j :=
                    le_trans (le_maxBucketWidth_mem _ required B' hkmem) (Nat.not_lt.mp hj)
                  simp [word, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2,
                    Scalar.Circuit.ArithExpr.denote]
    · have hge : g.sends.length ≤ s := Nat.not_lt.mp hs
      have hB : bucketOf slotMap required.length s = [] := bucketOf_empty_of_ge hbound' hge
      simp [hB, Layout.slot, List.getElem?_eq_none hge, word, Scalar.Circuit.ArithExpr.denote]
  · obtain ⟨hrecv, hbound, hslots⟩ := checked
    have hbound' : ∀ k < required.length, slotOf slotMap k < g.sends.length :=
      fun k hk => hbound k (List.mem_range.mpr hk)
    refine ⟨fun i => hrecv.sound a i, hbound', fun s => ?_⟩
    by_cases hs : s < g.sends.length
    · have hslot := hslots s (List.mem_range.mpr hs)
      dsimp only at hslot ⊢
      generalize hB : bucketOf slotMap required.length s = B at hslot ⊢
      cases B with
      | nil =>
          refine ⟨?_, fun j => ?_⟩
          · simpa [a', Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote] using hslot.1.denote a
          · simpa [a', word, Scalar.Circuit.ArithExpr.denote] using hslot.2.sound a j
      | cons k1 rest =>
          cases rest with
          | nil =>
              refine ⟨?_, fun j => hslot.2.sound a j⟩
              simpa [a', b, Polynomial.denote_subst] using hslot.1.denote a
          | cons k2 tail => exact hslot.elim
    · have hge : g.sends.length ≤ s := Nat.not_lt.mp hs
      have hB : bucketOf slotMap required.length s = [] := bucketOf_empty_of_ge hbound' hge
      simp [hB, Layout.slot, List.getElem?_eq_none hge, word, Scalar.Circuit.ArithExpr.denote]

structure Checked (sources : List (Chip F)) (id : String → Except String Nat) where
  layout : Layout F
  certificate : Certificate sources layout
  finite : layout.FiniteCertificate
  packets : ∀ m ∈ layout.members, m.PacketCertificate id layout
  padding : PacketCheck layout [] #[] (layout.back none) [] [] (fun v => .var v)

/-- Failure rejects the candidate; the heuristic cannot export an uncertified
layout. All proposition decisions below are finite structural checks. -/
def certify (sources : List (Chip F)) (id : String → Except String Nat) (g : Layout F) :
    Except String (Checked sources id) := do
  if hf : g.FiniteCertificate then
    if h : Certificate sources g then
      if hp : ∀ m ∈ g.members, m.PacketCertificate id g then
        if hz : PacketCheck g [] #[] (g.back none) [] [] (fun v => .var v) then
          return ⟨g, h, hf, hp, hz⟩
        else throw s!"group {g.name}: padding packet certificate failed"
      else throw s!"group {g.name}: encoded packet certificate failed"
    else throw s!"group {g.name}: row equivalence certificate failed"
  else throw s!"group {g.name}: finite row certificate failed"

variable {sources : List (Chip F)} {id : String → Except String Nat}

theorem Checked.localRule_iff (checked : Checked sources id) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    checked.layout.RowRule rom root premises ↔ ∃ c ∈ sources, c.LocalRule rom root premises :=
  (checked.layout.rowRule_iff checked.finite rom root premises).trans
    (checked.certificate.localRule_iff rom root premises)

theorem Checked.packet_sound (checked : Checked sources id) (m : Member F)
    (hm : m ∈ checked.layout.members) (a : Nat → F)
    (valid : checked.layout.ValidRow rom a) (active : a m.selector = 1) :
    ∃ provided required, messages id m.origin = .ok (provided, required) ∧
      SamePackets checked.layout m.slotMap a provided required (fun v => a (m.columns[v]?.getD 0)) := by
  obtain ⟨n, hn, _, selectors⟩ := checked.layout.select checked.certificate.shapes a valid.1 valid.2.1
  have sameSelector : n.selector = m.selector := by
    have h := selectors m hm
    by_contra hne
    simp [selected, hne, active] at h
  have same := checked.certificate.unique n hn m hm sameSelector
  subst n
  have back := checked.layout.back_sound checked.certificate.shapes a valid.1 (some m.selector) selectors
  have on : a (m.columns[m.sourceSelector]?.getD 0) = 1 := by
    simpa [← (checked.certificate.shapes m hm).1] using active
  have origCons : Satisfies m.origin.constraints (fun v => a (m.columns[v]?.getD 0)) :=
    checked.layout.selected_origin_constraints m hm a valid.1 on
  have hc := checked.packets m hm
  unfold Member.PacketCertificate at hc
  cases result : messages id m.origin with
  | error error => simp [result] at hc
  | ok pair =>
      obtain ⟨provided, required⟩ := pair
      simp only [result] at hc
      refine ⟨provided, required, rfl, ?_⟩
      have hs := hc.1.sound a (by simpa [Member.project, Scalar.Circuit.ArithExpr.denote] using origCons)
      simpa only [back, Member.project, Scalar.Circuit.ArithExpr.denote] using hs

/-- Every valid source assignment has a finite grouped row with exactly the
same raw lookup messages, including tags, enables, and zero-padded tails. -/
theorem Checked.packet_complete (checked : Checked sources id) (m : Member F)
    (hm : m ∈ checked.layout.members) (a : Nat → F)
    (valid : m.origin.ValidAssignment rom a) :
    ∃ (row : Row F) (provided : List (Polynomial F)) (required : List (Lookup F)),
      row.chip = checked.layout.name ∧ row.values.length = checked.layout.width ∧
      checked.layout.ValidRow rom row.assignment ∧ row.assignment m.selector = 1 ∧
      messages id m.origin = .ok (provided, required) ∧
      SamePackets checked.layout m.slotMap row.assignment provided required a := by
  let b := fun v => (m.embedding v).denote a
  let row := Row.ofAssignment checked.layout.name checked.layout.width b
  have finite := checked.layout.finiteAssignment checked.finite b
    (checked.certificate.extend_valid m hm a valid)
  have hc := checked.packets m hm
  unfold Member.PacketCertificate at hc
  cases result : messages id m.origin with
  | error error => simp [result] at hc
  | ok pair =>
      obtain ⟨provided, required⟩ := pair
      simp only [result] at hc
      refine ⟨row, provided, required, rfl, Row.ofAssignment_length _ _ _, finite.1, ?_, rfl, ?_⟩
      · rw [Row.ofAssignment_agree _ _ _ _ (checked.finite.2.2 m hm).1]
        simpa [b, selected, Scalar.Circuit.ArithExpr.denote] using
          (checked.certificate.extend_selectors m hm m hm).denote a
      · have values : (fun v => ((restrict checked.layout.width v).subst m.embedding).denote a) =
            row.assignment := by
          funext v
          rw [Polynomial.denote_subst]
          exact restrict_denote _ _ b _
        have hs := hc.2.sound a (by simpa [Scalar.Circuit.ArithExpr.denote] using valid.1)
        simpa only [values, Scalar.Circuit.ArithExpr.denote] using hs

theorem Checked.padding_sound (checked : Checked sources id) (a : Nat → F)
    (valid : Satisfies checked.layout.constraints a) (off : checked.layout.activation.denote a = 0) :
    SamePackets checked.layout #[] a [] [] (fun _ => 0) := by
  have selectors := checked.layout.off checked.certificate.shapes a valid off
  have back := checked.layout.back_sound checked.certificate.shapes a valid none selectors
  have h := checked.padding.sound a (fun _ hmem => by cases hmem)
  simpa [SamePackets, bucketOf, back, word, lookupAt, Scalar.Circuit.ArithExpr.denote] using h

theorem Checked.zero_padding (checked : Checked sources id) :
    Satisfies checked.layout.constraints (fun _ => 0) ∧
      checked.layout.activation.denote (fun _ => 0) = 0 ∧
      SamePackets checked.layout #[] (fun _ => 0) [] [] (fun _ => 0) := by
  have valid := checked.certificate.zero_constraints
  have off : checked.layout.activation.denote (fun _ => 0) = 0 := by
    simp [Layout.activation, sum_denote, Function.comp_def, Scalar.Circuit.ArithExpr.denote]
  exact ⟨valid, off, checked.padding_sound _ valid off⟩

end Aiur.Optimized.Grouping
