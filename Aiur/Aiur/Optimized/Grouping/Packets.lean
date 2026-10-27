import Aiur.Optimized.Grouping.Certificate
import Aiur.Optimized.Grouping.Finite

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def word (ps : List (Polynomial F)) (i : Nat) : Polynomial F := ps[i]?.getD (.const 0)

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

/-- Compare every encoded channel/width tag, enabled message, argument word,
and zero-padded tail. The logical payload check alone would omit these. -/
def PacketCheck (g : Layout F) (left : Nat → Polynomial F)
    (provided : List (Polynomial F)) (required : List (Lookup F))
    (right : Nat → Polynomial F) : Prop :=
  VectorCheck g.receive provided left right ∧
    ∀ i ∈ List.range (max g.sends.length required.length),
      ((g.slot i).enable.subst left).Identical ((lookupAt required i).enable.subst right) ∧
      VectorCheck (g.slot i).args (lookupAt required i).args left right

instance (g : Layout F) (left : Nat → Polynomial F) (provided : List (Polynomial F))
    (required : List (Lookup F)) (right : Nat → Polynomial F) :
    Decidable (PacketCheck g left provided required right) := by unfold PacketCheck; infer_instance

def Member.PacketCertificate (id : String → Except String Nat) (g : Layout F) (m : Member F) : Prop :=
  match messages id m.origin with
  | .error _ => False
  | .ok (provided, required) =>
      PacketCheck g (g.back (some m.selector)) provided required m.project ∧
      PacketCheck g (fun v => (restrict g.width v).subst m.embedding)
        provided required (fun v => .var v)

instance (id : String → Except String Nat) (g : Layout F) (m : Member F) :
    Decidable (m.PacketCertificate id g) := by unfold Member.PacketCertificate; split <;> infer_instance

/-- Values seen by the lookup protocol, extended with zeros in absent slots. -/
def SamePackets (g : Layout F) (a : Nat → F) (provided : List (Polynomial F))
    (required : List (Lookup F)) (b : Nat → F) : Prop :=
  (∀ i, (word g.receive i).denote a = (word provided i).denote b) ∧
    ∀ i, (g.slot i).enable.denote a = (lookupAt required i).enable.denote b ∧
      ∀ j, (word (g.slot i).args j).denote a = (word (lookupAt required i).args j).denote b

theorem PacketCheck.sound {g : Layout F} {left right : Nat → Polynomial F}
    {provided : List (Polynomial F)} {required : List (Lookup F)}
    (checked : PacketCheck g left provided required right) (a : Nat → F) :
    SamePackets g (fun v => (left v).denote a) provided required (fun v => (right v).denote a) := by
  refine ⟨fun i => checked.1.sound a i, ?_⟩
  intro i
  by_cases bound : i < max g.sends.length required.length
  · have h := checked.2 i (List.mem_range.mpr bound)
    refine ⟨?_, fun j => h.2.sound a j⟩
    simpa only [Polynomial.denote_subst] using h.1.denote a
  · have hg : g.sends.length ≤ i := by omega
    have hr : required.length ≤ i := by omega
    simp [Layout.slot, lookupAt, List.getElem?_eq_none hg, List.getElem?_eq_none hr,
      word, Scalar.Circuit.ArithExpr.denote]

structure Checked (sources : List (Chip F)) (id : String → Except String Nat) where
  layout : Layout F
  certificate : Certificate sources layout
  finite : layout.FiniteCertificate
  packets : ∀ m ∈ layout.members, m.PacketCertificate id layout
  padding : PacketCheck layout (layout.back none) [] [] (fun v => .var v)

/-- Failure rejects the candidate; the heuristic cannot export an uncertified
layout. All proposition decisions below are finite structural checks. -/
def certify (sources : List (Chip F)) (id : String → Except String Nat) (g : Layout F) :
    Except String (Checked sources id) := do
  if hf : g.FiniteCertificate then
    if h : Certificate sources g then
      if hp : ∀ m ∈ g.members, m.PacketCertificate id g then
        if hz : PacketCheck g (g.back none) [] [] (fun v => .var v) then
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
      SamePackets checked.layout a provided required (fun v => a (m.columns[v]?.getD 0)) := by
  obtain ⟨n, hn, _, selectors⟩ := checked.layout.select checked.certificate.shapes a valid.1 valid.2.1
  have sameSelector : n.selector = m.selector := by
    have h := selectors m hm
    by_contra hne
    simp [selected, hne, active] at h
  have same := checked.certificate.unique n hn m hm sameSelector
  subst n
  have back := checked.layout.back_sound checked.certificate.shapes a valid.1 (some m.selector) selectors
  have hc := checked.packets m hm
  unfold Member.PacketCertificate at hc
  cases result : messages id m.origin with
  | error error => simp [result] at hc
  | ok pair =>
      obtain ⟨provided, required⟩ := pair
      simp only [result] at hc
      refine ⟨provided, required, rfl, ?_⟩
      simpa only [back, Member.project, Scalar.Circuit.ArithExpr.denote] using hc.1.sound a

/-- Every valid source assignment has a finite grouped row with exactly the
same raw lookup messages, including tags, enables, and zero-padded tails. -/
theorem Checked.packet_complete (checked : Checked sources id) (m : Member F)
    (hm : m ∈ checked.layout.members) (a : Nat → F)
    (valid : m.origin.ValidAssignment rom a) :
    ∃ (row : Row F) (provided : List (Polynomial F)) (required : List (Lookup F)),
      row.chip = checked.layout.name ∧ row.values.length = checked.layout.width ∧
      checked.layout.ValidRow rom row.assignment ∧ row.assignment m.selector = 1 ∧
      messages id m.origin = .ok (provided, required) ∧
      SamePackets checked.layout row.assignment provided required a := by
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
        simpa only [values, Scalar.Circuit.ArithExpr.denote] using hc.2.sound a

theorem Checked.padding_sound (checked : Checked sources id) (a : Nat → F)
    (valid : Satisfies checked.layout.constraints a) (off : checked.layout.activation.denote a = 0) :
    SamePackets checked.layout a [] [] (fun _ => 0) := by
  have selectors := checked.layout.off checked.certificate.shapes a valid off
  have back := checked.layout.back_sound checked.certificate.shapes a valid none selectors
  have h := checked.padding.sound a
  simpa [SamePackets, back, word, lookupAt, Scalar.Circuit.ArithExpr.denote] using h

theorem Checked.zero_padding (checked : Checked sources id) :
    Satisfies checked.layout.constraints (fun _ => 0) ∧
      checked.layout.activation.denote (fun _ => 0) = 0 ∧
      SamePackets checked.layout (fun _ => 0) [] [] (fun _ => 0) := by
  have valid := checked.certificate.zero_constraints
  have off : checked.layout.activation.denote (fun _ => 0) = 0 := by
    simp [Layout.activation, sum_denote, Function.comp_def, Scalar.Circuit.ArithExpr.denote]
  exact ⟨valid, off, checked.padding_sound _ valid off⟩

end Aiur.Optimized.Grouping
