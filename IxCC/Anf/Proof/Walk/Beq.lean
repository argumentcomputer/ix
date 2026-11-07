import IxCC.Anf.Syntax

/-! # Structural equality of Anf terms is equality

Shrink's equal-arms rule compares alternatives with `Exp.beq`; its
correctness needs `Exp.beq e e' = true → e = e'` (M2.3). The contracts'
derived `BEq` instances are lawful (each unfolds to its fields'
comparisons). -/

set_option autoImplicit false

namespace IxCC.Ixon

instance : LawfulBEq Uses where
  rfl := by intro u; cases u <;> rfl
  eq_of_beq := by intro u u' h; cases u <;> cases u' <;> first | rfl | exact absurd h (by decide)

namespace V3

instance : LawfulBEq BinderContract where
  rfl := by
    intro b
    obtain ⟨u, v⟩ := b
    show (u == u && v == v) = true
    simp
  eq_of_beq := by
    intro b b' h
    obtain ⟨u, v⟩ := b
    obtain ⟨u', v'⟩ := b'
    have h' : (u == u' && v == v') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl

instance : LawfulBEq LetContract where
  rfl := by
    intro c
    obtain ⟨a, k, b⟩ := c
    show (a == a && (k == k && b == b)) = true
    simp
  eq_of_beq := by
    intro c c' h
    obtain ⟨a, k, b⟩ := c
    obtain ⟨a', k', b'⟩ := c'
    have h' : (a == a' && (k == k' && b == b')) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    rfl

end V3

end IxCC.Ixon

namespace IxCC.Anf

theorem Atom.beq_eq : ∀ {a a' : Atom}, a.beq a' = true → a = a'
  | .var i, .var j, h => by simp [Atom.beq] at h; rw [h]
  | .lit l, .lit l', h => by simp [Atom.beq] at h; rw [h]
  | .box, .box, _ => rfl
  | .var _, .lit _, h | .var _, .box, h | .lit _, .var _, h | .lit _, .box, h | .box, .var _, h
  | .box, .lit _, h => by simp [Atom.beq] at h

theorem atomsBeq_eq : ∀ {as as' : List Atom}, atomsBeq as as' = true → as = as'
  | [], [], _ => rfl
  | a :: as, a' :: as', h => by
    simp only [atomsBeq, Bool.and_eq_true] at h
    rw [Atom.beq_eq h.1, atomsBeq_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [atomsBeq] at h

mutual

theorem Exp.beq_eq : ∀ {e e' : Exp}, e.beq e' = true → e = e'
  | .bind c b e, .bind c' b' e', h => by
    simp only [Exp.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hb⟩, he⟩ := h
    rw [Bind.beq_eq hb, Exp.beq_eq he]
  | .join n r b e, .join n' r' b' e', h => by
    simp only [Exp.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hb⟩, he⟩ := h
    rw [Exp.beq_eq hb, Exp.beq_eq he]
  | .jump j as, .jump j' as', h => by
    simp only [Exp.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ha⟩ := h
    rw [atomsBeq_eq ha]
  | .case x alts d, .case x' alts' d', h => by
    simp only [Exp.beq, Bool.and_eq_true] at h
    obtain ⟨⟨hx, ha⟩, hd⟩ := h
    rw [Atom.beq_eq hx, Exp.altsBeq_eq ha, Exp.optBeq_eq hd]
  | .ret a, .ret a', h => by simp only [Exp.beq] at h; rw [Atom.beq_eq h]
  | .tick e, .tick e', h => by simp only [Exp.beq] at h; rw [Exp.beq_eq h]
  | .trap, .trap, _ => rfl
  | .bind .., .join .., h | .bind .., .jump .., h | .bind .., .case .., h | .bind .., .ret _, h
  | .bind .., .tick _, h | .bind .., .trap, h
  | .join .., .bind .., h | .join .., .jump .., h | .join .., .case .., h | .join .., .ret _, h
  | .join .., .tick _, h | .join .., .trap, h
  | .jump .., .bind .., h | .jump .., .join .., h | .jump .., .case .., h | .jump .., .ret _, h
  | .jump .., .tick _, h | .jump .., .trap, h
  | .case .., .bind .., h | .case .., .join .., h | .case .., .jump .., h | .case .., .ret _, h
  | .case .., .tick _, h | .case .., .trap, h
  | .ret _, .bind .., h | .ret _, .join .., h | .ret _, .jump .., h | .ret _, .case .., h
  | .ret _, .tick _, h | .ret _, .trap, h
  | .tick _, .bind .., h | .tick _, .join .., h | .tick _, .jump .., h | .tick _, .case .., h
  | .tick _, .ret _, h | .tick _, .trap, h
  | .trap, .bind .., h | .trap, .join .., h | .trap, .jump .., h | .trap, .case .., h
  | .trap, .ret _, h | .trap, .tick _, h => by simp [Exp.beq] at h

theorem Bind.beq_eq : ∀ {b b' : Bind}, b.beq b' = true → b = b'
  | .atom a, .atom a', h => by simp only [Bind.beq] at h; rw [Atom.beq_eq h]
  | .con c as, .con c' as', h => by
    simp only [Bind.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, ha⟩ := h
    rw [atomsBeq_eq ha]
  | .proj c i x, .proj c' i' x', h => by
    simp only [Bind.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hx⟩ := h
    rw [Atom.beq_eq hx]
  | .prim p as, .prim p' as', h => by
    simp only [Bind.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ha⟩ := h
    rw [atomsBeq_eq ha]
  | .glob g, .glob g', h => by simp only [Bind.beq, beq_iff_eq] at h; rw [h]
  | .call g as, .call g' as', h => by
    simp only [Bind.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ha⟩ := h
    rw [atomsBeq_eq ha]
  | .app f as, .app f' as', h => by
    simp only [Bind.beq, Bool.and_eq_true] at h
    obtain ⟨hf, ha⟩ := h
    rw [Atom.beq_eq hf, atomsBeq_eq ha]
  | .fn ps b, .fn ps' b', h => by
    simp only [Bind.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hb⟩ := h
    rw [Exp.beq_eq hb]
  | .atom _, .con .., h | .atom _, .proj .., h | .atom _, .prim .., h | .atom _, .glob _, h
  | .atom _, .call .., h | .atom _, .app .., h | .atom _, .fn .., h
  | .con .., .atom _, h | .con .., .proj .., h | .con .., .prim .., h | .con .., .glob _, h
  | .con .., .call .., h | .con .., .app .., h | .con .., .fn .., h
  | .proj .., .atom _, h | .proj .., .con .., h | .proj .., .prim .., h | .proj .., .glob _, h
  | .proj .., .call .., h | .proj .., .app .., h | .proj .., .fn .., h
  | .prim .., .atom _, h | .prim .., .con .., h | .prim .., .proj .., h | .prim .., .glob _, h
  | .prim .., .call .., h | .prim .., .app .., h | .prim .., .fn .., h
  | .glob _, .atom _, h | .glob _, .con .., h | .glob _, .proj .., h | .glob _, .prim .., h
  | .glob _, .call .., h | .glob _, .app .., h | .glob _, .fn .., h
  | .call .., .atom _, h | .call .., .con .., h | .call .., .proj .., h | .call .., .prim .., h
  | .call .., .glob _, h | .call .., .app .., h | .call .., .fn .., h
  | .app .., .atom _, h | .app .., .con .., h | .app .., .proj .., h | .app .., .prim .., h
  | .app .., .glob _, h | .app .., .call .., h | .app .., .fn .., h
  | .fn .., .atom _, h | .fn .., .con .., h | .fn .., .proj .., h | .fn .., .prim .., h
  | .fn .., .glob _, h | .fn .., .call .., h | .fn .., .app .., h => by simp [Bind.beq] at h

theorem Exp.altsBeq_eq : ∀ {as as' : List Alt}, Exp.altsBeq as as' = true → as = as'
  | [], [], _ => rfl
  | .mk k n b :: as, .mk k' n' b' :: as', h => by
    simp only [Exp.altsBeq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hb⟩, ha⟩ := h
    rw [Exp.beq_eq hb, Exp.altsBeq_eq ha]
  | [], _ :: _, h | _ :: _, [], h => by simp [Exp.altsBeq] at h

theorem Exp.optBeq_eq : ∀ {d d' : Option Exp}, Exp.optBeq d d' = true → d = d'
  | none, none, _ => rfl
  | some e, some e', h => by simp only [Exp.optBeq] at h; rw [Exp.beq_eq h]
  | none, some _, h | some _, none, h => by simp [Exp.optBeq] at h

end

end IxCC.Anf
