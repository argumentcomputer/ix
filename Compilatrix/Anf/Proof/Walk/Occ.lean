import Compilatrix.Anf.Proof.Walk.At

/-! # The rewriting walk: occurrences of dropped bindings

`NoDead live jlive e` says no dropped value binding (`live = false`) and no
dropped join point occurs in `e`; these lemmas pass it to subterms and read
off that an atom the walk resolves is live (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

theorem getElem?_cons_succ' {α : Type} (x : α) (xs : List α) (i : Nat) :
    (x :: xs)[i + 1]? = xs[i]? := rfl

theorem getElem?_replicate_append {α : Type} (n : Nat) (x : α) (xs : List α) (i : Nat) :
    (List.replicate n x ++ xs)[i + n]? = xs[i]? := by
  rw [List.getElem?_append_right (by simp)]; simp

theorem getElem?_replicate_lt {α : Type} {n : Nat} (x : α) (xs : List α) {i : Nat} (hi : i < n) :
    (List.replicate n x ++ xs)[i]? = some x := by
  rw [List.getElem?_append_left (by simp; exact hi)]; simp [hi]

/-! ## Passing `NoDead` down -/

theorem NoDead.bind_rhs {live jlive : List Bool} {c : Ixon.V3.LetContract} {b : Bind} {e : Exp}
    (h : NoDead live jlive (.bind c b e)) : ∀ i, live[i]? = some false → b.occ i = 0 := fun i hi => by
  have := h.1 i hi; simp only [Exp.occ] at this; omega

theorem NoDead.bind_body {live jlive : List Bool} {c : Ixon.V3.LetContract} {b : Bind} {e : Exp}
    (h : NoDead live jlive (.bind c b e)) (x : Bool) (h0 : x = false → e.occ 0 = 0) :
    NoDead (x :: live) jlive e := by
  refine ⟨fun i hi => ?_, fun j hj => by have := h.2 j hj; simpa [Exp.jocc] using this⟩
  cases i with
  | zero => simp at hi; exact h0 hi
  | succ i =>
    have := h.1 i (by simpa using hi)
    simp only [Exp.occ] at this; omega

theorem NoDead.join_body {live jlive : List Bool} {ar : Nat} {r : Bool} {b e : Exp}
    (h : NoDead live jlive (.join ar r b e)) :
    NoDead (List.replicate ar true ++ live) (if r then true :: jlive else jlive) b := by
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · by_cases hlt : i < ar
    · rw [getElem?_replicate_lt true live hlt] at hi; cases hi
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + ar := ⟨i - ar, by omega⟩
      rw [getElem?_replicate_append] at hi
      have := h.1 i' hi; simp only [Exp.occ] at this
      omega
  · cases r
    · have := h.2 j hj; simp only [Exp.jocc] at this; simp at this ⊢; omega
    · cases j with
      | zero => simp at hj
      | succ j =>
        have := h.2 j (by simpa using hj)
        simp only [Exp.jocc] at this; simp at this ⊢; omega

theorem NoDead.join_rest {live jlive : List Bool} {ar : Nat} {r : Bool} {b e : Exp}
    (h : NoDead live jlive (.join ar r b e)) (x : Bool) (h0 : x = false → e.jocc 0 = 0) :
    NoDead live (x :: jlive) e := by
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := h.1 i hi; simp only [Exp.occ] at this; omega
  · cases j with
    | zero => simp at hj; exact h0 hj
    | succ j =>
      have := h.2 j (by simpa using hj)
      simp only [Exp.jocc] at this; omega

theorem NoDead.tick {live jlive : List Bool} {e : Exp} (h : NoDead live jlive (.tick e)) :
    NoDead live jlive e :=
  ⟨fun i hi => by simpa [Exp.occ] using h.1 i hi, fun j hj => by simpa [Exp.jocc] using h.2 j hj⟩

theorem NoDead.case_atom {live jlive : List Bool} {x : Atom} {alts : List Alt} {d : Option Exp}
    (h : NoDead live jlive (.case x alts d)) : ∀ i, live[i]? = some false → x.occ i = 0 :=
  fun i hi => by have := h.1 i hi; simp only [Exp.occ] at this; omega

theorem NoDead.case_dflt {live jlive : List Bool} {x : Atom} {alts : List Alt} {e : Exp}
    (h : NoDead live jlive (.case x alts (some e))) : NoDead live jlive e :=
  ⟨fun i hi => by have := h.1 i hi; simp only [Exp.occ, Exp.optOcc] at this; omega,
   fun j hj => by have := h.2 j hj; simp only [Exp.jocc, Exp.optJocc] at this; omega⟩

theorem altsOcc_mem {i : Nat} : ∀ {alts : List Alt}, Exp.altsOcc i alts = 0 →
    ∀ a ∈ alts, Exp.occ (i + a.arity) a.body = 0
  | [], _, _, ha => by simp at ha
  | .mk k n b :: as, h, a, ha => by
    simp only [Exp.altsOcc] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · simp only [Alt.arity, Alt.body]; omega
    · exact altsOcc_mem (by omega) a ha

theorem altsJocc_mem {j : Nat} : ∀ {alts : List Alt}, Exp.altsJocc j alts = 0 →
    ∀ a ∈ alts, Exp.jocc j a.body = 0
  | [], _, _, ha => by simp at ha
  | .mk k n b :: as, h, a, ha => by
    simp only [Exp.altsJocc] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · simp only [Alt.body]; omega
    · exact altsJocc_mem (by omega) a ha

theorem NoDead.case_alts {live jlive : List Bool} {x : Atom} {alts : List Alt} {d : Option Exp}
    (h : NoDead live jlive (.case x alts d)) :
    ∀ a ∈ alts, NoDead (List.replicate a.arity true ++ live) jlive a.body := by
  intro a ha
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · by_cases hlt : i < a.arity
    · rw [getElem?_replicate_lt true live hlt] at hi; cases hi
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + a.arity := ⟨i - a.arity, by omega⟩
      rw [getElem?_replicate_append] at hi
      have h1 := h.1 i' hi; simp only [Exp.occ] at h1
      exact altsOcc_mem (by omega) a ha
  · have h2 := h.2 j hj; simp only [Exp.jocc] at h2
    exact altsJocc_mem (by omega) a ha

/-! ## Live atoms -/

theorem atom_live {live : List Bool} {σ : List Ent} {a : Atom}
    (hlen : σ.length = live.length) (hocc : ∀ i, live[i]? = some false → a.occ i = 0) :
    ∀ i, a = .var i → σ[i]? ≠ none → live[i]? = some true := by
  intro i ha hσ
  subst ha
  have hi : i < live.length := by
    rw [← hlen]
    rcases Nat.lt_or_ge i σ.length with h | h
    · exact h
    · exact absurd (List.getElem?_eq_none h) hσ
  cases hl : live[i] with
  | true => rw [List.getElem?_eq_getElem hi, hl]
  | false =>
    have := hocc i (by rw [List.getElem?_eq_getElem hi, hl])
    simp [Atom.occ] at this

theorem atoms_live {live : List Bool} {σ : List Ent} : ∀ {as : List Atom},
    σ.length = live.length → (∀ i, live[i]? = some false → Atom.occList i as = 0) →
    ∀ i, Atom.var i ∈ as → σ[i]? ≠ none → live[i]? = some true
  | [], _, _, _, h, _ => by simp at h
  | a :: as, hlen, hocc, i, hmem, hσ => by
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact atom_live hlen (fun j hj => by have := hocc j hj; simp only [Atom.occList] at this; omega)
        i rfl hσ
    · exact atoms_live hlen (fun j hj => by have := hocc j hj; simp only [Atom.occList] at this; omega)
        i hmem hσ

end Compilatrix.Anf.WalkProof
