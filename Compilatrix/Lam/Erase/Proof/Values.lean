import Compilatrix.Lam.Erase.Proof.Layout
import Compilatrix.Lam.Erase.Proof.Rel

/-! # Facts about related values

Inverting `VR` on constructors, reading kept fields through `KeptR`, the
kept index `unbox?` derives, constructor keys under the `Decidable ↦ Bool`
alias, and the primitives' agreement (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels)
open Compilatrix.Src.Relevance (FieldClass)

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-! ## Constructors -/

/-- A related constructor value is its unboxed field, or its kept fields
under its key. -/
theorem VR.con_inv {c : CId} {ls : Levels} {ps : List Src.Slot} {fs : List Src.Value} {v' : Val}
    (h : VR I G (.con c ls ps fs) v') {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat}
    {ty : Src.Term} (hd : I.decl? c = some (.ctor sf lv ind cidx np nf ty)) :
    fs.length = nf ∧
      ((∃ j a, I.unbox? ind [] = some j ∧ fs[j]? = some a ∧ VR I G a v' ∧
          ∀ i f, fs[i]? = some f → i ≠ j → f.isIrr = true) ∨
        (I.unbox? ind [] = none ∧ ∃ fs', v' = .con (I.ctorKey c) fs' ∧ KeptR I G c 0 fs fs')) := by
  cases h with
  | quot hq _ => rw [hd] at hq; cases hq
  | unboxed hd' hl hu hj ha hirr =>
    rw [hd] at hd'
    cases hd'
    exact ⟨hl, .inl ⟨_, _, hu, hj, ha, hirr⟩⟩
  | con hd' hl hu hk =>
    rw [hd] at hd'
    cases hd'
    exact ⟨hl, .inr ⟨hu, _, rfl, hk⟩⟩

theorem KeptR.get_drop {c : CId} :
    ∀ {i : Nat} {fs : List Src.Value} {fs' : List Val}, KeptR I G c i fs fs' →
      ∀ {j : Nat} {f : Src.Value}, fs[j]? = some f → I.kept c [] (i + j) = false → f.isIrr = true
  | _, _, _, .nil, _, _, h, _ => by simp at h
  | _, _, _, .kept hk _ _, 0, _, h, hj => by simp at h hj; rw [hj] at hk; cases hk
  | _, _, _, .kept _ _ hr, j + 1, _, h, hj => by
    simp only [List.getElem?_cons_succ] at h
    exact hr.get_drop h (by rw [← hj]; congr 1; omega)
  | _, _, _, .drop _ hf _, 0, _, h, _ => by simp at h; subst h; exact hf
  | _, _, _, .drop _ _ hr, j + 1, _, h, hj => by
    simp only [List.getElem?_cons_succ] at h
    exact hr.get_drop h (by rw [← hj]; congr 1; omega)

/-- The number of kept fields among the first `j`, from field `i`. -/
def keptBelow (I : Input) (c : CId) (i j : Nat) : Nat :=
  ((List.range j).filter fun x => I.kept c [] (i + x)).length

theorem keptBelow_succ (c : CId) (i j : Nat) :
    keptBelow I c i (j + 1) = keptBelow I c i j + if I.kept c [] (i + j) then 1 else 0 := by
  simp only [keptBelow, List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

theorem keptBelow_shift (c : CId) (i j : Nat) :
    keptBelow I c i (j + 1) =
      (if I.kept c [] i then 1 else 0) + keptBelow I c (i + 1) j := by
  induction j with
  | zero => cases h : I.kept c [] i <;> simp [keptBelow, h]
  | succ j ih =>
    rw [keptBelow_succ, ih, keptBelow_succ]
    have : i + (j + 1) = i + 1 + j := by omega
    rw [this]
    omega

theorem KeptR.get_kept {c : CId} :
    ∀ {i : Nat} {fs : List Src.Value} {fs' : List Val}, KeptR I G c i fs fs' →
      ∀ {j : Nat} {f : Src.Value}, fs[j]? = some f → I.kept c [] (i + j) = true →
        ∃ f', fs'[keptBelow I c i j]? = some f' ∧ VR I G f f'
  | _, _, _, .nil, _, _, h, _ => by simp at h
  | _, _, _, .kept _ hv _, 0, _, h, _ => by
    simp at h; subst h; exact ⟨_, by simp [keptBelow], hv⟩
  | i, _, _, .kept hk _ hr, j + 1, _, h, hj => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨f', h', hv⟩ := hr.get_kept h (by rw [← hj]; congr 1; omega)
    refine ⟨f', ?_, hv⟩
    rw [keptBelow_shift, hk, if_pos rfl, Nat.add_comm, List.getElem?_cons_succ]
    exact h'
  | _, _, _, .drop hk _ _, 0, _, _, hj => by simp at hj; rw [hj] at hk; cases hk
  | i, _, _, .drop hk _ hr, j + 1, _, h, hj => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨f', h', hv⟩ := hr.get_kept h (by rw [← hj]; congr 1; omega)
    refine ⟨f', ?_, hv⟩
    rw [keptBelow_shift, hk]
    simpa using h'

theorem KeptR.length {c : CId} :
    ∀ {i : Nat} {fs : List Src.Value} {fs' : List Val}, KeptR I G c i fs fs' →
      fs'.length = keptBelow I c i fs.length
  | _, _, _, .nil => by simp [keptBelow]
  | i, _, _, .kept hk _ hr => by
    rw [List.length_cons, List.length_cons, keptBelow_shift, hk, hr.length, if_pos rfl]
    omega
  | i, _, _, .drop hk _ hr => by
    rw [List.length_cons, keptBelow_shift, hk, hr.length]
    simp

theorem rank_eq_keptBelow (c : CId) (q : Profile) (j : Nat) :
    I.rank c q j = keptBelow I c 0 j := by
  simp only [Input.rank, keptBelow, Nat.zero_add, Input.kept_fun]

theorem keptCount_eq_keptBelow (c : CId) (q : Profile) (n : Nat) :
    I.keptCount c q n = keptBelow I c 0 n := by
  simp only [Input.keptCount, rank_eq_keptBelow]

/-! ## The unboxed field -/

theorem mem_zipIdx_filter {α : Type} (xs : List α) (p : α → Bool) (i : Nat) :
    i ∈ (xs.zipIdx.filter fun x => p x.1).map (·.2) ↔ ∃ a, xs[i]? = some a ∧ p a = true := by
  constructor
  · intro h
    obtain ⟨⟨a, i'⟩, hm, rfl⟩ := List.mem_map.1 h
    rw [List.mem_filter] at hm
    obtain ⟨hz, hp⟩ := hm
    rw [List.mem_zipIdx_iff_getElem?] at hz
    exact ⟨a, by simpa using hz, hp⟩
  · rintro ⟨a, ha, hp⟩
    refine List.mem_map.2 ⟨(a, i), ?_, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
    exact ⟨by simpa using ha, hp⟩

/-- The option computation after `unbox?` finds the kept index returns that
index or nothing. -/
theorem unbox?_tail_eq {α : Type} {o : Option α} {j j' : Nat}
    (h : (o.bind fun _ => some j') = some j) : j' = j := by
  cases o <;> simp_all

/-- `unbox? t q = some j`: `t` has one constructor, and `j` is its only
field kept at `q`. -/
theorem unbox?_spec {t : CId} {q : Profile} {j : Nat} (h : I.unbox? t q = some j) :
    ∃ k, I.ctorsOf t = [k] ∧ I.kept k q j = true ∧ ∀ i, i ≠ j → I.kept k q i = false := by
  revert h
  unfold Input.unbox?
  cases hd : I.decl? t with
  | none => intro h; cases h
  | some d =>
    cases d with
    | induct _ _ np _ ty _ =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · next k hk =>
        cases hf : I.fields? k with
        | none => intro h; cases h
        | some fields =>
          simp only [Option.bind_some]
          split
          · next j' hj' =>
            intro h
            have hjj : j' = j := by
              revert h
              split
              · intro h; cases h
              · cases I.decl? k with
                | none => intro h; cases h
                | some dk =>
                  cases dk with
                  | ctor _ _ _ _ _ _ cty =>
                    simp only [Option.bind_some]
                    cases piDomain? (np + j') cty with
                    | none => intro h; cases h
                    | some fieldTy =>
                      simp only [Option.bind_some]
                      split
                      · intro h; cases h
                      · intro h; simp at h; exact h.2
                  | _ => intro h; cases h
            subst hjj
            have hkept : ∀ i, I.kept k q i = true ↔ i = j' := by
              intro i
              have hm := mem_zipIdx_filter fields (fun c => !c.dropP q) i
              rw [hj'] at hm
              simp only [List.mem_singleton] at hm
              simp only [Input.kept, hf]
              constructor
              · intro hi
                apply hm.2
                cases hfi : fields[i]? with
                | none => rw [hfi] at hi; cases hi
                | some cls => rw [hfi] at hi; exact ⟨cls, rfl, by simpa using hi⟩
              · intro hi
                obtain ⟨cls, hcls, hp⟩ := hm.1 hi
                rw [hcls]
                simpa using hp
            exact ⟨k, hk, (hkept j').2 rfl, fun i hi => by
              cases hki : I.kept k q i with
              | false => rfl
              | true => exact absurd ((hkept i).1 hki) hi⟩
          · intro h; cases h
      · intro h; cases h
    | _ => intro h; cases h

/-! ## Primitives -/

theorem prim_sem_ofSrc (op : Src.PrimOp) (ns : List Nat) :
    Prim.sem (Prim.ofSrc op) ns = op.evalLits ns := by
  match ns with
  | [] => cases op <;> rfl
  | [a] => cases op <;> rfl
  | [a, b] => cases op <;> rfl
  | _ :: _ :: _ :: _ => cases op <;> rfl

end Compilatrix.Lam.Erase.Proof
