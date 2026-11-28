import IxCC.Anf.Proof.Defun.FirstOrder

/-! # λ-lifting keeps scope

The scoping half of P8's λ-lifting: a lifted global's body, the walk's image
`b'` of a local function's body renamed onto the function's captures
(`capRen`), is well scoped over the captures and the parameters
(`lifted_ws`), given that `b'` is well scoped where the function stood and
reads nothing out of scope there (which the walk checks). The captures are
complete (`captures_mem`), every capture lands below their count
(`capMap_lt`), and renaming free variables into scope keeps an expression
well scoped (`renameVars_ws`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-! ## Free variables at a deeper base -/

theorem atom_free_shift {d k x : Nat} : ∀ {a : Atom}, x + k ∈ a.free d → x ∈ a.free (d + k)
  | .var i, h => by
    simp only [Atom.free] at h ⊢
    split at h
    · simp only [List.mem_singleton] at h
      rw [if_pos (by omega)]
      simp only [List.mem_singleton]
      omega
    · simp at h
  | .lit _, h => by simp [Atom.free] at h
  | .box, h => by simp [Atom.free] at h

theorem atoms_free_shift {d k x : Nat} : ∀ {as : List Atom}, x + k ∈ Atom.freeList d as → x ∈ Atom.freeList (d + k) as
  | [], h => by simp [Atom.freeList] at h
  | a :: as, h => by
    simp only [Atom.freeList, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (atom_free_shift h)
    · exact .inr (atoms_free_shift h)

mutual

/-- A variable free under `d` binders at index `x + k` is free under `d + k`
binders at index `x`. -/
theorem free_shift {k x : Nat} : ∀ {d : Nat} {e : Exp}, x + k ∈ e.free d → x ∈ e.free (d + k)
  | d, .bind _ b e, h => by
    simp only [Exp.free, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (bindFree_shift h)
    · have := free_shift (d := d + 1) (e := e) h
      rw [show d + 1 + k = d + k + 1 by omega] at this
      exact .inr this
  | d, .join n _ b e, h => by
    simp only [Exp.free, List.mem_append] at h ⊢
    rcases h with h | h
    · have := free_shift (d := d + n) (e := b) h
      rw [show d + n + k = d + k + n by omega] at this
      exact .inl this
    · exact .inr (free_shift h)
  | _, .jump _ _, h => by
    simp only [Exp.free] at h ⊢
    exact atoms_free_shift h
  | d, .case x' alts dft, h => by
    simp only [Exp.free, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (atom_free_shift h))
    · exact .inl (.inr (altsFree_shift h))
    · exact .inr (optFree_shift h)
  | _, .ret _, h => by
    simp only [Exp.free] at h ⊢
    exact atom_free_shift h
  | _, .tick e, h => by
    simp only [Exp.free] at h ⊢
    exact free_shift h
  | _, .trap, h => by simp [Exp.free] at h

theorem bindFree_shift {k x : Nat} : ∀ {d : Nat} {b : Bind}, x + k ∈ b.free d → x ∈ b.free (d + k)
  | _, .atom _, h => by simp only [Bind.free] at h ⊢; exact atom_free_shift h
  | _, .proj .., h => by simp only [Bind.free] at h ⊢; exact atom_free_shift h
  | _, .con .., h => by simp only [Bind.free] at h ⊢; exact atoms_free_shift h
  | _, .prim .., h => by simp only [Bind.free] at h ⊢; exact atoms_free_shift h
  | _, .call .., h => by simp only [Bind.free] at h ⊢; exact atoms_free_shift h
  | _, .app .., h => by
    simp only [Bind.free, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (atom_free_shift h)
    · exact .inr (atoms_free_shift h)
  | _, .glob _, h => by simp [Bind.free] at h
  | d, .fn ps b, h => by
    simp only [Bind.free] at h ⊢
    have := free_shift (d := d + ps.length) (e := b) h
    rw [show d + ps.length + k = d + k + ps.length by omega] at this
    exact this

theorem altsFree_shift {k x : Nat} : ∀ {d : Nat} {alts : List Alt}, x + k ∈ Exp.altsFree d alts →
    x ∈ Exp.altsFree (d + k) alts
  | _, [], h => by simp [Exp.altsFree] at h
  | d, .mk _ n b :: as, h => by
    simp only [Exp.altsFree, List.mem_append] at h ⊢
    rcases h with h | h
    · have := free_shift (d := d + n) (e := b) h
      rw [show d + n + k = d + k + n by omega] at this
      exact .inl this
    · exact .inr (altsFree_shift h)

theorem optFree_shift {k x : Nat} : ∀ {d : Nat} {o : Option Exp}, x + k ∈ Exp.optFree d o →
    x ∈ Exp.optFree (d + k) o
  | _, none, h => by simp [Exp.optFree] at h
  | _, some e, h => by simp only [Exp.optFree] at h ⊢; exact free_shift h

end

/-! ## Renaming into scope -/

theorem atom_rename_ws {f : Nat → Nat} {d Γ Γ' : Nat} : ∀ {a : Atom}, a.WS (d + Γ) →
    (∀ x ∈ a.free d, f x < Γ') → (Atom.renameVars f d a).WS (d + Γ')
  | .var i, h, hf => by
    simp only [Atom.renameVars]
    split
    · simp only [Atom.WS]; omega
    · simp only [Atom.WS]
      have := hf (i - d) (by simp only [Atom.free]; rw [if_pos (by omega)]; exact List.mem_singleton_self _)
      omega
  | .lit _, _, _ => by simp only [Atom.renameVars, Atom.WS]
  | .box, _, _ => by simp only [Atom.renameVars, Atom.WS]

theorem atoms_rename_ws {f : Nat → Nat} {d Γ Γ' : Nat} : ∀ {as : List Atom}, Atom.WSList (d + Γ) as →
    (∀ x ∈ Atom.freeList d as, f x < Γ') → Atom.WSList (d + Γ') (Atom.renameList f d as)
  | [], _, _ => by simp only [Atom.renameList, Atom.WSList]
  | a :: as, h, hf => by
    simp only [Atom.renameList, Atom.WSList] at h ⊢
    refine ⟨atom_rename_ws h.1 fun x hx => hf x ?_, atoms_rename_ws h.2 fun x hx => hf x ?_⟩
    · simp only [Atom.freeList, List.mem_append]; exact .inl hx
    · simp only [Atom.freeList, List.mem_append]; exact .inr hx

theorem renameList_length (f : Nat → Nat) (d : Nat) : ∀ as : List Atom, (Atom.renameList f d as).length = as.length
  | [] => rfl
  | _ :: as => by simp only [Atom.renameList, List.length_cons, renameList_length f d as]

theorem renameAlts_keys (f : Nat → Nat) (d : Nat) :
    ∀ alts : List Alt, altKeys (Exp.renameAlts f d alts) = altKeys alts
  | [] => rfl
  | .mk k n b :: as => by simp only [Exp.renameAlts, altKeys, renameAlts_keys f d as]

mutual

/-- Renaming the free variables of a well-scoped expression into scope keeps it
well scoped. -/
theorem renameVars_ws (S : Sig) (f : Nat → Nat) {Γ Γ' : Nat} :
    ∀ (d : Nat) (Δ : List Nat) (e : Exp), Exp.WS S (d + Γ) Δ e → (∀ x ∈ e.free d, f x < Γ') →
      Exp.WS S (d + Γ') Δ (Exp.renameVars f d e)
  | d, Δ, .bind c b e, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free, List.mem_append] at h hf ⊢
    refine ⟨renameBind_ws S f d b h.1 fun x hx => hf x (.inl hx), ?_⟩
    have h2 : Exp.WS S (d + 1 + Γ) Δ e := by rw [show d + 1 + Γ = d + Γ + 1 by omega]; exact h.2
    have := renameVars_ws S f (d + 1) Δ e h2 fun x hx => hf x (.inr hx)
    rw [show d + 1 + Γ' = d + Γ' + 1 by omega] at this
    exact this
  | d, Δ, .join n r b e, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free, List.mem_append] at h hf ⊢
    have h1 : Exp.WS S (d + n + Γ) (if r then n :: Δ else Δ) b := by
      rw [show d + n + Γ = d + Γ + n by omega]; exact h.1
    have := renameVars_ws S f (d + n) _ b h1 fun x hx => hf x (.inl hx)
    rw [show d + n + Γ' = d + Γ' + n by omega] at this
    exact ⟨this, renameVars_ws S f d (n :: Δ) e h.2 fun x hx => hf x (.inr hx)⟩
  | d, Δ, .jump j as, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free] at h hf ⊢
    exact ⟨by rw [renameList_length]; exact h.1, atoms_rename_ws h.2 hf⟩
  | d, Δ, .case x alts dft, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free, List.mem_append] at h hf ⊢
    obtain ⟨hx, ha, hn, ho⟩ := h
    refine ⟨atom_rename_ws hx fun y hy => hf y (.inl (.inl hy)),
      renameAlts_ws S f d Δ alts ha fun y hy => hf y (.inl (.inr hy)), ?_,
      renameOpt_ws S f d Δ dft ho fun y hy => hf y (.inr hy)⟩
    rw [renameAlts_keys]
    exact hn
  | d, Δ, .ret a, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free] at h hf ⊢
    exact atom_rename_ws h hf
  | d, Δ, .tick e, h, hf => by
    simp only [Exp.WS, Exp.renameVars, Exp.free] at h hf ⊢
    exact renameVars_ws S f d Δ e h hf
  | _, _, .trap, _, _ => by simp only [Exp.WS, Exp.renameVars]

theorem renameBind_ws (S : Sig) (f : Nat → Nat) {Γ Γ' : Nat} :
    ∀ (d : Nat) (b : Bind), Bind.WS S (d + Γ) b → (∀ x ∈ b.free d, f x < Γ') →
      Bind.WS S (d + Γ') (Bind.renameVars f d b)
  | d, .atom a, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    exact atom_rename_ws h hf
  | d, .con c as, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    exact ⟨by rw [renameList_length]; exact h.1, atoms_rename_ws h.2 hf⟩
  | d, .proj c i x, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    exact ⟨h.1, atom_rename_ws h.2 hf⟩
  | d, .prim p as, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    exact ⟨by rw [renameList_length]; exact h.1, atoms_rename_ws h.2 hf⟩
  | d, .glob g, h, _ => by
    simp only [Bind.WS, Bind.renameVars] at h ⊢
    exact h
  | d, .call g as, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    refine ⟨by rw [renameList_length]; exact h.1, ?_, atoms_rename_ws h.2.2 hf⟩
    intro he
    have := congrArg List.length he
    rw [renameList_length] at this
    exact h.2.1 (List.eq_nil_of_length_eq_zero this)
  | d, .app g as, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free, List.mem_append] at h hf ⊢
    refine ⟨atom_rename_ws h.1 fun x hx => hf x (.inl hx), ?_,
      atoms_rename_ws h.2.2 fun x hx => hf x (.inr hx)⟩
    intro he
    have := congrArg List.length he
    rw [renameList_length] at this
    exact h.2.1 (List.eq_nil_of_length_eq_zero this)
  | d, .fn ps b, h, hf => by
    simp only [Bind.WS, Bind.renameVars, Bind.free] at h hf ⊢
    refine ⟨h.1, ?_⟩
    have h2 : Exp.WS S (d + ps.length + Γ) [] b := by
      rw [show d + ps.length + Γ = d + Γ + ps.length by omega]; exact h.2
    have := renameVars_ws S f (d + ps.length) [] b h2 hf
    rw [show d + ps.length + Γ' = d + Γ' + ps.length by omega] at this
    exact this

theorem renameAlts_ws (S : Sig) (f : Nat → Nat) {Γ Γ' : Nat} :
    ∀ (d : Nat) (Δ : List Nat) (alts : List Alt), Exp.AltsWS S (d + Γ) Δ alts →
      (∀ x ∈ Exp.altsFree d alts, f x < Γ') → Exp.AltsWS S (d + Γ') Δ (Exp.renameAlts f d alts)
  | _, _, [], _, _ => by simp only [Exp.AltsWS, Exp.renameAlts]
  | d, Δ, .mk k n b :: as, h, hf => by
    simp only [Exp.AltsWS, Exp.renameAlts, Exp.altsFree, List.mem_append] at h hf ⊢
    have h1 : Exp.WS S (d + n + Γ) Δ b := by rw [show d + n + Γ = d + Γ + n by omega]; exact h.2.1
    have := renameVars_ws S f (d + n) Δ b h1 fun x hx => hf x (.inl hx)
    rw [show d + n + Γ' = d + Γ' + n by omega] at this
    exact ⟨h.1, this, renameAlts_ws S f d Δ as h.2.2 fun x hx => hf x (.inr hx)⟩

theorem renameOpt_ws (S : Sig) (f : Nat → Nat) {Γ Γ' : Nat} :
    ∀ (d : Nat) (Δ : List Nat) (o : Option Exp), Exp.OptWS S (d + Γ) Δ o →
      (∀ x ∈ Exp.optFree d o, f x < Γ') → Exp.OptWS S (d + Γ') Δ (Exp.renameOpt f d o)
  | _, _, none, _, _ => by simp only [Exp.OptWS, Exp.renameOpt]
  | d, Δ, some e, h, hf => by
    simp only [Exp.OptWS, Exp.renameOpt, Exp.optFree] at h hf ⊢
    exact renameVars_ws S f d Δ e h hf


end

/-! ## The captures -/

theorem foldl_insert_isSome {α : Type} : ∀ (xs : List (Nat × α)) (m : Src.NatMap α) {k : Nat},
    ((m.get? k).isSome = true ∨ k ∈ xs.map (·.1)) →
      ((xs.foldl (fun m p => m.insert p.1 p.2) m).get? k).isSome = true
  | [], _, _, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | (k₀, x₀) :: xs, m, k, h => by
    rw [List.foldl_cons]
    refine foldl_insert_isSome xs _ ?_
    by_cases hk : k = k₀
    · left
      subst hk
      simp [Src.NatMap.get?_insert]
    · rcases h with h | h
      · left
        rw [Src.NatMap.get?_insert, if_neg hk]
        exact h
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hk
        · exact .inr h

/-- Every free variable in scope is a capture. -/
theorem captures_mem {Γ x : Nat} {free : List Nat} (hx : x ∈ free) (hlt : x < Γ) : x ∈ captures Γ free := by
  unfold captures
  simp only [List.mem_reverse, List.mem_filter, List.mem_range]
  refine ⟨hlt, ?_⟩
  unfold Src.NatSet.ofList Src.NatMap.contains Src.NatMap.ofList
  exact foldl_insert_isSome _ _ (.inr (by simp [hx]))

/-- Every capture's position is below their count. -/
theorem capMap_lt {caps : List Nat} {x : Nat} (hx : x ∈ caps) : (capMap caps).getD x 0 < caps.length := by
  have hpos : 0 < caps.length := List.length_pos_of_mem hx
  unfold Src.NatMap.getD
  cases hg : (capMap caps).get? x with
  | none => simpa using hpos
  | some v =>
    have hm := ofList_mem hg
    obtain ⟨⟨y, p⟩, -, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    simp only [Option.getD_some]
    omega

/-- **A lifted body is well scoped** over its captures and parameters: the
walk's image `b'` of a local function's body, well scoped where the function
stood (`Γ` values and `n` parameters, no join point) and reading nothing out
of scope there, renamed onto the captures. -/
theorem lifted_ws (S : Sig) {Γ n : Nat} {b' : Exp} (hws : Exp.WS S (Γ + n) [] b')
    (hfree : ∀ x ∈ b'.free n, x < Γ) :
    Exp.WS S ((captures Γ (b'.free n)).length + n) [] (Exp.renameVars (capRen (captures Γ (b'.free n)) n) 0 b') := by
  have h0 : Exp.WS S (0 + (Γ + n)) [] b' := by rw [Nat.zero_add]; exact hws
  have := renameVars_ws S (capRen (captures Γ (b'.free n)) n) (Γ' := (captures Γ (b'.free n)).length + n)
    0 [] b' h0 fun x hx => by
      unfold capRen
      try dsimp only
      split
      · omega
      · have hy : x - n ∈ b'.free n := by
          have := free_shift (d := 0) (k := n) (x := x - n) (e := b') (by rw [Nat.sub_add_cancel (by omega)]; exact hx)
          rwa [Nat.zero_add] at this
        have := capMap_lt (captures_mem hy (hfree _ hy))
        omega
  rwa [Nat.zero_add] at this

end IxCC.Anf.Defun.Proof
