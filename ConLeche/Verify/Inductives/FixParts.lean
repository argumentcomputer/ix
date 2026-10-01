module

public import ConLeche.Kernel.Inductives.NativeParts

public section

/-!
# The direct recursive recogniser, inverted (task #188)

`nativeShape?` is the sum route's core recogniser without the
one-constructor exclusion; `nativeParts?` adds the field kinds
(`nativeKinds?`, one list per constructor).  The inversions give
the pins the P tier consumes: the `isProp` datum, the recursor's level
parameters, the constructors' level parameters and the kinds'
placeholder.  What the recogniser pinned before task #220 and no longer
does — the recursor's NAME, its rule count and rule metadata, the
constructors' result shape — is checked at the install, where a
mismatch REJECTS (`checkNativeRec`, `checkSumCtor`); the facts
the P tier still needs come from those stages' own inversions
(`checkNativeRec_name`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- `nativeShape?` pins the block's data (task #220: everything the
recursor RECORD claims — its name, its level parameters, its rule count
and rule metadata — is the RECURSOR PIN's, thrown at
`checkNativeRec`, and no longer the recogniser's; so is the
constructors' result shape, official's "invalid return type", thrown at
`checkSumCtor`). -/
theorem nativeShape?_inv {nPd : Nat} {block : List ConstantInfo} {p : InductiveShape}
    (h : nativeShape? nPd block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false := by
  unfold nativeShape? at h
  split at h
  · next cvT caps rest =>
    split at h
    · next cs cvR mI rP rules hsplit =>
      try dsimp only at h
      split at h
      · exact nomatch h
      · next nPnIdx nP nIdx hcnt =>
        try dsimp only at h
        split at h
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
          generalize hs : (match Expr.stripPis (nP + nIdx) cvT.type with
            | some (_, .sort s) => s
            | _ => .zero) = s at h
          try dsimp only at h
          have hcs : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)),
              c.1.levelParams = cvT.levelParams ∧
              reservedBasisNames.contains c.1.name = false := by
            intro c hc'
            obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
            have := hc.2 c' hc''
            try simp only [Bool.and_eq_true, beq_iff_eq] at this
            exact ⟨this.1.2, this.2⟩
          split at h
          · obtain rfl := Option.some.inj h
            exact ⟨rfl, hcs, hc.1.1, hc.1.2⟩
          · obtain rfl := Option.some.inj h
            exact ⟨rfl, hcs, hc.1.1, hc.1.2⟩
        · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- A successful `mapM` in `Option` yields as many results. -/
theorem List.mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [List.mapM_option_length hbs]

/-- The recogniser is shape-only (task #210 Part D): the record's kinds
are the placeholder the install fills. -/
theorem nativeParts?_inv {nPd : Nat} {block : List ConstantInfo} {p : NativeParts}
    (h : nativeParts? nPd block = some p) :
    nativeShape? nPd block = some p.toInductiveShape ∧ p.kinds = [] := by
  unfold nativeParts? at h
  cases hs : nativeShape? nPd block with
  | none => rw [hs] at h; exact nomatch h
  | some p' =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

end ConLeche
