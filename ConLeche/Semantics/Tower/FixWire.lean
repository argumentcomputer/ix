module

public import ConLeche.Semantics.Tower.FixRecI
import ConLeche.Semantics.Tower.SumWire

@[expose] public section

/-!
# The recursive recursor leaf's closedness (task #188)

`nativeRecAVI` — the selected fixed point of the one-step
unfolding — is a closed term: the recursor type is a Π-tower over
closed binder data, the body's case split with inductive hypotheses
sits one below the K-frame, and an inductive-hypothesis argument
mentions the unfolded function, the block's variables, the field's
index expressions (moved to the payload's projections) and the
payload's projection only.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify

/-! ## Instantiation and the payload's projections -/

/-- Instantiation at a bounded term keeps the bound (one binder
consumed). -/
theorem bvarsBelow_inst {a : Term} {n : Nat} (ha : Term.bvarsBelow n a) :
    ∀ (e : Term) (k : Nat), Term.bvarsBelow (n + k + 1) e →
      Term.bvarsBelow (n + k) (Term.inst e a k)
  | .bvar i, k, he => by
    show Term.bvarsBelow (n + k) (if i < k then .bvar i else if i = k then Term.liftN k a else .bvar (i - 1))
    have hi : i < n + k + 1 := he
    split
    · show i < n + k; omega
    · split
      · exact VExprAux.bvarsBelow_liftN k a n 0 ha
      · show i - 1 < n + k; omega
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .app f b, k, he => ⟨bvarsBelow_inst ha f k he.1, bvarsBelow_inst ha b k he.2⟩
  | .lam A b, k, he => by
    refine ⟨bvarsBelow_inst ha A k he.1, ?_⟩
    have := bvarsBelow_inst ha b (k + 1) (by
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 from by omega]; exact he.2)
    rwa [show n + (k + 1) = n + k + 1 from by omega] at this
  | .pi A B, k, he => by
    refine ⟨bvarsBelow_inst ha A k he.1, ?_⟩
    have := bvarsBelow_inst ha B (k + 1) (by
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 from by omega]; exact he.2)
    rwa [show n + (k + 1) = n + k + 1 from by omega] at this
  | .eqE b c, k, he =>
    ⟨bvarsBelow_inst ha b k he.1, bvarsBelow_inst ha c k he.2⟩
  | .fst e, k, he => bvarsBelow_inst ha e k he
  | .snd e, k, he => bvarsBelow_inst ha e k he
  | .prf, _, _ => trivial

/-- The uniform projection of a bounded variable is bounded. -/
theorem projAV_bvar_below {i j k : Nat} (h : j < k) :
    Term.bvarsBelow k (projAV i (.bvar j)).erase :=
  projAV_below (i := i) (e := .bvar j) (k := k) h

/-- Substituting the payload's projections consumes the `i` virtual
field binders. -/
theorem substProj_below {K : Nat} (hK : 0 < K) :
    ∀ (i : Nat) (e : AnnotTerm), Term.bvarsBelow (K + i) e.erase →
      Term.bvarsBelow K (substProj i e).erase
  | 0, _, h => h
  | i + 1, e, h => by
    show Term.bvarsBelow K (substProj i (e.inst (projAV i (.bvar i)))).erase
    refine substProj_below hK i _ ?_
    rw [AnnotTerm.erase_inst]
    have := bvarsBelow_inst (n := K + i) (projAV_bvar_below (i := i) (j := i) (k := K + i) (by omega))
      e.erase 0 (by rw [Nat.add_zero]; exact h)
    rwa [Nat.add_zero] at this

/-! ## The inductive-hypothesis arguments -/

theorem domsBelow_mono : ∀ {ds : List (Nat × Nat × AnnotTerm)} {k k' : Nat}, k ≤ k' →
    DomsBelow k ds → DomsBelow k' ds
  | [], _, _, _, _ => trivial
  | _ :: ds, k, k', hk, h => ⟨Term.bvarsBelow.mono hk h.1, domsBelow_mono (ds := ds) (by omega) h.2⟩


/-- `substProj` under `m` binders consumes the `i` virtual field
binders. -/
theorem substProjAt_below {K : Nat} (hK : 0 < K) :
    ∀ (m i : Nat) (e : AnnotTerm), Term.bvarsBelow (K + i + m) e.erase →
      Term.bvarsBelow (K + m) (substProjAt m i e).erase
  | _, 0, _, h => by simpa [substProjAt] using h
  | m, i + 1, e, h => by
    show Term.bvarsBelow (K + m) (substProjAt m i (e.inst (projAV i (.bvar i)) m)).erase
    refine substProjAt_below hK m i _ ?_
    rw [AnnotTerm.erase_inst]
    exact bvarsBelow_inst (n := K + i) (projAV_bvar_below (i := i) (j := i) (k := K + i) (by omega))
      e.erase m (by rw [show K + i + m + 1 = K + (i + 1) + m from by omega]; exact h)

theorem ihTeleAt_length (nIdx n D i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    (ihTeleAt nIdx n D i tl).length = tl.length := by simp [ihTeleAt]

/-- A recursive field's telescope at the payload frame is closed below
the `(p⃗, M, m⃗)` block over the field variables. -/
theorem ihTeleAt_below {nP nIdx n D i : Nat} {tl : List (Nat × Nat × AnnotTerm)}
    (hT : DomsBelow (nP + i) tl) :
    DomsBelow (nP + D + nIdx + n + 2) (ihTeleAt nIdx n D i tl) := by
  refine domsBelow_of_getD fun k hk => ?_
  rw [ihTeleAt_length] at hk
  have hget : (ihTeleAt nIdx n D i tl).getD k default
      = ((tl.getD k default).1, (tl.getD k default).2.1,
          substProjAt k i ((tl.getD k default).2.2.liftN (D + nIdx + n + 2) (i + k))) := by
    unfold ihTeleAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  rw [hget]
  refine substProjAt_below (by omega) k i _ ?_
  rw [AnnotTerm.erase_liftN]
  have := VExprAux.bvarsBelow_liftN (D + nIdx + n + 2) _ (nP + i + k) (i + k) (hT.getD_below k hk)
  rwa [show nP + i + k + (D + nIdx + n + 2) = nP + D + nIdx + n + 2 + i + k from by omega] at this

/-- An inductive-hypothesis argument at the payload frame `K + D + 1`
mentions the unfolded function (`K = k + 1 + nP + 1 + n + nIdx`, the
K-frame's depth over the function's), the block's variables, the
field's telescope and index expressions and the payload's projection
applied to the telescope's variables. -/
theorem ihArgAV_below {ℓ k nP n nIdx D i : Nat} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hT : DomsBelow (nP + i) tl)
    (hE : ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length) E.erase) :
    Term.bvarsBelow (k + 1 + nP + 1 + n + nIdx + D + 1) (ihArgAV ℓ nP n nIdx D i tl Eis).erase := by
  unfold ihArgAV
  refine mkLamsC_below (domsBelow_mono (by omega) (ihTeleAt_below hT)) ?_
  rw [ihTeleAt_length, AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN
    (show D + 1 + nIdx + n + 1 + nP + tl.length < k + 1 + nP + 1 + n + nIdx + D + 1 + tl.length by omega) ?_
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_range] at hl
      show D + 1 + nIdx + tl.length + (nP + 1 + n) - 1 - l < _
      omega
    · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp ha
      refine Term.bvarsBelow.mono
        (show nP + D + nIdx + n + 2 + tl.length ≤ k + 1 + nP + 1 + n + nIdx + D + 1 + tl.length by omega) ?_
      refine substProjAt_below (by omega) tl.length i _ ?_
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (D + nIdx + n + 2) E.erase (nP + i + tl.length) (i + tl.length)
        (hE E hE')
      rwa [show nP + i + tl.length + (D + nIdx + n + 2) = nP + D + nIdx + n + 2 + i + tl.length from
        by omega] at this
  · rw [List.mem_singleton] at ha
    subst ha
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (projAV_bvar_below (by omega)) ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hl
    show tl.length - 1 - l < _
    omega

/-- The inductive-hypothesis arguments of every constructor at every
payload frame. -/
theorem ihArgsI_below {ℓ k nP n nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {ar : Nat → Nat}
    (hT : ∀ j i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase)
    (D j : Nat) :
    ∀ a ∈ ihArgsI ℓ nP n nIdx rss tlss Eiss ar D j,
      Term.bvarsBelow (k + 1 + nP + 1 + n + nIdx + D + 1) a.erase := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  exact ihArgAV_below (hT j i) (hE j i)

/-! ## The case split with inductive hypotheses -/

theorem caseBaseAVI_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K)
    {Fss : List (List AnnotTerm)} {ar : Nat → Nat} {ihArgs : Nat → Nat → List AnnotTerm} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (hih : ∀ a ∈ ihArgs D j, Term.bvarsBelow (K + D + 1) a.erase) :
    Term.bvarsBelow (K + D) (caseBaseAVI ℓ w Fss ar ihArgs n nIdx D j).erase := by
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    have hFj : FieldsBelow K (Fss.getD j []) := by
      rw [List.getD_eq_getElem?_getD]
      cases hjF : Fss[j]? with
      | none => trivial
      | some Fs' => exact h Fs' (List.mem_of_getElem? hjF)
    exact VExprAux.bvarsBelow_liftN D _ K 0 (towerBodyAV_below hFj)
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (show D + 1 + nIdx + n - 1 - j < K + D + 1 by omega) ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_below (show (0 : Nat) < K + D + 1 by omega)
    · exact hih a ha

theorem caseRecAVI_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K) {Fss : List (List AnnotTerm)}
    {ar : Nat → Nat} {ihArgs : Nat → Nat → List AnnotTerm}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (hih : ∀ D j, ∀ a ∈ ihArgs D j, Term.bvarsBelow (K + D + 1) a.erase) :
    ∀ (r : Nat) {D j : Nat} {kx : AnnotTerm},
      Term.bvarsBelow (K + D) kx.erase →
      Term.bvarsBelow (K + D) (caseRecAVI ℓ w Fss ar ihArgs n nIdx r D j kx).erase
  | 0, _, _, _, _ => ⟨trivial, trivial⟩
  | r + 1, D, j, _, hk => by
    refine natRecAV_below (caseMotiveAV_below hK h) (caseBaseAVI_below hK h (hih D j)) ?_ hk
    refine ⟨trivial, caseMotiveBodyAV_below hK h, ?_⟩
    have := caseRecAVI_below (ℓ := ℓ) (w := w) hK (ar := ar) (ihArgs := ihArgs) h hih r
      (D := D + 2) (j := j + 1) (kx := .bvar 1) (show (1 : Nat) < K + (D + 2) by omega)
    rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this

/-! ## The squash regime's body (task #202 A2) -/

/-- A field chain bounded at a depth is bounded at any deeper one. -/
theorem fieldsBelow_mono : ∀ {Fs : List AnnotTerm} {k k' : Nat}, k ≤ k' →
    FieldsBelow k Fs → FieldsBelow k' Fs
  | [], _, _, _, _ => trivial
  | _ :: Fs, k, k', hk, h => ⟨Term.bvarsBelow.mono hk h.1, fieldsBelow_mono (Fs := Fs) (by omega) h.2⟩

/-- A moved index expression: `ihIdxAtM` lifts by `nF - i + l` and
then by `o`. -/
theorem ihIdxAtM_below {nF o i l m K : Nat} {E : AnnotTerm} (hE : Term.bvarsBelow K E.erase) :
    Term.bvarsBelow (K + (nF - i + l) + o) (ihIdxAtM nF o i l m E).erase := by
  unfold ihIdxAtM
  rw [AnnotTerm.erase_liftN, AnnotTerm.erase_liftN]
  exact VExprAux.bvarsBelow_liftN o _ _ _ (VExprAux.bvarsBelow_liftN (nF - i + l) _ _ _ hE)

/-- A telescope moved to the ih frame is bounded there. -/
theorem ihTeleAtGo_below {nF o i l K : Nat} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow (K + k) tl →
      DomsBelow (K + (nF - i + l) + o + k) (ihTeleAtGo nF o i l k tl)
  | [], _, _ => trivial
  | d :: tl, k, h => by
    refine ⟨?_, ?_⟩
    · have := ihIdxAtM_below (nF := nF) (o := o) (i := i) (l := l) (m := k) h.1
      rwa [show K + k + (nF - i + l) + o = K + (nF - i + l) + o + k from by omega] at this
    · have := ihTeleAtGo_below (nF := nF) (o := o) (i := i) (l := l) (K := K) (tl := tl) (k := k + 1)
        (by rw [show K + (k + 1) = K + k + 1 from by omega]; exact h.2)
      rwa [show K + (nF - i + l) + o + (k + 1) = K + (nF - i + l) + o + k + 1 from by omega] at this

/-- The recursor's `(p⃗, M, m⃗)` variables under `m` binders below the
fields are bounded at any depth past the block. -/
theorem prefixVarsAV_below {nP n nF m K : Nat} (hK : nP + nF + n + m < K) :
    ∀ a ∈ prefixVarsAV nP n nF m, Term.bvarsBelow K a.erase := by
  intro a ha
  unfold prefixVarsAV at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_range] at hq
      show nP + nF + n + 1 + m - 1 - q < K
      omega
    · rw [List.mem_singleton] at ha
      subst ha
      show nF + n + m < K
      omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hq
    show nF + n - 1 - q + m < K
    omega

/-- **The ih application under a field's telescope is bounded** at a
depth past the block and the extras: the function is bounded under the
telescope, the telescope and the index expressions are scoped at the
field's frame. -/
theorem ihAppAVb_below {b nP n nF e i K : Nat} {Rm : Nat → AnnotTerm}
    (hR : ∀ m, Term.bvarsBelow (K + m) (Rm m).erase) (hK : nP + nF + n + e + 1 ≤ K)
    {tl : List (Nat × Nat × AnnotTerm)} (hT : DomsBelow (nP + i) tl)
    {Eis : List AnnotTerm} (hE : ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length) E.erase)
    (hi : i < nF) :
    Term.bvarsBelow K (ihAppAVb b Rm nP n nF e i tl Eis).erase := by
  unfold ihAppAVb
  refine mkLamsC_below ?_ ?_
  · have := ihTeleAtGo_below (K := nP + i) (nF := nF) (o := n + 1 + e) (i := i) (l := 0) (k := 0)
      (tl := tl) (by rw [Nat.add_zero]; exact hT)
    exact domsBelow_mono (by omega) this
  · rw [ihTeleAtR_length, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (hR tl.length) ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact prefixVarsAV_below (by omega) a ha
      · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp ha
        refine Term.bvarsBelow.mono
          (show nP + i + tl.length + (nF - i + 0) + (n + 1 + e) ≤ K + tl.length by omega) ?_
        exact ihIdxAtM_below (hE E hE')
    · rw [List.mem_singleton] at ha
      subst ha
      rw [AnnotTerm.erase_mkAppN]
      refine VExprAux.bvarsBelow_mkAppN (show nF - 1 - i + tl.length < K + tl.length by omega) ?_
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_range] at hq
      show tl.length - 1 - q < K + tl.length
      omega

theorem fieldTeleAt_length (o : Nat) (Fs : List AnnotTerm) : (fieldTeleAt o Fs).length = Fs.length := by
  simp [fieldTeleAt, liftFields_length]

/-- Fields bounded at their frame give binder data bounded there. -/
theorem domsBelow_of_fieldsBelow {K : Nat} :
    ∀ {Fs : List AnnotTerm}, FieldsBelow K Fs → DomsBelow K (Fs.map fun F => (0, 0, F))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, domsBelow_of_fieldsBelow h.2⟩

/-- **The squash regime's body is bounded one below the K-frame**
`K = k + 1 + nP + 1 + n + nIdx`: the constructor's field telescope
(scoped at the parameters) lifted under the major, the indices, the
minors and the motive; the minor at the fields and the ih
applications; the sources among the index variables. -/
theorem sqFixBodyAV_below {ℓ k nP n nIdx : Nat} {Fs Es : List AnnotTerm} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    (hFs : FieldsBelow nP Fs)
    (hT : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hE : ∀ i, ∀ E ∈ Eis.getD i [], Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase) :
    Term.bvarsBelow (k + 1 + nP + 1 + n + nIdx + 1)
      (sqFixBodyAV ℓ nP n nIdx Fs Es rs tls Eis).erase := by
  unfold sqFixBodyAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · refine mkLamsC_below ?_ ?_
    · unfold fieldTeleAt
      exact domsBelow_of_fieldsBelow (fieldsBelow_mono
        (show nP + (nIdx + n + 2) ≤ k + 1 + nP + 1 + n + nIdx + 1 by omega)
        (FieldsBelow_liftFields (n := nIdx + n + 2) (Nat.zero_le _) hFs))
    · rw [fieldTeleAt_length, AnnotTerm.erase_mkAppN]
      refine VExprAux.bvarsBelow_mkAppN
        (show Fs.length + 1 + nIdx + n - 1 < k + 1 + nP + 1 + n + nIdx + 1 + Fs.length by omega) ?_
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_range] at hq
        show Fs.length - 1 - q < k + 1 + nP + 1 + n + nIdx + 1 + Fs.length
        omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hik, -⟩ := mem_recIdx.mp hi
        refine ihAppAVb_below (K := k + 1 + nP + 1 + n + nIdx + 1 + Fs.length) ?_ (by omega)
          (hT i) (hE i) hik
        intro m
        show m + Fs.length + 1 + nIdx + n + 1 + nP < k + 1 + nP + 1 + n + nIdx + 1 + Fs.length + m
        omega
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨s', -, rfl⟩ := List.mem_map.mp ha
    cases s' with
    | none => trivial
    | some l =>
      show 1 + nIdx - 1 - l < k + 1 + nP + 1 + n + nIdx + 1
      omega

/-- The recursor body is bounded one below the K-frame
`K = k + 1 + nP + 1 + n + nIdx`. -/
theorem fixRecBodyAVI_below {ℓ w k nP nIdx : Nat} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hIds : Ids.length = nIdx)
    (h : ∀ Fs' ∈ rChains (nIdx + Fss.length + 1) nIdx Fss Ess,
      FieldsBelow (k + 1 + nP + 1 + Fss.length + nIdx) Fs')
    (hFs : ∀ Fs ∈ Fss, FieldsBelow nP Fs)
    (hT : ∀ j i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase) :
    Term.bvarsBelow (k + 1 + nP + 1 + Fss.length + nIdx + 1)
      (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss).erase := by
  by_cases hw : w = 0
  · subst hw
    by_cases hℓ : ℓ = 0
    · rw [fixRecBodyAVI_zero hℓ]
      trivial
    · rw [fixRecBodyAVI_sq hℓ, hIds]
      refine sqFixBodyAV_below ?_ (hT 0) (hE 0)
      cases hF0 : Fss[0]? with
      | none => rw [List.getD_eq_getElem?_getD, hF0]; trivial
      | some Fs => rw [List.getD_eq_getElem?_getD, hF0]; exact hFs Fs (List.mem_of_getElem? hF0)
  · rw [fixRecBodyAVI_pos hw, hIds]
    refine ⟨?_, show (0 : Nat) < k + 1 + nP + 1 + Fss.length + nIdx + 1 by omega⟩
    have := caseRecAVI_below (ℓ := ℓ) (w := w) (K := k + 1 + nP + 1 + Fss.length + nIdx)
      (ar := fun j => (Fss.getD j []).length)
      (ihArgs := ihArgsI ℓ nP Fss.length nIdx rss tlss Eiss (fun j => (Fss.getD j []).length))
      (show nIdx + Fss.length < k + 1 + nP + 1 + Fss.length + nIdx by omega) h
      (fun D j => ihArgsI_below (k := k) (rss := rss) (ar := fun j => (Fss.getD j []).length) hT hE D j)
      Fss.length (D := 1) (j := 0)
      (kx := .fst (.bvar 0)) (show (0 : Nat) < k + 1 + nP + 1 + Fss.length + nIdx + 1 by omega)
    exact this

/-! ## The leaf -/

/-- A Π-tower over bounded binder data with a bounded conclusion is
bounded. -/
theorem mkPisAV_below_of {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow k ds →
      Term.bvarsBelow (k + ds.length) C.erase → Term.bvarsBelow k (mkPisAV ds C).erase
  | [], _, _, hC => hC
  | d :: ds, k, hd, hC => by
    refine ⟨hd.1, mkPisAV_below_of hd.2 ?_⟩
    rwa [show k + 1 + ds.length = k + (d :: ds).length from by simp; omega]


/-- **The recursor leaf is closed**: its binder data are closed, its
conclusion mentions the motive, the indices and the major, its body is
the case split one below the K-frame. -/
theorem nativeRecAVI_below {ℓ w nP s : Nat} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {rds : List (Nat × Nat × AnnotTerm)} (k : Nat)
    (hd : DomsBelow 0 rds) (hlen : rds.length = nP + 1 + Fss.length + Ids.length + 1)
    (_hIds : Ids.length = Ids.length)
    (hFss : ∀ Fs' ∈ rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess,
      FieldsBelow (nP + 1 + Fss.length + Ids.length) Fs')
    (hFs : ∀ Fs ∈ Fss, FieldsBelow nP Fs)
    (hT : ∀ j i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase) :
    Term.bvarsBelow k (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).erase := by
  have hconc : ∀ m, Term.bvarsBelow (m + rds.length) (recConcAV Fss.length Ids.length).erase := by
    intro m
    have hlt : Ids.length + Fss.length < m + rds.length - 1 := by rw [hlen]; omega
    have := motAppAV_below (D' := 1) (K := m + rds.length - 1) hlt
    rw [show m + rds.length - 1 + 1 = m + rds.length from by rw [hlen]; omega] at this
    exact ⟨this, show (0 : Nat) < m + rds.length by rw [hlen]; omega⟩
  have hTy : ∀ m, Term.bvarsBelow m (recTyAV Fss.length Ids.length rds).erase := fun m =>
    mkPisAV_below_of (domsBelow_mono (Nat.zero_le m) hd) (hconc m)
  have hstep : ∀ m, Term.bvarsBelow m (fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).erase := by
    intro m
    refine ⟨hTy m, ?_⟩
    refine mkLamsC_below (domsBelow_mono (Nat.zero_le (m + 1)) hd) ?_
    have := fixRecBodyAVI_below (ℓ := ℓ) (w := w) (k := m) (nP := nP) (nIdx := Ids.length)
      (Fss := Fss) (Ess := Ess) (Ids := Ids) (rss := rss) (tlss := tlss) (Eiss := Eiss) rfl
      (fun Fs' hFs' => fieldsBelow_mono (by omega) (hFss Fs' hFs')) hFs hT hE
    rwa [show m + 1 + nP + 1 + Fss.length + Ids.length + 1 = m + 1 + rds.length from by
      rw [hlen]; omega] at this
  have hsig : Term.bvarsBelow k (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).erase := by
    refine ⟨⟨trivial, hTy k⟩, hTy k, ?_⟩
    refine ⟨⟨?_, show (0 : Nat) < k + 1 by omega⟩, show (0 : Nat) < k + 1 by omega⟩
    rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN 1 _ k 0 (hstep k)
  show Term.bvarsBelow k (AnnotTerm.erase (.fst (.app (.app (.const .choice [s]) _) .prf)))
  exact ⟨⟨trivial, hsig⟩, trivial⟩

end ConLeche.Semantics
