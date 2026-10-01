module

public import ConLeche.Semantics.Inductives.DeclNative
import ConLeche.Semantics.Inductives.DeclStructEta

@[expose] public section

/-!
# The direct sum declaration keeps the η-families closed (task #175
sum-types, indexed)

Every store the direct sum install performs is a fresh cons
(`checkConstantVal`'s duplicate guard for the former and the recursor;
the constructors are checked at the former's environment and consed
in order under the distinct-names guard), and the one former it
stores carries the sum's capability record (`sumCaps`, whose
`eta` is `false` — a sum is never structure-like), so
`EtaFamiliesClosed.cons_nonind` applies at every step.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape fueledOps checkSumInd checkSumCtors
   consSumCtors sumRules nativeCaps EtaFamiliesClosed
  EtaFamiliesClosedExcept)

/-- The constructors' conses keep the OTHER families closed (task
#210 Part A: the block's own family may claim η before its constructor
is stored). -/
theorem consSumCtors_etaClosedExcept {nP : Nat} {T : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EtaFamiliesClosedExcept env T →
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (ctorsA.map (·.1.name)).Nodup →
      EtaFamiliesClosedExcept (consSumCtors nP ctorsA env) T
  | [], _, hE, _, _ => hE
  | c :: cs, env, hE, hfresh, hnd => by
    simp only [consSumCtors]
    have hE' : EtaFamiliesClosedExcept ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩ T :=
      hE.cons (hfresh c List.mem_cons_self) (fun _ _ heq => nomatch heq)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine consSumCtors_etaClosedExcept hE' ?_ hnd.2
    intro c' hc'
    rw [ConLeche.Env.find?_cons]
    split
    · next heq =>
      exfalso
      apply hnd.1
      rw [List.mem_map]
      exact ⟨c', hc', heq.symm⟩
    · exact hfresh c' (List.mem_cons_of_mem _ hc')

/-- A name none of the consed constructors carries looks up below the
conses. -/
theorem consSumCtors_find?_of_not_mem {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      n ∉ ctorsA.map (·.1.name) → (consSumCtors nP ctorsA env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, hn => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [consSumCtors_find?_of_not_mem hn.2, ConLeche.Env.find?_cons, if_neg (fun h => hn.1 h.symm)]

/-- The projection table stage of the fixpoint route keeps the
η-families closed (task #210 Part A): the table's cons at a
structure-like block, nothing otherwise. -/
theorem checkNativeTable_etaClosed {p : ConLeche.NativeParts}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {env env₂ : Env}
    (h : ConLeche.checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss env = .ok env₂)
    (hE : EtaFamiliesClosed env) : EtaFamiliesClosed env₂ := by
  unfold ConLeche.checkNativeTable at h
  split at h
  · split at h
    · exact checkStructProjTable_etaClosed h hE
    · obtain rfl := Except.ok.inj h; exact hE
  · obtain rfl := Except.ok.inj h; exact hE

/-- **The direct recursive arm keeps the η-families closed** (task
#188; task #210 Part A: at a structure-like block the former claims η,
which its constructor's cons completes — the other families stay
closed across the former's cons, `EtaFamiliesClosedExcept`, and the
block's own family is closed once its constructor is stored). -/
theorem declNativeRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p₀ : ConLeche.NativeParts} (hE : EtaFamiliesClosed env)
    (h : DeclNativeRun μ F env p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, rfl,
    hCtors, -, hcaps, -, -, -, -, -, hRec, hTbl⟩ := h
  obtain ⟨cvT, s, hTn, -, hcvT, rfl, rfl, -⟩ := ConLeche.checkSumInd_shape hInd
  obtain ⟨hfT, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
    ConLeche.checkConstantVal_inv hcvT
  -- the completed record, as one name; the record the former carries
  -- is the classified one (task #268)
  try dsimp only at hCtors hRec hTbl hcaps
  rw [← hcaps] at hCtors hRec hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [ConLeche.NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [ConLeche.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hRec hTbl hpT hpC
  have hn : cvTa.name = p.cvT.name := by rw [hTeq, hpT]; exact hTn
  replace hnd : (p.ctors.map (·.1.name)).Nodup := by rw [hpC]; exact hnd
  have hfreshT : env.find? cvTa.name = none := by rw [hn, hpT, ← hTn]; exact hfT
  -- the former's cons: the other families stay closed
  have hE₁ : EtaFamiliesClosedExcept
      ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩
      p.cvT.name :=
    (hE.except p.cvT.name).cons hfreshT (fun cv caps heq _ => Or.inr (by
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
      exact hn))
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv hCtors
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hrun
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hCeq]
  have hfreshC : ∀ c ∈ ctorsA,
      (⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩ : Env).find?
        c.1.name = none := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hrun
    obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hn' : c.1.name = (p.ctors[j]).1.name := by rw [hCeq]
    rw [hn']; exact hfC
  have hE₂ : EtaFamiliesClosedExcept
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩)
      p.cvT.name :=
    consSumCtors_etaClosedExcept hE₁ hfreshC (by rw [hnames]; exact hnd)
  -- the block's own family: its constructor is stored by the conses
  have hTnot : p.cvT.name ∉ ctorsA.map (·.1.name) := by
    intro hmem
    obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hmem
    have := hfreshC c hc
    rw [hcn, ← hn] at this
    exact nomatch this.symm.trans (ConLeche.Env.find?_cons_self
      (ConstantInfo.indInfo cvTa (nativeCaps p)) env)
  have hE₂' : EtaFamiliesClosed
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩) := by
    refine hE₂.closed ?_
    intro cvT' caps hf he _
    rw [consSumCtors_find?_of_not_mem hTnot, ← hn] at hf
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj
      ((ConLeche.Env.find?_cons_self
        (ConstantInfo.indInfo cvTa (nativeCaps p)) env).symm.trans hf))
    -- η is claimed only at one constructor
    simp only [ConLeche.nativeCaps, ConLeche.nativeCapsAt] at he ⊢
    revert he hlen hnames hall
    cases hcs : p.ctors with
    | nil => intro _ _ _ he; exact nomatch he
    | cons c cs =>
      cases cs with
      | cons _ _ => intro _ _ _ he; exact nomatch he
      | nil =>
        intro hlen hall hnames _
        match ctorsA, hlen, hnames, hall with
        | [cA], _, hnames, hall =>
          have hn' : cA.1.name = c.1.name := by simpa using hnames
          obtain ⟨-, _, -, hrun⟩ := hall 0 c cA rfl rfl
          simp only [consSumCtors]
          refine ⟨cA.1, ?_⟩
          show Env.find? ⟨.ctorInfo cA.1 p.nP cA.2 :: _⟩ c.1.name
            = some (.ctorInfo cA.1 p.nP c.2)
          have hnF : cA.2 = c.2 := (hall 0 c cA rfl rfl).1
          rw [← hn', ← hnF]
          exact ConLeche.Env.find?_cons_self _ _
  -- the recursor's cons and the table
  obtain ⟨hnR, -, -, -, -⟩ := ConLeche.checkNativeRec_facts hRec
  obtain ⟨cvRi, -, -, -, hcvR, -⟩ := ConLeche.checkNativeRec_shape hRec
  obtain ⟨hfR, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hcvR
  refine checkNativeTable_etaClosed hTbl ?_
  refine EtaFamiliesClosed.cons_nonind hE₂' ?_ (fun _ _ heq => nomatch heq)
  show (consSumCtors p.nP ctorsA
    ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩).find?
      cvRa.name = none
  rw [hnR]; exact hfR

/-! ## The dispatch -/

/-- The `.indDecl` run dispatch keeps the η-families closed, by the
kernel's own case split. -/
theorem declIndRunDispatchEtaClosed {μ : CheckMode} {F : Nat}
    {env envI : Env} {block : List ConstantInfo} {nP : Nat}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndRunDispatch μ F env block nP envI) : EtaFamiliesClosed envI := by
  unfold DeclIndRunDispatch at h
  split at h
  · exact declNativeRun_etaClosed hE h
  · exact declIndEtaClosedRun hE h

end ConLeche.Semantics
