module

public import IxC.Kernel.Semantics.Inductives.DeclNativeJ
public import IxC.Kernel.Semantics.Inductives.DeclSumEta
public import IxC.Kernel.Semantics.DeclExt
import IxC.Kernel.Semantics.IndBlockRun
import IxC.Kernel.Verify.Inductives.StructWF

@[expose] public section

/-!
# The native route over a package: the η-families and the extension

Two facts about a native step that read only the record's freshness guards and
cons shapes, so they hold at every package:

* the step keeps the η-families closed (`declNativeRunJ_etaClosed`, the package
  form of `declNativeRun_etaClosed`): every cons is fresh, and the block's own
  family, which may claim η, is closed once its constructor is stored;
* the step extends the environment (`declNativeRunJ_envExt`): every constant it
  adds is fresh before the block, and the one table it may add is its own new
  structure's, so no structure stored before the step gains a table. This is the
  native route's half of `declRunJ_envExt`'s inductive premise.

The route without a recursor record has both facts by the same proofs, with the
table over the constructors (`declNativeNoRecRunJ_etaClosed`,
`declNativeNoRecRunJ_envExt`), and every route of `IndRoutesJ` has them
(`indRoutesJ_etaClosed`, `indRoutesJ_envExt`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr Key Level ConstantVal ConstantInfo IndCaps NativeParts EnvExt
  consSumCtors nativeCaps EtaFamiliesClosed EtaFamiliesClosedExcept projTableName)

/-! ## The η-families -/

/-- **The native route keeps the η-families closed**, over a package. -/
theorem declNativeRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {p₀ : NativeParts md} (hE : EtaFamiliesClosed env)
    (h : DeclNativeRunJ J env p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, rfl,
    hCtors, -, hcaps, -, -, -, -, -, hRec, hTbl, -⟩ := h
  obtain ⟨hTn, -, hfT, -⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, -, -, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hRec hTbl hcaps
  rw [← hcaps] at hCtors hRec hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hRec hTbl hpT hpC
  have hn : cvTa.name = p.cvT.name := by rw [hpT]; exact hTn
  replace hnd : (p.ctors.map (·.1.name)).Nodup := by rw [hpC]; exact hnd
  have hfreshT : env.find? cvTa.name = none := by rw [hTn]; exact hfT
  have hE₁ : EtaFamiliesClosedExcept
      ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩
      p.cvT.name :=
    (hE.except p.cvT.name).cons hfreshT (fun cv caps heq _ => Or.inr (by
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
      exact hn))
  obtain ⟨hlen, -, hall⟩ := hCtors
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hfreshC : ∀ c ∈ ctorsA,
      (⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩ : Env md).find?
        c.1.name = none := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, -, hfC, -⟩ := hrun.names
    rw [hCn]; exact hfC
  have hE₂ : EtaFamiliesClosedExcept
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩)
      p.cvT.name :=
    consSumCtors_etaClosedExcept hE₁ hfreshC (by rw [hnames]; exact hnd)
  have hTnot : p.cvT.name ∉ ctorsA.map (·.1.name) := by
    intro hmem
    obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hmem
    have := hfreshC c hc
    rw [hcn, ← hn] at this
    exact nomatch this.symm.trans (Ix.Kernel.Env.find?_cons_self
      (ConstantInfo.indInfo cvTa (nativeCaps p)) env)
  have hE₂' : EtaFamiliesClosed
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩) := by
    refine hE₂.closed ?_
    intro cvT' caps hf he _
    rw [consSumCtors_find?_of_not_mem hTnot, ← hn] at hf
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj
      ((Ix.Kernel.Env.find?_cons_self
        (ConstantInfo.indInfo cvTa (nativeCaps p)) env).symm.trans hf))
    simp only [Ix.Kernel.nativeCaps, Ix.Kernel.nativeCapsAt] at he ⊢
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
          simp only [consSumCtors]
          refine ⟨c.1.name, cA.1, rfl, ?_⟩
          show Env.find? ⟨.ctorInfo cA.1 p.nP cA.2 :: _⟩ c.1.name
            = some (.ctorInfo cA.1 p.nP c.2)
          have hnF : cA.2 = c.2 := (hall 0 c cA rfl rfl).1
          rw [← hn', ← hnF]
          exact Ix.Kernel.Env.find?_cons_self _ _
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  refine checkNativeTable_etaClosed hTbl ?_
  refine EtaFamiliesClosed.cons_nonind hE₂' ?_ (fun _ _ heq => nomatch heq)
  show (consSumCtors p.nP ctorsA
    ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩).find?
      cvRa.name = none
  rw [hnR]; exact hfR

/-- **The native route without a recursor record keeps the η-families closed**, over
a package: as `declNativeRunJ_etaClosed`, with the table over the constructors. -/
theorem declNativeNoRecRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {p₀ : NativeParts md} (hE : EtaFamiliesClosed env)
    (h : DeclNativeNoRecRunJ J env p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, rfl,
    hCtors, -, hcaps, -, -, -, hTbl, -⟩ := h
  obtain ⟨hTn, -, hfT, -⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, -, -, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hTbl hcaps
  rw [← hcaps] at hCtors hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hTbl hpT hpC
  have hn : cvTa.name = p.cvT.name := by rw [hpT]; exact hTn
  replace hnd : (p.ctors.map (·.1.name)).Nodup := by rw [hpC]; exact hnd
  have hfreshT : env.find? cvTa.name = none := by rw [hTn]; exact hfT
  have hE₁ : EtaFamiliesClosedExcept
      ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩
      p.cvT.name :=
    (hE.except p.cvT.name).cons hfreshT (fun cv caps heq _ => Or.inr (by
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
      exact hn))
  obtain ⟨hlen, -, hall⟩ := hCtors
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hfreshC : ∀ c ∈ ctorsA,
      (⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩ : Env md).find?
        c.1.name = none := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, -, hfC, -⟩ := hrun.names
    rw [hCn]; exact hfC
  have hE₂ : EtaFamiliesClosedExcept
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩)
      p.cvT.name :=
    consSumCtors_etaClosedExcept hE₁ hfreshC (by rw [hnames]; exact hnd)
  have hTnot : p.cvT.name ∉ ctorsA.map (·.1.name) := by
    intro hmem
    obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hmem
    have := hfreshC c hc
    rw [hcn, ← hn] at this
    exact nomatch this.symm.trans (Ix.Kernel.Env.find?_cons_self
      (ConstantInfo.indInfo cvTa (nativeCaps p)) env)
  have hE₂' : EtaFamiliesClosed
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (nativeCaps p) :: env.consts⟩) := by
    refine hE₂.closed ?_
    intro cvT' caps hf he _
    rw [consSumCtors_find?_of_not_mem hTnot, ← hn] at hf
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj
      ((Ix.Kernel.Env.find?_cons_self
        (ConstantInfo.indInfo cvTa (nativeCaps p)) env).symm.trans hf))
    simp only [Ix.Kernel.nativeCaps, Ix.Kernel.nativeCapsAt] at he ⊢
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
          simp only [consSumCtors]
          refine ⟨c.1.name, cA.1, rfl, ?_⟩
          show Env.find? ⟨.ctorInfo cA.1 p.nP cA.2 :: _⟩ c.1.name
            = some (.ctorInfo cA.1 p.nP c.2)
          have hnF : cA.2 = c.2 := (hall 0 c cA rfl rfl).1
          rw [← hn', ← hnF]
          exact Ix.Kernel.Env.find?_cons_self _ _
  exact checkNativeTable_etaClosed hTbl hE₂'

/-! ## The extension -/

/-- A fresh cons over an extension of `env` is an extension of `env` when it is not
the table of a structure stored in `env`. -/
theorem EnvExt.cons_over {env X : Env md} {c : ConstantInfo md} (hX : EnvExt env X)
    (hfresh : X.find? c.name = none)
    (hnt : ∀ {T : Key md} {cv : ConstantVal md} {caps : IndCaps md},
      env.find? T = some (.indInfo cv caps) → c.name ≠ projTableName T) :
    EnvExt env ⟨c :: X.consts⟩ where
  find := fun {k} {c'} h => by
    have h' := hX.find h
    have hne : c.name ≠ k := fun e => by
      rw [e, h'] at hfresh
      exact nomatch hfresh
    rw [EnvExt.find?_cons_ne hne]
    exact h'
  tables := fun hT => by
    rw [EnvExt.find?_cons_ne (hnt hT)]
    exact hX.tables hT

/-- A name that passes the front door's shape test is no projection table. -/
theorem ne_projTableName_of_shape {n : Key md} (h : n.isProjFnShape = false) (T : Key md) :
    n ≠ projTableName T := by
  intro e
  rw [e, projTableName_isProjFnShape] at h
  exact nomatch h

/-- The constructors' conses extend, over an extension, when each is fresh there
and none is a projection table. -/
theorem EnvExt.consSumCtors_over {env : Env md} {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {X : Env md}, EnvExt env X →
      (∀ c ∈ ctorsA, X.find? c.1.name = none) →
      (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, c.1.name.isProjFnShape = false) →
      EnvExt env (consSumCtors nP ctorsA X)
  | [], _, hX, _, _, _ => hX
  | c :: cs, X, hX, hfresh, hnd, hsh => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hX' : EnvExt env ⟨.ctorInfo c.1 nP c.2 :: X.consts⟩ := by
      refine EnvExt.cons_over hX (hfresh c List.mem_cons_self) ?_
      intro T _ _ _
      exact ne_projTableName_of_shape (hsh c List.mem_cons_self) T
    refine EnvExt.consSumCtors_over hX' ?_ hnd.2 (fun c' hc' => hsh c' (List.mem_cons_of_mem _ hc'))
    intro c' hc'
    rw [Ix.Kernel.Env.find?_cons]
    split
    · next heq =>
      exfalso
      apply hnd.1
      rw [List.mem_map]
      exact ⟨c', hc', heq.symm⟩
    · exact hfresh c' (List.mem_cons_of_mem _ hc')

/-- The projection table stage extends, over an extension, when the structure it
tables is not stored in `env`. -/
theorem checkNativeTable_envExt_over {env X X₂ : Env md} {p : NativeParts md}
    {ctorsA : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (hX : EnvExt env X) (hT : env.find? p.cvT.name = none)
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂) :
    EnvExt env X₂ := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      refine EnvExt.cons_over hX hfresh ?_
      intro T cv caps hf e
      have e₁ : projTableName p.cvT.name = projTableName T := e
      have e' : p.cvT.name = T := (Ix.Kernel.Key.aux.inj e₁).1
      rw [e', hf] at hT
      exact nomatch hT
    · obtain rfl := Except.ok.inj h; exact hX
  · obtain rfl := Except.ok.inj h; exact hX

/-- **A native step extends the environment**, over a package: the former, the
constructors and the recursor are fresh and pass the front door's shape test, and
the table, at a structure-like block, is the new structure's own. -/
theorem declNativeRunJ_envExt {J : Judgements md} {env env₂ : Env md} {p₀ : NativeParts md}
    (h : DeclNativeRunJ J env p₀ env₂) : EnvExt env env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, rfl,
    hCtors, -, -, -, -, -, -, -, hRec, hTbl, -⟩ := h
  obtain ⟨hTn, -, hfT, hTsh⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, -, -, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hRec hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hRec hTbl hpT hpC
  -- the former
  have hX₁ : EnvExt env ⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s)
      isRec) :: env.consts⟩ := by
    refine EnvExt.cons ?_ ?_
    · show env.find? cvTa.name = none
      rw [hTn]; exact hfT
    · intro T _ _ _
      show cvTa.name ≠ projTableName T
      rw [hTn]; exact ne_projTableName_of_shape hTsh T
  -- the constructors
  obtain ⟨hlen, -, hall⟩ := hCtors
  have hrunOf : ∀ c ∈ ctorsA,
      (⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
        :: env.consts⟩ : Env md).find? c.1.name = none ∧
      c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, -, hfC, hshC⟩ := hrun.names
    rw [hCn]; exact ⟨hfC, hshC⟩
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hX₂ := EnvExt.consSumCtors_over (nP := p.nP) hX₁ (fun c hc => (hrunOf c hc).1)
    (by rw [hnames, hpC]; exact hnd) (fun c hc => (hrunOf c hc).2)
  -- the recursor, then the table
  obtain ⟨hnR, -, hfR, hshR⟩ := hRec.recursor
  refine checkNativeTable_envExt_over (EnvExt.cons_over hX₂ ?_ ?_) (by rw [hpT]; exact hfT) hTbl
  · show (consSumCtors p.nP ctorsA _).find? cvRa.name = none
    rw [hnR]; exact hfR
  · intro T _ _ _
    show cvRa.name ≠ projTableName T
    rw [hnR]; exact ne_projTableName_of_shape hshR T

/-- **A native step without a recursor record extends the environment**, over a
package: the former and the constructors are fresh and pass the front door's shape
test, and the table, at a structure-like block, is the new structure's own. -/
theorem declNativeNoRecRunJ_envExt {J : Judgements md} {env env₂ : Env md} {p₀ : NativeParts md}
    (h : DeclNativeNoRecRunJ J env p₀ env₂) : EnvExt env env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, rfl,
    hCtors, -, -, -, -, -, hTbl, -⟩ := h
  obtain ⟨hTn, -, hfT, hTsh⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, -, -, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hTbl hpT hpC
  -- the former
  have hX₁ : EnvExt env ⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s)
      isRec) :: env.consts⟩ := by
    refine EnvExt.cons ?_ ?_
    · show env.find? cvTa.name = none
      rw [hTn]; exact hfT
    · intro T _ _ _
      show cvTa.name ≠ projTableName T
      rw [hTn]; exact ne_projTableName_of_shape hTsh T
  -- the constructors
  obtain ⟨hlen, -, hall⟩ := hCtors
  have hrunOf : ∀ c ∈ ctorsA,
      (⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
        :: env.consts⟩ : Env md).find? c.1.name = none ∧
      c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, -, hfC, hshC⟩ := hrun.names
    rw [hCn]; exact ⟨hfC, hshC⟩
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hX₂ := EnvExt.consSumCtors_over (nP := p.nP) hX₁ (fun c hc => (hrunOf c hc).1)
    (by rw [hnames, hpC]; exact hnd) (fun c hc => (hrunOf c hc).2)
  -- the table
  exact checkNativeTable_envExt_over hX₂ (by rw [hpT]; exact hfT) hTbl

/-! ## The twin recursor route -/

theorem find?_append_of_not_mem {env : Env md} {k : Key md} :
    ∀ {cs : List (ConstantInfo md)}, k ∉ cs.map (·.name) →
      (⟨cs ++ env.consts⟩ : Env md).find? k = env.find? k
  | [], _ => rfl
  | c :: cs, hnm => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    show Env.find? ⟨c :: (cs ++ env.consts)⟩ k = env.find? k
    rw [Ix.Kernel.Env.find?_cons, if_neg (Ne.symm hnm.1)]
    exact find?_append_of_not_mem hnm.2

theorem find?_append_none_of_not_mem {env : Env md} {k : Key md} :
    ∀ {cs : List (ConstantInfo md)}, k ∉ cs.map (·.name) → env.find? k = none →
      (⟨cs ++ env.consts⟩ : Env md).find? k = none
  | [], _, hf => hf
  | c :: cs, hnm, hf => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    show (c :: (cs ++ env.consts)).find? (·.name == k) = none
    rw [List.find?_cons_of_neg (by simp [Ne.symm hnm.1])]
    exact find?_append_none_of_not_mem hnm.2 hf

theorem find?_mem_of_nodup {rest : List (ConstantInfo md)} :
    ∀ {cs : List (ConstantInfo md)} {x : ConstantInfo md},
      (cs.map (·.name)).Nodup → x ∈ cs →
      (⟨cs ++ rest⟩ : Env md).find? x.name = some x
  | [], _, _, hx => nomatch hx
  | c :: cs, x, hnd, hx => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with heq | hx
    · subst heq
      exact Ix.Kernel.Env.find?_cons_self x ⟨cs ++ rest⟩
    · have hne : c.name ≠ x.name := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
      show Env.find? ⟨c :: (cs ++ rest)⟩ x.name = some x
      rw [Ix.Kernel.Env.find?_cons, if_neg hne]
      exact find?_mem_of_nodup hnd.2 hx

theorem find?_append_inv {env : Env md} {n : Key md} {x : ConstantInfo md} :
    ∀ {cs : List (ConstantInfo md)},
      (⟨cs ++ env.consts⟩ : Env md).find? n = some x →
      env.find? n = some x ∨ (x ∈ cs ∧ x.name = n)
  | [], hf => Or.inl hf
  | c :: cs, hf => by
    change Env.find? ⟨c :: (cs ++ env.consts)⟩ n = some x at hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · next heq =>
      obtain rfl := Option.some.inj hf
      exact Or.inr ⟨List.mem_cons_self, heq⟩
    · rcases find?_append_inv hf with hold | ⟨hmem, hn⟩
      · exact Or.inl hold
      · exact Or.inr ⟨List.mem_cons_of_mem c hmem, hn⟩

/-- **Unpacking a new recursor stored by the twin recursor route.** -/
theorem declRecTwinRunJ_newRec {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclRecTwinRunJ J env block env₂)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env₂.find? n = some (.recInfo cv mI rP rules)) (hn : env.find? n = none) :
    ∃ (ws : List (TwinRecPart md)) (f : Key md → Key md) (w : TwinRecPart md),
      w ∈ ws ∧ n = w.cvW.name ∧ cv = w.cvW' ∧ mI = w.mI ∧ rP = w.rP ∧ rules = w.rulesW' ∧
      ConstantValCheckJ J env w.cvW w.cvW' ∧
      env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) ∧
      w.cvW.levelParams = w.cvC.levelParams ∧
      (∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
        env₂.find? (Ix.Kernel.auxKey n .model) = some
          (.defnInfo ⟨Ix.Kernel.auxKey n .model, cvm.levelParams, cvm.type⟩ mval hint)) ∧
      (w.model? = none →
        (∀ cvm mval hint,
          env.find? (Ix.Kernel.auxKey w.kC .model) ≠ some (.defnInfo cvm mval hint)) ∧
        (∀ bsW domW bodyW bmW,
          w.cvW'.type.stripPis w.mI = some (bsW, .forallE domW bodyW bmW) →
          ∃ bsC domC bodyC bmC,
            w.cvC.type.stripPis w.mI = some (bsC, .forallE domC bodyC bmC) ∧
            domW.getAppFn = domC.getAppFn ∧
            domW.getAppArgs = domC.getAppArgs)) ∧
      w.rulesW.length = w.rulesW'.length ∧
      Forall₂ (fun (p : RecRule md × RecRule md) rC =>
        TwinRuleJ J env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩
          f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC)
        (w.rulesW.zip w.rulesW') w.rulesC := by
  obtain ⟨ws, f, -, -, rfl, hnd, -, -, hall⟩ := h
  have hf' : (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Env md).find? n
      = some (.recInfo cv mI rP rules) := by
    simpa [List.append_assoc] using hf
  rcases find?_append_inv hf' with hold | ⟨hmem, hname⟩
  · rw [hold] at hn
    exact nomatch hn
  · rcases List.mem_append.mp hmem with hrec | hmod
    · obtain ⟨w, hw, heq⟩ := List.mem_map.mp hrec
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq.symm
      obtain ⟨hcv, -, hfkC, hlps, hmodSpec, -, hlenW, hrules⟩ := hall w hw
      have hn' : n = w.cvW.name := by
        have h1 : w.cvW'.name = n := hname
        rw [hcv.name_eq] at h1
        exact h1.symm
      refine ⟨ws, f, w, hw, hn', rfl, rfl, rfl, rfl, hcv, hfkC, hlps, ?_, ?_, hlenW, hrules⟩
      · intro cvm mval hint hm
        subst hn'
        have hmemM : ConstantInfo.defnInfo
            ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint
            ∈ twinRecs ws ++ twinModels ws :=
          List.mem_append_right _
            (List.mem_filterMap.mpr ⟨w, hw, by simp [TwinRecPart.modelInfo?, hm]⟩)
        have hfindM := find?_mem_of_nodup (rest := env.consts) hnd hmemM
        simpa [List.append_assoc, ConstantInfo.name, ConstantInfo.toConstantVal] using hfindM
      · intro hnone
        rw [hnone] at hmodSpec
        exact hmodSpec
    · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
      unfold TwinRecPart.modelInfo? at hw
      obtain ⟨⟨_, _, _⟩, -, hcon⟩ := Option.map_eq_some_iff.mp hw
      exact nomatch hcon

theorem etaClosed_append_nonind {env : Env md} (hE : EtaFamiliesClosed env) :
    ∀ {cs : List (ConstantInfo md)},
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, env.find? c.name = none) →
      (∀ c ∈ cs, ∀ cv caps, c ≠ .indInfo cv caps) →
      EtaFamiliesClosed ⟨cs ++ env.consts⟩
  | [], _, _, _ => hE
  | c :: cs, hnd, hfr, hni => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hE' := etaClosed_append_nonind hE hnd.2
      (fun x hx => hfr x (List.mem_cons_of_mem c hx))
      (fun x hx => hni x (List.mem_cons_of_mem c hx))
    exact EtaFamiliesClosed.cons_nonind hE'
      (find?_append_none_of_not_mem hnd.1 (hfr c List.mem_cons_self))
      (fun cv caps heq _ => absurd heq (hni c List.mem_cons_self cv caps))

theorem envExt_append_shape {env : Env md} :
    ∀ {cs : List (ConstantInfo md)},
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, env.find? c.name = none) →
      (∀ c ∈ cs, c.name.isProjFnShape = false) →
      EnvExt env ⟨cs ++ env.consts⟩
  | [], _, _, _ => EnvExt.refl env
  | c :: cs, hnd, hfr, hsh => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hX := envExt_append_shape hnd.2
      (fun x hx => hfr x (List.mem_cons_of_mem c hx))
      (fun x hx => hsh x (List.mem_cons_of_mem c hx))
    refine EnvExt.cons_over hX
      (find?_append_none_of_not_mem hnd.1 (hfr c List.mem_cons_self)) ?_
    intro T _ _ _
    exact ne_projTableName_of_shape (hsh c List.mem_cons_self) T

/-- **The twin recursor route keeps the η-families closed**, over a package. -/
theorem declRecTwinRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (hE : EtaFamiliesClosed env)
    (h : DeclRecTwinRunJ J env block env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨ws, f, -, -, rfl, hnd, hfr, -, -⟩ := h
  rw [← List.append_assoc]
  refine etaClosed_append_nonind hE hnd hfr ?_
  intro c hc cv caps heq
  rcases List.mem_append.mp hc with hrec | hmod
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp hrec
    rw [← hw] at heq
    exact nomatch heq
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hw
    exact nomatch heq

/-- **The twin recursor route extends the environment**, over a package. -/
theorem declRecTwinRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclRecTwinRunJ J env block env₂) :
    EnvExt env env₂ := by
  obtain ⟨ws, f, -, -, rfl, hnd, hfr, -, hall⟩ := h
  rw [← List.append_assoc]
  refine envExt_append_shape hnd hfr ?_
  intro c hc
  rcases List.mem_append.mp hc with hrec | hmod
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
    have hcv := (hall w hw).1
    show w.cvW'.name.isProjFnShape = false
    rw [hcv.name_eq]
    exact hcv.shape
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hw
    rfl

/-! ## The routes -/

/-- **An inductive block's routes keep the η-families closed**, over a package. -/
theorem indRoutesJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (hE : EtaFamiliesClosed env)
    (h : IndRoutesJ J env block nP env₂) : EtaFamiliesClosed env₂ := by
  rcases h with ⟨_, -, hN⟩ | hM | ⟨_, -, hN⟩ | hT
  · exact declNativeRunJ_etaClosed hE hN
  · exact declIndEtaClosedRunJ hE hM
  · exact declNativeNoRecRunJ_etaClosed hE hN
  · exact declRecTwinRunJ_etaClosed hE hT

/-- **An inductive block's routes extend the environment**, over a package: the
inductive premise of `declRunJ_envExt` at `IndRoutesJ`. -/
theorem indRoutesJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (h : IndRoutesJ J env block nP env₂) :
    EnvExt env env₂ := by
  rcases h with ⟨_, -, hN⟩ | hM | ⟨_, -, hN⟩ | hT
  · exact declNativeRunJ_envExt hN
  · exact declIndRunJ_envExt hM
  · exact declNativeNoRecRunJ_envExt hN
  · exact declRecTwinRunJ_envExt hT

end Ix.Kernel.Semantics
