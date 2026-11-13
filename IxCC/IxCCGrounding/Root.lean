import IxCCGrounding.Ground
import IxCCGrounding.RootCheck

/-!
# Soundness at a root (`IxCCGrounding.Root`)

**`rootSound`**: in every set theory, every model of the kernel's reading with the laws, and every
level assignment: if the checked facts hold on `Sl` (`GroundFacts`, `CaseFacts`, `RootFacts`),
every application site SrcEval may evaluate that the direct route refuses is typed
(`SitesOkRes`), and SrcEval runs the root on first-order arguments to a value whose readback
names a kernel term at the result type (the tag checked by `ResultTag`), then the root applied to
the arguments' terms denotes what that term denotes.

`run` is δ on the root and β per argument: the fundamental lemma relates the root's value to the
root's denotation; the root's stored first-order type puts the arguments' sets in its domains at
graph-regime binders (`mem`); a literal's set is its constructor form's, an enumeration
argument's the listed constructor's image. The result reads back as a literal (its set is the
literal's) or as a field-less constructor whose key, by `ResultTag`, is the named constructor's.

`fibRoot` (a root `Nat → Nat`) and `decideRoot` (a root `Bool`, read back as `true`) are its
instances, the grounding statements of `fib 10 = 55` and of `decide (fib 10 = 55) = true`, with no
typing hypothesis: they take `DirectFacts` (the direct route refuses no site, decided by
`sitesDirectB`); their forms under `SitesOk` are kept as `fibRoot_of_sitesOk`,
`decideRoot_of_sitesOk`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result)

universe w

/-! ## Readback -/

theorem readback_nat {p : Program} {v : Value} {w : Nat}
    (h : IxCC.Src.readbackAll p v = some (.nat w)) : v = .lit w := by
  cases v with
  | lit n =>
    simp only [IxCC.Src.readbackAll, IxCC.Src.readback, Option.some.injEq,
      IxCC.Sem.Obs.nat.injEq] at h
    rw [h]
  | con c ls ps fs =>
    simp only [IxCC.Src.readbackAll, IxCC.Src.readback] at h
    cases hf : IxCC.Src.readbackFields p (fun _ _ _ => true) c ls 0 fs with
    | none => rw [hf] at h; simp at h
    | some os => rw [hf] at h; simp at h
  | _ => simp [IxCC.Src.readbackAll, IxCC.Src.readback] at h

theorem readbackFields_nil {p : Program} {c : CId} {ls : Levels} :
    ∀ {i : Nat} {fs : List Value},
      IxCC.Src.readbackFields p (fun _ _ _ => true) c ls i fs = some [] → fs = []
  | _, [], _ => rfl
  | i, v :: vs, h => by
    simp only [IxCC.Src.readbackFields] at h
    cases hr : IxCC.Src.readbackFields p (fun _ _ _ => true) c ls (i + 1) vs <;>
      cases hv : IxCC.Src.readback p (fun _ _ _ => true) v <;> simp [hr, hv] at h

theorem readback_ctor {p : Program} {v : Value} {i : Nat}
    (h : IxCC.Src.readbackAll p v = some (.ctor i [])) :
    ∃ c ls ps, v = .con c ls ps [] ∧ readTag p c = i := by
  cases v with
  | con c ls ps fs =>
    simp only [IxCC.Src.readbackAll, IxCC.Src.readback] at h
    cases hf : IxCC.Src.readbackFields p (fun _ _ _ => true) c ls 0 fs with
    | none => rw [hf] at h; simp at h
    | some os =>
      rw [hf] at h
      simp at h
      obtain ⟨htag, rfl⟩ := h
      obtain rfl := readbackFields_nil hf
      refine ⟨c, ls, ps, rfl, ?_⟩
      rw [← htag]
      unfold readTag
      cases p.decl? c with
      | none => rfl
      | some d => cases d <;> rfl
  | lit n => simp [IxCC.Src.readbackAll, IxCC.Src.readback] at h
  | _ => simp [IxCC.Src.readbackAll, IxCC.Src.readback] at h

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-! ## The arguments -/

section Args

variable {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann}
  {Sl : List CId}

/-- `enum_arg` over any word clause (step W). -/
theorem enum_argW {Ok' : CId → Levels → Prop} {Wd : Prop} (hF : FaithW Wd p env κ lpsOf (· ∈ Sl))
    {D c : CId} {i : Nat}
    (hE : EnumStored p env κ (· ∈ Sl) D) {safe : Bool} {cs : List CId} {ty : Term}
    (hd : p.decl? D = some (.induct safe 0 0 0 ty cs)) (hc : cs[i]? = some c)
    (φ : LevelParam → Nat) :
    RelV M p κ lpsOf (· ∈ Sl) Ok' (.con c [] [] []) (M.cval (κ c) φ) ∧
      (∀ ρ X, Denotes M.cval env φ ρ (.const (κ c) []) X ↔ X = M.cval (κ c) φ) ∧
      (∀ ρ X, Denotes M.cval env φ ρ (.const (κ D) []) X → M.cval (κ c) φ ∈ˢ X) := by
  obtain ⟨safe', ty', cs', hd', ⟨ciD, hfD, hlD⟩, hcs, _⟩ := hE
  rw [hd] at hd'
  injection hd' with hd''
  injection hd'' with _ _ _ _ _ hcs
  subst hcs
  obtain ⟨hS, -, cv, hfc, hlc, htc⟩ := hcs i c hc
  obtain ⟨ci, hci, hlps⟩ := hF.stored c hS
  rw [hfc] at hci
  cases hci
  have hlv : LvAt φ (lpsOf c) [] := by
    rw [← hlps]; simp only [ConstantInfo.toConstantVal, hlc]; intro i q h; simp at h
  refine ⟨?_, fun ρ X => den_const0 hfc hlc, fun ρ X hX => ?_⟩
  · have := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := (· ∈ Sl)) (Ok := Ok')
      (c := c) (ls := []) (ps := []) (fs := []) (φ := φ) (Ps := []) (Fs := []) (ρ := fun _ => empty)
      hS hlv hfc rfl rfl .nil .nil .nil
      (.inl (by rw [← hlps]; simpa [ConstantInfo.toConstantVal] using hlc))
    simpa using this
  · obtain ⟨T, hT, hm⟩ := mem_key M hfc φ ρ
    simp only [ConstantInfo.toConstantVal, htc] at hT
    rwa [Denotes_functional hT hX] at hm

/-- An enumeration's listed constructor relates to its image, which lies in the enumeration. -/
theorem enum_arg {Ok' : CId → Levels → Prop} (hF : Faith p env κ lpsOf (· ∈ Sl)) {D c : CId} {i : Nat}
    (hE : EnumStored p env κ (· ∈ Sl) D) {safe : Bool} {cs : List CId} {ty : Term}
    (hd : p.decl? D = some (.induct safe 0 0 0 ty cs)) (hc : cs[i]? = some c)
    (φ : LevelParam → Nat) :
    RelV M p κ lpsOf (· ∈ Sl) Ok' (.con c [] [] []) (M.cval (κ c) φ) ∧
      (∀ ρ X, Denotes M.cval env φ ρ (.const (κ c) []) X ↔ X = M.cval (κ c) φ) ∧
      (∀ ρ X, Denotes M.cval env φ ρ (.const (κ D) []) X → M.cval (κ c) φ ∈ˢ X) :=
  enum_argW hF hE hd hc φ

end Args

/-- **The fundamental lemma from the checked facts** (the form the root theorem uses). -/
theorem allP_of_facts (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl)) : ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP (fundHyps_of hL hG (sitesOk_of_res (lawsCore_of_laws hL) hG hT) fun c r hc hr hk => by
    obtain ⟨sh, hst, hpr⟩ := hC c r hc hr hk
    exact caseFires_of_shape hL hG.faith hG.natBasis hc hr hst hpr)

/-- `rootSound_core` over any word clause (step W: the word family calls it). -/
theorem rootSound_coreW (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Wd : Prop}
    (hG : GroundFactsW Wd p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {Ok' : CId → Levels → Prop} (hAllK : ∀ k, AllP M p κ lpsOf (· ∈ Sl) Ok' k)
    (hOkR : Ok' root [])
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hN := hG.natBasis
  have hF0 := natFacts M hN φ
  have hAll := hAllK k
  obtain ⟨ci, hfr, hlr, htr⟩ := hR.stored
  -- δ on the root
  rw [IxCC.Src.run_eq] at hrun
  obtain ⟨f, hf, happ⟩ := Result.bind_eq_ok_iff.mp hrun
  obtain ⟨ci2, hf2, hlps⟩ := hG.faith.stored root hR.mem
  rw [hfr] at hf2
  cases hf2
  have hlv : LvAt φ (lpsOf root) [] := by rw [← hlps, hlr]; intro i q h; simp at h
  have hrelf := hAll.evalConst [] root f φ hf hR.mem hOkR hlv
  -- the arguments
  obtain ⟨F, Es, hFd, hEs, rfl⟩ := (den_mkAppN es).mp hX
  obtain rfl : F = M.cval (κ root) φ := (den_const0 hfr hlr).mp hFd
  have hargs : ∀ {ts : List FoTy} {xs : List Value} {es : List KExpr} {Es : List V},
      (∀ D, FoTy.enum D ∈ ts → FoTy.enum D ∈ args) → FoArgs p κ ts xs es →
      DenotesList M.cval env φ ρ es Es →
      RelSlots M p κ lpsOf (· ∈ Sl) Ok' (xs.map .val) Es ∧
        ∀ (E : BVarIdx → V), Fits M.cval env φ E
          (piTele (ts.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ)) Es
          (pushAll Es E) (res.kexpr κ) := by
    intro ts xs es Es hsub hA hEs
    induction hA generalizing Es with
    | nil => cases hEs; exact ⟨.nil, fun E => by rw [pushAll_nil]; exact .nil⟩
    | @cons t ts x xs e es hv _ ih =>
      cases hEs with
      | @cons _ _ Y Ys hY hYs =>
      obtain ⟨ih1, ih2⟩ := ih (fun D h => hsub D (List.mem_cons_of_mem _ h)) hYs
      have hYrel : RelV M p κ lpsOf (· ∈ Sl) Ok' x Y ∧
          ∀ ρ' Z, Denotes M.cval env φ ρ' (t.kexpr κ) Z → Y ∈ˢ Z := by
        cases hv with
        | nat n =>
          rw [(lit_den M hF0 ρ n Y).mp hY]
          exact ⟨relV_lit_intro hN φ n, fun ρ' Z hZ => by
            rw [(hF0.natD ρ' Z).mp hZ]; exact lit_mem M hF0 n⟩
        | @enum D c i safe cs ty hd hc =>
          have hE := hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          obtain ⟨hrel, hden, hmem⟩ := enum_argW (M := M) (Ok' := Ok') hG.faith hE hd hc φ
          rw [(hden ρ Y).mp hY]
          exact ⟨hrel, fun ρ' Z hZ => hmem ρ' Z hZ⟩
      refine ⟨.cons (.val hYrel.1) ih1, fun E => ?_⟩
      obtain ⟨Z, hZ⟩ : ∃ Z, Denotes M.cval env φ E (t.kexpr κ) Z := by
        cases t with
        | nat => exact ⟨_, (hF0.natD E _).mpr rfl⟩
        | enum D =>
          obtain ⟨_, _, _, _, ⟨ciD, hfD, hlD⟩, _⟩ := hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          exact ⟨_, (den_const0 hfD hlD).mpr rfl⟩
      have h2 := ih2 (push Y E)
      rw [← pushAll_cons] at h2
      exact .cons hZ (hYrel.2 E Z hZ) (by simpa using h2)
  obtain ⟨hrelEs, hfitEs⟩ := hargs (fun D h => h) hA hEs
  -- the chain of applications, at graph-regime sites
  obtain ⟨TT, hTT, hmem⟩ := mem_key M hfr φ ρ
  rw [htr] at hTT
  have hchain : AppChain (M.cval (κ root) φ) Es :=
    appChain_of_fits _ _ hTT hmem (hfitEs ρ) (by
      have := denotesList_length hEs
      have hl := foArgs_length hA
      simp; omega) (fun b hb => by
        simp only [List.mem_map] at hb
        obtain ⟨_, _, rfl⟩ := hb
        simp [regime])
  have hrelv := hAll.applyAll f (xs.map .val) v _ Es happ hrelf hrelEs hchain
  -- the readback
  cases hO with
  | nat w =>
    obtain rfl := readback_nat hrb
    rw [relV_lit_eq hL hN φ hrelv]
    exact (lit_den M hF0 ρ w _).mpr rfl
  | @enum D c i safe cs ty hd hc =>
    obtain ⟨c'', ls, ps, rfl, htag⟩ := readback_ctor hrb
    have hE := hR.enums D (Or.inr rfl)
    obtain ⟨_, hden, _⟩ := enum_argW (M := M) (Ok' := Ok') hG.faith hE hd hc φ
    obtain ⟨_, _, _, hd', _, hcs, _⟩ := hE
    rw [hd] at hd'
    injection hd' with hd''
    injection hd'' with _ _ _ _ _ hcs
    subst hcs
    obtain ⟨_, _, cvc, hfc, hlc, _⟩ := hcs i c hc
    generalize hXv : Es.foldl app (M.cval (κ root) φ) = Xv at hrelv ⊢
    cases hrelv with
    | @con _ _ _ _ ψ cvC np nf Ps Fs ρc σc Rc hSc _ hfc' hPl hFl _ hfs _ =>
    obtain rfl := List.eq_nil_of_length_eq_zero (relVs_length hfs)
    have hnf : nf = 0 := by simpa using hFl.symm
    subst hnf
    have hkey : κ c'' = κ c := hRT safe ty cs c hd hc c'' hSc htag ⟨cvC, np, hfc'⟩
    rw [hkey, hfc] at hfc'
    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
    obtain ⟨rfl, rfl, -⟩ := hfc'
    obtain rfl := List.eq_nil_of_length_eq_zero hPl
    rw [List.nil_append, List.foldl_nil, hkey,
      hL.cval_params _ _ hfc ψ φ (by simp [ConstantInfo.toConstantVal, hlc])]
    exact (hden ρ _).mpr rfl

/-- **Soundness at a root, from the fundamental lemma**: the part of `rootSound` after the
fundamental lemma, over the laws other than canonicity (both families call it). -/
theorem rootSound_core (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {Ok' : CId → Levels → Prop} (hAllK : ∀ k, AllP M p κ lpsOf (· ∈ Sl) Ok' k)
    (hOkR : Ok' root [])
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_coreW hL hG hR hAllK hOkR hA hrun hrb hRT hO φ ρ X hX

/-- **Soundness at a root.** -/
theorem rootSound (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_core (lawsCore_of_laws hL) hG hR (allP_of_facts hL hG hC hT) hR.ok hA hrun hrb hRT hO φ
    ρ X hX

/-- The landed form of `rootSound`, under `SitesOk`. -/
theorem rootSound_of_sitesOk (hL : Laws M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res) (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound hL hG hC hR (sitesOkRes_of_sitesOk hT) hA hrun hrb hRT hO φ ρ X hX

/-- **`fib`, as an instance, with no typing hypothesis**: a root `Nat → Nat`, the direct route
refusing no site (`DirectFacts`, decided by `sitesDirectB`). -/
theorem fibRoot (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  rootSound hL hG hC hR (sitesOkRes_of_direct hD) (.cons (.nat n) .nil) hrun hrb trivial (.nat w)
    φ ρ X hX

/-- The landed form of `fibRoot`, under `SitesOk`. -/
theorem fibRoot_of_sitesOk (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat) (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  rootSound hL hG hC hR (sitesOkRes_of_sitesOk hT) (.cons (.nat n) .nil) hrun hrb trivial (.nat w)
    φ ρ X hX

/-- **`decide (fib 10 = 55)`, as an instance, with no typing hypothesis**: a root `Bool` read
back as constructor `1`, which denotes the kernel's `Bool.true`. -/
theorem decideRoot (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (_hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X := by
  obtain ⟨safe, ty, cs, hd, h1, hsome⟩ := hBL
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
  rw [ht] at h1
  obtain ⟨_, hkt, _⟩ := hG.faith.bool true t (by simpa using ht)
  have h := rootSound hL hG hC hR (sitesOkRes_of_direct hD) .nil hrun hrb hRT (.enum hd h1) φ ρ X hX
  simpa [hkt] using h

/-- The landed form of `decideRoot`, under `SitesOk`. -/
theorem decideRoot_of_sitesOk (hL : Laws M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (_hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X := by
  obtain ⟨safe, ty, cs, hd, h1, hsome⟩ := hBL
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
  rw [ht] at h1
  obtain ⟨_, hkt, _⟩ := hG.faith.bool true t (by simpa using ht)
  have h := rootSound hL hG hC hR (sitesOkRes_of_sitesOk hT) .nil hrun hrb hRT (.enum hd h1) φ ρ X
    hX
  simpa [hkt] using h

/-! ## The landed forms, over `GroundFacts` as first landed (no recursor in `Sl`)

Since G3, `GroundFacts` takes `RecFacts` (each recursor of `Sl` in an admitted class, with the
checked shape) where it took `NoRecr` (no recursor in `Sl`). The landed hypothesis implies the new
one (`groundFacts_of_noRecr`), so each root theorem implies its landed statement. -/

theorem rootSound_noRecr (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    (hG : GroundFactsNoRecr p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound hL (groundFacts_of_noRecr hG) hC hR hT hA hrun hrb hRT hO φ ρ X hX

theorem fibRoot_noRecr (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFactsNoRecr p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  fibRoot hL (groundFacts_of_noRecr hG) hC hR hD hrun hrb φ ρ X hX

theorem decideRoot_noRecr (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFactsNoRecr p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X :=
  decideRoot hL hb hBL (groundFacts_of_noRecr hG) hC hR hD hRT hrun hrb φ ρ X hX

/-! ## The canonicity-free family: the same conclusions over `LawsNoCanon`, with `NoCanon` -/

/-- **Soundness at a root, without canonicity**: `rootSound`'s conclusion, over `LawsNoCanon` in
place of `Laws`, with `NoCanon` among the checked facts. -/
theorem rootSound_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_core hL.core hG hR
    (allP (fundHyps_of_noCanon hL hG hC hNC (sitesOk_of_res hL.core hG hT))) hR.ok hA hrun hrb hRT
    hO φ ρ X hX

/-- **`fib`, without canonicity and with no typing hypothesis.** -/
theorem fibRoot_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  rootSound_noCanon hL hG hC hNC hR (sitesOkRes_of_direct hD) (.cons (.nat n) .nil) hrun hrb
    trivial (.nat w) φ ρ X hX

/-- **`decide (fib 10 = 55)`, without canonicity and with no typing hypothesis.** -/
theorem decideRoot_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (_hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X := by
  obtain ⟨safe, ty, cs, hd, h1, hsome⟩ := hBL
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
  rw [ht] at h1
  obtain ⟨_, hkt, _⟩ := hG.faith.bool true t (by simpa using ht)
  have h := rootSound_noCanon hL hG hC hNC hR (sitesOkRes_of_direct hD) .nil hrun hrb hRT
    (.enum hd h1) φ ρ X hX
  simpa [hkt] using h

/-! ## The canonicity-free family over #678's fields: `Laws678` for `LawsNoCanon`, with `LitDefs` -/

/-- **Soundness at a root, over #678's fields**: `rootSound_noCanon` with `Laws678` (verbatim copies
of the five fields of #678's public `Model` the family uses) for `LawsNoCanon`, at a reading whose
stored `Nat` roles are definitions (`LitDefs`). -/
theorem rootSound_678 (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_noCanon (lawsNoCanon_of_678 hL hLD) hG hC hNC hR hT hA hrun hrb hRT hO φ ρ X hX

/-- **`fib`, over #678's fields, with no typing hypothesis.** -/
theorem fibRoot_678 (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  fibRoot_noCanon (lawsNoCanon_of_678 hL hLD) hG hC hNC hR hD hrun hrb φ ρ X hX

/-- **`decide (fib 10 = 55)`, over #678's fields, with no typing hypothesis.** -/
theorem decideRoot_678 (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X :=
  decideRoot_noCanon (lawsNoCanon_of_678 hL hLD) hb hBL hG hC hNC hR hD hRT hrun hrb φ ρ X hX

end IxCC.Grounding
