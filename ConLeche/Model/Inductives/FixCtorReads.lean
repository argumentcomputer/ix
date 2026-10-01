module

public import ConLeche.Model.Inductives.FixRecReadDefs
public section

/-!
# The recursive constructors' reading premises (task #188)

The per-constructor facts of a recursive block (`FixCtorDataI`,
`FixDataP.lean` — the sum route's data with the field kinds, the
opened form, the per-field telescopes and index readings) yield the
reading premises `CtorReadsR` (`FixRecReadDefsP.lean`) the generated
recursor's reading theorems consume.  The bridge is that an opened
variable's type is its binder's domain instantiated at the earlier
variables (`openPisAtFvars_fvarTypeD`), and that instantiation at
variables changes neither the domain's leading `∀`-count
(`Expr.piBinders_instSeq`, whence `teleLen` off `reflOpen`'s binder
count) nor its body's argument count (`getAppArgs_instSeq_fvars`,
whence `fieldArity` off the opened form).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Instantiation at variables and the argument spine -/

/-- Substituting a variable maps an application's arguments. -/
theorem Expr.getAppArgs_instantiate1_fvar {i : Nat} {t : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar i t) k).getAppArgs
        = e.getAppArgs.map (fun a => a.instantiate1 (.fvar i t) k) := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    simp only [Expr.instantiate1, Expr.getAppArgs, List.map_append, List.map_cons, List.map_nil]
    rw [ihg k]
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; first | rfl | (simp only [Expr.instantiate1]; rfl)

/-- Instantiation at variables maps an application's arguments. -/
theorem Expr.getAppArgs_instSeq_fvars :
    ∀ (as : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ as, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty) →
      (Expr.instSeq as t e).getAppArgs = e.getAppArgs.map (Expr.instSeq as t)
  | [], _, e, _ => by simp [Expr.instSeq]
  | a :: as, t, e, hfv => by
    obtain ⟨i, ty, rfl⟩ := hfv a List.mem_cons_self
    show (Expr.instSeq as (t - 1) (e.instantiate1 (.fvar i ty) t)).getAppArgs = _
    rw [Expr.getAppArgs_instSeq_fvars as (t - 1) _ (fun a ha => hfv a (List.mem_cons_of_mem _ ha)),
      Expr.getAppArgs_instantiate1_fvar, List.map_map]
    rfl

/-! ## The constructor data, per block -/

/-- The recursive constructor data of a list of constructors, from
constructor `j` on. -/
@[expose] def fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatumR
  | [], _ => []
  | c :: cs, j =>
    (c.1.name, c.2, dsF j ψ, esF j ψ, ConLeche.recIdxOf (ksF j), eissF j ψ, tssF j ψ) ::
      fixCtorDataList dsF esF ksF eissF tssF ψ cs (j + 1)

omit [SetTheory V] in
theorem fixCtorDataList_length (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by
    simp [fixCtorDataList, fixCtorDataList_length dsF esF ksF eissF tssF ψ cs (j + 1)]

omit [SetTheory V] in
theorem fixCtorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j)[i]?
        = (cs[i]?).map fun c =>
            (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ, ConLeche.recIdxOf (ksF (j + i)),
              eissF (j + i) ψ, tssF (j + i) ψ)
  | [], _, _ => rfl
  | c :: cs, j, 0 => by simp [fixCtorDataList]
  | c :: cs, j, i + 1 => by
    simp only [fixCtorDataList, List.getElem?_cons_succ]
    rw [fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ cs (j + 1) i]
    congr 2
    funext c
    rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The per-constructor facts of a recursive block at a position. -/
@[expose] def FixCtorFactsAt {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  FixCtorDataI m env₀ T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j)
    (srcsF j) (ksF j) (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j)

omit [SetTheory V] in
/-- The recursive positions (finitary or reflexive) are bounded by the
field count. -/
theorem mem_recIdxOf {ks : List RecFieldKind} {i : Nat} :
    i ∈ ConLeche.recIdxOf ks ↔
      i < ks.length ∧ (ks.getD i .ordinary = .recursive ∨ ks.getD i .ordinary = .reflexive) := by
  unfold ConLeche.recIdxOf
  rw [List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

omit [SetTheory V] in
/-- The recursive positions are strictly increasing. -/
theorem recIdxOf_pairwise (ks : List RecFieldKind) : (ConLeche.recIdxOf ks).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

/-- A positional characterisation of the reading premises. -/
theorem CtorReadsR.of_getElem? {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      ctors.length = cds.length →
      (∀ (i : Nat) (c : Name × Nat × Expr × List Nat) (cd : CtorDatumR),
        ctors[i]? = some c → cds[i]? = some cd → CtorReadR m ψ T lps nP nIdx c cd) →
      CtorReadsR m ψ T lps nP nIdx ctors cds
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, cd :: cds, hlen, h =>
    .cons (h 0 c cd rfl rfl) (CtorReadsR.of_getElem? (by simpa using hlen)
      fun i c' cd' hc hcd => h (i + 1) c' cd' (by simpa using hc) (by simpa using hcd))

/-- **The reading premises from the constructor facts.** -/
theorem fixCtorReadsR_of {m : EnvModel V env} {env₀ : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} (ψ : Name → Nat)
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List RecFieldKind)}
    (hlenK : kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt m env₀ T lps nP nIdx resSort isProp large idxF dsF esF srcsF ksF fvsPF xFvsF
        xrestF eissF tssF i cA) :
    CtorReadsR m ψ T lps nP nIdx (ConLeche.nativeCtors4 ctorsA kinds)
      (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) := by
  refine CtorReadsR.of_getElem? ?_ ?_
  · rw [fixCtorDataList_length]
    simp [ConLeche.nativeCtors4, hlenK]
  intro i c cd hc hcd
  simp only [ConLeche.nativeCtors4, List.getElem?_zipWith] at hc
  cases hA : ctorsA[i]? with
  | none => rw [hA] at hc; exact nomatch hc
  | some cA =>
    have hi : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hA).1
    rw [hA, hks i hi] at hc
    simp only [Option.some.injEq] at hc
    subst hc
    rw [fixCtorDataList_getElem?, hA, Nat.zero_add] at hcd
    simp only [Option.map_some, Option.some.injEq] at hcd
    subst hcd
    obtain ⟨hf, hlps, hD⟩ := hcf i cA hA
    obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
    simp only [ConstantInfo.toConstantVal] at hCf hCb
    have hksLen := hD.ksLen
    -- the opening
    obtain ⟨crest, hopP, hopX⟩ := hD.opens
    have hopAll : openPisAtFvars (nP + cA.2) cA.1.type 0 = some (fvsPF i ++ xFvsF i, xrestF i) :=
      openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
    obtain ⟨cbs, es, hst, -⟩ := hD.resid
    -- the field variables, the raw binders and the frame
    have hlenAll : (fvsPF i ++ xFvsF i).length = nP + cA.2 := by
      rw [List.length_append, hD.pLen, hD.xLen]
    have hidxAll := (opening_vars_at hopAll).2.1
    have hxAt : ∀ (i' : Nat), i' < cA.2 → ∀ x, (xFvsF i)[i']? = some x →
        (fvsPF i ++ xFvsF i)[nP + i']? = some x := by
      intro i' hi' x hx
      rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
      exact hx
    have hfvL : ∀ (i' : Nat), ∀ a ∈ (fvsPF i ++ xFvsF i).take (nP + i'),
        ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
      intro i' a ha
      obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
      obtain ⟨ty, rfl⟩ := hidxAll q a hq
      exact ⟨_, ty, rfl⟩
    have hbGet : ∀ (i' : Nat), i' < cA.2 → ∃ b, cbs[nP + i']? = some b ∧
        cbs.getD (nP + i') default = b := by
      intro i' hi'
      have hlt : nP + i' < cbs.length := by rw [ConLeche.Expr.stripPis_length _ hst]; omega
      exact ⟨_, List.getElem?_eq_getElem hlt, by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl⟩
    -- a field's raw binder type, read through the opening's frame: its
    -- telescope's length and its body's argument count are the opened
    -- variable's type's
    have hpb : ∀ (i' : Nat), i' < cA.2 → ∀ x, (xFvsF i)[i']? = some x →
        ∀ b, cbs[nP + i']? = some b →
          (x.fvarTypeD.piBinders).1.length = (b.1.piBinders).1.length ∧
          (x.fvarTypeD.piBinders).2.getAppArgs.length
            = (b.1.piBinders).2.getAppArgs.length := by
      intro i' hi' x hx b hb
      have hty := openPisAtFvars_fvarTypeD (nP + cA.2) hopAll hst (nP + i') b x hb
        (hxAt i' hi' x hx)
      have hlenTake : ((fvsPF i ++ xFvsF i).take (nP + i')).length = nP + i' := by
        rw [List.length_take, hlenAll]
        omega
      obtain ⟨h1, h2⟩ := Expr.piBinders_instSeq ((fvsPF i ++ xFvsF i).take (nP + i'))
        (nP + i' - 1) b.1 (hfvL i') (by rw [hlenTake]; omega)
      rw [hty]
      refine ⟨h1, ?_⟩
      rw [h2, Expr.getAppArgs_instSeq_fvars _ _ _ (hfvL i'), List.length_map]
    refine ⟨rfl, rfl, ⟨_, hf, hlps⟩, hCf, hCb, hD.resid, hD.read ψ, hD.len ψ, hD.lenE ψ, rfl,
      ?_, recIdxOf_pairwise _, hD.eissLen ψ, ?_, hD.tssLen ψ, ?_, ?_, ?_, ?_⟩
    · intro i' hi'
      have := (mem_recIdxOf.mp hi').1
      rwa [hksLen] at this
    · -- the index readings' count
      intro i' hi'
      obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      rcases hk with hk | hk
      · exact hD.eisLen ψ i' hk hlt
      · exact hD.eisLenRefl ψ i' hk hlt
    · -- the telescope's length: the raw binder type's own `∀`-binders
      intro i' hi'
      obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      obtain ⟨x, hx⟩ : ∃ x, (xFvsF i)[i']? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hlt)⟩
      obtain ⟨b, hb, hbd⟩ := hbGet i' hlt
      have hteleEq : ConLeche.structFieldTeleOf cA.1.type nP cA.2 i' = (b.1.piBinders).1 := by
        unfold ConLeche.structFieldTeleOf
        rw [hst]
        simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
      rw [hteleEq, ← (hpb i' hlt x hx b hb).1]
      rcases hk with hk | hk
      · obtain ⟨hfn, -, -, -, -, -⟩ := hD.opened.recF i' x hx hk
        rw [Expr.piBinders_nil_of_getAppFn_const hfn,
          hD.tssNone ψ i' (fun h => by rw [hk] at h; exact nomatch h)]
        rfl
      · obtain ⟨afvs, body, -, hlenTl, -, -⟩ := hD.reflOpen ψ i' x hx hk
        rw [hlenTl]
    · -- a field's domain reads to its entry
      intro i' hi' fvs o hop x hx
      obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hopAll))
      rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen,
        Nat.add_sub_cancel_left] at hx
      exact hD.domRead ψ i' x hx
    · -- the domain's argument count, under the field's own telescope
      intro i' hi' cbs' body' hst'
      obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hst'.symm.trans hst))
      obtain ⟨x, hx⟩ : ∃ x, (xFvsF i)[i']? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hlt)⟩
      obtain ⟨b, hb, hbd⟩ := hbGet i' hlt
      rw [hbd, ← (hpb i' hlt x hx b hb).2]
      rcases hk with hk | hk
      · obtain ⟨hfn, -, hlenA, -, -, -⟩ := hD.opened.recF i' x hx hk
        rw [Expr.piBinders_nil_body (Expr.piBinders_nil_of_getAppFn_const hfn)]
        exact hlenA
      · obtain ⟨afvs, body, hop, -, -, -, -, hlenA, -, -, -⟩ := hD.opened.reflF i' x hx hk
        have hbody := openPisAtFvars_instSeq (x.fvarTypeD.piBinders).1.length hop
          (Expr.stripPis_piBinders x.fvarTypeD)
        have hfvA : ∀ a ∈ afvs, ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
          intro a ha
          obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
          obtain ⟨ty, rfl⟩ := (opening_vars_at hop).2.1 q a hq
          exact ⟨_, ty, rfl⟩
        rw [hbody, Expr.getAppArgs_instSeq_fvars _ _ _ hfvA, List.length_map] at hlenA
        exact hlenA
    · -- a field's entry
      intro i' hi'
      obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      rcases hk with hk | hk
      · rw [hD.tssNone ψ i' (fun h => by rw [hk] at h; exact nomatch h),
          hD.recEntry ψ i' hk hlt]
        rfl
      · exact hD.reflEntry ψ i' hk hlt

end ConLeche.Model
