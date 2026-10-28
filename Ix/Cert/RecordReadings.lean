import Ix.Cert.RecordTransfer
import Ix.Cert.StreamRename
import Ix.Cert.CtxAgreeProj
import Ix.CompileCert.CanonLevelReading
import Ix.CompileCert.DefinitionReading
import Ix.CompileCert.HeaderReading
import Ix.CompileCert.Canon.Ref
import Ix.Cert.GraphWalk

/-! # Singleton records read as quotient Source's declarations renamed

A definition, axiom or quotient constant compiles to one record. The compile-side reading
theorems (`DefinitionReading.constant_reads`, `HeaderReading.axiom_reads`,
`HeaderReading.quotient_reads`) read it back, in a context aligned with the compile
environment, as terms `Related` to the Lean constant's. This module turns those readings
into what the reader's streams need of a closure's record (`PlainUnits.record`): read in the
closure's context from any state related to quotient Source's, the record declares quotient
Source's declaration renamed.

* `matches_eq`: a reader term that `Matches` a Source conversion, at keys and levels the
  relations determine, is the conversion with its keys and levels mapped; at the renaming
  `names` of quotient Source (`sourceNames`: a name's representative's key, renamed), it is
  quotient Source's term renamed (`mapKL_eq`).
* `Numbering` facts: a constant's own numbering of distinct level parameters numbers them
  `0, …, n - 1`, keeps them apart and is aligned with the reader's positional levels.
* `definition_reads`, `axiom_reads`, `quotient_reads`: the compile-side readings, moved to the
  closure's context (`RecordTransfer.readRecord_le`), are quotient Source's declarations
  renamed; `definition_unit_reads`, `axiom_unit_reads`, `quotient_unit_reads` state them as the
  readings `PlainUnits.record` asks for.

What the closure supplies stays a premise: the compile run of the record and its reading
context (the compile environment's names keyed as quotient Source's, renamed), the closure's
context reading the record's references and key as that context does, the hint, quotient
Source's conversion and lowering of the constant, and distinct level parameters.
-/

namespace Ix.Cert.RecordReadings

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (FiberMap Numbering ingressKey ingressExpr canonLevelIn mapLevels)
open Ix.CompileCert.ExpressionState (Matches Related)

/-! ## Terms: what `Matches` determines -/

/-- A Source term with its keys mapped by `g` and its levels by `h`. -/
def mapKL {md' : Mode} (g : Key .source → Key md') (h : Ix.Kernel.Level → Ix.Kernel.Level) : Ix.Kernel.Expr .source → Ix.Kernel.Expr md'
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (mapKL g h t)
  | .sort u => .sort (h u)
  | .const k us => .const (g k) (us.map h)
  | .app a b => .app (mapKL g h a) (mapKL g h b)
  | .lam t b m => .lam (mapKL g h t) (mapKL g h b) m
  | .forallE t b m => .forallE (mapKL g h t) (mapKL g h b) m
  | .letE t v b l => .letE (mapKL g h t) (mapKL g h v) (mapKL g h b) l
  | .lit l => .lit l
  | .proj k i e => .proj (g k) i (mapKL g h e)

theorem forall₂_eq_map {α β : Type} {R : α → β → Prop} {h : α → β} (hR : ∀ a b, R a b → b = h a) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → bs = as.map h
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab rest => by rw [hR _ _ hab, forall₂_eq_map hR rest]; rfl

/-- **A term matching a Source term, at relations that determine keys and levels, is that
term mapped.** -/
theorem matches_eq {md' : Mode} {K : Key .source → CName md' → Prop} {L : Ix.Kernel.Level → Ix.Kernel.Level → Prop}
    {g : Key .source → Key md'} {h : Ix.Kernel.Level → Ix.Kernel.Level} (hK : ∀ k k', K k k' → k' = g k)
    (hL : ∀ l l', L l l' → l' = h l) {e : Ix.Kernel.Expr .source} {t : CExpr md'} (m : Matches K L e t) :
    t = mapKL g h e := by
  induction m with
  | bvar i => rfl
  | sort hl => rw [hL _ _ hl]; rfl
  | const hk hus => rw [hK _ _ hk, forall₂_eq_map hL hus]; rfl
  | app _ _ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | lam _ _ _ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | forallE _ _ _ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | letE _ _ _ _ ih₁ ih₂ ih₃ => rw [ih₁, ih₂, ih₃]; rfl
  | lit l => rfl
  | proj _ hk _ ih => rw [hK _ _ hk, ih]; rfl

/-- At quotient Source's keys renamed, a mapped term is quotient Source's term (keys at
representatives, levels mapped) renamed. -/
theorem mapKL_eq (ρ : FiberMap) (f : Mode.Id .source → Mode.Id .anon) (h : Ix.Kernel.Level → Ix.Kernel.Level)
    (e : Ix.Kernel.Expr .source) :
    mapKL (fun k => (Ix.LeanIngress.Key.subst ρ k).map f) h e =
      (mapLevels h (Ix.LeanIngress.Expr.substKeys ρ e)).mapKeys f := by
  induction e with
  | bvar i => rfl
  | fvar i t ih => simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, ih]
  | sort u => rfl
  | const k us => rfl
  | app a b iha ihb => simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, iha, ihb]
  | lam t b m iht ihb => simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, iht, ihb]
  | forallE t b m iht ihb =>
    simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, iht, ihb]
  | letE t v b l iht ihv ihb =>
    simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, iht, ihv, ihb]
  | lit l => rfl
  | proj k i x ih => simp only [mapKL, Ix.LeanIngress.Expr.substKeys, mapLevels, Ix.Kernel.Expr.mapKeys, ih]

/-- **Quotient Source's names, renamed**: a Lean name reads as its representative's key
renamed. -/
def sourceNames (ρ : FiberMap) (f : Mode.Id .source → Mode.Id .anon) (n : Ix.Name)
    (k : CName .anon) : Prop :=
  k = (Ix.LeanIngress.Key.subst ρ (ingressKey n)).map f

/-- **A relation reads only the names the term mentions**: two name relations that agree on
the term's mentions (`GraphWalk.Refs`: the constants it applies and the structures it projects)
relate it alike. -/
theorem related_mono {md : Mode} {names names' : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} {s : Ix.Expr} {t : CExpr md}
    (h : Related names levels s t) (agree : ∀ n k, GraphWalk.Refs n s → names n k → names' n k) :
    Related names' levels s t := by
  have self : ∀ n : Ix.Name, (n == n) = true := fun n => Address.beq_iff_eq.mpr rfl
  induction h with
  | bvar index hash => exact .bvar index hash
  | sort hash meaning => exact .sort hash meaning
  | const hash sources targets mapped universes =>
    exact .const hash sources targets (agree _ _ (.const (self _)) mapped) universes
  | app hash _ _ ihf iha =>
    exact .app hash (ihf fun n k r => agree n k (.appF r)) (iha fun n k r => agree n k (.appA r))
  | lam name info hash _ _ iht ihb =>
    exact .lam name info hash (iht fun n k r => agree n k (.lamT r)) (ihb fun n k r => agree n k (.lamB r))
  | all name info hash _ _ iht ihb =>
    exact .all name info hash (iht fun n k r => agree n k (.allT r)) (ihb fun n k r => agree n k (.allB r))
  | letE name nonDep hash _ _ _ iht ihv ihb =>
    exact .letE name nonDep hash (iht fun n k r => agree n k (.letT r)) (ihv fun n k r => agree n k (.letV r))
      (ihb fun n k r => agree n k (.letB r))
  | nat value hash => exact .nat value hash
  | str value hash => exact .str value hash
  | proj field hash mapped _ ih =>
    exact .proj field hash (agree _ _ (.projName (self _)) mapped) (ih fun n k r => agree n k (.projStruct r))
  | mdata data hash plain _ ih => exact .mdata data hash plain (ih fun n k r => agree n k (.mdata r))
  | contract data hash c frame read _ lowered ih =>
    exact .contract data hash c frame read (ih fun n k r => agree n k (.mdata r)) lowered

/-- **A term related to a Lean term at quotient Source's names renamed is the term's
quotient Source conversion renamed**, at a numbering that keeps the constant's level
parameters apart and is aligned with the reader's positional levels. -/
theorem related_renamed {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {params : List Ix.Name} {σ : Ix.Name → LevelParam}
    (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b)
    (aligned : ∀ i (h : i < params.length), id i = σ params[i]) {source : Ix.Expr}
    {target : CExpr .anon}
    (related : Related (sourceNames ρ f) (Ix.CompileCert.UniversePipeline.LevelMeaning params σ id)
      source target) :
    ∃ converted, ingressExpr σ source = .ok converted ∧
      target = (mapLevels (canonLevelIn (params.map σ))
        (Ix.LeanIngress.Expr.substKeys ρ converted)).mapKeys f := by
  obtain ⟨converted, hconv, hm⟩ := Ix.CompileCert.CanonLevelReading.related_ingress_canon inj aligned related
  refine ⟨converted, hconv, ?_⟩
  rw [matches_eq (g := fun k => (Ix.LeanIngress.Key.subst ρ k).map f)
    (h := canonLevelIn (params.map σ)) (fun k k' ⟨n, hk, hn⟩ => by rw [hn, hk]) (fun l l' hl => hl.symm) hm,
    mapKL_eq]

/-! ## Numberings of distinct level parameters -/

theorem findIdx?_beqRaw_nodup : ∀ {names : List Ix.Name}, names.Nodup → ∀ {i : Nat}
    (hi : i < names.length), names.findIdx? (Ix.Name.beqRaw · names[i]) = some i
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: as, hnd, i, hi => by
    rw [List.findIdx?_cons]
    cases i with
    | zero => simp [Ix.Name.beqRaw_iff.mpr rfl]
    | succ j =>
      have hj : j < as.length := by simpa using hi
      have hne : Ix.Name.beqRaw a as[j] = false := by
        rw [Bool.eq_false_iff]
        intro heq
        have := Ix.Name.beqRaw_iff.mp heq
        exact (List.nodup_cons.mp hnd).1 (this ▸ List.getElem_mem hj)
      simp only [List.getElem_cons_succ, hne, Bool.false_eq_true, ↓reduceIte]
      rw [findIdx?_beqRaw_nodup (List.nodup_cons.mp hnd).2 hj]
      rfl

/-- A constant's own numbering numbers its distinct level parameters by position. -/
theorem pos_nodup {names : Array Ix.Name} (hnd : names.toList.Nodup) {i : Nat}
    (hi : i < names.size) : (Numbering.mk names false).pos names[i] = i := by
  rcases names with ⟨l⟩
  have h := findIdx?_beqRaw_nodup hnd (i := i) (by simpa using hi)
  have h' : (List.toArray l).findIdx? (Ix.Name.beqRaw · (List.toArray l)[i]) = some i := by
    simpa [List.findIdx?_toArray] using h
  unfold Numbering.pos
  simp only [h']
  cases i <;> rfl

/-- A constant's own numbering of distinct level parameters is `0, …, n - 1`. -/
theorem params_nodup {names : Array Ix.Name} (hnd : names.toList.Nodup) :
    (Numbering.mk names false).params = List.range names.size := by
  apply List.ext_getElem
  · simp [Numbering.params]
  · intro i h₁ h₂
    have hi : i < names.size := by simpa [Numbering.params] using h₁
    simp only [Numbering.params, List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact pos_nodup hnd hi

/-- It keeps them apart. -/
theorem pos_inj {names : Array Ix.Name} (hnd : names.toList.Nodup) :
    ∀ a ∈ names.toList, ∀ b ∈ names.toList,
      (Numbering.mk names false).pos a = (Numbering.mk names false).pos b → a = b := by
  intro a ha b hb he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  simp only [Array.getElem_toList] at he ⊢
  rw [pos_nodup hnd (by simpa using hi), pos_nodup hnd (by simpa using hj)] at he
  subst he
  rfl

/-- It is aligned with the reader's positional levels. -/
theorem pos_aligned {names : Array Ix.Name} (hnd : names.toList.Nodup) :
    ∀ i (h : i < names.toList.length), id i = (Numbering.mk names false).pos names.toList[i] := by
  intro i h
  simp only [Array.getElem_toList, id]
  exact (pos_nodup hnd (by simpa using h)).symm

/-- Its positions are its parameters. -/
theorem params_map_pos (names : Array Ix.Name) :
    names.toList.map (Numbering.mk names false).pos = (Numbering.mk names false).params := rfl

/-! ## Quotient Source's conversion of a singleton -/

theorem numbering_beq_self (σ : Numbering) : (σ == σ) = true := by
  show (σ.large == σ.large && σ.names.isEqv σ.names Ix.Name.beqRaw) = true
  rw [Bool.and_eq_true]
  refine ⟨by simp, ?_⟩
  rw [Array.isEqv_iff_rel]
  exact ⟨rfl, fun i _ => Ix.Name.beqRaw_iff.mpr rfl⟩

theorem exprsOf_two {σ : Numbering} {t v : Ix.Expr} {ks : Array (CExpr .source)}
    (h : Ix.LeanIngress.exprsOf #[(σ, t), (σ, v)] = .ok ks) :
    ∃ t' v', ingressExpr σ.pos t = .ok t' ∧ ingressExpr σ.pos v = .ok v' ∧ ks = #[t', v'] := by
  simp [Ix.LeanIngress.exprsOf, numbering_beq_self] at h
  split at h
  · rename_i ks' hks
    cases h
    rw [Ix.LeanIngress.nameExprs_eq]
    simp only [Ix.LeanIngress.ingressExprs, List.mapM_cons, List.mapM_nil] at hks
    cases ht : ingressExpr σ.pos t <;> cases hv : ingressExpr σ.pos v <;>
      simp [ht, hv, bind, Except.bind, pure, Except.pure] at hks
    subst hks
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases h

theorem exprsOf_one {σ : Numbering} {t : Ix.Expr} {ks : Array (CExpr .source)}
    (h : Ix.LeanIngress.exprsOf #[(σ, t)] = .ok ks) :
    ∃ t', ingressExpr σ.pos t = .ok t' ∧ ks = #[t'] := by
  simp [Ix.LeanIngress.exprsOf] at h
  split at h
  · rename_i ks' hks
    cases h
    rw [Ix.LeanIngress.nameExprs_eq]
    simp only [Ix.LeanIngress.ingressExprs, List.mapM_cons, List.mapM_nil] at hks
    cases ht : ingressExpr σ.pos t <;> simp [ht, bind, Except.bind, pure, Except.pure] at hks
    subst hks
    exact ⟨_, rfl, rfl⟩
  · cases h

/-- **A singleton definition group converts to its one member**: the constant's key, its
numbering's parameters, its type and value converted under that numbering, its shape. -/
theorem convertDefinitions_single {ci : Ix.ConstantInfo} {c : Ix.LeanIngress.Converted}
    (h : Ix.LeanIngress.convertDefinitions #[ci] = .ok c) :
    ∃ s v t' v', Ix.LeanIngress.definitionShape ci = some s ∧
      Ix.LeanIngress.definitionValue ci = some v ∧
      ingressExpr (Numbering.mk ci.getCnst.levelParams false).pos ci.getCnst.type = .ok t' ∧
      ingressExpr (Numbering.mk ci.getCnst.levelParams false).pos v = .ok v' ∧
      c = .definitions #[⟨⟨ingressKey ci.getCnst.name, (Numbering.mk ci.getCnst.levelParams false).params, t'⟩,
        v', s.1, s.2.1, s.2.2⟩] := by
  cases hs : Ix.LeanIngress.definitionShape ci with
  | none =>
    simp [Ix.LeanIngress.convertDefinitions, hs, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind, Functor.map, Except.map] at h
  | some s =>
    cases hv : Ix.LeanIngress.definitionValue ci with
    | none =>
      simp [Ix.LeanIngress.convertDefinitions, hs, hv, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind, Functor.map, Except.map] at h
    | some v =>
      simp [Ix.LeanIngress.convertDefinitions, hs, hv] at h
      cases hk : Ix.LeanIngress.exprsOf
          #[(Numbering.mk ci.getCnst.levelParams false, ci.getCnst.type),
            (Numbering.mk ci.getCnst.levelParams false, v)] with
      | error e => rw [hk] at h; cases h
      | ok ks =>
        rw [hk] at h
        obtain ⟨t', v', ht, hv', rfl⟩ := exprsOf_two hk
        simp only [Functor.map, Except.map, Except.ok.injEq] at h
        exact ⟨s, v, t', v', rfl, rfl, ht, hv', h.symm⟩

/-- **An axiom converts** to its key, its numbering's parameters and its type converted. -/
theorem convert_axiom {v : Ix.AxiomVal} {c : Ix.LeanIngress.Converted}
    (h : Ix.LeanIngress.convert (.axiom v) = .ok c) :
    ∃ t', v.isUnsafe = false ∧
      ingressExpr (Numbering.mk v.cnst.levelParams false).pos v.cnst.type = .ok t' ∧
      c = .axiom ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩ := by
  simp [Ix.LeanIngress.convert] at h
  cases hu : v.isUnsafe
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    cases hk : Ix.LeanIngress.exprsOf #[(Numbering.mk v.cnst.levelParams false, v.cnst.type)] with
    | error e => rw [hk] at h; cases h
    | ok ks =>
      rw [hk] at h
      obtain ⟨t', ht, rfl⟩ := exprsOf_one hk
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      exact ⟨t', rfl, ht, h.symm⟩
  · simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- **A quotient constant converts** to its kind, key, numbering's parameters and type
converted. -/
theorem convert_quot {v : Ix.QuotVal} {c : Ix.LeanIngress.Converted}
    (h : Ix.LeanIngress.convert (.quot v) = .ok c) :
    ∃ t', ingressExpr (Numbering.mk v.cnst.levelParams false).pos v.cnst.type = .ok t' ∧
      c = .quot (Ix.LeanIngress.quotKindOf v.kind)
        ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩ := by
  simp [Ix.LeanIngress.convert] at h
  cases hk : Ix.LeanIngress.exprsOf #[(Numbering.mk v.cnst.levelParams false, v.cnst.type)] with
  | error e => rw [hk] at h; cases h
  | ok ks =>
    rw [hk] at h
    obtain ⟨t', ht, rfl⟩ := exprsOf_one hk
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨t', ht, h.symm⟩

/-! ## Quotient Source's members, canonical -/

theorem defMember_canon (m : Ix.LeanIngress.DefMember) : Ix.LeanIngress.DefMember.canon m =
    { m with cv := { m.cv with type := mapLevels (canonLevelIn m.cv.levelParams) m.cv.type },
             value := mapLevels (canonLevelIn m.cv.levelParams) m.value } := by
  have h1 := Ix.LeanIngress.mapLevelsGo_spec (f := canonLevelIn m.cv.levelParams) m.cv.type (memo := {})
    (by intro k v hk; simp at hk)
  have h2 := Ix.LeanIngress.mapLevelsGo_spec (f := canonLevelIn m.cv.levelParams) m.value h1.2
  show Ix.LeanIngress.DefMember.mk ⟨m.cv.name, m.cv.levelParams, (Ix.LeanIngress.mapLevelsGo (canonLevelIn m.cv.levelParams) ∅ m.cv.type).1⟩ (Ix.LeanIngress.mapLevelsGo (canonLevelIn m.cv.levelParams) (Ix.LeanIngress.mapLevelsGo (canonLevelIn m.cv.levelParams) ∅ m.cv.type).2 m.value).1 m.kind m.safety m.hint = _
  rw [h1.1, h2.1]

theorem canonValM_run (cv : Ix.Kernel.ConstantVal .source) :
    (Ix.LeanIngress.canonValM cv).run' {} =
      { cv with type := mapLevels (canonLevelIn cv.levelParams) cv.type } := by
  have h1 := Ix.LeanIngress.mapLevelsGo_spec (f := canonLevelIn cv.levelParams) cv.type (memo := {})
    (by intro k v hk; simp at hk)
  show Ix.Kernel.ConstantVal.mk cv.name cv.levelParams (Ix.LeanIngress.mapLevelsGo (canonLevelIn cv.levelParams) ∅ cv.type).1 = _
  rw [h1.1]

/-- **Quotient Source's member of a singleton definition group** at the hint `h`: renamed to
representatives, levels canonical. -/
def quotientMember (ρ : FiberMap) (m0 : Ix.LeanIngress.DefMember) (h : ReducibilityHint) :
    Ix.LeanIngress.DefMember :=
  Ix.LeanIngress.DefMember.canon (Ix.LeanIngress.DefMember.substKeys ρ { m0 with hint := h })

/-! ## The reader on a definition record -/

/-- The declaration `lowerDefinition` makes at a known hint. -/
def kindDecl (st : State .anon) (kind : Ix.DefKind) (cv : CVal .anon) (value : CExpr .anon)
    (h : ReducibilityHint) : CDecl .anon :=
  match kind with
  | .defn => .defnDecl cv ((projRewrite st cv value).getD value) h
  | .thm => .thmDecl cv ((projRewrite st cv value).getD value)
  | .opaq => .opaqueDecl cv value

theorem lowerDefinition_some {st : State .anon} {heights : CName .anon → Nat} {cv : CVal .anon}
    {value : CExpr .anon} {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {h : ReducibilityHint}
    {decl : CDecl .anon} {rw : Bool}
    (hl : lowerDefinition (some h) st heights cv value kind safety = .ok (decl, rw)) :
    decl = kindDecl st kind cv value h := by
  unfold lowerDefinition at hl
  cases hs : safetyDeclineOf kind safety with
  | some why => simp [hs, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hl
  | none =>
    cases kind <;> simp [hs, pure, Except.pure] at hl <;>
      (obtain ⟨rfl, -⟩ := hl; rfl)

/-- A definition record's reading: one declaration, lowered at the context's hint. -/
theorem readRecord_defn {cx : Ctx .anon} {st : State .anon} {owner : Address} {c : Ixon.Constant}
    {d : Ixon.Definition} (hc : c.info = .defn d) {r : Read .anon}
    (h : readRecord cx st owner c = .ok r) :
    ∃ key ty value decl rw, cx.memberKey (.member owner 0) = .ok key ∧
      lowerDefinition (cx.hint (.member owner 0)) st (st.heights.getD · 0)
        ⟨key, List.range d.lvls.toNat, ty⟩ value d.kind d.safety = .ok (decl, rw) ∧
      r = { decls := #[decl], projRewrites := if rw then 1 else 0 } := by
  unfold readRecord at h
  rw [hc] at h
  simp only at h
  obtain ⟨p, hp, hr⟩ := RecordTransfer.bind_ok h
  unfold readDefinition at hp
  obtain ⟨key, hkey, hp⟩ := RecordTransfer.bind_ok hp
  obtain ⟨ty, -, hp⟩ := RecordTransfer.bind_ok hp
  obtain ⟨value, -, hp⟩ := RecordTransfer.bind_ok hp
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  exact ⟨key, ty, value, p.1, p.2, hkey, hp, hr.symm⟩

/-- A declaration `DefinitionDecl` describes, at a definition's hint, is `kindDecl`'s. -/
theorem definitionDecl_kindDecl {st : State .anon} {cv : CVal .anon} {value : CExpr .anon}
    {kind : Ix.DefKind} {decl : CDecl .anon} {h : ReducibilityHint}
    (hd : DefinitionDecl cv value (projRewrite st cv value) kind decl)
    (hint : ∀ cv' v' h', decl = .defnDecl cv' v' h' → h' = h) :
    decl = kindDecl st kind cv value h := by
  cases hd with
  | defn h' => rw [hint _ _ _ rfl]; rfl
  | thm => rfl
  | opaq => rfl

/-! ## A compiled definition, read as quotient Source's declaration renamed -/

/-- What the compiler's definition view says of a constant, as quotient Source reads it. -/
theorem sourceData_facts {ci : Ix.ConstantInfo} {source : Ix.Def}
    (h : Ix.CompileCert.EmissionDispatch.sourceData ci = some source) :
    ci.getCnst.name = source.name ∧ ci.getCnst.levelParams = source.levelParams ∧
      ci.getCnst.type = source.type ∧ Ix.LeanIngress.definitionValue ci = some source.value ∧
      ∃ hint, Ix.LeanIngress.definitionShape ci = some (source.kind, source.safety, hint) := by
  cases ci with
  | defnInfo v =>
    simp only [Ix.CompileCert.EmissionDispatch.sourceData, Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, rfl, Ix.LeanIngress.hintOf v.hints, ?_⟩
    cases hs : v.safety <;>
      simp [Ix.LeanIngress.definitionShape, Ix.CompileM.definitionValData, Ix.LeanIngress.safetyOf,
        Ix.CompileM.convertSafety, hs]
  | thmInfo v =>
    simp only [Ix.CompileCert.EmissionDispatch.sourceData, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, _, rfl⟩
  | opaqueInfo v =>
    simp only [Ix.CompileCert.EmissionDispatch.sourceData, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, _, rfl⟩
  | _ => simp [Ix.CompileCert.EmissionDispatch.sourceData] at h

section Definition

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Sharing.Verify (BlockWireTablesWF)

/-- **A compiled definition reads, in a closure's context and from any state related to
quotient Source's, as quotient Source's declaration renamed.**

The compile run and its reading context `cx₁` are the compile-side reading theorem's
(`DefinitionReading.constant_reads`), at quotient Source's names renamed (`sourceNames`); the
closure's context `cx` reads the record's references as `cx₁` does with the block's blobs,
and both read its key and the hint `h`, at which quotient Source lowers the constant
(`quotientMember`). The level parameters are distinct. -/
theorem definition_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {P : KeyScope .source} (hP : P.Pre) (hf : InjOn f P)
    {ci : Ix.ConstantInfo} {source : Ix.Def}
    (view : EmissionDispatch.sourceData ci = some source)
    (nodup : source.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (safe : safetyDeclineOf source.kind source.safety = none)
    (ran : rawRun (compileConstantInfo ci) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f))
    (self : names source.name ((Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f))
    (agree : ∀ n k, (GraphWalk.Refs n source.type ∨ GraphWalk.Refs n source.value) → names n k →
      sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    {h : ReducibilityHint} (hint : cx.hint (.member output.blockAddr 0) = some h)
    (sameHint : cx₁.hint (.member output.blockAddr 0) = some h)
    {m0 : Ix.LeanIngress.DefMember}
    (conv : Ix.LeanIngress.convertDefinitions #[ci] = .ok (.definitions #[m0]))
    {stS : State .source} {stA : State .anon} (hst : StreamRename.StateRen f P stS stA)
    (ownersGood : ∀ k : Key .source, k.Good P → ∀ o, stS.projOwners[k]? = some o → o.Good P)
    (typeGood : (quotientMember ρ m0 h).cv.type.Good P) (valueGood : (quotientMember ρ m0 h).value.Good P)
    {declS : CDecl .source} {rwS : Bool}
    (lowS : lowerDefinition (some h) stS (stS.heights.getD · 0) (quotientMember ρ m0 h).cv
      (quotientMember ρ m0 h).value (quotientMember ρ m0 h).kind (quotientMember ρ m0 h).safety =
        .ok (declS, rwS)) :
    ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
      rA.decls = #[declS.mapKeys f] := by
  have aliases : DefinitionReading.SelfAliases source.name
      ((Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f) names := by
    intro query hq
    rw [Ix.CompileCert.Canon.nameCompareExact_eq_iff.mp hq]
    exact self
  -- the compile-side reading
  obtain ⟨-, -, result, declaration, type, value, read, decls, typeRel, valueRel, ddecl⟩ :=
    DefinitionReading.constant_reads (cx := cx₁) (names := names) (σ := (Numbering.mk source.levelParams false).pos)
      (bindings := bindings) context aligned external ci source view stA keyed aliases clean
      wire safe ran
  -- the record is a definition record
  have selfSound := DefinitionReading.singleton_self cx₁ output.blockAddr source.name context
    names keyed aliases
  have ran' := ran
  rw [EmissionDispatch.definition_run context ci source view] at ran'
  obtain ⟨-, -, -, erased, -⟩ := EmissionBlocks.definitionInfo_correct cx₁ id
    (DefinitionReading.selfAt cx₁ output.blockAddr) names (Numbering.mk source.levelParams false).pos bindings
    (EmissionDispatch.singletonContext source.name context) aligned external source
    (constsSatisfy_of_forall (fun name => selfSound name) _)
    (constsSatisfy_of_forall (fun name => selfSound name) _) clean ran'
  obtain ⟨target, hinfo, -, -, -⟩ := DefinitionReading.erase_defn erased
  -- the reading carries over to the closure's context
  have readA : readRecord cx stA output.blockAddr output.block = .ok result :=
    RecordTransfer.readRecord_le refs sameKey (by rw [hint, ← sameHint]; rfl) (by rw [hinfo]; rfl) read
  obtain ⟨key, ty, val, decl, rw, -, lowA, rfl⟩ := readRecord_defn hinfo readA
  rw [hint] at lowA
  have hdecl := lowerDefinition_some lowA
  simp only [Array.mk.injEq, List.cons.injEq, and_true] at decls
  subst decls
  -- the declaration read, at the context's hint
  have hdef : decl = kindDecl stA source.kind
      ⟨(Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f,
        List.range source.levelParams.size, type⟩ value h := by
    refine definitionDecl_kindDecl ddecl fun cv' v' h' he => ?_
    rw [hdecl] at he
    unfold kindDecl at he
    split at he <;> first | (cases he; rfl) | cases he
  -- quotient Source's member
  obtain ⟨hname, hlps, htype, hvalue, shapeHint, hshape⟩ := sourceData_facts view
  obtain ⟨s, v, t', v', hs, hv, ht', hv', hm0⟩ := convertDefinitions_single conv
  rw [hshape, Option.some.injEq] at hs
  rw [hvalue, Option.some.injEq] at hv
  subst hs hv
  simp only [Ix.LeanIngress.Converted.definitions.injEq, Array.mk.injEq, List.cons.injEq,
    and_true] at hm0
  rw [hlps, htype] at ht'
  rw [hlps] at hv'
  -- the reading's terms are quotient Source's renamed
  obtain ⟨convT, hconvT, htypeEq⟩ := related_renamed (pos_inj nodup) (pos_aligned nodup) 
    (related_mono typeRel fun n k r hn => agree n k (.inl r) hn)
  obtain ⟨convV, hconvV, hvalueEq⟩ := related_renamed (pos_inj nodup) (pos_aligned nodup)
    (related_mono valueRel fun n k r hn => agree n k (.inr r) hn)
  rw [ht', Except.ok.injEq] at hconvT
  rw [hv', Except.ok.injEq] at hconvV
  subst hconvT hconvV
  have hqm : quotientMember ρ m0 h =
      ⟨⟨Ix.LeanIngress.Key.subst ρ (ingressKey source.name), List.range source.levelParams.size,
        mapLevels (canonLevelIn (List.range source.levelParams.size)) (Ix.LeanIngress.Expr.substKeys ρ t')⟩,
        mapLevels (canonLevelIn (List.range source.levelParams.size)) (Ix.LeanIngress.Expr.substKeys ρ v'), source.kind,
        source.safety, h⟩ := by
    rw [quotientMember, defMember_canon, hm0]
    simp only [Ix.LeanIngress.DefMember.substKeys, Ix.LeanIngress.ConstantVal.substKeys, hname, hlps,
      params_nodup nodup]
  rw [params_map_pos, params_nodup nodup] at htypeEq hvalueEq
  -- quotient Source's lowering, renamed
  have agree : CtxAgree.ProjectionAgree f P stS stA := ⟨hst.owners, ownersGood, hst.levels⟩
  have heights : ∀ k : Key .source, k.Good P → stA.heights.getD (k.map f) 0 = stS.heights.getD k 0 := by
    intro k hk
    simp only [Std.HashMap.getD_eq_getD_getElem?, hst.heights k hk]
  have lowR := CtxAgree.lowerDefinition_mapKeys hP hf agree (heights := fun k => stS.heights.getD k 0)
    (heights' := fun k => stA.heights.getD k 0) heights typeGood valueGood (some h)
    (quotientMember ρ m0 h).kind (quotientMember ρ m0 h).safety
  rw [lowS] at lowR
  have hdeclS := lowerDefinition_some lowR
  refine ⟨_, readA, ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [hdef, hdeclS, hqm, htypeEq, hvalueEq]
  rfl

/-- **Quotient Source's header of a singleton constant**: renamed to representatives, levels
canonical. -/
def quotientHeader (ρ : FiberMap) (cv : CVal .source) : CVal .source :=
  (Ix.LeanIngress.canonValM (Ix.LeanIngress.ConstantVal.substKeys ρ cv)).run' {}

theorem quotientHeader_eq (ρ : FiberMap) (cv : CVal .source) :
    quotientHeader ρ cv = ⟨Ix.LeanIngress.Key.subst ρ cv.name, cv.levelParams,
      mapLevels (canonLevelIn cv.levelParams) (Ix.LeanIngress.Expr.substKeys ρ cv.type)⟩ := by
  rw [quotientHeader, canonValM_run]
  rfl

/-- **A compiled axiom reads, in a closure's context and from any state, as quotient
Source's declaration renamed**, under the compile-side reading theorem's premises
(`HeaderReading.axiom_reads`) at quotient Source's names renamed, with the closure's context
reading the record as the compile-side context does. -/
theorem axiom_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {v : Ix.AxiomVal} (nodup : v.cnst.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.axiomInfo v)) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey v.cnst.name)).map f))
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext v.cnst.name context).2
      (fun _ => none) names) v.cnst.type)
    (agree : ∀ n k, GraphWalk.Refs n v.cnst.type → names n k → sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    (sameHint : cx.hint (.member output.blockAddr 0) = cx₁.hint (.member output.blockAddr 0))
    {cv0 : CVal .source} (conv : Ix.LeanIngress.convert (.axiom v) = .ok (.axiom cv0))
    (stA : State .anon) :
    ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
      rA.decls = #[(Declaration.axiomDecl (quotientHeader ρ cv0)).mapKeys f] := by
  obtain ⟨t', safe, ht', hc⟩ := convert_axiom conv
  simp only [Ix.LeanIngress.Converted.axiom.injEq] at hc
  subst hc
  obtain ⟨-, -, type, typeRel, read⟩ :=
    HeaderReading.axiom_reads (cx := cx₁) (names := names)
      (σ := (Numbering.mk v.cnst.levelParams false).pos) (bindings := bindings) context aligned
      external v stA keyed scope clean wire safe ran
  have ran' := ran
  rw [EmissionDispatch.axiom_run context] at ran'
  obtain ⟨-, -, -, erased, -⟩ := EmissionBlocks.axiomInfo_correct cx₁ id (fun _ => none)
    names (Numbering.mk v.cnst.levelParams false).pos bindings
    (EmissionDispatch.singletonContext v.cnst.name context) aligned external v scope clean ran'
  obtain ⟨target, hinfo, -, -⟩ :=
    HeaderReading.erase_axio (payload := Emission.axiomPayload v (.sort 0)) erased
  have readA := RecordTransfer.readRecord_le refs sameKey sameHint (by rw [hinfo]; rfl) read
  refine ⟨_, readA, ⟨rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨convT, hconvT, htypeEq⟩ := related_renamed (pos_inj nodup) (pos_aligned nodup)
    (related_mono typeRel agree)
  rw [ht', Except.ok.injEq] at hconvT
  subst hconvT
  rw [params_map_pos, params_nodup nodup] at htypeEq
  rw [htypeEq, quotientHeader_eq, params_nodup nodup]
  rfl

/-- **A compiled quotient constant reads, in a closure's context and from any state, as
quotient Source's declaration renamed** (`HeaderReading.quotient_reads`'s premises). -/
theorem quotient_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {v : Ix.QuotVal} (nodup : v.cnst.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.quotInfo v)) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey v.cnst.name)).map f))
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext v.cnst.name context).2
      (fun _ => none) names) v.cnst.type)
    (agree : ∀ n k, GraphWalk.Refs n v.cnst.type → names n k → sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    (sameHint : cx.hint (.member output.blockAddr 0) = cx₁.hint (.member output.blockAddr 0))
    {kind : Ix.Kernel.QuotKind} {cv0 : CVal .source}
    (conv : Ix.LeanIngress.convert (.quot v) = .ok (.quot kind cv0)) (stA : State .anon) :
    ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
      rA.decls = #[(Declaration.quotDecl kind (quotientHeader ρ cv0)).mapKeys f] := by
  obtain ⟨t', ht', hc⟩ := convert_quot conv
  simp only [Ix.LeanIngress.Converted.quot.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨-, -, type, typeRel, read⟩ :=
    HeaderReading.quotient_reads (cx := cx₁) (names := names)
      (σ := (Numbering.mk v.cnst.levelParams false).pos) (bindings := bindings) context aligned
      external v stA keyed scope clean wire ran
  have ran' := ran
  rw [EmissionDispatch.quotient_run context] at ran'
  obtain ⟨-, -, -, erased, -⟩ := EmissionBlocks.quotientInfo_correct cx₁ id (fun _ => none)
    names (Numbering.mk v.cnst.levelParams false).pos bindings
    (EmissionDispatch.singletonContext v.cnst.name context) aligned external v scope clean ran'
  obtain ⟨target, hinfo, -, -⟩ := HeaderReading.erase_quot erased
  have readA := RecordTransfer.readRecord_le refs sameKey sameHint (by rw [hinfo]; rfl) read
  refine ⟨_, readA, ⟨rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨convT, hconvT, htypeEq⟩ := related_renamed (pos_inj nodup) (pos_aligned nodup)
    (related_mono typeRel agree)
  rw [ht', Except.ok.injEq] at hconvT
  subst hconvT
  rw [params_map_pos, params_nodup nodup] at htypeEq
  rw [htypeEq, quotientHeader_eq, params_nodup nodup]
  have hk : quotKind (convertQuotKind v.kind) = Ix.LeanIngress.quotKindOf v.kind := by
    cases v.kind <;> rfl
  rw [hk]
  rfl

/-! ## The units' readings -/

theorem lower_definition {st : State .source} {m : Ix.LeanIngress.DefMember} {r : Read .source}
    (h : Ix.LeanIngress.lower st (.definitions #[m]) = .ok r) :
    ∃ decl rw, lowerDefinition (some m.hint) st (st.heights.getD · 0) m.cv m.value m.kind m.safety =
        .ok (decl, rw) ∧ r = { decls := #[decl], projRewrites := if rw then 1 else 0 } := by
  have unfolded : Ix.LeanIngress.lower st (.definitions #[m]) =
      (do
        let (decl, rw) ← lowerDefinition (some m.hint) st (st.heights.getD · 0) m.cv m.value m.kind m.safety
        pure { decls := #[decl], projRewrites := if rw then 1 else 0 }) := rfl
  rw [unfolded] at h
  obtain ⟨p, hp, hr⟩ := RecordTransfer.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  exact ⟨p.1, p.2, hp, hr.symm⟩

/-- **A compiled definition's record reads as quotient Source's unit renamed**, from every
state related to the unit's (the `reads` of `StreamRename.PlainUnits.record`). -/
theorem definition_unit_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {P : KeyScope .source} (hP : P.Pre) (hf : InjOn f P)
    {ci : Ix.ConstantInfo} {source : Ix.Def}
    (view : EmissionDispatch.sourceData ci = some source)
    (nodup : source.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (safe : safetyDeclineOf source.kind source.safety = none)
    (ran : rawRun (compileConstantInfo ci) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f))
    (self : names source.name ((Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f))
    (agree : ∀ n k, (GraphWalk.Refs n source.type ∨ GraphWalk.Refs n source.value) → names n k →
      sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    {h : ReducibilityHint} (hint : cx.hint (.member output.blockAddr 0) = some h)
    (sameHint : cx₁.hint (.member output.blockAddr 0) = some h)
    {m0 : Ix.LeanIngress.DefMember}
    (conv : Ix.LeanIngress.convertDefinitions #[ci] = .ok (.definitions #[m0]))
    {stS : State .source}
    (ownersGood : ∀ k : Key .source, k.Good P → ∀ o, stS.projOwners[k]? = some o → o.Good P)
    (typeGood : (quotientMember ρ m0 h).cv.type.Good P) (valueGood : (quotientMember ρ m0 h).value.Good P)
    {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (.definitions #[quotientMember ρ m0 h]) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
        rA.decls = rS.decls.map (Declaration.mapKeys f) := by
  intro stA hst
  obtain ⟨declS, rwS, lowS, rfl⟩ := lower_definition lowered
  have hhint : (quotientMember ρ m0 h).hint = h := by
    rw [quotientMember, defMember_canon]
    rfl
  rw [hhint] at lowS
  obtain ⟨rA, read, plain, decls⟩ := definition_reads hP hf view nodup context clean wire safe ran
    aligned external keyed self agree refs sameKey hint sameHint conv hst ownersGood typeGood valueGood lowS
  exact ⟨rA, read, plain, by rw [decls]; simp⟩

/-- **A compiled axiom's record reads as quotient Source's unit renamed**, from every state. -/
theorem axiom_unit_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {P : KeyScope .source} {v : Ix.AxiomVal} (nodup : v.cnst.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.axiomInfo v)) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey v.cnst.name)).map f))
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext v.cnst.name context).2
      (fun _ => none) names) v.cnst.type)
    (agree : ∀ n k, GraphWalk.Refs n v.cnst.type → names n k → sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    (sameHint : cx.hint (.member output.blockAddr 0) = cx₁.hint (.member output.blockAddr 0))
    {cv0 : CVal .source} (conv : Ix.LeanIngress.convert (.axiom v) = .ok (.axiom cv0))
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (.axiom (quotientHeader ρ cv0)) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
        rA.decls = rS.decls.map (Declaration.mapKeys f) := by
  intro stA _
  have unfolded : Ix.LeanIngress.lower stS (.axiom (quotientHeader ρ cv0)) =
      .ok { decls := #[.axiomDecl (quotientHeader ρ cv0)] } := rfl
  rw [unfolded, Except.ok.injEq] at lowered
  subst lowered
  obtain ⟨rA, read, plain, decls⟩ := axiom_reads nodup context clean wire ran aligned external
    keyed scope agree refs sameKey sameHint conv stA
  exact ⟨rA, read, plain, by rw [decls]; simp⟩

/-- **A compiled quotient constant's record reads as quotient Source's unit renamed**, from
every state. -/
theorem quotient_unit_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {P : KeyScope .source} {v : Ix.QuotVal} (nodup : v.cnst.levelParams.toList.Nodup)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.quotInfo v)) context before = (.ok output, after))
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (keyed : cx₁.memberKey (.member output.blockAddr 0) =
      .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey v.cnst.name)).map f))
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext v.cnst.name context).2
      (fun _ => none) names) v.cnst.type)
    (agree : ∀ n k, GraphWalk.Refs n v.cnst.type → names n k → sourceNames ρ f n k)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    (sameKey : cx.memberKey (.member output.blockAddr 0) = cx₁.memberKey (.member output.blockAddr 0))
    (sameHint : cx.hint (.member output.blockAddr 0) = cx₁.hint (.member output.blockAddr 0))
    {kind : Ix.Kernel.QuotKind} {cv0 : CVal .source}
    (conv : Ix.LeanIngress.convert (.quot v) = .ok (.quot kind cv0))
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (.quot kind (quotientHeader ρ cv0)) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA output.blockAddr output.block = .ok rA ∧ StreamRename.Plain rA ∧
        rA.decls = rS.decls.map (Declaration.mapKeys f) := by
  intro stA _
  have unfolded : Ix.LeanIngress.lower stS (.quot kind (quotientHeader ρ cv0)) =
      .ok { decls := #[.quotDecl kind (quotientHeader ρ cv0)] } := rfl
  rw [unfolded, Except.ok.injEq] at lowered
  subst lowered
  obtain ⟨rA, read, plain, decls⟩ := quotient_reads nodup context clean wire ran aligned
    external keyed scope agree refs sameKey sameHint conv stA
  exact ⟨rA, read, plain, by rw [decls]; simp⟩

end Definition

/--
info: 'Ix.Cert.RecordReadings.definition_unit_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms definition_unit_reads

/--
info: 'Ix.Cert.RecordReadings.axiom_unit_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms axiom_unit_reads

/--
info: 'Ix.Cert.RecordReadings.quotient_unit_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quotient_unit_reads

end Ix.Cert.RecordReadings
