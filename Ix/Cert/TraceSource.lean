import Ix.Cert.TraceSegments
import Ix.Cert.DefinitionPremises
import Ix.CompileCert.CanonUnivScope

/-! # Quotient Source's side of the trace's segments

`TraceSegments.TraceNeeds` collects what the trace's segments need. This module proves the parts
that come from quotient Source's acceptance of its prepared stream.

* `kept_mem`: every declaration the trace keeps is in the prepared stream, which the checker
  accepted.
* `kept_levels` (`TraceNeeds.levels`): so a kept definition, theorem or opaque has distinct
  level positions (`DefinitionPremises.accepted_nodup`).
* `accepted_axiom`: an accepted axiom has distinct level positions, or is the pinned quotient
  soundness axiom's record and has one level parameter (its canonical comparison with the pin).
* `axiom_nodup` (`HeaderNeeds.nodup` for axioms): a kept axiom's level parameters are distinct.
* `quotient_nodup` (`HeaderNeeds.nodup` for quotient constants): a kept quotient constant's
  level parameters are distinct. Its record matches its pin canonically; `Quot.lift`'s pin has
  two parameters and its canonical type mentions the second, which a term numbered under two
  equal names cannot (`pinned_quot_nodup`). -/

namespace Ix.Cert.TraceSource

open Ix.Kernel Ix.Kernel.Reader
open Ix.Cert.TraceSegments (LoweredAt)
open Ix.LeanIngress (Converted Graph FiberMap)
open Ix.Cert.SourcePrelude (Scheduled)

/-! ## Kept declarations are accepted -/

/-- **Every declaration quotient Source's trace keeps is in the prepared stream.** -/
theorem kept_mem {pre : Prelude .source} {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {ℓ : Nat} {r : Read .source} (hr : rs[ℓ]? = some r) {d : Declaration .source} (hd : d ∈ r.decls.toList) :
    d ∈ ds.toList := by
  have hmem : d ∈ decls := by
    rw [← Array.mem_toList_iff, hflat]
    exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hr, hd⟩
  rw [hds]
  exact Array.mem_toList_iff.mpr (Frontend.mem_preparePrelude hmem)

/-- **The trace's kept definitions, theorems and opaques have distinct level positions**, when
the prepared stream is accepted. -/
theorem kept_levels {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls) :
    ∀ (ℓ : Nat) (r : Read .source), rs[ℓ]? = some r → ∀ d ∈ r.decls.toList, DefinitionBlockReads.DeclNodup d :=
  fun _ _ hr d hd => DefinitionPremises.accepted_nodup acc d (kept_mem hflat hds hr hd)

/-! ## Axioms -/

/-- **An accepted axiom's level positions are distinct**, or it is the pinned quotient soundness
axiom's record, which the checker compares with the pin canonically, so it has the pin's one
level parameter. -/
theorem accepted_axiom {md : Mode} {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : Cached.AcceptsRef μ ev ds env) {cv : Ix.Kernel.ConstantVal md} (hd : .axiomDecl cv ∈ ds) :
    LevelParam.nodup cv.levelParams = true ∨ cv.levelParams.length = 1 := by
  obtain ⟨F, hF⟩ := h
  unfold checkDeclsPure at hF
  obtain ⟨e, e', he⟩ := DefinitionPremises.foldlM_steps _ ds _ env hF _ hd
  by_cases hq : cv.name = quotSoundName
  · right
    simp only [checkDecl, hq, ↓reduceIte] at he
    split at he
    · rename_i hc
      have hc' := of_decide_eq_true hc
      have hlp := congrArg (fun c => c.toConstantVal.levelParams.length) hc'
      simpa [Ix.Kernel.ConstantInfo.canon, Ix.Kernel.ConstantVal.canon, Ix.Kernel.quotBasis, Ix.Kernel.quotSoundRaw,
        Ix.Kernel.ConstantInfo.toConstantVal] using hlp
    · cases he
  · left
    have run := Semantics.checkDeclRun_ofEnvFactsE he
    rcases run with ⟨hn, -⟩ | ⟨type', hcv, -⟩
    · exact absurd hn hq
    · exact hcv.2.2.2.1

/-- **A kept axiom's level parameters are distinct**, when the prepared stream is accepted. -/
theorem axiom_nodup {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {v : Ix.AxiomVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source} (low : LoweredAt g ρ hints start ls rs ℓ y (.axiom v) c stS raw rd) :
    rd = raw → v.cnst.levelParams.toList.Nodup := by
  intro e
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨cv0, rfl, hlps⟩ : ∃ cv0 : CVal .source, c = .axiom cv0 ∧
      cv0.levelParams = (Ix.LeanIngress.Numbering.mk v.cnst.levelParams false).params := by
    obtain ⟨_, -, -, rfl⟩ := RecordReadings.convert_axiom hconv
    exact ⟨_, rfl, rfl⟩
  have unfolded : Ix.LeanIngress.lower stS (((Converted.axiom cv0).withHints hints).quotient ρ) =
      .ok { decls := #[.axiomDecl (RecordReadings.quotientHeader ρ cv0)] } := rfl
  have hraw := Except.ok.inj (unfolded.symm.trans hl)
  subst e
  have hmem := kept_mem hflat hds hr (d := .axiomDecl (RecordReadings.quotientHeader ρ cv0))
    (by rw [← hraw]; simp)
  rcases accepted_axiom acc hmem with h | h
  · rw [RecordReadings.quotientHeader_eq, hlps] at h
    exact DefinitionBlockReads.nodup_of_params h
  · rw [RecordReadings.quotientHeader_eq, hlps] at h
    generalize v.cnst.levelParams = lps at h ⊢
    have hlen : lps.toList.length = 1 := by simpa [Ix.LeanIngress.Numbering.params] using h
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx]
    simp

/-! ## Level positions of a converted term, and quotient constants

A term converted under a numbering mentions only the numbering's positions, and the
canonical forms keep a set of positions they map into itself. So a quotient record that
matches its pin has distinct level parameters (`pinned_quot_nodup`, `quotient_nodup`). -/

section Positions

open Ix.LeanIngress (Numbering ingressLevel ingressExpr ingressMData withContract mapLevels canonLevelIn idxIn
  ofIdxIn univOfLevel levelOfUniv ingressKey quotKindOf)

theorem never_defined (ps : List LevelParam) :
    Ix.Kernel.PropWhen.paramsDefined ps Ix.Kernel.PropWhen.never = true := rfl

/-- A level converted under `σ` has its parameters among `ps` when every position of `σ` is. -/
theorem ingressLevel_defined {σ : Ix.Name → LevelParam} {ps : List LevelParam}
    (hσ : ∀ n, ps.contains (σ n) = true) :
    ∀ {l : Ix.Level} {l' : Ix.Kernel.Level}, ingressLevel σ l = .ok l' → l'.allParamsDefined ps = true
  | .zero _, _, h => by cases h; rfl
  | .succ u _, _, h => by
    rw [ingressLevel] at h
    obtain ⟨u', hu, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    have := ingressLevel_defined hσ hu
    exact this
  | .max u v _, _, h => by
    rw [ingressLevel] at h
    obtain ⟨u', hu, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨v', hv, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨ingressLevel_defined hσ hu, ingressLevel_defined hσ hv⟩
  | .imax u v _, _, h => by
    rw [ingressLevel] at h
    obtain ⟨u', hu, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨v', hv, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨ingressLevel_defined hσ hu, ingressLevel_defined hσ hv⟩
  | .param n _, _, h => by
    cases h
    exact hσ n
  | .mvar n _, _, h => by simp [ingressLevel, throw, throwThe, MonadExceptOf.throw] at h

theorem ingressLevels_defined {σ : Ix.Name → LevelParam} {ps : List LevelParam}
    (hσ : ∀ n, ps.contains (σ n) = true) :
    ∀ {us : List Ix.Level} {ls : List Ix.Kernel.Level}, us.mapM (ingressLevel σ) = .ok ls →
      ls.all (Ix.Kernel.Level.allParamsDefined ps) = true
  | [], _, h => by cases h; rfl
  | u :: us, _, h => by
    rw [List.mapM_cons] at h
    obtain ⟨l, hl, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨ls, hls, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨ingressLevel_defined hσ hl, ingressLevels_defined hσ hls⟩

/-- A contract frame changes a binder's contract only. -/
theorem withContract_defined {ps : List LevelParam} {c : Ix.SemanticContract.Contract} {e : Ix.Expr}
    {x x' : Ix.Kernel.Expr .source} (h : withContract c e x = .ok x') :
    x'.allLevelParamsDefined ps = x.allLevelParamsDefined ps := by
  unfold withContract at h
  split at h <;> first | (cases h; rfl) | simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A term converted under `σ` has its level parameters among `ps`** when every position of
`σ` is. -/
theorem ingressExpr_defined {σ : Ix.Name → LevelParam} {ps : List LevelParam}
    (hσ : ∀ n, ps.contains (σ n) = true) :
    ∀ {e : Ix.Expr} {e' : Ix.Kernel.Expr .source}, ingressExpr σ e = .ok e' → e'.allLevelParamsDefined ps = true
  | .bvar _ _, _, h => by
    cases h
    simp [Ix.Kernel.Expr.allLevelParamsDefined]
  | .fvar _ _, _, h => by simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | .mvar _ _, _, h => by simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | .sort u _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨l, hl, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact ingressLevel_defined hσ hl
  | .const n us _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨ls, hls, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact ingressLevels_defined hσ hls
  | .app f a _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨f', hf, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨a', ha, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ingressExpr_defined hσ hf, ingressExpr_defined hσ ha⟩
  | .lam _ t b _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨t', ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨b', hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨ingressExpr_defined hσ ht, ingressExpr_defined hσ hb⟩, never_defined ps⟩
  | .forallE _ t b _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨t', ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨b', hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨ingressExpr_defined hσ ht, ingressExpr_defined hσ hb⟩, never_defined ps⟩
  | .letE _ t v b _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨t', ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨v', hv, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨b', hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨ingressExpr_defined hσ ht, ingressExpr_defined hσ hv⟩, ingressExpr_defined hσ hb⟩
  | .lit (.natVal _) _, _, h => by cases h; rfl
  | .lit (.strVal _) _, _, h => by cases h; rfl
  | .mdata d e _, _, h => by
    rw [Ix.LeanIngress.ingressExpr_mdata] at h
    unfold ingressMData at h
    split at h
    · obtain ⟨c, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨x, hx, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      rw [withContract_defined h]
      exact ingressExpr_defined hσ hx
    · exact ingressExpr_defined hσ h
  | .proj _ _ e _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨e', he, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    have := ingressExpr_defined hσ he
    exact this

/-- Renaming keys keeps a term's level parameters. -/
theorem substKeys_defined (ρ : FiberMap) (ps : List LevelParam) :
    ∀ e : Ix.Kernel.Expr .source,
      (Ix.LeanIngress.Expr.substKeys ρ e).allLevelParamsDefined ps = e.allLevelParamsDefined ps
  | .bvar _ => rfl
  | .fvar _ t => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps t]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps f,
      substKeys_defined ρ ps a]
  | .lam t b _ => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps t,
      substKeys_defined ρ ps b]
  | .forallE t b _ => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps t,
      substKeys_defined ρ ps b]
  | .letE t v b _ => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps t,
      substKeys_defined ρ ps v, substKeys_defined ρ ps b]
  | .lit _ => rfl
  | .proj _ _ e => by
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.allLevelParamsDefined, substKeys_defined ρ ps e]

/-- Mapping every level of a term by a map that keeps parameters among `ps` keeps the term's. -/
theorem mapLevels_defined {f : Ix.Kernel.Level → Ix.Kernel.Level} {ps : List LevelParam}
    (hf : ∀ l, l.allParamsDefined ps = true → (f l).allParamsDefined ps = true) :
    ∀ {e : Ix.Kernel.Expr .source}, e.allLevelParamsDefined ps = true → (mapLevels f e).allLevelParamsDefined ps = true
  | .bvar _, _ => rfl
  | .fvar _ t, h => mapLevels_defined hf (e := t) h
  | .sort u, h => hf u h
  | .const _ us, h => by
    simp only [mapLevels, Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true, List.mem_map] at h ⊢
    rintro _ ⟨l, hl, rfl⟩
    exact hf l (h l hl)
  | .app a b, h => by
    simp only [mapLevels, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨mapLevels_defined hf h.1, mapLevels_defined hf h.2⟩
  | .lam t b _, h => by
    simp only [mapLevels, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨mapLevels_defined hf h.1.1, mapLevels_defined hf h.1.2⟩, h.2⟩
  | .forallE t b _, h => by
    simp only [mapLevels, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨mapLevels_defined hf h.1.1, mapLevels_defined hf h.1.2⟩, h.2⟩
  | .letE t v b _, h => by
    simp only [mapLevels, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨mapLevels_defined hf h.1.1, mapLevels_defined hf h.1.2⟩, mapLevels_defined hf h.2⟩
  | .lit _, _ => rfl
  | .proj _ _ e, h => mapLevels_defined hf (e := e) h

theorem univOfLevel_occurs {ι : LevelParam → Nat} {ps : List LevelParam} :
    ∀ {l : Ix.Kernel.Level}, l.allParamsDefined ps = true →
      ∀ v, Ix.CompileCert.CanonUnivScope.Occurs v (univOfLevel ι l) →
      ∃ p, ps.contains p = true ∧ v = (ι p).toUInt64
  | .zero, _, _, h => h.elim
  | .succ l, hl, v, h => univOfLevel_occurs (l := l) hl v h
  | .max _ _, hl, v, h => by
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hl
    rcases h with h | h
    exacts [univOfLevel_occurs hl.1 v h, univOfLevel_occurs hl.2 v h]
  | .imax _ _, hl, v, h => by
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hl
    rcases h with h | h
    exacts [univOfLevel_occurs hl.1 v h, univOfLevel_occurs hl.2 v h]
  | .param p, hl, _, h => ⟨p, hl, h⟩

theorem levelOfUniv_defined {π : Nat → LevelParam} {ps : List LevelParam} :
    ∀ {u : Ixon.Univ}, (∀ v, Ix.CompileCert.CanonUnivScope.Occurs v u → ps.contains (π v.toNat) = true) →
      (levelOfUniv π u).allParamsDefined ps = true
  | .zero, _ => rfl
  | .succ u, h => levelOfUniv_defined (u := u) h
  | .max _ _, h => by
    simp only [levelOfUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨levelOfUniv_defined fun v o => h v (.inl o), levelOfUniv_defined fun v o => h v (.inr o)⟩
  | .imax _ _, h => by
    simp only [levelOfUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨levelOfUniv_defined fun v o => h v (.inl o), levelOfUniv_defined fun v o => h v (.inr o)⟩
  | .var i, h => h i rfl

/-- **The compiler's canonical form of a level keeps its parameters among `ps`**, when every
position of `ps` comes back from its index in `lps`. -/
theorem canonLevelIn_defined {lps ps : List LevelParam}
    (hrt : ∀ p, ps.contains p = true → ps.contains (ofIdxIn lps ((idxIn lps p).toUInt64.toNat)) = true)
    {l : Ix.Kernel.Level} (hl : l.allParamsDefined ps = true) : (canonLevelIn lps l).allParamsDefined ps = true := by
  unfold canonLevelIn
  apply levelOfUniv_defined
  intro v hv
  obtain ⟨p, hp, rfl⟩ := univOfLevel_occurs hl v (Ix.CompileCert.CanonUnivScope.canonUniv_occurs _ v hv)
  exact hrt p hp

theorem canonLevel_defined {m : LevelParam → LevelParam} {ps : List LevelParam}
    (hm : ∀ p, ps.contains p = true → ps.contains (m p) = true) :
    ∀ {l : Ix.Kernel.Level}, l.allParamsDefined ps = true → (Ix.Kernel.canonLevel m l).allParamsDefined ps = true
  | .zero, _ => rfl
  | .succ l, h => canonLevel_defined hm (l := l) h
  | .max _ _, h => by
    simp only [Ix.Kernel.canonLevel, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨canonLevel_defined hm h.1, canonLevel_defined hm h.2⟩
  | .imax _ _, h => by
    simp only [Ix.Kernel.canonLevel, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨canonLevel_defined hm h.1, canonLevel_defined hm h.2⟩
  | .param p, h => hm p h

/-- **The pins' canonical form keeps a term's level parameters among `ps`** when its renaming
maps `ps` into itself. -/
theorem canonExpr_defined {md : Ix.Kernel.Mode} {m : LevelParam → LevelParam} {ps : List LevelParam}
    (hm : ∀ p, ps.contains p = true → ps.contains (m p) = true) :
    ∀ {e : Ix.Kernel.Expr md}, e.allLevelParamsDefined ps = true → (canonExpr m e).allLevelParamsDefined ps = true
  | .bvar _, _ => rfl
  | .fvar _ t, h => canonExpr_defined hm (e := t) h
  | .sort _, h => canonLevel_defined hm h
  | .const _ us, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true, List.mem_map] at h ⊢
    rintro _ ⟨l, hl, rfl⟩
    exact canonLevel_defined hm (h l hl)
  | .app a b, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨canonExpr_defined hm h.1, canonExpr_defined hm h.2⟩
  | .lam t b _, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨canonExpr_defined hm h.1.1, canonExpr_defined hm h.1.2⟩, never_defined ps⟩
  | .forallE t b _, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨canonExpr_defined hm h.1.1, canonExpr_defined hm h.1.2⟩, never_defined ps⟩
  | .letE t v b _, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨canonExpr_defined hm h.1.1, canonExpr_defined hm h.1.2⟩, canonExpr_defined hm h.2⟩
  | .lit _, _ => rfl
  | .proj _ _ e, h => canonExpr_defined hm (e := e) h

/-- Under a numbering of two equal names, every position is `0` (the name) or `2` (any other). -/
theorem pos_dup (a n : Ix.Name) : [0, 2].contains ((Numbering.mk ⟨[a, a]⟩ false).pos n) = true := by
  unfold Numbering.pos
  split
  · rfl
  · rfl
  · rename_i i h
    obtain ⟨hi, hp, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
    have hi' : i + 1 < 2 := hi
    obtain rfl : i = 0 := by omega
    exact absurd hp (hbefore 0 (by decide))

theorem pos_self (a : Ix.Name) : (Numbering.mk ⟨[a, a]⟩ false).pos a = 0 := by
  have hf : (Numbering.mk ⟨[a, a]⟩ false).names.findIdx? (Ix.Name.beqRaw · a) = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr
      ⟨(by decide : 0 < 2), Ix.Name.beqRaw_iff.mpr rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  unfold Numbering.pos
  rw [hf]
  rfl

/-- The pinned `Quot.lift`'s canonical type mentions its second level parameter. -/
theorem quotLift_mentions :
    (canonExpr (canonNameMap ((BasisKind.quotK.decls (md := .source)).getD Ix.Kernel.QuotKind.lift.slot
        (.axiomInfo default)).toConstantVal.levelParams)
      ((BasisKind.quotK.decls (md := .source)).getD Ix.Kernel.QuotKind.lift.slot
        (.axiomInfo default)).toConstantVal.type).allLevelParamsDefined [0, 2] = false := by
  decide

/-- **A quotient record matching its pin has distinct level parameters**: the pins of one
parameter force one name, and `Quot.lift`'s two, whose canonical type mentions the second
position, force two distinct ones (two equal names number no constant at position 1). -/
theorem pinned_quot_nodup {k : Ix.Kernel.QuotKind} {names : Array Ix.Name} {ρ : FiberMap}
    {key : Ix.Kernel.Key .source} {e : Ix.Expr} {t' : Ix.Kernel.Expr .source}
    (ht' : ingressExpr (Numbering.mk names false).pos e = .ok t')
    (hpin : quotPinHit k (RecordReadings.quotientHeader ρ ⟨key, (Numbering.mk names false).params, t'⟩) = true) :
    names.toList.Nodup := by
  unfold quotPinHit ConstantVal.canonEq at hpin
  have hc := of_decide_eq_true hpin
  rw [RecordReadings.quotientHeader_eq] at hc
  have hlen : names.size = ((BasisKind.quotK.decls (md := .source)).getD k.slot
      (.axiomInfo default)).toConstantVal.levelParams.length := by
    have := congrArg (fun c => c.levelParams.length) hc
    simpa [Ix.Kernel.ConstantVal.canon, Numbering.params] using this
  have hty : canonExpr (canonNameMap (Numbering.mk names false).params)
      (mapLevels (canonLevelIn (Numbering.mk names false).params) (Ix.LeanIngress.Expr.substKeys ρ t')) =
      canonExpr (canonNameMap ((BasisKind.quotK.decls (md := .source)).getD k.slot
          (.axiomInfo default)).toConstantVal.levelParams)
        ((BasisKind.quotK.decls (md := .source)).getD k.slot (.axiomInfo default)).toConstantVal.type :=
    congrArg Ix.Kernel.ConstantVal.type hc
  obtain ⟨l⟩ := names
  cases k
  case lift =>
    simp [Ix.Kernel.QuotKind.slot, BasisKind.decls, quotBasis, quotLiftRaw,
      Ix.Kernel.ConstantInfo.toConstantVal] at hlen
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> try simp at hlen
    show [a, b].Nodup
    refine List.nodup_cons.mpr ⟨fun hab => ?_, by simp⟩
    have hab' : a = b := List.mem_singleton.mp hab
    subst hab'
    have hparams : (Numbering.mk ⟨[a, a]⟩ false).params = [0, 0] := by
      simp [Numbering.params, pos_self]
    have lhs : (canonExpr (canonNameMap (Numbering.mk ⟨[a, a]⟩ false).params)
        (mapLevels (canonLevelIn (Numbering.mk ⟨[a, a]⟩ false).params)
          (Ix.LeanIngress.Expr.substKeys ρ t'))).allLevelParamsDefined [0, 2] = true := by
      rw [hparams]
      refine canonExpr_defined ?_ (mapLevels_defined (fun l hl => canonLevelIn_defined ?_ hl) ?_)
      · intro p hp
        simp at hp
        rcases hp with rfl | rfl <;> decide
      · intro p hp
        simp at hp
        rcases hp with rfl | rfl <;> decide
      · rw [substKeys_defined]
        exact ingressExpr_defined (pos_dup a) ht'
    rw [hty, quotLift_mentions] at lhs
    simp at lhs
  all_goals
    simp [Ix.Kernel.QuotKind.slot, BasisKind.decls, quotBasis, quotRaw, quotMkRaw, quotIndRaw, quotSoundRaw,
      Ix.Kernel.ConstantInfo.toConstantVal] at hlen
    rcases l with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> try simp at hlen
    simp

/-- **A kept quotient constant's level parameters are distinct**, when the prepared stream is
accepted: the checker installs a quotient record only when it matches its pin
(`pinned_quot_nodup`). -/
theorem quotient_nodup {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {v : Ix.QuotVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source} (low : LoweredAt g ρ hints start ls rs ℓ y (.quot v) c stS raw rd) :
    rd = raw → v.cnst.levelParams.toList.Nodup := by
  intro e
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨t', ht', rfl⟩ := RecordReadings.convert_quot hconv
  have unfolded : Ix.LeanIngress.lower stS (((Converted.quot (quotKindOf v.kind)
      ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩).withHints
        hints).quotient ρ) =
      .ok { decls := #[.quotDecl (quotKindOf v.kind) (RecordReadings.quotientHeader ρ
        ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩)] } :=
    rfl
  have hraw := Except.ok.inj (unfolded.symm.trans hl)
  subst e
  have hmem := kept_mem hflat hds hr (d := .quotDecl (quotKindOf v.kind)
    (RecordReadings.quotientHeader ρ
      ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩))
    (by rw [← hraw]; simp)
  obtain ⟨F, hF⟩ := acc
  unfold checkDeclsPure at hF
  obtain ⟨e₀, e₁, he⟩ := DefinitionPremises.foldlM_steps _ _ _ _ hF _ hmem
  simp only [checkDecl] at he
  split at he
  · rename_i hpin
    exact pinned_quot_nodup ht' hpin
  · cases he

end Positions

/--
info: 'Ix.Cert.TraceSource.kept_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms kept_levels

/--
info: 'Ix.Cert.TraceSource.axiom_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms axiom_nodup

/--
info: 'Ix.Cert.TraceSource.quotient_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quotient_nodup

end Ix.Cert.TraceSource
