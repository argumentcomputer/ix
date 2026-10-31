import Ix.Cert.TraceSegments
import Ix.Cert.DefinitionPremises
import Ix.CompileCert.CanonUnivScope
import Ix.Cert.NoCtor
import Ix.Cert.FamilyGroups
import Ix.Cert.CheckedConsts

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
  equal names cannot (`pinned_quot_nodup`).
* `axiom_noSelf`, `quotient_noSelf` (`HeaderNeeds.noSelf`): a kept axiom's or quotient constant's
  type names no constant by its own name. The checker's front door accepts an axiom only in an
  environment without it that holds every constant of its type (`CheckedConsts`), and installs
  the pinned records only when they match pins whose types do not name them.
* `inductive_noCtor` (`InductiveNeeds.noCtor`): no constructor of a kept inductive group occurs in
  its types or its constructors' types, for any number of types: the checker's shape guard on
  the group's `indDecl` (`Semantics.checkDecl_noCtor`), back through the renaming and the
  canonical levels.
* `inductive_shape` (`InductiveNeeds.hcsize`, `positions`): a lowered inductive group has one
  constructor list per type, each constructor at its position, as `inductiveGroup` reads them
  off the block (`FamilyGroups.inductiveGroup_shape`).
* `inductive_nodup` (`InductiveNeeds.nodup`, and `recLevels` with `recLevels_of`): a kept inductive
  group's first type and its recursors have distinct level parameters. The checker installs the
  group's `indDecl` as a pinned block, whose members match the pins canonically (a pin's member
  with two parameters has a canonical type that mentions the second, which a term numbered under
  two equal names cannot), or through its modeled or native route, which checks every type
  former's and recursor's level positions distinct (`member_names_nodup`).
* `family_levels` (`InductiveNeeds.lpsEq`, `ctorLps`, and `recLevels`' sharing): a lowered
  inductive group's types and constructors have its first type's level-parameter names, and its
  recursors one list, under the compile-report check `FamilyLevelParams` (quotient Source numbers
  each constant by its own list and cannot see the names). -/

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

theorem canonLevel_defined {m : LevelParam → LevelParam} {ps qs : List LevelParam}
    (hm : ∀ p, ps.contains p = true → qs.contains (m p) = true) :
    ∀ {l : Ix.Kernel.Level}, l.allParamsDefined ps = true → (Ix.Kernel.canonLevel m l).allParamsDefined qs = true
  | .zero, _ => rfl
  | .succ l, h => canonLevel_defined hm (l := l) h
  | .max _ _, h => by
    simp only [Ix.Kernel.canonLevel, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨canonLevel_defined hm h.1, canonLevel_defined hm h.2⟩
  | .imax _ _, h => by
    simp only [Ix.Kernel.canonLevel, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨canonLevel_defined hm h.1, canonLevel_defined hm h.2⟩
  | .param p, h => hm p h

/-- **The pins' canonical form keeps a term's level parameters among `qs`** when its renaming
maps `ps` into `qs`. -/
theorem canonExpr_defined {md : Ix.Kernel.Mode} {m : LevelParam → LevelParam} {ps qs : List LevelParam}
    (hm : ∀ p, ps.contains p = true → qs.contains (m p) = true) :
    ∀ {e : Ix.Kernel.Expr md}, e.allLevelParamsDefined ps = true → (canonExpr m e).allLevelParamsDefined qs = true
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
    exact ⟨⟨canonExpr_defined hm h.1.1, canonExpr_defined hm h.1.2⟩, never_defined qs⟩
  | .forallE t b _, h => by
    simp only [canonExpr, Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨⟨canonExpr_defined hm h.1.1, canonExpr_defined hm h.1.2⟩, never_defined qs⟩
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
      refine canonExpr_defined (ps := [0, 2]) ?_ (mapLevels_defined (fun l hl => canonLevelIn_defined ?_ hl) ?_)
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

/-! ## Axioms and quotient constants: no self-reference

The checker installs an axiom through its front door, whose environment does not hold the axiom
and holds every constant of its type (`CheckedConsts.constantValRun_noSelf`), or compares the
pinned quotient soundness record with its pin; it installs a quotient constant only when it
matches its pin. No pin's type names the pin. So a kept axiom's or quotient constant's type
names no constant by its own name (`axiom_noSelf`, `quotient_noSelf`). -/

section NoSelf

open Ix.LeanIngress (Numbering ingressExpr ingressKey quotKindOf)
open Ix.Cert.CheckedConsts (ConstsAll constsAll_of_mentions constsAll_canonExpr)

/-- No quotient pin's canonical type names the pin. -/
theorem quotPin_noSelf (k : Ix.Kernel.QuotKind) :
    (canonExpr (canonNameMap ((BasisKind.quotK.decls (md := .source)).getD k.slot
        (.axiomInfo default)).toConstantVal.levelParams)
      ((BasisKind.quotK.decls (md := .source)).getD k.slot (.axiomInfo default)).toConstantVal.type).mentionsConst
      ((BasisKind.quotK.decls (md := .source)).getD k.slot (.axiomInfo default)).toConstantVal.name = false := by
  cases k <;> decide

/-- The pinned quotient soundness axiom's canonical type does not name it. -/
theorem quotSoundPin_noSelf :
    (Ix.Kernel.ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default) : Ix.Kernel.ConstantInfo .source)
      ).toConstantVal.type.mentionsConst
      quotSoundName = false := by
  decide

/-- **An accepted axiom's type names no constant by the axiom's name**: the front door's
environment does not hold it and holds every constant of its type, or it is the pinned
quotient soundness record, which matches its pin canonically. -/
theorem accepted_axiom_noSelf {μ : CheckMode} {ev : Evidences .source} {ds : List (Declaration .source)}
    {env : Env .source} (h : Cached.AcceptsRef μ ev ds env) {cv : Ix.Kernel.ConstantVal .source}
    (hd : .axiomDecl cv ∈ ds) : ConstsAll (· ≠ cv.name) cv.type := by
  obtain ⟨F, hF⟩ := h
  unfold checkDeclsPure at hF
  obtain ⟨e, e', he⟩ := DefinitionPremises.foldlM_steps _ ds _ env hF _ hd
  by_cases hq : cv.name = quotSoundName
  · simp only [checkDecl, hq, ↓reduceIte] at he
    split at he
    · rename_i hc
      have hc' := of_decide_eq_true hc
      have hty : canonExpr (canonNameMap cv.levelParams) cv.type =
          (Ix.Kernel.ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default))).toConstantVal.type :=
        congrArg (fun c => c.toConstantVal.type) hc'
      have hpin := quotSoundPin_noSelf
      rw [← hty] at hpin
      rw [hq]
      exact (constsAll_canonExpr _).mp (constsAll_of_mentions hpin)
    · cases he
  · have run := Semantics.checkDeclRun_ofEnvFactsE he
    rcases run with ⟨hn, -⟩ | ⟨type', hcv, -⟩
    · exact absurd hn hq
    · exact CheckedConsts.constantValRun_noSelf hcv

/-- **A quotient header whose type names no constant by its key comes from a source type that
names no constant by its name.** -/
theorem noSelf_of_header {ρ : FiberMap} {σ : Numbering} {name : Ix.Name} {e : Ix.Expr}
    {t' : Ix.Kernel.Expr .source} (ht' : ingressExpr σ.pos e = .ok t')
    (h : ConstsAll (· ≠ (RecordReadings.quotientHeader ρ ⟨ingressKey name, σ.params, t'⟩).name)
      (RecordReadings.quotientHeader ρ ⟨ingressKey name, σ.params, t'⟩).type) :
    Ix.CompileCert.ExpressionState.ConstsSatisfy (fun m => m ≠ name) e := by
  simp only [RecordReadings.quotientHeader_eq, CheckedConsts.constsAll_mapLevels,
    CheckedConsts.constsAll_substKeys] at h
  exact Ix.CompileCert.ExpressionState.constsSatisfy_mono (fun n hn same => hn (by rw [same]))
    _ ((CheckedConsts.ingress_constsAll ht').mp h)

/-- **A kept axiom's type names no constant by its name** (`HeaderNeeds.noSelf` for axioms),
when the prepared stream is accepted. -/
theorem axiom_noSelf {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {v : Ix.AxiomVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source} (low : LoweredAt g ρ hints start ls rs ℓ y (.axiom v) c stS raw rd) :
    rd = raw → Ix.CompileCert.ExpressionState.ConstsSatisfy (fun m => m ≠ v.cnst.name) v.cnst.type := by
  intro e
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨t', -, ht', rfl⟩ := RecordReadings.convert_axiom hconv
  have unfolded : Ix.LeanIngress.lower stS (((Converted.axiom
      ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩).withHints hints).quotient ρ) =
      .ok { decls := #[.axiomDecl (RecordReadings.quotientHeader ρ
        ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩)] } := rfl
  have hraw := Except.ok.inj (unfolded.symm.trans hl)
  subst e
  have hmem := kept_mem hflat hds hr (d := .axiomDecl (RecordReadings.quotientHeader ρ
    ⟨ingressKey v.cnst.name, (Numbering.mk v.cnst.levelParams false).params, t'⟩)) (by rw [← hraw]; simp)
  exact noSelf_of_header ht' (accepted_axiom_noSelf acc hmem)

/-- **A kept quotient constant's type names no constant by its name** (`HeaderNeeds.noSelf` for
quotient constants), when the prepared stream is accepted: the checker installs it only when it
matches its pin canonically, which keeps its name and its type's constants. -/
theorem quotient_noSelf {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {v : Ix.QuotVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source} (low : LoweredAt g ρ hints start ls rs ℓ y (.quot v) c stS raw rd) :
    rd = raw → Ix.CompileCert.ExpressionState.ConstsSatisfy (fun m => m ≠ v.cnst.name) v.cnst.type := by
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
    refine noSelf_of_header (ρ := ρ) ht' ?_
    unfold quotPinHit ConstantVal.canonEq at hpin
    have hc := of_decide_eq_true hpin
    have hname := congrArg Ix.Kernel.ConstantVal.name hc
    have hty := congrArg Ix.Kernel.ConstantVal.type hc
    simp only [Ix.Kernel.ConstantVal.canon] at hname hty
    have hself := quotPin_noSelf (quotKindOf v.kind)
    rw [← hty, ← hname] at hself
    exact (constsAll_canonExpr _).mp (constsAll_of_mentions hself)
  · cases he

end NoSelf

/-! ## Inductive groups: no constructor in the family's types -/

/-- Renaming keys keeps a mentioned key, renamed. -/
theorem mentionsConst_substKeys (ρ : FiberMap) (k : Ix.Kernel.Key .source) :
    ∀ e : Ix.Kernel.Expr .source, e.mentionsConst k = true →
      (Ix.LeanIngress.Expr.substKeys ρ e).mentionsConst (Ix.LeanIngress.Key.subst ρ k) = true := by
  intro e
  induction e with
  | bvar => intro h; cases h
  | fvar _ t ih => exact ih
  | sort => intro h; cases h
  | const n _ =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, beq_iff_eq] at h ⊢
    rw [h]
  | app a b iha ihb =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.imp iha ihb
  | lam t b _ iht ihb =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.imp iht ihb
  | forallE t b _ iht ihb =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.imp iht ihb
  | letE t v b _ iht ihv ihb =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.imp (fun h' => h'.imp iht ihv) ihb
  | lit => intro h; cases h
  | proj s _ e ih =>
    intro h
    simp only [Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mentionsConst, Bool.or_eq_true, beq_iff_eq] at h ⊢
    exact h.imp (fun hs => by rw [hs]) ih

/-- **No constructor of a kept inductive group occurs in its types or its constructors' types**
(`InductiveNeeds.noCtor`), when the prepared stream is accepted: the group lowers to an
`indDecl` whose formers and constructors carry its members' types renamed to representatives
with canonical levels, and the checker's shape guard (`Semantics.checkDecl_noCtor`) refuses a
block one of whose constructor keys occurs in a former's or constructor's type. A constructor's
Lean name in a source type would give its renamed key there. -/
theorem inductive_noCtor {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source}
    (low : LoweredAt g ρ hints start ls rs ℓ y (.inductive types ctors recs) c stS raw rd) (kept : rd = raw)
    (hcsize : ctors.size = types.size) :
    ∀ i ∈ Ix.Cert.InductiveCompile.indsOf types ctors, ∀ e ∈ BlockEmission.memberSources (.indc i),
      Ix.CompileCert.ExpressionState.ConstsSatisfy (fun n =>
        ∀ i' ∈ Ix.Cert.InductiveCompile.indsOf types ctors, ∀ c ∈ i'.ctors.toList,
        n ≠ c.cnst.name) e := by
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨rb, rfl, typeEntries, ctorEntries⟩ := NoCtor.convertInductive_entries types ctors recs c hconv
  have hl' : lowerInductive stS (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)) =
      .ok raw := hl
  have hdecl := NoCtor.lowerInductive_decl hl'
  generalize NoCtor.recInfosOf _ = recInfos at hdecl
  subst kept
  have hmem := kept_mem hflat hds hr (Array.mem_toList_iff.mpr hdecl)
  obtain ⟨F, e₀, e₂, checked⟩ := NoCtor.acceptsRef_decl acc hmem
  -- an entry of the block read, renamed and with canonical levels
  let canonOf (entry : CVal .source × Nat × Nat) : CVal .source × Nat × Nat :=
    ((Ix.LeanIngress.canonValM (Ix.LeanIngress.ConstantVal.substKeys ρ entry.1)).run' {}, entry.2.1, entry.2.2)
  have canonOf_eq : ∀ entry : CVal .source × Nat × Nat, (canonOf entry).1 =
      ⟨Ix.LeanIngress.Key.subst ρ entry.1.name, entry.1.levelParams,
        Ix.LeanIngress.mapLevels (Ix.LeanIngress.canonLevelIn entry.1.levelParams)
          (Ix.LeanIngress.Expr.substKeys ρ entry.1.type)⟩ := by
    intro entry
    simp only [canonOf, RecordReadings.canonValM_run, Ix.LeanIngress.ConstantVal.substKeys]
  have typeIn : ∀ entry ∈ rb.types.toList, canonOf entry ∈
      (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)).types.toList := by
    intro entry h
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.map_map,
      List.mem_map]
    exact ⟨entry, h, rfl⟩
  have ctorIn : ∀ entry ∈ rb.ctors.toList, canonOf entry ∈
      (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)).ctors.toList := by
    intro entry h
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.map_map,
      List.mem_map]
    exact ⟨entry, h, rfl⟩
  -- every constructor's renamed key is a constructor name of the checked block
  have keyIn : ∀ cs ∈ ctors.toList, ∀ ct ∈ cs.toList,
      Ix.LeanIngress.Key.subst ρ (Ix.LeanIngress.ingressKey ct.cnst.name) ∈ Ix.Kernel.indCtorNames
        (NoCtor.blockOf (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)) recInfos) := by
    intro cs hcs ct hct
    obtain ⟨entry, entryIn, named, -⟩ := ctorEntries cs hcs ct hct
    unfold Ix.Kernel.indCtorNames
    refine List.mem_filterMap.mpr ⟨.ctorInfo (canonOf entry).1 entry.2.1 entry.2.2,
      NoCtor.mem_blockOf_ctor (ctorIn entry entryIn), ?_⟩
    simp only [canonOf_eq, named]
  -- a former's or constructor's type mentions no constructor key
  have absent : ∀ entry, (entry ∈ rb.types.toList ∨ entry ∈ rb.ctors.toList) →
      ∀ cs ∈ ctors.toList, ∀ ct ∈ cs.toList,
        entry.1.type.mentionsConst (Ix.LeanIngress.ingressKey ct.cnst.name) = false := by
    intro entry entryIn cs hcs ct hct
    have hno := Ix.Kernel.Semantics.checkDecl_noCtor (cv := (canonOf entry).1) checked (keyIn cs hcs ct hct) (by
      rcases entryIn with h | h
      · exact .inl ⟨{}, NoCtor.mem_blockOf_type (typeIn entry h)⟩
      · exact .inr ⟨entry.2.1, entry.2.2, NoCtor.mem_blockOf_ctor (ctorIn entry h)⟩)
    rw [canonOf_eq] at hno
    simp only [NoCtor.mentionsConst_mapLevels] at hno
    cases hm : entry.1.type.mentionsConst (Ix.LeanIngress.ingressKey ct.cnst.name) with
    | false => rfl
    | true => rw [mentionsConst_substKeys ρ _ _ hm] at hno; cases hno
  -- the constructors of the group, together
  have allCtors : ∀ i' ∈ Ix.Cert.InductiveCompile.indsOf types ctors, ∀ ct ∈ i'.ctors.toList,
      ∃ cs ∈ ctors.toList, ct ∈ cs.toList := by
    intro i' hi' ct hct
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi'
    rw [Ix.Cert.InductiveCompile.indsOf_getElem hcsize hk] at hct
    exact ⟨_, Array.getElem_mem_toList _, hct⟩
  have hC : ∀ ct ∈ ctors.flatten.toList, ∃ cs ∈ ctors.toList, ct ∈ cs.toList := by
    intro ct h
    simp only [Array.toList_flatten, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨cs, hcs, rfl⟩, hct⟩ := h
    exact ⟨cs, hcs, hct⟩
  have hC' : ∀ cs ∈ ctors.toList, ∀ ct ∈ cs.toList, ct ∈ ctors.flatten.toList := by
    intro cs hcs ct hct
    simp only [Array.toList_flatten, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨cs, hcs, rfl⟩, hct⟩
  have conclude : ∀ (item : Ix.LeanIngress.Numbering × Ix.Expr) (entry : CVal .source × Nat × Nat),
      (entry ∈ rb.types.toList ∨ entry ∈ rb.ctors.toList) →
      Ix.CompileCert.SourceConstructorPositions.Converts item entry.1.type →
      Ix.CompileCert.ExpressionState.ConstsSatisfy (fun n => ∀ i' ∈ Ix.Cert.InductiveCompile.indsOf types ctors,
        ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) item.2 := by
    intro item entry entryIn ⟨τ, conv⟩
    have h := NoCtor.noCtorIn_of_ingress (C := ctors.flatten) conv (fun ct hct => by
      obtain ⟨cs, hcs, hct'⟩ := hC ct hct
      exact absent entry entryIn cs hcs ct hct')
    exact Ix.CompileCert.ExpressionState.constsSatisfy_mono (fun name hn i' hi' ct hct => by
      obtain ⟨cs, hcs, hct'⟩ := allCtors i' hi' ct hct
      exact hn ct (hC' cs hcs ct hct')) _ h
  intro i hi e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  rw [Ix.Cert.InductiveCompile.indsOf_getElem hcsize hk] at he
  simp only [BlockEmission.memberSources, Ix.Cert.InductiveCompile.indOf, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨ct, hct, rfl⟩
  · obtain ⟨entry, entryIn, -, conv⟩ := typeEntries _ (Array.getElem_mem_toList _)
    exact conclude _ entry (.inl entryIn) conv
  · obtain ⟨entry, entryIn, -, conv⟩ := ctorEntries _ (Array.getElem_mem_toList _) ct hct
    exact conclude _ entry (.inr entryIn) conv

/-! ## Inductive groups: one constructor list per type, constructors at their positions -/

/-- **A lowered inductive group of quotient Source's graph has one constructor list per type,
each constructor declaring its position** (`InductiveNeeds.hcsize`, `positions`): the group is
`inductiveGroup`'s for a block of the closure (`FamilyGroups.inductive_origin`), which reads them
off the block or refuses it (`FamilyGroups.inductiveGroup_shape`). -/
theorem inductive_shape {ixe : Ixon.Env} {t : RoleTable} {hints : CName .source → Option ReducibilityHint}
    {sub : Ix.Environment} {ρ : FiberMap} {start : State .source} {ls : List Scheduled} {rs : List (Read .source)}
    {ℓ : Nat} {y : Scheduled} {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (ClosureLayout.quotientGraph ixe t hints sub) ρ hints start ls rs ℓ y
      (.inductive types ctors recs) c stS raw rd) :
    ctors.size = types.size ∧
      ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size), ctors[i][j].cidx = j := by
  have hmem : Ix.LeanIngress.Group.inductive types ctors recs ∈ Ix.LeanIngress.groupsOf sub (blocksOf sub) := by
    have hgroups : (ClosureLayout.quotientGraph ixe t hints sub).groups =
        Ix.LeanIngress.groupsOf sub (blocksOf sub) := ReaderUnits.graph_groups sub (blocksOf sub)
    rw [← hgroups]
    exact Array.mem_of_getElem? low.group
  obtain ⟨n, v, -, -, hg⟩ := FamilyGroups.inductive_origin hmem
  rcases FamilyGroups.inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨types', ctors', recs', e, -, hctors, -⟩
  · cases e
  cases e
  have hlen : types.toList.length = ctors.toList.length := InductiveCompile.forall₂_length hctors
  refine ⟨by simpa using hlen.symm, fun i hi j hj => ?_⟩
  have hiT : i < types.toList.length := by rw [hlen]; simpa using hi
  have hiC : i < ctors.toList.length := by simpa using hi
  have row := InductiveCompile.forall₂_getElem hctors i hiT hiC
  have hjC : j < ctors.toList[i].toList.length := by simpa using hj
  have hjV : j < types.toList[i].ctors.zipIdx.toList.length := by
    rw [InductiveCompile.forall₂_length row]; exact hjC
  obtain ⟨-, -, hidx⟩ := InductiveCompile.forall₂_getElem row j hjV hjC
  simp only [Array.getElem_toList] at hidx
  simpa [Array.toList_zipIdx, List.getElem_zipIdx] using hidx

/-! ## Inductive groups: distinct level parameters

The checker installs a lowered inductive group's `indDecl` either as one of the pinned blocks,
which it compares with the pin canonically member by member, or through its modeled or native
route, which checks each type former's and recursor's level positions distinct
(`ConstantValRun`, `checkConstantVal`). Either way the group's first type and its recursors have
distinct level-parameter names (`inductive_nodup`). -/

section Families

open Ix.LeanIngress (Numbering ingressExpr mapLevels canonLevelIn)

/-- **Distinct positions under a numbering are distinct names**, for any numbering. -/
theorem names_nodup {σ : Numbering} (h : LevelParam.nodup σ.params = true) : σ.names.toList.Nodup := by
  rw [DefinitionBlockReads.levelParam_nodup_iff] at h
  simp only [Numbering.params] at h
  exact List.Pairwise.of_map _ (fun a b hab e => hab (by rw [e])) h

/-- Under a numbering of two equal names, every position is among `[0, 2]`, or among `[1, 2]`
for a recursor's large numbering (whose first name is the elimination level `1`). -/
theorem pos_dup_any (a n : Ix.Name) (large : Bool) :
    (if large then [1, 2] else [0, 2]).contains ((Numbering.mk ⟨[a, a]⟩ large).pos n) = true := by
  unfold Numbering.pos
  cases h : (Numbering.mk ⟨[a, a]⟩ large).names.findIdx? (Ix.Name.beqRaw · n) with
  | none => cases large <;> rfl
  | some j =>
    cases j with
    | zero => cases large <;> rfl
    | succ i =>
      obtain ⟨hi, hp, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
      have hi' : i + 1 < 2 := hi
      obtain rfl : i = 0 := by omega
      exact absurd hp (hbefore 0 (by decide))

theorem params_dup (a : Ix.Name) (large : Bool) :
    (Numbering.mk ⟨[a, a]⟩ large).params = if large then [1, 1] else [0, 0] := by
  have hf : (Numbering.mk ⟨[a, a]⟩ large).names.findIdx? (Ix.Name.beqRaw · a) = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr
      ⟨(by decide : 0 < 2), Ix.Name.beqRaw_iff.mpr rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hpos : (Numbering.mk ⟨[a, a]⟩ large).pos a = if large then 1 else 0 := by
    unfold Numbering.pos
    rw [hf]
    cases large <;> rfl
  show [a, a].map (Numbering.mk ⟨[a, a]⟩ large).pos = _
  simp only [List.map_cons, List.map_nil, hpos]
  cases large <;> rfl

/-- **A term numbered under two equal names has its canonical form among `[0, 2]`**, under its
own numbering or a recursor's large one: the canonical levels keep its positions, and the pins'
renaming sends them there. -/
theorem dup_canon_defined (a : Ix.Name) (large : Bool) (ρ : FiberMap) {e : Ix.Expr}
    {t' : Ix.Kernel.Expr .source} (ht' : ingressExpr (Numbering.mk ⟨[a, a]⟩ large).pos e = .ok t') :
    (canonExpr (canonNameMap (Numbering.mk ⟨[a, a]⟩ large).params)
      (mapLevels (canonLevelIn (Numbering.mk ⟨[a, a]⟩ large).params)
        (Ix.LeanIngress.Expr.substKeys ρ t'))).allLevelParamsDefined [0, 2] = true := by
  have hdef := ingressExpr_defined (fun n => pos_dup_any a n large) ht'
  rw [← substKeys_defined ρ] at hdef
  rw [params_dup]
  cases large
  · refine canonExpr_defined (ps := [0, 2]) ?_
      (mapLevels_defined (fun l hl => canonLevelIn_defined ?_ hl) (by simpa using hdef))
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> decide
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> decide
  · refine canonExpr_defined (ps := [1, 2]) ?_
      (mapLevels_defined (fun l hl => canonLevelIn_defined ?_ hl) (by simpa using hdef))
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> decide
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> decide

/-- **The pinned blocks' members**: each has at most two level parameters, and one with two
(`Eq.rec`, `PUnit.rec`) has a canonical type that mentions the second. -/
theorem pin_members : ∀ k ∈ [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK],
    ∀ y ∈ (k.decls (md := .source)), y.toConstantVal.levelParams.length ≤ 1 ∨
      (y.toConstantVal.levelParams.length = 2 ∧
        (canonExpr (canonNameMap y.toConstantVal.levelParams) y.toConstantVal.type).allLevelParamsDefined
          [0, 2] = false) := by
  decide

/-- **A member of a pinned block, numbered under its names, has distinct names**: it matches a
pin's member canonically, so it has at most two names, and two equal names would put its
canonical type among `[0, 2]` (`dup_canon_defined`), where a pin's member with two names does
not lie (`pin_members`). -/
theorem pinned_member_nodup {block : List (Ix.Kernel.ConstantInfo .source)} {k : BasisKind}
    (hpin : basisPinHit block = some k) {ci : Ix.Kernel.ConstantInfo .source} (hci : ci ∈ block)
    (hnp : ∀ t, ci ≠ .projInfo t) {σ : Numbering} {ρ : FiberMap} {e : Ix.Expr}
    {t' : Ix.Kernel.Expr .source} (ht' : ingressExpr σ.pos e = .ok t')
    (hlps : ci.toConstantVal.levelParams = σ.params)
    (hty : ci.toConstantVal.type = mapLevels (canonLevelIn σ.params) (Ix.LeanIngress.Expr.substKeys ρ t')) :
    σ.names.toList.Nodup := by
  unfold basisPinHit at hpin
  obtain ⟨hfind, hcanon⟩ := Option.filter_eq_some_iff.mp hpin
  have hk := List.mem_of_find?_eq_some hfind
  unfold canonEqList at hcanon
  have hmap := of_decide_eq_true hcanon
  obtain ⟨y, hy, hcy⟩ : ∃ y ∈ k.decls, Ix.Kernel.ConstantInfo.canon y = Ix.Kernel.ConstantInfo.canon ci := by
    have h : Ix.Kernel.ConstantInfo.canon ci ∈ k.decls.map Ix.Kernel.ConstantInfo.canon :=
      hmap ▸ List.mem_map_of_mem hci
    exact List.mem_map.mp h
  have hynp : ∀ t, y ≠ .projInfo t := by
    rintro t rfl
    apply hnp t
    cases ci <;> simp_all [Ix.Kernel.ConstantInfo.canon]
  have hcv := congrArg Ix.Kernel.ConstantInfo.toConstantVal hcy
  rw [Ix.Kernel.ConstantInfo.canon_toConstantVal hynp, Ix.Kernel.ConstantInfo.canon_toConstantVal hnp] at hcv
  have hlen : y.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length := by
    have h := congrArg (fun c => c.levelParams.length) hcv
    simpa [Ix.Kernel.ConstantVal.canon] using h
  have htype : canonExpr (canonNameMap y.toConstantVal.levelParams) y.toConstantVal.type =
      canonExpr (canonNameMap ci.toConstantVal.levelParams) ci.toConstantVal.type :=
    congrArg Ix.Kernel.ConstantVal.type hcv
  have hsize : σ.names.toList.length = y.toConstantVal.levelParams.length := by
    rw [hlen, hlps]
    simp [Numbering.params]
  have hpm := pin_members k hk y hy
  obtain ⟨⟨l⟩, large⟩ := σ
  change l.length = _ at hsize
  show l.Nodup
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact List.nodup_nil
  · simp
  · refine List.nodup_cons.mpr ⟨fun hab => ?_, by simp⟩
    have hab' : a = b := List.mem_singleton.mp hab
    subst hab'
    rcases hpm with h1 | ⟨-, hmention⟩
    · simp at hsize
      omega
    · have hd := dup_canon_defined a large ρ ht'
      rw [← hty, ← hlps, ← htype, hmention] at hd
      cases hd
  · rcases hpm with h1 | ⟨h2, -⟩ <;> simp at hsize <;> omega

/-- A block the native route recognises is its former, then constructors closed by its
recursor. -/
theorem nativeShape?_block {nP : Nat} {block : List (Ix.Kernel.ConstantInfo .source)}
    {s : Ix.Kernel.InductiveShape .source}
    (hs : nativeShape? nP block = some s) :
    ∃ caps rest cs mI rP rules, block = .indInfo s.cvT caps :: rest ∧
      sumSplit rest = some (cs, s.cvR, mI, rP, rules) := by
  unfold nativeShape? at hs
  split at hs
  · rename_i cvT caps rest
    split at hs
    · rename_i cs cvR mI rP rules hsplit
      dsimp only at hs
      split at hs
      · cases hs
      · split at hs
        · have key : s.cvT = cvT ∧ s.cvR = cvR := by
            split at hs <;> (simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl⟩)
          obtain ⟨k1, k2⟩ := key
          exact ⟨caps, rest, cs, mI, rP, rules, by rw [k1], by rw [k2, hsplit]⟩
        · cases hs
    · cases hs
  · cases hs

/-- The modeled route's member fold checks each member's level positions distinct. -/
theorem indMembers_nodup {μ : CheckMode} {F : Nat} {names : List (Ix.Kernel.Key .source)}
    {caps : Ix.Kernel.IndCaps .source} :
    ∀ {env : Env .source} {l : List (Ix.Kernel.ConstantInfo .source)} {env₂ : Env .source},
      Semantics.IndMembersRun μ F names caps env l env₂ →
      ∀ ci ∈ l, LevelParam.nodup ci.toConstantVal.levelParams = true
  | _, [], _, _, _, hci => nomatch hci
  | _, c :: rest, _, h, ci, hci => by
    obtain ⟨cvA, ⟨type', run, -⟩, hrest⟩ := h
    rcases List.mem_cons.mp hci with rfl | hin
    · exact run.2.2.2.1
    · cases c with
      | indInfo => exact indMembers_nodup hrest ci hin
      | ctorInfo => exact indMembers_nodup hrest ci hin
      | _ => exact (hrest : False).elim

/-- The modeled route's recursor provisioning checks each recursor's level positions distinct. -/
theorem provisionRecs_nodup {μ : CheckMode} {F : Nat} {names : List (Ix.Kernel.Key .source)} :
    ∀ {envAcc : Env .source} {l : List (Ix.Kernel.ConstantInfo .source)} {envSelf : Env .source}
      {checked : List (Ix.Kernel.ConstantVal .source × Nat × Nat × List (Ix.Kernel.RecRule .source))},
      Semantics.ProvisionRecsRun μ F names envAcc l envSelf checked →
      ∀ ci ∈ l, LevelParam.nodup ci.toConstantVal.levelParams = true
  | _, [], _, _, _, _, hci => nomatch hci
  | _, c :: rest, _, _, h, ci, hci => by
    obtain ⟨cvA, mI, rP, rules, rest', -, ⟨type', run, -⟩, hrest, -⟩ := h
    rcases List.mem_cons.mp hci with rfl | hci
    · exact run.2.2.2.1
    · exact provisionRecs_nodup hrest ci hci

/-- **The modeled route checks every member's level positions distinct.** -/
theorem declIndRun_nodup {μ : CheckMode} {F : Nat} {env env₂ : Env .source}
    {block : List (Ix.Kernel.ConstantInfo .source)}
    (h : Semantics.DeclIndRun μ F env block env₂) :
    ∀ ci ∈ block, LevelParam.nodup ci.toConstantVal.levelParams = true := by
  intro ci hci
  dsimp only [Semantics.DeclIndRun] at h
  obtain ⟨hsplit, h⟩ := h
  rw [hsplit] at hci
  rcases h with ⟨_, _, _, _, _, -, -, _, _, members, recsRun, -⟩ | ⟨-, _, members, recsRun⟩
  all_goals
    rcases List.mem_append.mp hci with hm | hm
    · exact indMembers_nodup members ci hm
    · rcases recsRun with ⟨hnil, -⟩ | ⟨-, -, _, _, prov, -⟩
      · rw [hnil] at hm
        cases hm
      · exact provisionRecs_nodup prov ci hm

/-- **An installed inductive block that is not pinned has its type formers' and recursors' level
positions distinct**: the modeled route checks every member's, the native route its one
former's and its one recursor's. -/
theorem unpinned_nodup {μ : CheckMode} {F : Nat} {ev : Evidences .source} {env env₂ : Env .source}
    {block : List (Ix.Kernel.ConstantInfo .source)} {nP : Nat}
    (h : checkDecl μ (fueledOps μ F) ev env (.indDecl block nP) = .ok env₂) (hpin : basisPinHit block = none)
    {ci : Ix.Kernel.ConstantInfo .source} (hci : ci ∈ block)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨ ∃ cv mI rP rules, ci = .recInfo cv mI rP rules) :
    LevelParam.nodup ci.toConstantVal.levelParams = true := by
  have run := Semantics.checkDeclRun_ofEnvFactsE h
  simp only [Semantics.DeclRun, hpin] at run
  unfold Semantics.DeclIndRunDispatch at run
  cases hnp : nativeParts? nP block with
  | none =>
    rw [hnp] at run
    exact declIndRun_nodup run ci hci
  | some p₀ =>
    rw [hnp] at run
    obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest, isorts,
      hind, hp, -, -, -, -, -, -, -, -, hrec, -⟩ := run
    obtain ⟨cvT, s, -, hlpsT, hccv, hp₁, -, -⟩ := checkSumInd_shape hind
    obtain ⟨cvRi, -, -, -, hccvR, -⟩ := checkNativeRec_shape hrec
    obtain ⟨hshape, -⟩ := nativeParts?_inv hnp
    obtain ⟨caps, rest, cs, mI, rP, rules, hblock, hsplit⟩ := nativeShape?_block hshape
    rw [hblock] at hci
    rcases List.mem_cons.mp hci with rfl | hci
    · show LevelParam.nodup p₀.cvT.levelParams = true
      rw [← hlpsT]
      exact (checkConstantVal_inv hccv).2.2.2.1
    · rcases SourceInstalls.sumSplit_cover hsplit ci hci with rfl | ⟨c, -, rfl⟩
      · have hR : p.cvR = p₀.cvR := by
          rw [hp, hp₁]
          rfl
        show LevelParam.nodup p₀.cvR.levelParams = true
        rw [← hR]
        exact (checkConstantVal_inv hccvR).2.2.2.1
      · rcases hkind with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h

/-- **A type former or recursor of an installed inductive block, numbered under its names, has
distinct names**, pinned or not. -/
theorem member_names_nodup {μ : CheckMode} {F : Nat} {ev : Evidences .source} {env env₂ : Env .source}
    {block : List (Ix.Kernel.ConstantInfo .source)} {nP : Nat}
    (h : checkDecl μ (fueledOps μ F) ev env (.indDecl block nP) = .ok env₂)
    {ci : Ix.Kernel.ConstantInfo .source} (hci : ci ∈ block)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨ ∃ cv mI rP rules, ci = .recInfo cv mI rP rules)
    {σ : Numbering} {ρ : FiberMap} {e : Ix.Expr} {t' : Ix.Kernel.Expr .source}
    (ht' : ingressExpr σ.pos e = .ok t') (hlps : ci.toConstantVal.levelParams = σ.params)
    (hty : ci.toConstantVal.type = mapLevels (canonLevelIn σ.params) (Ix.LeanIngress.Expr.substKeys ρ t')) :
    σ.names.toList.Nodup := by
  cases hpin : basisPinHit block with
  | some k =>
    have hnp : ∀ t, ci ≠ .projInfo t := by
      rintro t rfl
      rcases hkind with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    exact pinned_member_nodup hpin hci hnp ht' hlps hty
  | none =>
    have hn := unpinned_nodup h hpin hci hkind
    rw [hlps] at hn
    exact names_nodup hn

/-- `canonInfo` of a recursor: its constant in canonical levels, its rules in some form. -/
theorem canonInfo_rec (cv : Ix.Kernel.ConstantVal .source) (m p : Nat) (rules : List (Ix.Kernel.RecRule .source)) :
    ∃ rules', Ix.LeanIngress.canonInfo (.recInfo cv m p rules) =
      .recInfo ((Ix.LeanIngress.canonValM cv).run' {}) m p rules' :=
  ⟨_, rfl⟩

/-- **A kept inductive group's first type and its recursors have distinct level parameters**
(`InductiveNeeds.nodup`, and `recLevels`' distinctness), when the prepared stream is accepted:
the group lowers to an `indDecl` whose first former and recursors carry the group's types and
recursors under their numberings (`SourceConversion.convertInductive_exact`), renamed and with
canonical levels, and the checker installed it (`member_names_nodup`). -/
theorem inductive_nodup {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source}
    (low : LoweredAt g ρ hints start ls rs ℓ y (.inductive types ctors recs) c stS raw rd) (kept : rd = raw)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) :
    first.cnst.levelParams.toList.Nodup ∧ ∀ r ∈ recs.toList, r.cnst.levelParams.toList.Nodup := by
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨first', rb, hfirst', rfl, -, htypes, -, -, hrecs⟩ := SourceConversion.convertInductive_exact hconv
  rw [hfirst] at hfirst'
  cases hfirst'
  have hl' : lowerInductive stS (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)) =
      .ok raw := hl
  have hdecl := NoCtor.lowerInductive_decl hl'
  subst kept
  have hmem := kept_mem hflat hds hr (Array.mem_toList_iff.mpr hdecl)
  obtain ⟨F, e₀, e₂, checked⟩ := NoCtor.acceptsRef_decl acc hmem
  refine ⟨?_, ?_⟩
  · have hmemF : first ∈ types.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfirst)
    obtain ⟨⟨cv, nP, nI⟩, hentry, rel⟩ := Ix.CompileCert.SourceConstructorPositions.forall₂_mem htypes hmemF
    have hin := NoCtor.mem_blockOf_type
      (rb := Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb))
      (recInfos := NoCtor.recInfosOf (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb)))
      (entry := ((Ix.LeanIngress.canonValM (Ix.LeanIngress.ConstantVal.substKeys ρ cv)).run' {}, nP, nI)) (by
        simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, Array.toList_map,
          List.map_map, List.mem_map]
        exact ⟨_, hentry, rfl⟩)
    refine member_names_nodup (ρ := ρ) checked hin (.inl ⟨_, _, rfl⟩) rel.2.2.1 ?_ ?_
    · simp only [RecordReadings.canonValM_run, Ix.Kernel.ConstantInfo.toConstantVal,
        Ix.LeanIngress.ConstantVal.substKeys]
      exact rel.2.1
    · simp only [RecordReadings.canonValM_run, Ix.Kernel.ConstantInfo.toConstantVal,
        Ix.LeanIngress.ConstantVal.substKeys]
      rw [rel.2.1]
  · intro r hrmem
    obtain ⟨⟨cv, rc, rules⟩, hentry, rel⟩ := Ix.CompileCert.SourceConstructorPositions.forall₂_mem hrecs hrmem
    obtain ⟨rules', hcanon⟩ := canonInfo_rec (Ix.LeanIngress.ConstantVal.substKeys ρ cv) 0 0
      (rules.map (Ix.LeanIngress.RecRule.substKeys ρ))
    obtain ⟨mI, rP, hin⟩ := NoCtor.mem_blockOf_rec
      (rb := Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ rb))
      (entry := ((Ix.LeanIngress.canonValM (Ix.LeanIngress.ConstantVal.substKeys ρ cv)).run' {}, rc, rules')) (by
        simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, Array.toList_map,
          List.map_map, List.mem_map]
        refine ⟨_, hentry, ?_⟩
        simp only [Function.comp_apply, hcanon])
    refine member_names_nodup (ρ := ρ) checked hin (.inr ⟨_, _, _, _, rfl⟩) rel.2.2.1 ?_ ?_
    · simp only [RecordReadings.canonValM_run, Ix.Kernel.ConstantInfo.toConstantVal,
        Ix.LeanIngress.ConstantVal.substKeys]
      exact rel.2.1
    · simp only [RecordReadings.canonValM_run, Ix.Kernel.ConstantInfo.toConstantVal,
        Ix.LeanIngress.ConstantVal.substKeys]
      rw [rel.2.1]

/-- **The recursors share distinct level parameters** (`InductiveNeeds.recLevels`), given that
they share them. -/
theorem recLevels_of {recs : Array Ix.RecursorVal} (nodup : ∀ r ∈ recs.toList, r.cnst.levelParams.toList.Nodup)
    (share : ∀ r ∈ recs.toList, ∀ r' ∈ recs.toList, r.cnst.levelParams = r'.cnst.levelParams) :
    ∃ rlps : Array Ix.Name, (∀ r ∈ recs.toList, r.cnst.levelParams = rlps) ∧ rlps.toList.Nodup := by
  by_cases hne : recs.toList = []
  · exact ⟨#[], fun r hr => (by rw [hne] at hr; cases hr), by simp⟩
  · obtain ⟨r₀, h₀⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨r₀.cnst.levelParams, fun r hr => share r hr r₀ h₀, nodup r₀ h₀⟩

end Families

/-! ## Inductive groups: shared level-parameter names

Quotient Source numbers each constant of a family by its own list, so it cannot see whether a
family's members, constructors and recursors share names; the compile can (a constructor compiles
under its inductive's list). A compile-report check makes them shared (`FamilyLevelParams`), and a
lowered group's lists are then its first type's (`family_levels`). -/

/-- **A lowered inductive group shares its first type's level-parameter names**
(`InductiveNeeds.lpsEq`, `ctorLps`), **and its recursors share one list** (`recLevels`' sharing),
under the family check: the group's types are the inductives its head lists, its constructors
theirs, and its recursors those of its head's family (`FamilyGroups.inductiveGroup_shape`). -/
theorem family_levels {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) (flp : FamilyLevelParams env)
    {hints : CName .source → Option ReducibilityHint} {ρ : FiberMap} {start : State .source}
    {ls : List Scheduled} {rs : List (Read .source)} {ℓ : Nat} {y : Scheduled}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (ClosureLayout.quotientGraph ixe t hints sub) ρ hints start ls rs ℓ y
      (.inductive types ctors recs) c stS raw rd)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) :
    (∀ v ∈ types.toList, v.cnst.levelParams = first.cnst.levelParams) ∧
      (∀ cs ∈ ctors.toList, ∀ ct ∈ cs.toList, ct.cnst.levelParams = first.cnst.levelParams) ∧
      ∀ r ∈ recs.toList, ∀ r' ∈ recs.toList, r.cnst.levelParams = r'.cnst.levelParams := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmem : Ix.LeanIngress.Group.inductive types ctors recs ∈ Ix.LeanIngress.groupsOf sub (blocksOf sub) := by
    have hgroups : (ClosureLayout.quotientGraph ixe t hints sub).groups =
        Ix.LeanIngress.groupsOf sub (blocksOf sub) := ReaderUnits.graph_groups sub (blocksOf sub)
    rw [← hgroups]
    exact Array.mem_of_getElem? low.group
  obtain ⟨n, v, hnv, -, hg⟩ := FamilyGroups.inductive_origin hmem
  rcases FamilyGroups.inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨types', ctors', recs', e, htypes, hctors, hrecs⟩
  · cases e
  cases e
  have hnE : env.consts.get? n = some (.inductInfo v) := hcl.mem_env (SourceStoredNames.stored_get hnv)
  obtain ⟨famT, famR, -⟩ := flp
  -- every type is an inductive the head lists, stored
  have typeAt : ∀ w ∈ types.toList, ∃ m ∈ v.all, env.consts.get? m = some (.inductInfo w) := by
    intro w hw
    obtain ⟨m, hm, hget, -⟩ := ReaderUnits.forall₂_mem_right htypes w hw
    exact ⟨m, Array.mem_toList_iff.mp hm, hcl.mem_env hget⟩
  have typeLps : ∀ w ∈ types.toList, w.cnst.levelParams = v.cnst.levelParams := by
    intro w hw
    obtain ⟨m, hm, hget⟩ := typeAt w hw
    exact (famT n v hnE).1 m hm w hget
  have firstLps : first.cnst.levelParams = v.cnst.levelParams :=
    typeLps first (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfirst))
  refine ⟨fun w hw => (typeLps w hw).trans firstLps.symm, fun cs hcs ct hct => ?_, fun r hr r' hr' => ?_⟩
  · obtain ⟨w, hw, row⟩ := ReaderUnits.forall₂_mem_right hctors cs hcs
    obtain ⟨x, hx, hxget, -, -⟩ := ReaderUnits.forall₂_mem_right row ct hct
    obtain ⟨m, -, hwget⟩ := typeAt w hw
    have hxc : x.1 ∈ w.ctors :=
      Array.mem_of_getElem? (Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp hx))
    rw [(famT m w hwget).2 x.1 hxc ct (hcl.mem_env hxget), typeLps w hw, firstLps]
  · have cand : ∀ r ∈ recs.toList, ∃ k, env.consts.get? k = some (.recInfo r) ∧ r.all[0]? = some n := by
      intro r hr
      obtain ⟨k, hk, hall⟩ := FamilyGroups.recsTable_mem
        (SourceStoredNames.blockRecursors_mem hrecs r (Array.mem_toList_iff.mp hr))
      exact ⟨k, SourceStoredNames.stored_get (SourceStoredNames.stored_input P hk), hall⟩
    obtain ⟨k, hk, hall⟩ := cand r hr
    obtain ⟨k', hk', hall'⟩ := cand r' hr'
    exact famR k k' r r' n hk hk' hall hall'


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

/--
info: 'Ix.Cert.TraceSource.inductive_noCtor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_noCtor

/--
info: 'Ix.Cert.TraceSource.inductive_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_shape

/--
info: 'Ix.Cert.TraceSource.inductive_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_nodup

/--
info: 'Ix.Cert.TraceSource.family_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms family_levels

/--
info: 'Ix.Cert.TraceSource.axiom_noSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms axiom_noSelf

/--
info: 'Ix.Cert.TraceSource.quotient_noSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quotient_noSelf

end Ix.Cert.TraceSource
