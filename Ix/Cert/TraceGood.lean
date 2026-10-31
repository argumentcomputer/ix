import Ix.Cert.TraceFold
import Ix.Cert.RecursorIndexFacts
import Ix.Cert.DefinitionEmission
import Ix.Cert.BlockRefs
import Ix.Cert.LeanOrder

/-! # Converted groups lie in the scope of representatives

`TraceSegments.TraceNeeds.good` asks that every group of quotient Source's graph that converts
has its quotient terms in the scope of representatives (`ConvGood (scope ixe t)`). The ingress
keys every name a Lean term references, a constant or a projection's structure, by the name's
ingress key (`ingress_good`), so a group's conversion is in the scope of input keys once every
name its terms reference is published (`TraceSegments.ConvGood` at `QIn`). Quotient Source then
renames onto representatives (`Key.subst_goodAt`) and puts levels in canonical form, which keeps
keys (`convGood_quotient`).

Every name a closure constant's terms reference is published: it is a key the input stores a
constant under, so the closure holds it (`IsClosure`), and every closure name is published. That
it is an input key comes from the compile, which compiled the constant: the compile reads its
sources, as `Related` terms, at any names that the compile's bindings and its block's members
satisfy (the emission theorems at `BlockRefs.addrCtx`), so every name the sources reference is a
member of the block or a binding of the fold's snapshot (`lone_names`, `block_names`), and both
are input keys (`GroupRuns.FoldBlock.bound_exact`, `fold_member_names`). A recursor's rules name
their constructors outside its terms; those are input keys by the report's family-name check
(`FamilyNamesStored`). -/

namespace Ix.Cert.TraceGood

-- Scope conversions in this proof module unfold the expanded role-key catalog.
set_option maxRecDepth 4096

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.LeanIngress (ingressExpr ingressKey ingressMData Group Converted FiberMap mapLevels
  canonLevelIn QIn QRepAt roleAtMap fiberAliasAt)
open Ix.Cert.ClosureLayout (quotientGraph)
open Ix.Cert.TraceSegments (ConvGood)
open Ix.Cert.GroupRuns (FoldBlock memberOf)

/-! ## The names a term references -/

/-- **`n` is a name `e` references**: a constant's name or a projection's structure, exactly
(`GraphWalk.Refs` compares names by `==`). -/
inductive Names (n : Ix.Name) : Ix.Expr → Prop
  | const {us : Array Ix.Level} {h : Address} : Names n (.const n us h)
  | projName {i : Nat} {s : Ix.Expr} {h : Address} : Names n (.proj n i s h)
  | projStruct {t : Ix.Name} {i : Nat} {s : Ix.Expr} {h : Address} : Names n s → Names n (.proj t i s h)
  | appF {f a : Ix.Expr} {h : Address} : Names n f → Names n (.app f a h)
  | appA {f a : Ix.Expr} {h : Address} : Names n a → Names n (.app f a h)
  | lamT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} : Names n t → Names n (.lam x t b bi h)
  | lamB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} : Names n b → Names n (.lam x t b bi h)
  | allT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      Names n t → Names n (.forallE x t b bi h)
  | allB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      Names n b → Names n (.forallE x t b bi h)
  | letT {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Names n t → Names n (.letE x t v b nd h)
  | letV {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Names n v → Names n (.letE x t v b nd h)
  | letB {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Names n b → Names n (.letE x t v b nd h)
  | mdata {d : Array (Ix.Name × Ix.DataValue)} {e : Ix.Expr} {h : Address} : Names n e → Names n (.mdata d e h)

/-- A name a term references is one the reference graph walks. -/
theorem Names.refs {n : Ix.Name} : ∀ {e : Ix.Expr}, Names n e → GraphWalk.Refs n e
  | _, .const => .const BEq.rfl
  | _, .projName => .projName BEq.rfl
  | _, .projStruct h => .projStruct h.refs
  | _, .appF h => .appF h.refs
  | _, .appA h => .appA h.refs
  | _, .lamT h => .lamT h.refs
  | _, .lamB h => .lamB h.refs
  | _, .allT h => .allT h.refs
  | _, .allB h => .allB h.refs
  | _, .letT h => .letT h.refs
  | _, .letV h => .letV h.refs
  | _, .letB h => .letB h.refs
  | _, .mdata h => .mdata h.refs

/-- **A related term's names**: every name a source term references is related to a key. -/
theorem related_names {md : Mode} {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Kernel.Level → Prop}
    {e : Ix.Expr} {t : CExpr md} (rel : Related names levels e t) {n : Ix.Name} (hn : Names n e) :
    ∃ k, names n k := by
  induction rel with
  | bvar => cases hn
  | sort => cases hn
  | const hash sources targets mapped universes =>
    cases hn
    exact ⟨_, mapped⟩
  | app hash _ _ fnIH argIH =>
    cases hn with
    | appF h => exact fnIH h
    | appA h => exact argIH h
  | lam name info hash _ _ typeIH bodyIH =>
    cases hn with
    | lamT h => exact typeIH h
    | lamB h => exact bodyIH h
  | all name info hash _ _ typeIH bodyIH =>
    cases hn with
    | allT h => exact typeIH h
    | allB h => exact bodyIH h
  | letE name nonDep hash _ _ _ typeIH valueIH bodyIH =>
    cases hn with
    | letT h => exact typeIH h
    | letV h => exact valueIH h
    | letB h => exact bodyIH h
  | nat => cases hn
  | str => cases hn
  | proj field hash mapped _ valueIH =>
    cases hn with
    | projName => exact ⟨_, mapped⟩
    | projStruct h => exact valueIH h
  | mdata data hash plain _ bodyIH =>
    cases hn with
    | mdata h => exact bodyIH h
  | contract data hash c frame read _ lowered bodyIH =>
    cases hn with
    | mdata h => exact bodyIH h

/-- The names of the sources a block's roots read. -/
theorem rootsRead_names {md : Mode} {reader : MemberReader md} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Kernel.Level → Prop} {sources : List Ix.Expr} {roots : List Ixon.Expr}
    (h : SharingRoots.RootsRead reader (Related names levels) sources roots) {e : Ix.Expr} (he : e ∈ sources)
    {n : Ix.Name} (hn : Names n e) : ∃ k, names n k := by
  obtain ⟨_, -, _, rel, -⟩ := InductiveUnits.forall₂_mem_left h e he
  exact related_names rel hn

/-! ## The ingress keys the names a term references -/

theorem withContract_good {Q : KeyScope .source} {c : Ix.SemanticContract.Contract}
    {e : Ix.Expr} {x y : Ix.Kernel.Expr .source} (h : Ix.LeanIngress.withContract c e x = .ok y) :
    y.Good Q ↔ x.Good Q := by
  unfold Ix.LeanIngress.withContract at h
  split at h <;> first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Iff.rfl)
    | cases h

/-- **A converted term is good when the ingress keys of the names its Lean term references
are**. -/
theorem ingress_good {σ : Ix.Name → LevelParam} {Q : KeyScope .source} (str : Q.Str) {e : Ix.Expr} :
    ∀ {k : Ix.Kernel.Expr .source}, ingressExpr σ e = .ok k →
      (∀ n, Names n e → (ingressKey n).Good Q) → k.Good Q := by
  induction e with
  | bvar i _ =>
    intro k h _
    simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | fvar _ _ => intro k h _; simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | mvar _ _ => intro k h _; simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | sort u _ =>
    intro k h _
    rw [ingressExpr] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  | const n us _ =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact refs n .const
  | app f a _ fIH aIH =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, hf, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, ha, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fIH hf fun n hn => refs n (.appF hn), aIH ha fun n hn => refs n (.appA hn)⟩
  | lam _ t b _ _ tIH bIH =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨tIH ht fun n hn => refs n (.lamT hn), bIH hb fun n hn => refs n (.lamB hn)⟩
  | forallE _ t b _ _ tIH bIH =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨tIH ht fun n hn => refs n (.allT hn), bIH hb fun n hn => refs n (.allB hn)⟩
  | letE _ t v b _ _ tIH vIH bIH =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hv, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨tIH ht fun n hn => refs n (.letT hn), vIH hv fun n hn => refs n (.letV hn),
      bIH hb fun n hn => refs n (.letB hn)⟩
  | lit l _ =>
    intro k h _
    cases l with
    | natVal _ =>
      simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at h
      subst h
      trivial
    | strVal _ =>
      simp only [ingressExpr, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact str
  | mdata d e _ eIH =>
    intro k h refs
    rw [Ix.LeanIngress.ingressExpr_mdata] at h
    unfold ingressMData at h
    split at h
    · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨_, hx, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      exact (withContract_good h).mpr (eIH hx fun n hn => refs n (.mdata hn))
    · exact eIH h fun n hn => refs n (.mdata hn)
  | proj t _ e _ eIH =>
    intro k h refs
    rw [ingressExpr] at h
    obtain ⟨_, he, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨refs t .projName, eIH he fun n hn => refs n (.projStruct hn)⟩

/-- A Lean term's conversion, or its placeholder, is good when the ingress keys of the names it
references are. -/
theorem convOf_good {Q : KeyScope .source} (str : Q.Str) (σ : Ix.LeanIngress.Numbering) {e : Ix.Expr}
    (refs : ∀ n, Names n e → (ingressKey n).Good Q) : (InductiveUnits.convOf σ e).Good Q := by
  unfold InductiveUnits.convOf
  split
  · rename_i k hk
    exact ingress_good str hk refs
  · trivial

/-! ## Renaming and canonical levels keep a group in scope -/

theorem good_mapLevels {Q : KeyScope .source} (f : Ix.LeanIngress.KLevel → Ix.LeanIngress.KLevel) :
    ∀ {e : Ix.Kernel.Expr .source}, (mapLevels f e).Good Q ↔ e.Good Q
  | .bvar _ => Iff.rfl
  | .fvar _ t => good_mapLevels f (e := t)
  | .sort _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .app _ _ => and_congr (good_mapLevels f) (good_mapLevels f)
  | .lam _ _ _ => and_congr (good_mapLevels f) (good_mapLevels f)
  | .forallE _ _ _ => and_congr (good_mapLevels f) (good_mapLevels f)
  | .letE _ _ _ _ => and_congr (good_mapLevels f) (and_congr (good_mapLevels f) (good_mapLevels f))
  | .lit _ => Iff.rfl
  | .proj _ _ e => and_congr Iff.rfl (good_mapLevels f (e := e))

/-- A hint override keeps a group's terms. -/
theorem convGood_withHints {Q : KeyScope .source} (hints : CName .source → Option ReducibilityHint) :
    ∀ {c : Converted}, ConvGood Q c → ConvGood Q (c.withHints hints)
  | .definitions ms, h => by
    intro m hm
    simp only [Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have := h m0 hm0
    split <;> exact this
  | .inductive _, h => h
  | .axiom _, h => h
  | .quot _ _, h => h

/-- **Renaming keys into a scope keeps a group's terms in it.** -/
theorem convGood_substKeys {ρ : FiberMap} {P Q : Ix.Kernel.Mode.Id .source → Prop}
    (hK : ∀ k : Key .source, k.Good (KeyScope.ofId P) → (Ix.LeanIngress.Key.subst ρ k).Good (KeyScope.ofId Q)) :
    ∀ {c : Converted}, ConvGood (KeyScope.ofId P) c → ConvGood (KeyScope.ofId Q) (c.substKeys ρ)
  | .definitions ms, h => by
    intro m hm
    simp only [Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨Ix.LeanIngress.Expr.substKeys_good hK (h m0 hm0).1,
      Ix.LeanIngress.Expr.substKeys_good hK (h m0 hm0).2⟩
  | .inductive rb, h => by
    obtain ⟨ht, hc, hn, hr⟩ := h
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun ns hns k hk => ?_, fun x hx => ?_⟩
    · simp only [Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, p, i⟩, hx0, rfl⟩ := hx
      exact Ix.LeanIngress.ConstantVal.substKeys_good hK (ht _ hx0)
    · simp only [Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, p, i⟩, hx0, rfl⟩ := hx
      exact Ix.LeanIngress.ConstantVal.substKeys_good hK (hc _ hx0)
    · simp only [Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.mem_map] at hns
      obtain ⟨ns0, hns0, rfl⟩ := hns
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
      exact hK _ (hn ns0 hns0 k0 hk0)
    · simp only [Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, rc, rules⟩, hx0, rfl⟩ := hx
      refine ⟨Ix.LeanIngress.ConstantVal.substKeys_good hK (hr _ hx0).1, fun r hr' => ?_⟩
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr'
      exact Ix.LeanIngress.RecRule.substKeys_good hK ((hr _ hx0).2 r0 hr0)
  | .axiom _, h => Ix.LeanIngress.Expr.substKeys_good hK h
  | .quot _ _, h => Ix.LeanIngress.Expr.substKeys_good hK h

/-- A converted inductive block's recursor rules fire inertly (as quotient Source converts them). -/
def Inert : Converted → Prop
  | .inductive rb => ∀ x ∈ rb.recs.toList, ∀ r ∈ x.2.2, r.fire = .inert
  | _ => True

/-- **Canonical levels keep a group's terms**, for inert recursor rules. -/
theorem convGood_canon {Q : KeyScope .source} :
    ∀ {c : Converted}, ConvGood Q c → Inert c → ConvGood Q c.canon
  | .definitions ms, h, _ => by
    intro m hm
    simp only [Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    rw [RecordReadings.defMember_canon]
    exact ⟨(good_mapLevels _).mpr (h m0 hm0).1, (good_mapLevels _).mpr (h m0 hm0).2⟩
  | .axiom cv, h, _ => by
    show ((Ix.LeanIngress.canonValM cv).run' {}).type.Good Q
    rw [RecordReadings.canonValM_run]
    exact (good_mapLevels _).mpr h
  | .quot _ cv, h, _ => by
    show ((Ix.LeanIngress.canonValM cv).run' {}).type.Good Q
    rw [RecordReadings.canonValM_run]
    exact (good_mapLevels _).mpr h
  | .inductive rb, h, inert => by
    obtain ⟨ht, hc, hn, hr⟩ := h
    refine ⟨fun x hx => ?_, fun x hx => ?_, hn, fun x hx => ?_⟩
    · simp only [Ix.LeanIngress.BlockRead.canon, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, p, i⟩, hx0, rfl⟩ := hx
      dsimp only
      rw [RecordReadings.canonValM_run]
      exact ⟨(ht _ hx0).1, (good_mapLevels _).mpr (ht _ hx0).2⟩
    · simp only [Ix.LeanIngress.BlockRead.canon, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, p, i⟩, hx0, rfl⟩ := hx
      dsimp only
      rw [RecordReadings.canonValM_run]
      exact ⟨(hc _ hx0).1, (good_mapLevels _).mpr (hc _ hx0).2⟩
    · simp only [Ix.LeanIngress.BlockRead.canon, Array.toList_map, List.mem_map] at hx
      obtain ⟨⟨cv, rc, rules⟩, hx0, rfl⟩ := hx
      dsimp only
      rw [InductiveUnits.canonRec_eq cv rules (inert _ hx0)]
      refine ⟨⟨(hr _ hx0).1.1, (good_mapLevels _).mpr (hr _ hx0).1.2⟩, fun r hr' => ?_⟩
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr'
      exact ⟨((hr _ hx0).2 r0 hr0).1, ((hr _ hx0).2 r0 hr0).2.1,
        (good_mapLevels _).mpr ((hr _ hx0).2 r0 hr0).2.2⟩

/-- **Quotient Source's form of a group in the scope of input keys is in the scope of
representatives**: the hint override, the renaming onto representatives (`Key.subst_goodAt`) and
canonical levels keep every key good. -/
theorem convGood_quotient {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    (hb : Ix.LeanIngress.TableBound ixe roles) (hints : CName .source → Option ReducibilityHint) {c : Converted}
    (good : ConvGood (KeyScope.ofId (QIn ixe)) c) (inert : Inert c) :
    ConvGood (KeyScope.ofId (QRepAt ixe roles)) ((c.withHints hints).quotient (fiberAliasAt ixe roles)) := by
  refine convGood_canon (convGood_substKeys (fun k hk => Ix.LeanIngress.Key.subst_goodAt hb hk)
    (convGood_withHints hints good)) ?_
  cases c with
  | «inductive» rb =>
    intro x hx r hr
    simp only [Ix.LeanIngress.BlockRead.substKeys, Array.toList_map, List.mem_map] at hx
    obtain ⟨⟨cv, rc, rules⟩, hx0, rfl⟩ := hx
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    simp [Ix.LeanIngress.RecRule.substKeys, inert _ hx0 r0 hr0, Ix.LeanIngress.RecRuleFire.substKeys]
  | _ => trivial

/-! ## A compiled constant's sources name members of its block or bindings -/

/-- A member slot read anywhere: the reading theorems are applied only for the names they
relate. -/
def selfAny : Nat → Option (ReadM (CName .anon)) := fun _ => some (.ok (.id default))

/-- **The names a block compiled at `cenv` is read at**: a name `own` holds (the block's
members), or a binding the compile resolves. -/
def BoundOr (cenv : CompileEnv) (own : Ix.Name → Prop) (m : Ix.Name) (_ : CName .anon) : Prop :=
  own m ∨ ∃ a, lookupBinding cenv {} m = some a

theorem boundOr_external (cenv : CompileEnv) (own : Ix.Name → Prop) (blob : Address → Option ByteArray) :
    BindingsCorrect cenv {} (BlockRefs.addrCtx blob) (BoundOr cenv own) :=
  fun _ a hb => ⟨.id a, BlockRefs.addrCtx_keyAt blob a, .inr ⟨a, hb⟩⟩

/-- A constant compiled alone reads its own name as a member slot. -/
theorem singleton_scope (name : Ix.Name) (context : CompileEnv × BlockEnv) (cenv : CompileEnv) (e : Ix.Expr) :
    ConstsSatisfy (SelfName (EmissionDispatch.singletonContext name context).2 selfAny
      (BoundOr cenv (· = name))) e :=
  constsSatisfy_of_forall (fun m index found => by
    obtain ⟨same, -⟩ := DefinitionReading.singleton_lookup name m index found
    exact ⟨_, rfl, .inl (Ix.CompileCert.Canon.nameCompareExact_eq_iff.mp same)⟩) e

/-- **The names a constant compiled alone references** are its own name or bindings of the
state it is compiled at. -/
theorem lone_names {ci : Ix.ConstantInfo} {cenv : CompileEnv} {benv : BlockEnv} {out : BlockResult}
    {after : BlockState} (ran : rawRun (compileConstantInfo ci) (cenv, benv) {} = (.ok out, after))
    (hi : ∀ v, ci ≠ .inductInfo v) (hct : ∀ v, ci ≠ .ctorInfo v) {e : Ix.Expr} (he : e ∈ termsOf ci)
    {n : Ix.Name} (hn : Names n e) : n = ci.getCnst.name ∨ ∃ a, lookupBinding cenv {} n = some a := by
  let cx := BlockRefs.addrCtx fun a => cenv.blobs.get? a
  have aligned : ∀ address, cx.blob address = cenv.blobs.get? address := fun _ => rfl
  cases ci with
  | axiomInfo v =>
    rw [EmissionDispatch.axiom_run (cenv, benv)] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.axiomInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = v.cnst.name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) v (singleton_scope _ _ cenv _) BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf, Ix.ConstantInfo.getCnst] using he) hn).elim fun _ h => h
  | quotInfo v =>
    rw [EmissionDispatch.quotient_run (cenv, benv)] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.quotientInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = v.cnst.name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) v (singleton_scope _ _ cenv _) BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf, Ix.ConstantInfo.getCnst] using he) hn).elim fun _ h => h
  | recInfo v =>
    rw [EmissionDispatch.recursor_run (cenv, benv)] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.recursorInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = v.cnst.name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) v (singleton_scope _ _ cenv _) (fun _ _ => singleton_scope _ _ cenv _)
      BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf] using he) hn).elim fun _ h => h
  | defnInfo v =>
    rw [EmissionDispatch.definition_run (cenv, benv) _ _ rfl] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.definitionInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = (definitionValData v).name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) _ (singleton_scope _ _ cenv _) (singleton_scope _ _ cenv _)
      BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf, definitionValData] using he) hn).elim fun _ h => h
  | thmInfo v =>
    rw [EmissionDispatch.definition_run (cenv, benv) _ _ rfl] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.definitionInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = (theoremValData v).name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) _ (singleton_scope _ _ cenv _) (singleton_scope _ _ cenv _)
      BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf, theoremValData] using he) hn).elim fun _ h => h
  | opaqueInfo v =>
    rw [EmissionDispatch.definition_run (cenv, benv) _ _ rfl] at ran
    obtain ⟨-, -, -, -, roots⟩ := EmissionBlocks.definitionInfo_correct cx (fun _ => default) selfAny
      (BoundOr cenv (· = (opaqueValData v).name)) (fun _ => default) {} _ aligned
      (boundOr_external cenv _ _) _ (singleton_scope _ _ cenv _) (singleton_scope _ _ cenv _)
      BlockStart.clean_empty ran
    exact (rootsRead_names roots (by simpa [termsOf, opaqueValData] using he) hn).elim fun _ h => h
  | inductInfo v => exact absurd rfl (hi v)
  | ctorInfo v => exact absurd rfl (hct v)

/-- The names of a block's members: a member's own, or a constructor's of a member. -/
def MemberName (ms : List MutConst) (n : Ix.Name) : Prop :=
  ∃ m ∈ ms, m.name = n ∨ ∃ c ∈ m.ctors.toList, c.cnst.name = n

/-- A name a fold of insertions holds was inserted, or the start held it. -/
theorem foldl_insP_some : ∀ (L : List (Ix.Name × Nat)) (m0 : Ix.MutCtx) {x : Ix.Name} {v : Nat},
    (L.foldl Ix.CompileCert.Canon.insP m0)[x]? = some v → (∃ p ∈ L, p.1 = x) ∨ m0[x]? = some v
  | [], _, _, _, h => .inr h
  | p :: L, m0, x, v, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insP_some L _ h with ⟨q, hq, e⟩ | h
    · exact .inl ⟨q, List.mem_cons_of_mem _ hq, e⟩
    · by_cases hp : p.1 = x
      · exact .inl ⟨p, List.mem_cons_self, hp⟩
      · simp only [Ix.CompileCert.Canon.insP] at h
        rw [Ix.CompileCert.Canon.treeMap_insert_ne _ _ hp] at h
        exact .inr h

/-- **A name a block's member context holds is a member's or a member's constructor's.** -/
theorem ctx_memberName {ms : List MutConst} {n : Ix.Name} {idx : Nat}
    (h : (MutConst.ctx ms)[n]? = some idx) : MemberName ms n := by
  rw [Ix.CompileCert.Canon.ctx_fold] at h
  rcases foldl_insP_some _ _ h with ⟨p, hp, rfl⟩ | h
  · obtain ⟨j, m, hm, hcase⟩ := (Ix.CompileCert.Canon.mem_ctxPairs _ 0 _ p).1 hp
    refine ⟨m, List.mem_of_getElem? hm, ?_⟩
    rcases hcase with rfl | ⟨k, c, hc, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨c, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hc), rfl⟩
  · rw [Ix.CompileCert.Canon.default_getElem?] at h
    cases h

/-- A block's members read their member names as member slots. -/
theorem block_scope (ms : List MutConst) (context : CompileEnv × BlockEnv) (cenv : CompileEnv) (e : Ix.Expr) :
    ConstsSatisfy (SelfName (BlockEmission.mutContext ms context).2 selfAny
      (BoundOr cenv (MemberName ms))) e :=
  constsSatisfy_of_forall (fun m index found => by
    change (MutConst.ctx ms).get? m = some index at found
    rw [Std.TreeMap.get?_eq_getElem?] at found
    exact ⟨_, rfl, .inl (ctx_memberName found)⟩) e

/-- **The names a block compiled in its members' order references** are member names or
bindings of the state it is compiled at. -/
theorem block_names {ms : List MutConst} {cenv : CompileEnv} {benv : BlockEnv} {out : BlockResult}
    {after : BlockState} (ran : rawRun (compileMutualBlock ms) (cenv, benv) {} = (.ok out, after))
    {m : MutConst} (hm : m ∈ ms) {e : Ix.Expr} (he : e ∈ BlockEmission.memberSources m) {n : Ix.Name}
    (hn : Names n e) : MemberName ms n ∨ ∃ a, lookupBinding cenv {} n = some a := by
  let cx := BlockRefs.addrCtx fun a => cenv.blobs.get? a
  let param : Nat → LevelParam := fun _ => default
  let σOf : MutConst → Ix.Name → LevelParam := fun _ _ => default
  let names := BoundOr cenv (MemberName ms)
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  have kept : ∀ m ∈ ms, Good cx param selfAny (DefinitionEmission.relOf param names σOf m) {} seededState :=
    fun m _ => (EmissionBlocks.preseed_then cx param selfAny {} (related := DefinitionEmission.relOf param names σOf m)
      (context := BlockEmission.mutContext ms (cenv, benv)) (fun _ => rfl)
      (BlockStart.clean_empty.good cx param selfAny _) seeded).1
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, -⟩ := bind_ok compiled
  unfold compileMutConsts at payloadRan
  obtain ⟨state, middle', classesRan, -⟩ := bind_ok payloadRan
  obtain ⟨-, ps, -, each⟩ := DefinitionEmission.members_each cx param selfAny names {} σOf
    (BlockEmission.mutContext ms (cenv, benv)) (fun _ => rfl) (boundOr_external cenv _ _) ms {}
    (fun _ _ e _ => block_scope ms _ cenv e) kept classesRan
  obtain ⟨_, -, -, -, roots⟩ := InductiveUnits.forall₂_mem_left each m hm
  exact (rootsRead_names roots he hn).elim fun _ h => h

/-! ## Every name a closure constant's sources reference is published -/

/-- `n` is a key the input stores a constant under. -/
def InputKey (env : Ix.Environment) (n : Ix.Name) : Prop :=
  ∃ ci, (n, ci) ∈ env.consts.toList

/-- `n` is published. -/
def Published (ixe : Ixon.Env) (n : Ix.Name) : Prop :=
  ∃ named, (n, named) ∈ ixe.named.toList

section Closure

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : RoleTable} {envQ : Env .source}

/-- An input constant looked up is stored under its own name. -/
theorem input_own (P : Premises env roots sub ixe failures t envQ) {k : Ix.Name} {ci : Ix.ConstantInfo}
    (h : env.consts.get? k = some ci) : InputKey env ci.getCnst.name := by
  obtain ⟨k0, hk0⟩ := SourceStoredNames.lookup_stored h
  refine ⟨ci, ?_⟩
  rw [inputsNamed P.compiled k0 ci hk0]
  exact hk0

/-- **A member the block's loop makes is named by input keys**, its constructors too. -/
theorem member_input (P : Premises env roots sub ixe failures t envQ) {k : Ix.Name} {m : MutConst}
    (hm : memberOf (env.consts.get? ·) k = some m) :
    InputKey env m.name ∧ ∀ c ∈ m.ctors.toList, InputKey env c.cnst.name := by
  unfold memberOf at hm
  split at hm
  · rename_i v hv
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp hm
    refine ⟨input_own P hv, fun c hc => ?_⟩
    have hc' : c ∈ cs := by simpa [MutConst.ctors, InductiveCompile.indOf] using hc
    obtain ⟨_, -, hy⟩ := TraceFold.mapM_ctorOf_mem hcs c hc'
    exact input_own P hy
  all_goals first
    | (rename_i v hv
       cases hm
       exact ⟨input_own P hv, by simp [MutConst.ctors, MutConst.fromDefinitionVal, MutConst.fromTheoremVal,
         MutConst.fromOpaqueVal]⟩)
    | cases hm

/-- A non-inductive member's sources are its constant's terms. -/
theorem memberSources_terms {E : Ix.Name → Option Ix.ConstantInfo} {x : Ix.Name} {ci : Ix.ConstantInfo}
    {m : MutConst} (hE : E x = some ci) (hm : memberOf E x = some m) (hi : ∀ v, ci ≠ .inductInfo v) :
    ∀ e ∈ BlockEmission.memberSources m, e ∈ termsOf ci := by
  cases ci with
  | inductInfo v => exact absurd rfl (hi v)
  | defnInfo v =>
    simp only [memberOf, hE, Option.some.injEq] at hm
    subst hm
    intro e he
    simpa [BlockEmission.memberSources, MutConst.fromDefinitionVal, termsOf] using he
  | thmInfo v =>
    simp only [memberOf, hE, Option.some.injEq] at hm
    subst hm
    intro e he
    simpa [BlockEmission.memberSources, MutConst.fromTheoremVal, termsOf] using he
  | opaqueInfo v =>
    simp only [memberOf, hE, Option.some.injEq] at hm
    subst hm
    intro e he
    simpa [BlockEmission.memberSources, MutConst.fromOpaqueVal, termsOf] using he
  | recInfo v =>
    simp only [memberOf, hE, Option.some.injEq] at hm
    subst hm
    intro e he
    simpa [BlockEmission.memberSources, termsOf] using he
  | _ => simp [memberOf, hE] at hm

/-- `sourceMembers` is one entry per member, in some order of the members. -/
theorem sourceMembers_perm (cs : Array MutConst) :
    (sourceMembers cs).Perm cs.toList := by
  rw [LeanOrder.sourceMembers_def]
  have p := ((Ix.CompileCert.Canon.qsort_perm cs.zipIdx (LeanOrder.zipBefore LeanOrder.orderKey)).toList).map (·.1)
  rw [Array.toList_zipIdx, List.zipIdx_map_fst] at p
  exact p

/-- **A name a closure constant's compiled member references is an input key**: the fold
compiled the constant's block at a snapshot whose bindings are input keys
(`FoldBlock.bound_exact`), alone (`lone_names`) or in its members' order (`block_names`), whose
members and constructors are input keys (`member_input`). -/
theorem fold_member_names (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (hx : (x, ci) ∈ sub.consts.toList) (hct : ∀ cv, ci ≠ .ctorInfo cv) {m : MutConst}
    (hm : memberOf (env.consts.get? ·) x = some m) {e : Ix.Expr} (he : e ∈ BlockEmission.memberSources m)
    {n : Ix.Name} (hn : Names n e) : InputKey env n := by
  obtain ⟨snap, rep, all, r, c, fb, -, hmem⟩ := GroupRuns.foldBlock_of P hx
  have hin : all.contains x = true := hmem hct
  have hxE : (x, ci) ∈ env.consts.toList := SourceStoredNames.stored_input P hx
  have hget : env.consts.get? x = some ci := SourceStoredNames.stored_get hxE
  have bound : ∀ a, lookupBinding snap.cenv {} n = some a → InputKey env n :=
    fun _ hb => fb.bound_exact P.compiled (TraceFold.lookup_empty hb)
  have envCongr : ∀ a b, (a == b) = true → env.consts.get? a = env.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths fb.ran
  rcases paths with ⟨hcond, hs⟩ | ⟨-, cs, out, s₄, hloop, hrun, -, -⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
    obtain ⟨hsize, hind⟩ := hcond
    have hne := Condense.condense_nonempty fb.block
    have hkey : (blockKey rep all == x) = true := GroupRuns.single_beq hsize (blockKey_mem (lo := rep) hne) hin
    rw [fb.env, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hkey, ← Std.HashMap.get?_eq_getElem?,
      hget] at hconst
    obtain rfl : const = ci := (Option.some.inj hconst).symm
    have hi : ∀ v, const ≠ .inductInfo v := fun v h => by subst h; simp [GroupRuns.isIndConst] at hind
    rcases lone_names hs hi hct (memberSources_terms hget hm hi e he) hn with rfl | ⟨a, hb⟩
    · refine ⟨const, ?_⟩
      rw [inputsNamed P.compiled x const hxE]
      exact hxE
    · exact bound a hb
  · have hcs := GroupRuns.membersLoop_eq _ _ hloop
    have hE : (fun k => snap.cenv.env.get? k) = fun k => env.consts.get? k := funext fb.env
    dsimp only at hcs
    rw [hE] at hcs
    have ofCs : ∀ m', m' ∈ cs.toList → ∃ k, memberOf (env.consts.get? ·) k = some m' := by
      intro m' hm'
      rw [hcs] at hm'
      simp only [List.nil_append, List.mem_filterMap] at hm'
      obtain ⟨k, -, hk⟩ := hm'
      exact ⟨k, hk⟩
    obtain ⟨k, hk, hxk⟩ := GroupRuns.listed hin
    have hmk : memberOf (env.consts.get? ·) k = some m := (GroupRuns.memberOf_congr envCongr hxk).symm.trans hm
    have hmcs : m ∈ cs.toList := by
      rw [hcs]
      simp only [List.nil_append, List.mem_filterMap]
      exact ⟨k, hk, hmk⟩
    have perm := sourceMembers_perm cs
    rcases block_names hrun (perm.mem_iff.mpr hmcs) he hn with ⟨m', hm', hname⟩ | ⟨a, hb⟩
    · obtain ⟨k', hk'⟩ := ofCs m' (perm.mem_iff.mp hm')
      obtain ⟨hnm, hct'⟩ := member_input P hk'
      rcases hname with rfl | ⟨c', hc', rfl⟩
      · exact hnm
      · exact hct' c' hc'
    · exact bound a hb

/-- **An input key a closure constant references is published**: the closure holds it. -/
theorem published_of_ref (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (hx : (x, ci) ∈ sub.consts.toList) {n : Ix.Name} (hr : (refsOf ci).contains n = true) (hin : InputKey env n) :
    Published ixe n := by
  obtain ⟨c, hc⟩ := hin
  have hcl : IsClosure env roots sub := P.source.1
  have hsx : (sub.consts.get? x).isSome = true := by rw [SourceStoredNames.stored_get hx]; rfl
  have hxE : env.consts.get? x = some ci := SourceStoredNames.stored_get (SourceStoredNames.stored_input P hx)
  have hreach : Reaches env roots n := .step (CompiledRefs.reaches_of_sub hcl hsx) ⟨ci, hxE, .inl hr⟩
  have hsubget : sub.consts.get? n = some c := ((hcl n).1 hreach).trans (SourceStoredNames.stored_get hc)
  obtain ⟨k, hk⟩ := SourceStoredNames.lookup_stored hsubget
  have e1 := inputsNamed P.compiled _ _ (SourceStoredNames.stored_input P hk)
  have e2 := inputsNamed P.compiled _ _ hc
  rw [e1] at e2
  subst e2
  obtain ⟨named, hmem, -⟩ := SourceStoredNames.stored_published P hk
  exact ⟨named, hmem⟩

/-- A closure name is published. -/
theorem published_of_stored (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (h : (n, ci) ∈ sub.consts.toList) : Published ixe n := by
  obtain ⟨named, hmem, -⟩ := SourceStoredNames.stored_published P h
  exact ⟨named, hmem⟩

/-- A published name's ingress key is in the scope of input keys. -/
theorem key_good (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} (h : Published ixe n) :
    (ingressKey n).Good (KeyScope.ofId (QIn ixe)) := by
  obtain ⟨_, hm⟩ := h
  exact ClosureKeying.ingressKey_good P.agree hm

/-- **A closure constant's term, every name it references an input key, references only names
whose ingress keys are in the scope of input keys.** -/
theorem term_good (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (hx : (x, ci) ∈ sub.consts.toList) {e : Ix.Expr} (he : e ∈ termsOf ci)
    (inputs : ∀ n, Names n e → InputKey env n) :
    ∀ n, Names n e → (ingressKey n).Good (KeyScope.ofId (QIn ixe)) :=
  fun n hn => key_good P (published_of_ref P hx (GraphRefs.refsOf_mentions ci he hn.refs) (inputs n hn))

end Closure

/-! ## Each kind of group -/

section Groups

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : RoleTable} {envQ : Env .source}
  {hints : CName .source → Option ReducibilityHint} {i : Nat}

/-- A definition group's member's type and value reference only names in the scope of input
keys. -/
theorem definition_terms (P : Premises env roots sub ixe failures t envQ) {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) {ci : Ix.ConstantInfo}
    (hci : ci ∈ members) {e : Ix.Expr} (he : e = ci.getCnst.type ∨ Ix.LeanIngress.definitionValue ci = some e) :
    ∀ n, Names n e → (ingressKey n).Good (KeyScope.ofId (QIn ixe)) := by
  have hst := TraceFold.members_stored P hgr ci hci
  obtain ⟨_, _, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) _ (Array.mem_of_getElem? hgr) trivial
  obtain ⟨-, defsM⟩ := GroupRuns.componentGroup_sorted hcomp
  have hd := defsM ci hci
  have hget : env.consts.get? ci.getCnst.name = some ci :=
    SourceStoredNames.stored_get (SourceStoredNames.stored_input P hst)
  obtain ⟨d, hsd, hmem⟩ := GroupRuns.memberOf_def (E := (env.consts.get? ·)) hget hd
  obtain ⟨-, -, htype, hval, -⟩ := RecordReadings.sourceData_facts hsd
  obtain ⟨hdt, hdv⟩ := TraceFold.sourceData_terms hsd
  have hct : ∀ cv, ci ≠ .ctorInfo cv := fun cv h => by subst h; simp [Ix.LeanIngress.isDefinition] at hd
  have he' : e = d.type ∨ e = d.value := by
    rcases he with rfl | h
    · exact .inl htype
    · rw [hval] at h
      exact .inr (Option.some.inj h).symm
  rcases he' with rfl | rfl
  · exact term_good P hst hdt fun n hn =>
      fold_member_names P hst hct hmem (by simp [BlockEmission.memberSources]) hn
  · exact term_good P hst hdv fun n hn =>
      fold_member_names P hst hct hmem (by simp [BlockEmission.memberSources]) hn

/-- **A definitions group converts in the scope of input keys.** -/
theorem definitions_good (P : Premises env roots sub ixe failures t envQ) {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) {c : Converted}
    (hconv : Ix.LeanIngress.convertDefinitions members = .ok c) :
    ConvGood (KeyScope.ofId (QIn ixe)) c ∧ Inert c := by
  have str : (KeyScope.ofId (md := .source) (QIn ixe)).Str := KeyScope.ofId_str _
  obtain ⟨l⟩ := members
  rcases l with _ | ⟨ci, _ | ⟨ci', rest⟩⟩
  · have h0 : Ix.LeanIngress.convertDefinitions #[] = .ok (.definitions #[]) := by
      simp [Ix.LeanIngress.convertDefinitions, Ix.LeanIngress.exprsOf]
      rfl
    obtain rfl : c = .definitions #[] := (Except.ok.inj (h0.symm.trans hconv)).symm
    exact ⟨fun m hm => by simp at hm, trivial⟩
  · have hconv' : Ix.LeanIngress.convertDefinitions #[ci] = .ok c := hconv
    obtain ⟨s, v, t', v', -, hv, ht, hv', rfl⟩ := RecordReadings.convertDefinitions_single hconv'
    refine ⟨fun m hm => ?_, trivial⟩
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨ingress_good str ht (definition_terms P hgr (by simp) (.inl rfl)),
      ingress_good str hv' (definition_terms P hgr (by simp) (.inr hv))⟩
  · obtain ⟨ms, order, hsize, hms, -, rfl⟩ := DefinitionBlockReads.convertDefinitions_block hconv (by simp)
    refine ⟨fun m hm => ?_, trivial⟩
    simp only [Array.toList_map, List.mem_map] at hm
    obtain ⟨k, -, rfl⟩ := hm
    by_cases hk : k < (⟨ci :: ci' :: rest⟩ : Array Ix.ConstantInfo).size
    · obtain ⟨s, v, t', v', -, hv, ht, hv', -, hmk⟩ := hms k hk
      rw [getElem!_def, hmk]
      exact ⟨ingress_good str ht (definition_terms P hgr (Array.getElem_mem hk) (.inl rfl)),
        ingress_good str hv' (definition_terms P hgr (Array.getElem_mem hk) (.inr hv))⟩
    · have hnone : ms[k]? = none := by
        rw [Array.getElem?_eq_none_iff]
        omega
      rw [getElem!_def, hnone]
      exact ⟨trivial, trivial⟩

/-- **An axiom group converts in the scope of input keys.** -/
theorem axiom_good (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {v : Ix.AxiomVal} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.axiom v)) {c : Converted}
    (hconv : Ix.LeanIngress.convert (.axiom v) = .ok c) : ConvGood (KeyScope.ofId (QIn ixe)) c ∧ Inert c := by
  obtain ⟨hsingle, hst⟩ := TraceFold.axiom_single hgr P
  obtain ⟨snap, rep, all, r, cc, fb, ran, -⟩ := TraceFold.singleton_compiled P scheduled hgr trivial hsingle hst
    (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨t', -, ht, rfl⟩ := RecordReadings.convert_axiom hconv
  have he : v.cnst.type ∈ termsOf (.axiomInfo v) := by simp [termsOf, Ix.ConstantInfo.getCnst]
  refine ⟨ingress_good (KeyScope.ofId_str _) ht (term_good P hst he fun n hn => ?_), trivial⟩
  rcases lone_names ran (fun _ h => by cases h) (fun _ h => by cases h) he hn with rfl | ⟨a, hb⟩
  · exact ⟨_, SourceStoredNames.stored_input P hst⟩
  · exact fb.bound_exact P.compiled (TraceFold.lookup_empty hb)

/-- **A quotient group converts in the scope of input keys.** -/
theorem quot_good (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {v : Ix.QuotVal} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.quot v)) {c : Converted}
    (hconv : Ix.LeanIngress.convert (.quot v) = .ok c) : ConvGood (KeyScope.ofId (QIn ixe)) c ∧ Inert c := by
  obtain ⟨hsingle, hst⟩ := TraceFold.quot_single hgr P
  obtain ⟨snap, rep, all, r, cc, fb, ran, -⟩ := TraceFold.singleton_compiled P scheduled hgr trivial hsingle hst
    (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨t', ht, rfl⟩ := RecordReadings.convert_quot hconv
  have he : v.cnst.type ∈ termsOf (.quotInfo v) := by simp [termsOf, Ix.ConstantInfo.getCnst]
  refine ⟨ingress_good (KeyScope.ofId_str _) ht (term_good P hst he fun n hn => ?_), trivial⟩
  rcases lone_names ran (fun _ h => by cases h) (fun _ h => by cases h) he hn with rfl | ⟨a, hb⟩
  · exact ⟨_, SourceStoredNames.stored_input P hst⟩
  · exact fb.bound_exact P.compiled (TraceFold.lookup_empty hb)

/-- **An inductive group's converted block is in a scope** when its names, the names its terms
reference and its rules' constructors are. -/
theorem srcBlock_good {Q : KeyScope .source} (str : Q.Str) {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal} {first : Ix.InductiveVal}
    (typeNames : ∀ v ∈ types.toList, (ingressKey v.cnst.name).Good Q)
    (typeTerms : ∀ v ∈ types.toList, ∀ n, Names n v.cnst.type → (ingressKey n).Good Q)
    (ctorNames : ∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, (ingressKey c.cnst.name).Good Q)
    (ctorTerms : ∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, ∀ n, Names n c.cnst.type → (ingressKey n).Good Q)
    (recNames : ∀ r ∈ recs.toList, (ingressKey r.cnst.name).Good Q)
    (recTerms : ∀ r ∈ recs.toList, ∀ e ∈ termsOf (.recInfo r), ∀ n, Names n e → (ingressKey n).Good Q)
    (ruleCtors : ∀ r ∈ recs.toList, ∀ rule ∈ r.rules.toList, (ingressKey rule.ctor).Good Q) :
    (InductiveUnits.srcBlock types ctors recs first).Good Q := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun ns hns k hk => ?_, fun x hx => ?_⟩
  · simp only [InductiveUnits.srcBlock, List.toList_toArray, List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨typeNames v hv, convOf_good str _ (typeTerms v hv)⟩
  · simp only [InductiveUnits.srcBlock, List.toList_toArray, List.mem_map, List.mem_flatMap] at hx
    obtain ⟨c, ⟨cs, hcs, hc⟩, rfl⟩ := hx
    exact ⟨ctorNames cs hcs c hc, convOf_good str _ (ctorTerms cs hcs c hc)⟩
  · simp only [InductiveUnits.srcBlock, List.toList_toArray, List.mem_map] at hns
    obtain ⟨cs, hcs, rfl⟩ := hns
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    exact ctorNames cs hcs c hc
  · simp only [InductiveUnits.srcBlock, List.toList_toArray, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨⟨recNames r hr, convOf_good str _ (recTerms r hr _ (by simp [termsOf]))⟩, fun rr hrr => ?_⟩
    simp only [InductiveUnits.srcRec, List.mem_map] at hrr
    obtain ⟨rule, hrule, rfl⟩ := hrr
    exact ⟨ruleCtors r hr rule hrule, trivial,
      convOf_good str _ (recTerms r hr _ (by simp [termsOf]; exact .inr ⟨rule, Array.mem_toList_iff.mp hrule, rfl⟩))⟩

/-- **An inductive group converts in the scope of input keys.** -/
theorem inductive_good (P : Premises env roots sub ixe failures t envQ) {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) {c : Converted}
    (hconv : Ix.LeanIngress.convertInductive types ctors recs = .ok c) :
    ConvGood (KeyScope.ofId (QIn ixe)) c ∧ Inert c := by
  have str : (KeyScope.ofId (md := .source) (QIn ixe)).Str := KeyScope.ofId_str _
  obtain ⟨first, -, rfl, -⟩ := InductiveUnits.convertInductive_src hconv
  obtain ⟨_, _, -, -, hrecs, hcsize, -, -, typeGet, ctorGet, ctorsOf⟩ := GroupRuns.inductive_facts P hgr
  have namesIn := ClosureLayout.converted_names_stored P hgr hconv
  have named : ∀ n, n ∈ (Group.inductive types ctors recs).names → (ingressKey n).Good (KeyScope.ofId (QIn ixe)) :=
    fun n hn => by
      obtain ⟨_, h⟩ := namesIn n hn
      exact key_good P (published_of_stored P h)
  -- the types, with their constructors, are the members the fold compiled
  have typeIdx : ∀ v ∈ types.toList, ∃ j, ∃ hj : j < types.size, types[j] = v := fun v hv => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    exact ⟨j, by simpa using hj, rfl⟩
  have ctorIdx : ∀ cs ∈ ctors.toList, ∃ j, ∃ hj : j < ctors.size, ctors[j] = cs := fun cs hcs => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcs
    exact ⟨j, by simpa using hj, rfl⟩
  have member : ∀ j (hj : j < types.size), memberOf (env.consts.get? ·) types[j].cnst.name =
      some (.indc (InductiveCompile.indOf types[j] (ctors[j]'(by omega)))) := fun j hj => by
    have hc := ctorsOf j hj (by omega)
    simp only [memberOf, (typeGet j hj).1, hc, Option.map_some, Array.toArray_toList]
  have typeTerm : ∀ j (hj : j < types.size), ∀ e ∈ BlockEmission.memberSources
      (.indc (InductiveCompile.indOf types[j] (ctors[j]'(by omega)))), ∀ n, Names n e → InputKey env n :=
    fun j hj e he n hn => fold_member_names P (typeGet j hj).2 (fun _ h => by cases h) (member j hj) he hn
  have ctorStored : ∀ j (hj : j < ctors.size) k (hk : k < ctors[j].size),
      (ctors[j][k].cnst.name, .ctorInfo ctors[j][k]) ∈ sub.consts.toList := fun j hj k hk => by
    obtain ⟨ci, hci⟩ := namesIn _ ((TraceSegments.inductive_names types ctors recs _).mpr
      (.inr (.inl ⟨j, hj, k, hk, rfl⟩)))
    have := SourceStoredNames.stored_get (SourceStoredNames.stored_input P hci)
    rw [ctorGet j hj k hk] at this
    cases this
    exact hci
  -- the recursors are the closure's, compiled under their own names
  have recStored : ∀ r ∈ recs.toList, (r.cnst.name, .recInfo r) ∈ sub.consts.toList := fun r hr => by
    obtain ⟨k, hk, -⟩ := FamilyGroups.recsTable_mem
      (SourceStoredNames.blockRecursors_mem hrecs r (Array.mem_toList_iff.mp hr))
    have e := inputsNamed P.compiled _ _ (SourceStoredNames.stored_input P hk)
    rw [← e] at hk
    exact hk
  have recTerm : ∀ r ∈ recs.toList, ∀ e ∈ termsOf (.recInfo r), ∀ n, Names n e →
      (ingressKey n).Good (KeyScope.ofId (QIn ixe)) := fun r hr e he => by
    have hst := recStored r hr
    have hget : env.consts.get? r.cnst.name = some (.recInfo r) :=
      SourceStoredNames.stored_get (SourceStoredNames.stored_input P hst)
    have hmem : memberOf (env.consts.get? ·) r.cnst.name = some (.recr r) := by simp only [memberOf, hget]
    exact term_good P hst he fun n hn => fold_member_names P hst (fun _ h => by cases h) hmem
      (by simpa [BlockEmission.memberSources, termsOf] using he) hn
  refine ⟨srcBlock_good str (fun v hv => ?_) (fun v hv => ?_) (fun cs hcs c hc => ?_) (fun cs hcs c hc => ?_)
    (fun r hr => named _ ((TraceSegments.inductive_names types ctors recs _).mpr ?_)) recTerm
    (fun r hr rule hrule => ?_), fun x hx rr hrr => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := typeIdx v hv
    exact named _ ((TraceSegments.inductive_names types ctors recs _).mpr (.inl ⟨j, hj, rfl⟩))
  · obtain ⟨j, hj, rfl⟩ := typeIdx v hv
    exact term_good P (typeGet j hj).2 (by simp [termsOf, Ix.ConstantInfo.getCnst])
      (typeTerm j hj _ (by simp [BlockEmission.memberSources, InductiveCompile.indOf]))
  · obtain ⟨j, hj, rfl⟩ := ctorIdx cs hcs
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact named _ ((TraceSegments.inductive_names types ctors recs _).mpr
      (.inr (.inl ⟨j, hj, k, by simpa using hk, by simp⟩)))
  · obtain ⟨j, hj, rfl⟩ := ctorIdx cs hcs
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < ctors[j].size := by simpa using hk
    have hjT : j < types.size := by omega
    refine term_good P (ctorStored j hj k hk') (by simp [termsOf, Ix.ConstantInfo.getCnst]) ?_
    refine typeTerm j hjT _ ?_
    simp only [BlockEmission.memberSources, InductiveCompile.indOf, List.mem_cons, List.mem_map,
      Array.mem_toList_iff]
    exact .inr ⟨ctors[j][k], Array.getElem_mem hk', by simp⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    exact .inr (.inr ⟨j, by simpa using hj, by simp⟩)
  · have hst := recStored r hr
    obtain ⟨cin, hcin⟩ := familyNamesStored P.compiled _ _ (SourceStoredNames.stored_input P hst) rule.ctor
      (by simp [familyNamesOf]; exact .inr ⟨rule, Array.mem_toList_iff.mp hrule, rfl⟩)
    exact key_good P (published_of_ref P hst (RecursorIndex.refsOf_rule r hrule) ⟨cin, hcin⟩)
  · simp only [InductiveUnits.srcBlock, List.toList_toArray, List.mem_map] at hx
    obtain ⟨r, -, rfl⟩ := hx
    simp only [InductiveUnits.srcRec, List.mem_map] at hrr
    obtain ⟨rule, -, rfl⟩ := hrr
    rfl

/-- **Every group of quotient Source's graph that converts lies in the scope of representatives**
(`TraceSegments.TraceNeeds.good`): its conversion is in the scope of input keys, since every name
its constants reference is published, and quotient Source's renaming onto representatives and
canonical levels keep it there. -/
theorem converted_good (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {gr : Group} {c : Converted} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr)
    (hconv : Ix.LeanIngress.convert gr = .ok c) :
    ConvGood (TraceSegments.scope ixe t) ((c.withHints hints).quotient (TraceSegments.fibers ixe t)) := by
  have hb := tableBound_of (defaultTable_check P.table) P.bound
  have inScope : ConvGood (KeyScope.ofId (QIn ixe)) c ∧ Inert c := by
    cases gr with
    | invalid ns e => simp [Ix.LeanIngress.convert, throw, throwThe, MonadExceptOf.throw] at hconv
    | definitions members => exact definitions_good P hgr hconv
    | «axiom» v => exact axiom_good P scheduled hgr hconv
    | quot v => exact quot_good P scheduled hgr hconv
    | «inductive» types ctors recs => exact inductive_good P hgr hconv
  exact convGood_quotient hb hints inScope.1 inScope.2

end Groups

/--
info: 'Ix.Cert.TraceGood.converted_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms converted_good

end Ix.Cert.TraceGood
