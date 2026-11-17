import IxVMRefinement.Core.CallScope
import IxVMRefinement.Assembly.LoadGlue
import IxVMRefinement.Decl.DeclsGlue

/-! # Load facts of a prefix, with no assumption about which calls occur

`ScopedLoadFacts c` speaks of the loads whose top call the scope `c.allowed` selects. Nothing in
it says which calls a run makes. This file separates the two halves of that contract.

* `ScopeResolved t env allowed`: every loader call the scope selects targets a key stored in
  `env` (for a constructor load, the inductive it belongs to). This is the property of a run: the
  loads it makes stay inside the prefix.
* `PrefixLoadFacts c`: for every scope that is resolved in this sense, the scoped load contract
  holds. This is a property of the records and the environment alone: no call list occurs in it,
  so it can be carried along a fold. Its installed-lookup claims are conditional on the key being
  stored, so it asserts nothing about a constant that is being checked and is not stored yet.

`prefixLoadFacts_of_empty` proves `PrefixLoadFacts` at an environment that stores nothing, from
the decoding of the records only: the contract is inhabited, and it is so at the start of every
fold. `CoreCompanions` are the fields of `CoreEnvFacts` that the store invariant does not give;
`FoldStoreInv.toCoreEnvFacts` assembles the scoped core's environment facts from them. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal ConstantInfo RecRule IndCaps BasisKind Expr)
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## The scope of a run stays inside the stored constants -/

/-- **Every loader call the scope selects targets a stored key.** `get_ci` at an address whose
key is stored; `get_ci_iprj` at a member whose inductive is stored; `get_ci_cprj` at a
constructor of a member whose inductive is stored; `proj_ctor` at a member whose first constructor
is stored. Calls of other functions are not constrained. -/
structure ScopeResolved (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (allowed : Call F → Prop) : Prop where
  getCI : ∀ (addr : SourceValue F) (h : Heap F) (a : Bytes.Address),
    allowed ⟨"Ingress::get_ci", [addr], h⟩ → Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, env.find? (keyOf t (ixAddr a)) = some ci
  getIprj : ∀ (bp : SourceValue F) (i : F) (h : Heap F) (b : Bytes.Address),
    allowed ⟨"Ingress::get_ci_iprj", [bp, .field i], h⟩ → Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, env.find? (keyOf t (iprjAddr (ixAddr b) (ZMod.val i))) = some ci
  getCprj : ∀ (bp : SourceValue F) (i j : F) (h : Heap F) (b : Bytes.Address),
    allowed ⟨"Ingress::get_ci_cprj", [bp, .field i, .field j], h⟩ →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, env.find? (keyOf t (iprjAddr (ixAddr b) (ZMod.val i))) = some ci
  projCtor : ∀ (bp : SourceValue F) (i : F) (h : Heap F) (b : Bytes.Address),
    allowed ⟨"KernelModeled::proj_ctor", [bp, .field i], h⟩ → Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, env.find? (keyOf t (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some ci

/-- A smaller scope is resolved when a larger one is. -/
theorem ScopeResolved.sub {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {allowed₁ allowed₂ : Call F → Prop} (h : ScopeResolved t env allowed₂)
    (hs : ∀ cl, allowed₁ cl → allowed₂ cl) : ScopeResolved t env allowed₁ where
  getCI := fun addr hp a hall ha => h.getCI addr hp a (hs _ hall) ha
  getIprj := fun bp i hp b hall hb => h.getIprj bp i hp b (hs _ hall) hb
  getCprj := fun bp i j hp b hall hb => h.getCprj bp i j hp b (hs _ hall) hb
  projCtor := fun bp i hp b hall hb => h.projCtor bp i hp b (hs _ hall) hb

/-- A scope resolved in an environment is resolved in every environment that keeps its keys. -/
theorem ScopeResolved.mono {t : Ix.Kernel.RoleTable} {env env₂ : Ix.Kernel.Env .anon}
    {allowed : Call F → Prop} (h : ScopeResolved t env allowed)
    (hk : ∀ k ci, env.find? k = some ci → ∃ ci₂, env₂.find? k = some ci₂) :
    ScopeResolved t env₂ allowed where
  getCI := fun addr hp a hall ha =>
    let ⟨ci, hci⟩ := h.getCI addr hp a hall ha
    hk _ ci hci
  getIprj := fun bp i hp b hall hb =>
    let ⟨ci, hci⟩ := h.getIprj bp i hp b hall hb
    hk _ ci hci
  getCprj := fun bp i j hp b hall hb =>
    let ⟨ci, hci⟩ := h.getCprj bp i j hp b hall hb
    hk _ ci hci
  projCtor := fun bp i hp b hall hb =>
    let ⟨ci, hci⟩ := h.projCtor bp i hp b hall hb
    hk _ ci hci

/-- A scope that selects no loader call is resolved in every environment. -/
theorem ScopeResolved.of_no_loads {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {allowed : Call F → Prop}
    (hno : ∀ cl, allowed cl → cl.name ≠ "Ingress::get_ci" ∧ cl.name ≠ "Ingress::get_ci_iprj" ∧
      cl.name ≠ "Ingress::get_ci_cprj" ∧ cl.name ≠ "KernelModeled::proj_ctor") :
    ScopeResolved t env allowed where
  getCI := fun _ _ _ hall _ => absurd rfl (hno _ hall).1
  getIprj := fun _ _ _ _ hall _ => absurd rfl (hno _ hall).2.1
  getCprj := fun _ _ _ _ _ hall _ => absurd rfl (hno _ hall).2.2.1
  projCtor := fun _ _ _ _ hall _ => absurd rfl (hno _ hall).2.2.2

/-! ## The load contract of a prefix -/

/-- **The loads read the prefix**: the scoped load contract holds at every scope whose loader
calls target stored keys. No call list occurs in the statement. -/
def PrefixLoadFacts (c : Ctx) : Prop :=
  ∀ allowed : Call F → Prop, ScopeResolved c.t c.env allowed →
    ScopedLoadFacts { toCtx := c, allowed := allowed }

/-- The scoped contract at the calls of a selected list, from the prefix contract and the
resolution of that list's loader calls. -/
theorem scopedLoadFacts_of_prefix {c : Ctx} (hp : PrefixLoadFacts c) {calls : List (Call F)}
    (hr : ScopeResolved c.t c.env (fun cl => cl ∈ calls)) :
    ScopedLoadFacts { toCtx := c, allowed := fun cl => cl ∈ calls } :=
  hp _ hr

private theorem noFind {c : Ctx} (henv : ∀ k, c.env.find? k = none) {k : KKey}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : c.env.find? k = some ci) : False := by
  rw [henv] at h
  cases h

private theorem decoded_of_recordAt {E : Ixon.Env} (hdec : L1.EnvDecoded E)
    {x : _root_.Address} {cm : Ixon.Constant} (hrec : Ix.Cert.recordAt E x = some cm) :
    ∀ lc, E.consts.get? x = some lc → Ixon.deConstantExact lc.rawBytes = .ok cm := by
  intro lc hlc
  obtain ⟨lc₀, hlc₀, _, hex, _⟩ := hdec.recordAt_deConstantExact hrec
  rw [hlc₀] at hlc
  cases hlc
  exact hex

/-- **The prefix contract holds where nothing is stored**, from the decoding of the records. Its
installed-lookup claims are vacuous there; its record claims (`indRecord`, `recordShape`,
`canonical`) are L1's. -/
theorem prefixLoadFacts_of_empty {c : Ctx} (hdec : L1.EnvDecoded c.E)
    (henv : ∀ k, c.env.find? k = none) : PrefixLoadFacts c := by
  intro allowed hres
  refine
    { getCI := ?_, getCprj := ?_, getIprj := ?_, indRecord := ?_, inductRecord := ?_,
      projTables := ?_, projTablesAt := ?_, unitLike := ?_, unitLikeRaw := ?_, eta := ?_,
      etaIota := ?_, recordShape := ?_, inductBlock := ?_, projTablesGuard := ?_,
      canonical := ?_, storedRes := fun _ _ _ => Resolved.ne, findRes := fun _ _ _ => Resolved.ne,
      ctorIndRes := fun _ _ _ _ _ _ _ => Resolved.ne, roleRes := fun _ _ _ _ _ => Resolved.ne }
  · intro addr ptr h h' cs a ev hall _ hg ha
    obtain ⟨ci, hci⟩ := hres.getCI addr h a hall ha
    exact (noFind henv hci).elim
  · intro bp ptr i j h h' cs b ev hall _ hg hb
    obtain ⟨ci, hci⟩ := hres.getCprj bp i j h b hall hb
    exact (noFind henv hci).elim
  · intro bp ptr i h h' cs b ev hall _ hg hb
    obtain ⟨ci, hci⟩ := hres.getIprj bp i h b hall hb
    exact (noFind henv hci).elim
  · intro addr ptr h h' cs a cm cb p xs ind ev hg ha hcm hcm_info hcb hcb_info hxs
    have hcm' : Ix.Cert.recordAt c.E (ixAddr a) = some cm := hcm
    have hcb' : Ix.Cert.recordAt c.E p.block = some cb := hcb
    have hg' : Good c cs := hg
    exact L1.indRecord_of_deConstantExact (c := c) (decoded_of_recordAt hdec hcm')
      (decoded_of_recordAt hdec hcb') ev hg' ha hcm' hcm_info hcb' hcb_info hxs
  · intro addr ptr h h' cs a nl ty np ni nc u blk idx ev hall _ hg ha hld
    obtain ⟨ci, hci⟩ := hres.getCI addr h a hall ha
    exact (noFind henv hci).elim
  · intro bp ip ptr h h' cs b i ev hall hg hb hip
    subst hip
    obtain ⟨ci, hci⟩ := hres.projCtor bp i h b hall hb
    exact (noFind henv hci).elim
  · intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i _ _ _ _ _ _ _ _ j cvC nP nF hctor
    exact (noFind henv hctor).elim
  · intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc _ _ _ _ _ hfind
    exact (noFind henv hfind).elim
  · intro ap ptr h h' cs a nl ty u blk p i b cvT caps _ _ _ _ _ _ _ hfind
    exact (noFind henv hfind).elim
  · intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hC
    exact (noFind henv hC).elim
  · intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l _ _ _ _ _ hT
    exact (noFind henv hT).elim
  · intro ap r h h' cs a cst ev hg ha hrec
    have hrec' : Ix.Cert.recordAt c.E (ixAddr a) = some cst := hrec
    have hg' : Good c cs := hg
    obtain ⟨lc₀, hlc₀, _, _, hde₀⟩ := hdec.recordAt_deConstantExact hrec'
    refine L1.recordShape_of_deConstant (c := c) (fun lc hlc => ?_) ev hg' ha hrec'
    rw [hlc₀] at hlc
    cases hlc
    exact hde₀
  · intro addr ptr h h' cs a b nl ty np ni nc u blk i ev hall _ hg ha hld hblk
    obtain ⟨ci, hci⟩ := hres.getCI addr h a hall ha
    exact (noFind henv hci).elim
  · intro bp ip ptr h h' cs b i _ _ _ _ j cvC nP nF tbl hctor
    exact (noFind henv hctor).elim
  · exact fun x lc info hwf hlc hraw cm hget => L1.canonical_of_wireWF hdec hwf hlc hraw hget

/-- The prefix contract at the empty environment. -/
theorem prefixLoadFacts_empty {E : Ixon.Env} (hdec : L1.EnvDecoded E) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) : PrefixLoadFacts ⟨E, Ix.Kernel.Env.empty, t, lim⟩ :=
  prefixLoadFacts_of_empty hdec (fun _ => rfl)

/-! ## The environment facts the store invariant does not give -/

/-- **Role and record companions of the scoped core's environment facts**: the fields of
`CoreEnvFacts` that `FoldStoreInv` does not supply. The scoped core reads no global
constructor-application typing fact, so none is listed (η evidence arrives with the observed
load). -/
structure CoreCompanions (c : Ctx) : Prop where
  natLit : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  strLit : c.inForce .string → Ix.Kernel.strLitSupported c.env = true
  natOps : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  natAdd : c.inForce .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  eqStored : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  quotBasis : c.inForce .quot → ∀ ci ∈ BasisKind.declsA (md := .anon) .quotK,
    c.env.find? ci.name = some ci
  recMajorRecord : ∀ k cv mI rP rls (p : _root_.Address) us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rls ≠ [] →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  recRulesNodupAndProj : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    (rls.map (·.ctor)).Nodup ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (us : List KLevel),
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (cprjAddr ip.block ip.idx.toNat j)
  recPlain : ∀ k cv mI rP rls rl cvj nP nF, c.env.find? k = some (.recInfo cv mI rP rls) →
    rl ∈ rls → rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    ∃ D T, piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  ruleCtorHead : ∀ k cv mI rP rls rl cvj nP nF T us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
    c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
    ∃ tus, (Expr.piResult cvj.type).getAppFn = .const T tus

/-- The scoped core's environment facts, from the store invariant, the table and the
companions. -/
theorem FoldStoreInv.toCoreEnvFacts {c : Ctx} (hS : FoldStoreInv c.env) (htwf : c.t.wf = true)
    (hR : CoreCompanions c) : CoreEnvFacts c where
  tableWf := htwf
  storeClosed := hS.storeClosed
  thmTyped := hS.thmTyped
  natLit := hR.natLit
  strLit := hR.strLit
  natOps := hR.natOps
  natAdd := hR.natAdd
  eqStored := hR.eqStored
  recRules := fun k cv mI rP rls hf =>
    let ⟨hnodup, hprj⟩ := hR.recRulesNodupAndProj k cv mI rP rls hf
    ⟨hnodup, fun rl hrl => hS.store.recRules_fire hf hrl, hprj⟩
  recPlain := hR.recPlain
  store := hS.store
  recMajorRecord := hR.recMajorRecord
  ruleCtorHead := hR.ruleCtorHead
  quotBasis := hR.quotBasis
  recEta := hS.recEta
  recArity := hS.recArity
  ruleCtorArity := hS.ruleCtorArity
  tableCtorArity := hS.tableCtorArity
  familyArity := hS.familyArity

/-- The companions hold where nothing is stored and no role is in force. -/
theorem coreCompanions_of_empty {c : Ctx} (henv : ∀ k, c.env.find? k = none)
    (hnf : ∀ r, ¬ c.inForce r) : CoreCompanions c where
  natLit := fun h _ _ => absurd h (hnf _)
  strLit := fun h => absurd h (hnf _)
  natOps := fun r h _ => absurd h (hnf r)
  natAdd := fun h => absurd h (hnf _)
  eqStored := fun h => absurd h (hnf _)
  quotBasis := fun h => absurd h (hnf _)
  recMajorRecord := fun k cv mI rP rls p us hf _ _ => (noFind henv hf).elim
  recRulesNodupAndProj := fun k cv mI rP rls hf => (noFind henv hf).elim
  recPlain := fun k cv mI rP rls rl cvj nP nF hf _ _ _ => (noFind henv hf).elim
  ruleCtorHead := fun k cv mI rP rls rl cvj nP nF T us hf _ _ _ => (noFind henv hf).elim

/-- **A value constant keeps the companions**: storing, at a fresh key that is no projection
table's, a constant that is neither a recursor nor a constructor (a definition, a theorem, an
axiom) preserves `CoreCompanions`. The role fields are monotone along the extension; the
recursor fields read only recursors and constructors, which are those of the prefix. -/
theorem CoreCompanions.cons_value {c : Ctx} (h : CoreCompanions c) {ci : ConstantInfo .anon}
    (hfresh : c.env.find? ci.name = none)
    (hnt : ∀ T : KKey, ci.name ≠ Ix.Kernel.projTableName T)
    (hrec : ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls)
    (hctor : ∀ cv nP nF, ci ≠ .ctorInfo cv nP nF) :
    CoreCompanions ⟨c.E, ⟨ci :: c.env.consts⟩, c.t, c.lim⟩ := by
  have hext : Ix.Kernel.EnvExt c.env ⟨ci :: c.env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hold : ∀ {k : KKey} {x : ConstantInfo .anon},
      (⟨ci :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x → x ≠ ci →
        c.env.find? k = some x := by
    intro k x hf hne
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact absurd (Option.some.inj hf).symm hne
    · exact hf
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := fun k cv mI rP rls p us hf hne hdom =>
        h.recMajorRecord k cv mI rP rls p us
          (hold hf (fun e => hrec cv mI rP rls e.symm)) hne hdom
      recRulesNodupAndProj := fun k cv mI rP rls hf =>
        h.recRulesNodupAndProj k cv mI rP rls (hold hf (fun e => hrec cv mI rP rls e.symm))
      recPlain := fun k cv mI rP rls rl cvj nP nF hf hrl hfire hc =>
        h.recPlain k cv mI rP rls rl cvj nP nF
          (hold hf (fun e => hrec cv mI rP rls e.symm)) hrl hfire
          (hold hc (fun e => hctor cvj nP nF e.symm))
      ruleCtorHead := fun k cv mI rP rls rl cvj nP nF T us hf hrl hc hdom =>
        h.ruleCtorHead k cv mI rP rls rl cvj nP nF T us
          (hold hf (fun e => hrec cv mI rP rls e.symm)) hrl
          (hold hc (fun e => hctor cvj nP nF e.symm)) hdom }

/-- No role is in force at the group limit `0`. -/
theorem not_inForce_of_lim_zero {c : Ctx} (hlim : c.lim = some 0) (r : Ix.Kernel.Role) :
    ¬ c.inForce r :=
  fun h => Nat.not_lt_zero _ (h.2 0 hlim)

/-- The companions at the empty environment under the group limit `0`. -/
theorem coreCompanions_empty (E : Ixon.Env) (t : Ix.Kernel.RoleTable) :
    CoreCompanions ⟨E, Ix.Kernel.Env.empty, t, some 0⟩ :=
  coreCompanions_of_empty (fun _ => rfl) (not_inForce_of_lim_zero rfl)

end IxVM.Refinement.Decl
