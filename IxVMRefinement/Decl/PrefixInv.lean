import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Decl.PrefixLoads
import IxVMRefinement.Core.Rekey
import IxVMRefinement.Whnf.Proj
import IxVMRefinement.L1.Cells

/-! # The standing invariant of a prefix

`PrefixInv E t lim env` is what a declaration step reads of the prefix `env` it runs against, for
the records `E`, the role table `t` and the group limit `lim` of the declarations being folded:

* the declaration layer's invariant (`FullDeclInv`, and its store part `FoldStoreInv`);
* the table's well-formedness;
* the companions of the scoped core's environment facts, at the limit;
* the scoped load contract at the prefix context `Ctx.stored`, whose keying resolves exactly the
  stored addresses. Its closing facts say that the unresolved key is not stored, that a stored
  constructor's inductive resolves, and that a role in force that is no inert axiom is stored;
* the stability of η typing under extension (`EtaStable`), which the η fields of the load
  contract need when the environment grows.

`prefixInv_empty` proves it at the empty environment under the limit `0`, for every well-formed
table. `PrefixInv.cons_value` proves that storing a definition, a theorem or an axiom at a fresh
key keeps it, given that the new record reloads as the constant stored (`hreload`): every other
clause is derived. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal ConstantInfo RecRule IndCaps BasisKind Expr)

universe u

set_option linter.unusedVariables false

/-! ## One more constant -/

/-- The context after one constant is stored. -/
abbrev consCtx (c : Ctx) (cn : ConstantInfo .anon) : Ctx :=
  ⟨c.E, ⟨cn :: c.env.consts⟩, c.t, c.lim⟩

section
variable {c : Ctx} {cn : ConstantInfo .anon}

/-- **A stage over a larger environment and a larger prefix keeps every key the smaller one
resolves.** -/
theorem stagedOver_keep {c₁ c₂ : Ctx} {pre₁ pre₂ : Ix.Kernel.Env .anon} (ht : c₂.t = c₁.t)
    (henv : ∀ {k : KKey} {ci : ConstantInfo .anon}, c₁.env.find? k = some ci →
      ∃ ci', c₂.env.find? k = some ci')
    (hpre : ∀ {k : KKey} {ci : ConstantInfo .anon}, pre₁.find? k = some ci →
      ∃ ci', pre₂.find? k = some ci')
    (x : _root_.Address) (h : (c₁.stagedOver pre₁).κ x ≠ unresolvedKey) :
    (c₂.stagedOver pre₂).κ x = (c₁.stagedOver pre₁).κ x := by
  have h' : resKey c₁.t (c₁.resolvesOver pre₁) x ≠ unresolvedKey := h
  have hr := res_of_resKey_ne h'
  have hr₂ : c₂.resolvesOver pre₂ x := by
    rcases hr with ⟨ci, hci⟩ | ⟨y, hy, ci, hci⟩
    · obtain ⟨ci', hci'⟩ := henv hci
      exact Or.inl ⟨ci', by rw [ht]; exact hci'⟩
    · obtain ⟨ci', hci'⟩ := hpre hci
      exact Or.inr ⟨y, hy, ci', by rw [ht]; exact hci'⟩
  show resKey c₂.t (c₂.resolvesOver pre₂) x = resKey c₁.t (c₁.resolvesOver pre₁) x
  calc resKey c₂.t (c₂.resolvesOver pre₂) x = keyOf c₂.t x := resKey_of_res hr₂
    _ = keyOf c₁.t x := by rw [ht]
    _ = resKey c₁.t (c₁.resolvesOver pre₁) x := (resKey_of_res hr).symm

/-- A fresh constant that is no projection table extends the environment. -/
theorem consCtx_ext (hfresh : c.env.find? cn.name = none)
    (hnt : ∀ T : KKey, cn.name ≠ Ix.Kernel.projTableName T) :
    Ix.Kernel.EnvExt c.env (consCtx c cn).env :=
  Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)

/-- What the longer environment stores, other than the new constant, the shorter one stores. -/
theorem consCtx_find_old {k : KKey} {x : ConstantInfo .anon}
    (hf : (consCtx c cn).env.find? k = some x) (hne : x ≠ cn) : c.env.find? k = some x := by
  have hf' : (⟨cn :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x := hf
  rw [Ix.Kernel.Env.find?_cons] at hf'
  split at hf'
  · exact absurd (Option.some.inj hf').symm hne
  · exact hf'

/-- A key the prefix resolves is kept by the longer prefix. -/
theorem consCtx_keep (hext : Ix.Kernel.EnvExt c.env (consCtx c cn).env) (x : _root_.Address)
    (h : c.stored.κ x ≠ unresolvedKey) : (consCtx c cn).stored.κ x = c.stored.κ x :=
  stagedOver_keep (c₁ := c) (c₂ := consCtx c cn) (pre₁ := c.env) (pre₂ := (consCtx c cn).env)
    rfl (fun hf => ⟨_, hext.find hf⟩) (fun hf => ⟨_, hext.find hf⟩) x h

/-- A key the longer prefix resolves, at an address a record can have, is the new constant's, or
one the prefix resolves. -/
theorem consCtx_split (x : _root_.Address) (hm : ¬ IsProjMarker x)
    (h : (consCtx c cn).stored.κ x ≠ unresolvedKey) :
    keyOf c.t x = cn.name ∨ c.stored.κ x ≠ unresolvedKey := by
  obtain ⟨ci, hci⟩ := Ctx.stored_key_ne h hm
  have hci' : (⟨cn :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? (keyOf c.t x) = some ci := hci
  by_cases e : cn.name = keyOf c.t x
  · exact Or.inl e.symm
  · rw [Ix.Kernel.Env.find?_cons, ite_eq_right e] at hci'
    refine Or.inr ?_
    rw [Ctx.stored_key_of_find hci']
    exact Resolved.ne

/-- **What the longer prefix stores at a context key, other than the new constant, the prefix
stores at the same key.** -/
theorem consCtx_old (h₁ : ScopedLoadFacts c.stored)
    (hext : Ix.Kernel.EnvExt c.env (consCtx c cn).env) {x : _root_.Address}
    {y : ConstantInfo .anon}
    (hf : (consCtx c cn).env.find? ((consCtx c cn).stored.κ x) = some y) (hne : y ≠ cn) :
    c.env.find? (c.stored.κ x) = some y ∧ (consCtx c cn).stored.κ x = c.stored.κ x := by
  have hfo := consCtx_find_old hf hne
  by_cases hr₂ : (consCtx c cn).stored.κ x = unresolvedKey
  · exfalso
    have hr₁ : c.stored.κ x = unresolvedKey := by
      by_contra hr
      exact hr ((consCtx_keep hext x hr).symm.trans hr₂)
    rw [hr₂, ← hr₁] at hfo
    exact h₁.findRes x y hfo hr₁
  · have e₂ : (consCtx c cn).stored.κ x = keyOf c.t x := (consCtx c cn).stored.key_eq hr₂
    rw [e₂] at hfo
    have e₁ : c.stored.κ x = keyOf c.t x := Ctx.stored_key_of_find hfo
    exact ⟨by rw [e₁]; exact hfo, e₂.trans e₁.symm⟩

/-- The name of a constant stored at a context key of the prefix resolves. -/
theorem stored_name_ne (h₁ : ScopedLoadFacts c.stored) {x : _root_.Address}
    {y : ConstantInfo .anon} (hf : c.env.find? (c.stored.κ x) = some y) :
    y.name ≠ unresolvedKey := by
  rw [WhnfAux.name_of_find hf]
  exact h₁.findRes x y hf

end

/-! ## η typing in every extension -/

/-- **η typing is stable**: for an η-capable family the environment stores, with its
constructor, the typing clause of `EtaUseFacts` holds in every extension of the environment. The
clause is an inversion on the constructor's stored type, which an extension keeps. -/
def EtaStable (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (T kc : KKey) (cvT cvc : ConstantVal .anon) (caps : IndCaps .anon) (nP nF : Nat),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ env' : Ix.Kernel.Env .anon, Ix.Kernel.EnvExt env env' →
      ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
        args.length = nP + nF →
        Ix.Kernel.Rules.Infer env' .io d (Ix.Kernel.Expr.mkAppN (.const kc us) args) ty →
          Ix.Kernel.Rules.Red env' d ty (Ix.Kernel.Expr.mkAppN (.const T us) (args.take nP))

theorem etaStable_empty : EtaStable Ix.Kernel.Env.empty := by
  intro T kc cvT cvc caps nP nF hT
  simp [Ix.Kernel.Env.find?, Ix.Kernel.Env.empty] at hT

/-- Storing a constant that is neither an inductive nor a constructor keeps η stability. -/
theorem EtaStable.cons_value {env : Ix.Kernel.Env .anon} (h : EtaStable env)
    {cn : ConstantInfo .anon} (hfresh : env.find? cn.name = none)
    (hnt : ∀ T : KKey, cn.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, cn ≠ .indInfo cv caps) (hctor : ∀ cv nP nF, cn ≠ .ctorInfo cv nP nF) :
    EtaStable ⟨cn :: env.consts⟩ := by
  intro T kc cvT cvc caps nP nF hT heta hkc hC env' hext'
  have hext : Ix.Kernel.EnvExt env ⟨cn :: env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hold : ∀ {k : KKey} {x : ConstantInfo .anon},
      (⟨cn :: env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x → x ≠ cn →
        env.find? k = some x := by
    intro k x hf hne
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact absurd (Option.some.inj hf).symm hne
    · exact hf
  exact h T kc cvT cvc caps nP nF (hold hT fun e => hind cvT caps e.symm) heta hkc
    (hold hC fun e => hctor cvc nP nF e.symm) env' (hext.trans hext')

/-! ## The load contract at the empty prefix -/

/-- **The load contract of the prefix context holds where nothing is stored and no role is in
force.** Every loader fact is conditional on a stored key; the record facts are L1's. -/
theorem storedLoads_of_empty {c : Ctx} (hdec : L1.EnvDecoded c.E)
    (henv : ∀ k, c.env.find? k = none) (hnf : ∀ r, ¬ c.inForce r) :
    ScopedLoadFacts c.stored := by
  have h₀ := prefixLoadFacts_of_empty hdec henv (fun _ => False)
    (ScopeResolved.of_no_loads fun _ h => h.elim)
  have nof : ∀ {k : KKey} {ci : ConstantInfo .anon}, c.env.find? k = some ci → False := by
    intro k ci h
    rw [henv] at h
    cases h
  have nores : ∀ {x : _root_.Address}, c.stored.κ x ≠ unresolvedKey → False := by
    intro x h
    have h' : resKey c.t (c.resolvesOver c.env) x ≠ unresolvedKey := h
    rcases res_of_resKey_ne h' with ⟨ci, hci⟩ | ⟨y, -, ci, hci⟩
    · exact nof hci
    · exact nof hci
  have nofam : ∀ {b : _root_.Address} {i : Nat}, c.stored.FamAt b i → False := by
    intro b i h
    rcases h with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
    · exact nof hf
    · exact nof hf
  exact
    { getCI := by
        intro addr ptr h h' cs a ev _ res _ _
        exact (nores res).elim
      getCprj := by
        intro bp ptr i j h h' cs b ev _ fam _ _
        exact (nofam fam).elim
      getIprj := by
        intro bp ptr i h h' cs b ev _ fam _ _
        exact (nofam fam).elim
      indRecord := h₀.indRecord
      inductRecord := by
        intro addr ptr h h' cs a nl ty np ni nc u blk idx ev _ res
        exact (nores res).elim
      projTables := by
        intro bp ip ptr h h' cs b i ev _ _ _ _ fam
        exact (nofam fam).elim
      projTablesAt := by
        intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i _ _ _ _ _ _ _ _ j cvC nP nF hf
        exact (nof hf).elim
      unitLike := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc _ _ _ _ _ hfT
        exact (nof hfT).elim
      unitLikeRaw := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps _ _ res
        exact (nores res).elim
      eta := by
        intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hfC
        exact (nof hfC).elim
      etaIota := by
        intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l _ _ _ _ _ hfT
        exact (nof hfT).elim
      recordShape := h₀.recordShape
      inductBlock := by
        intro addr ptr h h' cs a b nl ty np ni nc u blk i ev _ res
        exact (nores res).elim
      projTablesGuard := by
        intro bp ip ptr h h' cs b i _ _ _ _ j cvC nP nF tbl hf
        exact (nof hf).elim
      canonical := h₀.canonical
      storedRes := fun a ci hf => (nof hf).elim
      findRes := fun a ci hf => (nof hf).elim
      ctorIndRes := fun b i j cv nP nF hf => (nof hf).elim
      ctorIndPerm := fun a b i j cvT caps cv nP nF hf _ _ => (nof hf).elim
      roleRes := fun r a hf _ _ => (hnf r hf).elim }

/-! ## The load contract after a value constant -/

/-- **Storing a definition, a theorem or an axiom keeps the load contract of the prefix
context.** The new constant `cn` is stored at the fresh key of the address `a₀`; it is no
inductive, constructor or projection table. `hreload` is the one fact about the new record: a
load at its address returns the constant just stored. Every other clause follows from the
contract of the shorter prefix: a load at a key that was resolved before answers as before, and a
fact about a stored inductive, constructor or projection table speaks of constants of the
shorter prefix, because the guards name the kind of what is stored. -/
theorem storedLoads_cons_value {c : Ctx} (h₁ : ScopedLoadFacts c.stored)
    {cn : ConstantInfo .anon} {a₀ : _root_.Address}
    (hname : cn.name = keyOf c.t a₀)
    (hfresh : c.env.find? cn.name = none)
    (hnt : ∀ T : KKey, cn.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, cn ≠ .indInfo cv caps)
    (hctor : ∀ cv nP nF, cn ≠ .ctorInfo cv nP nF)
    (hproj : ∀ tbl, cn ≠ .projInfo tbl)
    (heta : EtaStable c.env)
    (hreload : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address),
      ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
      Bytes.RepAddressRef addrTy h a addr → keyOf c.t (ixAddr a) = cn.name →
      CIPtrRep (consCtx c cn).stored.κ h' ptr cn) :
    ScopedLoadFacts (consCtx c cn).stored := by
  have hext := consCtx_ext hfresh hnt
  have keep := consCtx_keep hext
  have old : ∀ {x : _root_.Address} {y : ConstantInfo .anon},
      (consCtx c cn).env.find? ((consCtx c cn).stored.κ x) = some y → y ≠ cn →
        c.env.find? (c.stored.κ x) = some y ∧ (consCtx c cn).stored.κ x = c.stored.κ x :=
    fun hf hne => consCtx_old h₁ hext hf hne
  have fam : ∀ {b : _root_.Address} {i : Nat}, (consCtx c cn).stored.FamAt b i →
      c.stored.FamAt b i := by
    intro b i hfam
    rcases hfam with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
    · exact Or.inl ⟨cv, caps, (old hf (fun e => hind cv caps e.symm)).1⟩
    · exact Or.inr ⟨j, cv, nP, nF, (old hf (fun e => hctor cv nP nF e.symm)).1⟩
  have famPerm : ∀ {b : _root_.Address} {i : Nat}, c.stored.FamAt b i →
      ProjPermitted c.stored.κ (iprjAddr b i) := by
    intro b i hfam
    have hr : c.stored.κ (iprjAddr b i) ≠ unresolvedKey := by
      rcases hfam with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
      · exact h₁.findRes _ _ hf
      · exact h₁.ctorIndRes _ _ _ _ _ _ hf
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr (iprjAddr_not_marker _ _)
    exact Ctx.stored_projPermitted_of_find hci
  have good₁ : ∀ {cs : List (Call F)}, CoreGood (consCtx c cn).stored cs → CoreGood c.stored cs :=
    fun g => ⟨g.noCollision, g.bounded, fun _ _ => trivial⟩
  have notInduct : ∀ {h' : Heap F} {ptr nl ty np ni nc u blk idx : SourceValue F},
      CIPtrRep (consCtx c cn).stored.κ h' ptr cn →
      loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
        False := by
    intro h' ptr nl ty np ni nc u blk idx hrep hld
    obtain ⟨v, hv, hci⟩ := hrep
    rw [hld] at hv
    injection hv with hv
    subst hv
    obtain ⟨cv, caps, _, _, _, e, _⟩ := WhnfAux.ind_inv hci
    exact hind cv caps e
  exact
    { getCI := by
        intro addr ptr h h' cs a ev _ res good ha
        rcases consCtx_split (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · refine ⟨cn, ?_, hreload addr ptr h h' cs a ev good.raw ha hnew⟩
          rw [(consCtx c cn).stored.key_eq res]
          show (⟨cn :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? (keyOf c.t (ixAddr a)) = some cn
          rw [hnew]
          exact Ix.Kernel.Env.find?_cons_self cn c.env
        · obtain ⟨ci, hf, hrep⟩ := h₁.getCI addr ptr h h' cs a ev trivial hold (good₁ good) ha
          refine ⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩
          rw [keep _ hold]
          exact hext.find hf
      getCprj := by
        intro bp ptr i j h h' cs b ev _ hfam good hb
        obtain ⟨⟨ci₀, hrep₀⟩, hall⟩ :=
          h₁.getCprj bp ptr i j h h' cs b ev trivial (fam hfam) (good₁ good) hb
        refine ⟨hrep₀.rekey_exists keep, fun cv nP nF hf => ?_⟩
        obtain ⟨hf₁, -⟩ := old hf (fun e => hctor cv nP nF e.symm)
        exact (hall cv nP nF hf₁).rekey_mono keep (stored_name_ne h₁ hf₁)
      getIprj := by
        intro bp ptr i h h' cs b ev _ hfam good hb
        obtain ⟨ci, hf, hrep⟩ :=
          h₁.getIprj bp ptr i h h' cs b ev trivial (fam hfam) (good₁ good) hb
        refine ⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩
        rw [keep _ (h₁.findRes _ _ hf)]
        exact hext.find hf
      indRecord := h₁.indRecord
      inductRecord := by
        intro addr ptr h h' cs a nl ty np ni nc u blk idx ev _ res good ha hld
        rcases consCtx_split (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · exact (notInduct (hreload addr ptr h h' cs a ev good ha hnew) hld).elim
        · exact h₁.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev trivial hold good
            ha hld
      projTables := by
        intro bp ip ptr h h' cs b i ev _ good hb hip hfam _
        obtain ⟨⟨ci, hf, hrep⟩, htab⟩ :=
          h₁.projTables bp ip ptr h h' cs b i ev trivial good hb hip (fam hfam)
            (famPerm (fam hfam))
        refine ⟨⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩, ?_⟩
        · rw [keep _ (h₁.findRes _ _ hf)]
          exact hext.find hf
        · intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor'
          obtain ⟨hc₁, ek⟩ := old hctor' (fun e => hctor cvC nP nF e.symm)
          obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
            htab sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hc₁
          have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
          refine ⟨tbl, ?_, ?_, ?_, ht4, ht5, ht6, ht7, ?_, ht9, ht10, ht11⟩
          · rw [ei]
            exact hext.find ht1
          · rw [ei]
            exact ht2
          · rw [ek]
            exact ht3
          · intro f hf'
            obtain ⟨hp, hth⟩ := ht8 f hf'
            exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
      projTablesAt := by
        intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG hs hld hblk
          j cvC nP nF hctor'
        obtain ⟨hc₁, ek⟩ := old hctor' (fun e => hctor cvC nP nF e.symm)
        obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
          h₁.projTablesAt bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG
            hs hld hblk j cvC nP nF hc₁
        have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
        refine ⟨tbl, ?_, ?_, ?_, ht4, ht5, ht6, ht7, ?_, ht9, ht10, ht11⟩
        · rw [ei]
          exact hext.find ht1
        · rw [ei]
          exact ht2
        · rw [ek]
          exact ht3
        · intro f hf'
          obtain ⟨hp, hth⟩ := ht8 f hf'
          exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
      unitLike := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc ev good ha hld hb hfT hfew hfC
        obtain ⟨hT₁, eT⟩ := old hfT (fun e => hind cvT caps e.symm)
        obtain ⟨hC₁, -⟩ := old hfC (fun e => hctor cvC nPc 0 e.symm)
        obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLike ap ptr h h' cs a nl ty u blk p i b cvT caps cvC
          nPc ev good ha hld hb hT₁ hfew hC₁
        refine ⟨hu1, hu2, ?_⟩
        rw [eT]
        exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      unitLikeRaw := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps ev _ _ good ha hld hb hfT hfew hz hn
        obtain ⟨hT₁, eT⟩ := old hfT (fun e => hind cvT caps e.symm)
        obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b cvT caps ev
          trivial (h₁.findRes _ _ hT₁) good ha hld hb hT₁ hfew
          ⟨hz.bp, hz.ptr, hz.before, hz.after, hz.calls, hz.observed, trivial, hz.good,
            hz.blockRep, hz.zeroFields⟩
          ⟨hn.ap, hn.before, hn.after, hn.calls, hn.observed, trivial, hn.good, hn.parentRep⟩
        refine ⟨hu1, hu2, ?_⟩
        rw [eT]
        exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      eta := by
        intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1
          hfC hnm hpos ev good hb hld hfT hmod hsort hnz hrec hsa
        obtain ⟨hC₁, eC⟩ := old hfC (fun e => hctor cvc cnP cnF e.symm)
        obtain ⟨hT₁, eT⟩ := old hfT (fun e => hind cvT caps e.symm)
        have hnC : cvc.name = (consCtx c cn).stored.κ (ixAddr ac) := WhnfAux.name_of_find hfC
        have hfC' : (consCtx c cn).env.find?
            ((consCtx c cn).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) =
              some (.ctorInfo cvc cnP cnF) := by
          rw [← hnm, hnC]
          exact hfC
        obtain ⟨-, eN⟩ := old hfC' (fun e => hctor cvc cnP cnF e.symm)
        obtain ⟨⟨he1, he2, he3, he4, he5⟩, huse⟩ := h₁.eta ac b sa i j cvc cvT caps cnP cnF us l
          bp ptr nl ty np u blk idx h1 h2 cs1 hC₁ (hnm.trans eN) hpos ev good hb hld hT₁ hmod
          hsort hnz hrec hsa
        refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5⟩, ?_⟩
        rw [eT, eC]
        exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
          heta _ _ cvT cvc caps cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      etaIota := by
        intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hb
          hfT hfC hmul hrec hsort hnz
        obtain ⟨hT₁, eT⟩ := old hfT (fun e => hind cvT caps e.symm)
        obtain ⟨hC₁, eC⟩ := old hfC (fun e => hctor cvc cnP cnF e.symm)
        obtain ⟨⟨he1, he2, he3, he4, he5, he6⟩, huse⟩ := h₁.etaIota pp ptr nl ty u blk h1 h2 cs1
          pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hb hT₁ hC₁ hmul hrec hsort hnz
        refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5, he6⟩, ?_⟩
        rw [eT, eC]
        exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
          heta _ _ cvT cvc caps cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      recordShape := h₁.recordShape
      inductBlock := by
        intro addr ptr h h' cs a b nl ty np ni nc u blk i ev _ res good ha hld hblk
        rcases consCtx_split (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · exact (notInduct (hreload addr ptr h h' cs a ev good ha hnew) hld).elim
        · exact h₁.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev trivial hold good
            ha hld hblk
      projTablesGuard := by
        intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor' htbl
        obtain ⟨hc₁, -⟩ := old hctor' (fun e => hctor cvC nP nF e.symm)
        have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
        rw [ei] at htbl
        exact h₁.projTablesGuard bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hc₁
          (consCtx_find_old htbl (fun e => hproj tbl e.symm))
      canonical := h₁.canonical
      storedRes := by
        intro a ci hf
        rw [Ctx.stored_key_of_find (c := consCtx c cn) hf]
        exact Resolved.ne
      findRes := by
        intro a ci hf
        by_cases e : ci = cn
        · rw [← WhnfAux.name_of_find hf, e, hname]
          exact Resolved.ne
        · rw [(old hf e).2]
          exact h₁.findRes a ci (old hf e).1
      ctorIndRes := by
        intro b i j cv nP nF hf
        obtain ⟨hf₁, -⟩ := old hf (fun e => hctor cv nP nF e.symm)
        have hr := h₁.ctorIndRes b i j cv nP nF hf₁
        rw [keep _ hr]
        exact hr
      ctorIndPerm := by
        intro a b i j cvT caps cv nP nF hf _ _
        obtain ⟨hf₁, -⟩ := old hf (fun e => hind cvT caps e.symm)
        have e₁ : c.stored.κ a = keyOf c.t a := c.stored.key_eq (h₁.findRes a _ hf₁)
        rw [e₁] at hf₁
        exact Ctx.stored_projPermitted_of_find (c := consCtx c cn) (hext.find hf₁)
      roleRes := by
        intro r a hf hi hb
        have hr := h₁.roleRes r a hf hi hb
        rw [keep _ hr]
        exact hr }

/-! ## The projection-table clause speaks of one-constructor members only -/

/-- **A load that returns an inductive with constructor count `1` reads a member whose record has
one constructor.** The projection-table clauses of the load contract are conditional on such a
load, so they say nothing of a family with two constructors: a prefix that stores one does not
falsify them. -/
theorem structLoad_one_ctor {c : ScopedCtx} (hl : ScopedLoadFacts c)
    {sap sptr nl ty np ni u blk idx : SourceValue F} {h1 h2 : Heap F} {cs1 : List (Call F)}
    {s : Bytes.Address}
    (ev : ObsFn W "Ingress::get_ci" [sap] h1 sptr h2 cs1) (hg : Good c.toCtx cs1)
    (hs : Bytes.RepAddressRef addrTy h1 s sap)
    (hld : loadValue h2 sptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, ni, .field 1, u, blk, idx]))
    {cm cb : Ixon.Constant} {p : Ixon.InductiveProj} {xs : Array Ixon.MutConst}
    {ind : Ixon.Inductive}
    (hcm : Ix.Cert.recordAt c.E (ixAddr s) = some cm) (hinfo : cm.info = .iPrj p)
    (hcb : Ix.Cert.recordAt c.E p.block = some cb) (hmuts : cb.info = .muts xs)
    (hind : xs[p.idx.toNat]? = some (.indc ind)) : ind.ctors.size = 1 := by
  obtain ⟨nl', ty', u', blk', b', hld', -, -, -, hsize⟩ :=
    hl.indRecord sap sptr h1 h2 cs1 s cm cb p xs ind ev hg hs hcm hinfo hcb hmuts hind
  rw [hld] at hld'
  injection hld' with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, -, -, -, hc, -, -, -⟩ := hargs
  have hsz : ind.ctors.size < 18446744069414584321 := lt_trans hsize (by norm_num)
  have h1 : ((1 : Nat) : F) = ((ind.ctors.size : Nat) : F) := by
    rw [Nat.cast_one]
    exact NatAux.field_inj hc
  exact ((NatAux.natCast_inj (by norm_num) hsz).mp h1).symm

/-! ## The references a record uses are stored -/

/-- **The references a record uses are stored**: every address at a used reference index of the
record has a constant in the environment. This is the form in which a declaration step takes the
claim layer's coverage and inert clauses. -/
def UsedRefsStored (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (c : Ixon.Constant) :
    Prop :=
  ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
    ∃ ci, env.find? (keyOf t x) = some ci

/-- The two clauses give it: a used reference that is no inert axiom's is stored (coverage), and
no used reference is an inert axiom's (inert). -/
theorem usedRefsStored_of_clauses {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {c : Ixon.Constant}
    (hcover : ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      IxVM.Consistency.inertKey (keyOf t x) = false → ∃ ci, env.find? (keyOf t x) = some ci)
    (hinert : ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      IxVM.Consistency.inertKey (keyOf t x) = false) : UsedRefsStored t env c :=
  fun i hi x hx => hcover i hi x hx (hinert i hi x hx)

/-- **A converted term of a record whose used references are stored is represented under the
prefix keying.** The expression `e` is one of the record's own (its reference indices are used
indices of the record) and has no recursion address. -/
theorem tmC_stored_of_usedRefs {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} {c : Ixon.Constant}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F} {X : KExpr}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e p)
    (he : ∀ i, i ∈ IxVM.Consistency.exprRefIdxs e → i ∈ IxVM.Consistency.usedRefIdxs c)
    (hstored : UsedRefsStored t env c) (rep : TmC (keyOf t) h X p) :
    TmC (Ctx.stored ⟨E₀, env, t, lim⟩).κ h X p := by
  have used : ∀ x, L1.RefUsed c.refs.toList c.sharing.toList e x →
      ∃ ci, env.find? (keyOf t x) = some ci := by
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · exact hstored i (he i hi) x hr
    · have hmem : i ∈ IxVM.Consistency.usedRefIdxs c := by
        unfold IxVM.Consistency.usedRefIdxs
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
      exact hstored i hmem x hr
  refine raw.tmC_rekey rep (fun x hu => ?_) (fun x hu => ?_)
  · rcases hu with hu | hr
    · obtain ⟨ci, hci⟩ := used x hu
      exact Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    · cases hr
  · obtain ⟨ci, hci⟩ := used x hu
    exact Ctx.stored_projPermitted_of_find (c := ⟨E₀, env, t, lim⟩) hci

/-! ## The invariant -/

/-- **Every load of the address of `cn` returns `cn`**, in any run good for the store `E`, under
the keying of the prefix `env` (which stores `cn`). The statement mentions no run of a check and
no group limit: it is a fact about the record at that address in `E`. -/
def ReloadsAs (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (cn : ConstantInfo .anon) : Prop :=
  ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good ⟨E, env, t, none⟩ cs →
    Bytes.RepAddressRef addrTy h a addr → keyOf t (ixAddr a) = cn.name →
    CIPtrRep (Ctx.stored ⟨E, env, t, none⟩).κ h' ptr cn

/-- **The standing invariant of a prefix** (module docstring). -/
structure PrefixInv (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (env : Ix.Kernel.Env .anon) : Prop where
  /-- The declaration layer's invariant, in every set theory. -/
  decl : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env
  /-- Its store part. -/
  store : FoldStoreInv env
  /-- The unresolved key is not stored. -/
  unresolved : env.find? unresolvedKey = none
  /-- The role table is well formed. -/
  tableWf : t.wf = true
  /-- The role and record companions of the scoped core's environment facts, at the limit. -/
  companions : CoreCompanions ⟨E, env, t, lim⟩
  /-- The scoped load contract at the prefix context. -/
  loads : ScopedLoadFacts (Ctx.stored ⟨E, env, t, lim⟩)
  /-- η typing of the stored η-capable families holds in every extension. -/
  etaStable : EtaStable env

/-- **The invariant holds at the empty environment under the limit `0`**, for decoded records and
any well-formed role table: nothing is stored and no role is in force. -/
theorem prefixInv_empty {E : Ixon.Env} (hdec : L1.EnvDecoded E) {t : Ix.Kernel.RoleTable}
    (htwf : t.wf = true) : PrefixInv.{u} E t (some 0) Ix.Kernel.Env.empty where
  decl := FullDeclInv.empty
  store := foldStoreInv_empty
  unresolved := rfl
  tableWf := htwf
  companions := coreCompanions_empty E t
  loads := storedLoads_of_empty (c := ⟨E, Ix.Kernel.Env.empty, t, some 0⟩) hdec (fun _ => rfl)
    (not_inForce_of_lim_zero rfl)
  etaStable := etaStable_empty

/-- The scoped core's facts at the prefix context. -/
theorem PrefixInv.scopedCoreFacts {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : PrefixInv.{u} E t lim env) :
    ScopedCoreFacts (Ctx.stored ⟨E, env, t, lim⟩) :=
  ⟨FoldStoreInv.toCoreEnvFacts (c := ⟨E, env, t, lim⟩) h.store h.tableWf h.companions,
    h.loads⟩

/-- **A stored constructor's inductive is stored**: the closing fact of the load contract, in the
table's keying. -/
theorem PrefixInv.ctor_ind_stored {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : PrefixInv.{u} E t lim env) {b : _root_.Address} {i j : Nat}
    {cv : ConstantVal .anon} {nP nF : Nat}
    (hf : env.find? (keyOf t (cprjAddr b i j)) = some (.ctorInfo cv nP nF)) :
    ∃ ci, env.find? (keyOf t (iprjAddr b i)) = some ci := by
  have hk : (Ctx.stored ⟨E, env, t, lim⟩).κ (cprjAddr b i j) = keyOf t (cprjAddr b i j) :=
    Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hf
  have hr := h.loads.ctorIndRes b i j cv nP nF (by rw [hk]; exact hf)
  exact Ctx.stored_key_ne hr (iprjAddr_not_marker _ _)

/-- **A value constant keeps the invariant.** Storing a definition, a theorem or an axiom `cn` at
the fresh key of the address `a₀` keeps `PrefixInv`, given the declaration layer's step
(`hdecl`, `hstore`) and the reload of the new record (`hreload`). -/
theorem PrefixInv.cons_value {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : PrefixInv.{u} E t lim env)
    {cn : ConstantInfo .anon} {a₀ : _root_.Address}
    (hname : cn.name = keyOf t a₀)
    (hfresh : env.find? cn.name = none)
    (hnt : ∀ T : KKey, cn.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, cn ≠ .indInfo cv caps)
    (hctor : ∀ cv nP nF, cn ≠ .ctorInfo cv nP nF)
    (hrec : ∀ cv mI rP rls, cn ≠ .recInfo cv mI rP rls)
    (hproj : ∀ tbl, cn ≠ .projInfo tbl)
    (hdecl : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env →
      FullDeclInv V ⟨cn :: env.consts⟩)
    (hstore : FoldStoreInv ⟨cn :: env.consts⟩)
    (hreload : ReloadsAs E t ⟨cn :: env.consts⟩ cn) :
    PrefixInv.{u} E t lim ⟨cn :: env.consts⟩ where
  decl := fun V _ => hdecl V (h.decl V)
  store := hstore
  unresolved := by
    have hne : cn.name ≠ unresolvedKey := by
      rw [hname]
      exact Resolved.ne
    show (⟨cn :: env.consts⟩ : Ix.Kernel.Env .anon).find? unresolvedKey = none
    rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]
    exact h.unresolved
  tableWf := h.tableWf
  companions := h.companions.cons_value hfresh hnt hrec hctor
  loads := storedLoads_cons_value (c := ⟨E, env, t, lim⟩) h.loads hname hfresh hnt hind
    hctor hproj h.etaStable hreload
  etaStable := h.etaStable.cons_value hfresh hnt hind hctor

end IxVM.Refinement.Decl
