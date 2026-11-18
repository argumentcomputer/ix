import IxVMRefinement.Core.Registry

/-! # The firing of the projection guards, and the load contract that carries it

The projection step of the registry (`infer_proj_common`) owes, at a projection out of a
propositional structure, the rules tier's firing condition `Ix.Kernel.Rules.FireSem` of the
table entry at the use's levels. What decides it is a reading of the run of
`KernelInfer::proj_guard`, which needs the registry's induction hypothesis; so the firing
cannot be stated before the registry, among the facts its steps are proved from
(`ScopedCoreBase`), and it is not stated over a limit.

* `ProjGuardFires c`: the firing at one context, as the projection step consumes it. It is the
  second hypothesis of the registry (`scoped_steps_base`).
* `ProjTableFires t E k tbl kc cvC`, `ProjTablesFire t E env`: the same with no context fixed,
  one stored table at a time, at every context over a role table and a store that stores the
  table and its constructor. This form names no limit, no call scope and no keying; it is kept
  by every step of the environment that keeps the lookups (`ProjTablesFire.step`), and it gives
  the firing at any context that stores the tables (`ProjTablesFire.fires`).
* `ScopedLoadFacts c`: the load contract a prefix carries, `ScopedLoadBase c` with
  `ProjTablesFire` at the context's table, store and environment; `ScopedCoreFacts c`: the
  facts the registry is run with above this file, the environment facts with that contract
  (`ScopedCoreFacts.base`, `ScopedCoreFacts.fires` give the registry's two hypotheses).
* `LoadFacts.projGuardFires`: the unrestricted contract of the seams instance still holds the
  guard of each `proj_guard` run at its own limit; it gives the firing at the unrestricted
  context.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **The projection guards fire at the context `c`**: for every run of
`KernelInfer::proj_guard` shorter than the calls the registry's induction hypothesis covers, at
member `i` of the block `b` whose inductive, first constructor and projection table the
environment stores and whose projection record the store holds, a returned level that is zero at
the use's levels gives the rules tier's firing condition of the table's entry at those levels.

The hypotheses are what the projection step has in hand, the observed load of the member's
constructor (`KernelModeled::proj_ctor`) among them. The statement is relative to the context
(its environment, keying, limit and call scope) through the induction hypothesis, so it is read
at each context off a statement that mentions none of them (`ProjTablesFire.fires`). -/
def ProjGuardFires (c : ScopedCtx) : Prop :=
  ∀ {calls0 : List (Call F)} (ih : IH c calls0)
    {x_rc x_block r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {i f : F}
    (hlt0 : calls.length < calls0.length) (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, .field i, .field f] h r h' calls)
    {b : Bytes.Address} (hrc : c.rc h x_rc)
    (hb : Bytes.RepAddressRef addrTy h b x_block)
    {x_blockC ptrC : SourceValue F} {hC hC' : Heap F} {csC : List (Call F)}
    (evC : ObsFn W "KernelModeled::proj_ctor" [x_blockC, .field i] hC ptrC hC' csC)
    (goodC : Good c.toCtx csC) (hbC : Bytes.RepAddressRef addrTy hC b x_blockC)
    {cvT : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hind : c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps))
    {cm : Ixon.Constant}
    (hrec : Ix.Cert.recordAt c.E (iprjAddr (ixAddr b) (ZMod.val i)) = some cm)
    (hinfo : cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩)
    {cvC : Ix.Kernel.ConstantVal .anon} {nP nF : Nat} {tbl : Ix.Kernel.ProjTable .anon}
    (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nP nF))
    (htbl : c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
      some (.projInfo tbl))
    (hnP : tbl.numParams = nP) (hnF : tbl.numFields = nF) (hf : ZMod.val f < nF)
    {g : KLevel} (hg : RepKLevel h' g r)
    {us : List KLevel} (hus : us.length = tbl.levelParams.length)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us g) = 0),
    Ix.Kernel.Rules.FireSem (tbl.entry (ZMod.val f)) us

/-! ## With no context: one stored table at every context -/

/-- **The stored projection table `tbl` of the structure at the key `k`, whose constructor
`cvC` is stored at `kc`, fires at every context** over the role table `t` and the store `E`:
at each context that stores the table and that constructor and has its core facts, a run of
`KernelInfer::proj_guard` at a member whose key is `k` fires the table's entry, as in
`ProjGuardFires`.

No limit, call scope or environment is fixed: the statement is kept by every extension of the
environment and by every change of limit. It is what a certificate of the table and the reading
of a use give of one table. -/
def ProjTableFires (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (k : KKey)
    (tbl : Ix.Kernel.ProjTable .anon) (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) : Prop :=
  ∀ (c : ScopedCtx), c.t = t → c.E = E → ScopedCoreBase c →
    c.env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
    (∃ nP nF : Nat, c.env.find? kc = some (.ctorInfo cvC nP nF)) →
    ∀ {calls0 : List (Call F)} (ih : IH c calls0)
      {x_rc x_block r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {i f : F}
      (hlt0 : calls.length < calls0.length) (good : CoreGood c calls)
      (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, .field i, .field f] h r h' calls)
      {b : Bytes.Address} (hrc : c.rc h x_rc)
      (hb : Bytes.RepAddressRef addrTy h b x_block)
      {cvT : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
      (hind : c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps))
      {cm : Ixon.Constant}
      (hrec : Ix.Cert.recordAt c.E (iprjAddr (ixAddr b) (ZMod.val i)) = some cm)
      (hinfo : cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩)
      (hk : c.κ (iprjAddr (ixAddr b) (ZMod.val i)) = k)
      {cvC' : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
      (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
        some (.ctorInfo cvC' nP nF))
      (hnP : tbl.numParams = nP) (hnF : tbl.numFields = nF) (hf : ZMod.val f < nF)
      {g : KLevel} (hg : RepKLevel h' g r)
      {us : List KLevel} (hus : us.length = tbl.levelParams.length)
      (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us g) = 0),
      Ix.Kernel.Rules.FireSem (tbl.entry (ZMod.val f)) us

/-- **Every projection table of a propositional structure that `env` stores fires at every
context** over `t` and `E`, with its stored constructor. No limit occurs. -/
def ProjTablesFire (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
    env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
    Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
    ∃ (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      env.find? kc = some (.ctorInfo cvC nP nF) ∧ ProjTableFires t E k tbl kc cvC

/-- **The tables of a context's environment firing everywhere give the firing at the context**:
what the registry's projection step consumes, read off the limit-free statement at the
context's own core facts. -/
theorem ProjTablesFire.fires {c : ScopedCtx} (hT : ProjTablesFire c.t c.E c.env)
    (hc : ScopedCoreBase c) : ProjGuardFires c := by
  intro calls0 ih x_rc x_block r h h' calls i f hlt0 good ev b hrc hb x_blockC ptrC hC hC' csC
    evC goodC hbC cvT caps hind cm hrec hinfo cvC nP nF tbl hctor htbl hnP hnF hf g hg us hus
    hzero hprop
  have hprop' : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true := hprop
  obtain ⟨kc, cvC₀, nP₀, nF₀, hkc, hfires⟩ := hT _ tbl htbl hprop'
  exact hfires c rfl rfl hc htbl ⟨nP₀, nF₀, hkc⟩ ih hlt0 good ev hrc hb hind hrec hinfo rfl hctor
    hnP hnF hf hg hus hzero hprop

/-- **A step of the environment keeps the tables firing**: the step keeps every lookup, and a
table of a propositional structure it stores new comes with its stored constructor and its own
firing. A step that stores no such table needs nothing; no limit is involved. -/
theorem ProjTablesFire.step {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} (h : ProjTablesFire t E env)
    (hfind : ∀ (k : KKey) (ci : Ix.Kernel.ConstantInfo .anon),
      env.find? k = some ci → env₂.find? k = some ci)
    (hnew : ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
      env₂.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
      Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
      env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) ∨
      ∃ (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
        env₂.find? kc = some (.ctorInfo cvC nP nF) ∧ ProjTableFires t E k tbl kc cvC) :
    ProjTablesFire t E env₂ := by
  intro k tbl htbl hprop
  rcases hnew k tbl htbl hprop with hold | hn
  · obtain ⟨kc, cvC, nP, nF, hkc, hf⟩ := h k tbl hold hprop
    exact ⟨kc, cvC, nP, nF, hfind _ _ hkc, hf⟩
  · exact hn

/-- **A step that keeps every lookup and stores no new projection table keeps the tables
firing.** -/
theorem ProjTablesFire.keep {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} (h : ProjTablesFire t E env)
    (hfind : ∀ (k : KKey) (ci : Ix.Kernel.ConstantInfo .anon),
      env.find? k = some ci → env₂.find? k = some ci)
    (hold : ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
      env₂.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
      env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl)) :
    ProjTablesFire t E env₂ :=
  h.step hfind (fun k tbl htbl _ => Or.inl (hold k tbl htbl))

/-- An environment that stores no projection table has every stored table firing. -/
theorem projTablesFire_of_noTable {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (h : ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
      env.find? (Ix.Kernel.projTableName k) ≠ some (.projInfo tbl)) :
    ProjTablesFire t E env :=
  fun k tbl htbl _ => (h k tbl htbl).elim

/-! ## The load contract a prefix carries -/

/-- **The load contract with the firing of the stored projection tables.** `ScopedLoadBase c`
is what the registry's own facts hold; this is what a prefix carries and what the callers of the
registry pass: the same, with every projection table of a propositional structure the
environment stores firing at every context over the context's role table and store. The added
clause names no limit. -/
structure ScopedLoadFacts (c : ScopedCtx) : Prop extends ScopedLoadBase c where
  /-- Every stored projection table of a propositional structure fires at every context. -/
  projFire : ProjTablesFire c.t c.E c.env

/-- **Context evidence for scoped registry runs, as a prefix carries it**: the environment facts
and the load contract with the firing of the stored projection tables. The registry's steps are
proved from its part before the registry (`ScopedCoreFacts.base`) and the firing at the context
(`ScopedCoreFacts.fires`). -/
structure ScopedCoreFacts (c : ScopedCtx) : Prop where
  env : CoreEnvFacts c.toCtx
  loads : ScopedLoadFacts c

/-- The part of the facts stated before the registry. -/
theorem ScopedCoreFacts.base {c : ScopedCtx} (hc : ScopedCoreFacts c) : ScopedCoreBase c :=
  ⟨hc.env, hc.loads.toScopedLoadBase⟩

/-- A lemma stated before the registry takes the facts a prefix carries: they are read as their
part before the registry. -/
instance {c : ScopedCtx} : Coe (ScopedCoreFacts c) (ScopedCoreBase c) := ⟨ScopedCoreFacts.base⟩

/-- The firing of the projection guards at the context, read off the load contract. -/
theorem ScopedCoreFacts.fires {c : ScopedCtx} (hc : ScopedCoreFacts c) : ProjGuardFires c :=
  hc.loads.projFire.fires hc.base

/-- What the environment stores under the context's keying resolves. -/
theorem ScopedCoreFacts.res_of_find {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : c.env.find? (c.κ a) = some ci) : c.κ a ≠ unresolvedKey :=
  hc.base.res_of_find h

/-- A key the environment stores under the table's keying resolves, and the context keys it as
the table does. -/
theorem ScopedCoreFacts.key_of_stored {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : c.env.find? (keyOf c.t a) = some ci) : c.κ a = keyOf c.t a :=
  hc.base.key_of_stored h

/-- The inductive a stored inductive names resolves. -/
theorem ScopedCoreFacts.res_of_ind {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a b : _root_.Address} {i : Nat} {cv : Ix.Kernel.ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon}
    (hfind : c.env.find? (c.κ a) = some (.indInfo cv caps))
    (hname : cv.name = c.κ (iprjAddr b i)) : c.κ (iprjAddr b i) ≠ unresolvedKey :=
  hc.base.res_of_ind hfind hname

/-- The inductive of a stored constructor resolves. -/
theorem ScopedCoreFacts.res_of_ctor {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a b : _root_.Address} {i j : Nat} {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (hfind : c.env.find? (c.κ a) = some (.ctorInfo cv nP nF))
    (hname : cv.name = c.κ (cprjAddr b i j)) (hb : HashedBlockAt c.E b) :
    c.κ (iprjAddr b i) ≠ unresolvedKey :=
  hc.base.res_of_ctor hfind hname hb

/-- The inductive of a stored constructor permits projection, at the address it is stored
under. -/
theorem ScopedCoreFacts.perm_of_ctor {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a ac b : _root_.Address} {i j : Nat} {cvT : Ix.Kernel.ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (hfindI : c.env.find? (c.κ a) = some (.indInfo cvT caps))
    (hnameI : cvT.name = c.κ (iprjAddr b i))
    (hfindC : c.env.find? (c.κ ac) = some (.ctorInfo cv nP nF))
    (hnameC : cv.name = c.κ (cprjAddr b i j)) (hb : HashedBlockAt c.E b) :
    ProjPermitted c.κ a :=
  hc.base.perm_of_ctor hfindI hnameI hfindC hnameC hb

/-- The address a role in force is bound to resolves. -/
theorem ScopedCoreFacts.res_of_role {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {r : Ix.Kernel.Role} {a : _root_.Address} (hb : c.t.addressOf? r = some a)
    (hf : c.inForce r) (hi : fabricatedRole r = true) : c.κ a ≠ unresolvedKey :=
  hc.base.res_of_role hb hf hi

/-! ## The unrestricted contract of the seams instance -/

/-- **The unrestricted load contract gives the firing at the unrestricted context**: its guard
clause is stated for each `proj_guard` run at the context's own limit, keyed on the observed
load of the member's constructor. -/
theorem LoadFacts.projGuardFires {c : Ctx} (hl : LoadFacts c) :
    ProjGuardFires (ScopedCtx.unrestricted c) := by
  intro calls0 ih x_rc x_block r h h' calls i f hlt0 good ev b hrc hb x_blockC ptrC hC hC' csC
    evC goodC hbC cvT caps hind cm hrec hinfo cvC nP nF tbl hctor htbl hnP hnF hf g hg us hus
    hzero hprop φ
  have hprop' : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true := hprop
  exact (hl.projTablesGuard x_blockC (.field i) ptrC hC hC' csC b i evC goodC hbC rfl 0 cvC nP nF
    tbl hctor htbl).2 hprop' f x_rc x_block r h h' calls g us hf hus ev good.raw hrc hb hg hzero φ

end IxVM.Refinement.Core
