import IxVMRefinement.Core.Good
import IxVMRefinement.Obs.KernelModeled
import IxVMRefinement.Obs.KernelModeled0

/-! # Core facts restricted to selected observed calls

Raw declaration traversal keeps `Good`. The registry uses `CoreGood` for its child-call
coverage, and installed loads separately require the exact top invocation to be allowed.
Legacy unrestricted facts embed explicitly; they are not used to establish actual coverage.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer)

/-- Environment facts used by the scoped core. Native eta shape is supplied only at its
observed route, rather than being required of every eta-capable reference declaration. -/
structure CoreEnvFacts (c : Ctx) : Prop where
  tableWf : c.t.wf = true
  storeClosed : Ix.Kernel.StoreClosed c.env
  thmTyped : ∀ n cv value, c.env.find? n = some (.thmInfo cv value) →
    value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
    ∃ vt s u, Infer c.env .full 0 value vt ∧ DefEq c.env 0 vt cv.type ∧
      Infer c.env .full 0 cv.type s ∧ Red c.env 0 s (.sort u) ∧
      ∀ φ, Ix.Kernel.Level.eval φ u = 0
  natLit : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  strLit : c.inForce .string → Ix.Kernel.strLitSupported c.env = true
  natOps : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  natAdd : c.inForce .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  eqStored : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  recRules : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    (rls.map (·.ctor)).Nodup ∧
    (∀ rl ∈ rls, rl.fire ≠ .inert ∧
      ∃ cvj nF, c.env.find? rl.ctor = some (.ctorInfo cvj rl.ctorParams nF)) ∧
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
  store : Ix.Kernel.Open.StoreInv c.env
  recMajorRecord : ∀ k cv mI rP rls (p : _root_.Address) us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rls ≠ [] →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  ruleCtorHead : ∀ k cv mI rP rls rl cvj nP nF T us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
    c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
    ∃ tus, (Ix.Kernel.Expr.piResult cvj.type).getAppFn = .const T tus
  quotBasis : c.inForce .quot → ∀ ci ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .quotK,
    c.env.find? ci.name = some ci
  recEta : ∀ k cv mI rP rl, c.env.find? k = some (.recInfo cv mI rP [rl]) →
    rl.eta = Ix.Kernel.recRuleEtaOf c.env.find? k rl.ctor
  recArity : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
    (cv.type.stripPis (mI + 1)).isSome = true
  ruleCtorArity : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
    ∀ cvj nP nF, c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
      nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true
  tableCtorArity : ∀ sn i entry, c.env.findProj? sn i = some entry →
    ∀ cvC nP nF, c.env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
      nP = entry.numParams ∧ nF = entry.numFields ∧ (cvC.type.stripPis (nP + nF)).isSome = true
  familyArity : ∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) →
    (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
      (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true)

theorem EnvFacts.toCoreEnvFacts {c : Ctx} (h : EnvFacts c) : CoreEnvFacts c where
  tableWf := h.tableWf
  storeClosed := h.storeClosed
  thmTyped := h.thmTyped
  natLit := h.natLit
  strLit := h.strLit
  natOps := h.natOps
  natAdd := h.natAdd
  eqStored := h.eqStored
  recRules := h.recRules
  recPlain := h.recPlain
  store := h.store
  recMajorRecord := h.recMajorRecord
  ruleCtorHead := h.ruleCtorHead
  quotBasis := h.quotBasis
  recEta := h.recEta
  recArity := h.recArity
  ruleCtorArity := h.ruleCtorArity
  tableCtorArity := h.tableCtorArity
  familyArity := h.familyArity

/-- Weak goodness together with coverage of the exact child calls. The first two fields
retain the collision and resource projections used throughout the core proofs. -/
structure CoreGood (c : ScopedCtx) (calls : List (Call F)) : Prop where
  noCollision : ¬ View.HashedCollision { env := c.E } [] calls
  bounded : IxVM.Consistency.Bounded calls
  allAllowed : ∀ cl ∈ calls, c.allowed cl

theorem CoreGood.raw {c : ScopedCtx} {cs : List (Call F)} (h : CoreGood c cs) :
    Good c.toCtx cs := ⟨h.noCollision, h.bounded⟩

theorem CoreGood.ofRaw {c : ScopedCtx} {cs : List (Call F)} (h : Good c.toCtx cs)
    (ha : ∀ cl ∈ cs, c.allowed cl) : CoreGood c cs := ⟨h.1, h.2, ha⟩

theorem CoreGood.sub {c : ScopedCtx} {cs calls : List (Call F)} (h : CoreGood c calls)
    (hs : ∀ cl ∈ cs, cl ∈ calls) : CoreGood c cs :=
  CoreGood.ofRaw (h.raw.sub hs) (fun cl hc => h.allAllowed cl (hs cl hc))

theorem CoreGood.allowedTop {c : ScopedCtx} {calls : List (Call F)} (h : CoreGood c calls)
    {fname : String} {args : List (SourceValue F)} {heap : Heap F}
    (hm : (⟨fname, args, heap⟩ : Call F) ∈ calls) : c.allowedTop fname args heap :=
  h.allAllowed _ hm

theorem CoreGood.unrestricted {c : Ctx} {calls : List (Call F)} (h : Good c calls) :
    CoreGood (ScopedCtx.unrestricted c) calls := ⟨h.1, h.2, fun _ _ => trivial⟩

/-- The eta facts needed at a concrete native observation. Stored typing and the global
store invariant remain separate; no claim is made about unrelated eta-capable families. -/
structure EtaUseFacts (env : Ix.Kernel.Env .anon) (T kc : KKey)
    (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon) (nP nF : Nat) : Prop where
  towers : Ix.Kernel.towerSlotsAll env T caps.etaFields = true
  sort : ∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
    caps.sortZ = Ix.Kernel.Level.zeronessOf l
  type : ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
    args.length = nP + nF → Infer env .io d (Ix.Kernel.Expr.mkAppN (.const kc us) args) ty →
      Red env d ty (Ix.Kernel.Expr.mkAppN (.const T us) (args.take nP))

theorem EnvFacts.etaUseFacts {c : Ctx} (h : EnvFacts c)
    {T kc : KKey} {cvT cvc : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    {nP nF : Nat} (hT : c.env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hC : c.env.find? kc = some (.ctorInfo cvc nP nF)) :
    EtaUseFacts c.env T kc cvT caps nP nF :=
  ⟨h.etaTowers T cvT caps hT heta, h.etaSort T cvT caps hT heta,
    h.etaType T kc cvT cvc caps nP nF hT heta hctor hC⟩

/-- A selected metadata read of a zero-field constructor. It makes no assertion that the
constructor is already installed in the semantic environment. -/
structure ZeroFieldCtorLoad (c : ScopedCtx) (block : Bytes.Address) (ind : F) where
  bp : SourceValue F
  ptr : SourceValue F
  before : Heap F
  after : Heap F
  calls : List (Call F)
  observed : ObsFn W "Ingress::get_ci_cprj" [bp, .field ind, .field 0]
    before ptr after calls
  allowed : c.allowedTop "Ingress::get_ci_cprj" [bp, .field ind, .field 0] before
  good : Good c.toCtx calls
  blockRep : Bytes.RepAddressRef addrTy before block bp
  zeroFields : ∃ nl ty blk idx cidx np u,
    loadValue after ptr = .ok (.construct kciEnum "Ctor" [nl, ty, blk, idx, cidx, np, .field 0, u])

/-- The actual nonrecursive-structure observation used by unit-like conversion. -/
structure NonrecursiveLoad (c : ScopedCtx) (parent : Bytes.Address) where
  ap : SourceValue F
  before : Heap F
  after : Heap F
  calls : List (Call F)
  observed : ObsFn W "KernelWhnf::struct_is_rec" [ap] before (.field 0) after calls
  allowed : c.allowedTop "KernelWhnf::struct_is_rec" [ap] before
  good : Good c.toCtx calls
  parentRep : Bytes.RepAddressRef addrTy before parent ap

private theorem ctorZero_of_rep {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk idx cidx np u : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Ctor" [nl, ty, blk, idx, cidx, np, .field 0, u]) ci) :
    ∃ cv nP, ci = .ctorInfo cv nP 0 := by
  have castZero : ∀ n : Nat, n < 72057594037927936 →
      (.field (0 : F) : SourceValue F) = .field (n : F) → n = 0 := by
    intro n hn he
    have hsmall : n < 18446744069414584321 := Nat.lt_trans hn (by decide)
    have hv := congrArg (fun x : F => ZMod.val x) (Value.field.inj he)
    simpa only [ZMod.val_zero, ZMod.val_natCast_of_lt hsmall] using hv.symm
  generalize hv : (Value.construct kciEnum "Ctor"
    [nl, ty, blk, idx, cidx, np, .field 0, u] : SourceValue F) = v at r
  cases r
  case ctor hval hnp hnf hcounts hkey =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    have hnF := castZero _ hcounts.2 hnf
    cases hnF
    exact ⟨_, _, rfl⟩
  all_goals (injection hv with _ htag _; exact absurd htag (by decide))

/-- **The roles whose constants the checker builds or loads by role**: the `Nat` literal
constructors and type, the accelerated `Nat` operations (the offset rules rebuild their
applications), the `Bool` results of the comparisons, the constants a string literal expands
to and its type, and the quotient constructor and eliminators. A term the checker builds
mentions these constants, so their keys must resolve; no other role is asked for. -/
def fabricatedRole : Ix.Kernel.Role → Bool
  | .nat | .natZero | .natSucc | .natPred | .natAdd | .natSub | .natMul | .natDiv | .natMod
  | .natGcd | .natPow | .natLand | .natLor | .natXor | .natShiftLeft | .natShiftRight
  | .natBeq | .natBle | .boolFalse | .boolTrue | .string | .listNil | .listCons | .char
  | .charOfNat | .stringOfList | .quotMk | .quotLift | .quotInd => true
  | _ => false

/-- **`b` is the address of a block record a run hashed**: bounded calls that hash no collision
with the store `E` hash bytes that decode exactly to a `muts` record, and `b` is their hash. -/
def HashedBlockAt (E : Ixon.Env) (b : _root_.Address) : Prop :=
  ∃ (cs : List (Call F)) (blk : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
    ¬ View.HashedCollision { env := E } [] cs ∧ IxVM.Consistency.Bounded cs ∧
    Hashed cs blk ∧ Ixon.deConstantExact blk = .ok cb ∧ cb.info = .muts ms ∧
    Address.blake3Pure blk = b

theorem HashedBlockAt.of_good {c : Ctx} {cs : List (Call F)} (hg : Good c cs) {blk : ByteArray}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hh : Hashed cs blk)
    (hex : Ixon.deConstantExact blk = .ok cb) (hms : cb.info = .muts ms) {b : _root_.Address}
    (hb : Address.blake3Pure blk = b) : HashedBlockAt c.E b :=
  ⟨cs, blk, cb, ms, hg.1, hg.2, hh, hex, hms, hb⟩

/-- Installed reads require allowed top invocations and coverage of their children. Raw record facts stay
conditional on actual stored records, and native eta observations carry their own evidence. -/
structure ScopedLoadFacts (c : ScopedCtx) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → c.allowedTop "Ingress::get_ci" [addr] h →
      c.κ (ixAddr a) ≠ unresolvedKey → CoreGood c cs →
    Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → c.allowedTop "Ingress::get_ci_cprj" [bp, .field i, .field j] h →
      c.FamAt (ixAddr b) (ZMod.val i) → CoreGood c cs →
    Bytes.RepAddressRef addrTy h b bp →
      (∃ ci₀, CIPtrRep c.κ h' ptr ci₀) ∧
      ∀ cv nP nF, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) =
          some (.ctorInfo cv nP nF) → CIPtrRep c.κ h' ptr (.ctorInfo cv nP nF)
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → c.allowedTop "Ingress::get_ci_iprj" [bp, .field i] h →
      c.FamAt (ixAddr b) (ZMod.val i) → CoreGood c cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧ CIPtrRep c.κ h' ptr ci
  indRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (cm cb : Ixon.Constant) (p : Ixon.InductiveProj) (xs : Array Ixon.MutConst)
      (ind : Ixon.Inductive),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c.toCtx cs → Bytes.RepAddressRef addrTy h a addr →
    Ix.Cert.recordAt c.E (ixAddr a) = some cm → cm.info = .iPrj p →
    Ix.Cert.recordAt c.E p.block = some cb → cb.info = .muts xs →
    xs[p.idx.toNat]? = some (.indc ind) →
    ∃ (nl ty u blk : SourceValue F) (b : Bytes.Address),
      loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, .field (ind.params.toNat : F),
        .field (ind.indices.toNat : F), .field (ind.ctors.size : F), u, blk,
        .field (p.idx.toNat : F)]) ∧
      Bytes.RepAddressRef addrTy h' b blk ∧ ixAddr b = p.block ∧
      p.idx.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56
  inductRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → c.allowedTop "Ingress::get_ci" [addr] h →
      c.κ (ixAddr a) ≠ unresolvedKey → Good c.toCtx cs → Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩
  projTables : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs →
    c.allowedTop "KernelModeled::proj_ctor" [bp, ip] h → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    c.FamAt (ixAddr b) (ZMod.val i) →
    ProjPermitted c.κ (iprjAddr (ixAddr b) (ZMod.val i)) →
    (∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some ci ∧
      CIPtrRep c.κ h' ptr ci) ∧
    ∀ (sap sptr nl ty np u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (s : Bytes.Address),
    ObsFn W "Ingress::get_ci" [sap] h1 sptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 s sap →
    loadValue h2 sptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      (cvC.type.stripPis 1).isSome = true →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  projTablesAt : ∀ (bp sap ptr nl ty np u blk : SourceValue F) (h h' h1 h2 : Heap F)
      (cs cs1 : List (Call F)) (b s : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
    ObsFn W "Ingress::get_ci" [sap] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 s sap →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      0 < nF →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  unitLike : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c.toCtx cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) →
    FewInductives c.toCtx (ixAddr b) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  /-- Unit-like conversion at an actual raw constructor observation. Producing this field
  requires the staged former to carry its actual IxC capabilities; raw counts alone do not
  justify a unit-like flag in an empty-capability stage. -/
  unitLikeRaw : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → c.allowedTop "Ingress::get_ci" [ap] h →
    c.κ (ixAddr a) ≠ unresolvedKey →
    Good c.toCtx cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) → FewInductives c.toCtx (ixAddr b) →
    ZeroFieldCtorLoad c b i → NonrecursiveLoad c a →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    c.env.find? (c.κ (ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 b bp →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Good c.toCtx cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    piSortAt cnP (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c.toCtx cs5 ∧
        Bytes.RepAddressRef addrTy h5 sa sp) →
    ixAddr sa = iprjAddr (ixAddr b) (ZMod.val i) →
    (caps.eta = true ∧ caps.etaCtor = some (c.κ (ixAddr ac)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts c.env (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))
      (c.κ (ixAddr ac)) cvT caps cnP cnF
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    c.env.find? (c.κ (ixAddr pa)) = some (.indInfo cvT caps) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good c.toCtx cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c.toCtx cs5 ∧
        Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (caps.eta = true ∧
      caps.etaCtor = some (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cnP = ZMod.val m ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts c.env (c.κ (ixAddr pa))
      (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) cvT caps cnP cnF
  recordShape : ∀ (ap r : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (cst : Ixon.Constant),
    ObsFn W "Ingress::load_verified_constant" [ap] h r h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a ap →
    Ix.Cert.recordAt c.E (ixAddr a) = some cst →
    Specs.Callees.ConstShapeRep h' cst r
  inductBlock : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a b : Bytes.Address) (nl ty np ni nc u blk : SourceValue F) (i : F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → c.allowedTop "Ingress::get_ci" [addr] h →
      c.κ (ixAddr a) ≠ unresolvedKey → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind)
  projTablesGuard : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
      (tbl : Ix.Kernel.ProjTable .anon),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) →
      Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true ∧
      (Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
        ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
          (g : KLevel) (us : List KLevel),
          ZMod.val f < nF → us.length = tbl.levelParams.length →
          ObsFn W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
          Good c.toCtx csg → RCRep c.t c.lim hg rc → Bytes.RepAddressRef addrTy hg b bp' →
          IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
          (∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
          ∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0)
  canonical : ∀ (x : _root_.Address) (lc : Ixon.LazyConstant) (info : Ixon.ConstantInfo),
    (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF →
    c.E.consts.get? x = some lc → lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ →
      ∀ cm, lc.get? = some cm → cm.info = info
  /-- A key the environment stores resolves. -/
  storedRes : ∀ (a : _root_.Address) (ci : Ix.Kernel.ConstantInfo .anon),
    c.env.find? (keyOf c.t a) = some ci → c.κ a ≠ unresolvedKey
  /-- What the environment stores under the context's keying is not at the unresolved key. -/
  findRes : ∀ (a : _root_.Address) (ci : Ix.Kernel.ConstantInfo .anon),
    c.env.find? (c.κ a) = some ci → c.κ a ≠ unresolvedKey
  /-- The inductive of a stored constructor resolves, at the address of a block record a run
  hashed. -/
  ctorIndRes : ∀ (b : _root_.Address) (i j : Nat) (cv : Ix.Kernel.ConstantVal .anon)
      (nP nF : Nat), HashedBlockAt c.E b →
    c.env.find? (c.κ (cprjAddr b i j)) = some (.ctorInfo cv nP nF) →
    c.κ (iprjAddr b i) ≠ unresolvedKey
  /-- The inductive of a stored constructor permits projection, at the address it is stored
  under, for a block record a run hashed. -/
  ctorIndPerm : ∀ (a b : _root_.Address) (i j : Nat) (cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cv : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
    HashedBlockAt c.E b →
    c.env.find? (c.κ a) = some (.indInfo cvT caps) → cvT.name = c.κ (iprjAddr b i) →
    c.env.find? (c.κ (cprjAddr b i j)) = some (.ctorInfo cv nP nF) → ProjPermitted c.κ a
  /-- A role in force whose constant the checker builds or loads by role resolves
  (`fabricatedRole`). Other roles in force need not be stored. -/
  roleRes : ∀ (r : Ix.Kernel.Role) (a : _root_.Address), c.inForce r →
    fabricatedRole r = true →
    c.t.addressOf? r = some a → c.κ a ≠ unresolvedKey

/-- Compatibility with the old unrestricted interface. This adapter does not construct
load evidence for a fresh declaration or establish its selected-call coverage. -/
theorem ScopedLoadFacts.ofUnrestricted {c : ScopedCtx} (hk : c.key = keyOf c.t)
    (he : EnvFacts c.toCtx) (h : LoadFacts c.toCtx) : ScopedLoadFacts c := by
  obtain ⟨c₀, allowed, key, key_spec⟩ := c
  dsimp only at hk
  subst hk
  exact {
  getCI := fun addr ptr h₀ h₁ cs a ev _ _ hg ha => h.getCI addr ptr h₀ h₁ cs a ev hg.raw ha
  getCprj := by
    intro bp ptr i j h₀ h₁ cs b ev _ _ hg hb
    obtain ⟨ci₀, hfind₀, hrep⟩ := h.getCprj bp ptr i j h₀ h₁ cs b ev hg.raw hb
    refine ⟨⟨ci₀, hrep⟩, fun cv nP nF hfind => ?_⟩
    have heq := Option.some.inj (hfind₀.symm.trans hfind)
    cases heq
    exact hrep
  getIprj := fun bp ptr i h₀ h₁ cs b ev _ _ hg hb => h.getIprj bp ptr i h₀ h₁ cs b ev hg.raw hb
  indRecord := h.indRecord
  inductRecord := fun addr ptr h₀ h₁ cs a nl ty np ni nc u blk idx ev _ _ hg ha ld =>
    h.inductRecord addr ptr h₀ h₁ cs a nl ty np ni nc u blk idx ev hg ha ld
  projTables := by
    intro bp ip ptr h₀ h₁ cs b i ev _ hg hb hip _ _
    subst ip
    have htables := h.projTables bp (.field i) ptr h₀ h₁ cs b i ev hg hb rfl
    obtain ⟨v, mid, cs_assert, cs_load, ev_assert, ev_load, hcalls⟩ :=
      Obs.«KernelModeled::proj_ctor».obs ev
    have hstored := h.getCprj bp ptr i 0 mid h₁ cs_load b ev_load
      (hg.sub fun cl hcl => by simp [hcalls, hcl])
      (Bytes.repAddressRef_heapMono₂ addrTy ev_assert.heap_extends hb)
    exact ⟨by simpa only [ZMod.val_zero] using hstored,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j cvC nP nF hc _ => htables j cvC nP nF hc⟩
  projTablesAt := fun bp sap ptr nl ty np u blk h₀ h₁ h1 h2 cs cs1 b s i evM gM hb evG gG hs hld
      hblk j cvC nP nF hc _ =>
    h.projTablesAt bp sap ptr nl ty np u blk h₀ h₁ h1 h2 cs cs1 b s i evM gM hb evG gG hs hld hblk
      j cvC nP nF hc
  unitLike := h.unitLike
  unitLikeRaw := by
    intro ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps ev _ _ hg ha ld hb hfind hfew hz _
    obtain ⟨ciC, hfindC, vC, hldC, hrepC⟩ := h.getCprj hz.bp hz.ptr i 0 hz.before hz.after
      hz.calls b hz.observed hz.good hz.blockRep
    obtain ⟨cnl, cty, cblk, cidx, ccidx, cnp, cu, hzero⟩ := hz.zeroFields
    rw [hzero] at hldC
    injection hldC with hvalue
    subst vC
    obtain ⟨cvC, nPc, rfl⟩ := ctorZero_of_rep hrepC
    simp only [ZMod.val_zero] at hfindC
    exact h.unitLike ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps cvC nPc
      ev hg ha ld hb hfind hfew hfindC
  eta := by
    intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h₁ h₂ cs₁
      hC hname hnF ev hg hb ld hT hmodeled hpi hnz hrec haddr
    have ho := h.eta ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx
      h₁ h₂ cs₁ hC hname hnF ev hg hb ld hT hmodeled hpi hnz hrec haddr
    exact ⟨ho, he.etaUseFacts hT ho.1 ho.2.1 hC⟩
  etaIota := by
    intro pp ptr nl ty u blk h₁ h₂ cs₁ pa b i m cvT cvc caps cnP cnF us l ev hg hp ld hb
      hT hC hmulti hrec hpi hnz
    have ho := h.etaIota pp ptr nl ty u blk h₁ h₂ cs₁ pa b i m cvT cvc caps cnP cnF us l
      ev hg hp ld hb hT hC hmulti hrec hpi hnz
    exact ⟨ho, he.etaUseFacts hT ho.1 ho.2.1 hC⟩
  recordShape := h.recordShape
  inductBlock := fun addr ptr h₀ h₁ cs a b nl ty np ni nc u blk i ev _ _ hg ha ld hb =>
    h.inductBlock addr ptr h₀ h₁ cs a b nl ty np ni nc u blk i ev hg ha ld hb
  projTablesGuard := h.projTablesGuard
  canonical := h.canonical
  storedRes := fun _ _ _ => Resolved.ne
  findRes := fun _ _ _ => Resolved.ne
  ctorIndRes := fun _ _ _ _ _ _ _ _ => Resolved.ne
  ctorIndPerm := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => inferInstance
  roleRes := fun _ _ _ _ _ => Resolved.ne }

/-- Context evidence for actual scoped registry runs. -/
structure ScopedCoreFacts (c : ScopedCtx) : Prop where
  env : CoreEnvFacts c.toCtx
  loads : ScopedLoadFacts c

theorem ScopedCoreFacts.ofUnrestricted {c : Ctx} (h : CoreFacts c) :
    ScopedCoreFacts (ScopedCtx.unrestricted c) :=
  ⟨h.env.toCoreEnvFacts, ScopedLoadFacts.ofUnrestricted rfl h.env h.loads⟩

/-! ## Resolution at the load sites

A step proof reads the resolution of the address it is about to load from what it has in hand:
the represented term whose constant it loads (`Tm.const_key_ne`, `Tm.head_key_ne`,
`Tm.proj_key_ne`), a stored constant (`res_of_find`), or the stored inductive or constructor
whose block member it names (`res_of_ind`, `res_of_ctor`). -/

private theorem find?_name_eq {env : Ix.Kernel.Env .anon} {k : KKey}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : env.find? k = some ci) : ci.name = k := by
  unfold Ix.Kernel.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- What the environment stores under the context's keying resolves. -/
theorem ScopedCoreFacts.res_of_find {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : c.env.find? (c.κ a) = some ci) : c.κ a ≠ unresolvedKey :=
  hc.loads.findRes a ci h

/-- A key the environment stores under the table's keying resolves, and the context keys it as
the table does. -/
theorem ScopedCoreFacts.key_of_stored {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : c.env.find? (keyOf c.t a) = some ci) : c.κ a = keyOf c.t a :=
  c.key_eq (hc.loads.storedRes a ci h)

/-- **The inductive a stored inductive names resolves**: the name is the stored key. -/
theorem ScopedCoreFacts.res_of_ind {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a b : _root_.Address} {i : Nat} {cv : Ix.Kernel.ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon}
    (hfind : c.env.find? (c.κ a) = some (.indInfo cv caps))
    (hname : cv.name = c.κ (iprjAddr b i)) : c.κ (iprjAddr b i) ≠ unresolvedKey := by
  have h1 : cv.name = c.κ a := find?_name_eq hfind
  rw [← hname, h1]
  exact hc.res_of_find hfind

/-- **The inductive of a stored constructor resolves.** -/
theorem ScopedCoreFacts.res_of_ctor {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a b : _root_.Address} {i j : Nat} {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (hfind : c.env.find? (c.κ a) = some (.ctorInfo cv nP nF))
    (hname : cv.name = c.κ (cprjAddr b i j)) (hb : HashedBlockAt c.E b) :
    c.κ (iprjAddr b i) ≠ unresolvedKey := by
  have h1 : cv.name = c.κ a := find?_name_eq hfind
  refine hc.loads.ctorIndRes b i j cv nP nF hb ?_
  rw [← hname, h1]
  exact hfind

/-- A stored inductive is family evidence at its own projection address. -/
theorem ScopedCtx.famAt_of_ind {c : ScopedCtx} {a b : _root_.Address} {i : Nat}
    {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hfind : c.env.find? (c.κ a) = some (.indInfo cv caps))
    (hname : cv.name = c.κ (iprjAddr b i)) : c.FamAt b i := by
  have h1 : cv.name = c.κ a := find?_name_eq hfind
  refine Or.inl ⟨cv, caps, ?_⟩
  rw [← hname, h1]
  exact hfind

/-- A stored constructor is family evidence for its inductive. -/
theorem ScopedCtx.famAt_of_ctor {c : ScopedCtx} {a b : _root_.Address} {i j : Nat}
    {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (hfind : c.env.find? (c.κ a) = some (.ctorInfo cv nP nF))
    (hname : cv.name = c.κ (cprjAddr b i j)) : c.FamAt b i := by
  have h1 : cv.name = c.κ a := find?_name_eq hfind
  refine Or.inr ⟨j, cv, nP, nF, ?_⟩
  rw [← hname, h1]
  exact hfind

/-- **The inductive of a stored constructor permits projection**, at the address it is stored
under: the permission a step needs for the `Proj` cells it builds at a structure it has the
constructor of. -/
theorem ScopedCoreFacts.perm_of_ctor {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a ac b : _root_.Address} {i j : Nat} {cvT : Ix.Kernel.ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (hfindI : c.env.find? (c.κ a) = some (.indInfo cvT caps))
    (hnameI : cvT.name = c.κ (iprjAddr b i))
    (hfindC : c.env.find? (c.κ ac) = some (.ctorInfo cv nP nF))
    (hnameC : cv.name = c.κ (cprjAddr b i j)) (hb : HashedBlockAt c.E b) :
    ProjPermitted c.κ a := by
  have h1 : cv.name = c.κ ac := find?_name_eq hfindC
  refine hc.loads.ctorIndPerm a b i j cvT caps cv nP nF hb hfindI hnameI ?_
  rw [← hnameC, h1]
  exact hfindC

/-- The address a role in force is bound to resolves. -/
theorem ScopedCoreFacts.res_of_role {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {r : Ix.Kernel.Role} {a : _root_.Address} (hb : c.t.addressOf? r = some a)
    (hf : c.inForce r) (hi : fabricatedRole r = true) : c.κ a ≠ unresolvedKey :=
  hc.loads.roleRes r a hf hi hb

/-- Discharge the resolution of a key from what a step proof has in hand. -/
macro "resolve_key" : tactic => `(tactic| first
  | with_reducible (first
    | assumption
    | exact Resolved.ne
    | exact Tm.const_key_ne (by assumption)
    | exact Tm.head_key_ne (by assumption)
    | exact Tm.proj_key_ne (by assumption)
    | exact ScopedCoreFacts.res_of_find (by assumption) (by assumption)
    | exact ScopedCoreFacts.res_of_ind (by assumption) (by assumption) (by assumption)
    | exact ScopedCoreFacts.res_of_ctor (by assumption) (by assumption) (by assumption)
        (by assumption))
  | exact ScopedCoreFacts.res_of_role (by with_reducible assumption)
      (by with_reducible assumption) (by with_reducible assumption) (by decide))

end IxVM.Refinement.Core
