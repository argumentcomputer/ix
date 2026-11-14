module

public import IxC.Kernel.Model.Open.Certs
public import IxC.Kernel.Verify.Rules.StoreClosed

@[expose] public section

/-!
# The stored constants' facts a reduction of the core reads

Facts about the constants of an environment, read off the three model-free invariants the
fold keeps (`EnvWF`, `RecCtorsStored`, `ProjOkT`; an `EnvModel` carries them as its `wf`,
`rec_ctors` and `proj_ok` fields). Together they are the **store invariant** `StoreInv`, which
every declaration step over derivations keeps from the empty environment on, with no model
(`Ix.Kernel.Model.storeFoldRoutes`); the facts below are stated over each invariant they read
and again over `StoreInv`:

* **every rule of a stored recursor fires**: `.plain` or `.nested`, never `.inert`, at a stored
  constructor whose parameter count is the rule's (`recRules_fire`,
  `recRules_fire_cases`);
* **a stored recursor with a rule has a binder for every argument up to its major premise**
  (`recArity_of`, through `StoredArities`, `storedArities_of`);
* **a rule's constructor has a binder for every parameter and field**
  (`ruleCtor_arity`), and so does **the constructor of a stored projection table's
  entry** (`tableCtor_arity`).
* **a unit-like or η-capable family has a binder for every parameter its flag counts**
  (`EnvWF.indCaps`, the first half of `StoredArities`);
* **a plain rule's major premise is its family at the constructor's level parameters, applied
  first to the recursor's leading variables** (`StoreInv.recPlain`);
* **a set K bit or η-rescue bit is the store's own verdict** (`StoreInv.recK`,
  `StoreInv.recEta`);
* **every stored term is closed** (`StoreInv.storeClosed`).

A projection function's telescope carries its own arity in the rules (`EtaProjCerts.cons`'s
`stripPis` premise).
-/

namespace Ix.Kernel.Open

open Ix.Kernel (Env Key ConstantInfo ConstantVal RecRule RecRuleFire ProjEntry EnvWF
  RecCtorsStored ProjOkT)

variable {env : Env md}

/-- **Every rule of a stored recursor fires at a stored constructor**: its mode is not `.inert`,
and its constructor is stored with the rule's parameter count. -/
theorem recRules_fire (h : RecCtorsStored env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) :
    rl.fire ≠ .inert ∧ ∃ cvj nF, env.find? rl.ctor = some (.ctorInfo cvj rl.ctorParams nF) := by
  obtain ⟨⟨cvj, hc, -, -, hfire, -⟩, -, -⟩ := h k cv mI rP rls hk rl hrl
  exact ⟨hfire, cvj, rl.nfields, hc⟩

/-- **A stored rule's mode is `.plain` or `.nested`.** -/
theorem recRules_fire_cases (h : RecCtorsStored env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) :
    rl.fire = .plain ∨ ∃ lvls pins, rl.fire = .nested lvls pins := by
  have hne := (recRules_fire h hk hrl).1
  cases hf : rl.fire with
  | inert => exact absurd hf hne
  | plain => exact .inl rfl
  | nested lvls pins => exact .inr ⟨lvls, pins, rfl⟩

/-- **A rule's constructor has a binder for every parameter and field.** -/
theorem ruleCtor_arity (h : RecCtorsStored env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) {cvj : ConstantVal md} {nP nF : Nat}
    (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF)) :
    nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true := by
  obtain ⟨⟨cvj', hc', -, -, -, htele⟩, -, -⟩ := h k cv mI rP rls hk rl hrl
  rw [hc] at hc'
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
  obtain ⟨bs, body, c, us, hs, -⟩ := Ix.Kernel.Expr.ctorTeleOk_head htele
  exact ⟨rfl, rfl, by rw [hs]; rfl⟩

/-- **The stored telescopes have their binders** (`StoredArities`), from the two model-free
invariants (`EnvModel.storedArities` at a model). -/
theorem storedArities_of (hwf : EnvWF env) (hrc : RecCtorsStored env) : StoredArities env := by
  refine ⟨fun T cvT caps hf => hwf.indCaps hf, fun r cv mI rP rules hf rl hrl hfire => ?_⟩
  obtain ⟨⟨cvj, -, hplain, -, -⟩, -, -⟩ := hrc r cv mI rP rules hf rl hrl
  cases hfr : rl.fire with
  | inert => exact absurd hfr hfire
  | plain =>
    obtain ⟨pre, dom, body, bm, -, hs, -⟩ := recRulePlain_shapeT (hplain hfr)
    exact stripPis_succ_isSome hs
  | nested lvls pins =>
    obtain ⟨-, -, -, -, -, h6, -⟩ := hwf _ (List.mem_of_find?_eq_some hf)
    obtain ⟨pre, dom, body, bm, -, hs, -⟩ :=
      ((h6 cv mI rP rules rfl rl hrl).2.2.2.2 lvls pins hfr).2.2.2
    exact stripPis_succ_isSome hs

/-- **A stored recursor with a rule has a binder for every argument up to its major premise.** -/
theorem recArity_of (hwf : EnvWF env) (hrc : RecCtorsStored env) {k : Key md}
    {cv : ConstantVal md} {mI rP : Nat} {rls : List (RecRule md)}
    (hk : env.find? k = some (.recInfo cv mI rP rls)) {rl : RecRule md} (hrl : rl ∈ rls) :
    (cv.type.stripPis (mI + 1)).isSome = true :=
  (storedArities_of hwf hrc).2 k cv mI rP rls hk rl hrl (recRules_fire hrc hk hrl).1

/-- **The constructor of a stored projection table's entry has a binder for every parameter and
field**, and is stored at the entry's counts. -/
theorem tableCtor_arity (h : ProjOkT env) {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hp : env.findProj? sn i = some entry) {cvC : ConstantVal md} {nP nF : Nat}
    (hc : env.find? entry.ctor = some (.ctorInfo cvC nP nF)) :
    nP = entry.numParams ∧ nF = entry.numFields ∧
      (cvC.type.stripPis (nP + nF)).isSome = true := by
  obtain ⟨tbl, ht, hi, rfl⟩ := Ix.Kernel.Env.findProj?_some hp
  obtain ⟨-, -, -, -, ⟨cvC', hC', -, bs, hs⟩⟩ := h _ tbl ht i hi
  rw [hc] at hC'
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hC')
  exact ⟨rfl, rfl, by rw [hs]; rfl⟩

/-! ## The store invariant -/

/-- **The store invariant**: every stored constant is syntactically well formed (`EnvWF`),
every rule of a stored recursor is recorded against its stored constructor with its two rescue
bits the store's own verdict (`RecCtorsStored`), and every stored projection table carries its
head data (`ProjOkT`). It holds at the empty environment and every declaration step over
derivations keeps it (`Ix.Kernel.Model.storeFoldRoutes`), with no model. -/
structure StoreInv (env : Env md) : Prop where
  wf : EnvWF env
  rec_ctors : RecCtorsStored env
  proj_ok : ProjOkT env

namespace StoreInv

theorem empty : StoreInv (md := md) Env.empty :=
  ⟨fun c hc => by simp [Env.empty] at hc, Ix.Kernel.RecCtorsStored.empty,
    Ix.Kernel.ProjOkT.empty⟩

/-- `recRules_fire` from the store invariant. -/
theorem recRules_fire (h : StoreInv env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) :
    rl.fire ≠ .inert ∧ ∃ cvj nF, env.find? rl.ctor = some (.ctorInfo cvj rl.ctorParams nF) :=
  _root_.Ix.Kernel.Open.recRules_fire h.rec_ctors hk hrl

/-- `recRules_fire_cases` from the store invariant. -/
theorem recRules_fire_cases (h : StoreInv env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) :
    rl.fire = .plain ∨ ∃ lvls pins, rl.fire = .nested lvls pins :=
  _root_.Ix.Kernel.Open.recRules_fire_cases h.rec_ctors hk hrl

/-- `ruleCtor_arity` from the store invariant. -/
theorem ruleCtor_arity (h : StoreInv env) {k : Key md} {cv : ConstantVal md}
    {mI rP : Nat} {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) {cvj : ConstantVal md} {nP nF : Nat}
    (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF)) :
    nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true :=
  _root_.Ix.Kernel.Open.ruleCtor_arity h.rec_ctors hk hrl hc

/-- `storedArities_of` from the store invariant. -/
theorem storedArities (h : StoreInv env) : StoredArities env :=
  storedArities_of h.wf h.rec_ctors

/-- `recArity_of` from the store invariant. -/
theorem recArity (h : StoreInv env) {k : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) :
    (cv.type.stripPis (mI + 1)).isSome = true :=
  recArity_of h.wf h.rec_ctors hk hrl

/-- `tableCtor_arity` from the store invariant. -/
theorem tableCtor_arity (h : StoreInv env) {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hp : env.findProj? sn i = some entry) {cvC : ConstantVal md} {nP nF : Nat}
    (hc : env.find? entry.ctor = some (.ctorInfo cvC nP nF)) :
    nP = entry.numParams ∧ nF = entry.numFields ∧
      (cvC.type.stripPis (nP + nF)).isSome = true :=
  _root_.Ix.Kernel.Open.tableCtor_arity h.proj_ok hp hc

/-- **A unit-like or η-capable family has a binder for every parameter its flag counts.** -/
theorem familyArity (h : StoreInv env) {T : Key md} {cvT : ConstantVal md}
    {caps : Ix.Kernel.IndCaps md} (hT : env.find? T = some (.indInfo cvT caps)) :
    (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
      (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true) :=
  h.wf.indCaps hT

/-- **Every stored term is closed**: types, definition values, rule right-hand sides and nested
instantiations, projection bodies (what the rules' top weakening asks of an environment). -/
theorem storeClosed (h : StoreInv env) : Ix.Kernel.StoreClosed env :=
  Ix.Kernel.StoreClosed.of_envWF h.wf

/-- **A plain rule's major premise**: the recursor's type has a binder for every argument before
the major premise, whose domain is the constructor's family at the constructor's level
parameters, applied first to the recursor's leading variables, one per constructor parameter. -/
theorem recPlain (h : StoreInv env) {k : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) (hfire : rl.fire = .plain) {cvj : ConstantVal md}
    {nP nF : Nat} (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF)) :
    ∃ pre dom body bm D,
      cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D (cvj.levelParams.map .param) ∧
      dom.getAppArgs.take nP = (List.range nP).map (fun k => Ix.Kernel.Expr.bvar (mI - 1 - k)) := by
  obtain ⟨⟨cvj', hc', hplain, -, -, -⟩, -, -⟩ := h.rec_ctors k cv mI rP rls hk rl hrl
  rw [hc] at hc'
  obtain ⟨rfl, rfl, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
  exact Ix.Kernel.recRulePlain_shapeT (hplain hfire)

/-- **A set K bit is the store's verdict**: the rule's constructor is stored with no field, its
result is headed by a stored family, and that family carries the K capability. -/
theorem recK (h : StoreInv env) {k : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) (hK : rl.k = true) :
    ∃ (cvj : ConstantVal md) (cnP : Nat) (T : Key md) (us : List Ix.Kernel.Level)
      (cvT : ConstantVal md) (caps : Ix.Kernel.IndCaps md),
      env.find? rl.ctor = some (.ctorInfo cvj cnP 0) ∧
      (cvj.type.piResult).getAppFn = .const T us ∧
      env.find? T = some (.indInfo cvT caps) ∧ caps.ruleK = true :=
  Ix.Kernel.recRuleKOf_inv ((h.rec_ctors k cv mI rP rls hk rl hrl).2.1 hK)

/-- **A set η-rescue bit is the store's verdict**: the rule's constructor is stored, its result
is headed by a stored family carrying the η capability at that constructor, the recursor's key
is not a projection function's, and the constructor's level parameters are the family's. -/
theorem recEta (h : StoreInv env) {k : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rls : List (RecRule md)} (hk : env.find? k = some (.recInfo cv mI rP rls))
    {rl : RecRule md} (hrl : rl ∈ rls) (hE : rl.eta = true) :
    ∃ (cvj : ConstantVal md) (cnP cnF : Nat) (T : Key md) (us : List Ix.Kernel.Level)
      (cvT : ConstantVal md) (caps : Ix.Kernel.IndCaps md),
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) ∧
      (cvj.type.piResult).getAppFn = .const T us ∧
      env.find? T = some (.indInfo cvT caps) ∧ caps.eta = true ∧
      caps.etaCtor = some rl.ctor ∧ Key.isProjFnShape k = false ∧
      cvj.levelParams = cvT.levelParams :=
  Ix.Kernel.recRuleEtaOf_inv ((h.rec_ctors k cv mI rP rls hk rl hrl).2.2 hE)

end StoreInv

end Ix.Kernel.Open
