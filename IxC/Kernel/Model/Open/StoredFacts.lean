module

public import IxC.Kernel.Model.Open.Certs

@[expose] public section

/-!
# The stored constants' facts a reduction of the core reads

Facts about the constants of an environment, read off the three model-free invariants the
fold keeps (`EnvWF`, `RecCtorsStored`, `ProjOkT`; an `EnvModel` carries them as its `wf`,
`rec_ctors` and `proj_ok` fields):

* **every rule of a stored recursor fires**: `.plain` or `.nested`, never `.inert`, at a stored
  constructor whose parameter count is the rule's (`recRules_fire`,
  `recRules_fire_cases`);
* **a stored recursor with a rule has a binder for every argument up to its major premise**
  (`recArity_of`, through `StoredArities`, `storedArities_of`);
* **a rule's constructor has a binder for every parameter and field**
  (`ruleCtor_arity`), and so does **the constructor of a stored projection table's
  entry** (`tableCtor_arity`).
* **a unit-like or η-capable family has a binder for every parameter its flag counts**
  (`EnvWF.indCaps`, the first half of `StoredArities`).

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

end Ix.Kernel.Open
