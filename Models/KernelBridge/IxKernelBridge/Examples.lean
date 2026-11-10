import IxKernelBridge.NatBridge

/-!
# Instances of the simulation lemma (`IxKernelBridge.Examples`)

`srcRun_to_red` and the theorems built on it hold for every relation
`constSpec` that satisfies `hconst`, so they say nothing about a program for
which no such relation exists. This module shows, in Lean, that the premises
can be met, and records which primitive operations can take part. It is the
machine-checked form of the positive instances built in the 2026-11-09 review
(refuter R2) and of the per-operation facts found there.

What the instances show:

- Each instance relates an honest root: `eRoot = .const k []`, where `k` is a
  level-free definition of `env` whose stored value is the kernel image of the
  Src definition, and `constSpec` maps each Src constant to the kernel constant
  or basis head it names. `RelConstStep.defn` is discharged by δ-reduction.
- The Src side of `id_bridge` to `addLit_bridge` is stated for every program
  whose entries have the shape ingress (`Src.Ingress.conv`) gives the Lean
  definition named, with no type arguments: the identity, `Nat.succ a`,
  `Nat.add a b` and `Nat.add a (nat_lit 1)`.
- `addLit_concrete` closes every hypothesis for a concrete two-constant program
  and a concrete `Env`.

What they do not show:

- The kernel-side values are hand transcriptions of the definitions, not the
  output of IxCK's Ixon reader on any compiled environment, and `envAdd` is not
  a `checkDecls`-accepted environment (its `Nat.add` is a stand-in whose only
  read property is that it is a definition). Nothing here connects `env` or
  `eRoot` to a compile claim's environment or target.
- Of the repository's fixture roots, only `Abi.nat1 (a : Nat) : Nat := a` has
  the shape `id_bridge` needs; the review established that by evaluating the
  ingested program, not by a proof in this package.

The per-operation premise of `RelHead.primBinNat` (`PrimPremise`) is proved for
the eleven binary operations whose Src and kernel results agree on all inputs
and refuted for the other three: `pow` (the kernel refuses exponents above
2^24) and `beq`/`ble` (their Src results are `Bool`, which `RelVal` does not
relate). `pred`, the one unary operation, has no `RelHead` case.
-/

namespace IxKernelBridge.Examples

open Ix.Kernel Ix.Kernel.Rules IxKernelBridge
open IxCC.Src (Program Term Levels CId Binder)

abbrev E := Expr .anon

/-! ## Per-operation agreement (`RelHead.primBinNat`'s premise) -/

/-- The premise `RelHead.primBinNat` takes for operation `op` at kernel key `k`. -/
def PrimPremise (op : IxCC.Src.PrimOp) (k : Key .anon) : Prop :=
  ∀ n0 n1 res, op.evalLits [n0, n1] = some res →
    ∃ out, res = .nat out ∧ natOpResult k n0 n1 = some (.lit (.natVal out))

theorem add_premise : PrimPremise .add natAddName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨n0 + n1, rfl, by simp [natOpResult]⟩

theorem sub_premise : PrimPremise .sub natSubName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨n0 - n1, rfl, by simp [natOpResult]⟩

theorem mul_premise : PrimPremise .mul natMulName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨n0 * n1, rfl, by simp [natOpResult]⟩

theorem div_premise : PrimPremise .div natDivName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  refine ⟨n0 / n1, ?_, by simp [natOpResult]⟩
  by_cases hb : n1 = 0 <;> simp [hb]

theorem mod_premise : PrimPremise .mod natModName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  refine ⟨n0 % n1, ?_, by simp [natOpResult]⟩
  by_cases hb : n1 = 0 <;> simp [hb]

theorem gcd_premise : PrimPremise .gcd natGcdName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨Nat.gcd n0 n1, rfl, by simp [natOpResult]⟩

theorem land_premise : PrimPremise .land natLandName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨Nat.land n0 n1, rfl, by simp [natOpResult]⟩

theorem lor_premise : PrimPremise .lor natLorName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨Nat.lor n0 n1, rfl, by simp [natOpResult]⟩

theorem xor_premise : PrimPremise .xor natXorName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  exact ⟨Nat.xor n0 n1, rfl, by simp [natOpResult]⟩

theorem shiftLeft_premise : PrimPremise .shiftLeft natShiftLeftName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  refine ⟨Nat.shiftLeft n0 n1, ?_, by simp [natOpResult]⟩
  rw [show Nat.shiftLeft n0 n1 = n0 * 2 ^ n1 from Nat.shiftLeft_eq n0 n1]

theorem shiftRight_premise : PrimPremise .shiftRight natShiftRightName := by
  intro n0 n1 res h
  simp [IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.arity, IxCC.Src.PrimOp.eval2] at h
  subst h
  refine ⟨Nat.shiftRight n0 n1, ?_, by simp [natOpResult]⟩
  rw [show Nat.shiftRight n0 n1 = n0 / 2 ^ n1 from Nat.shiftRight_eq_div_pow n0 n1]
  split
  · rename_i hlt
    by_cases h0 : n0 = 0
    · simp [h0]
    · have hlt2 : n0 < 2 ^ n1 := (Nat.log2_lt h0).mp hlt
      simp [Nat.div_eq_of_lt hlt2]
  · rfl

/-- `Nat.beq`'s Src result is a `Bool`, never the `.nat out` the premise requires. -/
theorem beq_premise_false (k : Key .anon) : ¬ PrimPremise .beq k := by
  intro h
  obtain ⟨out, hres, _⟩ := h 0 0 _ rfl
  simp [IxCC.Src.PrimOp.eval2] at hres

/-- `Nat.ble`'s Src result is a `Bool`, never the `.nat out` the premise requires. -/
theorem ble_premise_false (k : Key .anon) : ¬ PrimPremise .ble k := by
  intro h
  obtain ⟨out, hres, _⟩ := h 0 0 _ rfl
  simp [IxCC.Src.PrimOp.eval2] at hres

private def badSmall (k : Key .anon) : Bool :=
  match natOpResult k 2 3 with
  | some (.lit (.natVal 8)) => false
  | _ => true

/-- `Nat.pow` agrees with no accelerated kernel key: at `Nat.pow` the kernel
refuses the exponent `2^24 + 1`, and every other key disagrees with `2^3`. -/
theorem pow_premise_false :
    ∀ k ∈ (natBinOpNames : List (Key .anon)), ¬ PrimPremise .pow k := by
  intro k hk h
  have hall : (natBinOpNames : List (Key .anon)).all
      (fun k => decide (k = natPowName) || badSmall k) = true := by decide +kernel
  have hk' := List.all_eq_true.mp hall k hk
  cases hdec : decide (k = natPowName) with
  | true =>
    have hkp : k = natPowName := of_decide_eq_true hdec
    subst hkp
    obtain ⟨out, _, hr⟩ := h 2 16777217 _ rfl
    have hnone : (natOpResult (md := .anon) natPowName 2 16777217).isNone = true := by
      decide +kernel
    rw [hr] at hnone
    cases hnone
  | false =>
    rw [hdec, Bool.false_or] at hk'
    obtain ⟨out, hres, hr⟩ := h 2 3 _ rfl
    have h8 : out = 8 := by
      simp [IxCC.Src.PrimOp.eval2] at hres
      omega
    subst h8
    simp [badSmall, hr] at hk'

/-! ## Instances of `srcRun_to_red` with an honest root -/

/-- δ on a level-free stored definition. -/
theorem red_const_value {env : Env .anon} {k : Key .anon} {cv : ConstantVal .anon} {v : E}
    {hint : ReducibilityHint}
    (hf : env.find? k = some (.defnInfo cv v hint)) (hlp : cv.levelParams = []) :
    Red env 0 (.const k []) v := by
  have h := red_delta_const (d := 0) (us := []) hf (by simp [hlp])
  rw [hlp] at h
  rwa [show v.instantiateLevelParams [] [] = v from
    Ix.Kernel.Expr.instantiateLevelParams_self [] v] at h

/-- `def f (a : Nat) : Nat := a`, the shape of `Abi.nat1`. -/
theorem id_bridge {p : Program} {c : CId} {ty dom : Term} {b : Binder}
    (hres : p.table.resolveOf c = none)
    (hdecl : p.decl? c = some (.defn .defn .safe 0 ty (.lam b dom (.var 0))))
    {env : Env .anon} {k : Key .anon} {cv : ConstantVal .anon} {K : E} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hbasis : natBasisStored env = true)
    (hfind : env.find? k = some (.defnInfo cv (.lam K (.bvar 0) mb) hint))
    (hlp : cv.levelParams = []) (hK : K.bvarBound = 0) (hmb : mb.pw.isNever = true)
    {kf : Nat} {xs : List Nat} {out : Nat}
    (hrun : IxCC.Src.run p kf c (xs.map .lit) = .ok (.lit out)) :
    ∃ w, Red env 0 (mkNatApp (.const k []) xs) w ∧ rawNatLit? w = some out := by
  let cs : Levels → CId → E → Prop := fun _ c' e => c' = c ∧ e = .const k []
  have hconst : ∀ ls c' e, cs ls c' e → RelConstStep p env cs ls c' e := by
    rintro ls c' e ⟨rfl, rfl⟩
    exact RelConstStep.defn hres hdecl (red_const_value hfind hlp)
      (RelTerm.lam (by omega) (fun _ => hmb) (RelTerm.var (by omega)))
  exact srcRun_to_red hbasis hconst ⟨rfl, rfl⟩ hrun

/-- `def f (a : Nat) : Nat := Nat.succ a`. -/
theorem succ_bridge {p : Program} {c s : CId} {ty dom : Term} {b : Binder}
    {m : IxCC.Src.Mode} {r : IxCC.Src.Rel}
    (hres : p.table.resolveOf c = none)
    (hdecl : p.decl? c = some (.defn .defn .safe 0 ty (.lam b dom (.app (.const s []) (.var 0) m r))))
    {b1 : Bool} {lvls ind cidx : Nat} {cty : Term}
    (hresS : p.table.resolveOf s = none)
    (hdeclS : p.decl? s = some (.ctor b1 lvls ind cidx 0 1 cty))
    (hsucc : some s = p.known.natSucc) (hne : some s ≠ p.known.natZero)
    {env : Env .anon} {k : Key .anon} {cv : ConstantVal .anon} {K : E} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hbasis : natBasisStored env = true)
    (hfind : env.find? k = some (.defnInfo cv
      (.lam K (.app (.const natSuccName []) (.bvar 0)) mb) hint))
    (hlp : cv.levelParams = []) (hK : K.bvarBound = 0) (hmb : mb.pw.isNever = true)
    {kf : Nat} {xs : List Nat} {out : Nat}
    (hrun : IxCC.Src.run p kf c (xs.map .lit) = .ok (.lit out)) :
    ∃ w, Red env 0 (mkNatApp (.const k []) xs) w ∧ rawNatLit? w = some out := by
  let cs : Levels → CId → E → Prop := fun _ c' e =>
    (c' = c ∧ e = .const k []) ∨ (c' = s ∧ e = .const natSuccName [])
  have hconst : ∀ ls c' e, cs ls c' e → RelConstStep p env cs ls c' e := by
    rintro ls c' e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact RelConstStep.defn hres hdecl (red_const_value hfind hlp)
        (RelTerm.lam (by omega) (fun _ => hmb)
          (RelTerm.app (RelTerm.const rfl (Or.inr ⟨rfl, rfl⟩)) (RelTerm.var (by omega))))
    · exact RelConstStep.ctor hresS hdeclS (RelHead.natSucc hdeclS hsucc hne)
  exact srcRun_to_red hbasis hconst (Or.inl ⟨rfl, rfl⟩) hrun

/-- `def f (a b : Nat) : Nat := Nat.add a b`, with `Nat.add` resolved to the
primitive `add`. -/
theorem add_bridge {p : Program} {c a : CId} {ty dom1 dom2 : Term} {b1 b2 : Binder}
    {m1 m2 : IxCC.Src.Mode} {r1 r2 : IxCC.Src.Rel}
    (hres : p.table.resolveOf c = none)
    (hdecl : p.decl? c = some (.defn .defn .safe 0 ty
      (.lam b1 dom1 (.lam b2 dom2 (.app (.app (.const a []) (.var 1) m1 r1) (.var 0) m2 r2)))))
    (hresA : p.table.resolveOf a = some (.prim .add))
    {env : Env .anon} {k : Key .anon} {cv : ConstantVal .anon} {K1 K2 : E} {mb1 mb2 : BinderMeta}
    {hint : ReducibilityHint}
    (hbasis : natBasisStored env = true)
    (hstored : natOpStored env natAddName = true)
    (hfind : env.find? k = some (.defnInfo cv
      (.lam K1 (.lam K2 (.app (.app (.const natAddName []) (.bvar 1)) (.bvar 0)) mb2) mb1) hint))
    (hlp : cv.levelParams = []) (hK1 : K1.bvarBound = 0) (hK2 : K2.bvarBound ≤ 1)
    (hmb1 : mb1.pw.isNever = true) (hmb2 : mb2.pw.isNever = true)
    {kf : Nat} {xs : List Nat} {out : Nat}
    (hrun : IxCC.Src.run p kf c (xs.map .lit) = .ok (.lit out)) :
    ∃ w, Red env 0 (mkNatApp (.const k []) xs) w ∧ rawNatLit? w = some out := by
  let cs : Levels → CId → E → Prop := fun _ c' e =>
    (c' = c ∧ e = .const k []) ∨ (c' = a ∧ e = .const natAddName [])
  have hconst : ∀ ls c' e, cs ls c' e → RelConstStep p env cs ls c' e := by
    rintro ls c' e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact RelConstStep.defn hres hdecl (red_const_value hfind hlp)
        (RelTerm.lam (by omega) (fun _ => hmb1)
          (RelTerm.lam hK2 (fun _ => hmb2)
            (RelTerm.app
              (RelTerm.app (RelTerm.const rfl (Or.inr ⟨rfl, rfl⟩)) (RelTerm.var (by omega)))
              (RelTerm.var (by omega)))))
    · exact RelConstStep.prim hresA
        (RelHead.primBinNat rfl (by decide) hstored add_premise)
  exact srcRun_to_red hbasis hconst (Or.inl ⟨rfl, rfl⟩) hrun

/-- `def f (a : Nat) : Nat := Nat.add a (nat_lit n)`: a raw literal, not a
numeral (`OfNat.ofNat Nat n _` is outside the fragment). -/
theorem addLit_bridge {p : Program} {c a : CId} {ty dom : Term} {b : Binder} {n : Nat}
    {m1 m2 : IxCC.Src.Mode} {r1 r2 : IxCC.Src.Rel}
    (hres : p.table.resolveOf c = none)
    (hdecl : p.decl? c = some (.defn .defn .safe 0 ty
      (.lam b dom (.app (.app (.const a []) (.var 0) m1 r1) (.natLit n) m2 r2))))
    (hresA : p.table.resolveOf a = some (.prim .add))
    {env : Env .anon} {k : Key .anon} {cv : ConstantVal .anon} {K : E} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hbasis : natBasisStored env = true)
    (hstored : natOpStored env natAddName = true)
    (hfind : env.find? k = some (.defnInfo cv
      (.lam K (.app (.app (.const natAddName []) (.bvar 0)) (.lit (.natVal n))) mb) hint))
    (hlp : cv.levelParams = []) (hK : K.bvarBound = 0) (hmb : mb.pw.isNever = true)
    {kf : Nat} {xs : List Nat} {out : Nat}
    (hrun : IxCC.Src.run p kf c (xs.map .lit) = .ok (.lit out)) :
    ∃ w, Red env 0 (mkNatApp (.const k []) xs) w ∧ rawNatLit? w = some out := by
  let cs : Levels → CId → E → Prop := fun _ c' e =>
    (c' = c ∧ e = .const k []) ∨ (c' = a ∧ e = .const natAddName [])
  have hconst : ∀ ls c' e, cs ls c' e → RelConstStep p env cs ls c' e := by
    rintro ls c' e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact RelConstStep.defn hres hdecl (red_const_value hfind hlp)
        (RelTerm.lam (by omega) (fun _ => hmb)
          (RelTerm.app
            (RelTerm.app (RelTerm.const rfl (Or.inr ⟨rfl, rfl⟩)) (RelTerm.var (by omega)))
            RelTerm.natLit))
    · exact RelConstStep.prim hresA
        (RelHead.primBinNat rfl (by decide) hstored add_premise)
  exact srcRun_to_red hbasis hconst (Or.inl ⟨rfl, rfl⟩) hrun

/-! ## A fully concrete instance

An `Env` with the `Nat` basis and the kernel image of
`fun (a : Nat) => Nat.add a (nat_lit 1)`, and the matching two-constant Src
program. Every hypothesis of `addLit_bridge` is proved. -/

def kF : Key .anon := .id ⟨⟨#[1]⟩⟩

def vAddLit : E :=
  .lam (.const natName []) (.app (.app (.const natAddName []) (.bvar 0)) (.lit (.natVal 1)))
    BinderMeta.leanNever

def tyNN : E := .forallE (.const natName []) (.const natName []) BinderMeta.leanNever

/-- A stand-in for the stored `Nat.add`: `Red.natOp` reads only that it is a
level-free definition (`natOpStored`), not its value. -/
def natAddStub : ConstantInfo .anon :=
  .defnInfo ⟨natAddName, [], .forallE (.const natName []) tyNN BinderMeta.leanNever⟩
    (.lam (.const natName []) (.lam (.const natName []) (.bvar 1) BinderMeta.leanNever)
      BinderMeta.leanNever) .abbrev

def envAdd : Env .anon :=
  ⟨[.defnInfo ⟨kF, [], tyNN⟩ vAddLit .abbrev, natAddStub, natRecA, natSuccA, natZeroA, natA]⟩

theorem envAdd_basis : natBasisStored envAdd = true := by decide

theorem envAdd_stored : natOpStored envAdd natAddName = true := by decide

theorem envAdd_find : envAdd.find? kF = some (.defnInfo ⟨kF, [], tyNN⟩ vAddLit .abbrev) := rfl

/-- The Src program: constant `0` is the definition in ingress's shape, and
constant `1` stands for `Nat.add`, resolved to the primitive `add` as
`Table.build` resolves the pinned `Nat.add`. -/
def bodyAddLit : Term :=
  .lam {} (.const 2 []) (.app (.app (.const 1 []) (.var 0) .strict .rel) (.natLit 1) .strict .rel)

def tyAddLit : Term := .pi {} {} (.const 2 []) (.const 2 [])

def e0 : IxCC.Src.ConstEntry :=
  { ref := .member default 0, addr := default, decl := .defn .defn .safe 0 tyAddLit bodyAddLit }

def e1 : IxCC.Src.ConstEntry :=
  { ref := .member default 0, addr := default, decl := .defn .defn .safe 0 (.sort .zero) (.sort .zero) }

def tAddLit : IxCC.Src.Table :=
  { resolve := .node none .leaf (.node (some (.prim .add)) .leaf .leaf) }

def pAddLit : Program :=
  { consts := .node (some e0) .leaf (.node (some e1) .leaf .leaf), size := 2, table := tAddLit }

theorem pAddLit_res0 : pAddLit.table.resolveOf 0 = none := rfl
theorem pAddLit_decl0 : pAddLit.decl? 0 = some (.defn .defn .safe 0 tyAddLit bodyAddLit) := rfl
theorem pAddLit_res1 : pAddLit.table.resolveOf 1 = some (.prim .add) := rfl

set_option maxHeartbeats 1000000 in
theorem pAddLit_run : IxCC.Src.run pAddLit 10 0 ([41].map .lit) = .ok (.lit 42) := by
  simp [IxCC.Src.run, IxCC.Src.evalConst, pAddLit_res0, pAddLit_decl0, pAddLit_res1,
    IxCC.Src.eval, bodyAddLit, IxCC.Src.applyAll, IxCC.Src.apply, IxCC.Src.force,
    IxCC.Src.headValue, IxCC.Src.Program.headArity, IxCC.Src.fire, IxCC.Src.forceAll,
    IxCC.Src.litArgs, IxCC.Src.PrimOp.evalLits, IxCC.Src.PrimOp.eval2, IxCC.Src.PrimOp.arity,
    IxCC.Src.PropWhen.allowsBeta, IxCC.Src.PropWhen.holds, IxCC.Src.Rel.irrAt,
    IxCC.Src.Rel.irrWhen]

/-- Every hypothesis closed: in `envAdd`, the root applied to `41` reduces to `42`. -/
theorem addLit_concrete :
    ∃ w, Red envAdd 0 (mkNatApp (.const kF []) [41]) w ∧ rawNatLit? w = some 42 :=
  addLit_bridge (p := pAddLit) (c := 0) (a := 1) pAddLit_res0 pAddLit_decl0 pAddLit_res1
    envAdd_basis envAdd_stored envAdd_find rfl rfl rfl pAddLit_run

end IxKernelBridge.Examples
