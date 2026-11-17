import IxVMRefinement.Decl.RedClosed
import IxVMRefinement.Decl.PrefixInv

/-! # Structure η typing at open parameter spines

The typing fact behind structure η reads the type of a full application of a structure's
constructor: `mk.{us} ps fs : T.{us} ps`. The rules infer it by instantiating the stored
constructor type along the spine, and `Expr.instantiate1` does not lift the value it substitutes:
a parameter with a loose bound variable is captured by the binders after it. So the fact holds at
parameters with no loose bound variable (free variables are allowed: the circuit's terms are of
that kind), and fails at open ones.

* **The open form is false** (`etaType_open_false`): at a stored constructor whose binders are
  never-zero at the use's levels, the io grade certifies no argument (`Infer.appSkip`), so the
  spine `mk (bvar 0) (sort 0) …` infers a type in which the loose variable has been replaced by
  the last argument. That type has no loose bound variable, and reduction keeps it so
  (`red_bclosed`), so it does not reduce to `T.{us} (bvar 0) …`. Hence `EtaStable` and the
  typing clause of `EtaUseFacts` fail at every environment storing an η-capable family with a
  parameter and a second binder (`not_etaStable_of_param`, `FoldStoreInv.not_etaStable`), and the
  statement read off the stored constructor alone, `EtaTypeOpenStmt`, is false
  (`EtaOpenExample.not_etaTypeOpen`).
* **The true form** (`EtaStableC`, `EtaUseFactsC`): the same clauses at parameters with no loose
  bound variable. It holds wherever the fold invariant does (`FoldStoreInv.etaStableC`,
  `FoldStoreInv.etaUseFactsC`), at every extension, from the constructor's stored shape alone
  (`etaType_of_closed_stored`).
* **Where the open form holds**: where no η-capable family has a parameter
  (`etaStable_of_etaShape_noParams`, `FoldStoreInv.etaUseFacts_noParams`).
* **What the consumers hold** (`TmL.bclosed`, `EtaUseFactsC.type_tml`): the two steps that read
  the clause (`try_eta_struct_step`, `eta_iota_fab_step`) read it at argument lists the circuit
  represents at local depth `0`, which have no loose bound variable.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Level LevelParam ConstantVal ConstantInfo IndCaps BinderMeta Key Mode)
open Ix.Kernel.Rules (Red Infer)

universe u

/-! ## The type of a spine at never-zero binders -/

section
variable {md : Mode}

/-- **A telescope's residual instantiated along a spine**, first argument outermost: the type the
rules infer for a full application (`instantiate1` at the depth of the binders still to come). -/
def spineI : List (Expr md) → Nat → Expr md → Expr md
  | [], _, e => e
  | a :: rest, n, e => spineI rest (n - 1) (e.instantiate1 a (n - 1))

/-- Instantiation keeps a telescope's binder data. -/
theorem stripPis_instantiate1_metas {v : Expr md} (k : Nat) : ∀ {e : Expr md}
    {bs bs' : List (Expr md × BinderMeta)} {body body' : Expr md} (j : Nat),
    e.stripPis k = some (bs, body) → (e.instantiate1 v j).stripPis k = some (bs', body') →
    bs'.map (·.2) = bs.map (·.2) := by
  induction k with
  | zero =>
    intro e bs bs' body body' j h1 h2
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    rw [← h1.1, ← h2.1]
  | succ k ih =>
    intro e bs bs' body body' j h1 h2
    cases e with
    | forallE ty b m =>
      simp only [Expr.instantiate1, Expr.stripPis, Option.map_eq_some_iff] at h1 h2
      obtain ⟨⟨bs₀, body₀⟩, h1', he1⟩ := h1
      obtain ⟨⟨bs₁, body₁⟩, h2', he2⟩ := h2
      simp only [Prod.mk.injEq] at he1 he2
      obtain ⟨rfl, rfl⟩ := he1
      obtain ⟨rfl, rfl⟩ := he2
      simp only [List.map_cons, ih (j + 1) h1' h2']
    | _ => simp [Expr.stripPis] at h1

/-- Level instantiation of a telescope, binder data included. -/
theorem stripPis_ilp (ks : List LevelParam) (us : List Level) :
    ∀ (n : Nat) {e : Expr md} {bs : List (Expr md × BinderMeta)} {res : Expr md},
      e.stripPis n = some (bs, res) →
      (e.instantiateLevelParams ks us).stripPis n =
        some (bs.map (fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })), res.instantiateLevelParams ks us)
  | 0, e, bs, res, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, .forallE dom bo mb, bs, res, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, res₀⟩, hst₀, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [Expr.instantiateLevelParams, Expr.stripPis, stripPis_ilp ks us n hst₀]
  | n + 1, .bvar _, _, _, h | n + 1, .fvar _ _, _, _, h | n + 1, .sort _, _, _, h
  | n + 1, .const _ _, _, _, h | n + 1, .app _ _, _, _, h | n + 1, .lam _ _ _, _, _, h
  | n + 1, .letE _ _ _ _, _, _, h | n + 1, .lit _, _, _, h | n + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

/-- **At never-zero binders every spine infers** (the io grade's `appSkip` certifies no
argument), with the residual instantiated along it. -/
theorem infer_spine_skip {env : Env md} {d : Nat} :
    ∀ (args : List (Expr md)) {f ty : Expr md} {bs : List (Expr md × BinderMeta)} {res : Expr md},
      Infer env .io d f ty → ty.stripPis args.length = some (bs, res) →
      (∀ b ∈ bs, b.2.pw.isNever = true) →
      Infer env .io d (Expr.mkAppN f args) (spineI args args.length res)
  | [], f, ty, bs, res, hf, hst, _ => by
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨-, rfl⟩ := hst
    exact hf
  | a :: as, f, ty, bs, res, hf, hst, hnev => by
    obtain ⟨dom, body, mb, rfl⟩ : ∃ dom body mb, ty = .forallE dom body mb := by
      cases ty <;> first | exact ⟨_, _, _, rfl⟩ | simp [Expr.stripPis] at hst
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₀, res₀⟩, hst₀, heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hmb : mb.pw.isNever = true := hnev (dom, mb) List.mem_cons_self
    have happ : Infer env .io d (.app f a) (body.instantiate1 a) :=
      Ix.Kernel.Rules.Infer.appSkip hf .refl hmb
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) as.length (e := body) 0
      (by rw [hst₀]; rfl)
    obtain ⟨⟨bs₁, res₁⟩, hst₁⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hres₁, -⟩ := Expr.stripPis_instantiate1_eq (v := a) as.length 0 hst₀ hst₁
    have hmeta := stripPis_instantiate1_metas (v := a) as.length 0 hst₀ hst₁
    have hnev₁ : ∀ b ∈ bs₁, b.2.pw.isNever = true := by
      intro b hb
      have h1 : b.2 ∈ bs₁.map (·.2) := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [hmeta] at h1
      obtain ⟨b₀, hb₀, he⟩ := List.mem_map.mp h1
      rw [← he]
      exact hnev b₀ (List.mem_cons_of_mem _ hb₀)
    have ih := infer_spine_skip as happ hst₁ hnev₁
    rw [hres₁, Nat.zero_add] at ih
    show Infer env .io d (Expr.mkAppN (.app f a) as)
      (spineI as (as.length + 1 - 1) (res₀.instantiate1 a (as.length + 1 - 1)))
    rw [Nat.add_sub_cancel]
    exact ih

/-- `infer_spine_skip` at a stated arity. -/
theorem infer_spine_skip' {env : Env md} {d : Nat} (args : List (Expr md)) {n : Nat}
    (hn : args.length = n) {f ty : Expr md} {bs : List (Expr md × BinderMeta)} {res : Expr md}
    (hf : Infer env .io d f ty) (hst : ty.stripPis n = some (bs, res))
    (hnev : ∀ b ∈ bs, b.2.pw.isNever = true) :
    Infer env .io d (Expr.mkAppN f args) (spineI args n res) := by
  subst hn
  exact infer_spine_skip args hf hst hnev

/-- Each argument of a spine is bounded by the number of binders after it. -/
def SpineBounded : List (Expr md) → Nat → Prop
  | [], _ => True
  | a :: rest, n => a.looseBVarsBounded (n - 1) = true ∧ SpineBounded rest (n - 1)

theorem spineBounded_of_closed : ∀ (args : List (Expr md)) (n : Nat),
    (∀ a ∈ args, a.looseBVarsBounded 0 = true) → SpineBounded args n
  | [], _, _ => trivial
  | a :: as, n, h =>
    And.intro (Expr.looseBVarsBounded_mono (Nat.zero_le _) (h a List.mem_cons_self))
      (spineBounded_of_closed as (n - 1) (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- **A spine whose arguments are captured by the binders after them closes the residual.** -/
theorem lbb_spineI : ∀ (args : List (Expr md)) {e : Expr md},
    e.looseBVarsBounded args.length = true → SpineBounded args args.length →
    (spineI args args.length e).looseBVarsBounded 0 = true
  | [], _, he, _ => he
  | a :: as, e, he, hb => by
    obtain ⟨ha, hrest⟩ := hb
    have hl : (a :: as).length - 1 = as.length := by simp
    have ha' : a.looseBVarsBounded as.length = true := by simpa using ha
    have hrest' : SpineBounded as as.length := by simpa using hrest
    show (spineI as ((a :: as).length - 1)
      (e.instantiate1 a ((a :: as).length - 1))).looseBVarsBounded 0 = true
    rw [hl]
    exact lbb_spineI as (lbb_instantiate1_le he ha') hrest'

/-- The spine the refutation uses: a loose bound variable, then closed sorts. -/
def openSpine (n : Nat) : List (Expr md) := .bvar 0 :: List.replicate (n - 1) (.sort .zero)

theorem openSpine_length {n : Nat} (hn : 1 ≤ n) : (openSpine (md := md) n).length = n := by
  simp only [openSpine, List.length_cons, List.length_replicate]
  omega

theorem spineBounded_openSpine {n : Nat} (hn : 2 ≤ n) :
    SpineBounded (openSpine (md := md) n) (openSpine (md := md) n).length := by
  rw [openSpine_length (by omega)]
  show (Expr.bvar 0 : Expr md).looseBVarsBounded (n - 1) = true ∧
    SpineBounded (List.replicate (n - 1) (Expr.sort .zero : Expr md)) (n - 1)
  refine ⟨?_, spineBounded_of_closed _ _ fun x hx => ?_⟩
  · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  · rw [List.eq_of_mem_replicate hx]
    rfl

theorem bvar_mem_take_openSpine {n nP : Nat} (hP : 1 ≤ nP) :
    (Expr.bvar 0 : Expr md) ∈ (openSpine (md := md) n).take nP := by
  obtain ⟨p, rfl⟩ : ∃ p, nP = p + 1 := ⟨nP - 1, by omega⟩
  simp [openSpine]

/-- **The typing clause of structure η is false at open parameters.** At a stored constructor
with a closed type whose first `nP + nF` binders are never-zero at the levels `us`, with a
parameter and a second binder, a full application whose first parameter is a loose bound variable
infers a type that does not reduce to `T.{us}` at the spine's parameters, for every `T`. -/
theorem etaType_open_false {env : Env md} (hS : BClosedStore env) {kc : Key md}
    {cvc : ConstantVal md} {nP nF : Nat} (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    (hty : cvc.type.looseBVarsBounded 0 = true)
    {cbs : List (Expr md × BinderMeta)} {res : Expr md}
    (hstrip : cvc.type.stripPis (nP + nF) = some (cbs, res))
    {us : List Level} (hus : us.length = cvc.levelParams.length)
    (hnev : ∀ b ∈ cbs, (Level.substPW cvc.levelParams us b.2.pw).isNever = true)
    (hP : 1 ≤ nP) (hn : 2 ≤ nP + nF) (T : Key md) (d : Nat) :
    ∃ (args : List (Expr md)) (ty : Expr md), args.length = nP + nF ∧
      Infer env .io d (Expr.mkAppN (.const kc us) args) ty ∧
      ¬ Red env d ty (Expr.mkAppN (.const T us) (args.take nP)) := by
  have hlen : (openSpine (md := md) (nP + nF)).length = nP + nF := openSpine_length (by omega)
  have hconst : Infer env .io d (.const kc us)
      (cvc.type.instantiateLevelParams cvc.levelParams us) :=
    Ix.Kernel.Rules.Infer.const (ci := .ctorInfo cvc nP nF) hkc rfl hus
  have hinf := infer_spine_skip' (openSpine (nP + nF)) hlen hconst
    (stripPis_ilp cvc.levelParams us (nP + nF) hstrip) (by
      intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
      exact hnev b₀ hb₀)
  refine ⟨openSpine (nP + nF), _, hlen, hinf, fun hred => ?_⟩
  have hres : res.looseBVarsBounded (nP + nF) = true := by
    simpa using Expr.stripPis_body_bounded (nP + nF) (j := 0) hstrip hty
  have hclosed := lbb_spineI (openSpine (md := md) (nP + nF))
    (e := res.instantiateLevelParams cvc.levelParams us)
    (by rw [hlen]; exact lbb_ilp _ _ hres) (spineBounded_openSpine hn)
  rw [hlen] at hclosed
  have hopen := red_bclosed hred hS hclosed
  rw [lbb_mkAppN, Bool.and_eq_true, List.all_eq_true] at hopen
  have h0 := hopen.2 _ (bvar_mem_take_openSpine hP)
  simp [Expr.looseBVarsBounded] at h0

/-- Binder data that is the zero-ness of a level never zero at `us` is never zero at `us`. -/
theorem never_of_zeroness {lps : List LevelParam} {us : List Level} {l : Level}
    (hnz : (Level.subst lps us l).isNeverZero = true) {cbs : List (Expr md × BinderMeta)}
    (hz : ∀ b ∈ cbs, b.2.pw = Level.zeronessOf l) :
    ∀ b ∈ cbs, (Level.substPW lps us b.2.pw).isNever = true := by
  intro b hb
  rw [hz b hb, ← Level.zeronessOf_subst, ← Level.isNeverZero_eq_isNever]
  exact hnz

end

/-! ## `EtaStable` and `EtaUseFacts` as stated fail at a family with a parameter -/

/-- **`EtaStable` and the typing clause of `EtaUseFacts` fail at an η-capable family with a
parameter and a second binder** whose constructor's binders are never-zero at some levels. -/
theorem not_etaStable_of_param {env : Env .anon} (hS : BClosedStore env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    (hty : cvc.type.looseBVarsBounded 0 = true)
    {cbs : List (KExpr × BinderMeta)} {res : KExpr}
    (hstrip : cvc.type.stripPis (nP + nF) = some (cbs, res))
    {us : List KLevel} (hus : us.length = cvc.levelParams.length)
    (hnev : ∀ b ∈ cbs, (Level.substPW cvc.levelParams us b.2.pw).isNever = true)
    (hP : 1 ≤ nP) (hn : 2 ≤ nP + nF) :
    ¬ EtaStable env ∧ ¬ EtaUseFacts env T kc cvT caps nP nF := by
  obtain ⟨args, ty, hlen, hinf, hnot⟩ := etaType_open_false hS hkc hty hstrip hus hnev hP hn T 0
  exact ⟨fun h => hnot (h T kc cvT cvc caps nP nF hT heta hctor hkc env
      (Ix.Kernel.EnvExt.refl env) 0 us args ty hlen hinf),
    fun h => hnot (h.type 0 us args ty hlen hinf)⟩

/-- **The same at the fold invariant**, with the binder data read as the zero-ness of a level
(the constructor check's `ctorZeroOk`, the projection table's `structSort`) that is never zero at
`us`. Every other premise is the family's own shape. -/
theorem FoldStoreInv.not_etaStable {env : Env .anon} (h : FoldStoreInv env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    {cbs : List (KExpr × BinderMeta)} {res : KExpr} {l : KLevel}
    (hstrip : cvc.type.stripPis (nP + nF) = some (cbs, res))
    (hz : ∀ b ∈ cbs, b.2.pw = Level.zeronessOf l)
    {us : List KLevel} (hus : us.length = cvc.levelParams.length)
    (hnz : (Level.subst cvc.levelParams us l).isNeverZero = true)
    (hP : 1 ≤ nP) (hn : 2 ≤ nP + nF) :
    ¬ EtaStable env ∧ ¬ EtaUseFacts env T kc cvT caps nP nF :=
  not_etaStable_of_param (BClosedStore.of_wf h.store.wf) hT heta hctor hkc
    (envWF_type_bclosed h.store.wf hkc) hstrip hus (never_of_zeroness hnz hz) hP hn

/-- **The prefix invariant excludes such a family**: `PrefixInv` carries `EtaStable` and the fold
invariant, so it does not hold at an environment storing an η-capable family with a parameter and
a second binder, never-zero at some levels. -/
theorem PrefixInv.no_param_eta {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Env .anon} (h : PrefixInv.{u} E t lim env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    {cbs : List (KExpr × BinderMeta)} {res : KExpr} {l : KLevel}
    (hstrip : cvc.type.stripPis (nP + nF) = some (cbs, res))
    (hz : ∀ b ∈ cbs, b.2.pw = Level.zeronessOf l)
    {us : List KLevel} (hus : us.length = cvc.levelParams.length)
    (hnz : (Level.subst cvc.levelParams us l).isNeverZero = true)
    (hP : 1 ≤ nP) (hn : 2 ≤ nP + nF) : False :=
  (h.store.not_etaStable hT heta hctor hkc hstrip hz hus hnz hP hn).1 h.etaStable

/-- **The typing clause at every spine**, read off the constructor's own stored shape. False:
`EtaOpenExample.not_etaTypeOpen`. -/
def EtaTypeOpenStmt : Prop :=
  ∀ (env : Env .anon) (T kc : KKey) (cvc : ConstantVal .anon) (nP nF : Nat)
    (cbs : List (KExpr × BinderMeta)),
    env.find? kc = some (.ctorInfo cvc nP nF) → cvc.levelParams.Nodup →
    cvc.type.stripPis (nP + nF) =
      some (cbs, Expr.mkAppN (.const T (cvc.levelParams.map .param))
        (Ix.Kernel.structPsAt nF nP)) →
    ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
      args.length = nP + nF →
      Infer env .io d (Expr.mkAppN (.const kc us) args) ty →
      Red env d ty (Expr.mkAppN (.const T us) (args.take nP))

/-! ## The true form: parameters with no loose bound variable -/

/-- **The typing clause at closed parameters** (free variables allowed), read off the stored
constructor. -/
def EtaTypeClosedStmt : Prop :=
  ∀ (env : Env .anon) (T kc : KKey) (cvc : ConstantVal .anon) (nP nF : Nat)
    (cbs : List (KExpr × BinderMeta)),
    env.find? kc = some (.ctorInfo cvc nP nF) → cvc.levelParams.Nodup →
    cvc.type.stripPis (nP + nF) =
      some (cbs, Expr.mkAppN (.const T (cvc.levelParams.map .param))
        (Ix.Kernel.structPsAt nF nP)) →
    ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
      args.length = nP + nF → (∀ s ∈ args.take nP, s.looseBVarsBounded 0 = true) →
      Infer env .io d (Expr.mkAppN (.const kc us) args) ty →
      Red env d ty (Expr.mkAppN (.const T us) (args.take nP))

theorem etaTypeClosed : EtaTypeClosedStmt :=
  fun _ _ _ _ _ _ _ hkc hnd hstrip _ _ _ _ hlen hcl hinf =>
    etaType_of_closed_stored hkc hnd hstrip hlen hcl hinf

/-- **`EtaStable` at closed parameters.** -/
def EtaStableC (env : Env .anon) : Prop :=
  ∀ (T kc : KKey) (cvT cvc : ConstantVal .anon) (caps : IndCaps .anon) (nP nF : Nat),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ env' : Env .anon, Ix.Kernel.EnvExt env env' →
      ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
        args.length = nP + nF → (∀ s ∈ args.take nP, s.looseBVarsBounded 0 = true) →
        Infer env' .io d (Expr.mkAppN (.const kc us) args) ty →
          Red env' d ty (Expr.mkAppN (.const T us) (args.take nP))

/-- **It holds wherever the stored η-capable families have their shape**, at every extension:
an extension keeps the constructor, and the inversion reads nothing else (a later projection
table or recursor is not read). -/
theorem etaStableC_of_etaShape {env : Env .anon} (h : EtaShape env) : EtaStableC env := by
  intro T kc cvT cvc caps nP nF hT heta hctor hkc env' hext d us args ty hlen hcl hinf
  obtain ⟨_, hshape⟩ := h T cvT caps hT heta
  obtain ⟨hnd, _, _, _, cbs, hstrip⟩ := hshape kc cvc nP nF hctor hkc
  exact etaType_of_closed_stored (hext.find hkc) hnd hstrip hlen hcl hinf

theorem FoldStoreInv.etaStableC {env : Env .anon} (h : FoldStoreInv env) : EtaStableC env :=
  etaStableC_of_etaShape h.etaShape

/-- **`EtaStable` as stated holds where no η-capable family has a parameter.** -/
theorem etaStable_of_etaShape_noParams {env : Env .anon} (h : EtaShape env)
    (h0 : ∀ T cvT caps, env.find? T = some (.indInfo cvT caps) → caps.eta = true →
      caps.etaParams = 0) : EtaStable env := by
  intro T kc cvT cvc caps nP nF hT heta hctor hkc env' hext d us args ty hlen hinf
  obtain ⟨_, hshape⟩ := h T cvT caps hT heta
  obtain ⟨hnd, _, hnP, _, cbs, hstrip⟩ := hshape kc cvc nP nF hctor hkc
  have h0' : nP = 0 := hnP.trans (h0 T cvT caps hT heta)
  subst h0'
  exact etaType_of_closed_stored (hext.find hkc) hnd hstrip hlen (by simp) hinf

/-- **`EtaStable` as stated across an extension that adds only families with no parameter**: the
families with a parameter are the shorter environment's, with their constructors, and keep its
`EtaStable`; the others hold from their shape. -/
theorem EtaStable.of_ext_noParams {env env₂ : Env .anon} (h : EtaStable env)
    (hext : Ix.Kernel.EnvExt env env₂) (hshape : EtaShape env₂)
    (hold : ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → caps.eta = true →
      caps.etaParams ≠ 0 → env.find? T = some (.indInfo cvT caps) ∧
        ∀ kc c, caps.etaCtor = some kc → env₂.find? kc = some c → env.find? kc = some c) :
    EtaStable env₂ := by
  intro T kc cvT cvc caps nP nF hT heta hctor hkc env' hext' d us args ty hlen hinf
  by_cases h0 : caps.etaParams = 0
  · obtain ⟨_, hsh⟩ := hshape T cvT caps hT heta
    obtain ⟨hnd, _, hnP, _, cbs, hstrip⟩ := hsh kc cvc nP nF hctor hkc
    have h0' : nP = 0 := hnP.trans h0
    subst h0'
    exact etaType_of_closed_stored (hext'.find hkc) hnd hstrip hlen (by simp) hinf
  · obtain ⟨hT₁, hk₁⟩ := hold T cvT caps hT heta h0
    exact h T kc cvT cvc caps nP nF hT₁ heta hctor (hk₁ kc _ hctor hkc) env' (hext.trans hext')
      d us args ty hlen hinf

/-- **`EtaUseFacts` at closed parameters.** -/
structure EtaUseFactsC (env : Env .anon) (T kc : KKey) (cvT : ConstantVal .anon)
    (caps : IndCaps .anon) (nP nF : Nat) : Prop where
  towers : Ix.Kernel.towerSlotsAll env T caps.etaFields = true
  sort : ∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
    caps.sortZ = Level.zeronessOf l
  type : ∀ (d : Nat) (us : List KLevel) (args : List KExpr) (ty : KExpr),
    args.length = nP + nF → (∀ s ∈ args.take nP, s.looseBVarsBounded 0 = true) →
    Infer env .io d (Expr.mkAppN (.const kc us) args) ty →
      Red env d ty (Expr.mkAppN (.const T us) (args.take nP))

theorem FoldStoreInv.etaUseFactsC {env : Env .anon} (h : FoldStoreInv env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env.find? kc = some (.ctorInfo cvc nP nF)) :
    EtaUseFactsC env T kc cvT caps nP nF where
  towers := h.etaTowers T cvT caps hT heta
  sort := (h.etaShape T cvT caps hT heta).1
  type := fun d us args ty hlen hcl hinf =>
    h.etaStableC T kc cvT cvc caps nP nF hT heta hctor hkc env (Ix.Kernel.EnvExt.refl env)
      d us args ty hlen hcl hinf

/-- **`EtaUseFacts` as stated, at a family with no parameter.** -/
theorem FoldStoreInv.etaUseFacts_noParams {env : Env .anon} (h : FoldStoreInv env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env.find? kc = some (.ctorInfo cvc 0 nF)) :
    EtaUseFacts env T kc cvT caps 0 nF :=
  ⟨h.etaTowers T cvT caps hT heta, (h.etaShape T cvT caps hT heta).1,
    fun d us args ty hlen hinf =>
      (h.etaUseFactsC hT heta hctor hkc).type d us args ty hlen (by simp) hinf⟩

/-! ## What the consumers hold -/

/-- **A list of top-level circuit terms has no loose bound variable** (a free de Bruijn index of
the circuit is an opened variable, `Tm.bvarFree`). -/
theorem TmL.bclosed {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Aiur.Heap F} {Es : List KExpr} {p : Aiur.SourceValue F}
    (rep : TmL κ d Γ h Es p) : ∀ E ∈ Es, E.looseBVarsBounded 0 = true := by
  induction rep with
  | nil _ => intro E hE; simp at hE
  | cons _ rh _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact Tm.looseBVarsBounded rh
    · exact ih E hE

/-- **The closed form serves the consumers**: at an argument list the circuit represents (as
`try_eta_struct_step` and `eta_iota_fab_step` hold theirs), the closed clause gives the open
one's conclusion. -/
theorem EtaUseFactsC.type_tml {env : Env .anon} {T kc : KKey} {cvT : ConstantVal .anon}
    {caps : IndCaps .anon} {nP nF : Nat} (hU : EtaUseFactsC env T kc cvT caps nP nF)
    {κ : _root_.Address → KKey} {d' : Nat} {Γ : Nat → KExpr} {h : Aiur.Heap F}
    {args : List KExpr} {p : Aiur.SourceValue F}
    (hrep : TmL κ d' Γ h args p) {d : Nat} {us : List KLevel} {ty : KExpr}
    (hlen : args.length = nP + nF)
    (hinf : Infer env .io d (Expr.mkAppN (.const kc us) args) ty) :
    Red env d ty (Expr.mkAppN (.const T us) (args.take nP)) :=
  hU.type d us args ty hlen (fun s hs => TmL.bclosed hrep s (List.mem_of_mem_take hs)) hinf

end IxVM.Refinement.Decl
