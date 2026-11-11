import IxVMRefinement.Core.Rep
import Ix.IxVM.Refinement.Statement
import Ix.IxVM.Consistency.Statement
import IxVM.Lookup

/-! # The slice's statements: one spec per function, and what is assumed

For a context `c` (the kernel environment, the keying, the view), each function
of the slice gets a spec over its observed derivations (`*Spec`): a derivation of
`whnf(e) = e'` gives `Red`, a nonzero `is_def_eq` gives `DefEq`, and so on. Every
spec is conditional on `Good c calls`: no hashed collision (the escape of the
statement, `View.HashedCollision`), every record the run loads is in the view,
and the stand-in size bound (below).

`CoreSpecs` bundles the specs of the functions proved by the induction;
`Assumed` collects the specs of the functions the slice calls but does not
prove. Each `Assumed` field is what another part of the refinement must prove
about that function, stated in the form the induction consumes.

**The size bound.** IxVM counts with field elements (`Lists::length`, the index
arithmetic of `Lists::lookup`, `take` and `drop`), and a count is faithful only
below the field's characteristic (past it, a count wraps around). The circuit
bounds the counts: at most `2^39` distinct memoized calls in a valid ROM
(`MemoBounded`, the consistency statement's `MemoCallsAtMost`); a list
`Lists::length` counts is shorter than that, because it recurses through every
suffix and lists of different lengths need different keys
(`IxVMRefinement.Core.Bound`, `length_lt`). Since `red_beta` matches the
consumed arguments structurally, the slice itself branches on no count; the
bound stays in `Good` for the rest of the core (`red_iota`'s field split,
`red_proj`'s index). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The prepared source's world. -/
abbrev W : World F := IxVM.source.world

/-- The view's address of an IxVM address. -/
def ixAddr (a : Bytes.Address) : _root_.Address := ⟨⟨a.toArray⟩⟩

/-- **The context of the slice**: the kernel environment the derivations are
related to, the keying of addresses, and the view the records are read from. -/
structure Ctx where
  env : Ix.Kernel.Env .anon
  κ : Bytes.Address → Ix.Kernel.Key .anon
  V : View
  /-- The records of the fragment: those whose loads the record loader's assumption `Assumed.getCI`
  covers (for the slice, level-free definitions, theorems, axioms, inductives and
  constructors whose terms the relation represents). -/
  frag : _root_.Address → Prop

/-- **The functions the fragment does not call**: the native dispatchers (a run
that calls none of them fires no native reduction: `try_prim_dispatch` returns
tag `0`), the slow tiers of definitional equality, and the context-lowering
rebase of `is_def_eq` (whose results would need a depth-weakening lemma). -/
def nativeNames : List String :=
  ["KernelWhnf::try_nat_dispatch_prewhnf", "KernelNatPrim::try_str_dispatch",
   "KernelNatPrim::try_bitvec_dispatch", "KernelInfer::try_dec_dispatch",
   "KernelNatPrim::try_int_prim_dispatch",
   "KernelDefEq::k_is_def_eq_slow", "KernelDefEq::k_def_eq_rebase"]

/-- **The circuit's size bound**: at most `2^39` distinct memoized calls, in a valid ROM
(the trace ROM of the compiled circuit is valid whenever the consistency statement's width
ROM is: `traceROM_valid`). -/
abbrev MemoBounded (calls : List (Call F)) : Prop :=
  ∃ rom : ROM F, rom.Valid ∧ IxVM.Consistency.MemoCallsAtMost IxVM.source rom calls (2 ^ 39)

/-- **The calls are good**: they hashed no collision; every record they load is
in the view and in the fragment; they call no native dispatcher; and they have at
most `2^39` distinct memoized calls in a valid ROM (the circuit's bound, `MemoBounded`). -/
def Good (c : Ctx) (calls : List (Call F)) : Prop :=
  ¬ c.V.HashedCollision [] calls ∧
  (∀ cl ∈ calls, cl.name = "Ingress::get_ci" → ∀ addr a, cl.args = [addr] →
    Bytes.RepAddressRef addrTy cl.heap a addr →
      (∃ lc, c.V.env.consts.get? (ixAddr a) = some lc) ∧ c.frag (ixAddr a)) ∧
  (∀ cl ∈ calls, cl.name ∉ nativeNames) ∧
  MemoBounded calls

/-- The fragment's hypothesis on loads: every record the calls load is in the view
and in the fragment. -/
def LoadsInFrag (c : Ctx) (calls : List (Call F)) : Prop :=
  ∀ cl ∈ calls, cl.name = "Ingress::get_ci" → ∀ addr a, cl.args = [addr] →
    Bytes.RepAddressRef addrTy cl.heap a addr →
      (∃ lc, c.V.env.consts.get? (ixAddr a) = some lc) ∧ c.frag (ixAddr a)

/-- The fragment's hypothesis on natives: no native dispatcher is called. -/
def NoNatives (calls : List (Call F)) : Prop := ∀ cl ∈ calls, cl.name ∉ nativeNames

theorem hashed_mono {calls₁ calls₂ : List (Call F)} (hsub : ∀ x ∈ calls₁, x ∈ calls₂)
    {b : ByteArray} (h : Hashed calls₁ b) : Hashed calls₂ b := by
  obtain ⟨cl, hm, rest⟩ := h
  exact ⟨cl, hsub cl hm, rest⟩

theorem collision_mono {V : View} {calls₁ calls₂ : List (Call F)}
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) (h : V.HashedCollision [] calls₁) :
    V.HashedCollision [] calls₂ := by
  rcases h with ⟨x, held, bytes, hpre, hh, hne, hx⟩ | ⟨bytes, hpre, hx⟩
  · refine .inl ⟨x, held, bytes, ?_, hashed_mono hsub hh, hne, hx⟩
    rcases hpre with hp | hp | ⟨hh', hx'⟩
    · exact .inl hp
    · exact .inr (.inl hp)
    · exact .inr (.inr ⟨hashed_mono hsub hh', hx'⟩)
  · refine .inr ⟨bytes, ?_, hx⟩
    rcases hpre with hp | hp
    · exact .inl hp
    · exact .inr (hashed_mono hsub hp)

theorem Good.sub {c : Ctx} {calls₁ calls₂ : List (Call F)} (g : Good c calls₂)
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) (_hlen : calls₁.length ≤ calls₂.length) :
    Good c calls₁ :=
  ⟨fun h => g.1 (collision_mono hsub h), fun cl hcl => g.2.1 cl (hsub cl hcl),
    fun cl hcl => g.2.2.1 cl (hsub cl hcl),
    let ⟨rom, hv, keys, hk, cover⟩ := g.2.2.2; ⟨rom, hv, keys, hk, fun cl hcl => cover cl (hsub cl hcl)⟩⟩

/-- **The record-load escape** (the mechanics of the statement's escape at one
load): with no hashed collision, every byte string the run hashed to a stored
address is the view's data at that address. -/
theorem load_escape {V : View} {calls : List (Call F)} {x : _root_.Address}
    {lc : Ixon.LazyConstant} (hst : V.env.consts.get? x = some lc)
    (nc : ¬ V.HashedCollision [] calls) :
    ∀ bytes, Hashed calls bytes → Address.blake3Pure bytes = x → V.Preimage x bytes := by
  intro bytes hh hx
  by_cases heq : bytes = lc.rawBytes
  · exact .inl ⟨lc, hst, heq.symm⟩
  · exact absurd (.inl ⟨x, lc.rawBytes, bytes, .inl (.inl ⟨lc, hst, rfl⟩), hh, heq, hx⟩) nc

/-! ## What a loaded record must be -/

/-- **A loaded constant represents the environment's constant**, on the slice:
a definition is the environment's level-free definition with a represented
closed value; a quotient or recursor is outside the slice (the environment of
the slice has none reachable). -/
structure CIRep (c : Ctx) (h : Heap F) (ci : SourceValue F)
    (kci : Option (Ix.Kernel.ConstantInfo .anon)) : Prop where
  defn : ∀ n ty value sf hint,
    loadValue h ci = .ok (.construct kciEnum "Defn" [n, ty, value, sf, hint]) →
    ∃ cv V hn, kci = some (.defnInfo cv V hn) ∧ cv.levelParams = [] ∧ RepEc c.κ h V value
  quot : ∀ xs, loadValue h ci ≠ .ok (.construct kciEnum "Quot" xs)
  recr : ∀ xs, loadValue h ci ≠ .ok (.construct kciEnum "Rec" xs)

/-! ## Instance names of the generic list functions -/

abbrev lengthName : String := Obs.Names.«Lists::length<&KernelTypes::KExprNode>»
abbrev lookupName : String := Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>»
abbrev concatName : String := Obs.Names.«Lists::concat<&KernelTypes::KExprNode>»
abbrev snocName : String := Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>»

theorem length_inst : instanceName [] "Lists::length" (some [kexprTy]) = lengthName := by
  decide +kernel
theorem lookup_inst : instanceName [] "Lists::lookup" (some [kexprTy]) = lookupName := by
  decide +kernel
theorem concat_inst : instanceName [] "Lists::concat" (some [kexprTy]) = concatName := by
  decide +kernel
theorem snoc_inst : instanceName [] "Lists::snoc" (some [kexprTy]) = snocName := by
  decide +kernel

/-! ## The specs of the proved functions -/

section
variable (c : Ctx) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
  (h' : Heap F) (calls : List (Call F))

/-- `whnf(rc, e, types)` and `whnf_core(rc, e, types)`: **`Red`**. -/
def WhnfSpec : Prop :=
  ∀ rc e types, args = [rc, e, types] → Good c calls →
    ∀ d Γ E, RepE c.κ d Γ h E e → ∃ E', RepE c.κ d Γ h' E' r ∧ Red c.env d E E'

/-- `whnf_with_spine(rc, head, spine, types)`: `Red` of the applied head. -/
def WithSpineSpec : Prop :=
  ∀ rc hd sp types, args = [rc, hd, sp, types] → Good c calls →
    ∀ d Γ H As, RepE c.κ d Γ h H hd → RepSpine c.κ d Γ h As sp →
      ∃ E', RepE c.κ d Γ h' E' r ∧ Red c.env d (K.mkAppN H As) E'

/-- `red_beta(rc, lam, spine, types)`: tag `1` is `Red` of the applied `λ` to the
reduct applied to the rest of the spine (`Red.betaGate`, one step per consumed
argument). Nothing is claimed for tag `0` (no move). -/
def RedBetaSpec : Prop :=
  ∀ rc lam sp types, args = [rc, lam, sp, types] →
    ∀ d Γ L As, RepE c.κ d Γ h L lam → RepSpine c.κ d Γ h As sp →
      ∀ x y, r = .tuple [.field 1, x, y] →
        ∃ E Bs, RepE c.κ d Γ h' E x ∧ RepSpine c.κ d Γ h' Bs y ∧
          Red c.env d (K.mkAppN L As) (K.mkAppN E Bs)

/-- `whnf_const_head(rc, addr, lvls, head, spine, types)`, at a level-free
constant head: `Red` of the applied constant. -/
def ConstHeadSpec : Prop :=
  ∀ rc addr lvls hd sp types, args = [rc, addr, lvls, hd, sp, types] → Good c calls →
    ∀ d Γ a As, Bytes.RepAddressRef addrTy h a addr →
      RepList klevelListEnum RepIxVMKUniv h [] lvls →
      RepE c.κ d Γ h (.const (c.κ a) []) hd → RepSpine c.κ d Γ h As sp →
      ∃ E', RepE c.κ d Γ h' E' r ∧ Red c.env d (K.mkAppN (.const (c.κ a) []) As) E'

/-- `apply_spine(head, spine)`: the application. -/
def ApplySpineSpec : Prop :=
  ∀ hd sp, args = [hd, sp] →
    ∀ d Γ H As, RepE c.κ d Γ h H hd → RepSpine c.κ d Γ h As sp →
      RepE c.κ d Γ h' (K.mkAppN H As) r

/-- `peel_beta(lam, spine, acc)`: a `λ`-telescope of as many binders as it
consumed arguments, its body at the deeper local depth, the consumed arguments
reversed onto the accumulator, the rest of the spine; at most one binder per
call. -/
def PeelSpec : Prop :=
  ∀ lam sp acc, args = [lam, sp, acc] →
    ∀ d Γ k L As Cs, RepEk c.κ d Γ k h L lam → RepSpine c.κ d Γ h As sp →
      RepSpine c.κ d Γ h Cs acc →
      ∃ deep cons rest Ts D, r = .tuple [deep, cons, rest] ∧ L = K.lams Ts D ∧
        Ts.length ≤ As.length ∧ Ts.length ≤ calls.length ∧
        RepEk c.κ d Γ (k + Ts.length) h' D deep ∧
        RepSpine c.κ d Γ h' ((As.take Ts.length).reverse ++ Cs) cons ∧
        RepSpine c.κ d Γ h' (As.drop Ts.length) rest

/-- `collect_spine(e)`: head and spine. -/
def CollectSpec : Prop :=
  ∀ e, args = [e] →
    ∀ d Γ E, RepE c.κ d Γ h E e →
      ∃ hdp sp H As, r = .tuple [hdp, sp] ∧ RepE c.κ d Γ h' H hdp ∧
        RepSpine c.κ d Γ h' As sp ∧ E = K.mkAppN H As

/-- `expr_inst_levels(e, params)` at an empty level list: the identity. -/
def InstLevelsSpec : Prop :=
  ∀ e ps, args = [e, ps] → RepList klevelListEnum RepIxVMKUniv h [] ps → r = e ∧ h' = h

/-- `is_def_eq(rc, a, b, types)` and its tiers: a nonzero answer is **`DefEq`**.
Nothing is claimed for `0`. -/
def DefEqSpec : Prop :=
  ∀ rc a b types, args = [rc, a, b, types] → Good c calls → r ≠ .field 0 →
    ∀ d Γ A B, RepE c.κ d Γ h A a → RepE c.κ d Γ h B b → Ix.Kernel.Rules.DefEq c.env d A B

/-- `de_args(rc, aa, bb, types)`: a nonzero answer is pairwise `DefEq`. -/
def DeArgsSpec : Prop :=
  ∀ rc aa bb types, args = [rc, aa, bb, types] → Good c calls → r ≠ .field 0 →
    ∀ d Γ As Bs, RepSpine c.κ d Γ h As aa → RepSpine c.κ d Γ h Bs bb →
      Ix.Kernel.Rules.DefEqList c.env d As Bs

end

/-- **The specs of the functions the induction proves**, one field per function,
each conditional on the function's name. -/
structure CoreSpecs (c : Ctx) (n : String) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) : Prop where
  whnf : n = "KernelWhnf::whnf" → WhnfSpec c args h r h' calls
  whnfCore : n = "KernelWhnf::whnf_core" → WhnfSpec c args h r h' calls
  withSpine : n = "KernelWhnf::whnf_with_spine" → WithSpineSpec c args h r h' calls
  redBeta : n = "KernelWhnf::red_beta" → RedBetaSpec c args h r h'
  constHead : n = "KernelWhnf::whnf_const_head" → ConstHeadSpec c args h r h' calls
  applySpine : n = "KernelWhnf::apply_spine" → ApplySpineSpec c args h r h'
  peel : n = "KernelWhnf::peel_beta" → PeelSpec c args h r h' calls
  collect : n = "KernelTypes::collect_spine" → CollectSpec c args h r h'
  instLevels : n = "KernelLevels::expr_inst_levels" → InstLevelsSpec args h r h'
  defEq : n = "KernelDefEq::k_is_def_eq" → DefEqSpec c args h r calls
  defEqCore : n = "KernelDefEq::k_is_def_eq_core" → DefEqSpec c args h r calls
  defEqOrdered : n = "KernelDefEq::k_is_def_eq_ordered" → DefEqSpec c args h r calls
  tryApp : n = "KernelDefEq::try_def_eq_app" → DefEqSpec c args h r calls
  deArgs : n = "KernelDefEq::de_args" → DeArgsSpec c args h r calls

/-- **The induction hypothesis**: the specs hold for every observed derivation
with fewer calls. -/
def IH (c : Ctx) (calls : List (Call F)) : Prop :=
  ∀ n args b v a cs, cs.length < calls.length → ObsFn W n args b v a cs →
    CoreSpecs c n args b v a cs

/-! ## What the slice assumes -/

/-- **The specs the slice assumes**: those of the functions it calls and does
not prove. Each field is a proof obligation of another part of the refinement
(the record loader, substitution, the native reductions, the rest of the core),
stated in the form the induction consumes. -/
structure Assumed (c : Ctx) : Prop where
  /-- The fragment (by reading `try_prim_dispatch`: every family other than `0` calls
  one of `nativeNames`): a run that calls no native dispatcher gets tag `0`. The
  general obligation (tags `1`, `2` are reductions) belongs to the proof of the native
  reductions, and needs kernel rules for `Int`, `BitVec`, `String` and decisions. -/
  tryPrim : ∀ rc addr lvls sp types h r h' calls,
    ObsFn W "KernelWhnf::try_prim_dispatch" [rc, addr, lvls, sp, types] h r h' calls →
    (∀ cl ∈ calls, cl.name ∉ nativeNames) → ∃ x, r = .tuple [.field 0, x]
  /-- The fragment (by reading `projection_definition_info`: tag `1` needs a `Proj`
  node, which no represented term has): the shortcut does not fire on a
  represented value. -/
  tryProjDef : ∀ value nl lvls sp h r h' calls,
    ObsFn W "KernelWhnf::try_reduce_projection_definition" [value, nl, lvls, sp] h r h' calls →
    ∀ d Γ V, RepE c.κ d Γ h V value → ∃ x, r = .tuple [.field 0, x]
  /-- The record loader (decoder, `Convert`, the kernel's reader, BLAKE3): if every byte string
  the load hashed to the address is the view's data there, the loaded constant
  represents the environment's constant at the address's key. -/
  getCI : ∀ addr h ci h' calls,
    ObsFn W "Ingress::get_ci" [addr] h ci h' calls →
    ∀ a, Bytes.RepAddressRef addrTy h a addr →
      c.frag (ixAddr a) →
      (∀ bytes, Hashed calls bytes → Address.blake3Pure bytes = ixAddr a →
        c.V.Preimage (ixAddr a) bytes) →
      CIRep c h' ci (c.env.find? (c.κ a))
  /-- Substitution: `expr_inst1` substitutes a closed value at index `0`. -/
  inst1 : ∀ body v h r h' calls,
    ObsFn W "KernelSubst::expr_inst1" [body, v, .field 0] h r h' calls →
    ∀ d Γ B A, RepEk c.κ d Γ 1 h B body → RepE c.κ d Γ h A v →
      RepE c.κ d Γ h' (B.instantiate1 A) r
  /-- Substitution: `expr_inst_many` is bulk substitution (`instantiateList`). -/
  instMany : ∀ body vs h r h' calls,
    ObsFn W "KernelSubst::expr_inst_many" [body, vs, .field 0] h r h' calls →
    ∀ d Γ B As, RepEk c.κ d Γ As.length h B body → RepSpine c.κ d Γ h As vs →
      RepE c.κ d Γ h' (B.instantiateList As 0) r
  /-- library: `Lists::concat` appends. -/
  concat : ∀ l₁ l₂ h r h' calls, ObsFn W concatName [l₁, l₂] h r h' calls →
    ∀ d Γ As Bs, RepSpine c.κ d Γ h As l₁ → RepSpine c.κ d Γ h Bs l₂ →
      RepSpine c.κ d Γ h' (As ++ Bs) r
  /-- library: `Bytes::address_eq` answers `1` only on equal addresses. -/
  addressEq : ∀ x y h r h' calls, ObsFn W "Bytes::address_eq" [x, y] h r h' calls →
    ∀ a b, Bytes.RepAddressRef addrTy h a x → Bytes.RepAddressRef addrTy h b y →
      r = .field 1 → a = b
  /-- library: `Lists::snoc` appends one. -/
  snoc : ∀ l v h r h' calls, ObsFn W snocName [l, v] h r h' calls →
    ∀ d Γ As A, RepSpine c.κ d Γ h As l → RepE c.κ d Γ h A v →
      RepSpine c.κ d Γ h' (As ++ [A]) r

/-! ## Matching helpers -/

theorem natCast_lt_inj {a b : Nat} (ha : a < 2 ^ 39) (hb : b < 2 ^ 39)
    (heq : (a : F) = (b : F)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at heq
  have hm : (2 ^ 39 : Nat) ≤ Aiur.Library.U32.Goldilocks.modulus := by
    norm_num [Aiur.Library.U32.Goldilocks.modulus]
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hm), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hm)] at heq

theorem matchList_wild {heap : Heap F} {types : Types} :
    ∀ (n : Nat) (vs : List (SourceValue F)) {bs : Environment F Nat},
      matchListWith (W.matchPattern types heap) (List.replicate n .wildcard) vs =
        .ok (some bs) → bs = []
  | 0, [], bs, h => by
    simp [matchListWith, pure, Except.pure] at h; first | exact h | exact h.symm
  | 0, _ :: _, _, h => by simp [matchListWith, pure, Except.pure] at h
  | _ + 1, [], _, h => by simp [matchListWith, pure, Except.pure] at h
  | n + 1, v :: vs, bs, h => by
    rw [List.replicate_succ] at h
    simp only [matchListWith, matchPattern_wildcard, bind, Except.bind] at h
    cases hr : matchListWith (W.matchPattern types heap) (List.replicate n .wildcard) vs with
    | error e => rw [hr] at h; cases h
    | ok o =>
      rw [hr] at h
      cases o with
      | none => cases h
      | some rest =>
        have := matchList_wild n vs hr
        subst this
        simp [pure, Except.pure] at h
        first | exact h | exact h.symm

/-- A constructor pattern of wildcards binds nothing. -/
theorem construct_wild_bs {heap : Heap F} {types : Types} {t : Generic.Ty} {ctor : String} {n : Nat}
    {v : SourceValue F} {bs : Environment F Nat}
    (h : W.matchPattern types heap (.construct t ctor (List.replicate n .wildcard)) v =
      .ok (some bs)) :
    ∃ vs, v = .construct (constructorName types t) ctor vs ∧ bs = [] := by
  obtain ⟨vs, hv, _, hml⟩ := matchPattern_construct_inv h
  exact ⟨vs, hv, matchList_wild n vs hml⟩

theorem wild_bs {heap : Heap F} {types : Types} {v : SourceValue F} {bs : Environment F Nat}
    (h : W.matchPattern types heap .wildcard v = .ok (some bs)) : bs = [] := by
  rw [matchPattern_wildcard] at h
  injection h with h; injection h with h; exact h.symm

theorem literal_bs {heap : Heap F} {types : Types} {x : F} {v : SourceValue F}
    {bs : Environment F Nat}
    (h : W.matchPattern types heap (.literal x) v = .ok (some bs)) : v = .field x ∧ bs = [] := by
  rw [matchPattern_literal_any] at h
  by_cases hv : v = .field x
  · simp only [hv, ↓reduceIte] at h
    injection h with h; injection h with h
    exact ⟨hv, by first | exact h.symm | exact h⟩
  · simp only [hv, ↓reduceIte] at h
    cases h

theorem litTuple_bs {heap : Heap F} {types : Types} {x : F} {name : String} {v : SourceValue F}
    {bs : Environment F Nat}
    (h : W.matchPattern types heap (.tuple [.literal x, .bind name]) v = .ok (some bs)) :
    ∃ y, v = .tuple [.field x, y] ∧ bs = [(name, y)] := by
  obtain ⟨vs, rfl, hlen, hml⟩ := matchPattern_tuple_inv h
  match vs, hlen, hml with
  | [y1, y2], _, hml =>
    simp only [matchListWith, matchPattern_literal_any, matchPattern_bind] at hml
    by_cases hy : y1 = .field x
    · subst hy
      simp [bind, Except.bind, pure, Except.pure] at hml
      exact ⟨y2, rfl, hml.symm⟩
    · simp [hy, bind, Except.bind, pure, Except.pure] at hml

end IxVM.Refinement.Core
