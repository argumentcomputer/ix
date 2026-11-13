import IxVMRefinement.Core.Specs.Common

/-! # Specs of `KernelWhnf`: weak head normalization

One spec per function of `IxVM/IxVM/Source/KernelWhnf.lean` (58). The normalizers and the
spine forms conclude `Red`; the step functions (`red_*`, `try_*`) conclude `Red` for the tags
that mean "moved"; the telescope walks conclude the certificate relations; the structure-η
scans state their meaning on the heap terms. A yes/no answer claims at every answer other than
`0` (the scans, whose useful answer is "none found", at every answer other than `1`, on
represented terms); nothing is claimed for tag `0` / answer `0` unless the docstring says so.

**Telescope certificates.** `certs_all` head-normalizes a telescope that is not syntactically a
`∀` and goes on. The rules' `Certs` has no such step, so the walks are stated with `CertsR`
(below): `Certs` with a `Red` step on the telescope. Where a rule needs `Certs` (`Red.iota`,
`Red.rescueK`, `Red.rescueEta`) the step lemma reads it through `CertsR.toCerts`
(`Core/Certs.lean`): a stored telescope has a binder for every argument (an environment fact),
and a `∀` reduces only to itself. Specs marked "after the pending batch" are stated for the
circuit with the checks that batch adds. -/

namespace IxVM.Refinement.Core.Specs.Whnf

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer Certs DefEqList)

set_option linter.unusedVariables false

/-! ## Vocabulary -/

/-- Application to a list of arguments. -/
abbrev mkAppN (f : KExpr) (zs : List KExpr) : KExpr := Ix.Kernel.Expr.mkAppN f zs

/-- A list of terms under `k` local binders. -/
abbrev TmLk (c : Ctx) (d : Nat) (Γ : Nat → KExpr) (k : Nat) (h : Heap F) (Es : List KExpr)
    (p : SourceValue F) : Prop :=
  RepList kexprListEnum (fun h E p => Tm c.κ d Γ h k E p) h Es p

/-- The binder datum `never` (default contracts, `bmeta` of any never-zero level). -/
def nbMeta : Ix.Kernel.BinderMeta := { pw := .never }

/-- A `λ`-telescope whose binders have the datum `never`, outermost first. -/
def lamsNb : List KExpr → KExpr → KExpr
  | [], D => D
  | T :: Ts, D => .lam T (lamsNb Ts D) nbMeta

/-- The domain of the `n`-th binder of a `∀`-telescope after instantiating the binders before it
with `zs`, in order (the arguments have no loose bound variable). -/
def piDomInst : KExpr → List KExpr → Nat → Option KExpr
  | .forallE dom _ _, _, 0 => some dom
  | .forallE _ b _, a :: zs, n + 1 => piDomInst (b.instantiate1 a) zs n
  | _, _, _ => none

/-- The sort a `∀`-telescope ends in after exactly `n` binders (`Core.piSortAt`). -/
abbrev piSortAt : Nat → KExpr → Option KLevel := IxVM.Refinement.Core.piSortAt

/-- The body under exactly `n` leading `λ`s. -/
def stripLams : Nat → KExpr → Option KExpr
  | 0, e => some e
  | n + 1, .lam _ b _ => stripLams n b
  | _, _ => none

/-- The body under exactly `n` leading `∀`s. -/
def stripForalls : Nat → KExpr → Option KExpr
  | 0, e => some e
  | n + 1, .forallE _ b _ => stripForalls n b
  | _, _ => none

/-- The first `n` binders are `λ`s whose datum, instantiated at `ks ↦ us`, is `never`. -/
def lamsNeverAt (ks : List Ix.Kernel.LevelParam) (us : List KLevel) : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .lam _ b m => (Ix.Kernel.Level.substPW ks us m.pw).isNever = true ∧ lamsNeverAt ks us n b
  | _ + 1, _ => False

/-- The first `n` binders are `∀`s whose datum is `never`. -/
def forallsNever : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .forallE _ b m => m.pw.isNever = true ∧ forallsNever n b
  | _ + 1, _ => False

/-- The `Nat` operation a primitive-family code stands for (`KernelRoleSpec::role_prim_family`,
family `1`). -/
def natOpOf : Nat → Option Ix.Kernel.Role
  | 1 => some .natSucc
  | 2 => some .natPred
  | 3 => some .natAdd
  | 4 => some .natSub
  | 5 => some .natMul
  | 6 => some .natDiv
  | 7 => some .natMod
  | 8 => some .natGcd
  | 9 => some .natPow
  | 10 => some .natLand
  | 11 => some .natLor
  | 12 => some .natXor
  | 13 => some .natShiftLeft
  | 14 => some .natShiftRight
  | 15 => some .natBeq
  | 16 => some .natBle
  | _ => none

/-- **Telescope certificates up to reduction of the telescope**: `Certs`, with a step
`Red env d T T'` allowed before any slot (where `certs_all` head-normalizes). -/
inductive CertsR (env : Ix.Kernel.Env .anon) (d : Nat) (lic : Bool) :
    KExpr → List KExpr → Prop where
  | nil {T : KExpr} : CertsR env d lic T []
  | skip {ty body arg : KExpr} {mb : Ix.Kernel.BinderMeta} {rest : List KExpr} :
      lic = true → mb.pw.isNever = true → CertsR env d lic (body.instantiate1 arg) rest →
      CertsR env d lic (.forallE ty body mb) (arg :: rest)
  | cert {ty body arg ta : KExpr} {mb : Ix.Kernel.BinderMeta} {rest : List KExpr} :
      Infer env .io d arg ta → DefEq env d ta ty → CertsR env d lic (body.instantiate1 arg) rest →
      CertsR env d lic (.forallE ty body mb) (arg :: rest)
  | red {T T' : KExpr} {zs : List KExpr} :
      Red env d T T' → CertsR env d lic T' zs → CertsR env d lic T zs

/-- **A recursor's loaded data**: the environment stores the recursor `ci` at `k`, and a loaded
`Rec` value with these fields represents it (`CIRep.recr`: level count, closed type, the
counts, the rules one for one). -/
def RecInfoAt (c : Ctx) (h : Heap F) (k : KKey)
    (nl recTy np ni nm nmi rules kf : SourceValue F) (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  c.env.find? k = some ci ∧
    ∃ u blk idx : SourceValue F,
      c.ci h (.construct kciEnum "Rec" [nl, recTy, np, ni, nm, nmi, rules, kf, u, blk, idx]) ci

/-- **`p` is the address of the recursor's major inductive**: the head of the domain of the
major premise (binder `mI`) of the recursor's type is the constant at `p`. -/
def MajorHead (c : Ctx) (cv : Ix.Kernel.ConstantVal .anon) (mI : Nat) (p : Bytes.Address) :
    Prop :=
  ∃ us, (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ (ixAddr p)) us)

/-- The common hypotheses of a recursor reduction: the head `.const k us` and the spine, the
recursor stored at `k` and loaded with these fields, a level count that fits. -/
def RecRedHyps (c : Ctx) (h : Heap F) (k : KKey) (us : List KLevel) (lvls : SourceValue F)
    (nl recTy np ni nm nmi rules kf : SourceValue F) (cv : Ix.Kernel.ConstantVal .anon)
    (mI rP : Nat) (rls : List (Ix.Kernel.RecRule .anon)) : Prop :=
  RecInfoAt c h k nl recTy np ni nm nmi rules kf (.recInfo cv mI rP rls) ∧
    LvListRep h us lvls

/-! ## Spines and β -/

/-- `apply_spine(head, spine)`: the application, at any local depth (no claim beyond the
image; allocates `App` nodes). -/
def apply_spine : SpecFn := fun c args h r h' calls =>
  ∀ hd sp, args = [hd, sp] → Good c calls →
    ∀ d Γ k H As, c.tmk d Γ k h H hd → TmLk c d Γ k h As sp →
      c.tmk d Γ k h' (mkAppN H As) r

/-- `peel_beta(lam, spine, acc)`: the gated part of β. The head is a `λ`-telescope `Ts` with
datum `never` (a binder is consumed only where `level_is_not_zero` answers `1`) over a body
`D` at `|Ts|` more local binders; the consumed arguments, reversed, go onto `acc`; the rest of
the spine is returned. -/
def peel_beta : SpecFn := fun c args h r h' calls =>
  ∀ lam sp acc, args = [lam, sp, acc] → Good c calls →
    ∀ d Γ k L As Cs, c.tmk d Γ k h L lam → c.tml d Γ h As sp → c.tml d Γ h Cs acc →
      ∃ deep cons rest Ts D, r = .tuple [deep, cons, rest] ∧ L = lamsNb Ts D ∧
        Ts.length ≤ As.length ∧ c.tmk d Γ (k + Ts.length) h' D deep ∧
        c.tml d Γ h' ((As.take Ts.length).reverse ++ Cs) cons ∧
        c.tml d Γ h' (As.drop Ts.length) rest

/-- `peel_beta_cert(rc, lam, spine, acc, types)`: the certified β walk. From a term `L` under
`|Cs|` local binders whose bound variables the consumed arguments `Cs` (`acc`, innermost first)
stand for, applied to the spine `As`: `m` more arguments are consumed (`Red.betaGate` at a
`never` datum, `Red.beta` with the argument's io-grade type definitionally equal to the
domain otherwise), leaving the body `D` under `|Cs| + m` binders. It stops at the first
certificate that fails; nothing more is claimed. -/
def peel_beta_cert : SpecFn := fun c args h r h' calls =>
  ∀ rc lam sp acc types, args = [rc, lam, sp, acc, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ L Cs As, c.tmk d Γ Cs.length h L lam → c.tml d Γ h Cs acc → c.tml d Γ h As sp →
        ∃ deep cons rest m D, r = .tuple [deep, cons, rest] ∧ m ≤ As.length ∧
          c.tmk d Γ (Cs.length + m) h' D deep ∧
          c.tml d Γ h' ((As.take m).reverse ++ Cs) cons ∧ c.tml d Γ h' (As.drop m) rest ∧
          Red c.env d (mkAppN (L.instantiateList Cs 0) (As.take m))
            (D.instantiateList ((As.take m).reverse ++ Cs) 0)

/-- `beta_more(rc, deep, rest, consumed, types)`: `peel_beta_cert` where arguments remain and
the body is a `λ`, else no move; the same claim (note the argument order). -/
def beta_more : SpecFn := fun c args h r h' calls =>
  ∀ rc deep rest cons types, args = [rc, deep, rest, cons, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ L Cs As, c.tmk d Γ Cs.length h L deep → c.tml d Γ h Cs cons → c.tml d Γ h As rest →
        ∃ deep' cons' rest' m D, r = .tuple [deep', cons', rest'] ∧ m ≤ As.length ∧
          c.tmk d Γ (Cs.length + m) h' D deep' ∧
          c.tml d Γ h' ((As.take m).reverse ++ Cs) cons' ∧ c.tml d Γ h' (As.drop m) rest' ∧
          Red c.env d (mkAppN (L.instantiateList Cs 0) (As.take m))
            (D.instantiateList ((As.take m).reverse ++ Cs) 0)

/-- `red_beta(rc, lam, spine, types)`: tag `1` is `Red` of the applied `λ` to the reduct
applied to the rest of the spine (`Red.betaGate` and `Red.beta`, one per consumed argument).
Tag `0`: no move, no claim. -/
def red_beta : SpecFn := fun c args h r h' calls =>
  ∀ rc lam sp types, args = [rc, lam, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ L As, c.tm d Γ h L lam → c.tml d Γ h As sp →
      ∀ x y, r = .tuple [.field 1, x, y] →
        ∃ E Bs, c.tm d Γ h' E x ∧ c.tml d Γ h' Bs y ∧ Red c.env d (mkAppN L As) (mkAppN E Bs)

/-! ## Projections -/

/-- `red_proj(rc, struct_addr, fidx, scrut, types)`: tag `1` is `Red.proj`: the projection
`fidx` of the structure at `struct_addr` out of the scrutinee reduces to the result. Tag `0`:
no move. (The circuit fires only at a native structure with one constructor, no indices and a
never-zero sort at the constructor's levels; `Red.proj`'s `FireSem` is then vacuous and its
licensed `Certs` is all `never` skips, which the proof reads off the stored types.) -/
def red_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc sa fidx scrut types, args = [rc, sa, fidx, scrut, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ (s : Bytes.Address) (i : F) S,
      RepAddr h s sa → fidx = .field i → c.tm d Γ h S scrut →
      ∀ x, r = .tuple [.field 1, x] →
        ∃ E, c.tm d Γ h' E x ∧ Red c.env d (.proj (c.κ (ixAddr s)) (ZMod.val i) S) E

/-- `projection_definition_info(val, arity)`: tag `1` recognizes a projection function's value,
`λ … λ, proj s f (bvar j)`: the value (under `arity` local binders) is `m` more `λ`s over
`.proj (κ s) f (.bvar (n - 1 - j))` with `n = arity + m` and `j < n`, for an arity below `2^32`
(the counter is a field element). Tag `0`: no claim. -/
def projection_definition_info : SpecFn := fun c args h r h' calls =>
  ∀ val arity, args = [val, arity] → Good c calls →
    ∀ d Γ (a : F) V, arity = .field a → ZMod.val a < 4294967296 →
      c.tmk d Γ (ZMod.val a) h V val →
      ∀ (n f j : F) sp, r = .tuple [.field 1, .field n, sp, .field f, .field j] →
        ∃ (s : Bytes.Address) (m : Nat), RepAddr h' s sp ∧ ZMod.val n = ZMod.val a + m ∧
          ZMod.val j < ZMod.val n ∧
          stripLams m V = some (.proj (c.κ (ixAddr s)) (ZMod.val f)
            (.bvar (ZMod.val n - 1 - ZMod.val j)))

/-- `lams_never(v, n, lvls)`: a nonzero answer means the first `n` binders of the value are
`λ`s whose datum, at the levels `lvls` (positional parameters), is `never`. Answer `0`: no claim. -/
def lams_never : SpecFn := fun c args h r h' calls =>
  ∀ v n lvls, args = [v, n, lvls] → Good c calls →
    ∀ d Γ k V (m : F) us, c.tmk d Γ k h V v → n = .field m → LvListRep h us lvls →
      r ≠ .field 0 → lamsNeverAt (List.range us.length) us (ZMod.val m) V

/-- `try_reduce_projection_definition(value, nl, lvls, spine)`: the projection-function
shortcut. For the definition stored at `k` with this value (its level parameters, a permutation
of the positions as `ValRep` records, renamed to positions, `posOf`, as the loaded constant holds
it) and level count, tag `1` is `Red` of the
applied constant (`Red.delta`, then `Red.betaGate` at each of the value's `λ`s, whose
data are `never` at the use's levels) to the result. Tag `0`: no claim. -/
def try_reduce_projection_definition : SpecFn := fun c args h r h' calls =>
  ∀ value nl lvls sp, args = [value, nl, lvls, sp] → Good c calls →
    ∀ d Γ k cv V hn us As, c.env.find? k = some (.defnInfo cv V hn) →
      c.tmc h (posOf cv.levelParams V) value →
      cv.levelParams.Perm (List.range cv.levelParams.length) →
      cv.levelParams.length < 4294967296 →
      nl = .field (cv.levelParams.length : F) → LvListRep h us lvls → c.tml d Γ h As sp →
      ∀ x, r = .tuple [.field 1, x] →
        ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-! ## Unfolding and stored-shape tests -/

/-- `red_unfold(ci, lvls)`: **every tag other than `0` is `1` or `2`.** Tag `1`: the loaded
constant is a definition and the result represents its value at the levels `lvls`
(`instantiateLevelParams` at its parameters; the level count matches): `Red.delta`'s reduct.
Tag `2`: the same for a theorem: the reduct of `Red.deltaThm`, whose premises come from
`EnvFacts.thmTyped`. Tag `0`: no claim. -/
def red_unfold : SpecFn := fun c args h r h' calls =>
  ∀ v lvls, args = [v, lvls] → Good c calls → ∀ ci us, c.ci h v ci → LvListRep h us lvls →
    ∀ (t : F) x, r = .tuple [.field t, x] → t ≠ 0 →
      (t = 1 ∧ ∃ cv V hn, ci = .defnInfo cv V hn ∧ us.length = cv.levelParams.length ∧
        c.tmc h' (V.instantiateLevelParams cv.levelParams us) x) ∨
      (t = 2 ∧ ∃ cv V, ci = .thmInfo cv V ∧ us.length = cv.levelParams.length ∧
        c.tmc h' (V.instantiateLevelParams cv.levelParams us) x)

/-- `type_sort_never(ty, n, lvls)`: a nonzero answer means the type is syntactically `n` `∀`s
ending in a sort `l` that is never zero at the levels `lvls` (`Level.isNeverZero` of the
substitution). Answer `0`: no claim. -/
def type_sort_never : SpecFn := fun c args h r h' calls =>
  ∀ ty n lvls, args = [ty, n, lvls] → Good c calls →
    ∀ d Γ k T (m : F) us, c.tmk d Γ k h T ty → n = .field m → LvListRep h us lvls →
      r ≠ .field 0 → ∃ l, piSortAt (ZMod.val m) T = some l ∧
        (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true

/-- `slots_never(t, n)`: a nonzero answer means the first `n` binders of the telescope are
`∀`s with the datum `never` (`Certs.skip`'s premise at each slot). Answer `0`: no claim. -/
def slots_never : SpecFn := fun c args h r h' calls =>
  ∀ t n, args = [t, n] → Good c calls →
    ∀ d Γ k T (m : F), c.tmk d Γ k h T t → n = .field m → r ≠ .field 0 →
      forallsNever (ZMod.val m) T

/-- `pi_peel(t, args, subs_rev, n)`: tag `1` gives the domain of binder `n` of the telescope,
the telescope's bound variables instantiated by `subs_rev` (innermost first) and the binders
before `n` by `args` in order. Tag `0`: no claim. -/
def pi_peel : SpecFn := fun c args h r h' calls =>
  ∀ t zs subs n, args = [t, zs, subs, n] → Good c calls →
    ∀ d Γ T Cs As (m : F), c.tmk d Γ Cs.length h T t → c.tml d Γ h Cs subs →
      c.tml d Γ h As zs → n = .field m →
      ∀ x, r = .tuple [.field 1, x] →
        ∃ D, c.tm d Γ h' D x ∧ piDomInst (T.instantiateList Cs 0) As (ZMod.val m) = some D

/-- `pi_residual(t, args, subs_rev)`: tag `1` gives the telescope's codomain after all of
`args` (`Ix.Kernel.piResidual`), its bound variables instantiated by `subs_rev` first. Tag `0`:
no claim. -/
def pi_residual : SpecFn := fun c args h r h' calls =>
  ∀ t zs subs, args = [t, zs, subs] → Good c calls →
    ∀ d Γ T Cs As, c.tmk d Γ Cs.length h T t → c.tml d Γ h Cs subs → c.tml d Γ h As zs →
      ∀ x, r = .tuple [.field 1, x] →
        ∃ R, c.tm d Γ h' R x ∧ Ix.Kernel.piResidual (T.instantiateList Cs 0) As = some R

/-- `find_rule(rules, cidx)`: tag `1` finds the rule whose position (counted from `j`, the
first rule's) is `cidx`: its field count and closed right-hand side. Tag `0`: no claim. -/
def find_rule : SpecFn := fun c args h r h' calls =>
  ∀ rules cidx, args = [rules, cidx] → Good c calls →
    ∀ ps j rls, RulesRep c.κ h ps j rules rls →
      ∀ nf rhs, r = .tuple [.field 1, nf, rhs] →
        ∃ i rl, rls[i]? = some rl ∧ cidx = .field ((j + i : Nat) : F) ∧
          nf = .field (rl.nfields : F) ∧ c.tmc h' (posOf ps rl.rhs) rhs

/-! ## Telescope certificates -/

/-- `certs_all(rc, t, args, subs_rev, types)`: a nonzero answer is the unlicensed telescope
certificate of `args` against the telescope (its bound variables instantiated by `subs_rev`
first; `CertsR … false`: up to reduction of the telescope). Answer `0`: no claim. -/
def certs_all : SpecFn := fun c args h r h' calls =>
  ∀ rc t zs subs types, args = [rc, t, zs, subs, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ T Cs As, c.tmk d Γ Cs.length h T t → c.tml d Γ h Cs subs → c.tml d Γ h As zs →
        r ≠ .field 0 → CertsR c.env d false (T.instantiateList Cs 0) As

/-- `iota_certs(rc, rec_ty_i, rec_args, n_rec, cty, clvls, margs, n_ctor, types)`: a nonzero
answer gives `Red.iota`'s two licensed telescope walks (`CertsR … true`, read as `Certs` by
`CertsR.toCerts`): the recursor's (level-instantiated) type over its arguments, and the
constructor's type at the levels `clvls` over the major's arguments. `n_rec`, `n_ctor` are the
walks' lengths. Answer `0`: no claim. -/
def iota_certs : SpecFn := fun c args h r h' calls =>
  ∀ rc rt ra nr cty clvls ma nc types,
    args = [rc, rt, ra, nr, cty, clvls, ma, nc, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ RT RA CT cus MA, c.tmc h RT rt → c.tml d Γ h RA ra → nr = .field (RA.length : F) →
        c.tmc h CT cty → LvListRep h cus clvls → c.tml d Γ h MA ma →
        nc = .field (MA.length : F) → RA.length < 2 ^ 39 → MA.length < 2 ^ 39 → r ≠ .field 0 →
          CertsR c.env d true RT RA ∧
            CertsR c.env d true (CT.instantiateLevelParams (List.range cus.length) cus) MA

/-- `iota_cmp(rc, rec_ty_i, pre, major_idx, cty, clvls, cnp, margs, nindices, types)`:
a nonzero answer gives `Red.iota`'s comparisons, read off the major's domain `MD` in the
recursor's (level-instantiated) type instantiated by the arguments before the major: the
constructor's levels equal `MD`'s head's levels, the constructor's parameters are pairwise
definitionally equal to `MD`'s, and for an indexed family the residual indices of the
constructor's type at the major's arguments are pairwise definitionally equal to `MD`'s
indices. Answer `0`: no claim. Stated for the circuit after the fold-in regeneration, which
compares the indices only when the residual's heap head is a constant (so its arguments are the
image's); its path lemmas change at the pin. -/
def iota_cmp : SpecFn := fun c args h r h' calls =>
  ∀ rc rt pre mi cty clvls cnp ma ni types,
    args = [rc, rt, pre, mi, cty, clvls, cnp, ma, ni, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ RT PRE (m : F) CT cus (np : F) MA (nix : F), c.tmc h RT rt → c.tml d Γ h PRE pre →
        mi = .field m → c.tmc h CT cty → LvListRep h cus clvls → cnp = .field np →
        c.tml d Γ h MA ma → ni = .field nix → r ≠ .field 0 →
        ∃ (MD : KExpr) (k : KKey) (mus : List KLevel), piDomInst RT PRE (ZMod.val m) = some MD ∧
          MD.getAppFn = .const k mus ∧ LvEqList cus mus ∧
          DefEqList c.env d (MA.take (ZMod.val np)) (MD.getAppArgs.take (ZMod.val np)) ∧
          (nix ≠ 0 → ∃ RES,
            Ix.Kernel.piResidual (CT.instantiateLevelParams (List.range cus.length) cus) MA =
              some RES ∧
            DefEqList c.env d (RES.getAppArgs.drop (ZMod.val np))
              (MD.getAppArgs.drop (ZMod.val np)))

/-! ## ι -/

/-- `red_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices, rules, rec_parent,
major, types)`: `Red.iota` on a prepared major. For the recursor stored at `k` (loaded with
these fields), whose major inductive is at `rec_parent` (`MajorHead`), at levels of the right
count, applied to `As` whose major argument reduces to `M`: tag `1` is `Red` of the applied
recursor to the result. Tag `0`: no claim. The proof reads `EnvFacts.recRules` for the rule
lookup and the circuit's guard `compute_iprj_addr(cblock, cind) = rec_parent`. -/
def red_iota : SpecFn := fun c args h r h' calls =>
  ∀ rc rt lvls sp np nm nmi ni rules rp major types,
    args = [rc, rt, lvls, sp, np, nm, nmi, ni, rules, rp, major, types] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k us nl kf cv mI rP rls (p : Bytes.Address) As M,
        RecRedHyps c h k us lvls nl rt np ni nm nmi rules kf cv mI rP rls →
        us.length = cv.levelParams.length → RepAddr h p rp → MajorHead c cv mI p →
        c.tml d Γ h As sp → c.tm d Γ h M major → Red c.env d (As.getD mI (.bvar 0)) M →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-- `whnf_iota_major(rc, e, types)`: `Red` (whnf, then theorem heads unfolded at the major,
`Red.deltaThm`). -/
def whnf_iota_major : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ E', c.tm d Γ h' E' r ∧ Red c.env d E E'

/-- `try_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices, rules, types, head,
rec_parent)`: ι with the major's preparation. For the recursor stored at `k`, applied at
levels of the right count: tags `1` (the reduct) and `2` (the application itself) are `Red` of
the applied recursor to the result. Tag `0`: no claim. -/
def try_iota : SpecFn := fun c args h r h' calls =>
  ∀ rc rt lvls sp np nm nmi ni rules types hd rp,
    args = [rc, rt, lvls, sp, np, nm, nmi, ni, rules, types, hd, rp] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k us nl kf cv mI rP rls (p : Bytes.Address) As,
        RecRedHyps c h k us lvls nl rt np ni nm nmi rules kf cv mI rP rls →
        us.length = cv.levelParams.length → RepAddr h p rp → MajorHead c cv mI p →
        c.tm d Γ h (.const k us) hd → c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → (t = 1 ∨ t = 2) →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-- `k_synth_fab(rc, raw_major, cidx, nparams, rec_parent, types)`: the K rescue's
fabrication. For a single-rule recursor stored at `k` whose rule has the K bit (`rl.k = true`,
which the caller reads off the record's K flag), whose major inductive is at `rec_parent`,
with the rule's index `cidx` and parameter count `nparams`: tag `1` gives `fab` with
`Red.rescueK`: the major reduces to it. Tag `0`: no claim. -/
def k_synth_fab : SpecFn := fun c args h r h' calls =>
  ∀ rc maj cidx np rp types, args = [rc, maj, cidx, np, rp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k nl rt ni nm nmi rules cv mI rP rl (p : Bytes.Address) M,
        RecInfoAt c h k nl rt np ni nm nmi rules (.field 1) (.recInfo cv mI rP [rl]) →
        rl.k = true →
        cidx = .field 0 → RepAddr h p rp → MajorHead c cv mI p → c.tm d Γ h M maj →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ FAB, c.tm d Γ h' FAB x ∧ Red c.env d M FAB

/-- `try_k_synth_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices, rules,
rec_parent, types)`: K-like ι: the K rescue then ι on the fabricated major. For a recursor
stored at `k` with the K flag set in its record, at levels of the right count: tag `1` is
`Red` of the applied recursor to the result. Tag `0`: no claim. -/
def try_k_synth_iota : SpecFn := fun c args h r h' calls =>
  ∀ rc rt lvls sp np nm nmi ni rules rp types,
    args = [rc, rt, lvls, sp, np, nm, nmi, ni, rules, rp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k us nl cv mI rP rls (p : Bytes.Address) As,
        RecRedHyps c h k us lvls nl rt np ni nm nmi rules (.field 1) cv mI rP rls →
        us.length = cv.levelParams.length → RepAddr h p rp → MajorHead c cv mI p →
        c.tml d Γ h As sp →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-- `eta_iota_fab(rc, ind_nl, ind_ty, ind_np, block, idx, parent, major, types)`: the
structure-η rescue's fabrication. For a single-rule recursor stored at `k` whose rule has the
η bit (`rl.eta = true`, which the caller establishes from its shape checks) and whose major
inductive, at `parent`, is loaded with these fields: tag `1` gives `fab` with
`Red.rescueEta`: the major reduces to it. Tag `0`: no claim. -/
def eta_iota_fab : SpecFn := fun c args h r h' calls =>
  ∀ rc inl ity inp blk idx par major types,
    args = [rc, inl, ity, inp, blk, idx, par, major, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k nl rt np ni nm nmi rules kf cv mI rP rl (p : Bytes.Address) ici nix nc u M,
        RecInfoAt c h k nl rt np ni nm nmi rules kf (.recInfo cv mI rP [rl]) →
        rl.eta = true →
        RepAddr h p par → MajorHead c cv mI p →
        c.env.find? (c.κ (ixAddr p)) = some ici →
        c.ci h (.construct kciEnum "Induct" [inl, ity, inp, nix, nc, u, blk, idx]) ici →
        c.tm d Γ h M major →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ FAB, c.tm d Γ h' FAB x ∧ Red c.env d M FAB

/-- `try_struct_eta_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices, rules,
types)`: structure-η ι: the η rescue then ι on the fabricated major. For a recursor stored at
`k`, at levels of the right count: tag `1` is `Red` of the applied recursor to the result. Tag
`0`: no claim. -/
def try_struct_eta_iota : SpecFn := fun c args h r h' calls =>
  ∀ rc rt lvls sp np nm nmi ni rules types,
    args = [rc, rt, lvls, sp, np, nm, nmi, ni, rules, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k us nl kf cv mI rP rls As,
        RecRedHyps c h k us lvls nl rt np ni nm nmi rules kf cv mI rP rls →
        us.length = cv.levelParams.length → c.tml d Γ h As sp →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-- `red_rec(rc, nlvls, rec_ty, lvls, head, spine, nparams, nindices, nmotives, nminors, rules,
k_flag, types)`: the recursor dispatch (K, ι, structure-η ι). For the recursor stored at `k`
(loaded with these fields) applied to `As`: tags `1` (ι or structure-η ι), `2` (stuck: the
application) and `3` (the K reduct) are `Red` of the applied recursor to the result. Tag `0`:
no claim. The K branch runs only where `se_parent_addr` answers a nonzero tag (which
gives `MajorHead` for `try_k_synth_iota`). Stated for the circuit after the pending batch; its
path lemmas change at the pin. -/
def red_rec : SpecFn := fun c args h r h' calls =>
  ∀ rc nl rt lvls hd sp np ni nm nmi rules kf types,
    args = [rc, nl, rt, lvls, hd, sp, np, ni, nm, nmi, rules, kf, types] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ k us cv mI rP rls As,
        RecRedHyps c h k us lvls nl rt np ni nm nmi rules kf cv mI rP rls →
        c.tm d Γ h (.const k us) hd → c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → (t = 1 ∨ t = 2 ∨ t = 3) →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const k us) As) E

/-! ## Quotients -/

/-- `quot_certs(rc, is_lift, addr, lvls, rec_args, mk_addr, mk_lvls, mk_args, types)`: for the
eliminator the table binds at `addr` (`Quot.lift` with six arguments and two levels when
`is_lift = 1`, `Quot.ind` with five and one when `0`) and `Quot.mk`, bound at `mk_addr`, with
three arguments (the caller has checked the roles, in force, and the counts; where a level
is never zero a walk is skipped without reading the stored type, so the claim needs them): a
nonzero answer gives `Red.iota`'s two licensed walks (`CertsR … true`, read as `Certs` by
`CertsR.toCerts`), the eliminator's stored type at `lvls` over its arguments and `Quot.mk`'s
stored type at `mk_lvls` over its arguments, and, unless
the eliminator is `Quot.lift` at a never-zero motive level (where every datum of the rule's
right-hand side is `never`), the premise of the right-hand side's last `β`: the io-grade type
of `Quot.mk`'s third argument is definitionally equal to the eliminator's first. Answer `0`: no
claim. Stated for the circuit after the pending batch; its path lemmas change at the pin. -/
def quot_certs : SpecFn := fun c args h r h' calls =>
  ∀ rc il addr lvls ra mk mklvls ma types,
    args = [rc, il, addr, lvls, ra, mk, mklvls, ma, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a b : Bytes.Address) us mus RA MA, RepAddr h a addr → LvListRep h us lvls →
        c.tml d Γ h RA ra → RepAddr h b mk → LvListRep h mus mklvls → c.tml d Γ h MA ma →
        ((il = .field 1 ∧ c.t.addressOf? .quotLift = some (ixAddr a) ∧ c.inForce .quotLift ∧
            RA.length = 6 ∧ us.length = 2) ∨
          (il = .field 0 ∧ c.t.addressOf? .quotInd = some (ixAddr a) ∧ c.inForce .quotInd ∧
            RA.length = 5 ∧ us.length = 1)) →
        c.t.addressOf? .quotMk = some (ixAddr b) → c.inForce .quotMk → MA.length = 3 →
        r ≠ .field 0 →
          (∀ ci, c.env.find? (c.κ (ixAddr a)) = some ci →
            CertsR c.env d true
              (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) RA) ∧
          (∀ ci, c.env.find? (c.κ (ixAddr b)) = some ci →
            CertsR c.env d true
              (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams mus) MA) ∧
          ((il = .field 1 ∧ ∃ v, us[1]? = some v ∧ v.isNeverZero = true) ∨
            ∃ ta, Infer c.env .io d (MA.getD 2 (.bvar 0)) ta ∧
              DefEq c.env d ta (RA.getD 0 (.bvar 0)))

/-- `red_quot(rc, is_lift, addr, lvls, spine, types)`: the quotient's ι (`Red.iota` at the
stored `Quot.lift`/`Quot.ind` recursor, whose rule is for `Quot.mk`). For the eliminator the
table binds at `addr` (`Quot.lift` when `is_lift = 1`, `Quot.ind` when `0`, in force; the
caller has checked it with `role_is`): tag `1` is `Red` of the applied eliminator to the
result. Tag `0`: no claim. -/
def red_quot : SpecFn := fun c args h r h' calls =>
  ∀ rc il addr lvls sp types, args = [rc, il, addr, lvls, sp, types] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) us As,
        ((il = .field 1 ∧ c.t.addressOf? .quotLift = some (ixAddr a) ∧ c.inForce .quotLift) ∨
          (il = .field 0 ∧ c.t.addressOf? .quotInd = some (ixAddr a) ∧ c.inForce .quotInd)) →
        RepAddr h a addr → LvListRep h us lvls → c.tml d Γ h As sp →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) us) As) E

/-- `try_quot_iota(rc, addr, lvls, spine, types)`: the quotient's ι at a constant the table
binds to `Quot.lift` or `Quot.ind`: tag `1` is `Red` of the applied constant to the result.
Tag `0`: no claim. -/
def try_quot_iota : SpecFn := fun c args h r h' calls =>
  ∀ rc addr lvls sp types, args = [rc, addr, lvls, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) us As, RepAddr h a addr → LvListRep h us lvls → c.tml d Γ h As sp →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) us) As) E

/-! ## Natives -/

/-- `prim_family(rc, a)`: a nonzero family means the table binds a role to the address (in
force under the role context); family `1` means it is the `Nat` operation `natOpOf op`. A zero
family: no claim. -/
def prim_family : SpecFn := fun c args h r h' calls =>
  ∀ rc ap, args = [rc, ap] → Good c calls → c.rc h rc →
    ∀ (a : Bytes.Address) (f op : F), RepAddr h a ap → r = .tuple [.field f, .field op] →
      f ≠ 0 →
        (∃ role, c.t.addressOf? role = some (ixAddr a) ∧ c.inForce role) ∧
        (f = 1 → ∃ role, natOpOf (ZMod.val op) = some role ∧
          c.t.addressOf? role = some (ixAddr a) ∧ c.inForce role)

/-- `try_nat_dispatch_prewhnf(rc, head_addr, op, spine, types)`: the `Nat` natives after
head-normalizing the spine. At a constant the table binds to the operation `natOpOf op`, in
force (`prim_family`'s group test),
applied to `As` with an empty level list: tags `1` (the result) and `2` (a stuck form with
reduced arguments) are `Red` of the application to the result. Tag `0`: no claim. -/
def try_nat_dispatch_prewhnf : SpecFn := fun c args h r h' calls =>
  ∀ rc ha op sp types, args = [rc, ha, op, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) (o : F) role As, RepAddr h a ha → op = .field o →
        natOpOf (ZMod.val o) = some role → c.t.addressOf? role = some (ixAddr a) →
        c.inForce role → c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → (t = 1 ∨ t = 2) →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) []) As) E

/-- `try_prim_dispatch(rc, addr, lvls, spine, types)`: the native dispatch at a constant head:
tags `1` (the result, which the caller normalizes) and `2` (a stuck form with reduced
arguments, final) are `Red` of the applied constant to the result. Tag `0`: no claim. -/
def try_prim_dispatch : SpecFn := fun c args h r h' calls =>
  ∀ rc addr lvls sp types, args = [rc, addr, lvls, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) us As, RepAddr h a addr → LvListRep h us lvls → c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → (t = 1 ∨ t = 2) →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) us) As) E

/-- `nat_lit_to_ctor_or_self(rc, e)`: a `Nat` literal becomes one constructor layer
(`Red.natLit`: `Nat.zero`, or `Nat.succ` of the predecessor literal); any other term is
returned. `Red`. -/
def nat_lit_to_ctor_or_self : SpecFn := fun c args h r h' calls =>
  ∀ rc e, args = [rc, e] → Good c calls → c.rc h rc →
    ∀ d Γ E, c.tm d Γ h E e → ∃ E', c.tm d Γ h' E' r ∧ Red c.env d E E'

/-! ## The normalizers -/

/-- The common spec of a head normalizer `f(rc, e, types)`: `Red` of the input to the
result. -/
def NormSpec : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ E', c.tm d Γ h' E' r ∧ Red c.env d E E'

/-- `whnf(rc, e, types)`: `Red`. -/
def whnf : SpecFn := NormSpec

/-- `whnf_core(rc, e, types)`: `Red`. -/
def whnf_core : SpecFn := NormSpec

/-- `whnf_nd(rc, e, types)` (no δ at definition heads): `Red`. -/
def whnf_nd : SpecFn := NormSpec

/-- `whnf_nd_core(rc, e, types)`: `Red`. -/
def whnf_nd_core : SpecFn := NormSpec

/-- `whnf_struct_core(rc, e, types)` (β, ζ, projections and ι only): `Red`. -/
def whnf_struct_core : SpecFn := NormSpec

/-- The common spec of a spine normalizer `f(rc, head, spine, types)`: `Red` of the applied
head to the result. -/
def SpineSpec : SpecFn := fun c args h r h' calls =>
  ∀ rc hd sp types, args = [rc, hd, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ H As, c.tm d Γ h H hd → c.tml d Γ h As sp →
      ∃ E', c.tm d Γ h' E' r ∧ Red c.env d (mkAppN H As) E'

/-- `whnf_with_spine(rc, head, spine, types)`: `Red` of the applied head. -/
def whnf_with_spine : SpecFn := SpineSpec

/-- `whnf_nd_with_spine(rc, head, spine, types)`: `Red` of the applied head. -/
def whnf_nd_with_spine : SpecFn := SpineSpec

/-- `whnf_struct_core_spine(rc, head, spine, types)`: `Red` of the applied head. -/
def whnf_struct_core_spine : SpecFn := SpineSpec

/-- The common spec of a constant-head normalizer `f(rc, addr, lvls, head, spine, types)`: the
head is the constant at `addr` at the levels `lvls`; `Red` of the applied constant. -/
def ConstHeadSpec : SpecFn := fun c args h r h' calls =>
  ∀ rc addr lvls hd sp types, args = [rc, addr, lvls, hd, sp, types] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) us As, RepAddr h a addr → LvListRep h us lvls →
        c.tm d Γ h (.const (c.κ (ixAddr a)) us) hd → c.tml d Γ h As sp →
        ∃ E', c.tm d Γ h' E' r ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) us) As) E'

/-- `whnf_const_head(rc, addr, lvls, head, spine, types)`: natives, the projection-function
shortcut, δ, theorem heads stuck, quotient ι, the recursor dispatch. `Red`. -/
def whnf_const_head : SpecFn := ConstHeadSpec

/-- `whnf_nd_const_head(rc, addr, lvls, head, spine, types)`: as `whnf_const_head` without δ.
`Red`. -/
def whnf_nd_const_head : SpecFn := ConstHeadSpec

/-- `whnf_struct_core_const(rc, addr, lvls, head, spine, types)`: ι at a recursor head. `Red`. -/
def whnf_struct_core_const : SpecFn := ConstHeadSpec

/-- The common spec of a projection-head normalizer
`f(rc, struct_addr, fidx, inner, spine, types)`: `Red` of the applied projection. -/
def ProjHeadSpec : SpecFn := fun c args h r h' calls =>
  ∀ rc sa fidx inner sp types, args = [rc, sa, fidx, inner, sp, types] → Good c calls →
    c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (s : Bytes.Address) (i : F) S As, RepAddr h s sa → fidx = .field i →
        c.tm d Γ h S inner → c.tml d Γ h As sp →
        ∃ E', c.tm d Γ h' E' r ∧
          Red c.env d (mkAppN (.proj (c.κ (ixAddr s)) (ZMod.val i) S) As) E'

/-- `whnf_proj_head(rc, struct_addr, fidx, inner, spine, types)`: `Red` of the applied
projection (`Red.projArg`, the string-literal expansion, `Red.proj`, or the stuck form). -/
def whnf_proj_head : SpecFn := ProjHeadSpec

/-- `whnf_nd_proj_head(rc, struct_addr, fidx, inner, spine, types)`: `Red` of the applied
projection. -/
def whnf_nd_proj_head : SpecFn := ProjHeadSpec

/-- `whnf_struct_core_proj(rc, struct_addr, fidx, inner, spine, types, original)`: `original`
is the projection node itself; `Red` of the applied projection. -/
def whnf_struct_core_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc sa fidx inner sp types orig, args = [rc, sa, fidx, inner, sp, types, orig] →
    Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types →
      ∀ (s : Bytes.Address) (i : F) S As, RepAddr h s sa → fidx = .field i →
        c.tm d Γ h S inner → c.tm d Γ h (.proj (c.κ (ixAddr s)) (ZMod.val i) S) orig →
        c.tml d Γ h As sp →
        ∃ E', c.tm d Γ h' E' r ∧
          Red c.env d (mkAppN (.proj (c.κ (ixAddr s)) (ZMod.val i) S) As) E'

/-- `whnf_spine(rc, spine, types)`: each argument head-normalized: pointwise `Red`. -/
def whnf_spine : SpecFn := fun c args h r h' calls =>
  ∀ rc sp types, args = [rc, sp, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ As, c.tml d Γ h As sp →
      ∃ Bs, c.tml d Γ h' Bs r ∧ List.Forall₂ (Red c.env d) As Bs

/-! ## Structure η: the shape scans -/

/-- `se_parent_addr(rec_ty, skip)`: every tag other than `0` gives the address of the head
constant of the domain of binder `skip` of the telescope (`MajorHead` at the major premise).
Tag `0`: no claim. -/
def se_parent_addr : SpecFn := fun c args h r h' calls =>
  ∀ rt skip, args = [rt, skip] → Good c calls →
    ∀ d Γ k RT (n : F), c.tmk d Γ k h RT rt → skip = .field n →
      ∀ (t : F) pa, r = .tuple [.field t, pa] → t ≠ 0 →
        ∃ (p : Bytes.Address) (us : List KLevel), RepAddr h' p pa ∧
          (piDomAt (ZMod.val n) RT).map (·.getAppFn) = some (.const (c.κ (ixAddr p)) us)

/-- `apply_n_projs(head, parent, major, n_fields, i)`: the head applied to the projections
`i, i + 1, …` of the major out of the structure at `parent`, up to `n_fields`. -/
def apply_n_projs : SpecFn := fun c args h r h' calls =>
  ∀ hd par major nf i, args = [hd, par, major, nf, i] → Good c calls →
    ∀ d Γ H (p : Bytes.Address) M (n j : F), c.tm d Γ h H hd → RepAddr h p par →
      c.tm d Γ h M major → nf = .field n → i = .field j →
      ∃ m : Nat, j + (m : F) = n ∧
        c.tm d Γ h' (mkAppN H ((List.range m).map fun t =>
          (Ix.Kernel.Expr.proj (c.κ (ixAddr p)) (ZMod.val (j + (t : F))) M : KExpr))) r

/-- `se_addr_in(a, xs)`: exact membership (`Bytes::address_eq` decides). -/
def se_addr_in : SpecFn := fun c args h r h' calls =>
  ∀ ap xs, args = [ap, xs] → Good c calls →
    ∀ (a : Bytes.Address) ms, RepAddr h a ap → RepList addrListEnum RepAddr h ms xs →
      r = .field (if a ∈ ms then 1 else 0) ∧ h' = h

/-! ### Heap syntax

The scans run on IxVM's heap terms, not on their images: a `Let` node is not a `∀` node (its
image, ζ-expanded, may be a `∀`), and a `Let`'s value is scanned even where the body does not
use it. The field scan answers "found" at a `Let` that ends a `∀` chain (the fields behind it
are not read syntactically). The claims are stated on the heap, positively (they persist as the
heap grows). The kernel decides `is_rec` on the classified field kinds of the normalised
constructors (`nativeIsRec`, `IxC/Kernel/Inductives/NativeInstall.lean:621-647`; its first
pass reads the declared telescope syntactically, `nativeRawRec`, `:122-128`). -/

/-- **A chain of `∀` nodes in the heap**: the term at `p` is `∀` nodes with the domains `ds`
(outermost first) over the term at `q`. A `Let` node ends a chain. -/
inductive ForallChain (h : Heap F) :
    SourceValue F → List (SourceValue F) → SourceValue F → Prop where
  | nil {p : SourceValue F} : ForallChain h p [] p
  | cons {p dom cod lvl q : SourceValue F} {ds : List (SourceValue F)} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dom, cod, lvl]) →
      ForallChain h cod ds q → ForallChain h p (dom :: ds) q

/-- The heap term at `q` is a node other than a `∀` node. -/
def NotForallNode (h : Heap F) (q : SourceValue F) : Prop :=
  ∃ (ctor : String) (xs : List (SourceValue F)),
    loadValue h q = .ok (.construct kexprEnum ctor xs) ∧ ctor ≠ "Forall"

/-- The heap term at `q` is a node other than a `∀` or a `Let` node (where the field scan ends a
chain with "none found"). -/
def ChainEnd (h : Heap F) (q : SourceValue F) : Prop :=
  ∃ (ctor : String) (xs : List (SourceValue F)),
    loadValue h q = .ok (.construct kexprEnum ctor xs) ∧ ctor ≠ "Forall" ∧ ctor ≠ "Let"

/-- **No constant of the heap term is at an address satisfying `P`** (heap syntax: every node,
the parts of a `Let` included; a `Proj` node's structure address is not read, as IxVM's scans
do not read it). -/
inductive HeapClean (P : Bytes.Address → Prop) (h : Heap F) : SourceValue F → Prop where
  | bvar {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct kexprEnum "BVar" xs) → HeapClean P h p
  | srt {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct kexprEnum "Srt" xs) → HeapClean P h p
  | lit {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct kexprEnum "Lit" xs) → HeapClean P h p
  | const {p ap lp : SourceValue F} {a : Bytes.Address} :
      loadValue h p = .ok (.construct kexprEnum "Const" [ap, lp]) → RepAddr h a ap → ¬ P a →
      HeapClean P h p
  | app {p x y : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "App" [x, y]) →
      HeapClean P h x → HeapClean P h y → HeapClean P h p
  | lam {p x y l : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "Lam" [x, y, l]) →
      HeapClean P h x → HeapClean P h y → HeapClean P h p
  | forallE {p x y l : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [x, y, l]) →
      HeapClean P h x → HeapClean P h y → HeapClean P h p
  | letE {p x y z : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "Let" [x, y, z]) →
      HeapClean P h x → HeapClean P h y → HeapClean P h z → HeapClean P h p
  | proj {p ap i e : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "Proj" [ap, i, e]) → HeapClean P h e →
      HeapClean P h p

/-- **The fields of a constructor type are clean**: the maximal `∀` chain of the heap term
`ty` ends at a node other than a `∀` or a `Let` (`ChainEnd`) and has, after its first `p`
domains, only domains that mention no address of `membs`. Stated for the circuit after the
pending batch; its path lemmas change at the pin. -/
def FieldsClean (h : Heap F) (p : Nat) (membs : List Bytes.Address) (ty : SourceValue F) : Prop :=
  ∃ ds q, ForallChain h ty ds q ∧ ChainEnd h q ∧
    ∀ dp ∈ ds.drop p, HeapClean (· ∈ membs) h dp

/-- For every address of `ms` whose record in `c.E` is the inductive projection `p` of a block
member `ind`, every constructor of `ind` (`0, …, ctors.size - 1`, the constant at the key of its
projection record) is loaded with a type whose fields, after `ind`'s parameters, mention no
address of `membs` (`FieldsClean`, on the loaded heap term). Stated for the circuit after the
pending batch; its path lemmas change at the pin. -/
def MembersClean (c : Ctx) (h : Heap F) (ms membs : List Bytes.Address) : Prop :=
  ∀ m ∈ ms, ∀ (cm cb : Ixon.Constant) (p : Ixon.InductiveProj) (xs : Array Ixon.MutConst)
      (ind : Ixon.Inductive),
    Ix.Cert.recordAt c.E (ixAddr m) = some cm → cm.info = .iPrj p →
    Ix.Cert.recordAt c.E p.block = some cb → cb.info = .muts xs →
    xs[p.idx.toNat]? = some (.indc ind) →
    ∀ t < ind.ctors.size, ∃ (cicon : Ix.Kernel.ConstantInfo .anon) (w nl ty : SourceValue F)
        (rest : List (SourceValue F)),
      c.env.find? (c.κ (cprjAddr p.block p.idx.toNat t)) = some cicon ∧ c.ci h w cicon ∧
      w = .construct kciEnum "Ctor" (nl :: ty :: rest) ∧ FieldsClean h ind.params.toNat membs ty

/-- `se_mentions(e, members)`: an answer other than `1` means the heap term mentions no
address of `members` (`HeapClean`). Answer `1`: no claim. -/
def se_mentions : SpecFn := fun c args h r h' calls =>
  ∀ e xs, args = [e, xs] → Good c calls →
    ∀ ms, RepList addrListEnum RepAddr h ms xs → (∃ d Γ k E, c.tmk d Γ k h E e) →
      r ≠ .field 1 → HeapClean (· ∈ ms) h e

/-- `se_peel_tol(ty, n)`: the term after up to `n` leading `∀` nodes (fewer where the chain ends
at another node); nothing is allocated. -/
def se_peel_tol : SpecFn := fun c args h r h' calls =>
  ∀ ty n, args = [ty, n] → Good c calls → ∀ m : F, n = .field m →
    (∃ d Γ k T, c.tmk d Γ k h T ty) →
    h' = h ∧ ∃ ds, ForallChain h ty ds r ∧ ds.length ≤ ZMod.val m ∧
      (ds.length < ZMod.val m → NotForallNode h r)

/-- `se_scan_fields(ty, members)`: an answer other than `1` means the maximal `∀` chain of the
heap term ends at a node other than a `∀` or a `Let` (`ChainEnd`) and has only domains that
mention no address of `members`. Answer `1`: no claim. Stated for the circuit after the pending
batch; its path lemmas change at the pin. -/
def se_scan_fields : SpecFn := fun c args h r h' calls =>
  ∀ ty xs, args = [ty, xs] → Good c calls →
    ∀ ms, RepList addrListEnum RepAddr h ms xs → (∃ d Γ k T, c.tmk d Γ k h T ty) →
      r ≠ .field 1 →
      ∃ ds q, ForallChain h ty ds q ∧ ChainEnd h q ∧ ∀ dp ∈ ds, HeapClean (· ∈ ms) h dp

/-- `struct_block_member_addrs(parent, block)`: for a record at `block` in the records `c.E`,
the addresses of its members' projection records (`Ingress::build_recur_addrs`), every
inductive member's among them, when it is a block, and `[parent]` otherwise. -/
def struct_block_member_addrs : SpecFn := fun c args h r h' calls =>
  ∀ par blk, args = [par, blk] → Good c calls →
    ∀ (p b : Bytes.Address), RepAddr h p par → RepAddr h b blk →
      ∀ cb, Ix.Cert.recordAt c.E (ixAddr b) = some cb →
        ∃ xs, RepList addrListEnum RepAddr h' xs r ∧
          (∀ ms, cb.info = .muts ms → ∀ i ind, ms[i]? = some (.indc ind) →
            ∃ a ∈ xs, ixAddr a = iprjAddr (ixAddr b) i) ∧
          ((∀ ms, cb.info ≠ .muts ms) → xs = [p])

/-- `struct_scan_ctors(block, idx, num_ctors, n_params, members, c)`: an answer other than `1`
means the constructors `c, …, num_ctors - 1` of member `idx` of the block (the constants at the
keys of their projection records) are loaded with types whose fields, after `n_params`
binders, mention no address of `members` (`FieldsClean`). Answer `1`: no claim. Stated for the
circuit after the pending batch; its path lemmas change at the pin. -/
def struct_scan_ctors : SpecFn := fun c args h r h' calls =>
  ∀ blk idx nc np xs ci, args = [blk, idx, nc, np, xs, ci] → Good c calls →
    ∀ (b : Bytes.Address) (i n p j : F) ms, RepAddr h b blk → idx = .field i → nc = .field n →
      np = .field p → RepList addrListEnum RepAddr h ms xs → ci = .field j → r ≠ .field 1 →
      ∀ t < ZMod.val (n - j),
        ∃ (cicon : Ix.Kernel.ConstantInfo .anon) (w nl' ty' : SourceValue F)
          (rest : List (SourceValue F)),
          c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val (j + (t : F))))) =
            some cicon ∧ c.ci h' w cicon ∧ w = .construct kciEnum "Ctor" (nl' :: ty' :: rest) ∧
          FieldsClean h' (ZMod.val p) ms ty'

/-- `struct_scan_members(ms, members)`: an answer other than `1` is `MembersClean ms members`.
Answer `1`: no claim. Stated for the circuit after the pending batch; its path lemmas change at
the pin. -/
def struct_scan_members : SpecFn := fun c args h r h' calls =>
  ∀ msp xs, args = [msp, xs] → Good c calls →
    ∀ ms membs, RepList addrListEnum RepAddr h ms msp → RepList addrListEnum RepAddr h membs xs →
      r ≠ .field 1 → MembersClean c h' ms membs

/-- `struct_is_rec(parent)`: Lean's block-level `is_rec`. An answer other than `1` means: for the
block `b` IxVM loaded for the parent (when `block_is_multi` answers `0`), the member list it
computed (`struct_block_member_addrs`: every inductive member's projection record when the record
at `b` is a block, `[parent]` otherwise) is clean against itself (`MembersClean`); when the
parent's record is the inductive projection of a member of a block, `b` is that block. Answer
`1`: no claim. Stated for the circuit after the pending batch; its path lemmas change at the
pin. -/
def struct_is_rec : SpecFn := fun c args h r h' calls =>
  ∀ par, args = [par] → Good c calls →
    ∀ (p : Bytes.Address), RepAddr h p par → r ≠ .field 1 →
      ∃ (b : Bytes.Address) (ms : List Bytes.Address), MembersClean c h' ms ms ∧
        (∀ (cm cb : Ixon.Constant) (pp : Ixon.InductiveProj) (xs : Array Ixon.MutConst)
            (ind : Ixon.Inductive),
          Ix.Cert.recordAt c.E (ixAddr p) = some cm → cm.info = .iPrj pp →
          Ix.Cert.recordAt c.E pp.block = some cb → cb.info = .muts xs →
          xs[pp.idx.toNat]? = some (.indc ind) → ixAddr b = pp.block) ∧
        ∀ cb, Ix.Cert.recordAt c.E (ixAddr b) = some cb →
          (∀ xs, cb.info = .muts xs → ∀ i ind, xs[i]? = some (.indc ind) →
            ∃ a ∈ ms, ixAddr a = iprjAddr (ixAddr b) i) ∧
          ((∀ xs, cb.info ≠ .muts xs) → ms = [p])

/-! ## The family -/

inductive Fn where
  | apply_spine | peel_beta | red_beta | beta_more | peel_beta_cert | red_proj
  | type_sort_never | red_unfold | whnf_with_spine | whnf_proj_head | whnf_spine
  | try_nat_dispatch_prewhnf | prim_family | try_prim_dispatch | try_quot_iota | red_quot
  | quot_certs | whnf_const_head | red_rec | try_reduce_projection_definition | lams_never
  | projection_definition_info | nat_lit_to_ctor_or_self | try_k_synth_iota | k_synth_fab
  | whnf_iota_major | try_iota | red_iota | iota_cmp | iota_certs | slots_never | pi_peel
  | pi_residual | find_rule | try_struct_eta_iota | eta_iota_fab | certs_all | se_parent_addr
  | apply_n_projs | struct_is_rec | struct_scan_members | struct_block_member_addrs
  | struct_scan_ctors | se_peel_tol | se_scan_fields | se_mentions | se_addr_in | whnf
  | whnf_core | whnf_struct_core | whnf_struct_core_spine | whnf_struct_core_proj
  | whnf_struct_core_const | whnf_nd | whnf_nd_core | whnf_nd_with_spine | whnf_nd_proj_head
  | whnf_nd_const_head
  deriving DecidableEq, Repr

/-- The function's symbol, as `ObsFn` names it. -/
def Fn.name : Fn → String
  | .apply_spine => "KernelWhnf::apply_spine"
  | .peel_beta => "KernelWhnf::peel_beta"
  | .red_beta => "KernelWhnf::red_beta"
  | .beta_more => "KernelWhnf::beta_more"
  | .peel_beta_cert => "KernelWhnf::peel_beta_cert"
  | .red_proj => "KernelWhnf::red_proj"
  | .type_sort_never => "KernelWhnf::type_sort_never"
  | .red_unfold => "KernelWhnf::red_unfold"
  | .whnf_with_spine => "KernelWhnf::whnf_with_spine"
  | .whnf_proj_head => "KernelWhnf::whnf_proj_head"
  | .whnf_spine => "KernelWhnf::whnf_spine"
  | .try_nat_dispatch_prewhnf => "KernelWhnf::try_nat_dispatch_prewhnf"
  | .prim_family => "KernelWhnf::prim_family"
  | .try_prim_dispatch => "KernelWhnf::try_prim_dispatch"
  | .try_quot_iota => "KernelWhnf::try_quot_iota"
  | .red_quot => "KernelWhnf::red_quot"
  | .quot_certs => "KernelWhnf::quot_certs"
  | .whnf_const_head => "KernelWhnf::whnf_const_head"
  | .red_rec => "KernelWhnf::red_rec"
  | .try_reduce_projection_definition => "KernelWhnf::try_reduce_projection_definition"
  | .lams_never => "KernelWhnf::lams_never"
  | .projection_definition_info => "KernelWhnf::projection_definition_info"
  | .nat_lit_to_ctor_or_self => "KernelWhnf::nat_lit_to_ctor_or_self"
  | .try_k_synth_iota => "KernelWhnf::try_k_synth_iota"
  | .k_synth_fab => "KernelWhnf::k_synth_fab"
  | .whnf_iota_major => "KernelWhnf::whnf_iota_major"
  | .try_iota => "KernelWhnf::try_iota"
  | .red_iota => "KernelWhnf::red_iota"
  | .iota_cmp => "KernelWhnf::iota_cmp"
  | .iota_certs => "KernelWhnf::iota_certs"
  | .slots_never => "KernelWhnf::slots_never"
  | .pi_peel => "KernelWhnf::pi_peel"
  | .pi_residual => "KernelWhnf::pi_residual"
  | .find_rule => "KernelWhnf::find_rule"
  | .try_struct_eta_iota => "KernelWhnf::try_struct_eta_iota"
  | .eta_iota_fab => "KernelWhnf::eta_iota_fab"
  | .certs_all => "KernelWhnf::certs_all"
  | .se_parent_addr => "KernelWhnf::se_parent_addr"
  | .apply_n_projs => "KernelWhnf::apply_n_projs"
  | .struct_is_rec => "KernelWhnf::struct_is_rec"
  | .struct_scan_members => "KernelWhnf::struct_scan_members"
  | .struct_block_member_addrs => "KernelWhnf::struct_block_member_addrs"
  | .struct_scan_ctors => "KernelWhnf::struct_scan_ctors"
  | .se_peel_tol => "KernelWhnf::se_peel_tol"
  | .se_scan_fields => "KernelWhnf::se_scan_fields"
  | .se_mentions => "KernelWhnf::se_mentions"
  | .se_addr_in => "KernelWhnf::se_addr_in"
  | .whnf => "KernelWhnf::whnf"
  | .whnf_core => "KernelWhnf::whnf_core"
  | .whnf_struct_core => "KernelWhnf::whnf_struct_core"
  | .whnf_struct_core_spine => "KernelWhnf::whnf_struct_core_spine"
  | .whnf_struct_core_proj => "KernelWhnf::whnf_struct_core_proj"
  | .whnf_struct_core_const => "KernelWhnf::whnf_struct_core_const"
  | .whnf_nd => "KernelWhnf::whnf_nd"
  | .whnf_nd_core => "KernelWhnf::whnf_nd_core"
  | .whnf_nd_with_spine => "KernelWhnf::whnf_nd_with_spine"
  | .whnf_nd_proj_head => "KernelWhnf::whnf_nd_proj_head"
  | .whnf_nd_const_head => "KernelWhnf::whnf_nd_const_head"

/-- The function's spec. -/
def Fn.spec : Fn → SpecFn
  | .apply_spine => Whnf.apply_spine
  | .peel_beta => Whnf.peel_beta
  | .red_beta => Whnf.red_beta
  | .beta_more => Whnf.beta_more
  | .peel_beta_cert => Whnf.peel_beta_cert
  | .red_proj => Whnf.red_proj
  | .type_sort_never => Whnf.type_sort_never
  | .red_unfold => Whnf.red_unfold
  | .whnf_with_spine => Whnf.whnf_with_spine
  | .whnf_proj_head => Whnf.whnf_proj_head
  | .whnf_spine => Whnf.whnf_spine
  | .try_nat_dispatch_prewhnf => Whnf.try_nat_dispatch_prewhnf
  | .prim_family => Whnf.prim_family
  | .try_prim_dispatch => Whnf.try_prim_dispatch
  | .try_quot_iota => Whnf.try_quot_iota
  | .red_quot => Whnf.red_quot
  | .quot_certs => Whnf.quot_certs
  | .whnf_const_head => Whnf.whnf_const_head
  | .red_rec => Whnf.red_rec
  | .try_reduce_projection_definition => Whnf.try_reduce_projection_definition
  | .lams_never => Whnf.lams_never
  | .projection_definition_info => Whnf.projection_definition_info
  | .nat_lit_to_ctor_or_self => Whnf.nat_lit_to_ctor_or_self
  | .try_k_synth_iota => Whnf.try_k_synth_iota
  | .k_synth_fab => Whnf.k_synth_fab
  | .whnf_iota_major => Whnf.whnf_iota_major
  | .try_iota => Whnf.try_iota
  | .red_iota => Whnf.red_iota
  | .iota_cmp => Whnf.iota_cmp
  | .iota_certs => Whnf.iota_certs
  | .slots_never => Whnf.slots_never
  | .pi_peel => Whnf.pi_peel
  | .pi_residual => Whnf.pi_residual
  | .find_rule => Whnf.find_rule
  | .try_struct_eta_iota => Whnf.try_struct_eta_iota
  | .eta_iota_fab => Whnf.eta_iota_fab
  | .certs_all => Whnf.certs_all
  | .se_parent_addr => Whnf.se_parent_addr
  | .apply_n_projs => Whnf.apply_n_projs
  | .struct_is_rec => Whnf.struct_is_rec
  | .struct_scan_members => Whnf.struct_scan_members
  | .struct_block_member_addrs => Whnf.struct_block_member_addrs
  | .struct_scan_ctors => Whnf.struct_scan_ctors
  | .se_peel_tol => Whnf.se_peel_tol
  | .se_scan_fields => Whnf.se_scan_fields
  | .se_mentions => Whnf.se_mentions
  | .se_addr_in => Whnf.se_addr_in
  | .whnf => Whnf.whnf
  | .whnf_core => Whnf.whnf_core
  | .whnf_struct_core => Whnf.whnf_struct_core
  | .whnf_struct_core_spine => Whnf.whnf_struct_core_spine
  | .whnf_struct_core_proj => Whnf.whnf_struct_core_proj
  | .whnf_struct_core_const => Whnf.whnf_struct_core_const
  | .whnf_nd => Whnf.whnf_nd
  | .whnf_nd_core => Whnf.whnf_nd_core
  | .whnf_nd_with_spine => Whnf.whnf_nd_with_spine
  | .whnf_nd_proj_head => Whnf.whnf_nd_proj_head
  | .whnf_nd_const_head => Whnf.whnf_nd_const_head

end IxVM.Refinement.Core.Specs.Whnf
