import IxVMRefinement.Binding.FamilyOf
import IxVMRefinement.Binding.FamilyReconModel
import IxVMRefinement.StatementRel.LoadedReadsCanon

/-! # A block's flattened family, entry by entry: read off a family record, derived from the block

The family check of a block `B` with a family record compares two lists of entries
(`KernelModeled::check_nested_aux` with the changed `aux_all_in`): the flattened family read off
the record (`KernelCheck::build_flat_block`: the block's own types, then the auxiliary each
recursor's major premise names) and the flattened family derived from the block's constructors
alone (`nested_walk`). They must be the same entries in the same order. An entry is the type at a
position, whether it is an auxiliary (a type of a nested occurrence's block) or one of the
block's own types, the parameters it is taken at and its levels (`FlatEntry`). Two auxiliaries
over one container share their address and differ in their parameters or levels, so the
addresses alone do not fix the positions.

Every term the model reads of a record is the circuit's loaded form of it (`loadedAt`): the
kernel reader's conversion with the binder data `Convert` computes from the record's binder blocks
at the expression's root (`LoadedReads.canonAnn`, the form every `get_ci` load represents), a
`let` read as its reduct. The raw conversion alone gives every binder the datum `never` and keeps
`let`s.

* `mutsRoot`, `loadedAt`: the root of a block member's expressions, and the canonical reading.
* `FlatEntry` (with `peelForalls`, in `FamilyReconModel` under this namespace);
  `RecordFlat t E rb crb rs es`: recursor `k` of the record has its major premise over entry `k`,
  at its parameters and levels.
* `FlatView`: what the derivation reads of a store (the circuit's `get_ci`, `get_ci_cprj`,
  `build_flat_originals`, and a key's address); `FlatView.ofStore t E` reads them off the store.
* The derivation, mirroring the circuit: `mentions` (`expr_mentions_block`, `caddr_is_peer`),
  `occScanF` (`occ_scan`, `occ_scan_list`, `occ_params_lower`), `addBlockMembers`
  (`add_block_members`, `aux_entry_in`), `ctorsScan` (`ctors_scan`, `inst_ctor_params`,
  `peel_n_foralls`), `nestedWalk` (`nested_walk`), `originals` (`build_flat_originals` at the
  elimination offset), `derivedFlatAt`. Total: `occScanF` recurses on a fuel the caller sets to
  the term's size (`exprSize`), `nestedWalk` on a fuel of steps; everything else is structural.
* `BlockDerivedFlat t E B off es`: `es` is derived from `B` in `E` at some fuel, at the block's
  elimination offset `off` (`block_elim`, a function of the block).
* `derivedFlatAt_unique` (two fuels), `derivedFlatAt_le` (a view that answers more answers the
  same), `blockDerivedFlat_unique`: two stores whose readings agree where both answer derive the
  same entries from one block at one offset. -/

namespace IxVM.Refinement.Binding.FamilyFlat

open IxVM.Consistency

set_option linter.unusedVariables false

/-! ## The canonical reading -/

/-- **The root of member `i`'s expressions** among a block's binder-indexed roots
(`Convert::mut_const_roots`, summed over the members before it): a definition's type is at the
root, its value at the next; an inductive's type at the root, its constructor `j` at the root plus
`1 + j`; a recursor's type at the root, its rule `j` at the root plus `1 + j`. -/
abbrev mutsRoot (ms : Array Ixon.MutConst) (i : Nat) : IxVM.F :=
  ((IxVM.Refinement.L1.mutsRootOffset ms.toList i : Nat) : IxVM.F)

/-- **The circuit's loaded form of an expression `e` of the record `src`**, converted at root
`root` with `nl` level parameters: the kernel reader's conversion (universe variable `i` read as
the level parameter `i`, `recur` as `self`) with the binder data of the root's plan in the
record's binder blocks (`LoadedReads.canonAnn`; a `let` read as its reduct). Every `get_ci` load
of the record represents it (`LoadedReads.annotation_canon`). `none` where the conversion or the
plan fails. -/
noncomputable def loadedAt (t : Ix.Kernel.RoleTable) (blob : _root_.Address → Option ByteArray)
    (src : Ixon.Constant) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)))
    (nl : Nat) (root : IxVM.F) (e : Ixon.Expr) : Option (Ix.Kernel.Expr .anon) :=
  match ((exprReader t blob src id self).read e).toOption with
  | none => none
  | some e₀ => IxVM.Refinement.LoadedReads.canonAnn src (List.range nl) root e e₀

/-! ## Entries, and the record's -/

/-- The domain of the binder after `n` leading binders (a recursor's major premise's type, at
`n = params + motives + minors + indices`). -/
def binderDomAfter (n : Nat) (e : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  match peelForalls n e with
  | some (.forallE d _ _) => some d
  | _ => none

/-- **The record's flattened family, entry by entry** (`build_flat_block`, tied to the positions
by `check_recs`): recursor `k` of the record `rb` has, in the canonical reading (`loadedAt`, over
the record's tables at the member's root), a type whose major premise is headed by entry `k`'s
type at its levels, and, at an auxiliary, taken at its parameters (the major premise's first
arguments, lowered past the motives, minors and indices to the parameter frame). -/
def RecordFlat (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) : Prop :=
  ∀ (k : Nat) (r : Ixon.Recursor) (e : FlatEntry), rs[k]? = some (Ixon.MutConst.recr r) →
    es[k]? = some e →
    ∃ ty d, loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs k) r.typ = some ty ∧
      binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty =
        some d ∧
      Ix.Kernel.Expr.getAppFn d = .const (keyOf t e.addr) e.levels ∧
      (e.aux = true →
        ((Ix.Kernel.Expr.getAppArgs d).take e.params.length).map
            (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0) =
          e.params)

/-! ## What the derivation reads of a store -/

/-- What `get_ci` gives of an inductive type: its level count, parameter count, constructor
count, block and position in the block. -/
structure IndInfo where
  nl : Nat
  np : Nat
  nctors : Nat
  blk : _root_.Address
  idx : Nat

/-- **What the derivation reads of a store**: `get_ci` at an address (an inductive type,
`some none` another constant, `none` when no constant loads), `get_ci_cprj`'s constructor type,
`build_flat_originals`' member addresses of a block, and the address of a constant named by a
key. -/
structure FlatView where
  ci : _root_.Address → Option (Option IndInfo)
  ctorType : _root_.Address → Nat → Nat → Option (Ix.Kernel.Expr .anon)
  members : _root_.Address → Option (List _root_.Address)
  addr : Ix.Kernel.Key .anon → Option _root_.Address

/-- `get_ci` at an address of the store: an inductive type through its projection record. -/
def indInfoAt (E : Ixon.Env) (a : _root_.Address) : Option (Option IndInfo) :=
  match recordOf E a with
  | none => none
  | some c =>
    match c.info with
    | .iPrj p =>
      match recordOf E p.block with
      | none => none
      | some cb =>
        match cb.info with
        | .muts ms =>
          match ms[p.idx.toNat]? with
          | some (.indc ind) =>
            some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, p.block, p.idx.toNat⟩)
          | _ => none
        | _ => none
    | _ => some none

/-- `get_ci_cprj blk i c`'s type: constructor `c` of member `i` of the block at `b`, in the
canonical reading over the block's tables at the constructor's root (`mutsRoot ms i + 1 + c`). -/
noncomputable def ctorTypeAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (b : _root_.Address)
    (i c : Nat) : Option (Ix.Kernel.Expr .anon) :=
  match recordOf E b with
  | none => none
  | some cb =>
    match cb.info with
    | .muts ms =>
      match ms[i]? with
      | some (.indc ind) =>
        match ind.ctors[c]? with
        | none => none
        | some ctor =>
          loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t b ms) ctor.lvls.toNat
            (mutsRoot ms i + 1 + ((c : Nat) : IxVM.F)) ctor.typ
      | _ => none
    | _ => none

/-- The constant addresses of a block's inductive members, from position `i`. -/
def indcAddrs (b : _root_.Address) : Nat → List Ixon.MutConst → List _root_.Address
  | _, [] => []
  | i, m :: ms =>
    match m with
    | .indc _ => memberAddr b i m :: indcAddrs b (i + 1) ms
    | _ => indcAddrs b (i + 1) ms

/-- `build_flat_originals blk 0`'s addresses. -/
def membersAt (E : Ixon.Env) (b : _root_.Address) : Option (List _root_.Address) :=
  match recordOf E b with
  | none => none
  | some cb =>
    match cb.info with
    | .muts ms => some (indcAddrs b 0 ms.toList)
    | _ => none

/-- The address of the constant a key names under the role table. -/
def keyAddr (t : Ix.Kernel.RoleTable) : Ix.Kernel.Key .anon → Option _root_.Address
  | .id a => some a
  | .role r => t.addressOf? r
  | .aux _ _ => none

/-- **The readings of the store `E`** under the role table `t`. -/
noncomputable def FlatView.ofStore (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : FlatView :=
  ⟨indInfoAt E, ctorTypeAt t E, membersAt E, keyAddr t⟩

/-! ## The derivation -/

/-- Short-circuit disjunction of two answers. -/
def orB (x y : Option Bool) : Option Bool :=
  match x with
  | none => none
  | some true => some true
  | some false => y

/-- `caddr_is_peer`: the constant a key names is an inductive type of the block `B`. -/
def peer (V : FlatView) (B : _root_.Address) (k : Ix.Kernel.Key .anon) : Option Bool :=
  match V.addr k with
  | none => none
  | some a =>
    match V.ci a with
    | none => none
    | some none => some false
    | some (some i) => some (i.blk == B)

/-- `expr_mentions_block`: the term names an inductive type of the block `B`. -/
def mentions (V : FlatView) (B : _root_.Address) : Ix.Kernel.Expr .anon → Option Bool
  | .bvar _ => some false
  | .fvar _ _ => some false
  | .sort _ => some false
  | .const k _ => peer V B k
  | .app f a => orB (mentions V B f) (mentions V B a)
  | .lam t b _ => orB (mentions V B t) (mentions V B b)
  | .forallE t b _ => orB (mentions V B t) (mentions V B b)
  | .letE t v b _ => orB (mentions V B t) (orB (mentions V B v) (mentions V B b))
  | .lit _ => some false
  | .proj _ _ e => mentions V B e

/-- `list_any_mentions_block`. -/
def mentionsList (V : FlatView) (B : _root_.Address) : List (Ix.Kernel.Expr .anon) → Option Bool
  | [] => some false
  | e :: es => orB (mentions V B e) (mentionsList V B es)

/-- `has_bvar_in_range`: a loose variable with index in `[lo, hi)`. -/
def hasBVarIn (lo hi : Nat) : Ix.Kernel.Expr .anon → Bool
  | .bvar i => lo ≤ i && i < hi
  | .app f a => hasBVarIn lo hi f || hasBVarIn lo hi a
  | .lam t b _ => hasBVarIn lo hi t || hasBVarIn (lo + 1) (hi + 1) b
  | .forallE t b _ => hasBVarIn lo hi t || hasBVarIn (lo + 1) (hi + 1) b
  | .letE t v b _ => hasBVarIn lo hi t || hasBVarIn lo hi v || hasBVarIn (lo + 1) (hi + 1) b
  | .proj _ _ e => hasBVarIn lo hi e
  | _ => false

/-- `occ_params_lower`: an occurrence's parameters, from under `d` binders to the recursor's
parameters; none when one mentions one of those binders (the circuit refuses it). -/
def occParamsLower : List (Ix.Kernel.Expr .anon) → Nat → Option (List (Ix.Kernel.Expr .anon))
  | [], _ => some []
  | x :: xs, d =>
    if hasBVarIn 0 d x then none
    else
      match occParamsLower xs d with
      | none => none
      | some ys => some (Ix.Kernel.Expr.lowerBVars d 0 x :: ys)

/-- `aux_entry_in`: an auxiliary entry with the type, the parameters and the levels. -/
def auxEntryIn (acc : List FlatEntry) (a : _root_.Address) (sp : List (Ix.Kernel.Expr .anon))
    (us : List Ix.Kernel.Level) : Bool :=
  acc.any fun e => e.aux && e.addr == a && e.params == sp && e.levels == us

/-- `add_block_members`: every type of an occurrence's block at its parameters and levels,
unless already an entry. -/
def addBlockMembers : List _root_.Address → List (Ix.Kernel.Expr .anon) → List Ix.Kernel.Level →
    List FlatEntry → List FlatEntry
  | [], _, _, acc => acc
  | m :: ms, sp, us, acc =>
    addBlockMembers ms sp us (if auxEntryIn acc m sp us then acc else acc ++ [⟨m, true, sp, us⟩])

/-- `occ_scan_list`, over a scan of one term. -/
def scanList (rec : Ix.Kernel.Expr .anon → List FlatEntry → Option (List FlatEntry)) :
    List (Ix.Kernel.Expr .anon) → List FlatEntry → Option (List FlatEntry)
  | [], acc => some acc
  | x :: xs, acc =>
    match rec x acc with
    | none => none
    | some a => scanList rec xs a

/-- The constant heading a spine, if it is one. -/
def constOf : Ix.Kernel.Expr .anon → Option (Ix.Kernel.Key .anon × List Ix.Kernel.Level)
  | .const k us => some (k, us)
  | _ => none

/-- An occurrence of the inductive `i` with the arguments `args` is nested: `i` is outside the
block, with at least its parameters, and its parameters mention the block. -/
def nestedAt (V : FlatView) (B : _root_.Address) (i : IndInfo)
    (args : List (Ix.Kernel.Expr .anon)) : Option Bool :=
  match i.blk == B || decide (args.length < i.np) with
  | true => some false
  | false => mentionsList V B (args.take i.np)

/-- `occ_scan`'s application arm, given the scan of a subterm (`rec`): a nested occurrence adds
its block's types at its parameters and levels; otherwise the head (unless a constant) and the
arguments are scanned. -/
def appCase (rec : Ix.Kernel.Expr .anon → Nat → List FlatEntry → Option (List FlatEntry))
    (V : FlatView) (B : _root_.Address) (hd : Ix.Kernel.Expr .anon)
    (args : List (Ix.Kernel.Expr .anon)) (d : Nat) (acc : List FlatEntry) :
    Option (List FlatEntry) :=
  match constOf hd with
  | some (c, us) =>
    match V.addr c with
    | none => none
    | some ca =>
      match V.ci ca with
      | none => none
      | some none => scanList (fun x acc => rec x d acc) args acc
      | some (some i) =>
        match nestedAt V B i args with
        | none => none
        | some false => scanList (fun x acc => rec x d acc) args acc
        | some true =>
          match V.members i.blk with
          | none => none
          | some ms =>
            match occParamsLower (args.take i.np) d with
            | none => none
            | some sp => some (addBlockMembers ms sp us acc)
  | none =>
    match rec hd d acc with
    | none => none
    | some a => scanList (fun x acc => rec x d acc) args a

/-- **`occ_scan`** at a fuel: the nested occurrences in a term under `d` binders of a
constructor's type, added to the entries. A term that does not mention the block has none. -/
def occScanF (V : FlatView) (B : _root_.Address) :
    Nat → Ix.Kernel.Expr .anon → Nat → List FlatEntry → Option (List FlatEntry)
  | 0, _, _, _ => none
  | n + 1, e, d, acc =>
    match mentions V B e with
    | none => none
    | some false => some acc
    | some true =>
      match e with
      | .app f a =>
        appCase (occScanF V B n) V B (Ix.Kernel.Expr.getAppFn (.app f a))
          (Ix.Kernel.Expr.getAppArgs (.app f a)) d acc
      | .lam t b _ =>
        match occScanF V B n t d acc with
        | none => none
        | some a1 => occScanF V B n b (d + 1) a1
      | .forallE t b _ =>
        match occScanF V B n t d acc with
        | none => none
        | some a1 => occScanF V B n b (d + 1) a1
      | .letE t v b _ =>
        match occScanF V B n t d acc with
        | none => none
        | some a1 =>
          match occScanF V B n v d a1 with
          | none => none
          | some a2 => occScanF V B n b (d + 1) a2
      | .proj _ _ x => occScanF V B n x d acc
      | _ => some acc

/-- The size of a term: the fuel `occ_scan` needs (each call descends to a strict subterm). -/
def exprSize : Ix.Kernel.Expr .anon → Nat
  | .app f a => exprSize f + exprSize a + 1
  | .lam t b _ => exprSize t + exprSize b + 1
  | .forallE t b _ => exprSize t + exprSize b + 1
  | .letE t v b _ => exprSize t + exprSize v + exprSize b + 1
  | .proj _ _ e => exprSize e + 1
  | _ => 1

/-- One constructor of `ctors_scan`: its type at the entry's levels, past the parameters (a type
of the block, `peel_n_foralls`) or with the parameters instantiated (an auxiliary,
`inst_ctor_params`), scanned. The circuit's `expr_inst1` lifts the argument past the binders it
crosses, and an auxiliary's parameters are terms over the recursor's parameters, so the
substitution is the lifting one (`instantiate1Lift`). -/
def instCtorParams : Ix.Kernel.Expr .anon → List (Ix.Kernel.Expr .anon) →
    Option (Ix.Kernel.Expr .anon)
  | t, [] => some t
  | .forallE _ b _, v :: vs => instCtorParams (Ix.Kernel.Expr.instantiate1Lift b v 0) vs
  | _, _ :: _ => none

/-- A constructor type's body at an entry: past the `np` parameters at a type of the block, the
parameters `sp` instantiated at an auxiliary. -/
def ctorBody (aux : Bool) (np : Nat) (sp : List (Ix.Kernel.Expr .anon))
    (ty : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  match aux with
  | true => instCtorParams ty sp
  | false => peelForalls np ty

/-- One constructor's scan (`ctors_scan`'s step). -/
def ctorScan (V : FlatView) (B : _root_.Address) (i : IndInfo) (aux : Bool)
    (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level) (acc : List FlatEntry)
    (c : Nat) : Option (List FlatEntry) :=
  match V.ctorType i.blk i.idx c with
  | none => none
  | some cty =>
    match ctorBody aux i.np sp (cty.instantiateLevelParams (List.range us.length) us) with
    | none => none
    | some body => occScanF V B (exprSize body + 1) body 0 acc

/-- `ctors_scan`: the constructors `c` onwards of one entry. -/
def ctorsLoop (V : FlatView) (B : _root_.Address) (i : IndInfo) (aux : Bool)
    (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level) :
    List Nat → List FlatEntry → Option (List FlatEntry)
  | [], acc => some acc
  | c :: cs, acc =>
    match ctorScan V B i aux sp us acc c with
    | none => none
    | some a => ctorsLoop V B i aux sp us cs a

/-- **`ctors_scan`**: every constructor of one entry. -/
def ctorsScan (V : FlatView) (B : _root_.Address) (i : IndInfo) (aux : Bool)
    (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level) (acc : List FlatEntry) :
    Option (List FlatEntry) :=
  ctorsLoop V B i aux sp us (List.range i.nctors) acc

/-- **`nested_walk`** at a fuel of steps: the constructors of entry `i` onwards, each new entry
appended; the entries when every one is scanned. -/
def nestedWalk (V : FlatView) (B : _root_.Address) :
    Nat → Nat → List FlatEntry → Option (List FlatEntry)
  | 0, _, _ => none
  | n + 1, i, acc =>
    match acc[i]? with
    | none => some acc
    | some e =>
      match V.ci e.addr with
      | some (some info) =>
        match ctorsScan V B info e.aux e.params e.levels acc with
        | none => none
        | some a => nestedWalk V B n (i + 1) a
      | _ => none

/-- `build_flat_originals` at the elimination offset `off`: each type of the block at the
recursor's levels (its own level parameters shifted by `off`). -/
def originals (V : FlatView) (off : Nat) : List _root_.Address → Option (List FlatEntry)
  | [] => some []
  | a :: as =>
    match V.ci a with
    | some (some i) =>
      match originals V off as with
      | none => none
      | some es =>
        some (⟨a, false, [], (List.range i.nl).map fun j => .param (off + j)⟩ :: es)
    | _ => none

/-- **The flattened family derived from the block `B`** at the elimination offset `off` and a
fuel of steps: its types, then `nested_walk` from them. -/
def derivedFlatAt (V : FlatView) (B : _root_.Address) (off n : Nat) :
    Option (List FlatEntry) :=
  match V.members B with
  | none => none
  | some ms =>
    match originals V off ms with
    | none => none
    | some os => nestedWalk V B n 0 os

/-- **`es` is the flattened family derived from the block `B` in the store `E`** (the changed
`aux_all_in` in `check_nested_aux` asserts that a family record's entries are these, in order;
the constructor types in the canonical reading, `ctorTypeAt`),
at the block's elimination offset `off` (`block_elim`, a function of the block). -/
def BlockDerivedFlat (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address) (off : Nat)
    (es : List FlatEntry) : Prop :=
  ∃ n, derivedFlatAt (FlatView.ofStore t E) B off n = some es

/-! ## One derivation -/

/-- **`nestedWalk` answers the same at every larger fuel.** -/
theorem nestedWalk_mono (V : FlatView) (B : _root_.Address) :
    ∀ (n n' i : Nat) (acc r : List FlatEntry), nestedWalk V B n i acc = some r → n ≤ n' →
      nestedWalk V B n' i acc = some r := by
  intro n
  induction n with
  | zero =>
    intro n' i acc r h _
    simp [nestedWalk] at h
  | succ n ih =>
    intro n' i acc r h hle
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    simp only [nestedWalk] at h ⊢
    cases hi : acc[i]? with
    | none =>
      simp only [hi] at h ⊢
      exact h
    | some e =>
      simp only [hi] at h ⊢
      cases hc : V.ci e.addr with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none => simp [hc] at h
        | some info =>
          simp only [hc] at h ⊢
          cases hs : ctorsScan V B info e.aux e.params e.levels acc with
          | none => simp [hs] at h
          | some a =>
            simp only [hs] at h ⊢
            exact ih m (i + 1) a r h (by omega)

/-- **The derivation at two fuels is one.** -/
theorem derivedFlatAt_unique {V : FlatView} {B : _root_.Address} {off n n' : Nat}
    {es es' : List FlatEntry} (h : derivedFlatAt V B off n = some es)
    (h' : derivedFlatAt V B off n' = some es') : es = es' := by
  unfold derivedFlatAt at h h'
  cases hm : V.members B with
  | none => simp [hm] at h
  | some ms =>
    cases ho : originals V off ms with
    | none => simp [hm, ho] at h
    | some os =>
      simp only [hm, ho] at h h'
      have e1 := nestedWalk_mono V B n (max n n') 0 os es h (Nat.le_max_left _ _)
      have e2 := nestedWalk_mono V B n' (max n n') 0 os es' h' (Nat.le_max_right _ _)
      exact Option.some.inj (e1.symm.trans e2)

/-! ## A view that answers more -/

/-- **`V'` answers whatever `V` answers, the same.** -/
structure FlatView.Le (V V' : FlatView) : Prop where
  ci : ∀ a x, V.ci a = some x → V'.ci a = some x
  ctorType : ∀ b i c x, V.ctorType b i c = some x → V'.ctorType b i c = some x
  members : ∀ b x, V.members b = some x → V'.members b = some x
  addr : ∀ k x, V.addr k = some x → V'.addr k = some x

/-- **Two views agree where both answer.** -/
structure FlatView.Agree (V V' : FlatView) : Prop where
  ci : ∀ a x y, V.ci a = some x → V'.ci a = some y → x = y
  ctorType : ∀ b i c x y, V.ctorType b i c = some x → V'.ctorType b i c = some y → x = y
  members : ∀ b x y, V.members b = some x → V'.members b = some y → x = y
  addr : ∀ k x y, V.addr k = some x → V'.addr k = some y → x = y

/-- The view answering what either answers, the first first. -/
def FlatView.union (V V' : FlatView) : FlatView where
  ci a := match V.ci a with
    | some x => some x
    | none => V'.ci a
  ctorType b i c := match V.ctorType b i c with
    | some x => some x
    | none => V'.ctorType b i c
  members b := match V.members b with
    | some x => some x
    | none => V'.members b
  addr k := match V.addr k with
    | some x => some x
    | none => V'.addr k

theorem FlatView.le_union_left (V V' : FlatView) : V.Le (V.union V') where
  ci a x h := by simp [FlatView.union, h]
  ctorType b i c x h := by simp [FlatView.union, h]
  members b x h := by simp [FlatView.union, h]
  addr k x h := by simp [FlatView.union, h]

theorem FlatView.le_union_right {V V' : FlatView} (hA : V.Agree V') : V'.Le (V.union V') where
  ci a y hy := by
    simp only [FlatView.union]
    cases hx : V.ci a with
    | none => simp [hy]
    | some x => simp [hA.ci a x y hx hy]
  ctorType b i c y hy := by
    simp only [FlatView.union]
    cases hx : V.ctorType b i c with
    | none => simp [hy]
    | some x => simp [hA.ctorType b i c x y hx hy]
  members b y hy := by
    simp only [FlatView.union]
    cases hx : V.members b with
    | none => simp [hy]
    | some x => simp [hA.members b x y hx hy]
  addr k y hy := by
    simp only [FlatView.union]
    cases hx : V.addr k with
    | none => simp [hy]
    | some x => simp [hA.addr k x y hx hy]

theorem orB_le {x x' y y' : Option Bool} (hx : ∀ r, x = some r → x' = some r)
    (hy : ∀ r, y = some r → y' = some r) {r : Bool} (h : orB x y = some r) :
    orB x' y' = some r := by
  cases hxv : x with
  | none => simp [orB, hxv] at h
  | some b =>
    have hx' := hx b hxv
    cases b with
    | true =>
      simp only [orB, hxv] at h
      simp only [orB, hx']
      exact h
    | false =>
      simp only [orB, hxv] at h
      simp only [orB, hx']
      exact hy r h

theorem peer_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) {k : Ix.Kernel.Key .anon}
    {r : Bool} (h : peer V B k = some r) : peer V' B k = some r := by
  unfold peer at h ⊢
  cases ha : V.addr k with
  | none => simp [ha] at h
  | some a =>
    simp only [ha, hV.addr k a ha] at h ⊢
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      simp only [hc, hV.ci a x hc] at h ⊢
      exact h

theorem mentions_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) :
    ∀ (e : Ix.Kernel.Expr .anon) (r : Bool), mentions V B e = some r →
      mentions V' B e = some r := by
  intro e
  induction e with
  | bvar _ => intro r h; simp only [mentions] at h ⊢; exact h
  | fvar _ _ _ => intro r h; simp only [mentions] at h ⊢; exact h
  | sort _ => intro r h; simp only [mentions] at h ⊢; exact h
  | const k _ => intro r h; simp only [mentions] at h ⊢; exact peer_le hV B h
  | app f a ihf iha => intro r h; simp only [mentions] at h ⊢; exact orB_le ihf iha h
  | lam t b _ iht ihb => intro r h; simp only [mentions] at h ⊢; exact orB_le iht ihb h
  | forallE t b _ iht ihb => intro r h; simp only [mentions] at h ⊢; exact orB_le iht ihb h
  | letE t v b _ iht ihv ihb =>
    intro r h
    simp only [mentions] at h ⊢
    exact orB_le iht (fun r' h' => orB_le ihv ihb h') h
  | lit _ => intro r h; simp only [mentions] at h ⊢; exact h
  | proj _ _ e ih => intro r h; simp only [mentions] at h ⊢; exact ih r h

theorem mentionsList_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) :
    ∀ (es : List (Ix.Kernel.Expr .anon)) (r : Bool), mentionsList V B es = some r →
      mentionsList V' B es = some r := by
  intro es
  induction es with
  | nil => intro r h; exact h
  | cons e es ih =>
    intro r h
    simp only [mentionsList] at h ⊢
    exact orB_le (mentions_le hV B e) ih h

theorem nestedAt_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) (i : IndInfo)
    (args : List (Ix.Kernel.Expr .anon)) {r : Bool} (h : nestedAt V B i args = some r) :
    nestedAt V' B i args = some r := by
  unfold nestedAt at h ⊢
  cases hb : (i.blk == B || decide (args.length < i.np)) with
  | true =>
    simp only [hb] at h ⊢
    exact h
  | false =>
    simp only [hb] at h ⊢
    exact mentionsList_le hV B _ r h

theorem scanList_le {rec rec' : Ix.Kernel.Expr .anon → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ x acc r, rec x acc = some r → rec' x acc = some r) :
    ∀ (l : List (Ix.Kernel.Expr .anon)) (acc r : List FlatEntry), scanList rec l acc = some r →
      scanList rec' l acc = some r := by
  intro l
  induction l with
  | nil => intro acc r h; exact h
  | cons x xs ih =>
    intro acc r h
    simp only [scanList] at h ⊢
    cases hx : rec x acc with
    | none => simp [hx] at h
    | some a =>
      simp only [hx, hr x acc a hx] at h ⊢
      exact ih a r h

theorem appCase_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address)
    {rec rec' : Ix.Kernel.Expr .anon → Nat → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ e d acc r, rec e d acc = some r → rec' e d acc = some r)
    {hd : Ix.Kernel.Expr .anon} {args : List (Ix.Kernel.Expr .anon)} {d : Nat}
    {acc r : List FlatEntry} (h : appCase rec V B hd args d acc = some r) :
    appCase rec' V' B hd args d acc = some r := by
  have hs : ∀ acc r, scanList (fun x acc => rec x d acc) args acc = some r →
      scanList (fun x acc => rec' x d acc) args acc = some r :=
    fun acc r => scanList_le (fun x acc r => hr x d acc r) args acc r
  unfold appCase at h ⊢
  cases hk : constOf hd with
  | none =>
    simp only [hk] at h ⊢
    cases h1 : rec hd d acc with
    | none => simp [h1] at h
    | some a =>
      simp only [h1, hr hd d acc a h1] at h ⊢
      exact hs a r h
  | some p =>
    obtain ⟨c, us⟩ := p
    simp only [hk] at h ⊢
    cases ha : V.addr c with
    | none => simp [ha] at h
    | some ca =>
      simp only [ha, hV.addr c ca ha] at h ⊢
      cases hc : V.ci ca with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none =>
          simp only [hc, hV.ci ca none hc] at h ⊢
          exact hs acc r h
        | some i =>
          simp only [hc, hV.ci ca (some i) hc] at h ⊢
          cases hn : nestedAt V B i args with
          | none => simp [hn] at h
          | some b =>
            have hn' := nestedAt_le hV B i args hn
            cases b with
            | false =>
              simp only [hn, hn'] at h ⊢
              exact hs acc r h
            | true =>
              simp only [hn, hn'] at h ⊢
              cases hm : V.members i.blk with
              | none => simp [hm] at h
              | some ms =>
                simp only [hm, hV.members i.blk ms hm] at h ⊢
                exact h

theorem occScanF_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) :
    ∀ (n : Nat) (e : Ix.Kernel.Expr .anon) (d : Nat) (acc r : List FlatEntry),
      occScanF V B n e d acc = some r → occScanF V' B n e d acc = some r := by
  intro n
  induction n with
  | zero => intro e d acc r h; simp [occScanF] at h
  | succ n ih =>
    intro e d acc r h
    simp only [occScanF] at h ⊢
    cases hm : mentions V B e with
    | none => simp [hm] at h
    | some b =>
      have hm' := mentions_le hV B e b hm
      cases b with
      | false =>
        simp only [hm, hm'] at h ⊢
        exact h
      | true =>
        simp only [hm, hm'] at h ⊢
        cases e with
        | app f a =>
          simp only at h ⊢
          exact appCase_le hV B ih h
        | lam t b m =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1, ih t d acc a1 h1] at h ⊢
            exact ih b (d + 1) a1 r h
        | forallE t b m =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1, ih t d acc a1 h1] at h ⊢
            exact ih b (d + 1) a1 r h
        | letE t v b l =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1, ih t d acc a1 h1] at h ⊢
            cases h2 : occScanF V B n v d a1 with
            | none => simp [h2] at h
            | some a2 =>
              simp only [h2, ih v d a1 a2 h2] at h ⊢
              exact ih b (d + 1) a2 r h
        | proj s i x =>
          simp only at h ⊢
          exact ih x d acc r h
        | bvar _ => exact h
        | fvar _ _ => exact h
        | sort _ => exact h
        | const _ _ => exact h
        | lit _ => exact h

theorem ctorScan_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) (i : IndInfo)
    (aux : Bool) (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level)
    {acc r : List FlatEntry} {c : Nat} (h : ctorScan V B i aux sp us acc c = some r) :
    ctorScan V' B i aux sp us acc c = some r := by
  unfold ctorScan at h ⊢
  cases hc : V.ctorType i.blk i.idx c with
  | none => simp [hc] at h
  | some cty =>
    simp only [hc, hV.ctorType i.blk i.idx c cty hc] at h ⊢
    cases hb : ctorBody aux i.np sp (cty.instantiateLevelParams (List.range us.length) us) with
    | none => simp [hb] at h
    | some body =>
      simp only [hb] at h ⊢
      exact occScanF_le hV B _ body 0 acc r h

theorem ctorsLoop_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) (i : IndInfo)
    (aux : Bool) (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level) :
    ∀ (cs : List Nat) (acc r : List FlatEntry), ctorsLoop V B i aux sp us cs acc = some r →
      ctorsLoop V' B i aux sp us cs acc = some r := by
  intro cs
  induction cs with
  | nil => intro acc r h; exact h
  | cons c cs ih =>
    intro acc r h
    simp only [ctorsLoop] at h ⊢
    cases h1 : ctorScan V B i aux sp us acc c with
    | none => simp [h1] at h
    | some a =>
      simp only [h1, ctorScan_le hV B i aux sp us h1] at h ⊢
      exact ih a r h

theorem nestedWalk_le {V V' : FlatView} (hV : V.Le V') (B : _root_.Address) :
    ∀ (n i : Nat) (acc r : List FlatEntry), nestedWalk V B n i acc = some r →
      nestedWalk V' B n i acc = some r := by
  intro n
  induction n with
  | zero => intro i acc r h; simp [nestedWalk] at h
  | succ n ih =>
    intro i acc r h
    simp only [nestedWalk] at h ⊢
    cases hi : acc[i]? with
    | none =>
      simp only [hi] at h ⊢
      exact h
    | some e =>
      simp only [hi] at h ⊢
      cases hc : V.ci e.addr with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none => simp [hc] at h
        | some info =>
          simp only [hc, hV.ci e.addr (some info) hc] at h ⊢
          cases hs : ctorsScan V B info e.aux e.params e.levels acc with
          | none => simp [hs] at h
          | some a =>
            have hs' : ctorsScan V' B info e.aux e.params e.levels acc = some a :=
              ctorsLoop_le hV B info e.aux e.params e.levels _ acc a hs
            simp only [hs, hs'] at h ⊢
            exact ih (i + 1) a r h

theorem originals_le {V V' : FlatView} (hV : V.Le V') (off : Nat) :
    ∀ (as : List _root_.Address) (es : List FlatEntry), originals V off as = some es →
      originals V' off as = some es := by
  intro as
  induction as with
  | nil => intro es h; exact h
  | cons a as ih =>
    intro es h
    simp only [originals] at h ⊢
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none => simp [hc] at h
      | some i =>
        simp only [hc, hV.ci a (some i) hc] at h ⊢
        cases ho : originals V off as with
        | none => simp [ho] at h
        | some os =>
          simp only [ho, ih os ho] at h ⊢
          exact h

/-- **A view that answers more derives the same.** -/
theorem derivedFlatAt_le {V V' : FlatView} (hV : V.Le V') {B : _root_.Address} {off n : Nat}
    {es : List FlatEntry} (h : derivedFlatAt V B off n = some es) :
    derivedFlatAt V' B off n = some es := by
  unfold derivedFlatAt at h ⊢
  cases hm : V.members B with
  | none => simp [hm] at h
  | some ms =>
    simp only [hm, hV.members B ms hm] at h ⊢
    cases ho : originals V off ms with
    | none => simp [ho] at h
    | some os =>
      simp only [ho, originals_le hV off ms os ho] at h ⊢
      exact nestedWalk_le hV B n 0 os es h

/-- **Two views that agree where both answer derive the same entries from one block.** -/
theorem derivedFlatAt_agree {V V' : FlatView} (hA : V.Agree V') {B : _root_.Address}
    {off n n' : Nat} {es es' : List FlatEntry} (h : derivedFlatAt V B off n = some es)
    (h' : derivedFlatAt V' B off n' = some es') : es = es' :=
  derivedFlatAt_unique (derivedFlatAt_le (FlatView.le_union_left V V') h)
    (derivedFlatAt_le (FlatView.le_union_right hA) h')

/-- **Two stores whose readings agree where both answer derive the same flattened family from
one block, at one elimination offset.** -/
theorem blockDerivedFlat_unique {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env} {B : _root_.Address}
    {off : Nat} {es es' : List FlatEntry}
    (hA : FlatView.Agree (FlatView.ofStore t E) (FlatView.ofStore t E'))
    (h : BlockDerivedFlat t E B off es) (h' : BlockDerivedFlat t E' B off es') : es = es' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := h'
  exact derivedFlatAt_agree hA hn hn'

end IxVM.Refinement.Binding.FamilyFlat
