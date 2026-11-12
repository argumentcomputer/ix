module

public import IxC.Resource.Read
public import IxC.Resource.Eval
public import IxC.Kernel.Rules.Rel
public import IxC.Kernel.Verify.Level

/-!
# The mode-safety statement

`ModeSafe env s` is the statement a modes claim would carry: the claim's records
read as a run program `P` (`Reads`); for every seed with a run body, every input
heap meeting its declared modes (`InputsOk`), every extern behaving as its
declared modes allow (`ExternOk`) and every fuel, `runR` never ends in one of
its four violations. Runs that end `stuck` or out of fuel are not covered.

It is a definition. Nothing here, and nothing in this library, proves it of the
checker (`IxC.Resource.check`): that theorem and the others the follow-up work
proves are stated below as definitions (`DefaultOk`).

**One reading for typing and modes.** `env` is the kernel environment the
consistency statement's reading installs (`IxVM.Consistency.ConsistentRead`'s
`env`), and `s.store` that reading's records; a claim carrying both conclusions
states them inside one existential, so typing and modes are answered from the
same bytes.

**Classes are the kernel's.** The run program's classes are read with the
canonical class oracle (`canonClassifier`): a term is `irr` when the kernel's
rules (`Rules.Infer`, `Rules.Red`) type it as a type, a type former or a proof;
`imm` or `leaf` when they type it at an immediate or leaf type (`ImmT`, `LeafT`,
least fixed points, so a type that wraps itself is neither).
-/

@[expose] public section

namespace IxC.Resource

open Ixon
open Ix.Kernel (Env Key)

/-! ## Constructor shapes -/

/-- A constructor, as the classes need it: its kernel type, its parameter count,
and which of its fields are erased (its binders' modes in its record). -/
structure CtorShape where
  type : KExpr
  nParams : Nat
  erased : List Bool

/-- The record address a kernel key names. -/
def keyAddress (s : Subject) : Key .anon → Option Address
  | .id a => some a
  | .role r => s.table.addressOf? r
  | .aux _ _ => none

/-- A class oracle that answers `val`, for readings that use no class. -/
def noClasses : Classifier := { type := fun _ _ => .ok .val, node := fun _ _ => .ok .val }

/-- The constructors of the inductive type a key names, from the records. -/
def ctorShapes (rd : Reading) (k : Key .anon) : Option (List CtorShape) := do
  let a ← keyAddress rd.s k
  let r ← Ix.Kernel.Reader.resolve rd.s.store a
  let ind ← inductiveAt? rd.s r
  let x ← (rd.rcx noClasses r).toOption
  let .member _ i := r | none
  let base := rootBase x.c i
  let nP := ind.params.toNat
  (List.range ind.ctors.size).mapM fun ci => do
    let ctor ← ind.ctors[ci]?
    let type ← (x.toK [] ctor.typ).toOption
    let (alls, _) ← ((inBlock x.rm (rootKey (base + 1 + ci)) (do
        let (alls, cod) ← readForalls x readFuel ctor.typ
        let _ ← readSkel x readFuel cod
        pure alls)).run {}).toOption
    pure { type, nParams := nP, erased := (alls.drop nP).map fun (m, _, _) => m.input == .erased }

/-! ## The canonical classes -/

/-- Instantiate a type's leading ∀s with `args`. -/
def instParams : KExpr → List KExpr → Option KExpr
  | t, [] => some t
  | .forallE _ b _, a :: as => instParams (b.instantiate1 a) as
  | _, _ :: _ => none

/-- **The types of irrelevant terms**: `T`, opened at depth `d`, reduces to a
sort (its terms are types), to a ∀ whose body is again such a type (type
formers), or is a proposition (its terms are proofs). -/
inductive IrrType (env : Env .anon) : Nat → KExpr → Prop
  | sort {d : Nat} {T : KExpr} {u : Ix.Kernel.Level} :
      Ix.Kernel.Rules.Red env d T (.sort u) → IrrType env d T
  | former {d : Nat} {T A B : KExpr} {m : Ix.Kernel.BinderMeta} :
      Ix.Kernel.Rules.Red env d T (.forallE A B m) →
      IrrType env (d + 1) (B.instantiate1 (.fvar d A)) → IrrType env d T
  | prop {d : Nat} {T S : KExpr} {u : Ix.Kernel.Level} :
      Ix.Kernel.Rules.Infer env .full d T S → Ix.Kernel.Rules.Red env d S (.sort u) →
      (∀ φ, Ix.Kernel.Level.eval φ u = 0) → IrrType env d T

/-- A constructor type's kept fields (relevant and not erased), opened: the
field telescope of `T` with its erasure flags `er`, giving each kept field's
depth and type. -/
inductive KeptFields (env : Env .anon) : Nat → KExpr → List Bool → List (Nat × KExpr) → Prop
  | nil {d : Nat} {T : KExpr} : KeptFields env d T [] []
  | keep {d : Nat} {A B : KExpr} {m : Ix.Kernel.BinderMeta} {er : List Bool}
      {out : List (Nat × KExpr)} :
      ¬ IrrType env d A → KeptFields env (d + 1) (B.instantiate1 (.fvar d A)) er out →
      KeptFields env d (.forallE A B m) (false :: er) ((d, A) :: out)
  | drop {d : Nat} {A B : KExpr} {m : Ix.Kernel.BinderMeta} {e : Bool} {er : List Bool}
      {out : List (Nat × KExpr)} :
      (e = true ∨ IrrType env d A) → KeptFields env (d + 1) (B.instantiate1 (.fvar d A)) er out →
      KeptFields env d (.forallE A B m) (e :: er) out

mutual

/-- **Immediate types**, least: an enumeration (every constructor without a
kept field); `BitVec w` at a literal width `w ≤ 64` (by the role table's
`bitVec` role, and only where the type is already a leaf, so the role can only
refine a leaf); a trivial wrapper of an immediate; `Nat` if the class of `Nat`
is `imm`. -/
inductive ImmT (env : Env .anon) (sh : Key .anon → Option (List CtorShape)) : Nat → KExpr → Prop
  | nat {d : Nat} {T : KExpr} {us : List Ix.Kernel.Level} :
      natClass = .imm → Ix.Kernel.Rules.Red env d T (.const (.role .nat) us) → ImmT env sh d T
  | enum {d : Nat} {T : KExpr} {I : Key .anon} {us : List Ix.Kernel.Level} {args : List KExpr}
      {cs : List CtorShape} :
      Ix.Kernel.Rules.Red env d T (Ix.Kernel.Expr.mkAppN (.const I us) args) → sh I = some cs →
      (∀ c ∈ cs, ∃ T', instParams c.type (args.take c.nParams) = some T' ∧
        KeptFields env d T' c.erased []) →
      ImmT env sh d T
  | bitVec {d k : Nat} {T w : KExpr} {us : List Ix.Kernel.Level} :
      Ix.Kernel.Rules.Red env d T (.app (.const (.role .bitVec) us) w) →
      Ix.Kernel.Rules.Red env d w (.lit (.natVal k)) → k ≤ 64 → LeafT env sh d T → ImmT env sh d T
  | wrap {d d' : Nat} {T T' F : KExpr} {I : Key .anon} {us : List Ix.Kernel.Level}
      {args : List KExpr} {c : CtorShape} :
      Ix.Kernel.Rules.Red env d T (Ix.Kernel.Expr.mkAppN (.const I us) args) → sh I = some [c] →
      instParams c.type (args.take c.nParams) = some T' → KeptFields env d T' c.erased [(d', F)] →
      ImmT env sh d' F → ImmT env sh d T

/-- **Leaf types**, least: `Nat` if the class of `Nat` is `leaf`; a trivial
wrapper of a leaf. -/
inductive LeafT (env : Env .anon) (sh : Key .anon → Option (List CtorShape)) : Nat → KExpr → Prop
  | nat {d : Nat} {T : KExpr} {us : List Ix.Kernel.Level} :
      natClass = .leaf → Ix.Kernel.Rules.Red env d T (.const (.role .nat) us) → LeafT env sh d T
  | wrap {d d' : Nat} {T T' F : KExpr} {I : Key .anon} {us : List Ix.Kernel.Level}
      {args : List KExpr} {c : CtorShape} :
      Ix.Kernel.Rules.Red env d T (Ix.Kernel.Expr.mkAppN (.const I us) args) → sh I = some [c] →
      instParams c.type (args.take c.nParams) = some T' → KeptFields env d T' c.erased [(d', F)] →
      LeafT env sh d' F → LeafT env sh d T

end

/-- The class of the terms of type `T`. -/
noncomputable def typeClass (env : Env .anon) (sh : Key .anon → Option (List CtorShape))
    (d : Nat) (T : KExpr) : Cls := by
  classical
  exact if IrrType env d T then .irr else if ImmT env sh d T then .imm
    else if LeafT env sh d T then .leaf else .val

/-- The class of the term `e`. -/
noncomputable def nodeClass (env : Env .anon) (sh : Key .anon → Option (List CtorShape))
    (d : Nat) (e : KExpr) : Cls := by
  classical
  exact if ∃ T, Ix.Kernel.Rules.Infer env .full d e T ∧ IrrType env d T then .irr
    else if ∃ T, Ix.Kernel.Rules.Infer env .full d e T ∧ ImmT env sh d T then .imm
    else if ∃ T, Ix.Kernel.Rules.Infer env .full d e T ∧ LeafT env sh d T then .leaf
    else .val

/-- **The class oracle's definition**: the kernel's own judgements, over the
environment `env`. One definition, so a different oracle (a fueled run at fixed
limits, say) is a change here. -/
noncomputable def canonClassifier (env : Env .anon) (s : Subject) : Classifier :=
  let sh := ctorShapes (Reading.make s)
  { type := fun d T => .ok (typeClass env sh d T), node := fun d e => .ok (nodeClass env sh d e) }

/-- **The run program of a subject**, read with the kernel's classes. -/
def Reads (env : Env .anon) (s : Subject) (P : Prog) : Prop :=
  readProg s (canonClassifier env s) = .ok P

/-! ## Heaps meeting declared modes -/

/-- The values a cell holds. -/
def Cell.vals : Cell → List Val
  | .ctor _ fs => fs.toList
  | .num _ | .str _ => []
  | .clo env _ _ _ _ _ => env.map (·.val)
  | .pap _ as => as.toList
  | .once t _ => [t]

def Cell.isNum : Cell → Bool
  | .num _ => true
  | _ => false

/-- `l` is reachable from `v` in `h`. -/
inductive Reach (h : Heap) : Val → Nat → Prop
  | here {loc cap : Nat} {t : List Nat} : Reach h (.ref loc cap t) loc
  | step {loc cap : Nat} {t : List Nat} {o : Obj} {v : Val} {l : Nat} :
      h.objs[loc]? = some o → v ∈ o.cell.vals → Reach h v l → Reach h (.ref loc cap t) l

/-- `l` is in `v`'s ownership closure (`ownedSlots`; leaves excluded). -/
inductive OwnReach (P : Prog) (h : Heap) : Val → Nat → Prop
  | here {loc cap : Nat} {t : List Nat} {o : Obj} :
      h.objs[loc]? = some o → (o.cell.isNum = false ∨ natClass ≠ .leaf) →
      OwnReach P h (.ref loc cap t) loc
  | step {loc cap : Nat} {t : List Nat} {o : Obj} {i : Nat} {v : Val} {l : Nat} :
      h.objs[loc]? = some o → i ∈ ownedSlots P o.cell → o.cell.slot? i = some v →
      OwnReach P h v l → OwnReach P h (.ref loc cap t) l

/-- `v`'s ownership closure is a tree: no cell of it (a leaf excepted) is held
by two owned slots in it. -/
def OwnTree (P : Prog) (h : Heap) (v : Val) : Prop :=
  ∀ (p₁ p₂ i₁ i₂ l c₁ c₂ : Nat) (o₁ o₂ : Obj) (t₁ t₂ : List Nat),
    OwnReach P h v p₁ → OwnReach P h v p₂ → h.objs[p₁]? = some o₁ → h.objs[p₂]? = some o₂ →
    i₁ ∈ ownedSlots P o₁.cell → i₂ ∈ ownedSlots P o₂.cell →
    o₁.cell.slot? i₁ = some (.ref l c₁ t₁) → o₂.cell.slot? i₂ = some (.ref l c₂ t₂) →
    (∀ o, h.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf) →
    p₁ = p₂ ∧ i₁ = i₂

/-- A reference that is live and confined to no region. -/
def ValOk (h : Heap) : Val → Prop
  | .imm _ => True
  | .ref loc cap t => t = [] ∧ ∃ o, h.objs[loc]? = some o ∧ o.cap = cap

/-- A function type's skeleton from an interface: its parameters' arrows, the
last carrying the result mode. -/
def ifaceSkel : List Param → ResultMode → Skel → Skel
  | [], _, cod => cod
  | [p], r, cod => .arrow p.mode p.skel r cod
  | p :: ps, r, cod => .arrow p.mode p.skel .shared (ifaceSkel ps r cod)

/-- The skeleton of a partial application of `r` to `n` arguments. -/
def papSkel (P : Prog) (r : Ref) (n : Nat) : Option Skel :=
  match P.find? r with
  | some (.body ps res _ rs _) => some (ifaceSkel (ps.toList.drop n) res rs)
  | some (.extern ps res _ rs) => some (ifaceSkel (ps.toList.drop n) res rs)
  | _ => none

/-- A cell an input heap may hold: data, numbers, strings, and partial
applications of the program's constants; no closure of other code, no once view. -/
def InputCell (P : Prog) : Cell → Prop
  | .ctor _ _ | .num _ | .str _ => True
  | .pap r args => ∃ sk, papSkel P r args.size = some sk
  | .clo .. | .once .. => False

/-- An input heap: its cells are input cells; every value in it is a live,
unconfined reference or an immediate; it is acyclic. -/
def HeapOk (P : Prog) (h : Heap) : Prop :=
  ∀ (loc : Nat) (o : Obj), h.objs[loc]? = some o → InputCell P o.cell ∧ o.cap < h.nextCap ∧
    ∀ v ∈ o.cell.vals, ValOk h v ∧ ¬ Reach h v loc

/-- An argument a partial application in an input may hold: an immediate or a
number cell. -/
def PapArgOk (h : Heap) (v : Val) : Prop :=
  (∃ i, v = .imm i) ∨ ∃ loc cap o n, v = .ref loc cap [] ∧ h.objs[loc]? = some o ∧ o.cell = .num n

/-- An input at an arrow skeleton `s`: a partial application of a constant of
the program whose remaining interface `s` admits. -/
def ClosureAt (P : Prog) (h : Heap) (s : Skel) (v : Val) : Prop :=
  ∃ loc cap r args o sk, v = .ref loc cap [] ∧ h.objs[loc]? = some o ∧ o.cell = .pap r args ∧
    (∀ a ∈ args.toList, PapArgOk h a) ∧ papSkel P r args.size = some sk ∧ s.admits sk = true

/-- Every partial application reachable from `v` has a default remaining interface. -/
def DefaultPaps (P : Prog) (h : Heap) (v : Val) : Prop :=
  ∀ (l : Nat) (o : Obj) (r : Ref) (args : Array Val), Reach h v l → h.objs[l]? = some o → o.cell = .pap r args →
    (∀ a ∈ args.toList, PapArgOk h a) ∧ ∃ sk, papSkel P r args.size = some sk ∧ sk.isDefault = true

/-- An argument meeting a parameter: erased and irrelevant ones `irr`, the class
respected, a closure at an arrow skeleton the skeleton admits, and only default
closures elsewhere. -/
def ArgOk (P : Prog) (h : Heap) (p : Param) (a : Val) : Prop :=
  ValOk h a ∧
  (p.mode = .erased → a = .imm .irr) ∧
  (p.cls = .irr → a = .imm .irr) ∧
  (p.cls = .imm → ∃ i, a = .imm i) ∧
  (p.cls = .leaf → ∃ loc cap o n, a = .ref loc cap [] ∧ h.objs[loc]? = some o ∧ o.cell = .num n) ∧
  (match p.skel with
    | .arrow .. => ClosureAt P h p.skel a
    | _ => DefaultPaps P h a)

/-- **Inputs meeting the declared modes**: one argument per parameter, each
meeting it, in an input heap; an argument at a unique parameter owns a tree
that no other argument reaches. -/
def InputsOk (P : Prog) (h : Heap) (params : Array Param) (args : List Val) : Prop :=
  args.length = params.size ∧ HeapOk P h ∧
  (∀ (i : Nat) (p : Param) (a : Val), params[i]? = some p → args[i]? = some a → ArgOk P h p a) ∧
  (∀ (i : Nat) (p : Param) (a : Val), params[i]? = some p → args[i]? = some a → p.mode.isUnique = true →
    OwnTree P h a ∧ ∀ (j : Nat) (b : Val) (l : Nat), j ≠ i → args[j]? = some b → OwnReach P h a l → ¬ Reach h b l)

/-! ## Externs -/

/-- `v` is `a`, or held by a cell `a` reaches. -/
def HeldBy (h : Heap) (a v : Val) : Prop :=
  v = a ∨ ∃ l o, Reach h a l ∧ h.objs[l]? = some o ∧ v ∈ o.cell.vals

/-- A value an extern may produce: an immediate; a fresh, unconfined reference;
or a value held by an argument at a parameter that neither lends nor transfers. -/
def ExternVal (ps : Array Param) (args : List Val) (h : Heap) (v : Val) : Prop :=
  (∃ i, v = .imm i) ∨ (∃ loc cap, v = .ref loc cap [] ∧ h.objs.size ≤ loc) ∨
  ∃ (i : Nat) (p : Param) (a : Val), ps[i]? = some p ∧ args[i]? = some a ∧ p.mode.isBorrowed = false ∧
    p.mode.isUnique = false ∧ HeldBy h a v

/-- **Externs behave as their declared modes allow**: an extern changes no cell
it was given, except that it may kill the cells it received at a unique
parameter; it builds only input cells of values it may produce; its result is
such a value, of its class, and fresh and unshared at a unique result; it calls
no closure (higher-order externs are not covered). -/
def ExternOk (P : Prog) (ext : ExternOracle) : Prop :=
  ∀ (r : Ref) (ps : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel) (args : List Val)
    (h h' : Heap) (v : Val), P.find? r = some (.extern ps res rc rs) →
    ext r args h = some (h', v) →
    h.objs.size ≤ h'.objs.size ∧ h.nextCap ≤ h'.nextCap ∧
    (∀ (l : Nat) (o : Obj), h.objs[l]? = some o → ∃ o' : Obj, h'.objs[l]? = some o' ∧
      (o'.cell = o.cell ∧ o'.cap = o.cap ∨
        h.nextCap ≤ o'.cap ∧ ∃ (i : Nat) (p : Param) (a : Val), ps[i]? = some p ∧ args[i]? = some a ∧
          p.mode.isUnique = true ∧ OwnReach P h a l)) ∧
    (∀ (l : Nat) (o : Obj), h.objs.size ≤ l → h'.objs[l]? = some o →
      InputCell P o.cell ∧ ∀ w ∈ o.cell.vals, ExternVal ps args h w) ∧
    ExternVal ps args h v ∧
    (rc = .irr → v = .imm .irr) ∧ (rc = .imm → ∃ i, v = .imm i) ∧
    (rc = .leaf → ∃ loc cap o n, v = .ref loc cap [] ∧ h'.objs[loc]? = some o ∧ o.cell = .num n) ∧
    (res.isUnique = true → rc = .val → ∃ loc cap, v = .ref loc cap [] ∧ h.objs.size ≤ loc ∧
      OwnTree P h' v ∧
      ∀ l, OwnReach P h' v l → h.objs.size ≤ l ∧
        ∀ l₂ o₂ w, h'.objs[l₂]? = some o₂ → ¬ OwnReach P h' v l₂ → w ∈ o₂.cell.vals → ¬ Reach h' w l)

/-! ## The statement -/

/-- `r` is a constant the seed `a` claims: the constant at `a`, or a member of
the block at `a`. -/
def SeedRef (s : Subject) (a : Address) (r : Ref) : Prop :=
  match s.store a with
  | some c =>
    match c.info with
    | .muts ms => ∃ i, i < ms.size ∧ r = .member a i
    | _ => Ix.Kernel.Reader.resolve s.store a = some r
  | none => False

/-- **Mode safety.** The subject reads as a run program (malformed modes, a bad
run table or a telescope mismatch make this false, not vacuous), and for every
seed with a run body, every extern behaving as declared, every input meeting the
declared modes and every fuel, the run of the seed never reads an erased value,
never uses a reference revoked by a unique transfer, never lets a borrowed value
outlive its scope, and never calls a once-closure twice. Runs that end `stuck`
or out of fuel are not covered. -/
def ModeSafe (env : Env .anon) (s : Subject) : Prop :=
  (∃ P, Reads env s P) ∧
  ∀ P, Reads env s P → ∀ a ∈ s.seeds, ∀ r, SeedRef s a r →
    ∀ params res rc rs t, P.find? r = some (.body params res rc rs t) →
    ∀ ext, ExternOk P ext → ∀ h args, InputsOk P h params args →
    ∀ fuel k, runR P ext fuel r h args ≠ .violation k

/-! ## Statements for the follow-up work (definitions; nothing is proved here) -/

/-- A run term with every mode default. -/
def Term.defaultModes : Nat → Term → Bool
  | 0, _ => false
  | n + 1, t =>
    match t with
    | .irr | .var .. | .const .. | .natLit _ | .strLit _ => true
    | .app f a _ => Term.defaultModes n f && Term.defaultModes n a
    | .lam p res _ _ b => p.mode == .many && res == .shared && Term.defaultModes n b
    | .letE m _ v b => m == .value .many && Term.defaultModes n v && Term.defaultModes n b
    | .proj _ _ e _ => Term.defaultModes n e
    | .case _ mj alts ex _ =>
      Term.defaultModes n mj && alts.all (Term.defaultModes n) && ex.all (Term.defaultModes n)

/-- A run definition with every mode default. -/
def RunDef.defaultModes : RunDef → Bool
  | .body ps res _ _ t => ps.all (·.mode == .many) && res == .shared && Term.defaultModes (1 <<< 20) t
  | .extern ps res _ _ | .stuck ps res _ _ => ps.all (·.mode == .many) && res == .shared
  | .ctor _ _ _ fs => fs.all fun f => f.mode == .many && f.fmode == .inherited
  | .ind _ | .caseDef _ | .prim _ => true

/-- **`default_ok`**, to prove: a run program with every mode default never
violates (no transfer, region, once view or erased binding ever exists). It
justifies the checker's fast path. -/
def DefaultOk : Prop :=
  ∀ (P : Prog) (ext : ExternOracle) (fuel : Nat) (r : Ref) (h : Heap) (params : Array Param)
    (res : ResultMode) (rc : Cls) (rs : Skel) (t : Term) (args : List Val) (k : Violation),
    (∀ r' d, P.find? r' = some d → d.defaultModes = true) → ExternOk P ext →
    P.find? r = some (.body params res rc rs t) → InputsOk P h params args →
    runR P ext fuel r h args ≠ .violation k

end IxC.Resource

end
