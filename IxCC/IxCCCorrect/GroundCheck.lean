import Std.Data.HashSet
import IxCC.Src.Proof.NatMap
import IxCC.Lam.Erase.Proof.Correct
import IxCCCorrect.GroundRoot
import IxCCCorrect.Tiers

/-!
# The grounding check of the pipeline (`IxCCCorrect.GroundCheck`)

`groundCheck` is the one function a `compile` (or a certificate checker) calls to learn that the
program it compiled means what the kernel says its target means. It is total, reads only what the
checker already holds, and returns the calling convention it has validated:

```lean
groundCheck (k : Src.KernelFront.Kernel)        -- ingress: the kernel's acceptance and its reading
            (src : Src.Program)                 -- the checked source the object refines (`a.src`)
            (checked : Src.Relevance.Checked)   -- its checked annotation (`a.checked`)
            (ann : Src.Relevance.Ann)           -- the certificate's annotation (`c.relevance`)
            (view : Option Obs → Option (Option Obs))  -- the view of root 0 (`a.front.view 0`)
            (target : Ixon.Address)             -- the claimed address
    : Except String Abi
```

`.ok abi`: the claim's `abi` (the parameters, all `Nat`; the result, `Nat` or an enumeration with
its constructors' addresses in the order of the index the executable prints). `.error reason`: the
first refusal, by name (`groundRefusal`), for coverage reports.

**Where it runs.** Production (`IxCC/IxCC/`) may not import the grounding library or the kernel's
model, so this function cannot be called from `IxCC.compile`. It is Denotes-free, but it is
assembled from `IxCC.Grounding`'s checks, which live in the grounding library. The function a
consumer's theorem is about is therefore assembled here, above production: `compile` followed by
`groundCheck` on the artifact `compile` checked (`groundCheckRecheck`, `groundCheckRc`).

**What it decides** (`groundOkB`), on root 0 of the program:

| Part | Decision |
| --- | --- |
| `check`, `noCanon`, `litDefs`, `instCheck`, `headRegime` | the decided hypotheses of the grounding root theorem (`IxCC.Grounding.rootSound_678AGpWPP_of_check`), on `selEnv` of the kernel's environment and the root's closure |
| `root` | the root's facts (`rootCheck`): stored without level parameters at `Nat → … → Nat → res` |
| `target` | root 0's address is the claimed one, and the kernel reader's key for that address (`keyOf`) is the key the grounding check read the root under (links G2 and G3: decided, not proved from `Reading.build`) |
| `result` | at an enumeration result: every constructor the program declares for it without parameter or field is one of its listed ones; each is level-monomorphic, the root's view gives it a tag, and the address at that tag in the claim's list is its own, keyed by the reader as the check read it (link G5) |

The closure `Sl` and the instance set are computed here (`closureOf`, `instWalk`) and are not
trusted: the checks verify them.

`groundCheck_sound`: `.ok abi` gives `GroundOk`, the hypotheses of the composed theorems of
`IxCCCorrect.Compose`.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Grounding

/-! ## The closure (a producer: the checks verify what it returns) -/

/-- The worklist of `reach`: at most `fuel` constants are expanded. -/
def reachGo (p : Program) : Nat → List CId → Std.HashSet CId → Array CId → Array CId
  | 0, _, _, sl => sl
  | _ + 1, [], _, sl => sl
  | fuel + 1, c :: todo, seen, sl =>
    let st := ((runTerms p c).flatMap constsOf).foldl
      (fun (st : Std.HashSet CId × Array CId × List CId) d =>
        if st.1.contains d then st else (st.1.insert d, st.2.1.push d, d :: st.2.2))
      (seen, sl, [])
    reachGo p fuel (todo ++ st.2.2.reverse) st.1 st.2.1

/-- The constants named by the terms SrcEval runs from `seeds`, in discovery order (the order of
`tests-grounding`'s loaders). -/
def reach (p : Program) (seeds : List CId) : List CId :=
  let seeds := seeds.eraseDups
  (reachGo p (p.size + seeds.length + 1) seeds
    (seeds.foldl (fun (s : Std.HashSet CId) c => s.insert c) {}) seeds.toArray).toList

/-- **The closure the check runs on**, for one root: what SrcEval may reach from the root and the
pinned `Bool` constructors, and the runtime references of the word entries among them. -/
def closureOf (p : Program) (root : CId) : List CId :=
  let pins := [p.known.boolTrue, p.known.boolFalse].filterMap id
  let sl := reach p (root :: pins.filter (· != root))
  let refs := (sl.flatMap fun c => match p.table.resolveOf c with
    | some (.word ..) => (p.runtimeRefs c).map (·.1)
    | _ => []).eraseDups
  sl ++ refs.filter (!sl.contains ·)

/-- The fuel of the instance walk. -/
def instFuel : Nat := 1000000

/-! ## What the check reads off the artifact -/

/-- The kernel key of a Src constant under the reading (`Nat`'s where the reading has none: the
check then fails at that constant). -/
def keyMap (rd : Src.KernelFront.Reading) : CId → KKey :=
  fun c => (rd.key? c).getD Ix.Kernel.natName

/-- The kernel level parameters of a Src constant, as stored. -/
def lpsMap (env : KEnv) (κ : CId → KKey) : CId → List Nat := fun c =>
  match env.find? (κ c) with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The constant a root's declared type ends in. -/
def resConst (p : Program) (root : CId) : Option CId :=
  match p.decl? root with
  | some d =>
    match (Src.Term.pis d.type).2 with
    | .const r [] => some r
    | _ => none
  | none => none

/-- **The root's first-order result type**, read off its declaration: `Nat` where the declared type
ends in the pinned `Nat`, otherwise the enumeration it ends in (`rootCheck` then decides that the
kernel stores the root at this type). -/
def resTy (p : Program) (root : CId) : Option FoTy :=
  (resConst p root).map fun r => if some r = p.known.nat then FoTy.nat else FoTy.enum r

/-- The number of parameters the root declares. -/
def arityOf (p : Program) (root : CId) : Nat :=
  match p.decl? root with
  | some d => (Src.Term.pis d.type).1.length
  | none => 0

/-- **The result is a canonical form of the root's first-order result type.** -/
def CanonResult (p : Program) (root : CId) (v : Value) : Prop :=
  ∃ res, resTy p root = some res ∧ CanonAt p res v

/-- **SrcEval returns canonical forms** at root 0, on the `Nat` arguments `ns`: whatever it returns
is a literal (a `Nat` result) or a field-less value of a constructor the program declares for the
result enumeration. A fact about SrcEval alone; a progress proof by shapes has it
(`IxCCCorrect.Shape1`: `run_ok`, `ValOk.nat_inv`, `ValOk.enum_inv`). It is **not** a consequence of
`NeverWrong`: the compiler's view also accepts an unboxed one-field structure around a literal and
a `Decidable` constructor at a `Bool` root (`IxCCCorrect.Compose`, link G1). -/
def ReturnsCanon (p : Program) (ns : List Nat) : Prop :=
  ∀ (addr : Ixon.Address) (root : CId) (k : Nat) (v : Value),
    p.roots.head? = some (addr, root) →
    IxCC.Src.run p k root (ns.map Value.lit) = .ok v → CanonResult p root v

/-! ## The view on the result enumeration's constructors -/

/-- A root's view: the compiler's reading of a source observation at the root's readback type. -/
abbrev View := Option Obs → Option (Option Obs)

/-- The compiler's observation of a SrcEval value (`Lang.obs` of the checked source). -/
def obsOf (I : Lam.Erase.Input) (v : Value) : Option Obs :=
  Lang.obs (S := CheckedProgram) ((I, v) : Lang.Val CheckedProgram)

/-- The index the root's view gives the field-less value of constructor `c`. -/
def viewTag (I : Lam.Erase.Input) (view : View) (c : CId) : Option Nat :=
  match view (obsOf I (.con c [] [] [])) with
  | some (some (.ctor t [])) => some t
  | _ => none

theorem viewTag_some {I : Lam.Erase.Input} {view : View} {c : CId} {t : Nat}
    (h : viewTag I view c = some t) :
    view (obsOf I (.con c [] [] [])) = some (some (.ctor t [])) := by
  unfold viewTag at h
  split at h
  · rename_i t' heq
    cases h
    exact heq
  · cases h

/-- **The claim's constructor list**: the listed constructors' addresses, by the index the view
gives each. -/
def enumAddrs (p : Program) (I : Lam.Erase.Input) (view : View) (cs : List CId) :
    List Ixon.Address :=
  (List.range cs.length).filterMap fun t =>
    (cs.find? fun c => viewTag I view c == some t).map p.addr

/-- A declaration of `c` as a constructor of `D` with no parameter and no field puts `c` in `cs`. -/
def ctorOfB (D : CId) (cs : List CId) (c : CId) : Src.Decl → Bool
  | .ctor _ _ D' _ 0 0 _ => decide (D' = D → c ∈ cs)
  | _ => true

/-- Every constructor the program declares for `D` with no parameter and no field is in `cs`. -/
def ctorsListedB (p : Program) (D : CId) (cs : List CId) : Bool :=
  p.consts.toList.all fun x => ctorOfB D cs x.1 x.2.decl

theorem ctorsListed_sound {p : Program} {D : CId} {cs : List CId}
    (h : ctorsListedB p D cs = true) {c : CId} {s : Bool} {lv i : Nat} {ty : Term}
    (hd : p.decl? c = some (.ctor s lv D i 0 0 ty)) : c ∈ cs := by
  unfold Program.decl? Program.entry? at hd
  cases he : p.consts.get? c with
  | none => rw [he] at hd; cases hd
  | some e =>
    rw [he] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    have hm := IxCC.Src.NatMap.mem_toList he
    have h1 : ctorOfB D cs c e.decl = true := List.all_eq_true.mp h (c, e) hm
    rw [hd] at h1
    have h2 : decide (D = D → c ∈ cs) = true := h1
    exact of_decide_eq_true h2 rfl

/-- **The result part of the check.** Nothing at `Nat`. At an enumeration: its constructors are
listed in the program, fewer than `2 ^ 63`; every field-less, parameter-less constructor declared
for it is listed; each listed one has no universe parameter, a tag under the root's view, its own
address at that tag in the claim's list, and the reader's key for that address is the key the
grounding check read it under. -/
def resultOkB (p : Program) (I : Lam.Erase.Input) (view : View)
    (key : Ixon.Address → Option KKey) (κ : CId → KKey) : FoTy → Bool
  | .nat => true
  | .enum D =>
    match enumCtors p D with
    | some cs =>
      decide ((enumAddrs p I view cs).length < 2 ^ 63) && ctorsListedB p D cs &&
        cs.all fun c => decide (I.lvls c = 0) &&
          match viewTag I view c with
          | some t => decide ((enumAddrs p I view cs)[t]? = some (p.addr c)) &&
              decide (key (p.addr c) = some (κ c))
          | none => false
    | none => false

/-- The claim's result type for a first-order result. -/
def resOf (p : Program) (I : Lam.Erase.Input) (view : View) : FoTy → ResTy
  | .nat => .nat
  | .enum D =>
    match enumCtors p D with
    | some cs => .enum (enumAddrs p I view cs)
    | none => .enum []

/-- **What the result part establishes** (link G5): the claim's result type is `Nat` at a `Nat`
result; at an enumeration `D` it lists addresses, fewer than `2 ^ 63`, such that every constructor
the program declares for `D` without parameter or field is level-monomorphic, has a tag under the
root's view, and the address at that tag is its own, which the kernel's reader keys as the
grounding check read it. -/
def ResultOk (p : Program) (I : Lam.Erase.Input) (view : View)
    (key : Ixon.Address → Option KKey) (κ : CId → KKey) : FoTy → ResTy → Prop
  | .nat, r => r = ResTy.nat
  | .enum D, r => ∃ addrs : List Ixon.Address, r = ResTy.enum addrs ∧ addrs.length < 2 ^ 63 ∧
      ∀ (c : CId) (s : Bool) (lv i : Nat) (ty : Term),
        p.decl? c = some (.ctor s lv D i 0 0 ty) →
        I.lvls c = 0 ∧ ∃ t, view (obsOf I (.con c [] [] [])) = some (some (.ctor t [])) ∧
          addrs[t]? = some (p.addr c) ∧ key (p.addr c) = some (κ c)

theorem resultOk_sound {p : Program} {I : Lam.Erase.Input} {view : View}
    {key : Ixon.Address → Option KKey} {κ : CId → KKey} :
    ∀ {res : FoTy}, resultOkB p I view key κ res = true →
      ResultOk p I view key κ res (resOf p I view res)
  | .nat, _ => rfl
  | .enum D, h => by
    show ∃ addrs : List Ixon.Address, resOf p I view (FoTy.enum D) = ResTy.enum addrs ∧
      addrs.length < 2 ^ 63 ∧ ∀ (c : CId) (s : Bool) (lv i : Nat) (ty : Term),
        p.decl? c = some (.ctor s lv D i 0 0 ty) →
        I.lvls c = 0 ∧ ∃ t, view (obsOf I (.con c [] [] [])) = some (some (.ctor t [])) ∧
          addrs[t]? = some (p.addr c) ∧ key (p.addr c) = some (κ c)
    have h' : (match enumCtors p D with
      | some cs =>
        decide ((enumAddrs p I view cs).length < 2 ^ 63) && ctorsListedB p D cs &&
          cs.all fun c => decide (I.lvls c = 0) &&
            match viewTag I view c with
            | some t => decide ((enumAddrs p I view cs)[t]? = some (p.addr c)) &&
                decide (key (p.addr c) = some (κ c))
            | none => false
      | none => false) = true := h
    cases hcs : enumCtors p D with
    | none => rw [hcs] at h'; cases h'
    | some cs =>
      rw [hcs] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
      obtain ⟨⟨hlt, hlisted⟩, hall⟩ := h'
      refine ⟨enumAddrs p I view cs, by simp only [resOf, hcs], hlt, ?_⟩
      intro c s lv i ty hdc
      have hc := hall c (ctorsListed_sound hlisted hdc)
      obtain ⟨hl, ht⟩ := hc
      cases htag : viewTag I view c with
      | none => rw [htag] at ht; cases ht
      | some t =>
        rw [htag] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨hl, t, viewTag_some htag, ht.1, ht.2⟩

/-! ## The budget

The checks below walk the kernel's stored terms as trees. A stored value has no `let` (the
kernel stores the ζ-reduct), so a chain of `let`s that each use the last twice is stored as a
term whose tree is exponential in the chain (shared in memory, not in a walk):
`fixtures/fold`'s `mulChain32` drove the unbudgeted check past 300 GB. The check is total either way; the budget makes
it fail closed in bounded time and space. -/

/-- Whether the kernel terms in `todo` hold at most `fuel` nodes, counted as trees (a shared
subterm at each use). A tail call over the worklist. -/
def kWithin : Nat → List KExpr → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, e :: todo =>
    match e with
    | .app f a => kWithin fuel (f :: a :: todo)
    | .lam d b _ | .forallE d b _ => kWithin fuel (d :: b :: todo)
    | .letE t v b _ => kWithin fuel (t :: v :: b :: todo)
    | .proj _ _ e => kWithin fuel (e :: todo)
    | .fvar _ t => kWithin fuel (t :: todo)
    | _ => kWithin fuel todo

/-- The tree nodes the checks may walk: `2 ^ 24`. -/
def kBudget : Nat := 1 <<< 24

/-- The stored terms the checks read at a constant of the closure: its type, its value, its
recursor rules, and the statement of the theorem its table entry cites. -/
def storedTerms (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) : List KExpr :=
  let own := match env.find? (κ c) with
    | some (.defnInfo cv v _) => [cv.type, v]
    | some (.thmInfo cv v) => [cv.type, v]
    | some (.recInfo cv _ _ rules) => cv.type :: rules.map (·.rhs)
    | some ci => [ci.toConstantVal.type]
    | none => []
  let thm := match p.table.resolveOf c with
    | some (.eqn thm _) | some (.csimp _ _ thm) | some (.word _ _ thm) =>
      match env.find? (κ thm) with
      | some ci => [ci.toConstantVal.type]
      | none => []
    | _ => []
  own ++ thm

/-- **The budget**: the stored terms of the closure are within `kBudget` tree nodes. -/
def budgetB (p : Program) (env : KEnv) (κ : CId → KKey) (Sl : List CId) : Bool :=
  kWithin kBudget (Sl.flatMap (storedTerms p env κ))

/-! ## The decision -/

/-- **The pipeline's grounding decision** on root `root` of `src`, at the closure `Sl`, the
retyped environment `env'` and the instance set `Inst` the caller computed. -/
def groundOkB (src : Program) (ann : Src.Relevance.Ann) (I : Lam.Erase.Input) (view : View)
    (key : Ixon.Address → Option KKey) (target addr : Ixon.Address) (root : CId) (res : FoTy)
    (κ : CId → KKey) (lpsOf : CId → List Nat) (Sl : List CId) (env' : KEnv)
    (Inst : List (CId × Levels)) : Bool :=
  rootCheck src env' κ Sl ann root (List.replicate (arityOf src root) FoTy.nat) res &&
  groundCheckWPP src env' κ lpsOf ann Sl &&
  noCanonAB src env' κ Sl &&
  litDefsB env' &&
  instCheckB src env' κ lpsOf [root] Inst &&
  headRegimeSB src env' κ lpsOf ann Sl &&
  decide (addr = target) &&
  decide (key target = some (κ root)) &&
  resultOkB src I view key κ res

theorem groundOkB_sound {src : Program} {ann : Src.Relevance.Ann} {I : Lam.Erase.Input}
    {view : View} {key : Ixon.Address → Option KKey} {target addr : Ixon.Address} {root : CId}
    {res : FoTy} {κ : CId → KKey} {lpsOf : CId → List Nat} {Sl : List CId} {env' : KEnv}
    {Inst : List (CId × Levels)}
    (h : groundOkB src ann I view key target addr root res κ lpsOf Sl env' Inst = true) :
    rootCheck src env' κ Sl ann root (List.replicate (arityOf src root) FoTy.nat) res = true ∧
    groundCheckWPP src env' κ lpsOf ann Sl = true ∧ noCanonAB src env' κ Sl = true ∧
    litDefsB env' = true ∧ instCheckB src env' κ lpsOf [root] Inst = true ∧
    headRegimeSB src env' κ lpsOf ann Sl = true ∧ addr = target ∧
    key target = some (κ root) ∧ resultOkB src I view key κ res = true := by
  simp only [groundOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The first refusal, by name** (diagnostic: evaluated only when `groundOkB` is false). The parts
in the order `groundOkB` decides them; at `root` and `check` the false conjuncts are listed. -/
def groundRefusal (src : Program) (ann : Src.Relevance.Ann) (I : Lam.Erase.Input) (view : View)
    (key : Ixon.Address → Option KKey) (target addr : Ixon.Address) (root : CId) (res : FoTy)
    (κ : CId → KKey) (lpsOf : CId → List Nat) (Sl : List CId) (env' : KEnv)
    (Inst : List (CId × Levels)) (walked : Bool) : String :=
  let args := List.replicate (arityOf src root) FoTy.nat
  let falseOf := fun (ps : List (String × Bool)) => ps.filterMap fun x => if x.2 then none else some x.1
  let parts : List (String × (Unit → Bool) × (Unit → String)) :=
    [("root", fun _ => rootCheck src env' κ Sl ann root args res,
        fun _ => ",".intercalate (falseOf (rootParts src env' κ Sl ann root args res))),
     ("check", fun _ => groundCheckWPP src env' κ lpsOf ann Sl,
        fun _ =>
          let bad := falseOf (checkPartsWP src env' κ lpsOf ann Sl)
          ",".intercalate (if bad.isEmpty then ["punitSort"] else bad)),
     ("noCanon", fun _ => noCanonAB src env' κ Sl, fun _ => ""),
     ("litDefs", fun _ => litDefsB env', fun _ => ""),
     ("instCheck", fun _ => instCheckB src env' κ lpsOf [root] Inst,
        fun _ => if walked then "" else "the instance walk ran out of fuel"),
     ("headRegime", fun _ => headRegimeSB src env' κ lpsOf ann Sl, fun _ => ""),
     ("target", fun _ => decide (addr = target) && decide (key target = some (κ root)),
        fun _ => if addr = target then "the reader's key for the target is not the reading's"
          else "root 0 is not the claimed address"),
     ("result", fun _ => resultOkB src I view key κ res, fun _ => "")]
  match parts.find? fun x => !x.2.1 () with
  | some (name, _, detail) =>
    let d := detail ()
    if d.isEmpty then name else s!"{name}: {d}"
  | none => "none"

/-- The claim's calling convention for a root the check accepts. -/
def abiOf (src : Program) (I : Lam.Erase.Input) (view : View) (root : CId) (res : FoTy) : Abi :=
  { params := List.replicate (arityOf src root) ArgTy.nat, result := resOf src I view res }

/-- **The pipeline's grounding check**: see the module note for what it takes and returns. -/
def groundCheck (k : Src.KernelFront.Kernel) (src : Program) (checked : Src.Relevance.Checked)
    (ann : Src.Relevance.Ann) (view : View) (target : Ixon.Address) : Except String Abi :=
  match src.roots.head? with
  | none => .error "noRoot"
  | some (addr, root) =>
    match resTy src root with
    | none => .error "resultType: the root's declared type does not end in a constant"
    | some res =>
      let κ := keyMap k.rd
      let Sl := closureOf src root
      if budgetB src k.acc.env κ Sl then
        let lpsOf := lpsMap k.acc.env κ
        let env' := selEnv src k.acc.env κ Sl
        let walk := instWalk src [root] instFuel
        let Inst := walk.getD []
        let cx := k.acc.ctx
        let key : Ixon.Address → Option KKey :=
          fun a => (cx.keyAt (Src.KernelFront.kaddr a)).toOption
        let I := Lam.Erase.Input.ofProgram src checked
        if groundOkB src ann I view key target addr root res κ lpsOf Sl env' Inst then
          .ok (abiOf src I view root res)
        else
          .error (groundRefusal src ann I view key target addr root res κ lpsOf Sl env' Inst
            walk.isSome)
      else
        .error "budget: the kernel's stored terms of the root's closure exceed 2^24 tree nodes"

/-! ## What the check establishes -/

/-- **What an accepting `groundCheck` establishes** about the kernel's acceptance `acc`, the
checked source `src`, the root's view and the claimed address: root 0 is at the claimed address
and the kernel's reader keys that address as the grounding check read the root (G2, G3); the
claim's parameters are the root's declared count of `Nat`s; the decided hypotheses of the
grounding root theorem hold on the kernel's environment at the root's first-order type
(`Grounded`, link G); and the claim's result type is the one the view reports (`ResultOk`, G5). -/
def GroundOk (acc : Src.KernelFront.Accepted) (src : Program) (I : Lam.Erase.Input) (view : View)
    (target : Ixon.Address) (abi : Abi) : Prop :=
  ∃ (κ : CId → KKey) (lpsOf : CId → List Nat) (ann : Src.Relevance.Ann) (Sl : List CId)
      (Inst : List (CId × Levels)) (root : CId) (res : FoTy),
    src.roots.head? = some (target, root) ∧
    resTy src root = some res ∧
    keyOf acc target = some (κ root) ∧
    abi.params = List.replicate (arityOf src root) ArgTy.nat ∧
    Grounded src acc.env κ lpsOf ann Sl Inst root
      (List.replicate (arityOf src root) FoTy.nat) res ∧
    ResultOk src I view (keyOf acc) κ res abi.result

/-- **The check is sound**: an accepting `groundCheck` gives the hypotheses of the composed
theorems. -/
theorem groundCheck_sound {k : Src.KernelFront.Kernel} {src : Program}
    {checked : Src.Relevance.Checked} {ann : Src.Relevance.Ann} {view : View}
    {target : Ixon.Address} {abi : Abi}
    (h : groundCheck k src checked ann view target = .ok abi) :
    GroundOk k.acc src (Lam.Erase.Input.ofProgram src checked) view target abi := by
  unfold groundCheck at h
  unfold GroundOk
  cases hr : src.roots.head? with
  | none => rw [hr] at h; cases h
  | some ar =>
    obtain ⟨addr, root⟩ := ar
    rw [hr] at h
    dsimp only at h
    cases hres : resTy src root with
    | none => rw [hres] at h; cases h
    | some res =>
      rw [hres] at h
      dsimp only at h
      split at h
      · split at h
        · rename_i hbud hok
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := groundOkB_sound hok
          simp only [Except.ok.injEq] at h
          subst h
          subst h7
          exact ⟨keyMap k.rd, lpsMap k.acc.env (keyMap k.rd), ann, closureOf src root,
            (instWalk src [root] instFuel).getD [], root, res, rfl, hres, h8, rfl,
            ⟨h2, h3, h4, h5, h6, rootFacts_of_check h1⟩, resultOk_sound h9⟩
        · cases h
      · cases h

end IxCC.Correct
