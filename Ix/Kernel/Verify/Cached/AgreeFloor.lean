/-
Ported from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526.
Source: ConLeche/Verify/Cached/AgreeFloor.lean
Transformations: Lean 4.34.0 fix, the line `import all Init.LetFun` added
after `import ConLeche.Verify.EnvBound` (4.34.0 moved `letFun` to
`Init.LetFun` without exposing its body, which `Yields.letFun` and the
join-point walkers unfold); then the vendoring rewrite of `scripts/vendor-conleche.py` (paths and
namespace `ConLeche` → `Ix.Kernel`, without its comment line) is applied; this header added.
No statement, proof or tactic text changes.
-/
module

public import Ix.Kernel.Cached.Installed
import Ix.Kernel.Verify.EnvBound
import all Init.LetFun

public section

/-!
# The trusted↔P agreement floor (task #172, batch B7; restated at the
twin's retirement, 2026-09-06)

The *cheap floor* of census part 4 §3: whenever the cached driver
(`Ix/Kernel/Cached/ParsedC.lean`) at the trusted config and at the
verified config both **accept** a stream, the two installed
environments carry the same constants, in the same order, with the same
install skeletons — and in particular the same names and the same
count.

**What the retirement did to the statement.**  Until 2026-09-06 the
trusted lane was a separate driver (`checkDeclsT`,
`Ix/Kernel/Cached/ParsedT.lean`) over a hand-written cert-skipping core,
and the floor had to prove the skeleton spec for *both* drivers, stage
by stage — the second half of this file was a clause-by-clause
duplicate of the first.  Now there is one driver, `checkDecls
mode`, and the floor is the skeleton spec proved **once, for every
`mode : CheckMode`** (`checkDecls_skels`); the agreement of
two modes is its two instances glued by `Eq.trans`.  That is strictly
stronger than the frozen B7 statement: the old theorem is the new one
at `μP := .verified`, `μT := .trusted`, and the new one covers any two
modes (task #185: "any two configs" until the configuration record
retired).  The certification-only work the trusted mode omits
(`mode.verifiedChecks`, group A, and `mode.certs`) is invisible to the
skeleton by construction — the spec forgets everything a core computes
— which is exactly why the proof is mode-generic without a case
split.

Nothing here reasons about the cores.  The floor's whole content is
that the fold is *the same fold* at every config, and the only work is
that this is not quite true on the nose: the inductive-block clause
installs constants under **environment-dependent guards**
(`installProjFnStep*`'s model lookup).  So the induction runs on
the *install skeleton* — exactly the data those guards read, and
nothing a core computes — and the names corollary falls out.

Two facts close the remaining branches without core reasoning:

* the direct simple-structure clause (task #175 W4c, the priority
  route) installs under guards that are the block's own (the
  projection bodies' scoping, task #175 S1) or freshness checks, and
  its dispatch
  (`structPartsF?`) reads the index only through name lookups
  (`structNonRecF_skel`), so it runs on the skeleton too;
* at `.axiomDecl` the push-or-not decision is a function of the header
  name alone — the `sorryAx` record installs nothing in
  both drivers, and `stdAxiomOkF` is `false` off `propext`/`choice`, so
  every other accepted axiom installs exactly one `.axiomInfo`.

See DESIGN.md, "TASK #172 — BATCH B7: THE AGREEMENT FLOOR — STATEMENT
FREEZE" for the frozen statements and the scope (accept verdicts only;
T2c untouched).
-/

namespace Ix.Kernel.Cached

open Ix.Kernel

variable {pins : List NatOpPinSet}

/-! ## The kit: final-value reasoning for `CheckCM`

`CheckCM = StateT CState (Except CheckError)`.  The floor reads only
the *returned* environment, never the state, so the whole monadic
discipline it needs is: "`P` holds of every value this action can
return".  The bind rule then carries **no** hypothesis on the bound
action — which is what makes the long `do` blocks of the drivers
collapse to their final `pure`. -/

/-- `P` holds of every value the action can return. -/
@[expose] def Yields {α : Type} (m : CheckCM α) (P : α → Prop) : Prop :=
  ∀ s a s', m s = .ok (a, s') → P a

theorem Yields.mono {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (h : Yields m P) (hPQ : ∀ a, P a → Q a) : Yields m Q :=
  fun s a s' hr => hPQ a (h s a s' hr)

theorem Yields.pure {α : Type} {a : α} {P : α → Prop} (h : P a) :
    Yields (Pure.pure (f := CheckCM) a) P := by
  intro s b s' hr
  simp only [Pure.pure, StateT.pure, Except.pure] at hr
  cases hr; exact h

theorem Yields.ofThrow {α : Type} {e : CheckError} {P : α → Prop} :
    Yields (throw e : CheckCM α) P := by
  intro s a s' hr; cases hr

/-- The bind rule that carries **no** hypothesis on the bound action:
the property is about the returned value only, so the long guard
chains of the drivers collapse to their final `pure`. -/
theorem Yields.bind {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {P : β → Prop} (h : ∀ a, Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm : m s with
  | error e => rw [hs, hm] at hr; cases hr
  | ok v =>
    rw [hs, hm] at hr
    exact h v.1 v.2 b s' hr

/-- The bind rule that *uses* the bound action's own rule. -/
theorem Yields.bind' {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {Q : α → Prop} {P : β → Prop} (hm : Yields m Q)
    (h : ∀ a, Q a → Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm' : m s with
  | error e => rw [hs, hm'] at hr; cases hr
  | ok v =>
    rw [hs, hm'] at hr
    exact h v.1 (hm s v.1 v.2 hm') v.2 b s' hr

/-- Do-notation elaborates its guards through *join points*
(`have __do_jp := …`), so the clause walker needs the `letFun` rule to
step past them. -/
theorem Yields.letFun {α β : Type} {v : β} {f : β → CheckCM α}
    {P : α → Prop} (h : Yields (f v) P) : Yields (letFun v f) P := h

/-- A guard's failure branch, closed without descending into the join
point it calls (which is what keeps the walk linear). -/
theorem Yields.ofThrowBind {α β : Type} {e : CheckError} {f : α → CheckCM β}
    {P : β → Prop} : Yields ((throw e : CheckCM α) >>= f) P := by
  intro s b s' hr; cases hr

/-- A `Decidable` case analysis left behind when a guard's `ite` has
already been delta-expanded (`split` normalises it that way). -/
theorem Yields.ofDecRec {α : Type} {c : Prop} {d : Decidable c}
    {a : ¬c → CheckCM α} {b : c → CheckCM α} {P : α → Prop}
    (ha : ∀ h, Yields (a h) P) (hb : ∀ h, Yields (b h) P) :
    Yields (Decidable.rec (motive := fun _ => CheckCM α) a b d) P := by
  cases d with
  | isFalse h => exact ha h
  | isTrue h => exact hb h

theorem Yields.ofDecCases {α : Type} {c : Prop} {d : Decidable c}
    {a : ¬c → CheckCM α} {b : c → CheckCM α} {P : α → Prop}
    (ha : ∀ h, Yields (a h) P) (hb : ∀ h, Yields (b h) P) :
    Yields (Decidable.casesOn (motive := fun _ => CheckCM α) d a b) P := by
  cases d with
  | isFalse h => exact ha h
  | isTrue h => exact hb h

/-- The clause walker: step past join points and guards to the `pure`
leaves of a driver clause.

**Every `apply` runs `with_reducible`.**  At default transparency the
rules unify *vacuously* — `Bind.bind ?m ?f`, `letFun ?v ?f` and
`pure ?a` all unfold far enough to match an arbitrary action, which
makes the walk loop instead of descending.  At reducible transparency
each rule matches exactly its own head, so the walk is deterministic
and linear in the clause. -/
syntax "yields_step" : tactic
macro_rules
  | `(tactic| yields_step) => `(tactic|
      first
        | with_reducible exact Yields.ofThrowBind
        | ((with_reducible apply Yields.bind); intro)
        | with_reducible apply Yields.letFun
        | with_reducible exact Yields.ofThrow
        | ((with_reducible apply Yields.ofDecRec) <;> intro)
        | ((with_reducible apply Yields.ofDecCases) <;> intro)
        | split)

syntax "yields" : tactic
macro_rules
  | `(tactic| yields) =>
      `(tactic| all_goals (first | (yields_step; yields) | skip))

/-- One join-point step (`with_reducible`, as above). -/
syntax "ylet" : tactic
macro_rules
  | `(tactic| ylet) => `(tactic| with_reducible apply Yields.letFun)

/-- One uninformative bind step (`with_reducible`, as above). -/
syntax "ybind" : tactic
macro_rules
  | `(tactic| ybind) => `(tactic| (with_reducible apply Yields.bind); intro)

/-- The fold rule, with an abstraction `R` of the accumulator: if each
step takes `R b c` to `R b' (g c a)`, the fold takes it to
`R b' (l.foldl g c)`.  This is the shape both drivers' folds have —
the *specification* accumulator `c` is a pure function of the stream,
which is exactly how the two drivers are compared. -/
theorem Yields.foldlM_rel {α β γ : Type} {R : β → γ → Prop}
    {f : β → α → CheckCM β} {g : γ → α → γ}
    (hf : ∀ b a c, R b c → Yields (f b a) (fun b' => R b' (g c a))) :
    ∀ (l : List α) (b : β) (c : γ), R b c →
      Yields (l.foldlM f b) (fun b' => R b' (l.foldl g c))
  | [], b, c, h => by
      simp only [List.foldlM_nil, List.foldl_nil]
      exact Yields.pure h
  | a :: l, b, c, h => by
      simp only [List.foldlM_cons, List.foldl_cons]
      exact Yields.bind' (hf b a c h) fun b' hb' =>
        Yields.foldlM_rel hf l b' (g c a) hb'

/-! ## The install skeleton

Exactly the data of an installed constant that the *drivers'* install
guards read.  Everything a core computes — the annotated type, the
annotated value, `IndCaps`, a rule's right-hand side and its
`plain`/`inert` fire tag — is deliberately **forgotten**: those are the
class-1/2/3 divergent data, and forgetting them is what keeps the floor
free of core reasoning. -/

/-- The install skeleton of a constant. -/
inductive InstallSkel where
  | ax   (n : Name)
  | defn (n : Name)
  | thm  (n : Name)
  | ind  (n : Name)
  | ctor (n : Name) (numParams numFields : Nat)
  | recr (n : Name) (majorIdx rulePrefix : Nat) (ctors : List Name)
  | proj (n : Name)
  deriving DecidableEq, Repr, Inhabited

/-- The declared name of a skeleton. -/
def skelName : InstallSkel → Name
  | .ax n | .defn n | .thm n | .ind n => n
  | .ctor n _ _ | .recr n _ _ _ | .proj n => n

/-- The skeleton of an installed constant. -/
def ciSkel : ConstantInfo → InstallSkel
  | .axiomInfo cv => .ax cv.name
  | .defnInfo cv _ _ => .defn cv.name
  | .thmInfo cv _ => .thm cv.name
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | .recInfo cv mI rP rules => .recr cv.name mI rP (rules.map (·.ctor))
  | .projInfo tbl => .proj (projTableName tbl.structName)

@[simp] theorem skelName_ciSkel (ci : ConstantInfo) :
    skelName (ciSkel ci) = ci.name := by
  cases ci <;> rfl

/-- The skeleton list of an environment (newest first, as `consts`). -/
def envSkels (env : Env) : List InstallSkel := env.consts.map ciSkel

/-- Lookup at the skeleton level. -/
def skFind? (sk : List InstallSkel) (n : Name) : Option InstallSkel :=
  sk.find? (fun s => skelName s == n)

theorem skFind?_map (l : List ConstantInfo) (n : Name) :
    (l.find? (fun c => c.name == n)).map ciSkel = skFind? (l.map ciSkel) n := by
  simp only [skFind?, List.find?_map, Function.comp_def, skelName_ciSkel]

/-! ## The canonical index

Both drivers thread the index by `FEnv.push` from `mkFEnv Env.empty`,
so it is always `mkFEnv` of an environment — and then `FEnv.find?`
*is* `Env.find?` (`mkFEnv_find?`), which is what turns the drivers'
index guards into skeleton-level guards. -/

/-- The index is `mkFEnv` of an environment. -/
def Canon (fe : FEnv) : Prop := ∃ env, fe = mkFEnv env

theorem canon_push {fe : FEnv} (h : Canon fe) (ci : ConstantInfo) :
    Canon (fe.push ci) := by
  obtain ⟨env, rfl⟩ := h
  exact ⟨⟨ci :: env.consts⟩, rfl⟩

theorem canon_find? {fe : FEnv} (h : Canon fe) (n : Name) :
    fe.find? n = fe.env.find? n := by
  obtain ⟨env, rfl⟩ := h
  exact mkFEnv_find? env n

theorem canon_empty : Canon (mkFEnv Env.empty) := ⟨_, rfl⟩

/-- The floor's induction hypothesis: a canonical index whose
environment has the given skeleton list. -/
def SkelIs (fe : FEnv) (sk : List InstallSkel) : Prop :=
  Canon fe ∧ envSkels fe.env = sk

theorem SkelIs.find? {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (fe.find? n).map ciSkel = skFind? sk n := by
  rw [canon_find? h.1 n, ← h.2]
  exact skFind?_map _ n

theorem SkelIs.push {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) : SkelIs (fe.push ci) (ciSkel ci :: sk) :=
  ⟨canon_push h.1 ci, by
    show (ci :: fe.env.consts).map ciSkel = _
    rw [List.map_cons]
    exact congrArg (ciSkel ci :: ·) h.2⟩

/-- Skeleton inversion at a recursor (the one place a driver guard
reads more than a name). -/
theorem recr_of_ciSkel {ci : ConstantInfo} {n : Name} {mI rP : Nat}
    {cs : List Name} (h : ciSkel ci = .recr n mI rP cs) :
    ∃ cv rules, ci = .recInfo cv mI rP rules ∧ cv.name = n ∧
      rules.map (·.ctor) = cs := by
  cases ci <;> simp only [ciSkel] at h <;> cases h <;>
    exact ⟨_, _, rfl, rfl, rfl⟩

/-! ## The specification fold

One pure function per driver clause, computing the skeletons the clause
installs from the declaration and the skeletons already installed.  It
is **total**: on inputs the drivers reject it is junk, and `Yields`
makes junk vacuous. -/

/-- The skeleton `checkIndMemberS`/`checkIndMemberT` installs (junk off
the two accepted member kinds — that branch throws). -/
def indMemberSkel : ConstantInfo → InstallSkel
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | ci => .ax ci.name

/-- The skeleton the recursor group installs for one member (junk off
`.recInfo` — `provisionRecs*` throws there). -/
def recMemberSkel : ConstantInfo → InstallSkel
  | .recInfo cv mI rP rules => .recr cv.name mI rP (rules.map (·.ctor))
  | ci => .ax ci.name

/-- The member fold's specification step. -/
def indMemberSkels (sk : List InstallSkel) (ci : ConstantInfo) :
    List InstallSkel := indMemberSkel ci :: sk

/-- The recursor group's specification step. -/
def recMemberSkels (sk : List InstallSkel) (ci : ConstantInfo) :
    List InstallSkel := recMemberSkel ci :: sk

/-- `installProjFnStep*`'s specification: the model lookup decides. -/
def projFnStepSkels (T ctorName : Name) (nP : Nat)
    (sk : List InstallSkel) (i : Nat) : List InstallSkel :=
  if (skFind? sk (projModelName T i)).isSome then
    .recr (projFnName T i) nP nP [ctorName] :: sk
  else sk

/-! The block's member classifiers.  They are *named* (rather than
inlined `match` lambdas as in the driver) for one reason: the driver's
own lambdas compile to per-declaration matcher constants, so a rewrite
with the block-shape equation `split` hands back needs a rigid head to
aim at.  Each is definitionally the driver's lambda, so the bridge is
`exact`. -/

/-- The inductive-type-former members of a block. -/
def isIndCI : ConstantInfo → Bool
  | .indInfo _ _ => true
  | _ => false

/-- The constructor members of a block. -/
def isCtorCI : ConstantInfo → Bool
  | .ctorInfo _ _ _ => true
  | _ => false

/-- The recursor members of a block. -/
def isRecCI : ConstantInfo → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- The non-recursor members of a block. -/
def isNonRecCI : ConstantInfo → Bool
  | .recInfo _ _ _ _ => false
  | _ => true

/-- The modeled inductive-block clause's specification. -/
def indDeclSkelsModeled (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  let base := (block.filter isRecCI).foldl recMemberSkels
    ((block.filter isNonRecCI).foldl indMemberSkels sk)
  match block.filter isIndCI, block.filter isCtorCI with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      (List.range nF).foldl (projFnStepSkels cvT.name cvC.name nP) base
    else base
  | _, _ => base

/-! ### The direct simple-structure clause (task #175 W4c)

The priority gate `structPartsF?` reads the block (`structPartsCore?`,
pure) and the index only through `constsResolveF` on the raw
constructor domains — skeleton-level lookups — so the dispatch is a
function of the skeleton; the direct install's own install decisions
are the projection bodies' scoping (`structProjBodies`, a function of
the annotated constructor type; task #175 S1) plus freshness checks.
Nothing a core computes enters. -/

/-- `Expr.constsResolve` at the skeleton level (lookups through
`skFind?`). -/
def constsResolveSk (sk : List InstallSkel) : Expr → Bool
  | .bvar _ => true
  | .sort _ => true
  | .lit (.natVal _) =>
    (skFind? sk natName).isSome && (skFind? sk natZeroName).isSome &&
      (skFind? sk natSuccName).isSome
  | .lit (.strVal _) =>
    (skFind? sk natName).isSome && (skFind? sk natZeroName).isSome &&
      (skFind? sk natSuccName).isSome && (skFind? sk stringName).isSome &&
      (skFind? sk stringOfListName).isSome && (skFind? sk listName).isSome &&
      (skFind? sk listNilName).isSome && (skFind? sk listConsName).isSome &&
      (skFind? sk charName).isSome && (skFind? sk charOfNatName).isSome
  | .const n _ => (skFind? sk n).isSome
  | .fvar _ ty => constsResolveSk sk ty
  | .app f a => constsResolveSk sk f && constsResolveSk sk a
  | .lam ty body _ => constsResolveSk sk ty && constsResolveSk sk body
  | .forallE ty body _ => constsResolveSk sk ty && constsResolveSk sk body
  | .letE ty val body =>
    constsResolveSk sk ty && constsResolveSk sk val && constsResolveSk sk body
  | .proj s _ e => (skFind? sk s).isSome && constsResolveSk sk e

theorem SkelIs.isSome' {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (fe.find? n).isSome = (skFind? sk n).isSome := by
  rw [← h.find? n, Option.isSome_map]

theorem constsResolveF_skel {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) : ∀ e : Expr, Expr.constsResolveF fe e = constsResolveSk sk e := by
  intro e
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | lit l =>
    cases l <;> simp only [Expr.constsResolveF, constsResolveSk, h.isSome']
  | const n us => simp only [Expr.constsResolveF, constsResolveSk, h.isSome']
  | fvar _ ty ih => simp only [Expr.constsResolveF, constsResolveSk, ih]
  | app f a ihf iha =>
    simp only [Expr.constsResolveF, constsResolveSk, ihf, iha]
  | lam ty b _ ihty ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, ihty, ihb]
  | forallE ty b _ ihty ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, ihty, ihb]
  | letE t v b iht ihv ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, iht, ihv, ihb]
  | proj s _ e ihe =>
    simp only [Expr.constsResolveF, constsResolveSk, h.isSome', ihe]

/-! ### The direct sum clause (task #175 sum-types)

The second gate reads the index exactly as the first does — `constsResolveF`
on the raw constructor domains — and its install decisions are the block's
own; only the *number* of constants it pushes varies with the block (one
per constructor). -/

/-- The constructors' conses at the skeleton level (the first
constructor deepest, as `consSumCtors`). -/
def sumCtorSkels (nP : Nat) (cs : List (Name × Nat)) (sk : List InstallSkel) :
    List InstallSkel :=
  cs.foldl (fun acc c => .ctor c.1 nP c.2 :: acc) sk

/-- The direct sum install's skeleton: the former, every constructor in
declaration order, then the generated recursor with one rule per
constructor. -/
def sumSkels (p : InductiveShape) (sk : List InstallSkel) :
    List InstallSkel :=
  .recr p.cvR.name p.majorIdx p.rulePrefix (p.ctors.map (·.1.name)) ::
    sumCtorSkels p.nP (p.ctors.map fun c => (c.1.name, c.2))
      (.ind p.cvT.name :: sk)

/-- The fixpoint route's skeleton (task #210 Part A): the sum's, with
the projection table on top at a structure-like block (one
constructor, no index). -/
def nativeSkels (p : NativeParts) (sk : List InstallSkel) : List InstallSkel :=
  if p.ctors.length == 1 && p.nIdx == 0 then
    .proj (projTableName p.cvT.name) :: sumSkels p.toInductiveShape sk
  else sumSkels p.toInductiveShape sk

/-- The dispatch below the direct-sum gate: the direct recursive gate
(task #188; the sum's skeleton with the table at a structure-like
block), then the modeled block.  The RECOGNISER decides, and nothing
else (task #219), so the skeleton list needs no environment at all. -/
def indDeclSkels (nP : Nat) (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  match nativeParts? nP block with
  | some p => nativeSkels p sk
  | none => indDeclSkelsModeled block sk

/-- The skeletons one declaration installs. -/
def declCSkels : Declaration → List InstallSkel → List InstallSkel
  | .defnDecl cv _ _, sk => .defn cv.name :: sk
  | .thmDecl cv _, sk => .thm cv.name :: sk
  | .opaqueDecl cv _, sk => .ax cv.name :: sk
  | .axiomDecl cv, sk =>
    -- task #293: `Quot.sound` is the pinned quotient block's own
    -- record and installs nothing of its own, like `sorryAx`
    if cv.name = sorryAxName ∨ cv.name = quotSoundName then sk
    else .ax cv.name :: sk
  | .basisDecl kind, sk =>
    kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
  -- task #293: the quotient package's `type` record installs the
  -- pinned block; its other records are members of that block
  | .quotDecl k _, sk =>
    match k with
    | .type => BasisKind.quotK.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | _ => sk
  | .indDecl block nP, sk =>
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin
    match basisPinHit block with
    | some kind => kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | none => indDeclSkels nP block sk

/-! ## The shared install stages

`checkConstantValF`, `checkMemberValF`, `checkIotaRule(s)F` and
`installBasisDeclF` are the *generic* stages both drivers call (they
take the engine as a `CheckerOps` record).  Their skeleton facts are
proved once. -/

theorem checkConstantValF_name (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv) (fun cvA => cvA.name = cv.name) := by
  unfold checkConstantValF
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkMemberValF_name (ops : CheckerOps CheckCM)
    (blockNames : List Name) (fe : FEnv) (cv : ConstantVal) :
    Yields (checkMemberValF ops blockNames fe cv)
      (fun cvA => cvA.name = cv.name) := by
  unfold checkMemberValF
  refine Yields.bind' (checkConstantValF_name ops fe cv) fun cvA hcvA => ?_
  yields
  all_goals (apply Yields.pure; exact hcvA)

theorem checkIotaRuleF_ctor (mode : CheckMode) (ops : CheckerOps CheckCM)
    (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) :
    Yields (checkIotaRuleF mode ops fe' feSelf f cvName lps tyA mI rP j r)
      (fun r' => r'.ctor = r.ctor) := by
  unfold checkIotaRuleF
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkIotaRulesF_ctors (mode : CheckMode) (ops : CheckerOps CheckCM)
    (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      Yields (checkIotaRulesF mode ops fe' feSelf f cvName lps tyA mI rP j rules)
        (fun rules' => rules'.map (·.ctor) = rules.map (·.ctor))
  | _, [] => by
      unfold checkIotaRulesF
      exact Yields.pure rfl
  | j, r :: rest => by
      unfold checkIotaRulesF
      refine Yields.bind'
        (checkIotaRuleF_ctor mode ops fe' feSelf f cvName lps tyA mI rP j r)
        fun r' hr' => ?_
      refine Yields.bind'
        (checkIotaRulesF_ctors mode ops fe' feSelf f cvName lps tyA mI rP
          (j + 1) rest) fun rest' hrest' => ?_
      apply Yields.pure
      simp [hr', hrest']

theorem installBasisDeclF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => SkelIs fe' (ciSkel ci :: sk)) := by
  unfold installBasisDeclF
  yields
  all_goals (apply Yields.pure; exact h.push ci)

theorem SkelIs.isNone {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (skFind? sk n).isNone = (fe.find? n).isNone := by
  rw [← h.find? n]; cases fe.find? n <;> rfl

theorem SkelIs.isSome {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (skFind? sk n).isSome = (fe.find? n).isSome := by
  rw [← h.find? n]; cases fe.find? n <;> rfl

/-! ## The cached certified driver's install stages -/

theorem checkConstantValC_name (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValC mode fe cv) (fun p => p.1.name = cv.name) := by
  unfold checkConstantValC
  yields
  all_goals (apply Yields.pure; rfl)

theorem annotConstantValC_fresh (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (annotConstantValC mode fe cv)
      (fun p => p.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold annotConstantValC
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

theorem annotValueC_fresh (mode : CheckMode) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (record : Bool) :
    Yields (annotValueC mode fe cv value record)
      (fun r => r.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold annotValueC
  ybind
  refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hp => ?_
  obtain ⟨cvA, jty⟩ := p
  ybind
  exact Yields.pure hp

theorem checkDefnValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) (hint : ReducibilityHint) :
    Yields (checkDefnValC mode fe cvA jty value hint)
      (fun fe' => SkelIs fe' (.defn cvA.name :: sk)) := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkThmValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) :
    Yields (checkThmValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.thm cvA.name :: sk)) := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkOpaqueValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) :
    Yields (checkOpaqueValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.ax cvA.name :: sk)) := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkIndMemberS_skels (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) :
    Yields (checkIndMemberS mode blockNames caps fe ci)
      (fun fe' => SkelIs fe' (indMemberSkel ci :: sk)) := by
  unfold checkIndMemberS
  ybind
  refine Yields.bind'
    (checkMemberValF_name (sharedOpsC mode fe) blockNames fe ci.toConstantVal)
    fun cvA hcvA => ?_
  cases ci with
  | indInfo cvI capsI =>
    refine Yields.pure ?_
    have := h.push (.indInfo cvA caps)
    simpa [ciSkel, indMemberSkel, hcvA, ConstantInfo.toConstantVal] using this
  | ctorInfo cvI nP nF =>
    refine Yields.pure ?_
    have := h.push (.ctorInfo cvA nP nF)
    simpa [ciSkel, indMemberSkel, hcvA, ConstantInfo.toConstantVal] using this
  | _ => exact Yields.ofThrow

/-- The skeleton a provisioned recursor triple installs. -/
def provSkel (c : ConstantVal × Nat × Nat × List RecRule) : InstallSkel :=
  .recr c.1.name c.2.1 c.2.2.1 (c.2.2.2.map (·.ctor))

theorem provisionRecsS_spec (mode : CheckMode) (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) (feAcc : FEnv),
      Yields (provisionRecsS mode blockNames feAcc recs)
        (fun p => p.2.map provSkel = recs.map recMemberSkel) := by
  intro recs
  induction recs with
  | nil => intro feAcc; unfold provisionRecsS; exact Yields.pure rfl
  | cons ci rest ih =>
    intro feAcc
    unfold provisionRecsS
    cases ci with
    | recInfo cv mI rP rules =>
      ybind
      refine Yields.bind'
        (checkMemberValF_name (sharedOpsC mode feAcc) blockNames feAcc _)
        fun cvA hcvA => ?_
      refine Yields.bind' (ih _) fun q hq => ?_
      obtain ⟨feSelf, others⟩ := q
      refine Yields.pure ?_
      simp only [List.map_cons, provSkel, recMemberSkel, hcvA,
        ConstantInfo.toConstantVal] at hq ⊢
      rw [hq]
    | _ => exact Yields.ofThrow

theorem foldl_cons_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (b : List β),
      l.foldl (fun acc x => f x :: acc) b = (l.map f).reverse ++ b
  | [], b => rfl
  | a :: l, b => by
      simp [foldl_cons_map f l]

theorem foldl_recMemberSkels (recs : List ConstantInfo)
    (sk : List InstallSkel) :
    recs.foldl recMemberSkels sk = (recs.map recMemberSkel).reverse ++ sk :=
  foldl_cons_map recMemberSkel recs sk

theorem foldl_indMemberSkels (nonrecs : List ConstantInfo)
    (sk : List InstallSkel) :
    nonrecs.foldl indMemberSkels sk = (nonrecs.map indMemberSkel).reverse ++ sk :=
  foldl_cons_map indMemberSkel nonrecs sk

theorem checkIndRecsS_skels (mode : CheckMode) (blockNames : List Name)
    {fe₂ : FEnv} {sk : List InstallSkel} (h : SkelIs fe₂ sk)
    (recs : List ConstantInfo) :
    Yields (checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => SkelIs fe' (recs.foldl recMemberSkels sk)) := by
  unfold checkIndRecsS
  simp only []
  split
  · rename_i hemp
    have hr : recs = [] := by cases recs <;> simp_all
    subst hr
    exact Yields.pure h
  · split
    · refine Yields.bind'
        (provisionRecsS_spec mode blockNames recs fe₂) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      have hstep : ∀ (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule)
          (sk' : List InstallSkel), SkelIs acc sk' →
          Yields (do
            let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
              (fun n => if blockNames.contains n then n.str "_model" else n)
              c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
            pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
            (fun acc' => SkelIs acc' (provSkel c :: sk')) := by
        intro acc c sk' hacc
        refine Yields.bind'
          (checkIotaRulesF_ctors mode (sharedOpsC mode feSelf) fe₂ feSelf _
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2)
          fun rules' hrules' => ?_
        refine Yields.pure ?_
        simpa [ciSkel, provSkel, hrules'] using hacc.push
          (.recInfo c.1 c.2.1 c.2.2.1 rules')
      refine Yields.mono
        (Yields.foldlM_rel (R := SkelIs) hstep checked fe₂ sk h)
        fun fe' hfe' => ?_
      rw [foldl_recMemberSkels]
      simp only [foldl_cons_map] at hfe' 
      simp only [show checked.map provSkel = recs.map recMemberSkel from hq] at hfe'
      exact hfe'
    · exact Yields.ofThrowBind

theorem checkProjFnS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjFnS mode fe T ctorName lps nP nF i)
      (fun fe' => SkelIs fe' (.recr (projFnName T i) nP nP [ctorName] :: sk)) := by
  unfold checkProjFnS
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem installProjFnStepS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (installProjFnStepS mode T ctorName lps nP nF fe i)
      (fun fe' => SkelIs fe' (projFnStepSkels T ctorName nP sk i)) := by
  unfold installProjFnStepS projFnStepSkels
  rw [h.isSome (projModelName T i)]
  split <;> rename_i hb
  · ybind
    exact checkProjFnS_skels mode h T ctorName lps nP nF i
  · exact Yields.pure h

/-! ## The direct simple-structure install's skeleton (task #175 W4c)

Every stage's install decision is the block's own or a freshness
check; the stored constants' names are the block's (`checkConstantValF`
keeps the name). -/

theorem checkStructProjTableF_skels {w : StructWalkers} {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa fe)
      (fun fe' => SkelIs fe' (.proj (projTableName T) :: sk)) := by
  unfold checkStructProjTableF
  yields
  all_goals (refine Yields.pure ?_; exact h.push _)

/-- The members-then-recursors phase, shared by both arms of
`checkIndDeclSF`'s block match. -/
theorem indBase_skels (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
        checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => SkelIs fe'
        (recs.foldl recMemberSkels (nonrecs.foldl indMemberSkels sk))) := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
      (fun acc ci sk' hacc => checkIndMemberS_skels mode blockNames caps hacc ci)
      nonrecs fe sk h) fun fe₂ h₂ => ?_
  exact checkIndRecsS_skels mode blockNames h₂ recs

theorem checkIndDeclSF_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (block : List ConstantInfo) :
    Yields (checkIndDeclSF mode fe block)
      (fun fe' => SkelIs fe' (indDeclSkelsModeled block sk)) := by
  unfold checkIndDeclSF indDeclSkelsModeled
  simp only []
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
    split
    case h_1 cvT capsT cvC nP nF hI hC =>
      have hI' : block.filter isIndCI = [ConstantInfo.indInfo cvT capsT] := hI
      have hC' : block.filter isCtorCI = [ConstantInfo.ctorInfo cvC nP nF] := hC
      rw [hI', hC']
      simp only []
      ybind
      refine Yields.bind'
        (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
          (fun acc ci sk' hacc =>
            checkIndMemberS_skels mode _ _ hacc ci) _ fe sk h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsS_skels mode _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          -- the projection phase runs on structure-like blocks only
          -- (task #175 SigmaHom): a decision of the block's own
          -- constructor type, so the skeleton spec computes it
          by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams
              nP nF = true
          · simp only [if_pos hsl]
            exact Yields.foldlM_rel (R := SkelIs)
              (g := projFnStepSkels cvT.name cvC.name nP)
              (fun acc i sk' hacc =>
                installProjFnStepS_skels mode hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ _ h₃
          · simp only [if_neg hsl]
            exact Yields.pure (P := fun fe' => SkelIs fe' _) h₃
    case h_2 hne =>
      split
      case h_1 cvT capsT cvC nP nF hI hC =>
        exact absurd hC (hne cvT capsT cvC nP nF hI)
      case h_2 => exact indBase_skels mode _ _ h _ _

/-! ## The direct sum install's skeleton (task #175 sum-types, indexed)

Same shape as the structure route's, with the constructor stage run
over a list: the stored constructors' names and field counts are the
block's (`checkConstantValF` keeps the name, the stage keeps the
count), and the generated recursor's rules are one per constructor, so
the rule-name list the skeleton records is the block's own. -/

/-- The former's telescope stage keeps the block's name (task #195):
the checked constant is the input or a re-check at the block's own
header. -/
theorem checkSumTeleF_name (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    Yields (checkSumTeleF ops fe cv n cvTa₀)
      (fun r => r.1.name = cvTa₀.name ∨ r.1.name = cv.name) := by
  unfold checkSumTeleF
  split
  · exact Yields.pure (Or.inl rfl)
  · ybind
    refine Yields.bind' (checkConstantValF_name ops fe _) fun cvTa hn => ?_
    exact Yields.pure (Or.inr hn)

theorem checkSumIndF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ops : CheckerOps CheckCM) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) :
    Yields (checkSumIndF ops fe p capsOf)
      (fun r => SkelIs r.1 (.ind p.cvT.name :: sk) ∧ ∃ s, r.2.2 = p.withSort s) := by
  unfold checkSumIndF
  refine Yields.bind' (checkConstantValF_name ops fe p.cvT) fun cvTa₀ hn₀ => ?_
  refine Yields.bind' (checkSumTeleF_name ops fe p.cvT _ cvTa₀) fun r hn => ?_
  obtain ⟨cvTa, s⟩ := r
  have hn' : cvTa.name = p.cvT.name := by
    rcases hn with h1 | h1
    · exact h1.trans hn₀
    · exact h1
  yields
  all_goals
    (refine Yields.pure ⟨?_, s, rfl⟩
     have := h.push (.indInfo cvTa (capsOf (p.withSort s)))
     simpa [ciSkel, hn'] using this)

/-- The normalisation stores a constant of the declared name (task
#210 Part D). -/
theorem normCtorValF_name (ops : CheckerOps CheckCM) (fe : FEnv) (T : Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) (hn : cvCa.name = cvC.name) :
    Yields (normCtorValF ops fe T nP nF cvC cvCa) (fun r => r.name = cvC.name) := by
  unfold normCtorValF
  yields
  all_goals (dsimp only; split)
  all_goals first
    | (apply Yields.pure; exact hn)
    | exact Yields.mono (checkConstantValF_name ops fe _) (fun _ h => h)

theorem checkSumCtorF_name (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_name ops fe cvC) fun cvCa₀ hn₀ => ?_
  refine Yields.bind' (normCtorValF_name ops fe T nP nF cvC cvCa₀ hn₀) fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact hn)

/-- The constructor list's names and field counts are the block's, and
the field-sort lists come one per constructor (task #210 Part A). -/
theorem checkSumCtorsF_names (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun r => r.1.map (fun c => (c.1.name, c.2))
          = cs.map (fun c => (c.1.name, c.2)) ∧ r.2.length = cs.length)
  | [] => Yields.pure ⟨rfl, rfl⟩
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_name ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun q hn => ?_
    obtain ⟨cvCa, sorts⟩ := q
    refine Yields.bind' (checkSumCtorsF_names ops fe₀ fe T lps nP nIdx rs isProp
      large cvTa cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    have hn' : cvCa.name = c.1.name := hn
    exact Yields.pure ⟨by simp [hn', hrest.1], by simpa using hrest.2⟩

/-- The constructors' conses at the skeleton level. -/
theorem consSumCtorsF_skels (nP : Nat) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {fe : FEnv} {sk : List InstallSkel},
      SkelIs fe sk →
      SkelIs (consSumCtorsF nP ctorsA fe)
        (sumCtorSkels nP (ctorsA.map fun c => (c.1.name, c.2)) sk)
  | [], _, _, h => h
  | c :: cs, fe, sk, h => by
    have hstep := consSumCtorsF_skels nP (ctorsA := cs)
      (h.push (.ctorInfo c.1 nP c.2))
    simpa [consSumCtorsF, sumCtorSkels, ciSkel] using hstep

/-- The stored rules are one per constructor, in constructor order. -/
theorem sumRules_map_ctor (find? : Name → Option ConstantInfo)
    (recName : Name) (nP mI rP : Nat) (recTy : Expr) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr},
      rhss.length = ctorsA.length →
      (sumRules find? recName nP mI rP recTy ctorsA rhss).map (·.ctor)
        = ctorsA.map (·.1.name)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, rhs :: rhss, h => by
    simp only [sumRules, List.map_cons, List.cons.injEq, true_and,
      recRuleBits_ctor]
    exact sumRules_map_ctor find? recName nP mI rP recTy (by simpa using h)

/-! ### The direct recursive install (task #188) -/

/-- The generators' constructor list is one entry per constructor
when the kinds are one list per constructor (a local twin of
`Ix.Kernel.nativeCtors4_length`, `Ix/Kernel/Verify/Inductives/FixWF.lean`: this
floor imports no direct-route verification). -/
private theorem nativeCtors4_length' {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List RecFieldKind)} (h : ctorsA.length = kinds.length) :
    (nativeCtors4 ctorsA kinds).length = ctorsA.length := by
  simp [nativeCtors4, List.length_zipWith, h]

theorem checkNativeRulesF_len {w : StructWalkers} (fe : FEnv)
    (rlps : List Name) (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) :
    ∀ (k j : Nat),
      Yields (checkNativeRulesF (m := CheckCM) w fe rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j)
        (fun rhss => rhss.length = k)
  | 0, _ => Yields.pure rfl
  | k + 1, j => by
    unfold checkNativeRulesF
    refine Yields.bind fun rhs => ?_
    try ylet
    split
    case isTrue =>
      refine Yields.bind' (checkNativeRulesF_len fe rlps T lps elim large
        nP nIdx tty ctors recC rlvls k (j + 1)) fun rest hrest => ?_
      exact Yields.pure (by simp [hrest])
    case isFalse => exact Yields.ofThrowBind

/-- The recursor stage stores the generated recursor at the stream's
name, with one rule per generator entry. -/
theorem checkNativeRecF_yields (ops : CheckerOps CheckCM) {w : StructWalkers} (fe : FEnv)
    (p : NativeParts) (cvTa : ConstantVal)
    (ctorsA : List (ConstantVal × Nat)) :
    Yields (checkNativeRecF ops w fe p cvTa ctorsA)
      (fun r => r.1.name = p.cvR.name ∧
        r.2.length = (nativeCtors4 ctorsA p.kinds).length) := by
  unfold checkNativeRecF
  -- the recursor pin (task #220): two guards, each throwing
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.bind fun cvRi => ?_
  refine Yields.bind fun recTy => ?_
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
  refine Yields.bind fun _sty => ?_
  refine Yields.bind fun _u => ?_
  refine Yields.bind fun b => ?_
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
  try simp only []
  refine Yields.bind' (checkNativeRulesF_len _ p.cvR.levelParams
    p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
    (nativeCtors4 ctorsA p.kinds) p.cvR.name (p.cvR.levelParams.map .param)
    (nativeCtors4 ctorsA p.kinds).length 0)
    fun rhss hrhss => ?_
  exact Yields.pure ⟨rfl, by simpa using hrhss⟩

/-- The table stage of the fixpoint route at the skeleton level (task
#210 Part A): the table's skeleton at a structure-like block, nothing
otherwise — decided by the block's constructor count and index count,
since the annotated constructor list and the sort lists are one per
constructor. -/
theorem checkNativeTableF_skels {w : StructWalkers} {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (hlen : ctorsA.length = p.ctors.length)
    (hlenS : sortss.length = p.ctors.length) :
    Yields (checkNativeTableF (m := CheckCM) w p ctorsA sortss fe)
      (fun fe' => SkelIs fe' (if p.ctors.length == 1 && p.nIdx == 0 then
        .proj (projTableName p.cvT.name) :: sk else sk)) := by
  match ctorsA, sortss, hlen, hlenS with
  | [cA], [sorts], hlen, _ =>
    simp only [checkNativeTableF]
    have h1 : (p.ctors.length == 1) = true := by simp [← hlen]
    by_cases hi : (p.nIdx == 0) = true
    · rw [if_pos hi]
      simp only [h1, hi, Bool.and_self, if_true]
      exact checkStructProjTableF_skels h _ _ _ _ _ _ _ _ _
    · rw [if_neg hi]
      simp only [h1, hi, Bool.and_false]
      exact Yields.pure h
  | [], _, hlen, _ =>
    simp only [checkNativeTableF]
    have h1 : (p.ctors.length == 1) = false := by simp [← hlen]
    simp only [h1, Bool.false_and]
    exact Yields.pure h
  | _ :: _ :: _, _, hlen, _ =>
    simp only [checkNativeTableF]
    have h1 : (p.ctors.length == 1) = false := by simp [← hlen]
    simp only [h1, Bool.false_and]
    exact Yields.pure h
  | [_], [], hlen, hlenS => simp at hlen hlenS; omega
  | [_], _ :: _ :: _, hlen, hlenS => simp at hlen hlenS; omega

/-- One pass (task #268): the former's skeleton, the record's shape
(the sort read), the constructors by name and field count. -/
theorem checkNativePassS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (p : NativeParts) (isRec : Bool) :
    Yields (checkNativePassS mode fe p isRec)
      (fun r => SkelIs r.1.env₁ (.ind r.1.p.cvT.name :: sk) ∧
        (∃ s, r.1.p.toInductiveShape = p.toInductiveShape.withSort s) ∧
        r.1.ctorsA.map (fun c => (c.1.name, c.2)) = r.1.p.ctors.map (fun c => (c.1.name, c.2)) ∧
        r.1.sortss.length = r.1.p.ctors.length) := by
  unfold checkNativePassS
  refine Yields.bind' (checkSumIndF_skels h _ p.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTa, p₁⟩ := r₁
  obtain ⟨h₁, s, hps⟩ := h₁
  try simp only [] at hps
  subst hps
  try simp only []
  ybind
  refine Yields.bind' (checkSumCtorsF_names _ fe₁ fe₁ _ _ _ _ _ _ _ cvTa _) fun r hr => ?_
  obtain ⟨ctorsA, sortss⟩ := r
  obtain ⟨hns, hlenS⟩ := hr
  try simp only []
  refine Yields.bind fun kinds => ?_
  refine Yields.pure ⟨h₁, ⟨s, rfl⟩, hns, hlenS⟩

/-- The install after the pass: the sum's skeleton with the table at a
structure-like block. -/
theorem checkNativeTailS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} {q : NativePass FEnv}
    (h₁ : SkelIs q.env₁ (.ind q.p.cvT.name :: sk))
    (hns : q.ctorsA.map (fun c => (c.1.name, c.2)) = q.p.ctors.map (fun c => (c.1.name, c.2)))
    (hlenS : q.sortss.length = q.p.ctors.length) :
    Yields (checkNativeTailS mode fe q) (fun fe' => SkelIs fe' (nativeSkels q.p sk)) := by
  unfold checkNativeTailS
  -- the elimination restriction, on the completed record
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => ?elim) (fun _ => ?elimBad)
  case elimBad => exact Yields.ofThrowBind
  case elim =>
  ybind
  -- the index binders' sorts (read, not compared)
  refine Yields.bind fun _isorts => ?_
  try simp only []
  -- the field kinds, re-checked
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue hk =>
  -- the stream's rules against the generated ones
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  ybind
  refine Yields.bind' (checkNativeRecF_yields _ _ q.p q.cvTa q.ctorsA)
    fun r₃ h₃ => ?_
  obtain ⟨cvRa, rhss⟩ := r₃
  obtain ⟨hnR, hlen⟩ := h₃
  try simp only [] at hnR hlen
  try simp only []
  have hctors : q.ctorsA.map (·.1.name) = q.p.ctors.map (·.1.name) := by
    have := congrArg (List.map Prod.fst) hns
    simpa [List.map_map, Function.comp_def] using this
  have hlenA : q.ctorsA.length = q.p.kinds.length := by
    simp only [nativeFieldsOkF, Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.1
  have hlenC : q.ctorsA.length = q.p.ctors.length := by
    have := congrArg List.length hns
    simpa using this
  have hlen' : rhss.length = q.ctorsA.length := by
    rw [hlen, nativeCtors4_length' hlenA]
  have hbase : SkelIs (consSumCtorsF q.p.nP q.ctorsA q.env₁)
      (sumCtorSkels q.p.nP (q.p.ctors.map fun c => (c.1.name, c.2))
        (.ind q.p.cvT.name :: sk)) := by
    have hcs := consSumCtorsF_skels q.p.nP (ctorsA := q.ctorsA) h₁
    rwa [hns] at hcs
  have hpush := hbase.push (.recInfo cvRa q.p.majorIdx q.p.rulePrefix
    (sumRules (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name
      q.p.nP q.p.majorIdx q.p.rulePrefix cvRa.type q.ctorsA rhss))
  have hpush' : SkelIs (consSumCtorsF q.p.nP q.ctorsA q.env₁ |>.push (.recInfo cvRa q.p.majorIdx
      q.p.rulePrefix (sumRules (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name
        q.p.nP q.p.majorIdx q.p.rulePrefix cvRa.type q.ctorsA rhss)))
      (sumSkels q.p.toInductiveShape sk) := by
    simpa [ciSkel, sumSkels, hnR, sumRules_map_ctor _ _ _ _ _ _ hlen',
      hctors] using hpush
  -- the projection table at a structure-like block (task #210 Part A)
  refine Yields.mono (checkNativeTableF_skels hpush' q.p q.ctorsA q.sortss hlenC hlenS) ?_
  intro fe' h'
  unfold nativeSkels
  simpa [sumSkels] using h'

/-- The completed record's skeleton is the recognised one's: the sort
the former read is not in it. -/
theorem nativeSkels_withSort {p q : NativeParts} {s : Level}
    (hq : q.toInductiveShape = p.toInductiveShape.withSort s) (sk : List InstallSkel) :
    nativeSkels q sk = nativeSkels p sk := by
  have hc : q.ctors = p.ctors := by
    show q.toInductiveShape.ctors = p.toInductiveShape.ctors
    rw [hq]; rfl
  have hi : q.nIdx = p.nIdx := by
    show q.toInductiveShape.nIdx = p.toInductiveShape.nIdx
    rw [hq]; rfl
  have hT : q.cvT = p.cvT := by
    show q.toInductiveShape.cvT = p.toInductiveShape.cvT
    rw [hq]; rfl
  unfold nativeSkels
  rw [hc, hi, hT, hq]
  simp [sumSkels]

theorem checkNativeS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (p : NativeParts) :
    Yields (checkNativeS mode fe p)
      (fun fe' => SkelIs fe' (nativeSkels p sk)) := by
  unfold checkNativeS
  -- the front guard: the distinct constructor names
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => ?dupBad) (fun _ => ?main)
  case dupBad => exact Yields.ofThrowBind
  case main =>
  ybind
  -- the pass at the syntactic reading, and again where it overshot
  -- (task #268)
  refine Yields.bind' (checkNativePassS_skels mode h p (nativeRawRec p)) fun r hr => ?_
  obtain ⟨q, settled⟩ := r
  obtain ⟨h₁, ⟨s, hq⟩, hns, hlenS⟩ := hr
  try simp only [] at h₁ hq hns hlenS
  try simp only []
  cases settled with
  | true =>
    simp only [↓reduceIte]
    refine Yields.mono (checkNativeTailS_skels mode h₁ hns hlenS) ?_
    intro fe' h'
    rwa [nativeSkels_withSort hq] at h'
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  ybind
  refine Yields.bind' (checkNativePassS_skels mode h p (nativeIsRec q.p.kinds)) fun r' hr' => ?_
  obtain ⟨q', settled'⟩ := r'
  obtain ⟨h₁', ⟨s', hq'⟩, hns', hlenS'⟩ := hr'
  try simp only [] at h₁' hq' hns' hlenS'
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  refine Yields.mono (checkNativeTailS_skels mode h₁' hns' hlenS') ?_
  intro fe' h'
  rwa [nativeSkels_withSort hq'] at h'

/-! ### The tolerated-axiom branch

`sorryAx` is the one axiom the checker tolerates as a declaration, and
none of the pinned axiom guards can fire on it — so at `.axiomDecl` the
*push-or-not* decision is a function of the header name alone, in both
drivers. -/

theorem tolerated_not_std (fe : FEnv) (cvA : ConstantVal)
    (ht : cvA.name = sorryAxName) :
    stdAxiomOkF fe cvA = false := by
  rw [stdAxiomOkF, if_neg, if_neg] <;> rw [ht] <;> decide

theorem tolerated_ne_trust {n : Name}
    (ht : n = sorryAxName) : n ≠ trustCompilerName := by
  rw [ht]; decide

theorem tolerated_ne_ofReduce {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = ofReduceNatName ∨ n = ofReduceBoolName) := by
  rw [ht]; decide

theorem tolerated_ne_std {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = propextName ∨ n = choiceName) := by
  rw [ht]; decide

/-! ### The cached certified declaration clause -/

/-- The pinned-block install's skeleton reading, shared by the three
arms that install one (task #293). -/
theorem checkBasisDeclC_skels {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (kind : BasisKind) :
    Yields (checkBasisDeclC fe kind)
      (fun fe' => SkelIs fe'
        (kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk)) := by
  have hfold : ∀ (fe' : FEnv) (sk' : List InstallSkel), SkelIs fe' sk' →
      Yields (kind.declsA.foldlM installBasisDeclF fe')
        (fun x => SkelIs x
          (kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk')) :=
    fun fe' sk' h' =>
      Yields.foldlM_rel (R := SkelIs) (g := fun acc ci => ciSkel ci :: acc)
        (fun acc ci sk'' hacc => installBasisDeclF_skels hacc ci)
        kind.declsA fe' sk' h'
  unfold checkBasisDeclC
  yields
  all_goals exact hfold fe sk h

theorem checkDeclC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclC declCSkels
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkDefnValC mode fe cvA jty value hint)
        (fun fe' => SkelIs fe' (.defn cv.name :: sk)) := by
      rw [← hp]; exact checkDefnValC_skels mode h cvA jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    rw [← hp]
    exact checkThmValC_skels mode h cvA jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkOpaqueValC mode fe cvA jty value)
        (fun fe' => SkelIs fe' (.ax cv.name :: sk)) := by
      rw [← hp]; exact checkOpaqueValC_skels mode h cvA jty value
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | axiomDecl cv =>
    simp only []
    -- task #293: `Quot.sound` is compared with the pin and installs
    -- nothing of its own
    by_cases hqs : cv.name = quotSoundName
    · rw [if_pos hqs, if_pos (Or.inr hqs)]
      split
      · exact Yields.pure h
      · exact Yields.ofThrow
    · rw [if_neg hqs]
      refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
      obtain ⟨cvA, jty⟩ := p
      simp only []
      rw [← hp]
      by_cases ht : cvA.name = sorryAxName
      · rw [if_pos (Or.inl ht),
          if_neg (by rw [tolerated_not_std fe cvA ht]; exact Bool.false_ne_true),
          if_neg (tolerated_ne_trust ht), if_neg (tolerated_ne_ofReduce ht),
          if_neg (tolerated_ne_std ht), if_pos ht]
        exact Yields.pure h
      · have hne : ¬(cvA.name = sorryAxName ∨ cvA.name = quotSoundName) := by
          rintro (h' | h')
          · exact ht h'
          · exact hqs (hp ▸ h')
        rw [if_neg hne]
        yields
        all_goals first
          | (apply Yields.pure; exact h.push _)
          | exact absurd (by assumption) ht
  | basisDecl kind => exact checkBasisDeclC_skels h kind
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the
    -- other members install nothing, a mismatch throws
    simp only []
    cases k <;>
      (split
       · first
         | exact checkBasisDeclC_skels h .quotK
         | exact Yields.pure h
       · exact Yields.ofThrow)
  | indDecl block nP =>
    simp only []
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin; the declared parameter count (task #228) below it is a
    -- guard whose `throw` installs nothing
    split
    next kind hk => rw [hk]; exact checkBasisDeclC_skels h kind
    next hk =>
      rw [hk]
      split
      · unfold indDeclSkels
        cases nativeParts? nP block with
        | none => exact checkIndDeclSF_skels mode h block
        | some p => exact checkNativeS_skels mode h p
      · exact Yields.ofThrow

theorem checkDeclStepC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_skels mode h pd

/-! ## The floor

The fold installs every record by `annotStepC` (`checkDecls`,
`Ix/Kernel/Cached/Installed.lean`) — a separable value declaration by
the install halves, everything else by `checkDeclStepC` — and its
phase B pushes nothing, so the skeleton spec `declCSkels` computes the
installed environment at *every* mode.  Hence: whenever two modes both
**accept**, they installed the same constants, in the same order, with
the same skeletons — and in particular the same names and the same
count.

Scope, stated exactly: these are **accept-verdict** statements.  The
trusted config's purpose is to reject less, and the recorded
trusted-mode divergences are decline/accept divergences, untouched
here. -/

theorem skelIs_empty : SkelIs (mkFEnv Env.empty) [] := ⟨⟨_, rfl⟩, rfl⟩

/-- The declaration-stream specification: the skeletons a stream
installs, newest first. -/
def streamSkels (ds : List Declaration) : List InstallSkel :=
  ds.foldl (fun sk pd => declCSkels pd sk) []

/-! ### The direct-parse entry points (task #171's route) -/

/-- Phase A's step body installs the declaration's skeletons: the value
kinds push the one constant the fold's value checkers push, everything
else runs `checkDeclStepC`. -/
theorem annotStepC_skels (mode : CheckMode) (i : Nat) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pend : Array PendingCheck) (pd : Declaration) :
    Yields (annotStepC mode pins i fe pend pd) (fun r => SkelIs r.1 (declCSkels pd sk)) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode pins fe pd', pend) :
      CheckCM (FEnv × Array PendingCheck)) (fun r => SkelIs r.1 (declCSkels pd' sk)) :=
    fun pd' => Yields.bind' (checkDeclStepC_skels mode h pd') fun fe' h' => Yields.pure h'
  unfold annotStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value true) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      apply Yields.pure
      show SkelIs (fe.push (.defnInfo cvA jv hint)) (.defn cv.name :: sk)
      rw [← hr.1]; exact h.push _
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hr => ?_
    obtain ⟨cvA, jty⟩ := p
    ybind
    apply Yields.pure
    show SkelIs (fe.push (.thmInfo cvA value)) (.thm cv.name :: sk)
    rw [← hr.1]; exact h.push _
  | opaqueDecl cv value =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value false) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      apply Yields.pure
      show SkelIs (fe.push (.axiomInfo cvA)) (.ax cv.name :: sk)
      rw [← hr.1]; exact h.push _
  | axiomDecl cv => exact hord _
  | basisDecl kind => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- Phase A's accepting run installs the stream's skeletons. -/
theorem installRun_skels (mode : CheckMode) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (h : InstallRun mode pins ds p s q s') {sk : List InstallSkel} (hp : SkelIs p.2.1 sk) :
    SkelIs q.2.1 (ds.foldl (fun sk pd => declCSkels pd sk) sk) := by
  induction h generalizing sk with
  | nil p s => exact hp
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    rw [List.foldl_cons]
    exact ih (annotStepC_skels mode p.1 hp p.2.2 pd s (fe₁, pend₁) s₁ hstepC)

/-- **The skeleton spec, at every mode.**  This is the floor's whole
content since the twin's retirement: one fold, one proof. -/
theorem checkDecls_skels {mode : CheckMode} {ds : Array Declaration}
    {env : Env} (h : checkDecls mode pins ds = .ok env) :
    envSkels env = streamSkels ds.toList := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
  obtain ⟨n, s, r⟩ := fc.1.run
  exact (installRun_skels mode r skelIs_empty).2

/-- **The floor, direct-parse route.**  Whenever the cached driver at
two modes — in particular the trusted (`.trusted`) and the verified
(`.verified`) mode the binary ships — both accept the same stream, the
two installed environments carry the same install skeletons.  Stated
for any two modes: the old two-driver statement is the instance
`.trusted` / `.verified` (`trusted_agrees_skels_shipped`). -/
theorem trusted_agrees_skels_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envSkels envN = envSkels envP :=
  (checkDecls_skels hN).trans (checkDecls_skels hP).symm

/-- The census's sentence: the accepted declaration **names** agree. -/
theorem trusted_agrees_names_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (trusted_agrees_skels_D hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

/-- … and so do the accepted declaration **counts**. -/
theorem trusted_agrees_count_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (trusted_agrees_skels_D hP hN)
  simpa [envSkels] using h

/-- The shipped pair, spelled out: `--trusted` and `--verified` agree on
the install skeletons whenever both accept. -/
theorem trusted_agrees_skels_shipped {ds : Array Declaration} {envP envT : Env}
    (hP : checkDecls .verified pins ds = .ok envP)
    (hT : checkDecls .trusted pins ds = .ok envT) :
    envSkels envT = envSkels envP :=
  trusted_agrees_skels_D hP hT

end Ix.Kernel.Cached
