/-
  Ix.AuxGen.SourceEnv: the checked half of the Source service environment
  (AuxGen on IxC, M1; AUXGEN-IXC §3.2–§3.3).

  What AuxGen's kernel questions run against in Source mode, and what they
  need besides the environment's construction: the verified fold's state
  (`Fold`), its evidence, and the class map σ of the canonical flat blocks
  and generated constants installed so far. A `module`, over the shared term
  half of the Source ingress (`Ix.LeanIngress.Expr`), so the compiler's
  modules (the `AuxKernel` interface's IxC arm, AuxGen M2) can hold one.
  Building it from a Lean environment (lowering declaration groups through
  the Ixon reader's back half) is `Ix.AuxGen.SourceService`'s, which is not a
  module yet because the reader is not.

  * **The fold.** `Fold.step` is one declaration through both phases of the
    verified fold (`Cached.annotDeclStep`, then `Cached.checkPendingList` on
    the records the step left pending, against the environment after it), as
    the per-record step drivers run it; `Fold.steps` a group's declarations,
    the first failure the group's. A failure leaves the caller's fold as it
    was: folds are values.
  * **Terms in** (`ingress`, `key`): a Lean term renamed by σ
    (`Flat.renameExpr`), then the ingress's term conversion (`ingressExprs`)
    under the constant's numbering. σ fits `Key.map` (`Flat.ClassMap.misfit` is
    refused at every install), so this equals the ingress followed by
    `Key.map` of σ on Source keys.
  * **Installs.** `install` folds a block's lowered declarations and joins
    its σ, both or neither; `admitDefinition` checks a generated definition
    under its fresh name through σ and then maps its name there (the
    `AuxKernel` contract's clause 9: "IxC will use a fresh key and σ").

  Nothing here is trusted: every declaration goes through the verified
  fold, and what it cannot install is refused, with the fold's reason.

  * **The tier** (M7 Q1): partial and unsafe declarations, unsafe inductive
    blocks and recursor-less families, which the fold declines, are
    installed beside it, typing only (`Ix.Kernel.Tier`), in an overlay the
    logical fold never sees (`tier`). Each is checked at the view Lean's
    lattice gives its stage (`checkView`: a partial block sees the partial
    overlay, an unsafe opaque the logical index only, everything else the
    whole overlay), with tier constants opaque; a definition block the
    opaque check refuses is checked over the answer view instead, as Lean
    unfolds tier definitions while it checks a block (`Ix.Resource.Typing`'s
    rule). The **answer view** (`answers`, `Tier.AnswerView`) holds the
    overlay's δ and ι forms: only an unsafe block's answering scopes read it
    (`Ix.AuxGen.Ixc`). No tier install is a verdict.
-/
module
public import Ix.LeanIngress.Expr
public import IxC.Kernel.Cached.Installed
public import IxC.Kernel.Tier.Answer
public import Ix.AuxGen.FlatBlock
public section

namespace Ix.AuxGen.Source

open Ix.LeanIngress (ingressKey ingressExprs Numbering ExprError)
open Ix.AuxGen.Flat (ClassMap FlatError)

abbrev Decl := Ix.Kernel.Declaration .source

/-! ## The fold -/

/-- The fold's state: the indexed environment, the memo state, the fold
position. -/
structure Fold where
  fe : Ix.Kernel.FEnv .source := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState .source := {}
  pos : Nat := 0

instance : Inhabited Fold := ⟨{}⟩

/-- One declaration through both phases of the verified fold. -/
def Fold.step (ev : Ix.Kernel.Evidences .source) (f : Fold) (d : Decl) :
    Except (Ix.Kernel.CheckError .source) Fold :=
  match Ix.Kernel.Cached.annotDeclStep .verified ev (f.pos, f.fe, #[]) d f.cs with
  | .error (e, _) => .error e
  | .ok ((pos, fe, pend), cs) =>
    match Ix.Kernel.Cached.checkPendingList .verified fe pend.toList with
    | .ok () => .ok { fe, cs, pos }
    | .error (e, _) => .error e

/-- A group's declarations in order; the first failure is the group's. -/
def Fold.steps (ev : Ix.Kernel.Evidences .source) (f : Fold) (ds : Array Decl) :
    Except (Ix.Kernel.CheckError .source) Fold :=
  ds.foldlM (·.step ev) f

/-- `steps` on a fold its caller gives up: the fold after the group, or at
the first failure the fold before it, rebuilt from its environment with
fresh memo state, and the failure. The caller keeps no other reference to
the fold, so on success the index and the memo state are updated in place,
and only a failure costs a rebuild (the per-record step drivers' rollback,
`Benchmarks.Kernel.CheckIxeStep.Checker.step`). Under `steps`, whose caller
keeps the fold to fall back on, the group's first install copies the index
and the memo state. -/
def Fold.stepsOwned (ev : Ix.Kernel.Evidences .source) (f : Fold) (ds : Array Decl) :
    Fold × Option (Ix.Kernel.CheckError .source) := Id.run do
  let ⟨fe, cs, pos₀⟩ := f
  let before := fe.env
  let mut fe := fe
  let mut cs := cs
  let mut pos := pos₀
  for d in ds do
    match Ix.Kernel.Cached.annotDeclStep .verified ev (pos, fe, #[]) d cs with
    | .error (e, _) => return (⟨Ix.Kernel.mkFEnv before, {}, pos₀⟩, some e)
    | .ok ((pos', fe', pend), cs') =>
      match Ix.Kernel.Cached.checkPendingList .verified fe' pend.toList with
      | .ok () =>
        fe := fe'
        cs := cs'
        pos := pos'
      | .error (e, _) => return (⟨Ix.Kernel.mkFEnv before, {}, pos₀⟩, some e)
  return (⟨fe, cs, pos⟩, none)

/-- A failure as text: the verdict and the message, keys spelled as their
Lean names. -/
def renderCheck (e : Ix.Kernel.CheckError .source) : String := e.render toString

/-- Whether Source mode's role binding fixes a Lean name: its key is a role
key. σ never moves such a name (`Key.map` fixes `.role` keys). -/
def roleBound (n : Name) : Bool := ingressKey n matches .role _

/-! ## The checked environment -/

open Ix.Kernel.Tier (TierDecl TierInd TierIndOut AnswerView)

/-- What a tier install adds to the answer view: δ forms and opaque headers
(`infos`), or a checked inductive block (`ind`, its recursors' ι). -/
inductive TierAnswer where
  | infos (cis : List (Ix.Kernel.ConstantInfo .source))
  | ind (o : TierIndOut .source)

/-- **One tier install**: its stage in Lean's lattice (`TierDecl.stage`; an
inductive block is `2`), its check forms (tier constants opaque) and its
answer forms. -/
structure TierEntry where
  stage : Nat
  check : List (Ix.Kernel.ConstantInfo .source)
  answer : TierAnswer

/-- **The checked half of the service**: the fold, its evidence, the class
map σ of everything installed under fresh names, and the tier overlay. -/
structure SourceEnv where
  fold : Fold := {}
  ev : Ix.Kernel.Evidences .source := []
  sigma : ClassMap := {}
  tier : Array TierEntry := #[]

instance : Inhabited SourceEnv := ⟨{}⟩

namespace SourceEnv

/-- **The check view of a stage**: the logical index with the tier constants a
declaration of that stage may name pushed opaque: the partial ones at stage
`0`, none at `1` (an unsafe opaque, checked in Lean's safe mode), all at `2`. -/
def checkView (s : SourceEnv) (stage : Nat) : Ix.Kernel.FEnv .source :=
  if stage == 1 then s.fold.fe else
  s.tier.foldl (init := s.fold.fe) fun fe e =>
    if stage == 2 || e.stage == 0 then Ix.Kernel.Tier.pushAll fe e.check else fe

/-- **The answer view**: the logical index with the overlay's δ and ι forms,
of the tier constants `stage` may name (`checkView`'s rule; the whole overlay
by default). -/
def answers (s : SourceEnv) (stage : Nat := 2) : AnswerView .source :=
  s.tier.foldl (init := AnswerView.ofLogical s.fold.fe) fun av e =>
    if stage == 2 || e.stage == 0 then
      match e.answer with
      | .infos cis => av.pushInfos cis
      | .ind o => av.pushInd o
    else av

/-- A tier install's keys must be new to the logical index and the overlay. -/
def tierFresh (s : SourceEnv) (keys : List (Ix.Kernel.Key .source)) : Except String Unit :=
  let taken (k : Ix.Kernel.Key .source) : Bool :=
    (s.fold.fe.find? k).isSome || s.tier.any (·.check.any (·.name == k))
  match keys.find? taken with
  | some k => throw s!"tier: {k} is already declared"
  | none => pure ()

/-- σ joined after a tier install: `σ` fits `Key.map` (as `install`'s). -/
def joinSigma (s : SourceEnv) (σ : ClassMap) : Except String ClassMap := do
  if let some n := σ.misfit roleBound then throw (FlatError.roleBound n).render
  (s.sigma.union σ).mapError (·.render)

/-- A definition block's δ forms over the answer view, for a block the opaque
check refuses: each value's type, inferred with the block's δ forms in the
view, must be convertible to its header there (`Ix.Resource.Typing`'s
`defsOverAnswers`). -/
def defsOverAnswers (av : AnswerView .source) (infos : List (Ix.Kernel.ConstantInfo .source)) :
    Except (Ix.Kernel.CheckError .source) Unit := do
  let knot := (av.pushInfos infos).knot
  for info in infos do
    if let .defnInfo cvA jv _ := info then
      let ok ← Ix.Kernel.Tier.runC (do
        let ty ← knot.infer 0 jv
        knot.defeq 0 ty cvA.type)
      unless ok do
        throw (.invalid msg!"the value of {cvA.name} does not have its declared type, \
          with tier definitions and unsafe recursors reducing")

/-- **Install a tier declaration** (`hints`: a definition block's, by
member) with the σ it joins: checked at its stage's view, its constants added
to the overlay, opaque for checks and in δ form for answers. -/
def installTierDecl (s : SourceEnv) (d : TierDecl .source) (hints : List Ix.Kernel.ReducibilityHint)
    (σ : ClassMap := {}) : Except String SourceEnv := do
  s.tierFresh d.names
  let view := s.checkView d.stage
  let entry ← match d with
    | .defs _ ms =>
      let withHints := ms.zipIdx.map fun ((cv, v), j) => (cv, v, hints.getD j (.regular 0))
      let infos ← (Ix.Kernel.Tier.defsAnswerC view withHints).mapError renderCheck
      match Ix.Kernel.Tier.checkDeclC s.fold.fe view d with
      | .ok (_, ts) => pure ⟨d.stage, Ix.Kernel.Tier.TierConst.infos ts, .infos infos⟩
      | .error e =>
        -- Lean adds a block's members before it checks their bodies, unfolding
        -- tier definitions: the block over the answer view
        (defsOverAnswers (s.answers d.stage) infos).mapError fun _ => renderCheck e
        let headers := infos.filterMap fun
          | .defnInfo cvA _ _ => some (.axiomInfo cvA)
          | _ => none
        pure ⟨d.stage, headers, .infos infos⟩
    | _ =>
      let (_, ts) ← (Ix.Kernel.Tier.checkDeclC s.fold.fe view d).mapError renderCheck
      let infos := Ix.Kernel.Tier.TierConst.infos ts
      pure ⟨d.stage, infos, .infos infos⟩
  pure { s with tier := s.tier.push entry, sigma := ← s.joinSigma σ }

/-- **Install an inductive block typing only** (`Tier.indC`, at the whole
overlay's view) with the σ it joins: its check forms (formers without
capabilities, constructors, rule-less recursors) and, for answers, its
recursors' typed rules. -/
def installTierInd (s : SourceEnv) (b : TierInd .source) (σ : ClassMap := {}) :
    Except String SourceEnv := do
  s.tierFresh (b.types.map (·.1.name) ++ b.ctors.map (·.1.name) ++ b.recs.map (·.1.name))
  let o ← (Ix.Kernel.Tier.indC (s.checkView 2) b).mapError renderCheck
  pure { s with tier := s.tier.push ⟨2, o.checkInfos, .ind o⟩, sigma := ← s.joinSigma σ }

/-- **A Lean term as a Source term, through σ**: constants renamed by σ, then
the Source ingress's conversion under the numbering of `lps` (`large` for a
large eliminator's own terms). -/
def ingress (s : SourceEnv) (lps : Array Name) (es : List Expr) (large : Bool := false) :
    Except ExprError (List (Ix.Kernel.Expr .source)) :=
  let renamed := (es.mapM (Flat.renameExpr s.sigma)).run' {}
  ingressExprs (Numbering.mk lps large).pos renamed

/-- A Lean name's Source key, through σ. -/
def key (s : SourceEnv) (n : Name) : Ix.Kernel.Key .source := ingressKey (s.sigma.apply n)

/-- **Install a block** (a canonical flat block's lowered declarations) with
its σ: the declarations folded and σ joined, or neither, with the reason. A
σ that moves or produces a role-bound name is refused before any fold. -/
def install (s : SourceEnv) (ds : Array Decl) (σ : ClassMap) : Except String SourceEnv := do
  if let some n := σ.misfit roleBound then throw (FlatError.roleBound n).render
  let f ← (s.fold.steps s.ev ds).mapError renderCheck
  let σ' ← (s.sigma.union σ).mapError (·.render)
  pure { s with fold := f, sigma := σ' }

/-- **Admit a generated definition** (or theorem, `thm`) named `name`, with
level parameters `lps`, type and value: checked under its fresh name
(`Flat.fresh name`), its terms read through σ; on acceptance σ maps `name` to
the fresh name, so later queries and installs see the generated declaration.
The constants it references must be installed already. -/
def admitDefinition (s : SourceEnv) (name : Name) (lps : Array Name) (type value : Expr)
    (thm : Bool) (hint : Ix.Kernel.ReducibilityHint := .abbrev) : Except String SourceEnv := do
  if roleBound name then throw (FlatError.roleBound name).render
  let fresh := Flat.fresh name
  match s.ingress lps [type, value] with
  | .error e => throw s!"ingress: {e}"
  | .ok [t, v] =>
    let cv : Ix.Kernel.ConstantVal .source := ⟨ingressKey fresh, (Numbering.mk lps false).params, t⟩
    let d : Decl := if thm then .thmDecl cv v else .defnDecl cv v hint
    let f ← (s.fold.step s.ev d).mapError renderCheck
    let σ ← (s.sigma.insert name fresh).mapError (·.render)
    pure { s with fold := f, sigma := σ }
  | .ok _ => throw "ingress: arity"

/-- **Admit a generated definition of an unsafe block** (M7 Q1): as
`admitDefinition`, but by the tier, as an unsafe definition (a theorem too,
whose proof the tier does not distinguish), so it may name tier constants;
its δ form joins the answer view. -/
def admitTierDefinition (s : SourceEnv) (name : Name) (lps : Array Name) (type value : Expr)
    (thm : Bool) (hint : Ix.Kernel.ReducibilityHint := .abbrev) : Except String SourceEnv := do
  if roleBound name then throw (FlatError.roleBound name).render
  let fresh := Flat.fresh name
  match s.ingress lps [type, value] with
  | .error e => throw s!"ingress: {e}"
  | .ok [t, v] =>
    let cv : Ix.Kernel.ConstantVal .source := ⟨ingressKey fresh, (Numbering.mk lps false).params, t⟩
    let σ ← (({} : ClassMap).insert name fresh).mapError (·.render)
    s.installTierDecl (.defs .unsaf [(cv, v)]) [if thm then .opaque else hint] σ
  | .ok _ => throw "ingress: arity"

end SourceEnv

end Ix.AuxGen.Source

end
