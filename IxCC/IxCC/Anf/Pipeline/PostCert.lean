import IxCC.Anf.Shrink
import IxCC.Anf.Inline
import IxCC.Anf.Prune
import IxCC.Anf.DeadParam
import IxCC.Anf.Defun.Narrow
import IxCC.Anf.Defun.Flow

/-! # Post-P8 closure & dead-parameter certificate, runner, and producer

Separate from `Anf.Pipeline.Step` so exhaustive matches on `Step` outside the
middle end stay unchanged. Stored as an optional `post : Option PostCert` field
on `Anf.Pipeline.Cert` (omitted from JSON when `none`, so plain programs keep
byte-identical certificates).

All functions here use pure `List` / `Src.NatMap` / `Src.NatSet` with structural
fuel bounds (no `Std.HashSet`, no `Quot.sound` or `Classical.choice`). -/

namespace IxCC.Anf.Pipeline

/-- The nodes of `P`'s globals, counting each up to what is left of
`maxProgramNodes` and stopping once the total passes it. -/
def programNodesUpTo : List (GlobalId × GDef) → Nat → Nat
  | [], used => used
  | (_, gd) :: rest, used =>
    let used := used + gd.body.nodesUpTo (maxProgramNodes - used)
    if used > maxProgramNodes then used else programNodesUpTo rest used

/-- Refuse a program holding a global over `maxGlobalNodes` or deeper than
`maxDepth`, more than `maxProgramNodes` nodes in all, or more back-end work
than `maxBackWork`. The counts stop early and walk explicit worklists
(`Exp.nodesUpTo`, `Exp.depthUpTo`), so the check is cheap and shallow whatever
the program's size and depth. Inlining a callee doubles a mutually recursive
pair each round with one firing, so the walk's budgets alone do not bound
certificate rounds. -/
def checkGlobalNodes (P : Program) : Except String Program :=
  if !(P.globalList.all (fun (_, gd) => gd.body.nodesLe maxGlobalNodes) &&
      programNodesUpTo P.globalList 0 ≤ maxProgramNodes) then
    .error "middle end: a global or the program exceeds the node budget"
  else if !(P.globalList.all fun (_, gd) => gd.body.depthUpTo maxDepth maxGlobalNodes ≤ maxDepth) then
    .error "middle end: a global exceeds the depth budget"
  else if backWork P > maxBackWork then
    .error "middle end: the program exceeds the back end's work budget"
  else .ok P

/-- One certified post-P8 optimization step. -/
inductive PostStep where
  | shrink (cert : Shrink.Cert)
  | inline (round : Inline.Round)
  | prune
  | narrow (cert : Defun.Narrow.Cert)
  | deadParam
  deriving Inhabited

/-- Certificate for post-P8 optimization (known-dispatch shrinking, post-P8
inlining, P9 flow-directed dispatch narrowing, and P5 dead-parameter stripping). -/
structure PostCert where
  /-- Program `size` immediately before P8 (`Entry.run` output size), used to
  detect whether `Entry.run` added root entries relative to `Pipeline.produce`. -/
  baseSize : Nat := 0
  shrink : Shrink.Params := {}
  steps : List PostStep := []
  deriving Inhabited

/-- Maximum post-P8 steps allowed in a certificate. -/
def maxPostSteps : Nat := 48

/-- Maximum P9 narrowing steps allowed in a certificate. -/
def maxPostNarrow : Nat := 2

/-- Maximum P5 dead-parameter stripping steps allowed in a certificate. -/
def maxPostDeadParam : Nat := 4

def checkPostStep : PostStep → Bool
  | .shrink c => Shrink.checkCert c
  | .inline r => Inline.checkCert r
  | .prune => true
  | .narrow c => Defun.Narrow.checkCert c
  | .deadParam => true

def PostStep.isNarrow : PostStep → Bool
  | .narrow _ => true
  | _ => false

def PostStep.isDeadParam : PostStep → Bool
  | .deadParam => true
  | _ => false

def checkPostCert (pc : PostCert) : Bool :=
  pc.shrink.checkCert &&
  pc.steps.length ≤ maxPostSteps &&
  pc.steps.all checkPostStep &&
  (pc.steps.filter PostStep.isNarrow).length ≤ maxPostNarrow &&
  (pc.steps.filter PostStep.isDeadParam).length ≤ maxPostDeadParam

def PostStep.name : PostStep → String
  | .shrink _ => "post-P2"
  | .inline _ => "post-P3"
  | .prune => "post-prune"
  | .narrow _ => "P9"
  | .deadParam => "P5"

/-- Run one certified post-P8 step, followed by `checkGlobalNodes` on passes
that can grow code. -/
def PostStep.run (p : Shrink.Params) : PostStep → Program → Except String Program
  | .shrink c, P =>
    if c.length ≤ P.size then Shrink.run p c P >>= checkGlobalNodes
    else .error "shrink: the certificate lists more globals than the program has"
  | .inline r, P =>
    if r.length ≤ P.size then Inline.round P r >>= fun x => checkGlobalNodes x.1
    else .error "inline: a round lists more callers than the program has globals"
  | .prune, P => pure (Prune.run P)
  | .narrow c, P => checkGlobalNodes (Defun.Narrow.run c P)
  | .deadParam, P => checkGlobalNodes (DeadParam.run P)

/-- Replay a post-P8 certificate on the output of `Anf.defun`. -/
def runPost (pc : PostCert) (P : Program) : Except String Program :=
  match pc.steps with
  | [] => checkGlobalNodes P
  | _ :: _ => do
    let Q ← pc.steps.foldlM (fun Q s => s.run pc.shrink Q) P
    if firstOrder Q then checkGlobalNodes Q
    else .error "anf.post: residual closure"

/-! ## Deterministic post-P8 schedule producer -/

private def hasDispatchers (P : Program) : Bool :=
  P.globalList.any fun (_, gd) => Walk.isDispatchKey gd.key

private def hasDeadParams (P : Program) : Bool :=
  !(DeadParam.buildPlan P P.size P.globalList).isEmpty &&
  P.globalList.all (fun (_, gd) => DeadParam.globBelow P.size gd.body)

private def doPostShrinkBy (shrinkFn : Program → Except String (Shrink.Cert × Program))
    (P : Program) (steps : List PostStep) : Program × List PostStep :=
  if steps.length + 1 > maxPostSteps then (P, steps)
  else
    match shrinkFn P with
    | .ok (c, P') =>
      if c.any (· > 0) && c.length ≤ P.size && Shrink.checkCert c then
        match checkGlobalNodes P' with
        | .ok P'' => (P'', .shrink c :: steps)
        | .error _ => (P, steps)
      else (P, steps)
    | .error _ => (P, steps)

private def doPostPrune (P : Program) (steps : List PostStep) : Program × List PostStep :=
  if steps.length + 1 > maxPostSteps then (P, steps)
  else
    let P' := Prune.run P
    if P'.size < P.size then (P', .prune :: steps) else (P, steps)

private def doPostInlineRoundsBy (p : Shrink.Params)
    (shrinkFn : Program → Except String (Shrink.Cert × Program)) :
    Nat → Program → List PostStep → Program × List PostStep
  | 0, P, steps => (P, steps)
  | rem + 1, P, steps =>
    if steps.length + 3 > maxPostSteps then (P, steps)
    else
      let r := Inline.producePostP8 128 P
      if r.isEmpty || !Inline.checkCert r then (P, steps)
      else
        let res :=
          match PostStep.run p (.inline r) P with
          | .ok P3 => some (r, P3)
          | .error _ =>
            let r' := r.filter fun e => (PostStep.run p (.inline [e]) P).isOk
            if r'.isEmpty then none
            else (PostStep.run p (.inline r') P).toOption.map (r', ·)
        match res with
        | none => (P, steps)
        | some (r', P3) =>
          let (P2, steps2) := doPostShrinkBy shrinkFn P3 (.inline r' :: steps)
          doPostInlineRoundsBy p shrinkFn rem P2 steps2

private def doPostDeadParamRoundsBy (p : Shrink.Params)
    (shrinkFn : Program → Except String (Shrink.Cert × Program)) :
    Nat → Program → List PostStep → Program × List PostStep
  | 0, P, steps => (P, steps)
  | rem + 1, P, steps =>
    if steps.length + 4 > maxPostSteps || !hasDeadParams P then (P, steps)
    else
      match PostStep.run p .deadParam P with
      | .error _ => (P, steps)
      | .ok Pd =>
        let (P1, steps1) := doPostPrune Pd (.deadParam :: steps)
        let (P2, steps2) := doPostShrinkBy shrinkFn P1 steps1
        let (P3, steps3) := doPostPrune P2 steps2
        doPostDeadParamRoundsBy p shrinkFn rem P3 steps3

/-- Deterministic post-P8 optimization schedule returning both the `PostCert`
and the final optimized program, parameterized by a shrink step `shrinkFn`:
1. Post-P8 known-dispatch shrink (`P2`) + up to 6 rounds of post-P8 `(P3 → P2)` + `prune`.
2. If dispatchers remain, P9 flow analysis (`Flow.analyse P 4`) + dispatch narrowing
   (`Narrow.run`), followed by `P2` + up to 4 rounds of `(P3 → P2)` + `prune`.
3. Up to 3 rounds of P5 erased/dead-parameter stripping (`DeadParam.run`) + `prune` + `P2`. -/
def producePostBy (p : Shrink.Params) (shrinkFn : Program → Except String (Shrink.Cert × Program))
    (baseSize : Nat) (Q8 : Program) : PostCert × Program :=
  -- Stage 1: known-dispatch shrink + post-P8 (P3 → P2)* + prune
  let (P1, s1) := doPostShrinkBy shrinkFn Q8 []
  let (P2, s2) := doPostInlineRoundsBy p shrinkFn 6 P1 s1
  let (P3, s3) := doPostPrune P2 s2
  -- Stage 2+3: P9 flow-directed dispatch narrowing + post-P9 (P3 → P2)* + prune
  let (P4, s4) :=
    if hasDispatchers P3 && s3.length + 2 ≤ maxPostSteps then
      match Defun.Flow.analyse P3 4 with
      | some cert =>
        if Defun.Narrow.checkCert cert then
          match PostStep.run p (.narrow cert) P3 with
          | .ok Pn =>
            let (Pn1, sn1) := doPostShrinkBy shrinkFn Pn (.narrow cert :: s3)
            let (Pn2, sn2) := doPostInlineRoundsBy p shrinkFn 4 Pn1 sn1
            doPostPrune Pn2 sn2
          | .error _ => (P3, s3)
        else (P3, s3)
      | none => (P3, s3)
    else (P3, s3)
  -- Stage 4: P5 dead-parameter stripping + prune + shrink cleanup
  let (P5, s5) := doPostDeadParamRoundsBy p shrinkFn 3 P4 s4
  let pc : PostCert := { baseSize, shrink := p, steps := s5.reverse }
  if checkPostCert pc then (pc, P5) else ({ baseSize, shrink := p, steps := [] }, Q8)

/-- Deterministic post-P8 schedule producer using `Shrink.shrinkChecked`. -/
def producePost (baseSize : Nat) (Q8 : Program) : PostCert :=
  let p : Shrink.Params := {}
  (producePostBy p (fun P =>
    let (c, _) := Shrink.shrinkChecked p 64 P
    if c.any (· > 0) && Shrink.checkCert c then
      match PostStep.run p (.shrink c) P with
      | .ok P' => .ok (c, P')
      | .error e => .error e
    else .ok ([], P)) baseSize Q8).1

end IxCC.Anf.Pipeline
