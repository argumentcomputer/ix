import IxCC.Rt.Lower

/-! # Switches the lowering dispatches without types (the pipeline's check)

Cfg's `switch` selects an edge by the scrutinee's constructor key; the
lowering (`Rt.lower`) tests words and tags, and keys are forgotten.
The two agree on a value of the switched inductive, but constructor tags
repeat across inductives and a `Nat` literal's word is a field-less
constructor's, so on a value of another type a default arm could be Cfg's
choice while a tag test fires in Lir. Cfg carries no types, so
`Rt.lower_correct` assumes `SwitchOk` of every state Cfg reaches.

`switchesOk` is the check that discharges it without a typing invariant
: every switch has **no default arm**, does not mix `Nat`
keys with other keys, and gives **distinct keys distinct tests** (zero,
successor, a field-less constructor's word, a cell's tag); and `Nat.zero`
and `Nat.succ` are not pinned to one key. Then a switch Cfg can step on
selects an alternative whose key is the scrutinee's, and every other
alternative's test rejects the scrutinee's word (`Rt.Proof.dispatches_of_ok`),
whatever the scrutinee's type.

The pipeline never makes a default arm: erasure emits every `case` without
one (one alternative per constructor of the eliminated inductive, with
distinct tags) and the later passes keep or drop alternatives without
adding a default. `Recheck.run` runs `checkSwitches` before `Rt.lower`;
`Rt.lower` itself still accepts default arms (the hand-written `tests-rt`
programs use them), so the check is the recheck path's, not the lowering's.
Kernel-evaluable style: lists, `NatMap.toList`, structural recursion. -/

namespace IxCC.Rt

open IxCC.Lir (Word)
open IxCC.Fir (FunId)
open Lower

/-- An alternative's lowered test as data: the zero test, the successor, a
field-less constructor's word, a cell's tag (`none`: a key outside the
table). -/
def altTest (T : Tables) (k : Key.CtorKey) : Option (Nat × Word) :=
  (keyKind T k).map fun
    | .zero => (0, 0)
    | .succ => (1, 0)
    | .imm w => (2, w)
    | .cell t => (3, UInt64.ofNat t)

/-- Whether a key is one of `Nat`'s, as the lowering classifies it. -/
def natAlt (T : Tables) (k : Key.CtorKey) : Bool :=
  match keyKind T k with
  | some .zero | some .succ => true
  | _ => false

/-- Distinct keys have distinct tests. -/
def testsDistinct (T : Tables) : List (Key.CtorKey × Cfg.Edge) → Bool
  | [] => true
  | p :: rest => rest.all (fun q => p.1 == q.1 || altTest T p.1 != altTest T q.1) && testsDistinct T rest

/-- A switch the lowering dispatches on every value Cfg can select an
alternative for: no default, no `Nat` keys mixed with others, distinct
tests. -/
def switchOk (T : Tables) (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) : Bool :=
  d.isNone && (alts.all (fun p => natAlt T p.1) || alts.all (fun p => !natAlt T p.1)) && testsDistinct T alts

/-- A block whose terminator, if a switch, is `switchOk`. -/
def blockSwitchOk (T : Tables) (b : Cfg.Block) : Bool :=
  match b.term with
  | .switch _ alts d => switchOk T alts d
  | _ => true

/-- `Nat.zero` and `Nat.succ` are not pinned to one key. -/
def pinsApart (K : Lam.Known) : Bool := !(K.natZero.isSome && K.natZero == K.natSucc)

/-- **The pipeline's switch check** (see the module note). -/
def switchesOk (P : Cfg.Program) : Bool :=
  pinsApart P.known && P.funs.toList.all fun (_, fd) => fd.blocks.all (blockSwitchOk (tables P))

/-- Why the pipeline's switch check declines a program. -/
inductive SwitchError where
  | pins
  | dispatch (f : FunId) (b : Nat)
  deriving Repr, Inhabited

def SwitchError.render : SwitchError → String
  | .pins => "rt.pins: Nat.zero and Nat.succ are pinned to one key"
  | .dispatch f b => s!"rt.dispatch: function {f} block {b}: a switch with a default arm, with Nat keys \
      mixed with others, or with two keys the lowering's tests cannot tell apart (Cfg selects by key, \
      Lir by word and tag)"

instance : ToString SwitchError := ⟨SwitchError.render⟩

/-- The first function and block whose terminator fails the check. -/
def badSwitch (T : Tables) : List (FunId × Cfg.Fun) → Option (FunId × Nat)
  | [] => none
  | (f, fd) :: rest =>
    match fd.blocks.zipIdx.find? (fun (b, _) => !blockSwitchOk T b) with
    | some (_, i) => some (f, i)
    | none => badSwitch T rest

/-- `switchesOk`, with where it fails. -/
def checkSwitches (P : Cfg.Program) : Except SwitchError Unit :=
  if switchesOk P then pure ()
  else if !pinsApart P.known then throw .pins
  else
    match badSwitch (tables P) P.funs.toList with
    | some (f, b) => throw (.dispatch f b)
    | none => throw (.dispatch 0 0)

theorem checkSwitches_ok {P : Cfg.Program} (h : checkSwitches P = .ok ()) : switchesOk P = true := by
  unfold checkSwitches at h
  split at h
  · assumption
  · split at h
    · cases h
    · split at h <;> cases h

end IxCC.Rt
