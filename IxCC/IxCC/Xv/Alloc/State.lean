import IxCC.Xv.Alloc.Liveness
import IxCC.Xv.Alloc.ParMove
import IxCC.Xv.XlSemantics

/-!
# The allocator's machine state (untrusted)

Where each live register is during allocation: at most one machine register
(`occ`/`reg`), and whether its home cell already holds it (`home`). The
home of a register is its own frame slot, or, for a stack parameter, its
incoming cell. Registers are the allocatable set of 05 §6: every
general-purpose register except `rsp`, `rbp` and the context register
`r15` (`Xv.scratch`).

Also the chaos control plane (05 §12 item 3): seeded perturbations of
register order, hints, spill choice, split points and the move scratch. A
disabled `Chaos` is the deterministic allocator.
-/

namespace IxCC.Xv.Alloc

open IxCC.Lir (VReg Label)

structure RState where
  occ : Array (Option VReg) := Array.replicate 16 none
  reg : Std.HashMap VReg X86.GPR := {}
  home : Std.HashSet VReg := {}
  deriving Inhabited

namespace RState

def get (s : RState) (r : X86.GPR) : Option VReg := (s.occ[gprIndex r]?).join

def isFree (s : RState) (r : X86.GPR) : Bool := (s.get r).isNone

/-- Put `v` in register `r` (which must be free), leaving any other register
it was in. -/
def put (s : RState) (v : VReg) (r : X86.GPR) : RState :=
  let s := match s.reg[v]? with
    | some r0 => { s with occ := s.occ.set! (gprIndex r0) none }
    | none => s
  { s with occ := s.occ.set! (gprIndex r) (some v), reg := s.reg.insert v r }

/-- Empty register `r`. -/
def drop (s : RState) (r : X86.GPR) : RState :=
  match s.get r with
  | some v => { s with occ := s.occ.set! (gprIndex r) none, reg := s.reg.erase v }
  | none => s

/-- Keep only the registers `keep` accepts. -/
def restrict (s : RState) (keep : VReg → Bool) : RState :=
  { occ := s.occ.map fun o => o.filter keep
    reg := s.reg.filter fun v _ => keep v
    home := s.home.filter keep }

/-- Every register the state holds. -/
def values (s : RState) : List VReg :=
  let rs := s.reg.toList.map (·.1)
  rs ++ (s.home.toList.filter fun v => !s.reg.contains v)

end RState

/-! ## Chaos -/

/-- Perturbation rates in percent; zero everywhere is the deterministic
allocator. -/
structure Chaos where
  seed : UInt64 := 0
  /-- Shuffle the register preference order. -/
  shuffle : Bool := false
  /-- Ignore a register hint. -/
  ignoreHint : Nat := 0
  /-- Pick a random eviction victim. -/
  randomVictim : Nat := 0
  /-- Evict an unrelated live register before an instruction (a split). -/
  extraSpill : Nat := 0
  /-- Read an `any` use from its home even when it is in a register. -/
  homeUse : Nat := 0
  /-- Define an `any` definition straight into its home. -/
  homeDef : Nat := 0
  /-- Place a live register in its home only at a block entry. -/
  entryHome : Nat := 0
  /-- Store a definition to its home right away. -/
  spillAtDef : Nat := 0
  /-- Pretend no register is free when resolving parallel moves (forcing
  the extra slot and the victim). -/
  noFreeScratch : Nat := 0
  /-- Prefer only the first `regLimit` registers of the order. -/
  regLimit : Nat := 13
  deriving Repr, Inhabited

def Chaos.enabled (c : Chaos) : Bool :=
  c.shuffle || c.ignoreHint + c.randomVictim + c.extraSpill + c.homeUse + c.homeDef + c.entryHome +
    c.spillAtDef + c.noFreeScratch > 0 || c.regLimit < 13

/-- SplitMix64. -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- A chaos configuration drawn from `seed`: each knob on with its own
rate, so every seed stresses a different mix. -/
def Chaos.ofSeed (seed : UInt64) : Chaos :=
  let r (k : UInt64) (m : Nat) : Nat := (mix64 (seed + k * 0x9e3779b97f4a7c15)).toNat % m
  { seed
    shuffle := r 1 2 == 0
    ignoreHint := [0, 20, 60][r 2 3]!
    randomVictim := [0, 30, 100][r 3 3]!
    extraSpill := [0, 5, 20][r 4 3]!
    homeUse := [0, 25, 75][r 5 3]!
    homeDef := [0, 25, 75][r 6 3]!
    entryHome := [0, 30, 80][r 7 3]!
    spillAtDef := [0, 20, 60][r 8 3]!
    noFreeScratch := [0, 50, 100][r 9 3]!
    regLimit := [13, 8, 5, 3][r 10 4]! }

/-- The default register preference: caller-saved first (no save cost),
then callee-saved. -/
def defaultOrder : List X86.GPR :=
  [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rbx, .r12, .r13, .r14]

def calleeSavedRegs : List X86.GPR := [.rbx, .r12, .r13, .r14]

/-- Caller-saved registers preserved by the plain-RC runtime wrappers
(`rc_marker_inc1`, `rc_marker_dec`, `rc_publish_*`). -/
def rcSavedRegs : List X86.GPR := [.r8, .r9, .r10]

/-- Preference order for values live across calls: callee-saved first, then
RC-wrapper-saved (`r8`, `r9`, `r10`), then `rcx`, `rdx` (preserved by
`rc_marker_inc1`), then `rsi`, `rdi`, `rax`, `r11`. -/
def crossCallOrder : List X86.GPR :=
  [.rbx, .r12, .r13, .r14, .r8, .r9, .r10, .rcx, .rdx, .rsi, .rdi, .rax, .r11]

end IxCC.Xv.Alloc
