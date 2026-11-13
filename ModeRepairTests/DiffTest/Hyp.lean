import IxC.Resource

/-! # Decision procedures for the statement's hypotheses (MT)

`inputsOkB` transcribes `InputsOk` (Statement.lean:177-284) and `externCallOkB`
transcribes `ExternOk`'s clauses (Statement.lean:288-321) for one call. They are
the tester's own, independent of its generator: every generated input and every
extern call a run makes is decided here. Heaps are walked with explicit fuel; on
an input heap (acyclic, `HeapOk`) the walks terminate well inside it. -/

namespace MT.DiffTest

open IxC.Resource Ixon

/-- The statement this tree has: repairs I (an extern's fresh reference carries its cell's
capability; its new cells' capabilities are below its counter) and K (`ArgOk`'s class and skeleton
clauses only at a non-erased parameter). On the findings branch (`jcb/ixcc-mode-findings`) this flag
was written per tree under test (`DiffTest/Stmt.lean`, by `dt.sh sync`); here the tester builds
against this tree only, so it is fixed. -/
def stmtV2 : Bool := true

def walkFuel : Nat := 4096

def objAt (h : Heap) (l : Nat) : Option Obj := h.objs[l]?

/-- The locations `Reach h v` reaches (`Reach.here` holds even with no cell there). -/
def reachSet (h : Heap) : Nat → Val → List Nat
  | 0, _ => []
  | _ + 1, .imm _ => []
  | n + 1, .ref loc _ _ =>
    loc :: match objAt h loc with
      | some o => o.cell.vals.flatMap (reachSet h n)
      | none => []

def reaches (h : Heap) (v : Val) (l : Nat) : Bool := (reachSet h walkFuel v).contains l

def notLeafCell (o : Obj) : Bool := o.cell.isNum == false || natClass != .leaf

/-- The locations `OwnReach P h v` reaches. -/
def ownSet (P : Prog) (h : Heap) : Nat → Val → List Nat
  | 0, _ => []
  | _ + 1, .imm _ => []
  | n + 1, .ref loc _ _ =>
    match objAt h loc with
    | none => []
    | some o =>
      let here := if notLeafCell o then [loc] else []
      here ++ (ownedSlots P o.cell).flatMap fun i =>
        match o.cell.slot? i with
        | some sv => ownSet P h n sv
        | none => []

def ownReaches (P : Prog) (h : Heap) (v : Val) (l : Nat) : Bool := (ownSet P h walkFuel v).contains l

def valOk (h : Heap) : Val → Bool
  | .imm _ => true
  | .ref loc cap t => t.isEmpty && match objAt h loc with
    | some o => o.cap == cap
    | none => false

def inputCell (P : Prog) : Cell → Bool
  | .ctor .. | .num _ | .str _ => true
  | .pap r args => (papSkel P r args.size).isSome
  | .clo .. | .once .. => false

def heapOk (P : Prog) (h : Heap) : Bool :=
  (List.range h.objs.size).all fun loc =>
    match objAt h loc with
    | none => true
    | some o => inputCell P o.cell && decide (o.cap < h.nextCap) &&
        o.cell.vals.all fun v => valOk h v && !reaches h v loc

def papArgOk (h : Heap) : Val → Bool
  | .imm _ => true
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => o.cell.isNum
    | none => false

def closureAt (P : Prog) (h : Heap) (s : Skel) : Val → Bool
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => match o.cell with
      | .pap r args => args.all (papArgOk h) && match papSkel P r args.size with
        | some sk => s.admits sk
        | none => false
      | _ => false
    | none => false
  | .imm _ => false

def defaultPaps (P : Prog) (h : Heap) (v : Val) : Bool :=
  (reachSet h walkFuel v).all fun l =>
    match objAt h l with
    | some o => match o.cell with
      | .pap r args => args.all (papArgOk h) && match papSkel P r args.size with
        | some sk => sk.isDefault
        | none => false
      | _ => true
    | none => true

def isIrr (v : Val) : Bool := v == .imm .irr

def isImm : Val → Bool
  | .imm _ => true
  | _ => false

def isFreshNum (h : Heap) : Val → Bool
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => o.cell.isNum
    | none => false
  | .imm _ => false

def argOk (P : Prog) (h : Heap) (p : Param) (a : Val) : Bool :=
  valOk h a &&
  (p.mode != .erased || isIrr a) &&
  -- repair K (stmtV2): the class and skeleton clauses only at a non-erased parameter
  ((stmtV2 && p.mode == .erased) ||
    ((p.cls != .irr || isIrr a) &&
    (p.cls != .imm || isImm a) &&
    (p.cls != .leaf || isFreshNum h a) &&
    (match p.skel with
      | .arrow .. => closureAt P h p.skel a
      | _ => defaultPaps P h a)))

/-- `OwnTree`: no location is held by two distinct owned slots inside `v`'s
ownership closure (a leaf location excepted). -/
def ownTree (P : Prog) (h : Heap) (v : Val) : Bool := Id.run do
  let mut seen : List (Nat × Nat × Nat) := []  -- (target, holder, slot)
  for p in (ownSet P h walkFuel v).eraseDups do
    let some o := objAt h p | continue
    for i in ownedSlots P o.cell do
      match o.cell.slot? i with
      | some (.ref l _ _) =>
        let leafTarget := match objAt h l with
          | some ol => !notLeafCell ol
          | none => false
        if leafTarget then continue
        if seen.any fun (l', p', i') => l' == l && (p' != p || i' != i) then return false
        seen := (l, p, i) :: seen
      | _ => pure ()
  return true

/-- **`InputsOk`**, decided. -/
def inputsOkB (P : Prog) (h : Heap) (params : Array Param) (args : List Val) : Bool :=
  args.length == params.size && heapOk P h &&
  (List.range args.length).all fun i =>
    match params[i]?, args[i]? with
    | some p, some a =>
      argOk P h p a &&
      (!p.mode.isUnique || (ownTree P h a &&
        (List.range args.length).all fun j =>
          j == i || match args[j]? with
            | some b => (ownSet P h walkFuel a).all fun l => !reaches h b l
            | none => true))
    | _, _ => false

/-- Why `inputsOkB` fails (diagnostics). -/
def inputsWhy (P : Prog) (h : Heap) (params : Array Param) (args : List Val) : String := Id.run do
  if args.length != params.size then return "length"
  if !heapOk P h then return "heapOk"
  for i in List.range args.length do
    match params[i]?, args[i]? with
    | some p, some a =>
      if !argOk P h p a then return s!"argOk at {i} ({repr p})"
      if p.mode.isUnique && !ownTree P h a then return s!"ownTree at {i}"
    | _, _ => return "index"
  return "disjointness"

/-! ## Externs: one call against `ExternOk`'s clauses -/

def heldBy (h : Heap) (a v : Val) : Bool :=
  v == a || (reachSet h walkFuel a).any fun l =>
    match objAt h l with
    | some o => o.cell.vals.contains v
    | none => false

/-- `ExternVal ps args h h' v`. Repair I (stmtV2): a fresh reference is to a cell
of `h'` and carries that cell's capability. -/
def externVal (ps : Array Param) (args : List Val) (h h' : Heap) (v : Val) : Bool :=
  isImm v ||
  (match v with
    | .ref loc cap t => t.isEmpty && decide (h.objs.size ≤ loc) &&
        (!stmtV2 || match objAt h' loc with
          | some o => o.cap == cap
          | none => false)
    | _ => false) ||
  (List.range args.length).any fun i =>
    match ps[i]?, args[i]? with
    | some p, some a => !p.mode.isBorrowed && !p.mode.isUnique && heldBy h a v
    | _, _ => false

partial def termEq : Term → Term → Bool
  | .irr, .irr => true
  | .var i c, .var i' c' => i == i' && c == c'
  | .const r c, .const r' c' => r == r' && c == c'
  | .app f a c, .app f' a' c' => termEq f f' && termEq a a' && c == c'
  | .lam p r rc fv b, .lam p' r' rc' fv' b' => p == p' && r == r' && rc == rc' && fv == fv' && termEq b b'
  | .letE m d v b, .letE m' d' v' b' => m == m' && d == d' && termEq v v' && termEq b b'
  | .case k mj as ex c, .case k' mj' as' ex' c' =>
    k == k' && termEq mj mj' && c == c' && as.size == as'.size && ex.size == ex'.size &&
      (as.zip as').all (fun (x, y) => termEq x y) && (ex.zip ex').all (fun (x, y) => termEq x y)
  | .natLit n, .natLit n' => n == n'
  | .strLit s, .strLit s' => s == s'
  | .proj s i e c, .proj s' i' e' c' => s == s' && i == i' && termEq e e' && c == c'
  | _, _ => false

/-- Old cells compared by shape and values (closures by their terms too). -/
def sameCell : Cell → Cell → Bool
  | .clo env p r rc fv b, .clo env' p' r' rc' fv' b' =>
    env.length == env'.length && (env.zip env').all (fun (x, y) => x.val == y.val && x.mode == y.mode) &&
      p == p' && r == r' && rc == rc' && fv == fv' && termEq b b'
  | .ctor r fs, .ctor r' fs' => r == r' && fs == fs'
  | .num n, .num n' => n == n'
  | .str s, .str s' => s == s'
  | .pap r as, .pap r' as' => r == r' && as == as'
  | .once t sp, .once t' sp' => t == t' && sp == sp'
  | _, _ => false

/-- **`ExternOk`'s clauses for one call** of extern `r` with interface
`ps res rc`, arguments `args`, heaps `h → h'`, result `v`. -/
def externCallOkB (P : Prog) (ps : Array Param) (res : ResultMode) (rc : Cls) (args : List Val)
    (h h' : Heap) (v : Val) : Bool :=
  decide (h.objs.size ≤ h'.objs.size) && decide (h.nextCap ≤ h'.nextCap) &&
  ((List.range h.objs.size).all fun l =>
    match objAt h l, objAt h' l with
    | some o, some o' =>
      (sameCell o'.cell o.cell && o'.cap == o.cap) ||
      (decide (h.nextCap ≤ o'.cap) && (List.range args.length).any fun i =>
        match ps[i]?, args[i]? with
        | some p, some a => p.mode.isUnique && ownReaches P h a l
        | _, _ => false)
    | some _, none => false
    | none, _ => true) &&
  ((List.range h'.objs.size).all fun l =>
    if l < h.objs.size then true else match objAt h' l with
      | some o => inputCell P o.cell && (!stmtV2 || decide (o.cap < h'.nextCap)) &&
          o.cell.vals.all (externVal ps args h h')
      | none => true) &&
  externVal ps args h h' v &&
  (rc != .irr || isIrr v) && (rc != .imm || isImm v) && (rc != .leaf || isFreshNum h' v) &&
  (!(res.isUnique && rc == .val) ||
    (match v with
      | .ref loc _ t => t.isEmpty && decide (h.objs.size ≤ loc)
      | _ => false) &&
    ownTree P h' v &&
    (ownSet P h' walkFuel v).all fun l => decide (h.objs.size ≤ l) &&
      (List.range h'.objs.size).all fun l₂ =>
        ownReaches P h' v l₂ || match objAt h' l₂ with
          | some o₂ => o₂.cell.vals.all fun w => !reaches h' w l
          | none => true)

/-! ## SplitMix64 -/

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- The generator of case `i` of seed `s`. -/
def Rng.ofCase (s i : Nat) : Rng :=
  let (a, _) := (Rng.mk (UInt64.ofNat s)).next
  let (b, _) := (Rng.mk (a ^^^ UInt64.ofNat (i * 0x632BE59BD9B4E019))).next
  ⟨b⟩

end MT.DiffTest
