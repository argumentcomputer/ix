import Ix.Ixon

/-!
# Formers declared at a definition, on a compiled corpus

`ixvm-alias-formers` (manual) reads an `.ixe` file (`IX_ALIAS_IXE`) and writes `summary.txt`
and `families.tsv` to `IX_ALIAS_OUT`. Nothing is run through the program: the measurements
are of the records.

Every inductive member of every block record is read; a member whose declared former is not
`nP + nI` syntactic `∀`s into a sort (`former_is_tele` fails) is walked as the native check
walks it:

* `former_tele_at`: a syntactic `∀` is kept, a position that is not one is head-normalized and
  must be a `∀`; after `nP + nI` binders the residual is head-normalized once more, as
  `get_result_sort_level` reads the result sort there;
* `get_result_sort_level`: head normalization before every binder and at the end, which must
  give a sort; its binders and level are compared with the first walk's.

Head normalization is transcribed as δ of definitions (kind `definition`; theorems and opaque
constants are not unfolded), β and ζ, and every step is logged. The program's `whnf` also
reduces projections, recursors, quotients and the primitive operations, shortcuts a
projection-shaped definition, and takes β at a λ whose datum may be zero only with a
certificate (the argument's type convertible with the domain): the log counts the unfolded
definitions of projection shape, the β steps at such λs and the unfoldings whose level count
differs from the definition's (the program does not unfold those).

Each member is also read for: its leading syntactic `∀`s, a `let` among the first `nP + nI`
positions of the declared spine (before head normalization), its constructors' occurrences of
the family (the native route's reading), and, from every standalone recursor record, whether
the family it eliminates has a former that is not a telescope (the flag an earlier measurement
of the recursors used), to compare the two enumerations.
-/

namespace Tests.Ix.IxVM.AliasFormers

abbrev E := Ixon.Expr

def tsvLine (xs : List String) : String := "\t".intercalate xs

def b2s (b : Bool) : String := if b then "1" else "0"

def clip (s : String) (n : Nat := 400) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "…"

/-! ## Expanding a record: shares replaced by their entries, each binder with its datum -/

inductive AE where
  | sort (u : UInt64)
  | var (i : UInt64)
  | ref (i : UInt64) (us : Array UInt64)
  | recur (i : UInt64) (us : Array UInt64)
  | prj (t i : UInt64) (e : AE)
  | str (i : UInt64)
  | nat (i : UInt64)
  | app (f a : AE)
  | lam (d : Ixon.BinderNode) (t b : AE)
  | all (d : Ixon.BinderNode) (t b : AE)
  | letE (nd : Bool) (m : Ixon.LetMode) (t v b : AE)
  deriving Inhabited

partial def hasBinderUnder (full : Array Bool) : Ixon.Expr → Bool
  | .lam .. => true
  | .all .. => true
  | .app f a => hasBinderUnder full f || hasBinderUnder full a
  | .letE _ _ t v b => hasBinderUnder full t || hasBinderUnder full v || hasBinderUnder full b
  | .prj _ _ v => hasBinderUnder full v
  | .share n => full[n.toNat]?.getD false
  | _ => false

/-- Per sharing entry, whether it has a binder (through its own shares). -/
def binderful (sharing : Array Ixon.Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (hasBinderUnder out e)) #[]

structure ExpandCx where
  sharing : Array Ixon.Expr
  full : Array Bool
  blocks : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode)
  /-- the largest expanded tree accepted, in nodes -/
  cap : Nat

abbrev ExpandM := StateT (Std.HashMap (Nat × Nat) (AE × Nat)) (Except String)

/-- `e` expanded with the nodes of its block from `pos` on: the tree, its size, and the
position after its own nodes. -/
def expand (cx : ExpandCx) : Nat → Ixon.Expr → Array Ixon.BinderNode → Nat →
    ExpandM (AE × Nat × Nat)
  | 0, _, _, _ => throw "the expansion ran out of depth"
  | fuel + 1, e, nodes, pos => do
    match e with
    | .sort u => return (.sort u, 1, pos)
    | .var i => return (.var i, 1, pos)
    | .ref i us => return (.ref i us, 1, pos)
    | .recur i us => return (.recur i us, 1, pos)
    | .str i => return (.str i, 1, pos)
    | .nat i => return (.nat i, 1, pos)
    | .prj t i v =>
      let (v', s, p) ← expand cx fuel v nodes pos
      return (.prj t i v', s + 1, p)
    | .app f a =>
      let (f', s1, p1) ← expand cx fuel f nodes pos
      let (a', s2, p2) ← expand cx fuel a nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.app f' a', s1 + s2 + 1, p2)
    | .lam t b =>
      let some d := nodes[pos]? | throw "binder data: a block is shorter than its expression"
      if let .share _ := d then throw "binder data: a share node at a binder"
      let (t', s1, p1) ← expand cx fuel t nodes (pos + 1)
      let (b', s2, p2) ← expand cx fuel b nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.lam d t' b', s1 + s2 + 1, p2)
    | .all t b =>
      let some d := nodes[pos]? | throw "binder data: a block is shorter than its expression"
      if let .share _ := d then throw "binder data: a share node at a binder"
      let (t', s1, p1) ← expand cx fuel t nodes (pos + 1)
      let (b', s2, p2) ← expand cx fuel b nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.all d t' b', s1 + s2 + 1, p2)
    | .letE nd m t v b =>
      let (t', s1, p1) ← expand cx fuel t nodes pos
      let (v', s2, p2) ← expand cx fuel v nodes p1
      let (b', s3, p3) ← expand cx fuel b nodes p2
      if s1 + s2 + s3 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.letE nd m t' v' b', s1 + s2 + s3 + 1, p3)
    | .share n =>
      let i := n.toNat
      let some entry := cx.sharing[i]? | throw "a share names no entry"
      if cx.full[i]?.getD false then
        let some (.share v) := nodes[pos]? | throw "binder data: no share node at a share"
        let key := (i, v.toNat)
        match (← get)[key]? with
        | some (ae, s) => return (ae, s, pos + 1)
        | none =>
          let some sub := cx.blocks[(true, i, v.toNat)]? | throw "binder data: a variant is missing"
          let (ae, s, p) ← expand cx fuel entry sub 0
          unless p == sub.size do throw "binder data: a variant has unused nodes"
          modify (·.insert key (ae, s))
          return (ae, s, pos + 1)
      else
        let key := (i, 0)
        match (← get)[key]? with
        | some (ae, s) => return (ae, s, pos)
        | none =>
          let (ae, s, _) ← expand cx fuel entry #[] 0
          modify (·.insert key (ae, s))
          return (ae, s, pos)

def expandRoot (cx : ExpandCx) (root : Nat) (e : Ixon.Expr) : ExpandM AE := do
  let nodes := cx.blocks.getD (false, root, 0) #[]
  let (ae, _, p) ← expand cx (1 <<< 20) e nodes 0
  unless p == nodes.size do throw "binder data: a root block has unused nodes"
  return ae

/-! ## Resolved terms -/

/-- A binder datum as a zero set: `none` never zero, `some ps` zero exactly when every
parameter of `ps` is (ascending; empty: always zero). -/
abbrev Datum := Option (Array Nat)

inductive RE where
  | bvar (i : Nat)
  | sort (u : Ixon.Univ)
  | const (a : Address) (us : Array Ixon.Univ)
  | lit (str : Bool) (a : Address)
  | app (f a : RE)
  | lam (d : Datum) (t b : RE)
  | all (d : Datum) (t b : RE)
  | letE (t v b : RE)
  | prj (s : Address) (i : Nat) (e : RE)
  deriving BEq, Inhabited

def univInst (us : Array Ixon.Univ) : Ixon.Univ → Ixon.Univ
  | .zero => .zero
  | .succ u => .succ (univInst us u)
  | .max a b => .max (univInst us a) (univInst us b)
  | .imax a b => .imax (univInst us a) (univInst us b)
  | .var i => us[i.toNat]?.getD (.var i)

def unionAsc (a b : Array Nat) : Array Nat :=
  ((a ++ b).qsort (· < ·)).toList.eraseDups.toArray

def zeroSet : Ixon.Univ → Datum
  | .zero => some #[]
  | .succ _ => none
  | .var i => some #[i.toNat]
  | .max a b =>
    match zeroSet a, zeroSet b with
    | some x, some y => some (unionAsc x y)
    | _, _ => none
  | .imax _ b => zeroSet b

/-- A datum `ifAllZero ps` is the level `max (u p₁) … (u pₖ)`: at levels `us` its zero set. -/
def datumInst (us : Array Ixon.Univ) : Datum → Datum
  | none => none
  | some ps => ps.foldl (init := some #[]) fun acc p =>
    match acc, zeroSet (us[p]?.getD (.var p.toUInt64)) with
    | some x, some y => some (unionAsc x y)
    | _, _ => none

namespace RE

/-- Add `n` to every variable at or above `k`. -/
partial def liftGo (n : Nat) : Nat → RE → RE
  | k, .bvar i => if i ≥ k then .bvar (i + n) else .bvar i
  | k, .app f a => .app (liftGo n k f) (liftGo n k a)
  | k, .lam d t b => .lam d (liftGo n k t) (liftGo n (k + 1) b)
  | k, .all d t b => .all d (liftGo n k t) (liftGo n (k + 1) b)
  | k, .letE t v b => .letE (liftGo n k t) (liftGo n k v) (liftGo n (k + 1) b)
  | k, .prj s i e => .prj s i (liftGo n k e)
  | _, e => e

def lift (n k : Nat) (e : RE) : RE := if n == 0 then e else liftGo n k e

/-- Substitute `v` for the variable `k`; variables above it move down. -/
partial def inst (v : RE) : Nat → RE → RE
  | k, .bvar i => if i == k then RE.lift k 0 v else if i > k then .bvar (i - 1) else .bvar i
  | k, .app f a => .app (inst v k f) (inst v k a)
  | k, .lam d t b => .lam d (inst v k t) (inst v (k + 1) b)
  | k, .all d t b => .all d (inst v k t) (inst v (k + 1) b)
  | k, .letE t x b => .letE (inst v k t) (inst v k x) (inst v (k + 1) b)
  | k, .prj s i e => .prj s i (inst v k e)
  | _, e => e

partial def hasBVar : Nat → RE → Bool
  | k, .bvar i => i == k
  | k, .app f a => hasBVar k f || hasBVar k a
  | k, .lam _ t b => hasBVar k t || hasBVar (k + 1) b
  | k, .all _ t b => hasBVar k t || hasBVar (k + 1) b
  | k, .letE t v b => hasBVar k t || hasBVar k v || hasBVar (k + 1) b
  | k, .prj _ _ e => hasBVar k e
  | _, _ => false

/-- A constant at `t`, anywhere (a projection's structure aside). -/
partial def mentions (t : Address) : RE → Bool
  | .const c _ => c == t
  | .app f a => mentions t f || mentions t a
  | .lam _ d b => mentions t d || mentions t b
  | .all _ d b => mentions t d || mentions t b
  | .letE d v b => mentions t d || mentions t v || mentions t b
  | .prj _ _ e => mentions t e
  | _ => false

partial def hasLet : RE → Bool
  | .letE .. => true
  | .app f a => hasLet f || hasLet a
  | .lam _ d b => hasLet d || hasLet b
  | .all _ d b => hasLet d || hasLet b
  | .prj _ _ e => hasLet e
  | _ => false

partial def spine : RE → RE × Array RE
  | .app f a =>
    let (h, as) := spine f
    (h, as.push a)
  | e => (e, #[])

partial def instLevels (us : Array Ixon.Univ) : RE → RE
  | .sort u => .sort (univInst us u)
  | .const a ls => .const a (ls.map (univInst us))
  | .app f a => .app (instLevels us f) (instLevels us a)
  | .lam d t b => .lam (datumInst us d) (instLevels us t) (instLevels us b)
  | .all d t b => .all (datumInst us d) (instLevels us t) (instLevels us b)
  | .letE t v b => .letE (instLevels us t) (instLevels us v) (instLevels us b)
  | .prj s i e => .prj s i (instLevels us e)
  | e => e

partial def fmtU : Ixon.Univ → String
  | .zero => "0"
  | .succ u => "(" ++ fmtU u ++ "+1)"
  | .max a b => "max(" ++ fmtU a ++ "," ++ fmtU b ++ ")"
  | .imax a b => "imax(" ++ fmtU a ++ "," ++ fmtU b ++ ")"
  | .var i => "u" ++ toString i

def fmtD : Datum → String
  | none => "n"
  | some ps => "z" ++ toString ps.toList

partial def fmt (nm : Address → String) : Nat → RE → String
  | 0, _ => "…"
  | n + 1, e =>
    match e with
    | .bvar i => "#" ++ toString i
    | .sort u => "Sort " ++ fmtU u
    | .const a us =>
      if us.isEmpty then nm a else nm a ++ ".{" ++ ",".intercalate (us.toList.map fmtU) ++ "}"
    | .lit s a => (if s then "str:" else "nat:") ++ String.ofList ((toString a).toList.take 8)
    | .app f a => "(" ++ fmt nm n f ++ " " ++ fmt nm n a ++ ")"
    | .lam d t b => "(λ[" ++ fmtD d ++ "] " ++ fmt nm n t ++ ", " ++ fmt nm n b ++ ")"
    | .all d t b => "(∀[" ++ fmtD d ++ "] " ++ fmt nm n t ++ ", " ++ fmt nm n b ++ ")"
    | .letE t v b => "(let " ++ fmt nm n t ++ " := " ++ fmt nm n v ++ "; " ++ fmt nm n b ++ ")"
    | .prj s i x => fmt nm n x ++ "." ++ nm s ++ "." ++ toString i

end RE

def appN (f : RE) (args : List RE) : RE := args.foldl RE.app f

/-- The variables `o + n - 1, …, o`. -/
def psAt (o n : Nat) : List RE := (List.range n).map fun k => RE.bvar (o + n - 1 - k)

/-- The levels `u_off, …, u_(off + n - 1)`. -/
def lpsOf (off n : Nat) : Array Ixon.Univ :=
  (Array.range n).map fun i => Ixon.Univ.var (off + i).toUInt64

/-! ## Reading records -/

def datumOf : Ixon.BinderNode → Except String Datum
  | .never _ => .ok none
  | .zero _ => .ok (some #[])
  | .ifAllZero ps _ => .ok (some (ps.map (·.toNat)))
  | .undecided _ => .error "an undecided binder datum"
  | .share _ => .error "a share node at a binder"

structure RCx where
  refs : Array Address
  univs : Array Ixon.Univ
  recur : Array Address

def RCx.univ (cx : RCx) (i : UInt64) : Except String Ixon.Univ :=
  match cx.univs[i.toNat]? with
  | some u => .ok u
  | none => .error "a level index out of range"

def RCx.ref (cx : RCx) (i : UInt64) : Except String Address :=
  match cx.refs[i.toNat]? with
  | some a => .ok a
  | none => .error "a reference index out of range"

partial def resolve (cx : RCx) : AE → Except String RE
  | .sort u => do return .sort (← cx.univ u)
  | .var i => pure (.bvar i.toNat)
  | .ref i us => do return .const (← cx.ref i) (← us.mapM cx.univ)
  | .recur i us => do
    let some a := cx.recur[i.toNat]? | throw "a recursive reference out of range"
    return .const a (← us.mapM cx.univ)
  | .prj t i e => do return .prj (← cx.ref t) i.toNat (← resolve cx e)
  | .str i => do return .lit true (← cx.ref i)
  | .nat i => do return .lit false (← cx.ref i)
  | .app f a => do return .app (← resolve cx f) (← resolve cx a)
  | .lam d t b => do return .lam (← datumOf d) (← resolve cx t) (← resolve cx b)
  | .all d t b => do return .all (← datumOf d) (← resolve cx t) (← resolve cx b)
  | .letE _ _ t v b => do return .letE (← resolve cx t) (← resolve cx v) (← resolve cx b)

def expandCxOf (c : Ixon.Constant) (cap : Nat) : ExpandCx :=
  { sharing := c.sharing, full := binderful c.sharing, cap := cap,
    blocks := c.binders.foldl
      (fun m b => m.insert (b.shared, b.index.toNat, b.variant.toNat) b.nodes) {} }

/-- Roots of a record (number, expression), expanded and resolved. -/
def readRoots (c : Ixon.Constant) (cx : RCx) (roots : Array (Nat × E)) (cap : Nat) :
    Except String (Array RE) := do
  let ecx := expandCxOf c cap
  let act : ExpandM (Array AE) := roots.mapM fun (r, e) => expandRoot ecx r e
  let (aes, _) ← act.run {}
  aes.mapM (resolve cx)

def memberRoots : Ixon.MutConst → Nat
  | .defn _ => 2
  | .indc i => i.ctors.size + 1
  | .recr r => r.rules.size + 1

def rootOffset (ms : Array Ixon.MutConst) (idx : Nat) : Nat :=
  (ms.extract 0 idx).foldl (fun n m => n + memberRoots m) 0

def projAddr (info : Ixon.ConstantInfo) : Address :=
  Address.blake3 (Ixon.ser ({ info, sharing := #[], refs := #[], univs := #[], binders := #[] } :
    Ixon.Constant))

def iprjAddr (block : Address) (idx : Nat) : Address := projAddr (.iPrj ⟨idx.toUInt64, block⟩)

/-- The projection of each member, by its kind. -/
def recurOf (block : Address) (ms : Array Ixon.MutConst) : Array Address :=
  (Array.range ms.size).map fun i =>
    match ms[i]? with
    | some (.defn _) => projAddr (.dPrj ⟨i.toUInt64, block⟩)
    | some (.recr _) => projAddr (.rPrj ⟨i.toUInt64, block⟩)
    | _ => projAddr (.iPrj ⟨i.toUInt64, block⟩)

/-- The value and level count of the definition (kind `definition`) at `a`, resolved. -/
def defnInfo (env : Ixon.Env) (a : Address) (cap : Nat) : Except String (Option (RE × Nat)) := do
  let some c := env.getConst? a | return none
  match c.info with
  | .defn d =>
    let .defn := d.kind | return none
    let rs ← readRoots c { refs := c.refs, univs := c.univs, recur := #[a] } #[(1, d.value)] cap
    return rs[0]?.map fun v => (v, d.lvls.toNat)
  | .dPrj p =>
    let some bc := env.getConst? p.block | return none
    let .muts ms := bc.info | return none
    let some (Ixon.MutConst.defn d) := ms[p.idx.toNat]? | return none
    let .defn := d.kind | return none
    let off := rootOffset ms p.idx.toNat
    let rs ← readRoots bc { refs := bc.refs, univs := bc.univs, recur := recurOf p.block ms }
      #[(off + 1, d.value)] cap
    return rs[0]?.map fun v => (v, d.lvls.toNat)
  | _ => return none

def kindName : Ix.DefKind → String
  | .defn => "definition"
  | .opaq => "opaque"
  | .thm => "theorem"

/-- The kind of the constant at `a`. -/
def constKind (env : Ixon.Env) (a : Address) : String :=
  match env.getConst? a with
  | none => "missing"
  | some c =>
    match c.info with
    | .defn d => kindName d.kind
    | .dPrj p =>
      match env.getConst? p.block with
      | some bc =>
        match bc.info with
        | .muts ms =>
          match ms[p.idx.toNat]? with
          | some (Ixon.MutConst.defn d) => kindName d.kind
          | _ => "other"
        | _ => "other"
      | none => "missing"
    | .iPrj _ => "inductive"
    | .cPrj _ => "constructor"
    | .rPrj _ => "recursor"
    | .recr _ => "recursor"
    | .axio _ => "axiom"
    | .quot _ => "quotient"
    | .muts _ => "block"

/-- A value `λ x₁ … xₖ, xᵢ.j` (the shape the program's projection-definition shortcut reads). -/
partial def projShape : Nat → RE → Bool
  | n, .lam _ _ b => projShape (n + 1) b
  | n, .prj _ _ (.bvar i) => decide (i < n)
  | _, _ => false

/-! ## Head normalization, transcribed, with a log of its steps -/

structure WLog where
  deltas : Array Address := #[]
  betas : Nat := 0
  /-- β steps at a λ whose datum may be zero: the program takes them with a certificate -/
  betaCert : Nat := 0
  zetas : Nat := 0
  /-- δ steps whose level count differs from the definition's -/
  lvlMismatch : Nat := 0
  /-- unfolded definitions of projection shape -/
  projDefs : Array Address := #[]
  deriving Inhabited

def fuelW : Nat := 100000

/-- δ of definitions, β, ζ at the head (as `nat_former_tele`'s and `former_tele_at`'s
transcription reads `whnf`), each step logged. -/
partial def whnfL (env : Ixon.Env) (cap : Nat) (fuel : Nat) (lg : WLog) (e : RE) :
    Except String (RE × WLog) := do
  if fuel == 0 then throw "whnf: out of fuel"
  match e with
  | .letE _ v b => whnfL env cap (fuel - 1) { lg with zetas := lg.zetas + 1 } (RE.inst v 0 b)
  | _ =>
    let (h, args) := e.spine
    match h with
    | .lam d _ body =>
      if args.isEmpty then pure (e, lg)
      else
        let lg' := { lg with betas := lg.betas + 1,
                             betaCert := lg.betaCert + (if d.isSome then 1 else 0) }
        whnfL env cap (fuel - 1) lg' (appN (RE.inst args[0]! 0 body) (args.toList.drop 1))
    | .letE _ v b =>
      whnfL env cap (fuel - 1) { lg with zetas := lg.zetas + 1 } (appN (RE.inst v 0 b) args.toList)
    | .const a us =>
      match ← defnInfo env a cap with
      | some (v, nl) =>
        let lg' := { lg with deltas := lg.deltas.push a,
                             lvlMismatch := lg.lvlMismatch + (if us.size == nl then 0 else 1),
                             projDefs := if projShape 0 v then lg.projDefs.push a else lg.projDefs }
        whnfL env cap (fuel - 1) lg' (appN (v.instLevels us) args.toList)
      | none => pure (e, lg)
    | _ => pure (e, lg)

def headDesc (env : Ixon.Env) (nm : Address → String) (e : RE) : String :=
  let (h, args) := e.spine
  let hs := match h with
    | .const a _ => nm a ++ " [" ++ constKind env a ++ "]"
    | .bvar i => "variable #" ++ toString i
    | .sort u => "sort " ++ RE.fmtU u
    | .lit .. => "literal"
    | .lam .. => "λ"
    | .all .. => "∀"
    | .letE .. => "let"
    | .prj .. => "projection"
    | .app .. => "application"
  if args.isEmpty then hs else hs ++ s!" applied to {args.size}"

/-! ## The former's walks -/

def formerIsTele : Nat → RE → Bool
  | 0, .sort _ => true
  | 0, _ => false
  | k + 1, .all _ _ b => formerIsTele k b
  | _, _ => false

partial def leadAlls : RE → Nat
  | .all _ _ b => leadAlls b + 1
  | _ => 0

/-- The positions (below `n`) before which a `let` stands on the declared spine, read
syntactically through `∀`s and `let`s. -/
def synLets (n : Nat) (ty : RE) : Array Nat := Id.run do
  let mut cur := ty
  let mut k := 0
  let mut lets : Array Nat := #[]
  for _ in [0:1000000] do
    if k ≥ n then break
    match cur with
    | .all _ _ b =>
      k := k + 1
      cur := b
    | .letE _ _ b =>
      lets := lets.push k
      cur := b
    | _ => break
  return lets

structure PosRes where
  k : Nat
  /-- `declared` (a syntactic `∀` of the declared type), `whnf` (head-normalized here),
  `unfolded` (a syntactic `∀` of an earlier position's head normal form), `failed` -/
  src : String
  head : String := ""
  log : WLog := {}
  deriving Inhabited

structure WalkRes where
  poss : Array PosRes := #[]
  doms : Array (Datum × RE) := #[]
  /-- empty: `n` binders reached and the residual's head normal form is a sort -/
  err : String := ""
  residual : Option RE := none
  endLog : WLog := {}
  endSort : Option Ixon.Univ := none
  endHead : String := ""
  deriving Inhabited

/-- `former_tele_at` (and, at the end, `get_result_sort_level`'s last step). -/
def teleWalk (env : Ixon.Env) (nm : Address → String) (cap n : Nat) (ty : RE) : WalkRes := Id.run do
  let mut cur := ty
  let mut inWhnf := false
  let mut poss : Array PosRes := #[]
  let mut doms : Array (Datum × RE) := #[]
  for k in [0:n] do
    match cur with
    | .all d t b =>
      poss := poss.push { k := k, src := if inWhnf then "unfolded" else "declared" }
      doms := doms.push (d, t)
      cur := b
    | _ =>
      let hd := headDesc env nm cur
      match whnfL env cap fuelW {} cur with
      | .error e =>
        return { poss := poss.push { k := k, src := "failed", head := hd }, doms := doms,
                 err := s!"position {k}: {e}" }
      | .ok (r, lg) =>
        match r with
        | .all d t b =>
          poss := poss.push { k := k, src := "whnf", head := hd, log := lg }
          doms := doms.push (d, t)
          inWhnf := true
          cur := b
        | _ =>
          return { poss := poss.push { k := k, src := "failed", head := hd, log := lg },
                   doms := doms,
                   err := s!"position {k}: the head normal form is not a ∀ ({headDesc env nm r})" }
  let base : WalkRes := { poss := poss, doms := doms, residual := some cur }
  match whnfL env cap fuelW {} cur with
  | .error e => return { base with err := s!"end: {e}" }
  | .ok (r, lg) =>
    match r with
    | .sort u => return { base with endLog := lg, endSort := some u }
    | _ =>
      let msg := "end: the head normal form is not a sort"
      return { base with endLog := lg, endHead := headDesc env nm r, err := msg }

/-- `get_result_sort_level`: head normalization before every binder and at the end. -/
def resultSortLevel (env : Ixon.Env) (cap n : Nat) (ty : RE) :
    Except String (Ixon.Univ × Array (Datum × RE)) := do
  let mut cur := ty
  let mut doms : Array (Datum × RE) := #[]
  for _ in [0:n] do
    let (w, _) ← whnfL env cap fuelW {} cur
    match w with
    | .all d t b =>
      doms := doms.push (d, t)
      cur := b
    | _ => throw "a position whose head normal form is not a ∀"
  let (w, _) ← whnfL env cap fuelW {} cur
  match w with
  | .sort u => return (u, doms)
  | _ => throw "the end's head normal form is not a sort"

/-! ## Constructors' occurrences of the family (the native route's reading) -/

def peelN : Nat → RE → Except String RE
  | 0, e => pure e
  | n + 1, .all _ _ b => peelN n b
  | _, _ => throw "peel: not a ∀"

def fieldDom (cty : RE) (np i : Nat) : Except String RE := do
  match ← peelN (np + i) cty with
  | .all _ d _ => pure d
  | _ => throw "no field binder"

/-- `nat_positivity`: 0 not reached, 1 recursive, 2 reflexive, 3 not a native occurrence. -/
partial def positivity (e : RE) (t : Address) (lps : Array Ixon.Univ) (np ni o k : Nat) : Nat :=
  match e with
  | .all _ d b => if d.mentions t then 3 else positivity b t lps np ni o (k + 1)
  | _ =>
    let (h, args) := e.spine
    match h with
    | .const c us =>
      if c == t && us == lps && args.size == np + ni then
        if args.toList.take np == psAt (o + k) np && (args.toList.drop np).all (fun a => !a.mentions t)
        then (if k == 0 then 1 else 2) else 3
      else 3
    | _ => 3

/-- `nat_rec_idx`: the recursive and reflexive fields, in order. -/
def recIdxOf (cty : RE) (t : Address) (lps : Array Ixon.Univ) (np ni nf : Nat) :
    Except String (List Nat) := do
  let mut out : Array Nat := #[]
  for i in [0:nf] do
    let dom ← fieldDom cty np i
    let kind := if dom.mentions t then positivity dom t lps np ni i 0 else 0
    if kind == 3 then throw s!"field {i} is not an occurrence the native route reads"
    if kind != 0 then
      if (← peelN (np + i + 1) cty).hasBVar 0 then throw s!"a later binder mentions field {i}"
      out := out.push i
  pure out.toList

/-! ## Per family -/

structure FamRes where
  name : String := ""
  addr : Address := default
  block : Address := default
  oneType : Bool := false
  allInd : Bool := false
  native : Bool := false
  unsafe_ : Bool := false
  lvls : Nat := 0
  np : Nat := 0
  ni : Nat := 0
  nc : Nat := 0
  lead : Nat := 0
  synLets : Array Nat := #[]
  letAnywhere : Bool := false
  walk : WalkRes := {}
  grsl : String := ""
  cls : String := ""
  declared : String := ""
  tele : String := ""
  notes : Array String := #[]
  deriving Inhabited

def FamRes.whnfPoss (f : FamRes) : Array PosRes :=
  f.walk.poss.filter fun p => p.src == "whnf" || p.src == "failed"

def FamRes.residualSort (f : FamRes) : Bool :=
  match f.walk.residual with
  | some (.sort _) => true
  | _ => false

def FamRes.endLevel (f : FamRes) : String :=
  match f.walk.endSort with
  | some u => RE.fmtU u
  | none => "-"

def FamRes.residualStr (nm : Address → String) (f : FamRes) : String :=
  match f.walk.residual with
  | some r => clip (RE.fmt nm 30 r) 300
  | none => "-"

def FamRes.endHnf (f : FamRes) : String :=
  match f.walk.endSort with
  | some _ => "sort"
  | none => if f.walk.endHead.isEmpty then "-" else f.walk.endHead

def FamRes.allDeltas (f : FamRes) : Array Address :=
  (f.walk.poss.foldl (fun acc p => acc ++ p.log.deltas) #[]) ++ f.walk.endLog.deltas

def FamRes.betas (f : FamRes) : Nat := f.walk.poss.foldl (fun n p => n + p.log.betas) f.walk.endLog.betas
def FamRes.betaCert (f : FamRes) : Nat :=
  f.walk.poss.foldl (fun n p => n + p.log.betaCert) f.walk.endLog.betaCert
def FamRes.zetas (f : FamRes) : Nat := f.walk.poss.foldl (fun n p => n + p.log.zetas) f.walk.endLog.zetas
def FamRes.lvlMismatch (f : FamRes) : Nat :=
  f.walk.poss.foldl (fun n p => n + p.log.lvlMismatch) f.walk.endLog.lvlMismatch
def FamRes.projDefs (f : FamRes) : Nat :=
  f.walk.poss.foldl (fun n p => n + p.log.projDefs.size) f.walk.endLog.projDefs.size
def FamRes.zetaAtParam (f : FamRes) : Bool := f.walk.poss.any fun p => p.k < f.np && p.log.zetas > 0
def FamRes.letAtParam (f : FamRes) : Bool := f.synLets.any (· < f.np)

def classOf (np ni lead : Nat) (w : WalkRes) : String :=
  if lead < np then "parameters not syntactic"
  else if !w.err.isEmpty then "other: " ++ w.err
  else
    match w.endSort with
    | none => "other: no end sort"
    | some _ =>
      if ni == 0 then "alias to a sort with no index"
      else if w.poss.any (·.src == "whnf") then "alias to a Π"
      else "alias to a sort after syntactic indices"

def analyseFamily (env : Ixon.Env) (nm : Address → String) (cap : Nat) (blk : Address)
    (ms : Array Ixon.MutConst) (j : Nat) (ind : Ixon.Inductive) (pty : RE) (ctyps : Array RE)
    (oneType allInd : Bool) : FamRes := Id.run do
  let np := ind.params.toNat
  let ni := ind.indices.toNat
  let members := recurOf blk ms
  let self := members[j]!
  let mut notes : Array String := #[]
  let mut occ := true
  if oneType then
    for (ct, k) in ind.ctors.zipIdx do
      match ctyps[k]? with
      | none => occ := false
      | some cty =>
        match recIdxOf cty self (lpsOf 0 ind.lvls.toNat) np ni ct.fields.toNat with
        | .error e =>
          occ := false
          notes := notes.push s!"constructor {k}: {e}"
        | .ok _ => pure ()
  let w := teleWalk env nm cap (np + ni) pty
  let lead := leadAlls pty
  let grsl := match resultSortLevel env cap (np + ni) pty with
    | .error e => "error: " ++ e
    | .ok (u, doms) =>
      if w.err.isEmpty && w.endSort == some u && w.doms == doms then "agrees"
      else s!"differs (level {RE.fmtU u})"
  let tele := match w.endSort with
    | some u =>
      if w.err.isEmpty then
        RE.fmt nm 60 (w.doms.foldr (fun (d, t) acc => RE.all d t acc) (RE.sort u))
      else "-"
    | none => "-"
  return { name := nm self, addr := self, block := blk, oneType := oneType, allInd := allInd,
           native := oneType && occ,
           unsafe_ := ind.isUnsafe || ind.ctors.any (·.isUnsafe),
           lvls := ind.lvls.toNat, np := np, ni := ni, nc := ind.ctors.size, lead := lead,
           synLets := synLets (np + ni) pty, letAnywhere := pty.hasLet, walk := w, grsl := grsl,
           cls := classOf np ni lead w, declared := RE.fmt nm 60 pty, tele := tele, notes := notes }

/-- The family a standalone recursor record eliminates (the head of its major premise) and
whether that family's former is not a telescope into a sort. -/
def recFamily (env : Ixon.Env) (cap : Nat) (a : Address) (c : Ixon.Constant) (r : Ixon.Recursor) :
    Except String (Address × Bool) := do
  let rs ← readRoots c { refs := c.refs, univs := c.univs, recur := #[a] } #[(0, r.typ)] cap
  let some sty := rs[0]? | throw "no type"
  let n := (r.params + r.motives + r.minors + r.indices).toNat
  let .all _ dom _ ← peelN n sty | throw "no major premise"
  let (h, _) := dom.spine
  let .const p _ := h | throw "the major premise's head is not a constant"
  let some pc := env.getConst? p | throw "the family's record is missing"
  let .iPrj ip := pc.info | throw "the major premise's head is not an inductive projection"
  let some bc := env.getConst? ip.block | throw "the family's block is missing"
  let .muts ms := bc.info | throw "the family's block is not a block"
  let idx := ip.idx.toNat
  let some (Ixon.MutConst.indc ind) := ms[idx]? | throw "the family's member is not an inductive"
  let off := rootOffset ms idx
  let rs2 ← readRoots bc { refs := bc.refs, univs := bc.univs, recur := recurOf ip.block ms }
    #[(off, ind.typ)] cap
  let some pty := rs2[0]? | throw "no former"
  return (p, !formerIsTele (ind.params.toNat + ind.indices.toNat) pty)

/-! ## The run -/

def histogram (xs : Array String) : Array (String × Nat) :=
  let m : Std.HashMap String Nat := xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) {}
  m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)

def posCode (p : PosRes) : String :=
  match p.src with
  | "declared" => "D"
  | "unfolded" => "U"
  | "whnf" => "W"
  | _ => "X"

def posDetail (nm : Address → String) (p : PosRes) : String :=
  s!"{p.k}: {p.head}; δ [{", ".intercalate (p.log.deltas.toList.map nm)}]; β {p.log.betas} (datum not never {p.log.betaCert}); ζ {p.log.zetas}; level-count mismatch {p.log.lvlMismatch}; projection-shaped {p.log.projDefs.size}"

def run : IO UInt32 := do
  let some path ← IO.getEnv "IX_ALIAS_IXE" | throw (IO.userError "set IX_ALIAS_IXE to an .ixe file")
  let some outDir ← IO.getEnv "IX_ALIAS_OUT" | throw (IO.userError "set IX_ALIAS_OUT")
  let dir := System.FilePath.mk outDir
  IO.FS.createDirAll dir
  let cap := 5000000
  let t0 ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  IO.println s!"[ixvm-alias-formers] {path}: {env.consts.size} records, {env.named.size} names ({(← IO.monoMsNow) - t0} ms)"
  -- names: the least name of each address
  let mut nameOf : Std.HashMap Address String := {}
  for (n, nmd) in env.named.toArray do
    let s := toString n
    match nameOf.get? nmd.addr with
    | some old => if s < old then nameOf := nameOf.insert nmd.addr s
    | none => nameOf := nameOf.insert nmd.addr s
  let nameMap := nameOf
  let nm : Address → String := fun a => nameMap.getD a (String.ofList ((toString a).toList.take 12))
  -- every inductive member of every block record
  let all := env.consts.toArray
  let mut nBlocks := 0
  let mut nIndBlocks := 0
  let mut nOneType := 0
  let mut nMembers := 0
  let mut nTele := 0
  let mut readErrs : Array String := #[]
  let mut fams : Array FamRes := #[]
  for (a, lc) in all do
    let isMuts := match lc.peekTag with
      | .ok .muts => true
      | _ => false
    if !isMuts then continue
    let some c := lc.get? | continue
    let .muts ms := c.info | continue
    nBlocks := nBlocks + 1
    let inds := ms.zipIdx.filterMap fun | (.indc i, j) => some (i, j) | _ => none
    if inds.isEmpty then continue
    nIndBlocks := nIndBlocks + 1
    let oneType := inds.size == 1
    let allInd := inds.size == ms.size
    if oneType then nOneType := nOneType + 1
    let rcx : RCx := { refs := c.refs, univs := c.univs, recur := recurOf a ms }
    for (ind, j) in inds do
      nMembers := nMembers + 1
      let off := rootOffset ms j
      match readRoots c rcx #[(off, ind.typ)] cap with
      | .error e => readErrs := readErrs.push s!"{nm (iprjAddr a j)}\t{a}\tformer not read: {e}"
      | .ok rs =>
        let pty := rs[0]!
        if formerIsTele (ind.params.toNat + ind.indices.toNat) pty then
          nTele := nTele + 1
        else
          let roots := ind.ctors.zipIdx.map fun (ct, k) => (off + 1 + k, ct.typ)
          match readRoots c rcx roots cap with
          | .error e => readErrs := readErrs.push s!"{nm (iprjAddr a j)}\t{a}\tconstructors not read: {e}"
          | .ok ctyps => fams := fams.push (analyseFamily env nm cap a ms j ind pty ctyps oneType allInd)
  IO.println s!"[ixvm-alias-formers] {nIndBlocks} inductive blocks, {fams.size} formers not a telescope ({(← IO.monoMsNow) - t0} ms)"
  -- every name of each such family
  let famSet : Std.HashSet Address := fams.foldl (fun s f => s.insert f.addr) {}
  let mut namesOf : Std.HashMap Address (Array String) := {}
  for (n, nmd) in env.named.toArray do
    if famSet.contains nmd.addr then
      namesOf := namesOf.insert nmd.addr ((namesOf.getD nmd.addr #[]).push (toString n))
  -- the recursors' reading: the families whose recursor record names a non-telescope former
  let mut nRecs := 0
  let mut nRecErr := 0
  let mut recErrs : Array String := #[]
  let mut canonSet : Std.HashSet Address := {}
  let mut withRec : Std.HashSet Address := {}
  for (a, lc) in all do
    let isRec := match lc.peekTag with
      | .ok .recr => true
      | _ => false
    if !isRec then continue
    let some c := lc.get? | continue
    let .recr r := c.info | continue
    nRecs := nRecs + 1
    match recFamily env cap a c r with
    | .error e =>
      nRecErr := nRecErr + 1
      recErrs := recErrs.push s!"{nm a}\t{e}"
    | .ok (p, flag) =>
      withRec := withRec.insert p
      if flag then canonSet := canonSet.insert p
  let famsS := fams.qsort fun x y => x.name < y.name || (x.name == y.name && toString x.addr < toString y.addr)
  -- the table
  let mut lines : Array String := #[tsvLine ["name", "all names", "family address", "block address",
    "one-type", "native", "unsafe", "levels", "params", "indices", "constructors",
    "leading syntactic foralls", "let positions on the declared spine (below nP+nI)",
    "let at a parameter position", "let anywhere in the declared type", "zeta at a parameter position",
    "positions (D declared, W head-normalized, U from an earlier head normal form, X failed)",
    "head-normalized positions: head before, steps", "unfolded constants (positions and end, in order)",
    "beta steps", "beta steps at a datum not never", "zeta steps", "level-count mismatches",
    "projection-shaped unfoldings", "binders reached", "residual after nP+nI binders",
    "residual syntactically a sort", "end: head normal form", "end sort level", "end unfolded",
    "get_result_sort_level", "classification", "recursor reading flags the family",
    "has a recursor record", "declared type", "telescope", "notes"]]
  for f in famsS do
    let names := (namesOf.getD f.addr #[]).qsort (· < ·)
    let w := f.walk
    let letsS := if f.synLets.isEmpty then "-" else ",".intercalate (f.synLets.toList.map toString)
    lines := lines.push (tsvLine [f.name, ",".intercalate names.toList, toString f.addr,
      toString f.block, b2s f.oneType, b2s f.native, b2s f.unsafe_, toString f.lvls,
      toString f.np, toString f.ni, toString f.nc, toString f.lead, letsS,
      b2s f.letAtParam, b2s f.letAnywhere, b2s f.zetaAtParam,
      String.join (w.poss.toList.map posCode),
      " | ".intercalate (f.whnfPoss.toList.map (posDetail nm)),
      ",".intercalate (f.allDeltas.toList.map nm),
      toString f.betas, toString f.betaCert, toString f.zetas, toString f.lvlMismatch,
      toString f.projDefs, toString w.doms.size, f.residualStr nm, b2s f.residualSort,
      f.endHnf, f.endLevel, ",".intercalate (w.endLog.deltas.toList.map nm),
      f.grsl, f.cls, b2s (canonSet.contains f.addr), b2s (withRec.contains f.addr),
      clip f.declared 900, clip f.tele 900, " ; ".intercalate f.notes.toList])
  IO.FS.writeFile (dir / "families.tsv") ("\n".intercalate lines.toList ++ "\n")
  -- the summary
  let inClass := famsS.filter fun f => f.oneType && f.native && !f.unsafe_
  let cnt (p : FamRes → Bool) (xs : Array FamRes) : Nat := (xs.filter p).size
  let mut s : Array String := #[]
  s := s.push s!"corpus: {path}"
  s := s.push s!"records: {env.consts.size}; names: {env.named.size}"
  s := s.push s!"block records: {nBlocks}; with an inductive member: {nIndBlocks}; one inductive member: {nOneType}"
  s := s.push s!"inductive members: {nMembers}; former a telescope of nP+nI binders into a sort: {nTele}; not: {fams.size}; not read: {readErrs.size}"
  for l in readErrs.extract 0 40 do s := s.push s!"  {l}"
  s := s.push ""
  s := s.push s!"== formers not a telescope: {fams.size}"
  s := s.push s!"one-type: {cnt (·.oneType) fams}; native one-type: {cnt (fun f => f.oneType && f.native) fams}; unsafe: {cnt (·.unsafe_) fams}; mutual or nested members: {cnt (!·.oneType) fams}"
  s := s.push s!"native one-type safe (the class): {inClass.size}"
  for (label, xs) in [("all formers not a telescope", famsS), ("the class", inClass)] do
    s := s.push s!"-- {label} ({xs.size})"
    for (k, n) in histogram (xs.map (·.cls)) do s := s.push s!"  classification {k}: {n}"
    s := s.push s!"  zero constructors: {cnt (·.nc == 0) xs}"
    s := s.push s!"  a let on the declared spine below nP+nI: {cnt (!·.synLets.isEmpty) xs}; at a parameter position: {cnt (·.letAtParam) xs}; anywhere in the declared type: {cnt (·.letAnywhere) xs}; ζ at a parameter position while head-normalizing: {cnt (·.zetaAtParam) xs}"
    s := s.push s!"  leading syntactic ∀ ≥ nP: {cnt (fun f => f.lead ≥ f.np) xs}; = nP: {cnt (fun f => f.lead == f.np) xs}"
    s := s.push s!"  walk reaches nP+nI binders and the residual's head normal form is a sort: {cnt (·.walk.err.isEmpty) xs}"
    s := s.push s!"  residual after nP+nI binders syntactically a sort: {cnt (·.residualSort) xs}"
    s := s.push s!"  get_result_sort_level agrees with the walk (binders and level): {cnt (·.grsl == "agrees") xs}"
    s := s.push s!"  head-normalized positions: one: {cnt (·.whnfPoss.size == 1) xs}; more: {cnt (·.whnfPoss.size > 1) xs}; none: {cnt (·.whnfPoss.isEmpty) xs}"
    s := s.push s!"  first head-normalized position = nP: {cnt (fun f => (f.whnfPoss[0]?.map (·.k)) == some f.np) xs}"
    s := s.push s!"  β steps at a datum not never: {cnt (·.betaCert > 0) xs}; level-count mismatches: {cnt (·.lvlMismatch > 0) xs}; projection-shaped unfoldings: {cnt (·.projDefs > 0) xs}; ζ steps: {cnt (·.zetas > 0) xs}"
    for (k, n) in histogram (xs.map (·.endLevel)) do
      s := s.push s!"  end sort {k}: {n}"
    for (k, n) in histogram (xs.map fun f => ",".intercalate ((f.allDeltas.toList.map nm).eraseDups)) do
      s := s.push s!"  unfolded {k}: {n}"
    for (k, n) in histogram (xs.map fun f => ",".intercalate (f.whnfPoss.toList.map (·.head))) do
      s := s.push s!"  head before normalization {k}: {n}"
  s := s.push ""
  s := s.push "== per family: name, nP, nI, constructors, leading syntactic ∀, positions, unfolded, classification, end sort, recursor reading"
  for f in famsS do
    s := s.push s!"  {f.name}\tnP {f.np}\tnI {f.ni}\tctors {f.nc}\t∀ {f.lead}\t{String.join (f.walk.poss.toList.map posCode)}\t{",".intercalate ((f.allDeltas.toList.map nm).eraseDups)}\t{f.cls}\tSort {f.endLevel}\tnative {b2s f.native}\tone-type {b2s f.oneType}\tunsafe {b2s f.unsafe_}\trecursor-flag {b2s (canonSet.contains f.addr)}"
  s := s.push ""
  s := s.push "== against the recursors' reading (a standalone recursor record's family whose former is not a telescope)"
  s := s.push s!"standalone recursor records: {nRecs}; family read: {nRecs - nRecErr}; not: {nRecErr}"
  for l in recErrs.extract 0 20 do s := s.push s!"  {l}"
  let both := famsS.filter fun f => canonSet.contains f.addr
  let onlyHere := famsS.filter fun f => !canonSet.contains f.addr
  let onlyRec := canonSet.toArray.filter fun p => !famSet.contains p
  s := s.push s!"families flagged by the recursors' reading: {canonSet.size}; here: {fams.size}; in both: {both.size}; only here: {onlyHere.size}; only in the recursors' reading: {onlyRec.size}"
  for f in onlyHere do s := s.push s!"  only here: {f.name}\thas a recursor record {b2s (withRec.contains f.addr)}"
  for p in onlyRec do s := s.push s!"  only in the recursors' reading: {nm p}"
  s := s.push s!"elapsed ms: {(← IO.monoMsNow) - t0}"
  IO.FS.writeFile (dir / "summary.txt") ("\n".intercalate s.toList ++ "\n")
  for l in s.toList.take 300 do IO.println l
  return 0

end Tests.Ix.IxVM.AliasFormers
