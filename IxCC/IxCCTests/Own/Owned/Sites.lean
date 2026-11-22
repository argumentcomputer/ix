import IxCCTests.Own.Owned.Oracle
import IxCCTests.Own.Owned.Mutate

/-! # The ownership checker's suite: site-directed mutants (the theorem's direction, tested)

Random edits of a placement mostly act on immediates or on paths no input runs. Here every edit
is chosen with the checker's own context at
the site, as the negative controls are: its subject is a variable that is not an immediate and
holds a token (or is borrowed) there, and the edit is one a placement could legitimately make, so
that the checker accepts many of them and an accepted one changes the reference-count traffic on
cells. Edits work on *chains*: a straight run of actions, bindings and join declarations, ending
in a terminal; a chain's context is the checker's (`stepStmt`).

Kinds (each an untrusted placement change the checker must judge):
* `dec-earlier`, `dec-later`: move a `dec x` within its chain (half the time to just after the
  last statement that mentions `x`);
* `dec-into-branches`, `dec-out-of-branches`: push a `dec x` into every alternative of the chain's
  `case`, or hoist one found in every alternative before the `case`;
* `cancel-inc-dec`: delete an `inc x` and a later `dec x` (the chain's, or one in each alternative):
  a copy becomes a move;
* `span-inc-dec`: insert `inc x` at one point and `dec x` at a later one;
* `borrow-instead`: delete the `inc x` after `x := proj y` and the `dec x` that released it;
* `uncapture`: remove a variable from a join's captured list, release it before every jump to the
  join and delete its decrements in the body;
* `capture`: add an owned variable to a join's captured list, delete its decrement before every
  jump to the join, and release it at the body's start;
* `trap-leak`: delete a `dec` on a chain that ends in `trap` (a trap may leak).

A third of the mutants carry a second edit. -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var JoinId FunId Arg Rhs)

inductive Stmt where
  | act (a : Action)
  | bind (x : Var) (r : Rhs)
  | jp (j : JoinId) (ps cs : List Var) (rec : Bool) (body : Code)

instance : Inhabited Stmt := ⟨.act (.dec 0)⟩

def spine : Code → List Stmt × Code
  | .act a k => let (s, t) := spine k; (.act a :: s, t)
  | .bind x r k => let (s, t) := spine k; (.bind x r :: s, t)
  | .jp j ps cs rec b k => let (s, t) := spine k; (.jp j ps cs rec b :: s, t)
  | t => ([], t)

def unspine : List Stmt → Code → Code
  | [], t => t
  | .act a :: s, t => .act a (unspine s t)
  | .bind x r :: s, t => .bind x r (unspine s t)
  | .jp j ps cs rec b :: s, t => .jp j ps cs rec b (unspine s t)

def stepStmt (Δ : JCtx) (Γ : Ctx) : Stmt → Option (JCtx × Ctx)
  | .act (.inc x n) => match Γ.inc x n with | .ok Γ' => some (Δ, Γ') | .error _ => none
  | .act (.dec x) => match Γ.dec x with | .ok Γ' => some (Δ, Γ') | .error _ => none
  | .bind x r => match bindCtx Γ x r with | .ok Γ' => some (Δ, Γ') | .error _ => none
  | .jp j _ cs _ _ => some (Δ.insert j cs, Γ)

/-- The context before each statement, then before the terminal (`none` after a refusal). -/
def ctxs (Δ : JCtx) (Γ : Ctx) : List Stmt → List (Option (JCtx × Ctx))
  | [] => [some (Δ, Γ)]
  | s :: ss => some (Δ, Γ) :: match stepStmt Δ Γ s with
    | some (Δ', Γ') => ctxs Δ' Γ' ss
    | none => ss.map (fun _ => none) ++ [none]

def stmtVars : Stmt → List Var
  | .act (.inc x _) | .act (.dec x) => [x]
  | .bind x r => x :: rhsUses r
  | .jp _ _ cs _ _ => cs

def termVars : Code → List Var
  | .ret a => argVars [a]
  | .tcall _ args | .jmp _ args => argVars args
  | .case x _ _ => [x]
  | _ => []

/-- Holds a token here (not an immediate). -/
def holds (ctx : Option (JCtx × Ctx)) (x : Var) : Bool :=
  match ctx with
  | some (_, Γ) => !Γ.isImm x && Γ.tokens x ≥ 1
  | none => false

def heldOrBorrowed (ctx : Option (JCtx × Ctx)) (x : Var) : Bool :=
  match ctx with
  | some (_, Γ) => !Γ.isImm x && (Γ.tokens x ≥ 1 || Γ.borrowed x)
  | none => false

def isDecOf (x : Var) : Stmt → Bool
  | .act (.dec y) => y == x
  | _ => false

def findIdx (p : Stmt → Bool) (ss : List Stmt) (from_ : Nat := 0) : Option Nat :=
  ((ss.zipIdx).find? fun (s, i) => i ≥ from_ && p s).map (·.2)

/-- A branch's chain without its first top-level `dec x` (`none` if it has none). -/
def dropFirstDec (x : Var) (c : Code) : Option Code :=
  let (ss, t) := spine c
  (findIdx (isDecOf x) ss).map fun i => unspine (ss.eraseIdx i) t

def mapBranches (f : Code → Option Code) : Code → Option Code
  | .case x alts d => do
    let alts' ← alts.mapM fun (.mk key b) => do return Alt.mk key (← f b)
    let d' ← match d with
      | some b => some <$> f b
      | none => pure none
    return .case x alts' d'
  | _ => none

partial def deleteDecs (x : Var) : Code → Code
  | .act (.dec y) k => if y == x then deleteDecs x k else .act (.dec y) (deleteDecs x k)
  | .act a k => .act a (deleteDecs x k)
  | .bind y r k => .bind y r (deleteDecs x k)
  | .jp j ps cs rec b k => .jp j ps cs rec (deleteDecs x b) (deleteDecs x k)
  | .case y alts d => .case y (alts.map fun (.mk key b) => .mk key (deleteDecs x b)) (d.map (deleteDecs x))
  | t => t

/-- Every `jmp j` gets `dec x` before it. -/
partial def decBeforeJumps (j : JoinId) (x : Var) : Code → Code
  | .act a k => .act a (decBeforeJumps j x k)
  | .bind y r k => .bind y r (decBeforeJumps j x k)
  | .jp j' ps cs rec b k => .jp j' ps cs rec (decBeforeJumps j x b) (decBeforeJumps j x k)
  | .case y alts d =>
    .case y (alts.map fun (.mk key b) => .mk key (decBeforeJumps j x b)) (d.map (decBeforeJumps j x))
  | .jmp j' args => if j' == j then .act (.dec x) (.jmp j' args) else .jmp j' args
  | t => t

/-- On every chain that ends in `jmp j`, delete its last top-level `dec x`. -/
partial def undecBeforeJumps (j : JoinId) (x : Var) (c : Code) : Code :=
  let (ss, t) := spine c
  let ss := ss.map fun (s : Stmt) => match s with
    | .jp j' ps cs rec b => Stmt.jp j' ps cs rec (undecBeforeJumps j x b)
    | s => s
  let t : Code := match t with
    | .case y alts d =>
      .case y (alts.map fun (.mk key b) => .mk key (undecBeforeJumps j x b)) (d.map (undecBeforeJumps j x))
    | t => t
  match t with
  | .jmp j' _ =>
    if j' == j then
      match ((ss.zipIdx).filter fun (s, _) => isDecOf x s).getLast? with
      | some (_, i) => unspine (ss.eraseIdx i) t
      | none => unspine ss t
    else unspine ss t
  | _ => unspine ss t

inductive SiteKind where
  | decEarlier | decLater | decIntoBranches | decOutOfBranches | cancelIncDec | spanIncDec
  | borrowInstead | uncapture | capture | trapLeak
  deriving BEq, Repr, Inhabited

def SiteKind.all : List SiteKind :=
  [.decEarlier, .decLater, .decIntoBranches, .decOutOfBranches, .cancelIncDec, .spanIncDec,
   .borrowInstead, .uncapture, .capture, .trapLeak]

def SiteKind.name : SiteKind → String
  | .decEarlier => "dec-earlier" | .decLater => "dec-later"
  | .decIntoBranches => "dec-into-branches" | .decOutOfBranches => "dec-out-of-branches"
  | .cancelIncDec => "cancel-inc-dec" | .spanIncDec => "span-inc-dec"
  | .borrowInstead => "borrow-instead" | .uncapture => "uncapture" | .capture => "capture"
  | .trapLeak => "trap-leak"

abbrev Edit := List Stmt × Code × String

/-- One edit of one chain, chosen with the checker's context; `none` if the chain has no site. -/
def editChain (kind : SiteKind) (r : Rng) (Δ : JCtx) (Γ : Ctx) (ss : List Stmt) (t : Code) :
    Option Edit × Rng :=
  let cx := ctxs Δ Γ ss
  let n := ss.length
  let at_ (i : Nat) : Option (JCtx × Ctx) := cx[i]?.join
  let decs := (ss.zipIdx).filterMap fun (s, i) => match s with
    | .act (.dec x) => if holds (at_ i) x then some (i, x) else none
    | _ => none
  let incs := (ss.zipIdx).filterMap fun (s, i) => match s with
    | .act (.inc x 1) => if heldOrBorrowed (at_ i) x then some (i, x) else none
    | _ => none
  match kind with
  | .decEarlier =>
    if decs.isEmpty then (none, r) else
    let ((i, x), r) := r.pick decs
    let ok := (List.range i).filter fun p => holds (at_ p) x
    if ok.isEmpty then (none, r) else
    let tight := ((List.range i).filter fun q => (stmtVars ss[q]!).contains x).getLast?.map (· + 1)
    let (coin, r) := r.next 2
    let (p, r) := match tight with
      | some p => if coin == 0 && p < i && ok.contains p then (p, r) else r.pick ok
      | none => r.pick ok
    (some ((ss.eraseIdx i).insertIdx p (.act (.dec x)), t, s!"move dec v{x} from {i} to {p}"), r)
  | .decLater =>
    let later := decs.filter fun (i, _) => i + 1 < n
    if later.isEmpty then (none, r) else
    let ((i, x), r) := r.pick later
    let (p, r) := r.next (n - 1 - i)
    let p := i + 1 + p
    (some ((ss.eraseIdx i).insertIdx p (.act (.dec x)), t, s!"move dec v{x} from {i} to {p}"), r)
  | .decIntoBranches =>
    match t with
    | .case .. =>
      if decs.isEmpty then (none, r) else
      let ((i, x), r) := r.pick decs
      match mapBranches (fun b => some (.act (.dec x) b)) t with
      | some t' => (some (ss.eraseIdx i, t', s!"push dec v{x} at {i} into every branch"), r)
      | none => (none, r)
    | _ => (none, r)
  | .decOutOfBranches =>
    match t with
    | .case y alts d =>
      let bodies := alts.map (fun (.mk _ b) => b) ++ d.toList
      let cands := ((bodies.head?.map fun b => (spine b).1).getD []).filterMap fun
        | .act (.dec x) => if holds (at_ n) x && x != y then some x else none
        | _ => none
      let cands := cands.filter fun x => bodies.all fun b => (dropFirstDec x b).isSome
      if cands.isEmpty then (none, r) else
      let (x, r) := r.pick cands
      match mapBranches (dropFirstDec x) t with
      | some t' => (some (ss ++ [.act (.dec x)], t', s!"hoist dec v{x} out of every branch"), r)
      | none => (none, r)
    | _ => (none, r)
  | .cancelIncDec =>
    if incs.isEmpty then (none, r) else
    let ((i, x), r) := r.pick incs
    match findIdx (isDecOf x) ss (i + 1) with
    | some q => (some (((ss.eraseIdx q).eraseIdx i), t, s!"delete inc v{x} at {i} and dec at {q}"), r)
    | none =>
      match mapBranches (dropFirstDec x) t with
      | some t' => (some (ss.eraseIdx i, t', s!"delete inc v{x} at {i} and its dec in every branch"), r)
      | none => (none, r)
  | .spanIncDec =>
    let sites := (List.range (n + 1)).flatMap fun p =>
      ((ss.flatMap stmtVars) ++ termVars t).eraseDups.filterMap fun x =>
        if heldOrBorrowed (at_ p) x then some (p, x) else none
    if sites.isEmpty then (none, r) else
    let ((p, x), r) := r.pick sites
    let (q, r) := r.next (n + 1 - p)
    let ss' := ss.insertIdx p (.act (.inc x 1))
    (some (ss'.insertIdx (p + 1 + q) (.act (.dec x)), t, s!"inc v{x} at {p}, dec at {p + 1 + q}"), r)
  | .borrowInstead =>
    let projs := (ss.zipIdx).filterMap fun (s, i) => match s, ss[i + 1]? with
      | .bind x (.proj y _ _), some (.act (.inc x' 1)) =>
        if x == x' && heldOrBorrowed (at_ i) y then some (i, x) else none
      | _, _ => none
    if projs.isEmpty then (none, r) else
    let ((i, x), r) := r.pick projs
    match findIdx (isDecOf x) ss (i + 2) with
    | some q => (some (((ss.eraseIdx q).eraseIdx (i + 1)), t, s!"borrow v{x} at {i}: inc and dec at {q} deleted"), r)
    | none =>
      match mapBranches (dropFirstDec x) t with
      | some t' => (some (ss.eraseIdx (i + 1), t', s!"borrow v{x} at {i}: inc and its dec in every branch deleted"), r)
      | none => (none, r)
  | .uncapture =>
    let joins := (ss.zipIdx).flatMap fun (s, i) => match s with
      | .jp _ _ cs _ _ => (cs.filter fun c => holds (at_ i) c).map (i, ·)
      | _ => []
    if joins.isEmpty then (none, r) else
    let ((i, c), r) := r.pick joins
    match ss[i]! with
    | .jp j ps cs rec b =>
      let b' := deleteDecs c b
      let b' := if rec then decBeforeJumps j c b' else b'
      let (ss2, t2) := spine (decBeforeJumps j c (unspine (ss.drop (i + 1)) t))
      (some (ss.take i ++ [.jp j ps (cs.erase c) rec b'] ++ ss2, t2, s!"uncapture v{c} from j{j}"), r)
    | _ => (none, r)
  | .capture =>
    let joins := (ss.zipIdx).flatMap fun (s, i) => match s with
      | .jp _ _ cs _ _ =>
        let held : List Var := match at_ i with
          | some (_, Γi) => (Γi.own.toList.filter (fun (p : Nat × Nat) => p.2 ≥ 1)).map (fun p => p.1)
          | none => []
        let vs := held.filter fun c => !cs.contains c && holds (at_ i) c
        vs.map (i, ·)
      | _ => []
    if joins.isEmpty then (none, r) else
    let ((i, c), r) := r.pick joins
    match ss[i]! with
    | .jp j ps cs rec b =>
      let b' := if rec then undecBeforeJumps j c b else b
      let (ss2, t2) := spine (undecBeforeJumps j c (unspine (ss.drop (i + 1)) t))
      (some (ss.take i ++ [.jp j ps (cs ++ [c]) rec (.act (.dec c) b')] ++ ss2, t2, s!"capture v{c} in j{j}"), r)
    | _ => (none, r)
  | .trapLeak =>
    match t with
    | .trap =>
      if decs.isEmpty then (none, r) else
      let ((i, x), r) := r.pick decs
      (some (ss.eraseIdx i, t, s!"leak v{x} at {i} before a trap"), r)
    | _ => (none, r)

structure WS where
  next : Nat := 0
  what : Option String := none
  rng : Rng

/-- Apply `edit` to the `target`-th chain (preorder), with the chain's context. -/
partial def walkChains (target : Nat) (kind : SiteKind) (Δ : JCtx) (Γ : Ctx) (c : Code) :
    StateM WS Code := do
  let (ss, t) := spine c
  let s ← get
  set { s with next := s.next + 1 }
  if s.next == target then
    let (res, r) := editChain kind s.rng Δ Γ ss t
    modify fun s => { s with rng := r }
    match res with
    | some (ss', t', what) =>
      modify fun s => { s with what := some what }
      return unspine ss' t'
    | none => return c
  let cx := ctxs Δ Γ ss
  let mut out : Array Stmt := #[]
  for (st, i) in ss.zipIdx do
    match st, cx[i]?.join with
    | .jp j ps cs rec b, some (Δi, Γi) =>
      let b' ← walkChains target kind (if rec then Δi.insert j cs else Δi) (Γi.enter cs ps) b
      out := out.push (.jp j ps cs rec b')
    | st, _ => out := out.push st
  let t' ← match t, cx[ss.length]?.join with
    | .case x alts d, some (Δt, Γt) => do
      let alts' ← alts.mapM fun (.mk key b) => do return Alt.mk key (← walkChains target kind Δt Γt b)
      let d' ← match d with
        | some b => some <$> walkChains target kind Δt Γt b
        | none => pure none
      pure (Code.case x alts' d')
    | t, _ => pure t
  return unspine out.toList t'

def chainCount (params : List Var) (body : Code) : Nat :=
  ((walkChains 1000000000 .trapLeak .leaf (Ctx.entry params) body).run { rng := ⟨0⟩ }).2.next

/-- One site-directed edit of a body, trying up to 8 chains; `none` if no site was found. -/
def siteEdit (kind : SiteKind) (params : List Var) (body : Code) (r : Rng) :
    Option (Code × String) × Rng := Id.run do
  let n := chainCount params body
  let mut r := r
  for _ in List.range 8 do
    let (i, r1) := r.next n
    let (c, s) := (walkChains i kind .leaf (Ctx.entry params) body).run { rng := r1 }
    r := s.rng
    if let some what := s.what then return (some (c, what), r)
  return (none, r)

end IxCCTests.Own.Owned
