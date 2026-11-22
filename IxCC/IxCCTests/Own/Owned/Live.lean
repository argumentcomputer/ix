import IxCC.Own.Plain.Program

/-! # The ownership checker's suite: a liveness-based ownership producer (untrusted)

Places `inc`/`dec` by liveness over `Fir.Code`: a variable is dropped right after its last use on
each path (at the start of a `case` branch that does not use it, after the projection or read
that was its last use, before a call or allocation when it is not an argument), moved (not
incremented) into its last consuming use, and incremented only for occurrences beyond the one it
moves. A projection's result is incremented at once when it is used later (borrowed until then);
a join captures exactly the variables its body uses besides its parameters (immediates of the
declaration excluded). Function parameters not used are dropped at entry. `trap` drops nothing.

Two passes: `annotate` computes each node's live-in set (a fixpoint for a recursive join);
`place` walks forward with the owned and immediate sets. It is untrusted: the checker
(`IxCC.Own.Plain.checkOwned`) decides. `partial` is acceptable here (a test; no checked path); a production version
would carry fuel. -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var JoinId FunId Arg Rhs)

abbrev VSet := Src.NatSet

instance : Inhabited Code := ⟨.trap⟩

def VSet.ofVars (xs : List Var) : VSet := Src.NatSet.ofList xs
def _root_.IxCC.Src.NatMap.vsVars (s : VSet) : List Var := s.toList.map (·.1)
def _root_.IxCC.Src.NatMap.vsAddAll (s : VSet) (xs : List Var) : VSet := xs.foldl (fun s x => s.insert x) s
def _root_.IxCC.Src.NatMap.vsUnion (a b : VSet) : VSet := a.vsAddAll b.vsVars
def _root_.IxCC.Src.NatMap.vsDiff (a b : VSet) : VSet := (a.vsVars.filter (!b.contains ·)).foldl (fun s x => s.insert x) .leaf
def _root_.IxCC.Src.NatMap.vsInter (a b : VSet) : VSet := (a.vsVars.filter b.contains).foldl (fun s x => s.insert x) .leaf

def rhsVars : Rhs → List Var
  | .arg a => argVars [a]
  | .ctor _ args | .call _ args | .prim _ args => argVars args
  | .proj y _ _ => [y]

inductive ACode where
  | bind (x : Var) (r : Rhs) (k : ACode) (liveK : VSet)
  | jp (j : JoinId) (ps : List Var) (rec : Bool) (body k : ACode) (captured : List Var) (liveBody : VSet)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List (Key.CtorKey × ACode × VSet)) (dflt : Option (ACode × VSet))
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

instance : Inhabited ACode := ⟨.trap⟩

mutual
partial def fixCaptured (Δ : Src.NatMap (List Var)) (j : JoinId) (ps : List Var) (body : Fir.Code)
    (c : List Var) (fuel : Nat) : List Var :=
  let c' := (annotate (Δ.insert j c) body).2.vsVars.filter (fun v => !ps.contains v)
  if c'.length == c.length || fuel == 0 then c' else fixCaptured Δ j ps body c' (fuel - 1)

partial def annotate (Δ : Src.NatMap (List Var)) : Fir.Code → ACode × VSet
  | .bind x r k =>
    let (ak, lk) := annotate Δ k
    (.bind x r ak lk, (lk.erase x).vsAddAll (rhsVars r))
  | .jp j ps rec body k =>
    let capturedOf (live : VSet) : List Var := live.vsVars.filter (fun v => !ps.contains v)
    let captured :=
      if rec then fixCaptured Δ j ps body [] 10000
      else capturedOf (annotate Δ body).2
    let (ab, lb) := annotate (if rec then Δ.insert j captured else Δ) body
    let (ak, lk) := annotate (Δ.insert j captured) k
    (.jp j ps rec ab ak captured lb, lk)
  | .jmp j args => (.jmp j args, (VSet.ofVars (Δ.getD j [])).vsAddAll (argVars args))
  | .case x alts d =>
    let as := alts.map fun (.mk key b) => let (ab, lb) := annotate Δ b; (key, ab, lb)
    let ad := d.map (annotate Δ)
    let live := as.foldl (fun s (_, _, lb) => s.vsUnion lb) (Src.NatSet.insert .leaf x)
    let live := match ad with | some (_, ld) => live.vsUnion ld | none => live
    (.case x as ad, live)
  | .ret a => (.ret a, VSet.ofVars (argVars [a]))
  | .tcall f args => (.tcall f args, VSet.ofVars (argVars args))
  | .trap => (.trap, .leaf)
end

/-- Occurrence counts of the non-immediate variable arguments, in first-occurrence order. -/
def occurrences (imm : VSet) (args : List Arg) : List (Var × Nat) :=
  (argVars args).foldl (fun acc v =>
    if imm.contains v then acc
    else match acc.find? (·.1 == v) with
      | some _ => acc.map fun (w, n) => if w == v then (w, n + 1) else (w, n)
      | none => acc ++ [(v, 1)]) []

/-- Tokens for a consuming use: move one owned token of each variable not live afterwards,
increment for every other occurrence. Returns the increments and the moved variables. -/
def consume (owned imm liveAfter : VSet) (args : List Arg) : List Action × List Var :=
  (occurrences imm args).foldl (fun (incs, moved) (v, n) =>
    if owned.contains v && !liveAfter.contains v then
      (incs ++ List.replicate (n - 1) (.inc v 1), moved ++ [v])
    else (incs ++ List.replicate n (.inc v 1), moved)) ([], [])

def decs (xs : List Var) : List Action := xs.map .dec

def removeAll (s : VSet) (xs : List Var) : VSet := xs.foldl (fun s x => s.erase x) s

partial def place (Δ : Src.NatMap (List Var)) (owned imm : VSet) : ACode → Code
  | .bind x r k liveK =>
    match r with
    | .proj y _ _ =>
      if imm.contains y then .bind x r (place Δ owned (imm.insert x) k)
      else
        let (owned, incs) := if liveK.contains x then (owned.insert x, [Action.inc x 1]) else (owned, [])
        let dead := (owned.vsDiff liveK).vsVars
        .bind x r (actionPrefix (incs ++ decs dead) (place Δ (removeAll owned dead) imm k))
    | .prim _ args =>
      let imm := (imm.vsAddAll (argVars args)).insert x
      let owned := removeAll owned (argVars args)
      let dead := (owned.vsDiff liveK).vsVars
      .bind x r (actionPrefix (decs dead) (place Δ (removeAll owned dead) imm k))
    | .arg (.var y) =>
      if imm.contains y then .bind x r (place Δ owned (imm.insert x) k) else
      let (incs, moved) := consume owned imm liveK [.var y]
      let owned := removeAll owned moved
      let (owned, post) := if liveK.contains x then (owned.insert x, []) else (owned, [Action.dec x])
      actionPrefix incs (.bind x r (actionPrefix post (place Δ owned imm k)))
    | .arg _ => .bind x r (place Δ owned (imm.insert x) k)
    | .ctor c args =>
      if c.arity == 0 then .bind x r (place Δ owned (imm.insert x) k) else
      let (incs, moved) := consume owned imm liveK args
      let owned := removeAll owned moved
      let dead := (owned.vsDiff liveK).vsVars
      let owned := removeAll owned dead
      let (owned, post) := if liveK.contains x then (owned.insert x, []) else (owned, [Action.dec x])
      actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post (place Δ owned imm k)))
    | .call _ args =>
      let (incs, moved) := consume owned imm liveK args
      let owned := removeAll owned moved
      let dead := (owned.vsDiff liveK).vsVars
      let owned := removeAll owned dead
      let (owned, post) := if liveK.contains x then (owned.insert x, []) else (owned, [Action.dec x])
      actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post (place Δ owned imm k)))
  | .jp j ps rec body k captured liveBody =>
    let captured := captured.filter (!imm.contains ·)
    let ownedBody := (VSet.ofVars captured).vsAddAll ps
    let deadBody := (ownedBody.vsDiff liveBody).vsVars
    let bodyCode := actionPrefix (decs deadBody)
      (place (if rec then Δ.insert j captured else Δ) (removeAll ownedBody deadBody) imm body)
    .jp j ps captured rec bodyCode (place (Δ.insert j captured) owned imm k)
  | .jmp j args =>
    let captured := Δ.getD j []
    let keep := VSet.ofVars captured
    let (incs, moved) := consume owned imm keep args
    let dead := ((removeAll owned moved).vsDiff keep).vsVars
    actionPrefix (incs ++ decs dead) (.jmp j args)
  | .case x alts d =>
    let branch (ab : ACode) (lb : VSet) : Code :=
      let dead := (owned.vsDiff lb).vsVars
      actionPrefix (decs dead) (place Δ (removeAll owned dead) imm ab)
    .case x (alts.map fun (key, ab, lb) => .mk key (branch ab lb)) (d.map fun (ad, ld) => branch ad ld)
  | .ret a =>
    let (incs, moved) := consume owned imm .leaf [a]
    actionPrefix (incs ++ decs (removeAll owned moved).vsVars) (.ret a)
  | .tcall f args =>
    let (incs, moved) := consume owned imm .leaf args
    actionPrefix (incs ++ decs (removeAll owned moved).vsVars) (.tcall f args)
  | .trap => .trap

def liveBody (params : List Var) (body : Fir.Code) : Code :=
  let (ab, lb) := annotate .leaf body
  let owned := VSet.ofVars params
  let dead := (owned.vsDiff lb).vsVars
  actionPrefix (decs dead) (place .leaf (removeAll owned dead) .leaf ab)

/-- The liveness producer's whole map. -/
def liveMap (F : Fir.Program) : Src.NatMap Code :=
  F.funs.map fun fd => liveBody (fd.params.map (·.1)) fd.body

end IxCCTests.Own.Owned
