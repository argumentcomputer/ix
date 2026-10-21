/- The generic rewrite hook may return a different no-site result after a
   proof-justified hit. Only the production engine's ordering permits skipping it. -/
import LSpec
import Ix.Compile.Pass.Translate

namespace Tests.Ix.Compile.RewriteRetry
open LSpec
open _root_.Ix (Name Expr Level ConstantInfo)
open _root_.Ix.Compile.Pass

def nm (s : String) : Name := Name.mkStr Name.mkAnon s
def term (s : String) : Expr := Expr.mkConst (nm s) #[]
def lookup (n : Name) : Except String (Option Expansion) :=
  .ok (if n == nm "head" then some {
    levelParams := #[], value := term "baseline", arity := 0, needsRewrite := false
  } else none)

def callback (site : Option Name) (_ : Name) (_ : Array Level) (_ : Array Expr) :
    Option (Expr × Array ConstantInfo × Option String × Array String) :=
  some (if site.isSome then (term "pj", #[], some "O7", #[])
        else (term "generic-no-site", #[], none, #[]))

def genericRetry : Bool :=
  match ((rw lookup 8 false (term "head")).run {
      site := some (nm "caller"), opt? := callback }).run {} with
  | .ok ((value, _), state) =>
    reprStr value == reprStr (term "generic-no-site") && state.pjFired
  | .error _ => false

def ordered (site : Option Name) (n : Name) (us : Array Level) (args : Array Expr) :
    Option (Expr × Array ConstantInfo × Option String × Array String) :=
  if site.isSome then callback site n us args else none

def orderedNeighbour (skipPjRetry inPlace : Bool) : Bool :=
  match ((rw lookup 8 false (term "head")).run {
      site := some (nm "caller"), opt? := ordered, skipPjRetry, inPlace }).run {} with
  | .ok ((value, _), state) =>
    reprStr value == reprStr (term (if inPlace then "pj" else "baseline")) &&
      state.pjFired == !inPlace
  | .error _ => false


/-- Two definition sites share an effectful expansion; two theorem values
also share the term-memo key. Every member must retain the decline. -/
def sharedDeclines : Bool := Id.run do
  let expand (n : Name) : Except String (Option Expansion) :=
    .ok (if n == nm "outer" then some {
      levelParams := #[], value := term "inner", arity := 0, needsRewrite := true
    } else if n == nm "inner" then some {
      levelParams := #[], value := term "baseline", arity := 0, needsRewrite := false
    } else none)
  let cause := "recorded decline inside a shared expansion"
  let cfg : RwConfig := {
    decline? := fun n _ _ => if n == nm "inner" then some cause else none }
  let member (s : String) (theoremValue : Bool) : Name × ConstantInfo :=
    let n := nm s
    let cnst : _root_.Ix.ConstantVal := { name := n, levelParams := #[], type := term "T" }
    (n, if theoremValue then
      .thmInfo { cnst, value := term "outer", all := #[n] }
    else .defnInfo { cnst, value := term "outer", all := #[n], hints := .abbrev, safety := .safe })
  let members := #[member "a" false, member "b" false, member "c" true, member "d" true]
  match rewriteBlock expand members cfg with
  | .error _ => return false
  | .ok out =>
    return out.overlay.size == 4 &&
      out.declines == (#["a", "b", "c", "d"].map fun s => (nm s, cause))

def suite : List TestSeq := [
  test "generic rewrite callbacks retain their no-site retry" genericRetry,
  test "ordered callback keeps the faithful result with and without retry"
    (orderedNeighbour false false && orderedNeighbour true false),
  test "ordered callback keeps the in-place PJ result with and without retry"
    (orderedNeighbour false true && orderedNeighbour true true),
  test "declines survive shared expansions and term memo hits across members" sharedDeclines]

end Tests.Ix.Compile.RewriteRetry
