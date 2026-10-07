/- The generic rewrite hook may return a different no-site result after a
   proof-justified hit. Only the production engine's ordering permits skipping it. -/
module
public import LSpec
public import Ix.Compile.Pass.Translate
public section

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
    Option (Expr × Array ConstantInfo × Option String) :=
  some (if site.isSome then (term "pj", #[], some "O7")
        else (term "generic-no-site", #[], none))

def genericRetry : Bool :=
  match (rw lookup 8 false (term "head")).run {
      base := 0, site := some (nm "caller"), opt? := callback } with
  | .ok (value, state) =>
    reprStr value == reprStr (term "generic-no-site") && state.pjFired
  | .error _ => false

def ordered (site : Option Name) (n : Name) (us : Array Level) (args : Array Expr) :
    Option (Expr × Array ConstantInfo × Option String) :=
  if site.isSome then callback site n us args else none

def orderedNeighbour (skipPjRetry inPlace : Bool) : Bool :=
  match (rw lookup 8 false (term "head")).run {
      base := 0, site := some (nm "caller"), opt? := ordered, skipPjRetry, inPlace } with
  | .ok (value, state) =>
    reprStr value == reprStr (term (if inPlace then "pj" else "baseline")) &&
      state.pjFired == !inPlace
  | .error _ => false

def suite : List TestSeq := [
  test "generic rewrite callbacks retain their no-site retry" genericRetry,
  test "ordered callback keeps the faithful result with and without retry"
    (orderedNeighbour false false && orderedNeighbour true false),
  test "ordered callback keeps the in-place PJ result with and without retry"
    (orderedNeighbour false true && orderedNeighbour true true)]

end Tests.Ix.Compile.RewriteRetry
end

