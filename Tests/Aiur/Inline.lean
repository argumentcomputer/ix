module

public import LSpec
public import Ix.Aiur

/-!
Unit tests for definition-site inlining (`inline fn`): the flag makes every
plain call a splice site, so the inline-expansion pass must reject the same
hazards it rejects for `@`-calls — inline recursion, direct or through a
chain of inline functions — plus `unconstrained` calls to inline functions,
whose whole point is to carry no lookup.
-/

public section

open LSpec Aiur

namespace AiurTests.Inline

def directRecursion : Source.Toplevel := ⟦
  inline fn spin(x: G) -> G { spin(x) }
⟧

/-- The cycle closes only through plain calls: neither function `@`-calls
the other, so nothing but the definition-site flags makes it inline
recursion. -/
def chainedRecursion : Source.Toplevel := ⟦
  inline fn ping(x: G) -> G { pong(x) }
  inline fn pong(x: G) -> G { ping(x) }
⟧

/-- Not recursion: `pong` is not inline, so `ping`'s plain call to it is an
ordinary call and only `pong`'s `@ping` splices. -/
def acyclicMix : Source.Toplevel := ⟦
  inline fn ping(x: G) -> G { pong(x) }
  fn pong(x: G) -> G { @ping(x) }
⟧

def unconstrainedCall : Source.Toplevel := ⟦
  inline fn dbl(x: G) -> G { x + x }
  fn f(x: G) -> G { #dbl(x) }
⟧

/-- Well-founded chain: plain calls to inline functions expand away, leaving
no application of an inline function anywhere. -/
def chain : Source.Toplevel := ⟦
  inline fn dbl(x: G) -> G { x + x }
  inline fn quad(x: G) -> G { dbl(dbl(x)) }
  pub fn f(x: G) -> G { quad(x) + dbl(x) }
⟧

def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def inlineCallsRemain (t : Source.Toplevel) : Bool :=
  let inl := fun g => (t.functions.find? (·.name == g)).map (·.inline) |>.getD false
  t.functions.any fun f => !(f.body.inlineCallSites inl).isEmpty

def tests : TestSeq :=
  test "direct inline recursion is rejected" (isError directRecursion.inlineCalls) ++
  test "inline recursion through a plain call is rejected"
    (isError chainedRecursion.inlineCalls) ++
  test "unconstrained call to an inline function is rejected"
    (isError unconstrainedCall.inlineCalls) ++
  test "a plain call to a non-inline function does not close a cycle"
    (!isError acyclicMix.inlineCalls) ++
  (match chain.inlineCalls with
   | .error e => test s!"inline chain expands: {e}" false
   | .ok t => test "inline chain expands away every inline call" (!inlineCallsRemain t))

end AiurTests.Inline
