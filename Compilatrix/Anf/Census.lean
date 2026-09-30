import Compilatrix.Anf.Syntax

/-! # Occurrence counts

The syntactic facts the passes' heuristics read (Appel–Jim counts, 02 §8):
how often a value variable occurs, how often as the head of an application
of a given arity, how often a join point is jumped to, and whether a term's
free variables are all below a bound. They decide *whether* a rewrite is
worth it (dead, used once); soundness never depends on them, except that a
binding the walk drops must have no occurrence at all. Structural recursion
(kernel-evaluable, D17). -/

namespace Compilatrix.Anf

namespace Atom

def occ (i : Nat) : Atom → Nat
  | .var j => if i == j then 1 else 0
  | _ => 0

def occList (i : Nat) : List Atom → Nat
  | [] => 0
  | a :: as => a.occ i + occList i as

/-- Every variable is below `n`. -/
def below (n : Nat) : Atom → Bool
  | .var j => decide (j < n)
  | _ => true

end Atom

mutual

/-- Occurrences of value variable `i`. -/
def Exp.occ (i : Nat) : Exp → Nat
  | .bind _ b e => Bind.occ i b + Exp.occ (i + 1) e
  | .join n _ b e => Exp.occ (i + n) b + Exp.occ i e
  | .jump _ as => Atom.occList i as
  | .case x alts d => x.occ i + Exp.altsOcc i alts + Exp.optOcc i d
  | .ret a => a.occ i
  | .tick e => Exp.occ i e
  | .trap => 0

def Bind.occ (i : Nat) : Bind → Nat
  | .atom a | .proj _ _ a => a.occ i
  | .con _ as | .prim _ as | .call _ as => Atom.occList i as
  | .app f as => f.occ i + Atom.occList i as
  | .glob _ => 0
  | .fn ps b => Exp.occ (i + ps.length) b

def Exp.altsOcc (i : Nat) : List Alt → Nat
  | [] => 0
  | .mk _ n b :: as => Exp.occ (i + n) b + Exp.altsOcc i as

def Exp.optOcc (i : Nat) : Option Exp → Nat
  | none => 0
  | some e => Exp.occ i e

end

mutual

/-- Occurrences of `i` as the head of an application of at least `n`
arguments. -/
def Exp.headOcc (i n : Nat) : Exp → Nat
  | .bind _ b e => Bind.headOcc i n b + Exp.headOcc (i + 1) n e
  | .join k _ b e => Exp.headOcc (i + k) n b + Exp.headOcc i n e
  | .case _ alts d => Exp.altsHeadOcc i n alts + Exp.optHeadOcc i n d
  | .tick e => Exp.headOcc i n e
  | .jump .. | .ret _ | .trap => 0

def Bind.headOcc (i n : Nat) : Bind → Nat
  | .app (.var j) as => if i == j && as.length ≥ n then 1 else 0
  | .fn ps b => Exp.headOcc (i + ps.length) n b
  | _ => 0

def Exp.altsHeadOcc (i n : Nat) : List Alt → Nat
  | [] => 0
  | .mk _ k b :: as => Exp.headOcc (i + k) n b + Exp.altsHeadOcc i n as

def Exp.optHeadOcc (i n : Nat) : Option Exp → Nat
  | none => 0
  | some e => Exp.headOcc i n e

end

mutual

/-- Jumps to join point `j`. -/
def Exp.jocc (j : Nat) : Exp → Nat
  | .bind _ _ e => Exp.jocc j e
  | .join _ r b e => Exp.jocc (if r then j + 1 else j) b + Exp.jocc (j + 1) e
  | .jump k _ => if j == k then 1 else 0
  | .case _ alts d => Exp.altsJocc j alts + Exp.optJocc j d
  | .tick e => Exp.jocc j e
  | .ret _ | .trap => 0

def Exp.altsJocc (j : Nat) : List Alt → Nat
  | [] => 0
  | .mk _ _ b :: as => Exp.jocc j b + Exp.altsJocc j as

def Exp.optJocc (j : Nat) : Option Exp → Nat
  | none => 0
  | some e => Exp.jocc j e

end

mutual

/-- Every free value variable is below `n` (a closed body over `n`
parameters when `n` is the arity). -/
def Exp.closedBelow (n : Nat) : Exp → Bool
  | .bind _ b e => Bind.closedBelow n b && Exp.closedBelow (n + 1) e
  | .join k _ b e => Exp.closedBelow (n + k) b && Exp.closedBelow n e
  | .jump _ as => as.all (·.below n)
  | .case x alts d => x.below n && Exp.altsClosedBelow n alts && Exp.optClosedBelow n d
  | .ret a => a.below n
  | .tick e => Exp.closedBelow n e
  | .trap => true

def Bind.closedBelow (n : Nat) : Bind → Bool
  | .atom a | .proj _ _ a => a.below n
  | .con _ as | .prim _ as | .call _ as => as.all (·.below n)
  | .app f as => f.below n && as.all (·.below n)
  | .glob _ => true
  | .fn ps b => Exp.closedBelow (n + ps.length) b

def Exp.altsClosedBelow (n : Nat) : List Alt → Bool
  | [] => true
  | .mk _ k b :: as => Exp.closedBelow (n + k) b && Exp.altsClosedBelow n as

def Exp.optClosedBelow (n : Nat) : Option Exp → Bool
  | none => true
  | some e => Exp.closedBelow n e

end

/-- The free variable of an atom under `n` binders, as an index outside
them. -/
def Atom.free (n : Nat) : Atom → List Nat
  | .var i => if i ≥ n then [i - n] else []
  | _ => []

def Atom.freeList (n : Nat) : List Atom → List Nat
  | [] => []
  | a :: as => a.free n ++ Atom.freeList n as

mutual

/-- Free value variables under `n` binders, as indices outside them (with
repetition). -/
def Exp.free (n : Nat) : Exp → List Nat
  | .bind _ b e => Bind.free n b ++ Exp.free (n + 1) e
  | .join k _ b e => Exp.free (n + k) b ++ Exp.free n e
  | .jump _ as => Atom.freeList n as
  | .case x alts d => x.free n ++ Exp.altsFree n alts ++ Exp.optFree n d
  | .ret a => a.free n
  | .tick e => Exp.free n e
  | .trap => []

def Bind.free (n : Nat) : Bind → List Nat
  | .atom a | .proj _ _ a => a.free n
  | .con _ as | .prim _ as | .call _ as => Atom.freeList n as
  | .app f as => f.free n ++ Atom.freeList n as
  | .glob _ => []
  | .fn ps b => Exp.free (n + ps.length) b

def Exp.altsFree (n : Nat) : List Alt → List Nat
  | [] => []
  | .mk _ k b :: as => Exp.free (n + k) b ++ Exp.altsFree n as

def Exp.optFree (n : Nat) : Option Exp → List Nat
  | none => []
  | some e => Exp.free n e

end

mutual

/-- Globals referenced by `call` or `glob`, with repetition. -/
def Exp.refs : Exp → List GlobalId
  | .bind _ b e => Bind.refs b ++ Exp.refs e
  | .join _ _ b e => Exp.refs b ++ Exp.refs e
  | .case _ alts d => Exp.altsRefs alts ++ Exp.optRefs d
  | .tick e => Exp.refs e
  | .jump .. | .ret _ | .trap => []

def Bind.refs : Bind → List GlobalId
  | .glob g | .call g _ => [g]
  | .fn _ b => Exp.refs b
  | _ => []

def Exp.altsRefs : List Alt → List GlobalId
  | [] => []
  | .mk _ _ b :: as => Exp.refs b ++ Exp.altsRefs as

def Exp.optRefs : Option Exp → List GlobalId
  | none => []
  | some e => Exp.refs e

end

mutual

/-- Globals called by `call`, with repetition. -/
def Exp.sites : Exp → List GlobalId
  | .bind _ b e => Bind.sites b ++ Exp.sites e
  | .join _ _ b e => Exp.sites b ++ Exp.sites e
  | .case _ alts d => Exp.altsSites alts ++ Exp.optSites d
  | .tick e => Exp.sites e
  | .jump .. | .ret _ | .trap => []

def Bind.sites : Bind → List GlobalId
  | .call g _ => [g]
  | .fn _ b => Exp.sites b
  | _ => []

def Exp.altsSites : List Alt → List GlobalId
  | [] => []
  | .mk _ _ b :: as => Exp.sites b ++ Exp.altsSites as

def Exp.optSites : Option Exp → List GlobalId
  | none => []
  | some e => Exp.sites e

end

end Compilatrix.Anf
