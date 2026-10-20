/-! # Lean sources of the Source-mode check's own fixtures

Ordinary Lean declarations, checked by Lean's kernel, that
`Tests.Ix.Kernel.SourceIngress` checks in Source mode beside the Ixon reader's
fixtures (`Tests.Ix.Kernel.ReaderFidelityDefs`): a quotient whose closure does
not reach the pinned `Nat` operations (the reader's fixture quotient divides,
so it is blocked at the empty pin list), used through `Quot.lift`, `Quot.ind`
and `Quot.sound`. The module imports only `Init`. -/

namespace Tests.Ix.Kernel.SourceIngressDefs

def boolRel (a b : Bool) : Prop := a = b ∨ True

def BoolQ : Type := Quot boolRel

def BoolQ.mk (b : Bool) : BoolQ := Quot.mk boolRel b

def BoolQ.const (q : BoolQ) : Nat := Quot.lift (fun _ => 0) (fun _ _ _ => rfl) q

theorem BoolQ.mk_eq (a b : Bool) : BoolQ.mk a = BoolQ.mk b := Quot.sound (Or.inr trivial)

theorem BoolQ.const_eq (q : BoolQ) : q.const = 0 :=
  Quot.ind (β := fun q : BoolQ => q.const = 0) (fun _ => rfl) q

end Tests.Ix.Kernel.SourceIngressDefs

/-! ## Alias fibers (quotient Source, `ALPHA-COLLAPSE.md` §8.4)

`aliasOne` and `aliasTwo` are α-equal, so they are one fiber; `aliasUser`
references the second, and after the collapse the first. `aliasOther` is not
equal to them. `Flag` is `Bool` up to names: its block is a role alias. -/

namespace Tests.Ix.Kernel.SourceIngressDefs

def aliasOne : Nat := Nat.succ Nat.zero

def aliasTwo : Nat := Nat.succ Nat.zero

def aliasUser : Nat := Nat.succ aliasTwo

def aliasOther : Nat := Nat.zero

inductive Flag where
  | off
  | on

end Tests.Ix.Kernel.SourceIngressDefs
