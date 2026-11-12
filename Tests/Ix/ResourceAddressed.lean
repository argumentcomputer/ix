module

public import Ix.Ixon

public section

/-! # Small addressed Ixon environments with binder contracts

Fixtures for the claim and codec tests: a unit type's block with its
projection, constructor and recursor records, and an identity on it whose
binder carries a contract. -/

namespace Tests.ResourceAddressed

open Ixon

abbrev E := Ixon.Expr

/-- A record's address: BLAKE3 of its bytes. -/
def commit (constant : Constant) : Address := Address.blake3 (serConstant constant)

/-- A projection record. -/
def wrapper (info : Ixon.ConstantInfo) : Constant := ⟨info, #[], #[], #[]⟩

/-- A constructor's projection record. -/
def constructorWrapper (block : Address) (index ctor : UInt64) : Constant :=
  wrapper (.cPrj ⟨index, ctor, block⟩)

def store (env : Ixon.Env) (c : Constant) : Ixon.Env × Address :=
  let address := commit c
  (env.storeConst address c, address)

def unitBlock : Constant := {
  info := .muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩]
  sharing := #[], refs := #[], univs := #[.zero] }

/-- `U.rec`, the recursor of `unitBlock`'s type at `refs = [U, U.mk]`:
`{motive : U → Sort u} → motive U.mk → (t : U) → motive t`, the `k`-like
large eliminator of a `Prop` with one constructor and no fields, with the
rule `fun motive mk => mk`. Every Lean inductive comes with its recursor,
and the typing half (IxC's tiered entry) declines a block without one. -/
def unitRec (type ctor : Address) : Constant :=
  let motive := Expr.leanAll (.ref 0 #[]) (.sort 0)
  let typ := Expr.leanAll motive (Expr.leanAll (.app (.var 0) (.ref 1 #[]))
    (Expr.leanAll (.ref 0 #[]) (.app (.var 2) (.var 0))))
  { info := .recr ⟨true, false, 1, 0, 0, 1, 1, typ,
      #[⟨0, Expr.leanLam motive (Expr.leanLam (.app (.var 0) (.ref 1 #[])) (.var 0))⟩]⟩
    sharing := #[], refs := #[type, ctor], univs := #[.var 0] }

/-- The unit type's block, its projection and constructor records, and its
recursor (a separate record: the block's and the projections' addresses do
not depend on it). -/
def unitEnv : Ixon.Env × Address := Id.run do
  let (env, block) := store {} unitBlock
  let (env, type) := store env (wrapper (.iPrj ⟨0, block⟩))
  let (env, ctor) := store env (constructorWrapper block 0 0)
  let (env, _) := store env (unitRec type ctor)
  return (env, type)

def linearLocal : Ixon.BinderContract := ⟨.linear, .localShared⟩

def identity (unit : Address) (input : Ixon.BinderContract := linearLocal)
    (result : ValueContract := .localShared) : Constant := {
  info := .defn ⟨.defn, .safe, 0,
    .all input result (.ref 0 #[]) (.ref 0 #[]),
    .lam input (.ref 0 #[]) (.share 0)⟩
  sharing := #[.var 0], refs := #[unit], univs := #[] }

def fixtures : Array (String × Constant) := Id.run do
  let (_, unit) := unitEnv
  return #[ ("unit", unitBlock), ("identity", identity unit),
    ("identity_unique", identity unit ⟨.linear, .unique⟩ .unique) ]

end Tests.ResourceAddressed

end
