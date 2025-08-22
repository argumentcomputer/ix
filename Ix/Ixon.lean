import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import Ix.Claim
import Ix.Ixon.Tag
import Ix.Ixon.Const
import Ix.Ixon.Metadata

namespace Ixon

inductive Ixon where
| vari : UInt64 -> Ixon                       -- 0x0X, variables
| sort : Univ -> Ixon                         -- 0x90, universes
| refr : Address -> List Univ -> Ixon         -- 0x1X, global reference
| recr : UInt64 -> List Univ -> Ixon          -- 0x2X, local recursion
| apps : Ixon -> Ixon -> List Ixon -> Ixon    -- 0x3X, funciton application
| lams : List Ixon -> Ixon -> Ixon            -- 0x4X, lambda abstraction
| alls : List Ixon -> Ixon -> Ixon            -- 0x5X, universal quantification
| letE : Bool -> Ixon -> Ixon -> Ixon -> Ixon -- 0x91, 0x92 let expression
| proj : Address -> UInt64 -> Ixon -> Ixon    -- 0x6X, structure projection
| strl : String -> Ixon                       -- 0x7X, utf8 string
| natl : Nat -> Ixon                          -- 0x8X, natural number
| list : List Ixon -> Ixon                    -- 0xAX, list
| defn : Definition -> Ixon                   -- 0xB0, definition
| axio : Axiom -> Ixon                        -- 0xB1, axiom
| quot : Quotient -> Ixon                     -- 0xB2, quotient
| cprj : ConstructorProj -> Ixon              -- 0xB3, ctor projection
| rprj : RecursorProj -> Ixon                 -- 0xB4, recr projection
| iprj : InductiveProj -> Ixon                -- 0xB5, indc projection
| dprj : DefinitionProj -> Ixon               -- 0xB6, defn projection
| inds : List Inductive -> Ixon               -- 0xCX, mutual inductive types
| defs : List Definition -> Ixon              -- 0xDX, mutual definitions
| meta : Metadata -> Ixon                     -- 0xE0, Lean4 metadata
| prof : Proof -> Ixon                        -- 0xE1, zero-knowledge proof
| eval : EvalClaim -> Ixon                    -- 0xE2, cryptographic claim
| chck : CheckClaim -> Ixon                   -- 0xE3, cryptographic claim
| comm : Comm -> Ixon                         -- 0xE4, cryptographic commitment
| envn : Unit -> Ixon                         -- 0xE5, Lean4 environment
deriving BEq, Repr, Inhabited

open Serialize

partial def putIxon : Ixon -> PutM Unit
| .vari i => put (Tag4.mk 0x0 i)
| .sort u => put (Tag4.mk 0x9 0x0) *> put u
| .refr a lvls => do
  put (Tag4.mk 0x1 lvls.length.toUInt64) *> put a *> putMany putUniv lvls
| .recr i lvls => put (Tag4.mk 0x2 i) *> putList lvls
| .apps f a as => do
  put (Tag4.mk 0x3 as.length.toUInt64)
  putIxon f *> putIxon a *> putMany putIxon as
| .lams ts b => do
  put (Tag4.mk 0x4 ts.length.toUInt64) *> putMany putIxon ts *> putIxon b
| .alls ts b => do
  put (Tag4.mk 0x5 ts.length.toUInt64) *> putMany putIxon ts *> putIxon b
| .letE nD t d b => do
  if nD then put (Tag4.mk 0x9 0x1) else put (Tag4.mk 0x9 0x2)
  putIxon t *> putIxon d *> putIxon b
| .proj t n x => put (Tag4.mk 0x6 n) *> putBytes t.hash *> putIxon x
| .strl s => putString s -- 0x7
| .natl n => putNat n -- 0x8
| .list xs => do
  put (Tag4.mk 0xA xs.length.toUInt64)
  List.forM xs putIxon
| .defn x => put (Tag4.mk 0xB 0x0) *> put x
| .axio x => put (Tag4.mk 0xB 0x1) *> put x
| .quot x => put (Tag4.mk 0xB 0x2) *> put x
| .cprj x => put (Tag4.mk 0xB 0x3) *> put x
| .rprj x => put (Tag4.mk 0xB 0x4) *> put x
| .iprj x => put (Tag4.mk 0xB 0x5) *> put x
| .dprj x => put (Tag4.mk 0xB 0x6) *> put x
| .inds xs => put (Tag4.mk 0xC xs.length.toUInt64) *> putMany put xs
| .defs xs => put (Tag4.mk 0xD xs.length.toUInt64) *> putMany put xs
| .meta x => put (Tag4.mk 0xE 0x0) *> put x
| .prof x => put (Tag4.mk 0xE 0x1) *> put x
| .eval x => put (Tag4.mk 0xE 0x2) *> put x
| .chck x => put (Tag4.mk 0xE 0x3) *> put x
| .comm x => put (Tag4.mk 0xE 0x4) *> put x
| .envn x => put (Tag4.mk 0xE 0x5) *> put x

def getIxon : GetM Ixon := do
  let st ← MonadState.get
  go (st.bytes.size - st.idx)
  where
    go : Nat → GetM Ixon
    | 0 => throw "Out of fuel"
    | Nat.succ f => do
      let tag <- getTag4
      match tag with
      | ⟨0x0, x⟩ => pure <| .vari x
      | ⟨0x9, 0⟩ => .sort <$> getUniv
      | ⟨0x1, x⟩ => .refr <$> get <*> getMany x getUniv
      | ⟨0x2, x⟩ => .recr <$> pure x <*> get
      | ⟨0x3, x⟩ => .apps <$> go f <*> go f <*> getMany x (go f)
      | ⟨0x4, x⟩ => .lams <$> getMany x (go f) <*> go f
      | ⟨0x5, x⟩ => .alls <$> getMany x (go f) <*> go f
      | ⟨0x9, 1⟩ => .letE true <$> go f <*> go f <*> go f
      | ⟨0x9, 2⟩ => .letE false <$> go f <*> go f <*> go f
      | ⟨0x6, x⟩ => .proj <$> get <*> pure x <*> go f
      | ⟨0x7, _⟩ => .strl <$> getString' tag
      | ⟨0x8, _⟩ => .natl <$> getNat' tag
      | ⟨0xA, x⟩ => .list <$> getMany x (go f)
      | ⟨0xB, 0x0⟩ => .defn <$> get
      | ⟨0xB, 0x1⟩ => .axio <$> get
      | ⟨0xB, 0x2⟩ => .quot <$> get
      | ⟨0xB, 0x3⟩ => .cprj <$> get
      | ⟨0xB, 0x4⟩ => .rprj <$> get
      | ⟨0xB, 0x5⟩ => .iprj <$> get
      | ⟨0xB, 0x6⟩ => .dprj <$> get
      | ⟨0xC, x⟩ => .inds <$> getMany x get
      | ⟨0xD, x⟩ => .defs <$> getMany x get
      | ⟨0xE, 0x0⟩ => .meta <$> get
      | ⟨0xE, 0x1⟩ => .prof <$> get
      | ⟨0xE, 0x2⟩ => .eval <$> get
      | ⟨0xE, 0x3⟩ => .chck <$> get
      | ⟨0xE, 0x4⟩ => .comm <$> get
      | ⟨0xE, 0x5⟩ => .envn <$> get
      | x => throw s!"Unknown Ixon tag {repr x}"

instance : Serialize Ixon where
  put := putIxon
  get := getIxon

end Ixon

