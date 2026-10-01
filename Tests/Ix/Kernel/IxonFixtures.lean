import Ix.Ixon.Types

/-! # Ixon record fixtures

Small canonical Ixon records shared by the codec, byte-admission, projection
and block-order tests: a polymorphic identity (plain, with sharing, and an
alias referring to it), a constructor-free `False` family with its large
eliminator (as one block and as separately stored family and recursor
records, with their projections), and a mutual block exercising every
member kind, table and contract. -/

namespace Tests.Ix.Kernel.IxonFixtures

def address (tag : UInt8) : Address := ⟨⟨Array.replicate 32 tag⟩⟩

def idType : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
def idBody : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))

def identity : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 1, idType, idBody⟩, #[], #[], #[.var 0]⟩

def sharedIdentity : Ixon.Constant :=
  { identity with
    info := .defn ⟨.defn, .safe, 1, .share 0, .share 2⟩
    sharing := #[idType, idBody, .share 1] }

def aliasIdentity : Ixon.Constant :=
  { identity with
    info := .defn ⟨.defn, .safe, 1, idType, .ref 0 #[0]⟩
    refs := #[address 1] }

/-- A no-constructor inductive and its large eliminator in one block. -/
def falseBlock : Ixon.Constant :=
  let falseType : Ixon.Expr := .recur 0 #[]
  let motive := Ixon.Expr.leanAll falseType (.sort 1)
  let recType := Ixon.Expr.leanAll motive
    (.leanAll falseType (.app (.var 1) (.var 0)))
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[]⟩,
    .recr ⟨false, false, 1, 0, 0, 1, 0, recType, #[]⟩], #[], #[], #[.zero, .var 0]⟩

def falseProjection : Ixon.Constant := ⟨.iPrj ⟨0, address 3⟩, #[], #[], #[]⟩
def recProjection : Ixon.Constant := ⟨.rPrj ⟨1, address 3⟩, #[], #[], #[]⟩
def falseStore : List (Address × Ixon.Constant) :=
  [(address 3, falseBlock), (address 4, falseProjection), (address 5, recProjection)]

/-- Physical Ixon layout: the family and recursor have independent owners. -/
def falseFamily : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[]⟩], #[], #[], #[.zero]⟩

def falseRecursor : Ixon.Recursor :=
  let falseType := Ixon.Expr.ref 0 #[]
  let motive := Ixon.Expr.leanAll falseType (.sort 1)
  ⟨false, false, 1, 0, 0, 1, 0,
    .leanAll motive (.leanAll falseType (.app (.var 1) (.var 0))), #[]⟩

def falseRecursorRecord (recursor : Ixon.Recursor := falseRecursor) : Ixon.Constant :=
  ⟨.recr recursor, #[], #[address 4], #[.zero, .var 0]⟩

def separatedFalse (recursor : Ixon.Recursor := falseRecursor) : List (Address × Ixon.Constant) :=
  [(address 3, falseFamily), (address 6, falseRecursorRecord recursor), (address 4, falseProjection)]

/-- Every member kind, unused and repeated table slots, sharing, and
non-default contracts (serialization fixture; not well typed). -/
def variedBlock : Ixon.Constant :=
  ⟨.muts #[
    .defn ⟨.opaq, .part, 2, .sort 2,
      .letE (.lean true) (.sort 0) (.ref 1 #[2, 1]) (.var 0)⟩,
    .indc ⟨true, 3, 4, 5, .sort 0, #[⟨true, 6, 0, 7, 8, .recur 1 #[]⟩]⟩,
    .recr ⟨true, true, 9, 10, 11, 12, 13, .sort 1,
      #[⟨14, .share 1⟩, ⟨15, .var 0⟩]⟩],
    #[.var 2, .share 0, .var 99], #[address 1, address 1, address 99],
    #[.zero, .var 0, .zero, .max (.var 0) (.var 1)]⟩

/-- Every record variant, including all four projection kinds. -/
def variants : List (Address × Ixon.Constant) :=
  [(address 1, identity), (address 12, variedBlock),
   (address 13, ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩),
   (address 14, ⟨.iPrj ⟨1, address 12⟩, #[], #[], #[]⟩),
   (address 15, ⟨.cPrj ⟨1, 0, address 12⟩, #[], #[], #[]⟩),
   (address 16, ⟨.rPrj ⟨2, address 12⟩, #[], #[], #[]⟩),
   (address 17, ⟨.axio ⟨true, 18446744073709551615, .sort 0⟩, #[], #[], #[.zero]⟩)]

end Tests.Ix.Kernel.IxonFixtures
