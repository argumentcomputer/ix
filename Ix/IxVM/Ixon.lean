import Ix.Aiur.Meta

namespace IxVM

def ixon := ⟦
  enum Address {
    Bytes([[G; 4]; 8])
  }

  enum Nat {
    Bytes(ByteStream)
  }

  enum AddressList {
    Cons(Address, &AddressList),
    Nil
  }

  enum RecursorRuleList {
    Cons(Nat, Address, &RecursorRuleList),
    Nil
  }

  enum MutConstList {
    ConsDefn(
      DefKind,
      DefinitionSafety,
      Nat,
      Address,
      Address,
      &MutConstList
    ),
    ConsIndc(
      G, G, G,
      Nat, Nat, Nat, Nat,
      Address, ConstructorList,
      &MutConstList
    ),
    ConsRecr(
      G, G,
      Nat, Nat, Nat, Nat, Nat,
      Address, RecursorRuleList,
      &MutConstList
    ),
    Nil
  }

  enum ConstructorList {
    Cons(G, Nat, Nat, Nat, Nat, Address, &ConstructorList),
    Nil
  }

  enum Tag4 {
    Mk(G, [G; 8])
  }

  enum DefKind {
    Definition,
    Opaque,
    Theorem
  }

  enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial
  }

  enum QuotKind {
    Typ,
    Ctor,
    Lift,
    Ind
  }

  enum Claim {
    Evals(Address, Address, Address, Address),
    Checks(Address, Address, Address)
  }

  enum Ixon {
    NAnon,                                 -- 0x00, anonymous name
    NStr(Address, Address),                -- 0x01, string name
    NNum(Address, Address),                -- 0x02, number name
    UZero,                                 -- 0x03, universe zero
    USucc(Address),                        -- 0x04, universe successor
    UMax(Address, Address),                -- 0x05, universe max
    UIMax(Address, Address),               -- 0x06, universe impredicative max
    UVar(Nat),                             -- 0x1X, universe variable
    EVar(Nat),                             -- 0x2X, expression variable
    ERef(Address, AddressList),            -- 0x3X, expression reference
    ERec(Nat, AddressList),                -- 0x4X, expression recursion
    EPrj(Address, Nat, Address),           -- 0x5X, expression projection
    ESort(Address),                        -- 0x80, expression sort
    EStr(Address),                         -- 0x81, expression string
    ENat(Address),                         -- 0x82, expression natural
    EApp(Address, Address),                -- 0x83, expression application
    ELam(Address, Address),                -- 0x84, expression lambda
    EAll(Address, Address),                -- 0x85, expression forall
    ELet(G, Address, Address, Address),    -- 0x86, 0x87, expression let. TODO: change the first argument to a Bool
    Blob(ByteStream),                      -- 0x9X, tagged bytes
    Defn(                                  -- 0xA0, definition constant
      DefKind,
      DefinitionSafety,
      Nat,
      Address,
      Address
    ),
    Recr(                                  -- 0xA1, recursor constant
      G, G,
      Nat, Nat, Nat, Nat, Nat,
      Address, RecursorRuleList
    ),
    Axio(G, Nat, Address),                    -- 0xA2, axiom constant. TODO: change the first argument to a Bool
    Quot(QuotKind, Nat, Address),             -- 0xA3, quotient constant
    CPrj(Nat, Nat, Address),                  -- 0xA4, constructor projection
    RPrj(Nat, Address),                       -- 0xA5, recursor projection
    IPrj(Nat, Address),                       -- 0xA6, inductive projection
    DPrj(Nat, Address),                       -- 0xA7, definition projection
    Muts(MutConstList),                       -- 0xBX, mutual constants
    Prof(Claim, ByteStream),                  -- 0xE0, zero-knowledge proof
    Eval(Address, Address, Address, Address), -- 0xE1, evaluation claim
    Chck(Address, Address, Address),          -- 0xE2, typechecking claim
    Comm(Address, Address),                   -- 0xE3, cryptographic commitment
    Envn(AddressList)                         -- 0xE4, multi-claim environment
    -- Prim(BuiltIn)                          -- 0xE5, compiler built-ins
    -- Meta(Metadata)                         --  0xFX, metadata
  }
⟧

end IxVM
