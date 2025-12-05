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

  enum Tag4 {
    Mk(G, [G; 8])
  }

  enum DefKind {
    Definition,
    Opaque,
    Theorem
  }

  enum BuiltIn {
    Obj,
    Neutral,
    Unreachable
  }

  enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial
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
    -- Defn(Definition),                      -- 0xA0, definition constant
    -- Recr(Recursor),                        -- 0xA1, recursor constant
    -- Axio(Axiom),                           -- 0xA2, axiom constant
    -- Quot(Quotient),                        -- 0xA3, quotient constant
    -- CPrj(ConstructorProj),                 -- 0xA4, constructor projection
    -- RPrj(RecursorProj),                    -- 0xA5, recursor projection
    -- IPrj(InductiveProj),                   -- 0xA6, inductive projection
    -- DPrj(DefinitionProj),
    -- 0xA7, definition projection
    -- Muts(Vec<MutConst>),                   -- 0xBX, mutual constants
    -- Prof(Proof),                              -- 0xE0, zero-knowledge proof
    Eval(Address, Address, Address, Address), -- 0xE1, evaluation claim
    Chck(Address, Address, Address),          -- 0xE2, typechecking claim
    Comm(Address, Address),                   -- 0xE3, cryptographic commitment
    -- Envn(Env),                             -- 0xE4, multi-claim environment
    Prim(BuiltIn)                             -- 0xE5, compiler built-ins
    -- Meta(Metadata)                            --  0xFX, metadata
  }
⟧

end IxVM
