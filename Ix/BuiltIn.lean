
namespace Ix

inductive BuiltIn where
| commit
| reveal
deriving Inhabited, Repr, BEq, Ord, Hashable

end Ix

--structure Commitment (α : Type _) where
--  adr : Address
--  deriving Inhabited, Lean.ToExpr
--
--instance : ToString (Commitment α) where
--  toString comm := "c" ++ toString comm.adr

--def Commitment.ofString (s : String) : Option $ Commitment α :=
--  match s.data with
--  | 'c' :: adrChars => .mk <$> Address.fromString ⟨adrChars⟩
--  | _ => none
--
---- TODO: secrets should be 32-bytes long
--opaque commit (secret : Address) (payload : α) : Commitment α
--opaque secret (comm : Commitment α) : Address
--opaque reveal [Inhabited α] (comm : Commitment α) : α
--opaque revealThen [Inhabited β] (comm : Commitment α) (f : β) : β

--def persistCommit (secret : Address) (payload : Address) : IO $ Commitment α :=
--  let commAdr := Blake3.hash $ secret.hash ++ payload.hash
--  -- TODO: persist commitment preimages as private data
--  return ⟨⟨commAdr.val⟩⟩
--
--def mkCommitRaw 
--  (secret : Address) (type : Lean.Expr) (value : Lean.Expr)
--  (consts : Lean.ConstMap)
--  : IO (Commitment α) := do
--  let adr <- computeIxAddress (mkAnonDefInfoRaw type value) consts
--  persistCommit secret adr
--
--def mkCommit [Lean.ToExpr α] (secret : Address) (a : α) (consts : Lean.ConstMap) 
--  : IO (Commitment α) := do
--  let adr <- (computeIxAddress (mkAnonDefInfo a) consts)
--  persistCommit secret adr

--namespace Ix.BuiltIn

--inductive Commitment (A: Type _) where
--| comm
--
--opaque commit : Nat -> 

--structure TypeProof where
--  value : Address
--  type : Address
--  bin : ByteArray
--  deriving Inhabited

--structure TypeProofD (A: Type) where
--  value : AddressD A
--  type : AddressD Type
--  bin : ByteArray
--  proof: Validates bin type value
--  deriving Inhabited
--
--opaque TypeProof.commit.{u} (α : Type u) (a : α) (secret: Nat := 0)  : TypeProof
--opaque TypeProof.reveal.{u} (α : Type u) (t: TypeProof) (secret: Nat := 0) : Option α
--opaque TypeProof.verify (t: TypeProof) : Bool
--
--opaque TypeProof.revealD.{u} (α : Type u) (t: TypeProofD) (secret: Nat := 0) : α

--structure EvalProof where
--  input : TypeProof
--  output: TypeProof
--  bin: ByteArray
--  deriving Inhabited
--
--opaque EvalProof.prove (input output: TypeProof) (secret: Nat := 0) : EvalProof
--opaque EvalProof.verify (p: Proof) : Bool
--opaque EvalProof.eval.{u} (α: Type u) (p: EvalProof) (a: α) : Option α

-- def f x := if x == 1 then 42 else 0
-- let p := EvalProof { <f 1 ~> 42> }
-- p.eval 1 ~> 42

--end Ix.BuiltIn
