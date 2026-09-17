import Compilatrix.IxIR0.Eval
import Ix.Ixby

/-! The Ixby backend refines the erased, pure IxIR₀ boundary directly. -/

namespace Compilatrix.Ixby

open Ixon (Address)

structure Source where
  declarations : List (Address × IxIR0.Decl)
  main : IxIR0.Expr
  /-- Inputs are supplied in application order; de Bruijn zero is the last input. -/
  parameters : Nat := 0
  deriving BEq, Repr, Inhabited

def Source.ctx (source : Source) : IxIR0.Ctx :=
  { env := IxIR0.Env.Index.toEnv (IxIR0.Env.Index.ofList source.declarations) }

structure Config where
  limits : Ix.Ixby.Limits := {}
  depth : Nat := 10000
  work : Nat := 1000000
  deriving BEq, Repr, Inhabited

/-- Private boxes have member 1; source constructors always have member 0. -/
def boxId (tag : Nat) : Ix.Ixby.CtorId := { block := 0, member := 1, tag }

/-- The source's full 32 address bytes, interpreted little endian. No hashing,
truncation to a machine word, or equality of digests is assumed by the ABI. -/
def constructorId (address : Address) (tag : Nat) : Ix.Ixby.CtorId :=
  { block := ⟨address.hash.data.foldr (fun byte acc => acc * 256 + byte.toNat) 0 %
      (2 ^ 256), Nat.mod_lt _ (by decide)⟩, member := 0, tag }

structure Constructor where
  address : Address
  tag : Nat
  fields : Nat
  deriving BEq, Repr, Inhabited

def Constructor.id (ctor : Constructor) : Ix.Ixby.CtorId := constructorId ctor.address ctor.tag

def Source.constructors (source : Source) : Array Constructor :=
  (source.declarations.filterMap fun (address, decl) => match decl with
    | .ctor tag fields => some { address, tag, fields }
    | _ => none).toArray

def constructorTable (source : Source) : Array Ix.Ixby.CtorDecl :=
  #[{ id := boxId 0, fields := 0 }, { id := boxId 1, fields := 1 },
    { id := boxId 2, fields := 1 }, { id := boxId 3, fields := 1 }] ++
  source.constructors.map (fun ctor => { id := ctor.id, fields := ctor.fields })

/-- First-backend external data ABI. Functions execute internally, but cannot
be supplied or decoded as host data. Constructor addresses and tags are retained. -/
inductive Data where
  | nat (value : Nat)
  | str (value : String)
  | ctor (address : Address) (tag : Nat) (fields : List Data)
  | erased
  deriving Repr, Inhabited

/- Total structural equality; the derived nested BEq would be opaque. -/
mutual
  def Data.equal : Data → Data → Bool
    | .nat a, .nat b => a == b
    | .str a, .str b => a == b
    | .ctor a t xs, .ctor b u ys => a == b && t == u && Data.equalFields xs ys
    | .erased, .erased => true
    | _, _ => false
  def Data.equalFields : List Data → List Data → Bool
    | [], [] => true
    | x :: xs, y :: ys => Data.equal x y && Data.equalFields xs ys
    | _, _ => false
end

instance : BEq Data := ⟨Data.equal⟩


/-- Runtime equality checks retain ordinary kernel equality evidence. -/
theorem Data.eq_of_equal (a : Data) : ∀ b, Data.equal a b = true → a = b := by
  induction a using Data.rec
      (motive_2 := fun xs => ∀ ys, Data.equalFields xs ys = true → xs = ys) with
  | nat n => intro b h; cases b <;> simp_all [Data.equal]
  | str s => intro b h; cases b <;> simp_all [Data.equal]
  | ctor address tag fields ih =>
    intro b h
    cases b <;> simp_all [Data.equal]
    exact ih _ h.2
  | erased => intro b h; cases b <;> simp_all [Data.equal]
  | nil =>
    rename_i ys h
    cases ys <;> simp_all [Data.equalFields]
  | cons head tail ihHead ihTail =>
    rename_i ys h
    cases ys <;> simp_all [Data.equalFields]
    exact ⟨ihHead _ h.1, ihTail _ h.2⟩


def Data.toValue : Data → IxIR0.Value
  | .nat n => .lit (.nat n)
  | .str s => .lit (.str s)
  | .ctor address tag fields => .ctor address tag (fields.map Data.toValue)
  | .erased => .erased

/-- Observation is bounded independently of machine execution; function
results are reported as outside the external data ABI. -/
def observe : Nat → IxIR0.Value → Option Data
  | 0, _ => none
  | fuel + 1, value => match value with
    | .lit (.nat n) => some (.nat n)
    | .lit (.str s) => some (.str s)
    | .ctor address tag fields => return .ctor address tag (← fields.mapM (observe fuel))
    | .erased => some .erased
    | _ => none

/-- Bound the whole host input forest before constructing target boxes. -/
def admitData (limits : Ix.Ixby.Limits) : Nat → List Data → Except String Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error "Ixby input data node limit"
  | remaining + 1, value :: rest => do
      match value with
      | .ctor _ _ fields =>
          if fields.length > limits.operands then throw "Ixby input field count limit"
          admitData limits remaining (fields ++ rest)
      | _ => admitData limits remaining rest


def encodeData (source : Source) (config : Config) : Nat → Data → Except String Ix.Ixby.Value
  | 0, _ => .error "Ixby input data depth limit"
  | fuel + 1, data => match data with
    | .nat n => .ok (.ctor (boxId 1) #[.scalar (.nat n)])
    | .str s => .ok (.ctor (boxId 2) #[.scalar (.str s)])
    | .erased => .ok (.ctor (boxId 0) #[])
    | .ctor address tag fields => do
        unless source.constructors.any (fun ctor => ctor.address == address &&
            ctor.tag == tag && ctor.fields == fields.length) do
          throw "Ixby input constructor is outside the compiled ABI"
        return .ctor (constructorId address tag)
          (← fields.mapM (encodeData source config fuel)).toArray

def decodeData (source : Source) : Nat → Ix.Ixby.Value → Option Data
  | 0, _ => none
  | fuel + 1, .ctor id fields => do
      if id == boxId 0 then
        if fields.isEmpty then some .erased else none
      else if id == boxId 1 then
        match fields.toList with
        | [.scalar (.nat n)] => some (.nat n)
        | _ => none
      else if id == boxId 2 then
        match fields.toList with
        | [.scalar (.str s)] => some (.str s)
        | _ => none
      else
        let ctor ← source.constructors.find? (fun ctor => ctor.id == id)
        if fields.size != ctor.fields then none else
          return .ctor ctor.address ctor.tag (← fields.toList.mapM (decodeData source fuel))
  | _, _ => none

end Compilatrix.Ixby
