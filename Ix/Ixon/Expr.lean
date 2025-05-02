import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ

namespace Ixon

-- 0xTTTT_LXXX
inductive Expr where
  -- 0x0, ^1
  | vari (idx: UInt64) : Expr
  -- 0x1, {max (add 1 2) (var 1)}
  | sort (univ: Univ) : Expr
  -- 0x2 #dead_beef_cafe_babe {u1, u2, ... }
  | cnst (adr: Address) (lvls: List Univ) : Expr
  -- 0x3 #1.{u1, u2, u3}
  | rec_ (idx: UInt64) (lvls: List Univ) : Expr
  -- 0x4 (f x y z)
  | apps (func: Expr) (arg: Expr) (args: List Expr) : Expr
  -- 0x5 (λ A B C => body)
  | lams (types: List Expr) (body: Expr) : Expr
  -- 0x6 (∀ A B C -> body)
  | alls (types: List Expr) (body: Expr) : Expr
  -- 0x7 (let d : A in b)
  | let_ (nonDep: Bool) (type: Expr) (defn: Expr) (body: Expr) : Expr
  -- 0x8 .1
  | proj (type: Address) (idx: UInt64) (struct: Expr): Expr
  -- 0x9 "foobar"
  | strl (lit: String) : Expr
  -- 0xA 0xdead_beef
  | natl (lit: Nat): Expr
  deriving Inhabited, Repr, BEq
-- array: 0xB
-- const: 0xC


def putExprTag (tag: UInt8) (val: UInt64) : PutM :=
  let t := UInt8.shiftLeft tag 4
  if val < 8
  then putUInt8 (UInt8.lor t (UInt64.toUInt8 val)) *> pure ()
  else do
    putUInt8 (UInt8.lor (UInt8.lor t 0b1000) (byteCount val - 1))
    putTrimmedLE val

partial def putExpr : Expr -> PutM
| .vari i => putExprTag 0x0 i
| .sort u => putExprTag 0x1 0 *> putUniv u
| .cnst a lvls => do
  putExprTag 0x2 (Nat.toUInt64 lvls.length)
  putBytes a.hash *> putList putUniv lvls
| .rec_ i lvls => do
  putExprTag 0x3 (Nat.toUInt64 lvls.length)
  putUInt64LE i *> putList putUniv lvls
| .apps f a as => do
  putExprTag 0x4 (Nat.toUInt64 as.length)
  putExpr f *> putExpr a *> putList putExpr as
| .lams ts b => do
  putExprTag 0x5 (Nat.toUInt64 ts.length)
  putList putExpr ts *> putExpr b
| .alls ts b => do
  putExprTag 0x6 (Nat.toUInt64 ts.length) *>
  putList putExpr ts *> putExpr b
| .let_ nD t d b => do
  if nD then putExprTag 0x7 1 else putExprTag 0x7 0
  putExpr t *> putExpr d *> putExpr b
| .proj t n x => do
  putExprTag 0x8 n
  putBytes t.hash
  putExpr x
| .strl l => do
  let bytes := l.toUTF8
  putExprTag 0x9 (UInt64.ofNat bytes.size)
  putBytes bytes
| .natl l => do
  let bytes := natToBytesLE l
  putExprTag 0xA (UInt64.ofNat bytes.size)
  putBytes { data := bytes }

def getExprTag (isLarge: Bool) (small: UInt8) : GetM UInt64 := do
  if isLarge then (fromTrimmedLE ·.data) <$> getBytes (UInt8.toNat small + 1)
  else return Nat.toUInt64 (UInt8.toNat small)

def getExpr : GetM Expr := do
  let st ← get
  go (st.bytes.size - st.index)
  where
    go : Nat → GetM Expr
    | 0 => throw "Out of fuel"
    | Nat.succ f => do
      let tagByte ← getUInt8
      let tag := UInt8.shiftRight tagByte 4
      let small := UInt8.land tagByte 0b111
      let isLarge := UInt8.land tagByte 0b1000 != 0
      match tag with
      | 0x0 => .vari <$> getExprTag isLarge small
      | 0x1 => .sort <$> getUniv
      | 0x2 => do
        let n ← getExprTag isLarge small
        .cnst <$> (Address.mk <$> getBytes 32) <*> getList n getUniv
      | 0x3 => do
        let n ← getExprTag isLarge small
        .rec_ <$> getUInt64LE <*> getList n getUniv
      | 0x4 => do
        let n ← getExprTag isLarge small
        .apps <$> go f <*> go f <*> getList n (go f)
      | 0x5 => do
        let n ← getExprTag isLarge small
        .lams <$> getList n (go f) <*> go f
      | 0x6 => do
        let n ← getExprTag isLarge small
        .alls <$> getList n (go f) <*> go f
      | 0x7 => do
        let n ← getExprTag isLarge small
        if n == 0 then
          .let_ .false <$> go f <*> go f <*> go f
        else 
          .let_ .true <$> go f <*> go f <*> go f
      | 0x8 => do
        let n ← getExprTag isLarge small
        .proj <$> (Address.mk <$> getBytes 32) <*> pure n <*> go f
      | 0x9 => do
        let n ← getExprTag isLarge small
        let bs ← getBytes n.toNat
        match String.fromUTF8? bs with
        | .some s => return .strl s
        | .none => throw s!"invalid UTF8 bytes {bs}"
      | 0xA => do
        let n ← getExprTag isLarge small
        let bs ← getBytes n.toNat
        return .natl (natFromBytesLE bs.data)
      | x => throw s!"Unknown Ixon Expr tag {x}"

instance : Serialize Expr where
  put := runPut ∘ putExpr
  get := runGet getExpr

def putArray (xs : List PutM) : PutM := do
  putExprTag 0xB (UInt64.ofNat xs.length)
  List.forM xs id

def putByteArray (x: ByteArray) : PutM := do
  putExprTag 0xB (UInt64.ofNat x.size)
  x.toList.forM putUInt8

def getArray (getM: GetM A) : GetM (List A) := do
  let tagByte ← getUInt8
  let tag := UInt8.shiftRight tagByte 4
  let small := UInt8.land tagByte 0b111
  let isLarge := (UInt8.land tagByte 0b1000 != 0)
  match tag with
  | 0xB => do
    let len <- UInt64.toNat <$> getExprTag isLarge small
    List.mapM (λ _ => getM) (List.range len) 
  | e => throw s!"expected Array with tag 0xB, got {e}"

def getByteArray : GetM ByteArray := do
  let xs <- getArray getUInt8
  return ⟨xs.toArray⟩


def putOption (putM: A -> PutM): Option A → PutM
| .none => putArray []
| .some x => putArray [putM x]

def getOption [Repr A] (getM: GetM A): GetM (Option A) := do
  match ← getArray getM with
  | [] => return .none
  | [x] => return .some x
  | e => throw s!"Expected Option, got {repr e}"

def putNatl (x: Nat) : PutM := putExpr (.natl x)
def getNatl : GetM Nat := do
  match (← getExpr) with
  | .natl n => return n
  | x => throw s!"expected Expr.Nat, got {repr x}"

end Ixon
