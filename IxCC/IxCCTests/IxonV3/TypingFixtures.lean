import IxCC.Ixon.V3.Validate

/-! Small addressed fixtures adapted from the producer's
Tests/Ix/Tc/{IxonFixtures,CheckTests}.lean at the v3 source pin, framed as Ixon v4.
The byte writer is test-only; production admission always reads bytes. -/

namespace IxCCTests.IxonV3.TypingFixtures

open IxCC.Ixon IxCC.Ixon.V3

abbrev E := IxCC.Ixon.V3.Expr
abbrev C := IxCC.Ixon.V3.Constant
abbrev Environment := IxCC.Ixon.V3.Env

def arrow (a b : E) : E := .all .many .shared a b
def lambda (a b : E) : E := .lam .many a b

def store (env : Environment) (c : C) : Environment × IxCC.Ixon.Address :=
  let raw := constantBytes c
  let address := Address.blake3 raw
  ({ env with consts := env.consts.insert address raw }, address)

def block (env : Environment) (c : C) : Environment × IxCC.Ixon.Address := Id.run do
  let (env, address) := store env c
  let mut env := env
  if let .muts members := c.info then
    for i in [:members.size] do
      let wrapper : V3.ConstantInfo := match members[i]! with
        | .defn _ => .dPrj ⟨i.toUInt64, address⟩
        | .indc _ => .iPrj ⟨i.toUInt64, address⟩
        | .recr _ => .rPrj ⟨i.toUInt64, address⟩
      env := (store env ⟨wrapper, #[], #[], #[]⟩).1
      if let .indc ind := members[i]! then
        for j in [:ind.ctors.size] do
          env := (store env ⟨.cPrj ⟨i.toUInt64, j.toUInt64, address⟩, #[], #[], #[]⟩).1
  return (env, address)

def axiomType : C := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
def base : Environment × IxCC.Ixon.Address := store {} axiomType

def identity (a : IxCC.Ixon.Address) : C :=
  ⟨.defn ⟨.defn, .safe, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
    lambda (.ref 0 #[]) (.var 0)⟩, #[], #[a], #[]⟩

def natLike : V3.Inductive :=
  ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
      ⟨false, 0, 1, 0, 1, arrow (.recur 0 #[]) (.recur 0 #[])⟩]⟩

def indEnv (ind : V3.Inductive) (univs : Array Univ := #[.succ .zero]) : Environment :=
  (block {} ⟨.muts #[.indc ind], #[], #[], univs⟩).1

/-- The producer's canonical singleton recursor and independent mutations. -/
def recursorEnv (k tamper : Bool) (levelCount : UInt64 := 1) : Environment := Id.run do
  let ind : V3.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let (env, parent) := block {} ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let motive := arrow (.ref 0 #[]) (.sort 0)
  let typ := arrow motive (arrow (.app (.var 0) (.ref 1 #[]))
    (arrow (.ref 0 #[]) (.app (.var 2) (.var 0))))
  let rhs := lambda motive (lambda (.app (.var 0) (.ref 1 #[]))
    (.var (if tamper then 1 else 0)))
  let recursor : V3.Recursor := ⟨k, false, levelCount, 0, 0, 1, 1, typ, #[⟨0, rhs⟩]⟩
  return (block env ⟨.muts #[.recr recursor], #[],
    #[V3.indcProjAddr parent 0, V3.ctorProjAddr parent 0 0], #[.var 0]⟩).1

/-- Independent framing for constructing complete adversarial input files. -/
def bytes (env : Environment) : ByteArray := _root_.Ixon.runPut do
  let constants := env.consts.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  let blobs := env.blobs.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  _root_.Ixon.putTagN 4 0xE envVersion
  _root_.Ixon.putBytes (Merkle.rootCanonical (constants.map Prod.fst)).hash
  _root_.Ixon.putU8 0
  _root_.Ixon.putTagN 0 0 env.assumptions.size.toUInt64
  for address in env.assumptions do _root_.Ixon.putBytes address.hash
  for table in #[blobs, constants] do
    _root_.Ixon.putTagN 0 0 table.size.toUInt64
    for (address, raw) in table do
      _root_.Ixon.putBytes address.hash
      _root_.Ixon.putTagN 0 0 raw.size.toUInt64
      _root_.Ixon.putBytes raw
  _root_.Ixon.putTagN 0 0 0

end IxCCTests.IxonV3.TypingFixtures
