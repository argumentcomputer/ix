import Ix.CompileCert.ReaderIndex
import IxVMRefinement.RoleVal.CommittedData

/-! # Kernel-decided pure prelude evaluation on `committedDefaultRoleTable`

Pure `List`/`Nat`/`Bool`/`Option` simulation of role bindings, recursor indexing,
and prelude shape verification on `committedPreludeList` and `committedDefaultRoleTable`,
isolated into its own module so the 6 `decide +kernel` checks compile once in seconds
and stay cached. -/

namespace IxVM.Refinement.RoleVal

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

theorem nth?_eq {α : Type} : ∀ (l : List α) (n : Nat), nth? l n = l[n]?
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => nth?_eq xs n

def committedPreAddrs : List _root_.Address :=
  committedPreludeList.map Prod.fst

def beqAddrFast (a b : _root_.Address) : Bool :=
  a.hash.data.toList == b.hash.data.toList

theorem beqAddrFast_eq (a b : _root_.Address) :
    beqAddrFast a b = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  rw [beqAddrFast, beq_iff_eq, beq_iff_eq]
  rcases a with ⟨⟨la⟩⟩
  rcases b with ⟨⟨lb⟩⟩
  simp

def containsAddrFast (l : List _root_.Address) (a : _root_.Address) : Bool :=
  l.any (beqAddrFast · a)

theorem containsAddrFast_eq (l : List _root_.Address) (a : _root_.Address) :
    containsAddrFast l a = l.contains a := by
  apply Bool.eq_iff_iff.mpr
  rw [containsAddrFast, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨x, hx, hbeq⟩
    rw [beqAddrFast_eq, beq_iff_eq] at hbeq
    rwa [← hbeq]
  · intro ha
    exact ⟨a, ha, by rw [beqAddrFast_eq]; exact beq_self_eq_true a⟩

def lookupAddrFast {β : Type} (a : _root_.Address) :
    List (_root_.Address × β) → Option β
  | [] => none
  | (k, v) :: rest => if beqAddrFast a k then some v else lookupAddrFast a rest

theorem lookupAddrFast_eq {β : Type} (a : _root_.Address)
    (l : List (_root_.Address × β)) :
    lookupAddrFast a l = l.lookup a := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rw [lookupAddrFast, List.lookup_cons, beqAddrFast_eq, ih]
    cases (a == k) <;> rfl

def preStorePure (a : _root_.Address) : Option Ixon.Constant :=
  lookupAddrFast a committedPreludeList

theorem preStorePure_eq (a : _root_.Address) :
    preStorePure a = committedPreludeList.lookup a :=
  lookupAddrFast_eq a committedPreludeList

def constRefBlock : ConstRef _root_.Address → _root_.Address
  | .member b _ => b
  | .ctor b _ _ => b

def constRefCode : ConstRef _root_.Address → Nat
  | .member b i => addrHead32 b * 256 + i * 2
  | .ctor b i j => addrHead32 b * 256 + (i * 16 + j) * 2 + 1

def cnameCode : CName .anon → Nat
  | .role r => r.idx + 1
  | _ => 0

theorem committedPreEvAddrs_nodup :
    (committedPreAddrs ++ committedEvAddrs).Nodup := by
  apply nodup_of_nodup_map addrHead32
  exact nodup_of_nodupNat (by decide +kernel)

theorem committedPreAddrs_nodup : committedPreAddrs.Nodup :=
  (List.nodup_append.mp committedPreEvAddrs_nodup).1

theorem preEvAddrs_disjoint {a : _root_.Address}
    (hp : a ∈ committedPreAddrs) (he : a ∈ committedEvAddrs) : False :=
  (List.nodup_append.mp committedPreEvAddrs_nodup).2.2 a hp a he rfl

def preRefsAndProjClosedBool : Bool :=
  committedPreludeList.all fun (_, c) =>
    c.refs.toList.all (containsAddrFast committedPreAddrs) &&
    match c.info with
    | .cPrj p => containsAddrFast committedPreAddrs p.block
    | .rPrj p => containsAddrFast committedPreAddrs p.block
    | .iPrj p => containsAddrFast committedPreAddrs p.block
    | .dPrj p => containsAddrFast committedPreAddrs p.block
    | _ => true

theorem preRefsAndProjClosed : preRefsAndProjClosedBool = true := by
  decide +kernel

def pureRolesList : List (ConstRef _root_.Address × CName .anon) :=
  committedDefaultRoleTable.bound.toList.filterMap fun (ro, a) =>
    if containsAddrFast committedPreAddrs a then
      (resolve preStorePure a).map fun ref => (ref, Ix.Kernel.roleKey ro)
    else none

def beqConstRefFast : ConstRef _root_.Address → ConstRef _root_.Address → Bool
  | .member b1 i1, .member b2 i2 => beqAddrFast b1 b2 && i1 == i2
  | .ctor b1 i1 c1, .ctor b2 i2 c2 => beqAddrFast b1 b2 && i1 == i2 && c1 == c2
  | _, _ => false

theorem beqConstRefFast_eq (x y : ConstRef _root_.Address) :
    beqConstRefFast x y = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq]
  cases x with
  | member b1 i1 =>
    cases y with
    | member b2 i2 =>
      rw [beqConstRefFast, Bool.and_eq_true, beqAddrFast_eq, beq_iff_eq, beq_iff_eq,
        ConstRef.member.injEq]
    | ctor b2 i2 c2 =>
      simp [beqConstRefFast]
  | ctor b1 i1 c1 =>
    cases y with
    | member b2 i2 =>
      simp [beqConstRefFast]
    | ctor b2 i2 c2 =>
      rw [beqConstRefFast, Bool.and_eq_true, Bool.and_eq_true, beqAddrFast_eq,
        beq_iff_eq, beq_iff_eq, beq_iff_eq, and_assoc, ConstRef.ctor.injEq]

def lookupConstRefFast {β : Type} (k : ConstRef _root_.Address) :
    List (ConstRef _root_.Address × β) → Option β
  | [] => none
  | (k', v) :: rest => if beqConstRefFast k k' then some v else lookupConstRefFast k rest

theorem lookupConstRefFast_eq {β : Type} (k : ConstRef _root_.Address)
    (l : List (ConstRef _root_.Address × β)) :
    lookupConstRefFast k l = l.lookup k := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    rw [lookupConstRefFast, List.lookup_cons, beqConstRefFast_eq, ih]
    cases (k == k') <;> rfl

def pureRolesLookup (ref : ConstRef _root_.Address) : Option (CName .anon) :=
  lookupConstRefFast ref pureRolesList

theorem pureRolesList_nodup : (pureRolesList.map Prod.fst).Nodup := by
  apply nodup_of_nodup_map constRefCode
  exact nodup_of_nodupNat (by decide +kernel)

theorem pureRolesList_block_mem :
    ∀ p ∈ pureRolesList, constRefBlock p.1 ∈ committedPreAddrs := by
  have hb : (pureRolesList.all fun p => containsAddrFast committedPreAddrs (constRefBlock p.1)) = true := by
    decide +kernel
  intro p hp
  have h1 := List.all_eq_true.mp hb p hp
  rw [containsAddrFast_eq, List.contains_iff_mem] at h1
  exact h1

def recursorMembersFast (c : Ixon.Constant) : List (Nat × Ixon.Recursor) :=
  match c.info with
  | .recr r => [(0, r)]
  | .muts ms => ms.toList.zipIdx.filterMap fun | (.recr r, j) => some (j, r) | _ => none
  | _ => []

def unshareGoFast (sh : List Ixon.Expr) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => e
  | n + 1, .share i =>
    match nth? sh i.toNat with
    | some e' => unshareGoFast sh n e'
    | none => .share i
  | _, e => e

def unshareFast (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr :=
  unshareGoFast c.sharing.toList (c.sharing.toList.length + 1) e

def stripAllFast (c : Ixon.Constant) : Nat → Ixon.Expr → Option (List Ixon.Expr × Ixon.Expr)
  | 0, e => some ([], e)
  | n + 1, e =>
    match unshareFast c e with
    | .all t b =>
      match stripAllFast c n b with
      | some (ts, r) => some (t :: ts, r)
      | none => none
    | _ => none

def stripAllFullChecked (c : Ixon.Constant) : Nat → Ixon.Expr → Option (List Ixon.Expr × Ixon.Expr)
  | 0, _ => none
  | n + 1, e =>
    match unshareFast c e with
    | .all t b =>
      match stripAllFullChecked c n b with
      | some (ts, r) => some (t :: ts, r)
      | none => none
    | e' => some ([], e')

def appHeadChecked (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, _ => none
  | n + 1, e =>
    match unshareFast c e with
    | .app f _ => appHeadChecked c n f
    | e' => some e'

def headRefChecked (store : Store) (owner : _root_.Address) (c : Ixon.Constant) (e : Ixon.Expr) :
    Option (ConstRef _root_.Address) := do
  let hd ← appHeadChecked c 64 e
  match hd with
  | .ref i _ => do resolve store (← nth? c.refs.toList i.toNat)
  | .recur i _ =>
    match c.info with
    | .muts ms => if i.toNat < ms.toList.length then some (.member owner i.toNat) else none
    | _ => if i == 0 then some (.member owner 0) else none
  | _ => none

def analyseRecursorChecked (store : Store) (owner : _root_.Address) (c : Ixon.Constant)
    (r : Ixon.Recursor) :
    Option (Nat × List (ConstRef _root_.Address) × ConstRef _root_.Address) := do
  let nP := r.params.toNat
  let nM := r.motives.toNat
  let nm := r.minors.toNat
  let nI := r.indices.toNat
  let depth := nP + nM + nm + nI + 1
  let (doms, body) ← stripAllFast c depth r.typ
  let .var k ← appHeadChecked c 64 body | none
  let pos := depth - 1 - k.toNat
  if !(k.toNat < depth && nP ≤ pos && pos < nP + nM) then none else
  let carriersL ← (doms.drop nP |>.take nM).mapM fun dom => do
    let (bs, _) ← stripAllFullChecked c 64 dom
    headRefChecked store owner c (← bs.getLast?)
  let major ← headRefChecked store owner c (← doms.getLast?)
  some (pos - nP, carriersL, major)

def inductivesList (members : List Ixon.MutConst) : List (Nat × Ixon.Inductive) :=
  members.zipIdx.filterMap fun | (.indc ind, index) => some (index, ind) | _ => none

def orderForList (carriers : List (ConstRef _root_.Address)) (owner : _root_.Address)
    (count : Nat) : List Nat :=
  (carriers.take count).filterMap fun
    | .member block index => if beqAddrFast block owner then some index else none
    | .ctor .. => none

def orderValidList (firstIndex : Nat) (indcsL : List (Nat × Ixon.Inductive))
    (orderL : List Nat) : Bool :=
  orderL.length == indcsL.length && nth? orderL 0 == some firstIndex &&
    orderL.all (fun index => indcsL.any (·.1 == index)) &&
    orderL.eraseDups.length == indcsL.length

structure PureIdx where
  recs : List (ConstRef _root_.Address × RecEntry) := []
  blocks : List (_root_.Address × List Nat) := []
  found : List (_root_.Address × List (Nat × ConstRef _root_.Address)) := []

def pureCandStep (owner : _root_.Address) (c : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (s : PureIdx) : Option PureIdx := do
  let (pos, rec) := member
  let ref : ConstRef _root_.Address := .member owner pos
  if !(lookupConstRefFast ref s.recs).isNone then none else
  if !(c.refs.toList.all (containsAddrFast committedPreAddrs)) then none else
  let (motive, carriersL, major) ← analyseRecursorChecked preStorePure owner c rec
  let ConstRef.member block firstIdx ← nth? carriersL 0 | none
  if !(containsAddrFast committedPreAddrs block) then none else
  let blockRec ← preStorePure block
  let .muts members := blockRec.info | none
  let indcsL := inductivesList members.toList
  let (_, first) ← nth? indcsL 0
  let orderL := orderForList carriersL block indcsL.length
  if !(orderValidList firstIdx indcsL orderL) then none else
  if !(lookupAddrFast block s.found).isNone then none else
  if !(lookupAddrFast block s.blocks).isNone then none else
  let large := rec.lvls.toNat == first.lvls.toNat + 1
  let entry : RecEntry := ⟨block, motive, major, large⟩
  some {
    recs := (ref, entry) :: s.recs
    blocks := (block, orderL) :: s.blocks
    found := (block, [(motive, ref)]) :: s.found
  }

def pureRecordIdxStep (rec : _root_.Address × Ixon.Constant) (s : PureIdx) :
    Option PureIdx :=
  match recursorMembersFast rec.2 with
  | [] => some s
  | [m] => pureCandStep rec.1 rec.2 m s
  | _ => none

def pureIndexRecords : List (_root_.Address × Ixon.Constant) → PureIdx → Option PureIdx
  | [], s => some s
  | r :: rs, s => do
    let s' ← pureRecordIdxStep r s
    pureIndexRecords rs s'

def purePreIdx? : Option PureIdx :=
  pureIndexRecords committedPreludeList (PureIdx.mk [] [] [])

def pureRecsLookup (ref : ConstRef _root_.Address) : Option RecEntry := do
  let s ← purePreIdx?
  lookupConstRefFast ref s.recs

def pureBlocksLookup (b : _root_.Address) :
    Option (List Nat × List (ConstRef _root_.Address)) := do
  let s ← purePreIdx?
  let orderL ← lookupAddrFast b s.blocks
  let foundL ← lookupAddrFast b s.found
  some (orderL, foundL.map (·.2))

def preInputIndexedBool : Bool :=
  committedPreludeList.all fun (a, c) =>
    (recursorMembersFast c).all fun (_, r) =>
      match analyseRecursorChecked preStorePure a c r with
      | some (_, carriersL, _) =>
        match carriersL with
        | ConstRef.member b _ :: _ => containsAddrFast committedPreAddrs b
        | _ => false
      | none => false

theorem preInputIndexed_true : preInputIndexedBool = true := by
  decide +kernel

def purePreIdxFoundSingletonsBool : Bool :=
  match purePreIdx? with
  | some s => s.found.all fun (_, l) => l.length == 1
  | none => false

theorem purePreIdx_found_singletons : purePreIdxFoundSingletonsBool = true := by
  decide +kernel

/-! ### Shape-only expression and prelude stream simulation -/

structure ExprShape where
  piLen : Nat
  piSort? : Option Ix.Kernel.Level

def pureKeyAtOpt (a : _root_.Address) : Option (CName .anon) :=
  if containsAddrFast committedPreAddrs a then
    match resolve preStorePure a with
    | some r => pureRolesLookup r
    | none => none
  else none

def pureMemberKeyOpt (r : ConstRef _root_.Address) : Option (CName .anon) :=
  pureRolesLookup r

structure PureShapeECx where
  refs : List _root_.Address
  univs : List CLevel
  selfOk : Nat → Bool

def pureLevelsOk (univsLen : Nat) : List UInt64 → Bool
  | [] => true
  | u :: us => u.toNat < univsLen && pureLevelsOk univsLen us

def pureConvExprShape (pe : PureShapeECx) (tbl : List (Option ExprShape)) :
    Ixon.Expr → Option ExprShape
  | .var _ => some ⟨0, none⟩
  | .sort i =>
    match nth? pe.univs i.toNat with
    | some u => some ⟨0, some u⟩
    | none => none
  | .ref i us =>
    match nth? pe.refs i.toNat with
    | some a =>
      match pureKeyAtOpt a with
      | some _ => if pureLevelsOk pe.univs.length us.toList then some ⟨0, none⟩ else none
      | none => none
    | none => none
  | .recur i us =>
    if pe.selfOk i.toNat && pureLevelsOk pe.univs.length us.toList then
      some ⟨0, none⟩
    else none
  | .prj i _ v =>
    match nth? pe.refs i.toNat with
    | some a =>
      match pureKeyAtOpt a, pureConvExprShape pe tbl v with
      | some _, some _ => some ⟨0, none⟩
      | _, _ => none
    | none => none
  | .str _ => none
  | .nat _ => none
  | .app f a =>
    match pureConvExprShape pe tbl f, pureConvExprShape pe tbl a with
    | some _, some _ => some ⟨0, none⟩
    | _, _ => none
  | .lam t b =>
    match pureConvExprShape pe tbl t, pureConvExprShape pe tbl b with
    | some _, some _ => some ⟨0, none⟩
    | _, _ => none
  | .all t b =>
    match pureConvExprShape pe tbl t, pureConvExprShape pe tbl b with
    | some _, some sb => some ⟨sb.piLen + 1, sb.piSort?⟩
    | _, _ => none
  | .letE _ _ t v b =>
    match pureConvExprShape pe tbl t, pureConvExprShape pe tbl v, pureConvExprShape pe tbl b with
    | some _, some _, some _ => some ⟨0, none⟩
    | _, _, _ => none
  | .share i =>
    match nth? tbl i.toNat with
    | some r => r
    | none => none

def pureBuildShapeTbl (pe : PureShapeECx) :
    List Ixon.Expr → List (Option ExprShape) → List (Option ExprShape)
  | [], tbl => tbl
  | e :: es, tbl => pureBuildShapeTbl pe es (tbl ++ [pureConvExprShape pe tbl e])

def pureReadExprShape (src : Ixon.Constant) (param : Nat → Ix.Kernel.LevelParam)
    (selfOk : Nat → Bool) (e : Ixon.Expr) : Option ExprShape :=
  let pe : PureShapeECx := ⟨src.refs.toList, src.univs.toList.map (convUniv param), selfOk⟩
  let tbl := pureBuildShapeTbl pe src.sharing.toList []
  pureConvExprShape pe tbl e

def pureReadRecRulesOk (src : Ixon.Constant) (param : Nat → Ix.Kernel.LevelParam)
    (selfOk : Nat → Bool) (mb : _root_.Address) (mi : Nat) :
    List (Ixon.RecursorRule × Nat) → Bool
  | [] => true
  | (rule, k) :: rest =>
    (pureMemberKeyOpt (.ctor mb mi k)).isSome &&
    (pureReadExprShape src param selfOk rule.rhs).isSome &&
    pureReadRecRulesOk src param selfOk mb mi rest

def pureReadRecursorKeyCounts (blockLps : List Ix.Kernel.LevelParam)
    (ref : ConstRef _root_.Address) (entry : RecEntry) : Option (CName .anon × RecCounts) := do
  let .member rOwner j := ref | none
  if !containsAddrFast committedPreAddrs rOwner then none else
  let rc ← preStorePure rOwner
  let (_, r) ← (recursorMembersFast rc).find? (·.1 == j)
  if r.isUnsafe then none else
  let key ← pureMemberKeyOpt ref
  let selfOk : Nat → Bool := fun i => match rc.info with
    | .muts rms => i < rms.toList.length && (pureMemberKeyOpt (.member rOwner i)).isSome
    | _ => i == 0
  let lps := recLps entry.large blockLps
  let _ ← pureReadExprShape rc (recParam lps) selfOk r.typ
  let .member mb mi := entry.major | none
  if !containsAddrFast committedPreAddrs mb then none else
  let major ← inductiveAt preStorePure entry.major
  if !(major.ctors.toList.length == r.rules.toList.length) then none else
  if !pureReadRecRulesOk rc (recParam lps) selfOk mb mi r.rules.toList.zipIdx then none else
  some (key, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k,
    some entry.motive⟩)

def pureReadCtorShapes (owner : _root_.Address) (src : Ixon.Constant)
    (selfOk : Nat → Bool) (nPd : Nat) :
    List (Ixon.Constructor × Nat) → Option (List (CName .anon × Nat))
  | [] => some []
  | (ctor, j) :: rest => do
    if !(ctor.cidx.toNat == j) then none else
    if ctor.isUnsafe then none else
    let ck ← pureMemberKeyOpt (.ctor owner 0 j)
    let csh ← pureReadExprShape src id selfOk ctor.typ
    if !(nPd + ctor.fields.toNat == csh.piLen) then none else
    let tail ← pureReadCtorShapes owner src selfOk nPd rest
    some ((ck, ctor.fields.toNat) :: tail)

def levelIsZeroFast : Ix.Kernel.Level → Option Bool
  | .zero => some true
  | .param _ => some false
  | .succ _ => some false
  | _ => none

def kCheckSingleShape (tsh : ExprShape) (pairs : List (CName .anon × Nat)) (rk : Bool) : Bool :=
  match pairs with
  | [(_, nF)] =>
    match tsh.piSort? with
    | some s =>
      if nF == 0 then
        match levelIsZeroFast s with
        | some b => rk == b
        | none => false
      else rk == false
    | none => true
  | _ => rk == false

def checkSingleRecShape (nPd : Nat) (tsh : ExprShape) (pairs : List (CName .anon × Nat))
    (rc : RecCounts) : Bool :=
  rc.params == nPd &&
  rc.motives == 1 &&
  rc.minors == pairs.length &&
  kCheckSingleShape tsh pairs rc.k &&
  match rc.motive with
  | some 0 =>
    match tsh.piSort? with
    | some _ => nPd + rc.indices == tsh.piLen
    | none => true
  | _ => true

def pureReadInductive1Names (owner : _root_.Address) (c : Ixon.Constant)
    (ind : Ixon.Inductive) : Option (List (CName .anon)) := do
  let (orderL, recsL) ← pureBlocksLookup owner
  if !(orderL == [0]) then none else
  let [recRef] := recsL | none
  let entry ← pureRecsLookup recRef
  if ind.isUnsafe then none else
  let nPd := ind.params.toNat
  let blockLps := List.range ind.lvls.toNat
  let tk ← pureMemberKeyOpt (.member owner 0)
  let selfOk : Nat → Bool := fun i => i == 0
  let tsh ← pureReadExprShape c id selfOk ind.typ
  let pairs ← pureReadCtorShapes owner c selfOk nPd ind.ctors.toList.zipIdx
  let (rkey, rc) ← pureReadRecursorKeyCounts blockLps recRef entry
  if !checkSingleRecShape nPd tsh pairs rc then none else
  let declNames := (tk :: pairs.map Prod.fst) ++ [rkey]
  if !nodupNat (declNames.map cnameCode) then none else
  some declNames

def pureReadRecordNames (owner : _root_.Address) (c : Ixon.Constant) :
    Option (List (List (CName .anon))) :=
  match c.info with
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ =>
    if (resolveSource preStorePure owner c).isNone then none else some []
  | .recr _ =>
    if (pureRecsLookup (.member owner 0)).isSome then some [] else none
  | .axio a =>
    if a.isUnsafe then none else do
      let ck ← pureMemberKeyOpt (.member owner 0)
      let _ ← pureReadExprShape c id (fun _ => false) a.typ
      some [[ck]]
  | .quot q => do
    let ck ← pureMemberKeyOpt (.member owner 0)
    let _ ← pureReadExprShape c id (fun _ => false) q.typ
    some [[ck]]
  | .muts ms =>
    match ms.toList with
    | [.indc ind] => do
      let names ← pureReadInductive1Names owner c ind
      some [names]
    | _ => none
  | .defn _ => none

def pureReadStreamNames :
    List (_root_.Address × Ixon.Constant) → Option (List (List (CName .anon)))
  | [] => some []
  | (a, c) :: rest => do
    let g ← pureReadRecordNames a c
    let gs ← pureReadStreamNames rest
    some (g ++ gs)

def fallbackRecursorShapeFast (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms => ms.toList.all fun | .recr _ => false | _ => true
  | _ => true

def eqRoleGroup : List (CName .anon) → List Ix.Kernel.Role → Bool
  | [], [] => true
  | .role r1 :: ks, r2 :: rs => r1.idx == r2.idx && eqRoleGroup ks rs
  | _, _ => false

def eqRoleGroups : List (List (CName .anon)) → List (List Ix.Kernel.Role) → Bool
  | [], [] => true
  | g1 :: gs1, g2 :: gs2 => eqRoleGroup g1 g2 && eqRoleGroups gs1 gs2
  | _, _ => false

def purePreludeCheckBool : Bool :=
  match pureReadStreamNames committedPreludeList with
  | some groups =>
    eqRoleGroups groups Ix.Kernel.preludeShape &&
    committedPreludeList.all (fun p => fallbackRecursorShapeFast p.2)
  | none => false

theorem purePreludeCheck_ok : purePreludeCheckBool = true := by
  decide +kernel

end IxVM.Refinement.RoleVal
