import Ix.Compiler.Ixon.Eval
import Ix.Compiler.Ixon.Sharing

/-!
# Sharing/evaluator coherence

Full inlining extends from expressions and constants to evaluator frames,
resolution contexts, heads, and recursive values. Under decoder-level sharing
well-formedness, a single mutual fuel induction proves that every successful
run of `eval`, `evalRef`, `apply`, `applyMany`, `saturate`, or `fire` remains
successful after inlining and returns the correspondingly inlined value.
Closed-expression and definition-constant corollaries expose the result at the
public evaluator entry points.
-/

namespace Ix.Compiler.Ixon.Eval

def Frame.inlineSharing (F : Frame) : Frame :=
  { sharing := #[]
    refs := F.refs
    univs := F.univs
    selfMuts := F.selfMuts.map
      (MutConst.mapExprs (Sharing.inlineExpr F.sharing))
    uinst := F.uinst
    selfAddr := F.selfAddr }

def EvalCtx.inlineSharing (ctx : EvalCtx) : EvalCtx :=
  { resolve := fun address => (ctx.resolve address).map Constant.inlineSharing
    blobs := ctx.blobs
    preserveNeutralElims := ctx.preserveNeutralElims
    natBlock := ctx.natBlock
    stringLiteral := ctx.stringLiteral
    quotientKind := ctx.quotientKind
    externArity := ctx.externArity
    oracle := ctx.oracle }

@[simp] theorem Frame.inlineSharing_refs (F : Frame) :
    F.inlineSharing.refs = F.refs := by rfl

@[simp] theorem Frame.ofConst_sharing (c : Constant) (uinst : List Nat)
    (selfAddr : Option Address) :
    (Frame.ofConst c uinst selfAddr).sharing = c.sharing := by rfl

@[simp] theorem Frame.inlineSharing_univs (F : Frame) :
    F.inlineSharing.univs = F.univs := by rfl

@[simp] theorem Frame.inlineSharing_uinst (F : Frame) :
    F.inlineSharing.uinst = F.uinst := by rfl

@[simp] theorem Frame.inlineSharing_selfAddr (F : Frame) :
    F.inlineSharing.selfAddr = F.selfAddr := by rfl

@[simp] theorem EvalCtx.inlineSharing_blobs (ctx : EvalCtx) :
    ctx.inlineSharing.blobs = ctx.blobs := by rfl

@[simp] theorem EvalCtx.inlineSharing_preserveNeutralElims (ctx : EvalCtx) :
    ctx.inlineSharing.preserveNeutralElims = ctx.preserveNeutralElims := by rfl

@[simp] theorem EvalCtx.inlineSharing_resolve (ctx : EvalCtx)
    (address : Address) :
    ctx.inlineSharing.resolve address =
      (ctx.resolve address).map Constant.inlineSharing := by rfl

@[simp] theorem EvalCtx.inlineSharing_natBlock (ctx : EvalCtx) :
    ctx.inlineSharing.natBlock = ctx.natBlock := by rfl

@[simp] theorem EvalCtx.inlineSharing_stringLiteral (ctx : EvalCtx) :
    ctx.inlineSharing.stringLiteral = ctx.stringLiteral := by rfl

theorem EvalCtx.Strict.inlineSharing {ctx : EvalCtx} (h : ctx.Strict) :
    ctx.inlineSharing.Strict :=
  ⟨by simpa using h.neutralElims, by simpa using h.stringLiterals⟩

@[simp] theorem EvalCtx.inlineSharing_quotientKind (ctx : EvalCtx) :
    ctx.inlineSharing.quotientKind = ctx.quotientKind := by rfl

@[simp] theorem EvalCtx.inlineSharing_externArity (ctx : EvalCtx) :
    ctx.inlineSharing.externArity = ctx.externArity := by rfl

@[simp] theorem EvalCtx.inlineSharing_oracle (ctx : EvalCtx) :
    ctx.inlineSharing.oracle = ctx.oracle := by rfl

def Head.inlineSharing : Head → Head
  | .ctorH block indIdx cidx arity => .ctorH block indIdx cidx arity
  | .neuH id => .neuH id
  | .extH address arity => .extH address arity
  | .quotH address kind => .quotH address kind
  | .recH block r F =>
    .recH block (r.mapExprs (Sharing.inlineExpr F.sharing)) F.inlineSharing

mutual
  def Value.inlineSharing : Value → Value
    | .sortV lvl => .sortV lvl
    | .piV uses owned F env dom cod =>
      .piV uses owned F.inlineSharing (valuesInlineSharing env)
        (Sharing.inlineExpr F.sharing dom)
        (Sharing.inlineExpr F.sharing cod)
    | .closV uses F env dom body =>
      .closV uses F.inlineSharing (valuesInlineSharing env)
        (Sharing.inlineExpr F.sharing dom)
        (Sharing.inlineExpr F.sharing body)
    | .papV head args =>
      .papV head.inlineSharing (valuesInlineSharing args)
    | .quotV address representative =>
      .quotV address representative.inlineSharing
    | .ctorV block indIdx cidx args =>
      .ctorV block indIdx cidx (valuesInlineSharing args)
    | .litV lit => .litV lit
  termination_by value => sizeOf value

  def valuesInlineSharing : List Value → List Value
    | [] => []
    | value :: values => value.inlineSharing :: valuesInlineSharing values
  termination_by values => sizeOf values

end

theorem Frame.inlineSharing_ofConst (c : Constant) (uinst : List Nat)
    (selfAddr : Option Address) :
    (Frame.ofConst c uinst selfAddr).inlineSharing =
      Frame.ofConst c.inlineSharing uinst selfAddr := by
  cases c with
  | mk info sharing refs univs =>
    cases info <;> simp [Frame.ofConst, Frame.inlineSharing,
      Constant.inlineSharing, ConstantInfo.mapExprs,
      MutConst.mapExprs, ConstantIdentityLaws.mapMutConst,
      ConstantIdentityLaws.mapInfo, selfMutsOf]

theorem Frame.inlineSharing_set_uinst (F : Frame) (uinst : List Nat) :
    ({ F with uinst := uinst }).inlineSharing =
      { F.inlineSharing with uinst := uinst } := by rfl

theorem evalUnivArgs_inlineSharing (F : Frame) (idxs : Array UInt64) :
    evalUnivArgs F.inlineSharing idxs = evalUnivArgs F idxs := by
  rfl

theorem majorCtor_inlineSharing (peel : Bool) (value : Value) :
    majorCtor peel value.inlineSharing =
      (majorCtor peel value).map fun result =>
        (result.1, valuesInlineSharing result.2) := by
  cases value <;> simp [Value.inlineSharing, majorCtor, Except.map]
  case litV lit =>
    cases lit <;> simp
    case natL n =>
      cases peel <;> cases n <;>
        simp [Value.inlineSharing, valuesInlineSharing]

@[simp] theorem guardRecMajor_inlineSharing (block : Option Address)
    (params : Nat) (value : Value) :
    guardRecMajor block params value.inlineSharing =
      guardRecMajor block params value := by
  cases value <;> simp [Value.inlineSharing, guardRecMajor]

def rootsBelow (table : Array Expr) (roots : List Expr) : Prop :=
  ∀ e ∈ roots, Sharing.sharesBelow table.size e = true

structure Frame.SharingWF (F : Frame) : Prop where
  tableOk : Sharing.tableWF F.sharing = true
  selfMutsOk : ∀ (i : Nat) (member : MutConst),
    F.selfMuts[i]? = some member →
    rootsBelow F.sharing member.exprs

inductive Head.SharingWF : Head → Prop where
  | ctorH (block : Address) (indIdx cidx arity : Nat) :
      SharingWF (.ctorH block indIdx cidx arity)
  | neuH (id : NeutralId) : SharingWF (.neuH id)
  | extH (address : Address) (arity : Nat) :
      SharingWF (.extH address arity)
  | quotH (address : Address) (kind : QuotKind) :
      SharingWF (.quotH address kind)
  | recH (block : Option Address) (r : Recursor) (F : Frame)
      (hframe : Frame.SharingWF F)
      (hrecr : rootsBelow F.sharing r.exprs) :
      SharingWF (.recH block r F)

mutual
inductive Value.SharingWF : Value → Prop where
  | sortV (lvl : Nat) : Value.SharingWF (.sortV lvl)
  | piV (uses : Uses) (owned : Owned) (F : Frame) (env : List Value)
      (dom cod : Expr) (hframe : Frame.SharingWF F)
      (henv : ValuesSharingWF env)
      (hdom : Sharing.sharesBelow F.sharing.size dom = true)
      (hcod : Sharing.sharesBelow F.sharing.size cod = true) :
      Value.SharingWF (.piV uses owned F env dom cod)
  | closV (uses : Uses) (F : Frame) (env : List Value) (dom body : Expr)
      (hframe : Frame.SharingWF F) (henv : ValuesSharingWF env)
      (hdom : Sharing.sharesBelow F.sharing.size dom = true)
      (hbody : Sharing.sharesBelow F.sharing.size body = true) :
      Value.SharingWF (.closV uses F env dom body)
  | papV (h : Head) (args : List Value) (hhead : Head.SharingWF h)
      (hargs : ValuesSharingWF args) :
      Value.SharingWF (.papV h args)
  | quotV (address : Address) (representative : Value)
      (hrepresentative : Value.SharingWF representative) :
      Value.SharingWF (.quotV address representative)
  | ctorV (block : Address) (indIdx cidx : Nat) (args : List Value)
      (hargs : ValuesSharingWF args) :
      Value.SharingWF (.ctorV block indIdx cidx args)
  | litV (lit : Lit) : Value.SharingWF (.litV lit)

inductive ValuesSharingWF : List Value → Prop where
  | nil : ValuesSharingWF []
  | cons (head : Value) (tail : List Value)
      (hhead : Value.SharingWF head) (htail : ValuesSharingWF tail) :
      ValuesSharingWF (head :: tail)
end

structure EvalCtx.SharingWF (ctx : EvalCtx) : Prop where
  resolveOk : ∀ address c, ctx.resolve address = some c →
    c.sharingWF = true
  oracleOk : ∀ address args value,
    ValuesSharingWF args →
    ctx.oracle address args = some value →
    ctx.oracle address (valuesInlineSharing args) =
        some value.inlineSharing ∧
      value.SharingWF

theorem valuesInlineSharing_eq_map (values : List Value) :
    valuesInlineSharing values = values.map Value.inlineSharing := by
  induction values with
  | nil => simp [valuesInlineSharing]
  | cons value values ih => simp [valuesInlineSharing, ih]

@[simp] theorem valuesInlineSharing_append (left right : List Value) :
    valuesInlineSharing (left ++ right) =
      valuesInlineSharing left ++ valuesInlineSharing right := by
  simp [valuesInlineSharing_eq_map]

@[simp] theorem valuesInlineSharing_length (values : List Value) :
    (valuesInlineSharing values).length = values.length := by
  simp [valuesInlineSharing_eq_map]

theorem valuesInlineSharing_getElem? (values : List Value) (i : Nat) :
    (valuesInlineSharing values)[i]? =
      (values[i]?).map Value.inlineSharing := by
  simp [valuesInlineSharing_eq_map, List.getElem?_map]

theorem valuesInlineSharing_getLast? (values : List Value) :
    (valuesInlineSharing values).getLast? =
      values.getLast?.map Value.inlineSharing := by
  simp [valuesInlineSharing_eq_map, List.getLast?_map]

@[simp] theorem valuesInlineSharing_take (n : Nat) (values : List Value) :
    valuesInlineSharing (values.take n) =
      (valuesInlineSharing values).take n := by
  simp [valuesInlineSharing_eq_map, List.map_take]

@[simp] theorem valuesInlineSharing_drop (n : Nat) (values : List Value) :
    valuesInlineSharing (values.drop n) =
      (valuesInlineSharing values).drop n := by
  simp [valuesInlineSharing_eq_map, List.map_drop]

theorem ValuesSharingWF.mem {values : List Value}
    (hvalues : ValuesSharingWF values) {value : Value}
    (hmem : value ∈ values) : value.SharingWF := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
    cases hvalues with
    | cons _ _ hhead htail =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hhead
    · exact ih htail hmem

theorem ValuesSharingWF.getElem?_eq {values : List Value}
    (hvalues : ValuesSharingWF values) {i : Nat} {value : Value}
    (hget : values[i]? = some value) : value.SharingWF := by
  apply hvalues.mem
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hi, heq⟩
  exact List.mem_iff_getElem.mpr ⟨i, hi, heq⟩

theorem ValuesSharingWF.getLast?_eq {values : List Value}
    (hvalues : ValuesSharingWF values) {value : Value}
    (hget : values.getLast? = some value) : value.SharingWF := by
  apply hvalues.mem
  rcases List.getLast?_eq_some_iff.mp hget with ⟨pre, rfl⟩
  simp

theorem ValuesSharingWF.append {left right : List Value}
    (hleft : ValuesSharingWF left) (hright : ValuesSharingWF right) :
    ValuesSharingWF (left ++ right) := by
  induction left with
  | nil => simpa using hright
  | cons head tail ih =>
    cases hleft with
    | cons _ _ hhead htail =>
      exact .cons head (tail ++ right) hhead (ih htail)

theorem ValuesSharingWF.take {values : List Value}
    (hvalues : ValuesSharingWF values) (n : Nat) :
    ValuesSharingWF (values.take n) := by
  induction n generalizing values with
  | zero => exact .nil
  | succ n ih =>
    cases values with
    | nil => exact .nil
    | cons head tail =>
      cases hvalues with
      | cons _ _ hhead htail =>
        exact .cons head (tail.take n) hhead (ih htail)

theorem ValuesSharingWF.drop {values : List Value}
    (hvalues : ValuesSharingWF values) (n : Nat) :
    ValuesSharingWF (values.drop n) := by
  induction n generalizing values with
  | zero => simpa using hvalues
  | succ n ih =>
    cases values with
    | nil => exact .nil
    | cons head tail =>
      cases hvalues with
      | cons _ _ hhead htail => exact ih htail

theorem arrayAll_of_mem {α : Type} {values : Array α} {p : α → Bool}
    (hall : values.all p = true) {value : α} (hmem : value ∈ values) :
    p value = true := by
  have hall' := (Array.all_eq_true.mp hall)
  rcases List.mem_iff_getElem.mp (Array.mem_def.mp hmem) with
    ⟨i, hi, heq⟩
  have hi' : i < values.size := by simpa using hi
  have hvalue : values[i] = value := by simpa using heq
  rw [← hvalue]
  exact hall' i hi'

theorem constantTableWF_of_sharingWF (c : Constant)
    (h : c.sharingWF = true) : Sharing.tableWF c.sharing = true := by
  exact ((Sharing.layer1WF_iff c.sharing c.info.exprs.toArray).mp h).tableOk

theorem constantRootsBelow_of_sharingWF (c : Constant)
    (h : c.sharingWF = true) : rootsBelow c.sharing c.info.exprs := by
  intro e he
  have hlayer :=
    (Sharing.layer1WF_iff c.sharing c.info.exprs.toArray).mp h
  apply arrayAll_of_mem hlayer.bodiesOk
  simpa using he

theorem Frame.sharingWF_ofConst (c : Constant) (uinst : List Nat)
    (selfAddr : Option Address) (h : c.sharingWF = true) :
    (Frame.ofConst c uinst selfAddr).SharingWF := by
  constructor
  · exact constantTableWF_of_sharingWF c h
  · intro i member hget
    have hroots := constantRootsBelow_of_sharingWF c h
    cases hi : c.info with
    | muts members =>
      have hget' : members[i]? = some member := by
        simpa [Frame.ofConst, selfMutsOf, hi] using hget
      have hmem : member ∈ members.toList := by
        rcases Array.getElem?_eq_some_iff.mp hget' with ⟨hib, heq⟩
        exact Array.mem_def.mp (by
          apply Array.mem_iff_getElem.mpr
          exact ⟨i, hib, heq⟩)
      intro e he
      apply hroots e
      rw [hi]
      simp only [ConstantInfo.exprs, List.mem_flatMap]
      exact ⟨member, hmem, he⟩
    | defn d =>
      cases i with
      | zero =>
        have hmember : member = .defn d := by
          simpa [Frame.ofConst, selfMutsOf, hi] using hget.symm
        subst member
        intro e he
        apply hroots e
        rw [hi]
        simpa [ConstantInfo.exprs, MutConst.exprs] using he
      | succ i => simp [Frame.ofConst, selfMutsOf, hi] at hget
    | recr r =>
      cases i with
      | zero =>
        have hmember : member = .recr r := by
          simpa [Frame.ofConst, selfMutsOf, hi] using hget.symm
        subst member
        intro e he
        apply hroots e
        rw [hi]
        simpa [ConstantInfo.exprs, MutConst.exprs] using he
      | succ i => simp [Frame.ofConst, selfMutsOf, hi] at hget
    | axio | quot | cPrj | rPrj | iPrj | dPrj =>
      simp [Frame.ofConst, selfMutsOf, hi] at hget

theorem Frame.SharingWF.with_uinst {F : Frame} (hF : F.SharingWF)
    (uinst : List Nat) : ({ F with uinst := uinst }).SharingWF := by
  cases hF
  constructor <;> assumption

theorem selfMutsOf_mapExprs (info : ConstantInfo) (f : Expr → Expr) :
    selfMutsOf (info.mapExprs f) =
      (selfMutsOf info).map (MutConst.mapExprs f) := by
  cases info <;> simp [ConstantInfo.mapExprs, MutConst.mapExprs,
    ConstantIdentityLaws.mapMutConst, ConstantIdentityLaws.mapInfo,
    selfMutsOf]

theorem resolveMut_inlineSharing_of_eq {ctx : EvalCtx} {block : Address}
    {idx : Nat} {c : Constant} {member : MutConst}
    (hresolve : resolveMut ctx block idx = .ok (c, member)) :
    resolveMut ctx.inlineSharing block idx =
      .ok (c.inlineSharing,
        member.mapExprs (Sharing.inlineExpr c.sharing)) := by
  unfold resolveMut at hresolve ⊢
  cases hc : ctx.resolve block with
  | none =>
    rw [hc] at hresolve
    contradiction
  | some found =>
    rw [hc] at hresolve
    simp only at hresolve
    cases hm : (selfMutsOf found.info)[idx]? with
    | none =>
      rw [hm] at hresolve
      contradiction
    | some foundMember =>
      rw [hm] at hresolve
      cases hresolve
      simp [Constant.inlineSharing, selfMutsOf_mapExprs,
        EvalCtx.inlineSharing, hc, Array.getElem?_map, hm]

theorem resolveMut_components_of_eq {ctx : EvalCtx} {block : Address}
    {idx : Nat} {c : Constant} {member : MutConst}
    (hresolve : resolveMut ctx block idx = .ok (c, member)) :
    ctx.resolve block = some c ∧
      (selfMutsOf c.info)[idx]? = some member := by
  unfold resolveMut at hresolve
  cases hc : ctx.resolve block with
  | none => rw [hc] at hresolve; contradiction
  | some found =>
    rw [hc] at hresolve
    simp only at hresolve
    cases hm : (selfMutsOf found.info)[idx]? with
    | none => rw [hm] at hresolve; contradiction
    | some foundMember =>
      rw [hm] at hresolve
      cases hresolve
      exact ⟨rfl, hm⟩

theorem constantMemberRoots_of_getElem (c : Constant) (i : Nat)
    (member : MutConst) (hsharing : c.sharingWF = true)
    (hget : (selfMutsOf c.info)[i]? = some member) :
    rootsBelow c.sharing member.exprs := by
  have hroots := constantRootsBelow_of_sharingWF c hsharing
  cases hi : c.info with
  | muts members =>
    have hget' : members[i]? = some member := by
      simpa [selfMutsOf, hi] using hget
    have hmem : member ∈ members.toList := by
      rcases Array.getElem?_eq_some_iff.mp hget' with ⟨hib, heq⟩
      exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨i, hib, heq⟩)
    intro e he
    apply hroots e
    rw [hi]
    simp only [ConstantInfo.exprs, List.mem_flatMap]
    exact ⟨member, hmem, he⟩
  | defn d =>
    cases i with
    | zero =>
      have hmember : member = .defn d := by
        simpa [selfMutsOf, hi] using hget.symm
      subst member
      intro e he
      apply hroots e
      rw [hi]
      simpa [ConstantInfo.exprs, MutConst.exprs] using he
    | succ i => simp [selfMutsOf, hi] at hget
  | recr r =>
    cases i with
    | zero =>
      have hmember : member = .recr r := by
        simpa [selfMutsOf, hi] using hget.symm
      subst member
      intro e he
      apply hroots e
      rw [hi]
      simpa [ConstantInfo.exprs, MutConst.exprs] using he
    | succ i => simp [selfMutsOf, hi] at hget
  | axio | quot | cPrj | rPrj | iPrj | dPrj =>
    simp [selfMutsOf, hi] at hget

theorem resolveMut_sharingWF_of_eq {ctx : EvalCtx} (hctx : ctx.SharingWF)
    {block : Address} {idx : Nat} {c : Constant} {member : MutConst}
    (hresolve : resolveMut ctx block idx = .ok (c, member)) :
    c.sharingWF = true ∧ rootsBelow c.sharing member.exprs := by
  have hcomponents := resolveMut_components_of_eq hresolve
  have hc := hctx.resolveOk block c hcomponents.1
  exact ⟨hc, constantMemberRoots_of_getElem c idx member hc hcomponents.2⟩

theorem Frame.inlineSharing_selfMuts_getElem? {F : Frame} {i : Nat}
    {member : MutConst} (hget : F.selfMuts[i]? = some member) :
    F.inlineSharing.selfMuts[i]? =
      some (member.mapExprs (Sharing.inlineExpr F.sharing)) := by
  simp [Frame.inlineSharing, Array.getElem?_map, hget]

@[simp] theorem Head.arity?_inlineSharing (h : Head) :
    h.inlineSharing.arity? = h.arity? := by
  cases h <;> rfl

@[simp] theorem Value.isNeutral_inlineSharing (value : Value) :
    value.inlineSharing.isNeutral = value.isNeutral := by
  cases value with
  | papV head args =>
    cases head <;> simp [Value.inlineSharing, Head.inlineSharing,
      Value.isNeutral, recArity, Recursor.mapExprs,
      ConstantIdentityLaws.mapRecursor] <;> rfl
  | sortV | piV | closV | quotV | ctorV | litV =>
    simp [Value.inlineSharing, Value.isNeutral]

theorem projectValue_inlineSharing {ctx : EvalCtx} {F : Frame}
    {typeRefIdx fieldIdx : UInt64} {value result : Value}
    (hctx : ctx.SharingWF) (hvalue : value.SharingWF)
    (hproject : projectValue ctx F typeRefIdx fieldIdx value = .ok result) :
    projectValue ctx.inlineSharing F.inlineSharing typeRefIdx fieldIdx
        value.inlineSharing = .ok result.inlineSharing ∧
      result.SharingWF := by
  unfold projectValue resolveProjectionTarget at hproject ⊢
  cases href : F.refs[typeRefIdx.toNat]? with
  | none =>
    rw [href] at hproject
    dsimp only at hproject
    contradiction
  | some typeAddress =>
    have href' : F.inlineSharing.refs[typeRefIdx.toNat]? =
        some typeAddress := by simpa using href
    rw [href] at hproject
    rw [href']
    dsimp only at hproject ⊢
    cases htype : ctx.resolve typeAddress with
    | none =>
      rw [htype] at hproject
      contradiction
    | some typeConstant =>
      rw [htype] at hproject
      rw [EvalCtx.inlineSharing_resolve, htype]
      dsimp only at hproject ⊢
      cases hinfo : typeConstant.info with
      | iPrj projection =>
        rw [hinfo] at hproject
        dsimp only at hproject
        simp only [Option.map, Constant.inlineSharing,
          ConstantInfo.mapExprs, ConstantIdentityLaws.mapInfo, hinfo]
        cases hresolve : resolveMut ctx projection.block
            projection.idx.toNat with
        | error err =>
          rw [hresolve] at hproject
          contradiction
        | ok pair =>
          rcases pair with ⟨blockConstant, member⟩
          rw [hresolve] at hproject
          rw [resolveMut_inlineSharing_of_eq hresolve]
          cases member with
          | defn definition => contradiction
          | recr recursor => contradiction
          | indc ind =>
            simp only [MutConst.mapExprs,
              ConstantIdentityLaws.mapMutConst,
              ConstantIdentityLaws.mapInductive] at hproject ⊢
            cases value with
            | ctorV block indIdx cidx args =>
              cases hvalue with
              | ctorV _ _ _ _ hargs =>
                simp only [Value.inlineSharing]
                dsimp only at hproject ⊢
                cases hmatches :
                    block == projection.block &&
                      indIdx == projection.idx.toNat with
                | false =>
                  rw [hmatches] at hproject
                  contradiction
                | true =>
                  simp only [hmatches, if_true] at hproject ⊢
                  cases harg : args[ind.params.toNat + fieldIdx.toNat]? with
                  | none =>
                    rw [harg] at hproject
                    contradiction
                  | some projected =>
                    rw [harg] at hproject
                    cases hproject
                    rw [valuesInlineSharing_getElem?, harg]
                    exact ⟨rfl, hargs.getElem?_eq harg⟩
            | papV head args =>
              cases hvalue with
              | papV _ _ hhead hargs =>
                simp only [Value.inlineSharing]
                dsimp only at hproject ⊢
                cases hneutral :
                    (Value.papV head args).isNeutral &&
                      ctx.preserveNeutralElims with
                | false =>
                  rw [hneutral] at hproject
                  contradiction
                | true =>
                  rw [hneutral] at hproject
                  cases hproject
                  have hneutral' :
                      ((Value.papV head.inlineSharing
                            (valuesInlineSharing args)).isNeutral &&
                          ctx.inlineSharing.preserveNeutralElims) = true := by
                    have hvneutral :
                        (Value.papV head.inlineSharing
                          (valuesInlineSharing args)).isNeutral =
                            (Value.papV head args).isNeutral := by
                      simpa only [Value.inlineSharing] using
                        Value.isNeutral_inlineSharing (Value.papV head args)
                    rw [hvneutral,
                      EvalCtx.inlineSharing_preserveNeutralElims]
                    exact hneutral
                  rw [hneutral']
                  exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                      valuesInlineSharing],
                    .papV _ _ (.neuH _) (.cons _ _
                    (.papV _ _ hhead hargs) .nil)⟩
            | sortV | piV | closV | quotV | litV =>
              simp [Value.isNeutral] at hproject
      | defn _ => rw [hinfo] at hproject; contradiction
      | axio _ => rw [hinfo] at hproject; contradiction
      | quot _ => rw [hinfo] at hproject; contradiction
      | cPrj _ => rw [hinfo] at hproject; contradiction
      | rPrj _ => rw [hinfo] at hproject; contradiction
      | dPrj _ => rw [hinfo] at hproject; contradiction
      | recr _ => rw [hinfo] at hproject; contradiction
      | muts _ => rw [hinfo] at hproject; contradiction

theorem majorCtor_sharingWF {peel : Bool} {value : Value}
    (hvalue : value.SharingWF) {cidx : Nat} {args : List Value}
    (hmajor : majorCtor peel value = .ok (cidx, args)) :
    ValuesSharingWF args := by
  cases hvalue with
  | ctorV block indIdx cidx values hvalues =>
    simp only [majorCtor] at hmajor
    cases hmajor
    exact hvalues
  | litV lit =>
    cases lit with
    | strL => simp [majorCtor] at hmajor
    | natL n =>
      cases peel <;> cases n <;> simp [majorCtor] at hmajor
      · rw [hmajor.2]
        exact .nil
      · rw [← hmajor.2]
        exact .cons _ _ (.litV _) .nil
  | sortV | piV | closV | papV | quotV => simp [majorCtor] at hmajor

theorem quotientRep?_inlineSharing (value : Value) :
    quotientRep? value.inlineSharing =
      (quotientRep? value).map Value.inlineSharing := by
  cases value <;> simp [Value.inlineSharing, quotientRep?]

theorem quotientRep?_sharingWF {quotient representative : Value}
    (hquotient : quotient.SharingWF)
    (hrep : quotientRep? quotient = some representative) :
    representative.SharingWF := by
  cases hquotient with
  | quotV address stored hstored =>
    simp only [quotientRep?] at hrep
    cases hrep
    exact hstored
  | sortV | piV | closV | papV | ctorV | litV =>
    simp [quotientRep?] at hrep

theorem rootsBelow_definition_value {table : Array Expr} {d : Definition}
    (h : rootsBelow table d.exprs) :
    Sharing.sharesBelow table.size d.value = true := by
  exact h d.value (by simp [Definition.exprs])

theorem rootsBelow_recursor_rule {table : Array Expr} {r : Recursor}
    (h : rootsBelow table r.exprs) {i : Nat} {rule : RecursorRule}
    (hget : r.rules[i]? = some rule) :
    Sharing.sharesBelow table.size rule.rhs = true := by
  apply h rule.rhs
  simp only [Recursor.exprs, List.mem_cons]
  right
  rw [List.mem_map]
  rcases Array.getElem?_eq_some_iff.mp hget with ⟨hi, heq⟩
  exact ⟨rule, Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨i, hi, heq⟩), rfl⟩

@[simp] theorem Definition.mapExprs_value (f : Expr → Expr)
    (d : Definition) : (d.mapExprs f).value = f d.value := by rfl

@[simp] theorem Definition.mapExprs_lvls (f : Expr → Expr)
    (d : Definition) : (d.mapExprs f).lvls = d.lvls := by rfl

@[simp] theorem Definition.mapExprs_kind (f : Expr → Expr)
    (d : Definition) : (d.mapExprs f).kind = d.kind := by rfl

@[simp] theorem Definition.mapExprs_safety (f : Expr → Expr)
    (d : Definition) : (d.mapExprs f).safety = d.safety := by rfl

@[simp] theorem unfoldable_mapExprs (f : Expr → Expr) (d : Definition) :
    unfoldable (d.mapExprs f) = unfoldable d := by
  simp [unfoldable]

@[simp] theorem Recursor.mapExprs_lvls (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).lvls = r.lvls := by rfl

@[simp] theorem Recursor.mapExprs_params (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).params = r.params := by rfl

@[simp] theorem Recursor.mapExprs_motives (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).motives = r.motives := by rfl

@[simp] theorem Recursor.mapExprs_minors (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).minors = r.minors := by rfl

@[simp] theorem Recursor.mapExprs_indices (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).indices = r.indices := by rfl

@[simp] theorem Recursor.mapExprs_rules (f : Expr → Expr) (r : Recursor) :
    (r.mapExprs f).rules = r.rules.map (RecursorRule.mapExprs f) := by rfl

@[simp] theorem RecursorRule.mapExprs_fields (f : Expr → Expr)
    (r : RecursorRule) : (r.mapExprs f).fields = r.fields := by rfl

@[simp] theorem RecursorRule.mapExprs_rhs (f : Expr → Expr)
    (r : RecursorRule) : (r.mapExprs f).rhs = f r.rhs := by rfl

@[simp] theorem Inductive.mapExprs_lvls (f : Expr → Expr)
    (ind : Inductive) : (ind.mapExprs f).lvls = ind.lvls := by rfl

@[simp] theorem Inductive.mapExprs_params (f : Expr → Expr)
    (ind : Inductive) : (ind.mapExprs f).params = ind.params := by rfl

@[simp] theorem inlineExpr_sort (table : Array Expr) (i : UInt64) :
    Sharing.inlineExpr table (.sort i) = .sort i := by rfl

@[simp] theorem inlineExpr_var (table : Array Expr) (i : UInt64) :
    Sharing.inlineExpr table (.var i) = .var i := by rfl

@[simp] theorem inlineExpr_ref (table : Array Expr) (i : UInt64)
    (us : Array UInt64) :
    Sharing.inlineExpr table (.ref i us) = .ref i us := by rfl

@[simp] theorem inlineExpr_recur (table : Array Expr) (i : UInt64)
    (us : Array UInt64) :
    Sharing.inlineExpr table (.recur i us) = .recur i us := by rfl

@[simp] theorem inlineExpr_prj (table : Array Expr) (r f : UInt64)
    (v : Expr) :
    Sharing.inlineExpr table (.prj r f v) =
      .prj r f (Sharing.inlineExpr table v) := by rfl

@[simp] theorem inlineExpr_str (table : Array Expr) (i : UInt64) :
    Sharing.inlineExpr table (.str i) = .str i := by rfl

@[simp] theorem inlineExpr_nat (table : Array Expr) (i : UInt64) :
    Sharing.inlineExpr table (.nat i) = .nat i := by rfl

@[simp] theorem inlineExpr_app (table : Array Expr) (f a : Expr) :
    Sharing.inlineExpr table (.app f a) =
      .app (Sharing.inlineExpr table f) (Sharing.inlineExpr table a) := by rfl

@[simp] theorem inlineExpr_lam (table : Array Expr) (uses : Uses)
    (dom body : Expr) :
    Sharing.inlineExpr table (.lam uses dom body) =
      .lam uses (Sharing.inlineExpr table dom)
        (Sharing.inlineExpr table body) := by rfl

@[simp] theorem inlineExpr_all (table : Array Expr) (uses : Uses)
    (owned : Owned) (dom cod : Expr) :
    Sharing.inlineExpr table (.all uses owned dom cod) =
      .all uses owned (Sharing.inlineExpr table dom)
        (Sharing.inlineExpr table cod) := by rfl

@[simp] theorem inlineExpr_letE (table : Array Expr) (nonDep : Bool)
    (typ value body : Expr) :
    Sharing.inlineExpr table (.letE nonDep typ value body) =
      .letE nonDep (Sharing.inlineExpr table typ)
        (Sharing.inlineExpr table value)
        (Sharing.inlineExpr table body) := by rfl

theorem sharesBelow_mono {lower upper : Nat} (hle : lower ≤ upper)
    (e : Expr) (h : Sharing.sharesBelow lower e = true) :
    Sharing.sharesBelow upper e = true := by
  induction e with
  | sort | var | ref | recur | str | nat => rfl
  | share i =>
    simp only [Sharing.sharesBelow, decide_eq_true_eq] at h ⊢
    omega
  | prj r f value ih =>
    simp only [Sharing.sharesBelow] at h ⊢
    exact ih h
  | app fn arg ihFn ihArg =>
    simp only [Sharing.sharesBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihFn h.1, ihArg h.2⟩
  | lam uses dom body ihDom ihBody =>
    simp only [Sharing.sharesBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihDom h.1, ihBody h.2⟩
  | all uses owned dom cod ihDom ihCod =>
    simp only [Sharing.sharesBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihDom h.1, ihCod h.2⟩
  | letE nonDep typ value body ihTyp ihValue ihBody =>
    simp only [Sharing.sharesBelow, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihTyp h.1.1, ihValue h.1.2⟩, ihBody h.2⟩

theorem entriesWF_getElem?_sharesBelow (next : Nat) (entries : List Expr)
    (i : Nat) (entry : Expr)
    (hwf : Sharing.entriesWF next entries = true)
    (hget : entries[i]? = some entry) :
    Sharing.sharesBelow (next + i) entry = true := by
  induction entries generalizing next i with
  | nil => simp at hget
  | cons head tail ih =>
    simp only [Sharing.entriesWF, Bool.and_eq_true] at hwf
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hget
      cases hget
      simpa using Sharing.sharesBelow_of_entryWF hwf.1
    | succ i =>
      rw [List.getElem?_cons_succ] at hget
      have hbelow := ih (next + 1) i hwf.2 hget
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbelow

theorem tableWF_getElem?_sharesBelow (table : Array Expr) (i : Nat)
    (entry : Expr) (hwf : Sharing.tableWF table = true)
    (hget : table[i]? = some entry) :
    Sharing.sharesBelow table.size entry = true := by
  have hlist : table.toList[i]? = some entry := by simpa using hget
  have hbelow := entriesWF_getElem?_sharesBelow 0 table.toList i entry hwf hlist
  have hi : i < table.size := (Array.getElem?_eq_some_iff.mp hget).choose
  exact sharesBelow_mono (Nat.le_of_lt hi) entry (by simpa using hbelow)

private def CoherentAt (fuel : Nat) : Prop :=
  (∀ ctx F env e v, ctx.SharingWF → F.SharingWF →
    ValuesSharingWF env → Sharing.sharesBelow F.sharing.size e = true →
    eval ctx fuel F env e = .ok v →
    eval ctx.inlineSharing fuel F.inlineSharing
        (valuesInlineSharing env) (Sharing.inlineExpr F.sharing e) =
          .ok v.inlineSharing ∧ v.SharingWF) ∧
  (∀ ctx address uinst v, ctx.SharingWF →
    evalRef ctx fuel address uinst = .ok v →
    evalRef ctx.inlineSharing fuel address uinst = .ok v.inlineSharing ∧
      v.SharingWF) ∧
  (∀ ctx f a v, ctx.SharingWF → f.SharingWF → a.SharingWF →
    apply ctx fuel f a = .ok v →
    apply ctx.inlineSharing fuel f.inlineSharing a.inlineSharing =
      .ok v.inlineSharing ∧ v.SharingWF) ∧
  (∀ ctx f args v, ctx.SharingWF → f.SharingWF →
    ValuesSharingWF args → applyMany ctx fuel f args = .ok v →
    applyMany ctx.inlineSharing fuel f.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF) ∧
  (∀ ctx h args v, ctx.SharingWF → h.SharingWF →
    ValuesSharingWF args → saturate ctx fuel h args = .ok v →
    saturate ctx.inlineSharing fuel h.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF) ∧
  (∀ ctx h args v, ctx.SharingWF → h.SharingWF →
    ValuesSharingWF args → fire ctx fuel h args = .ok v →
    fire ctx.inlineSharing fuel h.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF)

private theorem bindOkSharing {α β : Type} (a : α)
    (f : α → Except Err β) : (Except.ok a >>= f) = f a := rfl

private theorem bindErrSharing {α β : Type} (err : Err)
    (f : α → Except Err β) :
    ((Except.error err : Except Err α) >>= f) = .error err := rfl

private theorem applyStringChars_inlineSharing_of
    {apply₁ apply₂ : Value → Value → Except Err Value}
    (happly : ∀ f a v, f.SharingWF → a.SharingWF →
      apply₁ f a = .ok v →
        apply₂ f.inlineSharing a.inlineSharing = .ok v.inlineSharing ∧
          v.SharingWF)
    {charOfNat cons list result : Value} (chars : List Char)
    (hcharOfNat : charOfNat.SharingWF) (hcons : cons.SharingWF)
    (hlist : list.SharingWF)
    (h : applyStringChars apply₁ charOfNat cons chars list = .ok result) :
    applyStringChars apply₂ charOfNat.inlineSharing cons.inlineSharing chars
        list.inlineSharing = .ok result.inlineSharing ∧ result.SharingWF := by
  induction chars generalizing list with
  | nil =>
      simp only [applyStringChars] at h ⊢
      cases h
      exact ⟨rfl, hlist⟩
  | cons char chars ih =>
      simp only [applyStringChars] at h ⊢
      cases hchar : apply₁ charOfNat (.litV (.natL char.toNat)) with
      | error err => rw [hchar, bindErrSharing] at h; contradiction
      | ok charValue =>
        rw [hchar, bindOkSharing] at h
        obtain ⟨hchar', hcharWF⟩ := happly charOfNat
          (.litV (.natL char.toNat)) charValue hcharOfNat
          (Value.SharingWF.litV (.natL char.toNat)) hchar
        have hchar'' : apply₂ charOfNat.inlineSharing
            (.litV (.natL char.toNat)) = .ok charValue.inlineSharing := by
          simpa [Value.inlineSharing] using hchar'
        rw [hchar'', bindOkSharing]
        cases hpartial : apply₁ cons charValue with
        | error err => rw [hpartial, bindErrSharing] at h; contradiction
        | ok partialCons =>
          rw [hpartial, bindOkSharing] at h
          obtain ⟨hpartial', hpartialWF⟩ := happly cons charValue partialCons
            hcons hcharWF hpartial
          rw [hpartial', bindOkSharing]
          cases hnext : apply₁ partialCons list with
          | error err => rw [hnext, bindErrSharing] at h; contradiction
          | ok nextList =>
            rw [hnext, bindOkSharing] at h
            obtain ⟨hnext', hnextWF⟩ := happly partialCons list nextList
              hpartialWF hlist hnext
            rw [hnext', bindOkSharing]
            exact ih hnextWF h

private theorem prepareStringMajor_inlineSharing_of
    {evalReference₁ evalReference₂ : Address → List Nat → Except Err Value}
    {apply₁ apply₂ : Value → Value → Except Err Value}
    (href : ∀ address uinst value,
      evalReference₁ address uinst = .ok value →
        evalReference₂ address uinst = .ok value.inlineSharing ∧
          value.SharingWF)
    (happly : ∀ f a value, f.SharingWF → a.SharingWF →
      apply₁ f a = .ok value →
        apply₂ f.inlineSharing a.inlineSharing = .ok value.inlineSharing ∧
          value.SharingWF)
    (config : Option StringLiteralConfig) {rawMajor result : Value}
    (hrawMajor : rawMajor.SharingWF)
    (h : prepareStringMajor evalReference₁ apply₁ config rawMajor =
      .ok result) :
    prepareStringMajor evalReference₂ apply₂ config rawMajor.inlineSharing =
        .ok result.inlineSharing ∧ result.SharingWF := by
  cases rawMajor with
  | litV literal =>
      cases literal with
      | natL n =>
        simp only [prepareStringMajor, Value.inlineSharing] at h ⊢
        cases h
        exact ⟨by simp [Value.inlineSharing], hrawMajor⟩
      | strL string =>
        cases config with
        | none =>
          simp only [prepareStringMajor, Value.inlineSharing] at h ⊢
          cases h
          exact ⟨by simp [Value.inlineSharing], hrawMajor⟩
        | some config =>
          simp only [prepareStringMajor, Value.inlineSharing] at h ⊢
          cases hcharType : evalReference₁ config.charType [] with
          | error err => rw [hcharType, bindErrSharing] at h; contradiction
          | ok charType =>
            rw [hcharType, bindOkSharing] at h
            obtain ⟨hcharType', hcharTypeWF⟩ := href _ _ _ hcharType
            rw [hcharType', bindOkSharing]
            cases hcharOfNat : evalReference₁ config.charOfNat [] with
            | error err => rw [hcharOfNat, bindErrSharing] at h; contradiction
            | ok charOfNat =>
              rw [hcharOfNat, bindOkSharing] at h
              obtain ⟨hcharOfNat', hcharOfNatWF⟩ := href _ _ _ hcharOfNat
              rw [hcharOfNat', bindOkSharing]
              cases hstringOfList :
                  evalReference₁ config.stringOfList [] with
              | error err =>
                rw [hstringOfList, bindErrSharing] at h
                contradiction
              | ok stringOfList =>
                rw [hstringOfList, bindOkSharing] at h
                obtain ⟨hstringOfList', hstringOfListWF⟩ :=
                  href _ _ _ hstringOfList
                rw [hstringOfList', bindOkSharing]
                cases hlistNil : evalReference₁ config.listNil [0] with
                | error err => rw [hlistNil, bindErrSharing] at h; contradiction
                | ok listNil =>
                  rw [hlistNil, bindOkSharing] at h
                  obtain ⟨hlistNil', hlistNilWF⟩ := href _ _ _ hlistNil
                  rw [hlistNil', bindOkSharing]
                  cases hnil : apply₁ listNil charType with
                  | error err => rw [hnil, bindErrSharing] at h; contradiction
                  | ok nil =>
                    rw [hnil, bindOkSharing] at h
                    obtain ⟨hnil', hnilWF⟩ := happly listNil charType nil
                      hlistNilWF hcharTypeWF hnil
                    rw [hnil', bindOkSharing]
                    cases hlistCons : evalReference₁ config.listCons [0] with
                    | error err =>
                      rw [hlistCons, bindErrSharing] at h
                      contradiction
                    | ok listCons =>
                      rw [hlistCons, bindOkSharing] at h
                      obtain ⟨hlistCons', hlistConsWF⟩ :=
                        href _ _ _ hlistCons
                      rw [hlistCons', bindOkSharing]
                      cases hcons : apply₁ listCons charType with
                      | error err => rw [hcons, bindErrSharing] at h; contradiction
                      | ok cons =>
                        rw [hcons, bindOkSharing] at h
                        obtain ⟨hcons', hconsWF⟩ := happly listCons charType cons
                          hlistConsWF hcharTypeWF hcons
                        rw [hcons', bindOkSharing]
                        cases hlist : applyStringChars apply₁ charOfNat cons
                            string.toList.reverse nil with
                        | error err =>
                          rw [hlist, bindErrSharing] at h
                          contradiction
                        | ok list =>
                          rw [hlist, bindOkSharing] at h
                          obtain ⟨hlist', hlistWF⟩ :=
                            applyStringChars_inlineSharing_of happly
                              string.toList.reverse hcharOfNatWF hconsWF hnilWF
                              hlist
                          rw [hlist', bindOkSharing]
                          exact happly stringOfList list result
                            hstringOfListWF hlistWF h
  | sortV | piV | closV | papV | quotV | ctorV =>
      simp only [prepareStringMajor, Value.inlineSharing] at h ⊢
      cases h
      exact ⟨by simp [Value.inlineSharing], hrawMajor⟩

private theorem coherentAt : ∀ fuel, CoherentAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx F env e v hctx hF henv he hev
      rw [eval.eq_def] at hev
      simp at hev
    · intro ctx address uinst v hctx hev
      rw [evalRef.eq_def] at hev
      simp at hev
    · intro ctx f a v hctx hf ha hev
      rw [apply.eq_def] at hev
      simp at hev
    · intro ctx f args v hctx hf hargs hev
      rw [applyMany.eq_def] at hev
      simp at hev
    · intro ctx h args v hctx hh hargs hev
      rw [saturate.eq_def] at hev
      simp at hev
    · intro ctx h args v hctx hh hargs hev
      rw [fire.eq_def] at hev
      simp at hev
  | succ n ih =>
    obtain ⟨ihE, ihR, ihA, ihM, ihS, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx F env e v hctx hF henv he hev
      cases e with
      | var i =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_var]
        dsimp only at hev ⊢
        cases hget : env[i.toNat]? with
        | none => rw [hget] at hev; contradiction
        | some value =>
          rw [hget] at hev
          cases hev
          rw [valuesInlineSharing_getElem?, hget]
          exact ⟨rfl, henv.getElem?_eq hget⟩
      | sort i =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_sort]
        dsimp only [Frame.inlineSharing, Value.inlineSharing] at hev ⊢
        cases hget : F.univs[i.toNat]? with
        | none => rw [hget] at hev; contradiction
        | some u =>
          rw [hget] at hev
          simp only at hev ⊢
          cases hev
          exact ⟨by simp [Value.inlineSharing], .sortV _⟩
      | str i =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_str]
        dsimp only [Frame.inlineSharing, EvalCtx.inlineSharing,
          Value.inlineSharing] at hev ⊢
        cases href : F.refs[i.toNat]? with
        | none => rw [href] at hev; contradiction
        | some address =>
          rw [href] at hev
          simp only at hev ⊢
          cases hblob : ctx.blobs address with
          | none => rw [hblob] at hev; contradiction
          | some blob =>
            cases blob with
            | natB n => rw [hblob] at hev; contradiction
            | strB s =>
              rw [hblob] at hev
              simp only at hev ⊢
              cases hev
              exact ⟨by simp [Value.inlineSharing], .litV _⟩
      | nat i =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_nat]
        dsimp only [Frame.inlineSharing, EvalCtx.inlineSharing,
          Value.inlineSharing] at hev ⊢
        cases href : F.refs[i.toNat]? with
        | none => rw [href] at hev; contradiction
        | some address =>
          rw [href] at hev
          simp only at hev ⊢
          cases hblob : ctx.blobs address with
          | none => rw [hblob] at hev; contradiction
          | some blob =>
            cases blob with
            | strB s => rw [hblob] at hev; contradiction
            | natB n =>
              rw [hblob] at hev
              simp only at hev ⊢
              cases hev
              exact ⟨by simp [Value.inlineSharing], .litV _⟩
      | lam uses dom body =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_lam]
        dsimp only [Value.inlineSharing] at hev ⊢
        cases hev
        simp only [Sharing.sharesBelow, Bool.and_eq_true] at he
        exact ⟨by simp [Value.inlineSharing],
          .closV uses F env dom body hF henv he.1 he.2⟩
      | all uses owned dom cod =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_all]
        dsimp only [Value.inlineSharing] at hev ⊢
        cases hev
        simp only [Sharing.sharesBelow, Bool.and_eq_true] at he
        exact ⟨by simp [Value.inlineSharing],
          .piV uses owned F env dom cod hF henv he.1 he.2⟩
      | letE nonDep typ val body =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_letE]
        dsimp only at hev ⊢
        simp only [Sharing.sharesBelow, Bool.and_eq_true] at he
        cases hval : eval ctx n F env val with
        | error err => rw [hval] at hev; contradiction
        | ok value =>
          rw [hval] at hev
          obtain ⟨hval', hvalueWF⟩ :=
            ihE ctx F env val value hctx hF henv he.1.2 hval
          rw [hval']
          have hbody := ihE ctx F (value :: env) body v hctx hF
            (.cons value env hvalueWF henv) he.2 hev
          change eval ctx.inlineSharing n F.inlineSharing
            (value.inlineSharing :: valuesInlineSharing env)
              (Sharing.inlineExpr F.sharing body) =
                .ok v.inlineSharing ∧ v.SharingWF
          simpa [valuesInlineSharing] using hbody
      | app fn arg =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_app]
        dsimp only at hev ⊢
        simp only [Sharing.sharesBelow, Bool.and_eq_true] at he
        cases hfn : eval ctx n F env fn with
        | error err => rw [hfn] at hev; contradiction
        | ok fnValue =>
          rw [hfn] at hev
          obtain ⟨hfn', hfnWF⟩ :=
            ihE ctx F env fn fnValue hctx hF henv he.1 hfn
          rw [hfn']
          cases harg : eval ctx n F env arg with
          | error err => rw [harg] at hev; contradiction
          | ok argValue =>
            rw [harg] at hev
            obtain ⟨harg', hargWF⟩ :=
              ihE ctx F env arg argValue hctx hF henv he.2 harg
            rw [harg']
            change apply ctx.inlineSharing n fnValue.inlineSharing
              argValue.inlineSharing = .ok v.inlineSharing ∧ v.SharingWF
            exact ihA ctx fnValue argValue v hctx hfnWF hargWF hev
      | prj typeIdx fieldIdx val =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_prj]
        dsimp only at hev ⊢
        cases hval : eval ctx n F env val with
        | error err => rw [hval] at hev; contradiction
        | ok value =>
          rw [hval, bindOkSharing] at hev
          obtain ⟨hval', hvalueWF⟩ :=
            ihE ctx F env val value hctx hF henv he hval
          rw [hval', bindOkSharing]
          exact projectValue_inlineSharing hctx hvalueWF hev
      | share i =>
        rw [eval.eq_def] at hev
        dsimp only at hev
        cases hget : F.sharing[i.toNat]? with
        | none => rw [hget] at hev; contradiction
        | some entry =>
          rw [hget] at hev
          obtain ⟨htarget, hvWF⟩ := ihE ctx F env entry v hctx hF henv
            (tableWF_getElem?_sharesBelow F.sharing i.toNat entry
              hF.tableOk hget) hev
          constructor
          · rw [Sharing.inlineExpr_share_eq_inlineExpr_entry F.sharing i
              entry hF.tableOk hget]
            exact eval_mono (Nat.le_succ n) htarget
          · exact hvWF
      | ref refIdx univIdxs =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_ref]
        simp only [Frame.inlineSharing_refs]
        dsimp only at hev ⊢
        cases href : F.refs[refIdx.toNat]? with
        | none => rw [href] at hev; contradiction
        | some address =>
          rw [href] at hev
          simp only at hev ⊢
          cases huinst : evalUnivArgs F univIdxs with
          | error err => rw [huinst] at hev; contradiction
          | ok uinst =>
            rw [huinst] at hev
            obtain ⟨htarget, hvWF⟩ := ihR ctx address uinst v hctx hev
            rw [evalUnivArgs_inlineSharing, huinst]
            exact ⟨htarget, hvWF⟩
      | recur recIdx univIdxs =>
        rw [eval.eq_def] at hev ⊢
        simp only [inlineExpr_recur]
        dsimp only at hev ⊢
        cases huinst : evalUnivArgs F univIdxs with
        | error err => rw [huinst] at hev; contradiction
        | ok uinst =>
          rw [huinst] at hev
          rw [evalUnivArgs_inlineSharing, huinst]
          rw [bindOkSharing] at hev ⊢
          cases hmember : F.selfMuts[recIdx.toNat]? with
          | none => rw [hmember] at hev; contradiction
          | some member =>
            rw [hmember] at hev
            have hmember' := Frame.inlineSharing_selfMuts_getElem?
              (F := F) hmember
            have hroots := hF.selfMutsOk recIdx.toNat member hmember
            cases member with
            | defn d =>
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst] at hmember'
              rw [hmember']
              simp only
              change (guardLvls d.lvls uinst >>= fun _ =>
                if unfoldable d then
                  eval ctx n { F with uinst := uinst } [] d.value
                else
                  match F.selfAddr with
                  | none => neutralMember F.selfAddr recIdx.toNat
                  | some block =>
                    match ctx.externArity
                        (Address.memberAddr block recIdx.toNat) with
                    | none => neutralMember F.selfAddr recIdx.toNat
                    | some arity => saturate ctx n
                        (.extH (Address.memberAddr block recIdx.toNat) arity)
                        []) =
                  .ok v at hev
              cases hguard : guardLvls d.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapDefinition
                      (Sharing.inlineExpr F.sharing) d).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapDefinition] using hguard
                rw [hguard', bindOkSharing]
                cases hunfold : unfoldable d with
                | false =>
                  rw [hunfold] at hev
                  simp only [Bool.false_eq_true, if_false] at hev
                  have hunfold' : unfoldable
                      (ConstantIdentityLaws.mapDefinition
                        (Sharing.inlineExpr F.sharing) d) = false := by
                    simpa [ConstantIdentityLaws.mapDefinition,
                      unfoldable] using hunfold
                  rw [hunfold']
                  simp only [Bool.false_eq_true, if_false]
                  cases hself : F.selfAddr with
                  | none =>
                    rw [hself] at hev
                    simp [neutralMember] at hev
                  | some block =>
                    rw [hself] at hev
                    dsimp only at hev
                    simp only [Frame.inlineSharing_selfAddr, hself]
                    cases hext : ctx.externArity
                        (Address.memberAddr block recIdx.toNat) with
                    | none =>
                      rw [hext] at hev
                      simp only [EvalCtx.inlineSharing_externArity, hext]
                      simp only [neutralMember] at hev ⊢
                      cases hev
                      exact ⟨by simp [Value.inlineSharing,
                          Head.inlineSharing, valuesInlineSharing],
                        .papV _ _ (.neuH _) .nil⟩
                    | some arity =>
                      rw [hext] at hev
                      simp only [EvalCtx.inlineSharing_externArity, hext]
                      simpa [Head.inlineSharing, valuesInlineSharing] using
                        ihS ctx (.extH
                          (Address.memberAddr block recIdx.toNat) arity)
                          [] v hctx (.extH _ _) .nil hev
                | true =>
                  rw [hunfold] at hev
                  have hunfold' : unfoldable
                      (ConstantIdentityLaws.mapDefinition
                        (Sharing.inlineExpr F.sharing) d) = true := by
                    simpa [ConstantIdentityLaws.mapDefinition,
                      unfoldable] using hunfold
                  rw [hunfold']
                  have hbody := ihE ctx { F with uinst := uinst } []
                    d.value v hctx (hF.with_uinst uinst) .nil
                    (rootsBelow_definition_value hroots) hev
                  simpa [ConstantIdentityLaws.mapDefinition,
                    Frame.inlineSharing_set_uinst,
                    valuesInlineSharing] using hbody
            | recr r =>
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst] at hmember'
              rw [hmember']
              simp only
              change (guardLvls r.lvls uinst >>= fun _ =>
                .ok (.papV
                  (.recH F.selfAddr r { F with uinst := uinst }) [])) =
                    .ok v at hev
              cases hguard : guardLvls r.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapRecursor
                      (Sharing.inlineExpr F.sharing) r).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapRecursor] using hguard
                rw [hguard', bindOkSharing]
                cases hev
                exact ⟨by simp [Recursor.mapExprs,
                    ConstantIdentityLaws.mapRecursor,
                    Value.inlineSharing, Head.inlineSharing,
                    Frame.inlineSharing_set_uinst, valuesInlineSharing],
                  .papV _ _
                    (.recH F.selfAddr r { F with uinst := uinst }
                      (hF.with_uinst uinst)
                      (by simpa [MutConst.exprs] using hroots))
                    .nil⟩
            | indc ind =>
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst] at hmember'
              rw [hmember']
              simp only
              change (guardLvls ind.lvls uinst >>= fun _ =>
                neutralMember F.selfAddr recIdx.toNat) =
                  .ok v at hev
              cases hguard : guardLvls ind.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapInductive
                      (Sharing.inlineExpr F.sharing) ind).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapInductive] using hguard
                rw [hguard', bindOkSharing]
                cases hself : F.selfAddr with
                | none =>
                  rw [hself] at hev
                  simp [neutralMember] at hev
                | some block =>
                  rw [hself] at hev
                  simp only [Frame.inlineSharing_selfAddr, hself,
                    neutralMember] at hev ⊢
                  cases hev
                  exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                      valuesInlineSharing],
                    .papV _ _ (.neuH _) .nil⟩
    · intro ctx address uinst v hctx hev
      rw [evalRef.eq_def] at hev ⊢
      dsimp only at hev ⊢
      cases hresolve : ctx.resolve address with
      | none => rw [hresolve] at hev; contradiction
      | some c =>
        rw [hresolve] at hev
        dsimp only at hev
        simp only [EvalCtx.inlineSharing_resolve, hresolve, Option.map_some]
        have hcWF := hctx.resolveOk address c hresolve
        cases hinfo : c.info with
        | defn d =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (guardLvls d.lvls uinst >>= fun _ =>
            if unfoldable d then
              eval ctx n (Frame.ofConst c uinst) [] d.value
            else
              match ctx.externArity address with
              | none => .ok (.papV (.neuH (.const address)) [])
              | some arity => saturate ctx n (.extH address arity) []) =
                .ok v at hev
          cases hguard : guardLvls d.lvls uinst with
          | error err =>
            rw [hguard, bindErrSharing] at hev
            contradiction
          | ok checked =>
            rw [hguard, bindOkSharing] at hev
            have hguard' : guardLvls
                (ConstantIdentityLaws.mapDefinition
                  (Sharing.inlineExpr c.sharing) d).lvls uinst =
                .ok checked := by
              simpa [ConstantIdentityLaws.mapDefinition] using hguard
            rw [hguard', bindOkSharing]
            cases hunfold : unfoldable d with
            | false =>
              rw [hunfold] at hev
              have hunfold' : unfoldable
                  (ConstantIdentityLaws.mapDefinition
                    (Sharing.inlineExpr c.sharing) d) = false := by
                simpa [ConstantIdentityLaws.mapDefinition,
                  unfoldable] using hunfold
              rw [hunfold']
              cases hext : ctx.externArity address with
              | none =>
                rw [hext] at hev
                simp only [EvalCtx.inlineSharing_externArity, hext]
                cases hev
                exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                    valuesInlineSharing],
                  .papV _ _ (.neuH _) .nil⟩
              | some arity =>
                rw [hext] at hev
                simp only [EvalCtx.inlineSharing_externArity, hext]
                simpa [Head.inlineSharing, valuesInlineSharing] using
                  ihS ctx (.extH address arity) [] v hctx
                    (.extH address arity) .nil hev
            | true =>
              rw [hunfold] at hev
              have hunfold' : unfoldable
                  (ConstantIdentityLaws.mapDefinition
                    (Sharing.inlineExpr c.sharing) d) = true := by
                simpa [ConstantIdentityLaws.mapDefinition,
                  unfoldable] using hunfold
              rw [hunfold']
              have hroots := constantRootsBelow_of_sharingWF c hcWF
              have hvalue : Sharing.sharesBelow c.sharing.size d.value = true := by
                apply hroots d.value
                rw [hinfo]
                simp [ConstantInfo.exprs, Definition.exprs]
              have hbody := ihE ctx (Frame.ofConst c uinst) [] d.value v
                hctx (Frame.sharingWF_ofConst c uinst none hcWF) .nil
                hvalue hev
              simpa [Frame.inlineSharing_ofConst, Frame.inlineSharing,
                Frame.ofConst, EvalCtx.inlineSharing,
                Constant.inlineSharing, ConstantInfo.mapExprs,
                ConstantIdentityLaws.mapInfo, hinfo,
                ConstantIdentityLaws.mapDefinition,
                MutConst.mapExprs, ConstantIdentityLaws.mapMutConst,
                selfMutsOf,
                valuesInlineSharing] using hbody
        | recr r =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (guardLvls r.lvls uinst >>= fun _ =>
            .ok (.papV (.recH (some address) r
              (Frame.ofConst c uinst (some address))) [])) = .ok v at hev
          cases hguard : guardLvls r.lvls uinst with
          | error err =>
            rw [hguard, bindErrSharing] at hev
            contradiction
          | ok checked =>
            rw [hguard, bindOkSharing] at hev
            have hguard' : guardLvls
                (ConstantIdentityLaws.mapRecursor
                  (Sharing.inlineExpr c.sharing) r).lvls uinst =
                .ok checked := by
              simpa [ConstantIdentityLaws.mapRecursor] using hguard
            rw [hguard', bindOkSharing]
            cases hev
            have hrootsAll := constantRootsBelow_of_sharingWF c hcWF
            have hroots : rootsBelow c.sharing r.exprs := by
              intro e he
              apply hrootsAll e
              rw [hinfo]
              simpa [ConstantInfo.exprs] using he
            exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                Frame.inlineSharing, Frame.ofConst, hinfo,
                Recursor.mapExprs, MutConst.mapExprs,
                ConstantIdentityLaws.mapRecursor,
                ConstantIdentityLaws.mapMutConst, selfMutsOf,
                valuesInlineSharing],
              .papV _ _
                (.recH (some address) r
                  (Frame.ofConst c uinst (some address))
                  (Frame.sharingWF_ofConst c uinst (some address) hcWF)
                  hroots)
                .nil⟩
        | axio ax =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (guardLvls ax.lvls uinst >>= fun _ =>
            match ctx.externArity address with
            | none => .ok (.papV (.neuH (.const address)) [])
            | some arity => saturate ctx n (.extH address arity) []) =
              .ok v at hev
          cases hguard : guardLvls ax.lvls uinst with
          | error err =>
            rw [hguard, bindErrSharing] at hev
            contradiction
          | ok checked =>
            rw [hguard, bindOkSharing] at hev
            have hguard' : guardLvls
                (ConstantIdentityLaws.mapAxiom
                  (Sharing.inlineExpr c.sharing) ax).lvls uinst =
                .ok checked := by
              simpa [ConstantIdentityLaws.mapAxiom] using hguard
            rw [hguard', bindOkSharing]
            cases hext : ctx.externArity address with
            | none =>
              rw [hext] at hev
              simp only [EvalCtx.inlineSharing_externArity, hext]
              cases hev
              exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                  valuesInlineSharing],
                .papV _ _ (.neuH _) .nil⟩
            | some arity =>
              rw [hext] at hev
              simp only [EvalCtx.inlineSharing_externArity, hext]
              simpa [Head.inlineSharing, valuesInlineSharing] using
                ihS ctx (.extH address arity) [] v hctx
                  (.extH address arity) .nil hev
        | quot q =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (guardLvls q.lvls uinst >>= fun _ =>
            match ctx.quotientKind address with
            | none => .ok (.papV (.neuH (.const address)) [])
            | some kind =>
              if kind == q.kind then .ok (.papV (.quotH address kind) [])
              else .error (.stuck
                "configured quotient kind mismatch")) = .ok v at hev
          cases hguard : guardLvls q.lvls uinst with
          | error err =>
            rw [hguard, bindErrSharing] at hev
            contradiction
          | ok checked =>
            rw [hguard, bindOkSharing] at hev
            have hguard' : guardLvls
                (ConstantIdentityLaws.mapQuotient
                  (Sharing.inlineExpr c.sharing) q).lvls uinst =
                .ok checked := by
              simpa [ConstantIdentityLaws.mapQuotient] using hguard
            rw [hguard', bindOkSharing]
            cases hkind : ctx.quotientKind address with
            | none =>
              rw [hkind] at hev
              cases hev
              rw [EvalCtx.inlineSharing_quotientKind, hkind]
              exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                  valuesInlineSharing],
                .papV _ _ (.neuH _) .nil⟩
            | some kind =>
              rw [hkind] at hev
              simp only at hev
              cases hmatch : kind == q.kind with
              | false => simp [hmatch] at hev
              | true =>
                rw [hmatch] at hev
                cases hev
                rw [EvalCtx.inlineSharing_quotientKind, hkind]
                simp only
                  [ConstantIdentityLaws.mapQuotient, hmatch]
                exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                    valuesInlineSharing],
                  .papV _ _ (.quotH _ _) .nil⟩
        | cPrj p =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (match resolveMut ctx p.block p.idx.toNat with
            | Except.ok (_, .indc ind) =>
              match ind.ctors[p.cidx.toNat]? with
              | none => Except.error (Err.stuck
                  "constructor projection out of range")
              | some ct => guardLvls ct.lvls uinst >>= fun _ =>
                  saturate ctx n
                    (.ctorH p.block p.idx.toNat p.cidx.toNat
                      (ct.params.toNat + ct.fields.toNat)) []
            | Except.ok _ => Except.error (Err.stuck
                "constructor projection targets a non-inductive")
            | Except.error err => Except.error err) = Except.ok v at hev
          cases hmember : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hmember] at hev; contradiction
          | ok pair =>
            rcases pair with ⟨blockConst, member⟩
            rw [hmember] at hev
            cases member with
            | defn d => simp at hev
            | recr r => simp at hev
            | indc ind =>
              change (match ind.ctors[p.cidx.toNat]? with
                | none => Except.error (Err.stuck
                    "constructor projection out of range")
                | some ct => guardLvls ct.lvls uinst >>= fun _ =>
                    saturate ctx n
                      (.ctorH p.block p.idx.toNat p.cidx.toNat
                        (ct.params.toNat + ct.fields.toNat)) []) =
                          Except.ok v at hev
              rw [resolveMut_inlineSharing_of_eq hmember]
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst,
                ConstantIdentityLaws.mapInductive]
              cases hctor : ind.ctors[p.cidx.toNat]? with
              | none => rw [hctor] at hev; contradiction
              | some ctor =>
                rw [hctor] at hev
                rw [Array.getElem?_map, hctor]
                simp only [Option.map_some]
                change (guardLvls ctor.lvls uinst >>= fun _ =>
                  saturate ctx n
                    (.ctorH p.block p.idx.toNat p.cidx.toNat
                      (ctor.params.toNat + ctor.fields.toNat)) []) = .ok v at hev
                cases hguard : guardLvls ctor.lvls uinst with
                | error err =>
                  rw [hguard, bindErrSharing] at hev
                  contradiction
                | ok checked =>
                  rw [hguard, bindOkSharing] at hev
                  have hguard' : guardLvls
                      (ConstantIdentityLaws.mapConstructor
                        (Sharing.inlineExpr blockConst.sharing) ctor).lvls
                        uinst = .ok checked := by
                    simpa [ConstantIdentityLaws.mapConstructor] using hguard
                  rw [hguard', bindOkSharing]
                  have hsat := ihS ctx
                    (.ctorH p.block p.idx.toNat p.cidx.toNat
                      (ctor.params.toNat + ctor.fields.toNat)) [] v hctx
                    (.ctorH _ _ _ _) .nil hev
                  simpa [ConstantIdentityLaws.mapConstructor,
                    Head.inlineSharing, valuesInlineSharing] using hsat
        | rPrj p =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (match resolveMut ctx p.block p.idx.toNat with
            | Except.ok (blockConst, .recr r) =>
              guardLvls r.lvls uinst >>= fun _ =>
                Except.ok (Value.papV
                  (.recH (some p.block) r
                    (Frame.ofConst blockConst uinst (some p.block))) [])
            | Except.ok _ => Except.error (Err.stuck
                "recursor projection targets a non-recursor")
            | Except.error err => Except.error err) = Except.ok v at hev
          cases hmember : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hmember] at hev; contradiction
          | ok pair =>
            rcases pair with ⟨blockConst, member⟩
            rw [hmember] at hev
            cases member with
            | defn d => simp at hev
            | indc ind => simp at hev
            | recr r =>
              change (guardLvls r.lvls uinst >>= fun _ =>
                Except.ok (Value.papV
                  (.recH (some p.block) r
                    (Frame.ofConst blockConst uinst (some p.block))) [])) =
                  Except.ok v at hev
              rw [resolveMut_inlineSharing_of_eq hmember]
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst]
              have hblockWF := resolveMut_sharingWF_of_eq hctx hmember
              cases hguard : guardLvls r.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapRecursor
                      (Sharing.inlineExpr blockConst.sharing) r).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapRecursor] using hguard
                rw [hguard', bindOkSharing]
                cases hev
                have hroots : rootsBelow blockConst.sharing r.exprs := by
                  simpa [MutConst.exprs] using hblockWF.2
                exact ⟨by
                    simp only [Value.inlineSharing, Head.inlineSharing,
                      valuesInlineSharing]
                    rw [Frame.inlineSharing_ofConst]
                    rfl,
                  .papV _ _
                    (.recH (some p.block) r
                      (Frame.ofConst blockConst uinst (some p.block))
                      (Frame.sharingWF_ofConst blockConst uinst
                        (some p.block) hblockWF.1)
                      hroots)
                    .nil⟩
        | iPrj p =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (match resolveMut ctx p.block p.idx.toNat with
            | Except.ok (_, .indc ind) =>
              guardLvls ind.lvls uinst >>= fun _ =>
                Except.ok (Value.papV (.neuH (.const address)) [])
            | Except.ok _ => Except.error (Err.stuck
                "inductive projection targets a non-inductive")
            | Except.error err => Except.error err) = Except.ok v at hev
          cases hmember : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hmember] at hev; contradiction
          | ok pair =>
            rcases pair with ⟨blockConst, member⟩
            rw [hmember] at hev
            cases member with
            | defn d => simp at hev
            | recr r => simp at hev
            | indc ind =>
              change (guardLvls ind.lvls uinst >>= fun _ =>
                .ok (.papV (.neuH (.const address)) [])) = .ok v at hev
              rw [resolveMut_inlineSharing_of_eq hmember]
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst]
              cases hguard : guardLvls ind.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapInductive
                      (Sharing.inlineExpr blockConst.sharing) ind).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapInductive] using hguard
                rw [hguard', bindOkSharing]
                cases hev
                exact ⟨by simp [Value.inlineSharing, Head.inlineSharing,
                    valuesInlineSharing],
                  .papV _ _ (.neuH _) .nil⟩
        | dPrj p =>
          rw [hinfo] at hev
          simp only [Constant.inlineSharing, ConstantInfo.mapExprs,
            ConstantIdentityLaws.mapInfo, hinfo]
          change (match resolveMut ctx p.block p.idx.toNat with
            | Except.ok (blockConst, .defn d) =>
              guardLvls d.lvls uinst >>= fun _ =>
                if unfoldable d then
                  eval ctx n
                    (Frame.ofConst blockConst uinst (some p.block)) [] d.value
                else
                  match ctx.externArity
                      (Address.memberAddr p.block p.idx.toNat) with
                  | none => .ok (.papV (.neuH (.const address)) [])
                  | some arity => saturate ctx n
                      (.extH (Address.memberAddr p.block p.idx.toNat) arity)
                      []
            | Except.ok _ => Except.error (Err.stuck
                "definition projection targets a non-definition")
            | Except.error err => Except.error err) = Except.ok v at hev
          cases hmember : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hmember] at hev; contradiction
          | ok pair =>
            rcases pair with ⟨blockConst, member⟩
            rw [hmember] at hev
            cases member with
            | indc ind => simp at hev
            | recr r => simp at hev
            | defn d =>
              change (guardLvls d.lvls uinst >>= fun _ =>
                if unfoldable d then
                  eval ctx n
                    (Frame.ofConst blockConst uinst (some p.block)) [] d.value
                else
                  match ctx.externArity
                      (Address.memberAddr p.block p.idx.toNat) with
                  | none => .ok (.papV (.neuH (.const address)) [])
                  | some arity => saturate ctx n
                      (.extH (Address.memberAddr p.block p.idx.toNat) arity)
                      []) = .ok v at hev
              rw [resolveMut_inlineSharing_of_eq hmember]
              simp only [MutConst.mapExprs,
                ConstantIdentityLaws.mapMutConst]
              have hblockWF := resolveMut_sharingWF_of_eq hctx hmember
              cases hguard : guardLvls d.lvls uinst with
              | error err =>
                rw [hguard, bindErrSharing] at hev
                contradiction
              | ok checked =>
                rw [hguard, bindOkSharing] at hev
                have hguard' : guardLvls
                    (ConstantIdentityLaws.mapDefinition
                      (Sharing.inlineExpr blockConst.sharing) d).lvls uinst =
                    .ok checked := by
                  simpa [ConstantIdentityLaws.mapDefinition] using hguard
                rw [hguard', bindOkSharing]
                cases hunfold : unfoldable d with
                | false =>
                  rw [hunfold] at hev
                  simp only [Bool.false_eq_true, if_false] at hev
                  have hunfold' : unfoldable
                      (ConstantIdentityLaws.mapDefinition
                        (Sharing.inlineExpr blockConst.sharing) d) = false := by
                    simpa [ConstantIdentityLaws.mapDefinition,
                      unfoldable] using hunfold
                  rw [hunfold']
                  simp only [Bool.false_eq_true, if_false]
                  cases hext : ctx.externArity
                      (Address.memberAddr p.block p.idx.toNat) with
                  | none =>
                    rw [hext] at hev
                    simp only [EvalCtx.inlineSharing_externArity, hext]
                    cases hev
                    exact ⟨by simp [Value.inlineSharing,
                        Head.inlineSharing, valuesInlineSharing],
                      .papV _ _ (.neuH _) .nil⟩
                  | some arity =>
                    rw [hext] at hev
                    simp only [EvalCtx.inlineSharing_externArity, hext]
                    simpa [Head.inlineSharing, valuesInlineSharing] using
                      ihS ctx (.extH
                        (Address.memberAddr p.block p.idx.toNat) arity)
                        [] v hctx (.extH _ _) .nil hev
                | true =>
                  rw [hunfold] at hev
                  have hunfold' : unfoldable
                      (ConstantIdentityLaws.mapDefinition
                        (Sharing.inlineExpr blockConst.sharing) d) = true := by
                    simpa [ConstantIdentityLaws.mapDefinition,
                      unfoldable] using hunfold
                  rw [hunfold']
                  have hvalue : Sharing.sharesBelow blockConst.sharing.size
                      d.value = true :=
                    rootsBelow_definition_value (by
                      simpa [MutConst.exprs] using hblockWF.2)
                  have hbody := ihE ctx
                    (Frame.ofConst blockConst uinst (some p.block)) []
                    d.value v hctx
                    (Frame.sharingWF_ofConst blockConst uinst
                      (some p.block) hblockWF.1)
                    .nil hvalue hev
                  rw [Frame.inlineSharing_ofConst] at hbody
                  simpa [ConstantIdentityLaws.mapDefinition,
                    valuesInlineSharing] using hbody
        | muts members =>
          rw [hinfo] at hev
          simp at hev
    · intro ctx f a v hctx hf ha hev
      cases f with
      | sortV lvl => rw [apply.eq_def] at hev; simp at hev
      | piV uses owned F env dom cod =>
        rw [apply.eq_def] at hev
        simp at hev
      | closV uses F env dom body =>
        rw [apply.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hf with
        | closV _ _ _ _ _ hF henv hdom hbody =>
          have hresult := ihE ctx F (a :: env) body v hctx hF
            (.cons a env ha henv) hbody hev
          simpa [Value.inlineSharing, valuesInlineSharing] using hresult
      | papV head args =>
        rw [apply.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hf with
        | papV _ _ hhead hargs =>
          have hresult := ihS ctx head (args ++ [a]) v hctx hhead
            (hargs.append (.cons a [] ha .nil)) hev
          simpa [Value.inlineSharing, valuesInlineSharing] using hresult
      | quotV address representative =>
        rw [apply.eq_def] at hev
        simp at hev
      | ctorV block indIdx cidx args =>
        rw [apply.eq_def] at hev
        simp at hev
      | litV lit =>
        rw [apply.eq_def] at hev
        simp at hev
    · intro ctx f args v hctx hf hargs hev
      cases args with
      | nil =>
        rw [applyMany.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hev
        exact ⟨by simp [valuesInlineSharing], hf⟩
      | cons a rest =>
        rw [applyMany.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hargs with
        | cons _ _ ha hrest =>
          cases happly : apply ctx n f a with
          | error err => rw [happly] at hev; contradiction
          | ok applied =>
            rw [happly] at hev
            obtain ⟨happly', happliedWF⟩ :=
              ihA ctx f a applied hctx hf ha happly
            simp only [valuesInlineSharing]
            change (do
              let applied ← apply ctx.inlineSharing n f.inlineSharing
                a.inlineSharing
              applyMany ctx.inlineSharing n applied
                (valuesInlineSharing rest)) =
                  .ok v.inlineSharing ∧ v.SharingWF
            rw [happly']
            have hresult := ihM ctx applied rest v hctx happliedWF hrest hev
            simpa only [bindOkSharing] using hresult
    · intro ctx h args v hctx hh hargs hev
      rw [saturate.eq_def] at hev ⊢
      dsimp only at hev ⊢
      rw [Head.arity?_inlineSharing]
      cases harity : h.arity? with
      | none =>
        rw [harity] at hev
        simp only at hev ⊢
        cases hev
        exact ⟨by simp [Value.inlineSharing], .papV h args hh hargs⟩
      | some arity =>
        rw [harity] at hev
        simp only at hev ⊢
        cases hlength : args.length == arity with
        | false =>
          simp only [valuesInlineSharing_length, hlength] at ⊢
          rw [hlength] at hev
          cases hev
          exact ⟨by simp [Value.inlineSharing], .papV h args hh hargs⟩
        | true =>
          simp only [valuesInlineSharing_length, hlength] at ⊢
          rw [hlength] at hev
          exact ihF ctx h args v hctx hh hargs hev
    · intro ctx h args v hctx hh hargs hev
      cases h with
      | ctorH block indIdx cidx arity =>
        rw [fire.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hev
        exact ⟨by simp [Head.inlineSharing, Value.inlineSharing],
          .ctorV block indIdx cidx args hargs⟩
      | neuH id =>
        rw [fire.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases hev
        exact ⟨by simp [Head.inlineSharing, Value.inlineSharing],
          .papV (.neuH id) args hh hargs⟩
      | extH address arity =>
        rw [fire.eq_def] at hev ⊢
        dsimp only at hev ⊢
        cases horacle : ctx.oracle address args with
        | none =>
          rw [horacle] at hev
          contradiction
        | some result =>
          rw [horacle] at hev
          obtain ⟨horacle', hresultWF⟩ :=
            hctx.oracleOk address args result hargs horacle
          cases hev
          simp only [Head.inlineSharing, EvalCtx.inlineSharing_oracle,
            horacle']
          exact ⟨trivial, hresultWF⟩
      | quotH address kind =>
        cases kind with
        | type =>
          rw [fire.eq_def] at hev ⊢
          dsimp only at hev ⊢
          cases hev
          exact ⟨by simp [Head.inlineSharing, Value.inlineSharing],
            .papV (.quotH address .type) args hh hargs⟩
        | ctor =>
          rw [fire.eq_def] at hev ⊢
          dsimp only at hev ⊢
          cases hrepresentative : args[2]? with
          | none => rw [hrepresentative] at hev; contradiction
          | some representative =>
            rw [hrepresentative] at hev
            cases hev
            rw [valuesInlineSharing_getElem?, hrepresentative]
            simp only [Head.inlineSharing, Option.map, Value.inlineSharing]
            exact ⟨by trivial, .quotV address representative
              (hargs.getElem?_eq hrepresentative)⟩
        | lift =>
          rw [fire.eq_def] at hev ⊢
          dsimp only at hev ⊢
          simp only [Head.inlineSharing]
          cases hfn : args[3]? with
          | none =>
            rw [hfn] at hev
            rw [valuesInlineSharing_getElem?, hfn]
            cases hev
          | some fn =>
            rw [hfn] at hev
            rw [valuesInlineSharing_getElem?, hfn]
            simp only [Option.map]
            cases hquotient : args[5]? with
            | none =>
              rw [hquotient] at hev
              rw [valuesInlineSharing_getElem?, hquotient]
              cases hev
            | some quotient =>
              rw [hquotient] at hev
              rw [valuesInlineSharing_getElem?, hquotient]
              simp only [Option.map]
              simp only at hev
              cases hrep : quotientRep? quotient with
              | none =>
                rw [hrep] at hev
                rw [quotientRep?_inlineSharing, hrep]
                cases hev
              | some representative =>
                rw [hrep] at hev
                rw [quotientRep?_inlineSharing, hrep]
                simp only [Option.map]
                have hfnWF : fn.SharingWF := hargs.getElem?_eq hfn
                have hquotientWF : quotient.SharingWF :=
                  hargs.getElem?_eq hquotient
                have hrepresentativeWF : representative.SharingWF :=
                  quotientRep?_sharingWF hquotientWF hrep
                exact ihA ctx fn representative v hctx hfnWF
                  hrepresentativeWF hev
        | ind =>
          rw [fire.eq_def] at hev ⊢
          dsimp only at hev ⊢
          simp only [Head.inlineSharing]
          cases hmotive : args[3]? with
          | none =>
            rw [hmotive] at hev
            rw [valuesInlineSharing_getElem?, hmotive]
            cases hev
          | some motive =>
            rw [hmotive] at hev
            rw [valuesInlineSharing_getElem?, hmotive]
            simp only [Option.map]
            cases hquotient : args[4]? with
            | none =>
              rw [hquotient] at hev
              rw [valuesInlineSharing_getElem?, hquotient]
              cases hev
            | some quotient =>
              rw [hquotient] at hev
              rw [valuesInlineSharing_getElem?, hquotient]
              simp only [Option.map]
              simp only at hev
              cases hrep : quotientRep? quotient with
              | none =>
                rw [hrep] at hev
                rw [quotientRep?_inlineSharing, hrep]
                cases hev
              | some representative =>
                rw [hrep] at hev
                rw [quotientRep?_inlineSharing, hrep]
                simp only [Option.map]
                have hmotiveWF : motive.SharingWF :=
                  hargs.getElem?_eq hmotive
                have hquotientWF : quotient.SharingWF :=
                  hargs.getElem?_eq hquotient
                have hrepresentativeWF : representative.SharingWF :=
                  quotientRep?_sharingWF hquotientWF hrep
                exact ihA ctx motive representative v hctx hmotiveWF
                  hrepresentativeWF hev
      | recH block r F =>
        cases hh with
        | recH _ _ _ hF hr =>
          rw [fire.eq_def] at hev ⊢
          dsimp only at hev ⊢
          simp only [Head.inlineSharing]
          cases hlast : args.getLast? with
          | none =>
            rw [hlast] at hev
            contradiction
          | some major =>
            rw [hlast] at hev
            simp only at hev
            rw [valuesInlineSharing_getLast?, hlast]
            simp only [Option.map]
            simp only [Recursor.mapExprs_params]
            have hmajorWF : major.SharingWF := hargs.getLast?_eq hlast
            cases hprepare : prepareStringMajor (evalRef ctx n) (apply ctx n)
                ctx.stringLiteral major with
            | error err =>
              rw [hprepare, bindErrSharing] at hev
              contradiction
            | ok prepared =>
              rw [hprepare, bindOkSharing] at hev
              obtain ⟨hprepare', hpreparedWF⟩ :=
                prepareStringMajor_inlineSharing_of
                  (fun address uinst value href =>
                    ihR ctx address uinst value hctx href)
                  (fun function argument value hfunction hargument happly =>
                    ihA ctx function argument value hctx hfunction hargument
                      happly)
                  ctx.stringLiteral hmajorWF hprepare
              rw [EvalCtx.inlineSharing_stringLiteral, hprepare',
                bindOkSharing]
              cases hneutral :
                  prepared.isNeutral && ctx.preserveNeutralElims with
              | true =>
                rw [hneutral] at hev
                have hneutral' :
                    (prepared.inlineSharing.isNeutral &&
                      ctx.inlineSharing.preserveNeutralElims) = true := by
                  rw [Value.isNeutral_inlineSharing prepared,
                    EvalCtx.inlineSharing_preserveNeutralElims]
                  exact hneutral
                rw [hneutral']
                cases hev
                exact ⟨by simp [Value.inlineSharing, Head.inlineSharing],
                  .papV _ _ (.recH block r F hF hr) hargs⟩
              | false =>
                rw [hneutral] at hev
                have hneutral' :
                    (prepared.inlineSharing.isNeutral &&
                      ctx.inlineSharing.preserveNeutralElims) = false := by
                  rw [Value.isNeutral_inlineSharing prepared,
                    EvalCtx.inlineSharing_preserveNeutralElims]
                  exact hneutral
                rw [hneutral']
                cases hguard : guardRecMajor block r.params.toNat prepared with
                | error err =>
                  rw [hguard, bindErrSharing] at hev
                  contradiction
                | ok checked =>
                  rw [hguard, bindOkSharing] at hev
                  rw [guardRecMajor_inlineSharing, hguard, bindOkSharing]
                  cases hmajor : majorCtor
                      (block.isSome && ctx.natBlock == block) prepared with
                  | error err =>
                    rw [hmajor, bindErrSharing] at hev
                    contradiction
                  | ok result =>
                    rcases result with ⟨cidx, cargs⟩
                    rw [hmajor, bindOkSharing] at hev
                    have hcargsWF : ValuesSharingWF cargs :=
                      majorCtor_sharingWF hpreparedWF hmajor
                    have hmajor' : majorCtor
                        (block.isSome && ctx.inlineSharing.natBlock == block)
                        prepared.inlineSharing =
                          .ok (cidx, valuesInlineSharing cargs) := by
                      rw [EvalCtx.inlineSharing_natBlock,
                        majorCtor_inlineSharing, hmajor]
                      rfl
                    rw [hmajor', bindOkSharing]
                    cases hrule : r.rules[cidx]? with
                    | none =>
                      rw [hrule] at hev
                      contradiction
                    | some rule =>
                      rw [hrule] at hev
                      simp only at hev
                      rw [Recursor.mapExprs_rules, Array.getElem?_map, hrule]
                      simp only [Option.map]
                      cases harity :
                          cargs.length != r.params.toNat + rule.fields.toNat with
                      | true =>
                        rw [harity] at hev
                        contradiction
                      | false =>
                        rw [harity] at hev
                        simp only [valuesInlineSharing_length,
                          RecursorRule.mapExprs_fields, harity]
                        simp only [Bool.false_eq_true, if_false,
                          RecursorRule.mapExprs_rhs] at hev ⊢
                        cases heval : eval ctx n F [] rule.rhs with
                        | error err =>
                          rw [heval, bindErrSharing] at hev
                          contradiction
                        | ok rhsV =>
                          rw [heval, bindOkSharing] at hev
                          obtain ⟨heval', hrhsWF⟩ := ihE ctx F [] rule.rhs
                            rhsV hctx hF ValuesSharingWF.nil
                            (rootsBelow_recursor_rule hr hrule) heval
                          have heval'' :
                              eval ctx.inlineSharing n F.inlineSharing []
                                (Sharing.inlineExpr F.sharing rule.rhs) =
                                  .ok rhsV.inlineSharing := by
                            simpa [valuesInlineSharing] using heval'
                          rw [heval'', bindOkSharing]
                          have hcallArgs : ValuesSharingWF
                              (args.take (r.params.toNat + r.motives.toNat +
                                  r.minors.toNat) ++
                                cargs.drop r.params.toNat) :=
                            (hargs.take _).append (hcargsWF.drop _)
                          have hresult := ihM ctx rhsV
                            (args.take (r.params.toNat + r.motives.toNat +
                                r.minors.toNat) ++
                              cargs.drop r.params.toNat)
                            v hctx hrhsWF hcallArgs hev
                          simpa only [valuesInlineSharing_append,
                            valuesInlineSharing_take,
                            valuesInlineSharing_drop,
                            Recursor.mapExprs_motives,
                            Recursor.mapExprs_minors] using hresult

/-! ## Public sharing-coherence theorems -/

/-- Inlining a well-formed sharing table in a frame, environment, and term
preserves every successful evaluation and normalizes its resulting value. -/
theorem eval_inlineSharing {ctx : EvalCtx} {fuel : Nat} {F : Frame}
    {env : List Value} {e : Expr} {v : Value}
    (hctx : ctx.SharingWF) (hF : F.SharingWF)
    (henv : ValuesSharingWF env)
    (he : Sharing.sharesBelow F.sharing.size e = true)
    (hev : eval ctx fuel F env e = .ok v) :
    eval ctx.inlineSharing fuel F.inlineSharing
        (valuesInlineSharing env) (Sharing.inlineExpr F.sharing e) =
          .ok v.inlineSharing ∧ v.SharingWF :=
  (coherentAt fuel).1 ctx F env e v hctx hF henv he hev

/-- Constant resolution commutes with sharing inlining on successful runs. -/
theorem evalRef_inlineSharing {ctx : EvalCtx} {fuel : Nat}
    {address : Address} {uinst : List Nat} {v : Value}
    (hctx : ctx.SharingWF)
    (hev : evalRef ctx fuel address uinst = .ok v) :
    evalRef ctx.inlineSharing fuel address uinst = .ok v.inlineSharing ∧
      v.SharingWF :=
  (coherentAt fuel).2.1 ctx address uinst v hctx hev

/-- Unary application commutes with sharing inlining on successful runs. -/
theorem apply_inlineSharing {ctx : EvalCtx} {fuel : Nat} {f a v : Value}
    (hctx : ctx.SharingWF) (hf : f.SharingWF) (ha : a.SharingWF)
    (hev : apply ctx fuel f a = .ok v) :
    apply ctx.inlineSharing fuel f.inlineSharing a.inlineSharing =
      .ok v.inlineSharing ∧ v.SharingWF :=
  (coherentAt fuel).2.2.1 ctx f a v hctx hf ha hev

/-- Variadic application commutes with sharing inlining on successful runs. -/
theorem applyMany_inlineSharing {ctx : EvalCtx} {fuel : Nat} {f v : Value}
    {args : List Value} (hctx : ctx.SharingWF) (hf : f.SharingWF)
    (hargs : ValuesSharingWF args)
    (hev : applyMany ctx fuel f args = .ok v) :
    applyMany ctx.inlineSharing fuel f.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF :=
  (coherentAt fuel).2.2.2.1 ctx f args v hctx hf hargs hev

/-- Head saturation commutes with sharing inlining on successful runs. -/
theorem saturate_inlineSharing {ctx : EvalCtx} {fuel : Nat} {h : Head}
    {args : List Value} {v : Value} (hctx : ctx.SharingWF)
    (hh : h.SharingWF) (hargs : ValuesSharingWF args)
    (hev : saturate ctx fuel h args = .ok v) :
    saturate ctx.inlineSharing fuel h.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF :=
  (coherentAt fuel).2.2.2.2.1 ctx h args v hctx hh hargs hev

/-- Firing a saturated head commutes with sharing inlining on successful
runs, including recursor rule selection and constructor-field application. -/
theorem fire_inlineSharing {ctx : EvalCtx} {fuel : Nat} {h : Head}
    {args : List Value} {v : Value} (hctx : ctx.SharingWF)
    (hh : h.SharingWF) (hargs : ValuesSharingWF args)
    (hev : fire ctx fuel h args = .ok v) :
    fire ctx.inlineSharing fuel h.inlineSharing
        (valuesInlineSharing args) = .ok v.inlineSharing ∧ v.SharingWF :=
  (coherentAt fuel).2.2.2.2.2 ctx h args v hctx hh hargs hev

/-- Closed evaluation is invariant under complete sharing inlining. -/
theorem evalClosed_inlineSharing {ctx : EvalCtx} {fuel : Nat} {F : Frame}
    {e : Expr} {v : Value} (hctx : ctx.SharingWF) (hF : F.SharingWF)
    (he : Sharing.sharesBelow F.sharing.size e = true)
    (hev : evalClosed ctx F e fuel = .ok v) :
    evalClosed ctx.inlineSharing F.inlineSharing
        (Sharing.inlineExpr F.sharing e) fuel = .ok v.inlineSharing ∧
      v.SharingWF := by
  simpa [evalClosed, valuesInlineSharing] using
    eval_inlineSharing hctx hF ValuesSharingWF.nil he hev

/-- Evaluating a well-formed definition constant is invariant under replacing
the constant store and the selected constant by their fully inlined views. -/
theorem evalConst_inlineSharing {ctx : EvalCtx} {c : Constant}
    {uinst : List Nat} {fuel : Nat} {v : Value}
    (hctx : ctx.SharingWF) (hc : c.sharingWF = true)
    (hev : evalConst ctx c uinst fuel = .ok v) :
    evalConst ctx.inlineSharing c.inlineSharing uinst fuel =
      .ok v.inlineSharing ∧ v.SharingWF := by
  cases hinfo : c.info with
  | defn d =>
    rw [evalConst, hinfo] at hev
    have hrootsAll := constantRootsBelow_of_sharingWF c hc
    have hroots : rootsBelow c.sharing d.exprs := by
      intro e he
      apply hrootsAll e
      rw [hinfo]
      simpa [ConstantInfo.exprs] using he
    have hresult := eval_inlineSharing hctx
      (Frame.sharingWF_ofConst c uinst none hc)
      ValuesSharingWF.nil (rootsBelow_definition_value hroots) hev
    simpa [evalConst, Constant.inlineSharing, hinfo,
      ConstantInfo.mapExprs, ConstantIdentityLaws.mapInfo,
      Frame.inlineSharing_ofConst, Definition.mapExprs_value,
      ConstantIdentityLaws.mapDefinition,
      valuesInlineSharing] using hresult
  | recr r => simp [evalConst, hinfo] at hev
  | axio a => simp [evalConst, hinfo] at hev
  | quot q => simp [evalConst, hinfo] at hev
  | cPrj p => simp [evalConst, hinfo] at hev
  | rPrj p => simp [evalConst, hinfo] at hev
  | iPrj p => simp [evalConst, hinfo] at hev
  | dPrj p => simp [evalConst, hinfo] at hev
  | muts members => simp [evalConst, hinfo] at hev

end Ix.Compiler.Ixon.Eval
