import IxCC.Src.Pinned
import IxCC.Src.Table.Shape
import IxCC.Src.Resource.Profile
import IxCC.Ixon.PureHash

/-! Structural resource-selection bindings against Src declarations. These
checks deliberately establish no resource-checker verdict or profile semantics. -/

namespace IxCC.Src.Resource

open IxCC.Ixon

def headers (type : Term) : List Header :=
  type.pis.1.zipIdx.filterMap fun ((b, _), i) =>
    if b.contract == .many then none else some { position := i, contract := b.contract }

private def resolve (p : Program) (a : IxCC.Ixon.Address) : Except String CId :=
  match p.lookup a with
  | some c => pure c
  | none => throw s!"resource binding: address {a} is absent from the closure"

def validateContext (p : Program) (ctx : Context) : Except String Profile := do
  unless IxCC.Ixon.Address.blake3Pure ctx.bytes == ctx.address do throw "resource binding: profile hash mismatch"
  let profile ← Profile.ofBytes ctx.bytes
  unless profile.scalarTypes.isEmpty do throw "resource binding: scalar ownership crossing is unsupported"
  for xs in [profile.assumptions, profile.shareableTypes, profile.choices,
      profile.caseDefinitions, profile.linearTypes] do
    for a in xs.toList do let _ ← resolve p a
  for a in [profile.natType, profile.stringType, profile.eqType].filterMap id do
    let c ← resolve p a
    unless (p.decl? c).any (fun d => match d with | .induct .. => true | _ => false) do
      throw "resource binding: profile type is not an inductive declaration"
  if let some eq := profile.eqType then
    unless p.known.eq.any (p.addr · == eq) do throw "resource binding: Eq is not the pinned declaration"
  if let some nat := profile.natType then
    unless p.known.nat.any (p.addr · == nat) do throw "resource binding: Nat is not the pinned declaration"
  for (a, mask) in profile.interfaces.toList do
    let c ← resolve p a
    let some d := p.decl? c | throw "resource binding: absent interface"
    unless d.type.pis.1.length == mask.size do throw "resource binding: interface arity mismatch"
  for (f, t) in profile.equations.toList do
    let f ← resolve p f
    let t ← resolve p t
    unless (p.decl? f).any (fun d => match d with | .defn .defn .safe .. => true | _ => false) &&
        (p.decl? t).any (fun d => match d with | .defn .thm .safe .. => true | _ => false) do
      throw "resource binding: equation pair has the wrong declaration kinds"
  let mut seen : List IxCC.Ixon.Address := []
  for pair in ctx.pairs do
    unless !seen.contains pair.definition do throw "resource binding: duplicate checked definition"
    seen := pair.definition :: seen
    unless pair.profile == ctx.address do throw "resource binding: checked pair names another profile"
    unless profile.equations.toList.contains (pair.definition, pair.equation) do
      throw "resource binding: checked pair is not bound by the effective profile"
    let f ← resolve p pair.definition
    let t ← resolve p pair.equation
    let some (.defn .defn .safe n type _) := p.decl? f | throw "resource binding: subject is not safe"
    let some (.defn .thm .safe n' theoremType _) := p.decl? t | throw "resource binding: equation is not a safe theorem"
    unless n == n' do throw "resource binding: equation universe count differs"
    let (bs, conclusion) := theoremType.pis
    let some (sourceBinders, resultType) := Table.peelPis bs.length type
      | throw "resource binding: subject has fewer binders than the equation"
    unless (sourceBinders.zip bs).all (fun ((_, d), (_, td)) => Table.domainEqv p d td) do
      throw "resource binding: equation binder domains differ"
    match conclusion.spine with
    | (.const eq [_], [(eqType, _), (lhs, _), (_, _)]) =>
      unless p.known.eq == some eq do throw "resource binding: theorem is not over pinned Eq"
      unless Table.domainEqv p resultType eqType do throw "resource binding: equation result type differs"
      let us := (List.range n).map fun i => Univ.var i.toUInt64
      let args := (List.range bs.length).reverse.map fun i => (Term.var i, Mode.strict, Rel.rel)
      unless lhs.eqv (Term.mkApps (.const f us) args) do
        throw "resource binding: theorem does not equate the bound subject"
    | _ => throw "resource binding: theorem is not an equation telescope"
    unless pair.contracts == headers type do throw "resource binding: source header metadata differs"
    unless pair.contracts == headers theoremType do throw "resource binding: theorem header metadata differs"
  return profile

def validate (p : Program) : Except String Unit := do
  if let some ctx := p.resource then let _ ← validateContext p ctx

/-- The selected theorem must be bound by the raw profile and checked-pair
records. No Boolean verdict or diagnostic name participates. -/
def requirePair (p : Program) (f thm : CId) : Except String Unit := do
  let some ctx := p.resource | throw "eqn-drops-contracts: no resource equation binding"
  let _ ← validateContext p ctx
  unless ctx.pairs.any (fun q => q.definition == p.addr f && q.equation == p.addr thm) do
    throw "eqn-drops-contracts: equation is not the bound checked pair"

/-- A bound RHS cannot silently become a primitive, csimp, case, or fallback.
This only checks equation selection, not arbitrary profile execution behavior. -/
def selected (p : Program) (table : Table) : Except String Unit := do
  validate p
  if let some ctx := p.resource then
    for (_, entry) in table.resolve.toList do
      if let .csimp .. := entry then throw "resource binding: csimp replacement is unsupported"
    for pair in ctx.pairs do
      let f ← resolve p pair.definition
      let thm ← resolve p pair.equation
      match table.resolveOf f with
      | some (.eqn actual _) =>
        unless actual == thm do throw "resource binding: another equation overrides the checked pair"
      | _ => throw "resource binding: checked equation was refused, omitted, or overridden"

end IxCC.Src.Resource
