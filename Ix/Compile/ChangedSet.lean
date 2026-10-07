/- # The changed-set record (the output contract, design document §11.5)

## Contract
Input: the final driver state of a Pass 3 compile (`CompileEnv`, as every
driver returns it: `compileEnvAux`, `compileEnvParallelAux`,
`compileLeanInput`'s `LeanPipelineOut.cenv`). Output: a deterministic record
of every name whose compiled form the compiler *intentionally* made something
other than the independent export of Lean's declaration, and of the faithful
but non-canonical constants it knows about, each with the compiler's own
reason. `ix compile-lean` writes it next to the `.ixe` (`<stem>.changed.json`);
no byte of the `.ixe` depends on it.

Every claim is read from a table the compiler fills while it compiles, never
from a symptom of the output:
* `image`: `CompileEnv.p3Heads` (image-kind auxiliaries of a changed block ↦
  the block's key) and `p3Blocks` (key ↦ Lean's `all`);
* `rewritten`: `p3Rewritten` (members the call-site rewrite changed; their
  metadata carries the `_ix.inline` records);
* `decline`: `p3NonCanonical` (one cause per constant, the last);
* `transported`, `carried`, `canonical` (clique), `lean-form` (clique kept
  in Lean's form, and Lean's encoding constants of a transported clique):
  `p3Cliques`, `p3CliqueRoots`, `p3CliquePlans` (the plan each clique's
  blocks used, including its side-car record `_ix.clique`);
* `pj-form`, `inherited`: `p3PjForms` (the Lean definitions whose canonical
  form `c._ix` a proof-justified pass wrote, with the passes), and the input's
  references to them;
* `canonical` (other): the reserved names (D14) the output binds;
* `refused`, `failed`: `CompileEnv.ungrounded` (a refused caller by the clique
  hook's named error, `Ix.Compile.Pass.callerRefusalPrefix`).

## Faithfulness
Observational: a function of the final state; nothing here is read by the
compile.

## Canonicity
The record is a function of the tables, which are functions of the input
(the block rule; schedule identity): sorted, it is the same bytes for every
driver and worker count (the `changed-set` suite checks 1 against 32
workers).

## Side condition and fallback
Only a Pass 3 compile has the tables; with `IX_PASS3=off` no record is made.

## Non-canonical set and evidence
Not a pass. Evidence: the `changed-set` suite (determinism, coverage of every
image head, transported member, `_ix.inline` carrier and reserved name, and
every address in the artifact).
-/
module
public import Ix.Compile.Pass.Driver
public section

namespace Ix.Compile.ChangedSet

open Ix (Name ConstantInfo)
open Ix.CompileM (CompileEnv)
open Ix.Compile.Pass (CliqueOutcome CliquePlan)

/-- The format tag, first field of the record. -/
def formatTag : String := "ix-changed-set/1"

/-- What the compiler did to a name (the record's change classes). -/
inductive Change where
  /-- a Lean auxiliary of a changed inductive block: its image (Def 3.4/3.5) -/
  | image
  /-- a Lean constant whose call sites into a changed block were rewritten
  (Def 3.6: inline images, then O1–O6/O11a) -/
  | rewritten
  /-- a recorded decline of a definitional pass (O11a) -/
  | decline
  /-- a member of a transported definition clique (value `Φ_σ`) -/
  | transported
  /-- an equation lemma carried with a transported clique -/
  | carried
  /-- a reserved `_ix` name (D14): a canonical constant with no Lean counterpart -/
  | canonical
  /-- the Lean name of a definition whose canonical form `c._ix` a
  proof-justified pass wrote (D1): the Lean name keeps the faithful form -/
  | pjForm
  /-- a Lean constant that references a `pj-form` name (its term is Lean's) -/
  | inherited
  /-- a clique, or Lean's encoding constant of a transported clique, kept in
  Lean's form -/
  | leanForm
  /-- a block refused by the clique hook (a caller unfolding Lean's encoding) -/
  | refused
  /-- any other block failure: the name publishes nothing -/
  | failed
  deriving BEq, Inhabited

def Change.tag : Change → String
  | .image => "image" | .rewritten => "rewritten" | .decline => "decline"
  | .transported => "transported" | .carried => "carried" | .canonical => "canonical"
  | .pjForm => "pj-form" | .inherited => "inherited" | .leanForm => "lean-form"
  | .refused => "refused" | .failed => "failed"

/-- Whether the compiler's claim is that the Ix constant under the name is
**not** the independent export of Lean's declaration (true for `image`,
`rewritten`, `decline`, `transported`, `carried`, and for `canonical`, which
has no Lean declaration), or that it is (false: `pj-form`, `inherited`,
`lean-form` are faithful, non-canonical forms; `refused` and `failed` publish
nothing). -/
def Change.differs : Change → Bool
  | .image | .rewritten | .decline | .transported | .carried | .canonical => true
  | _ => false

/-- One claim about one name. -/
structure Entry where
  name : Name
  change : Change
  /-- the non-canonical cause (the vocabulary of design document §7.1/§7.2:
  `IMAGE`, `O11A-PENDING`, `PJ-FORM-<pass>`, `INHERITED`, `ORDER-STMT`,
  `NOSPEC`, `SHAPE`, `GUESSLEX`), `none` where the form is canonical -/
  cause : Option String := none
  /-- the address of the Ix constant under the name (`Named.addr`) -/
  addr : Option Address := none
  /-- `Named.original` (an image: Lean's form compiled without rewrite) -/
  original : Option Address := none
  /-- the changed block's key, the clique's key, or the related name -/
  ref : Option Name := none
  detail : String := ""
  deriving Inhabited

/-- A changed inductive block. -/
structure BlockRow where
  key : Name
  /-- Lean's `all`, each with the address of its Ix inductive -/
  all : Array (Name × Option Address)
  /-- its image-kind heads -/
  heads : Array Name
  deriving Inhabited

/-- An encoded definition clique of the input (`p3Cliques`). -/
structure CliqueRow where
  key : Name
  all : Array Name
  /-- `transported`, `baseline`, `unchanged`, `not-encoded`, or `unplanned`
  (no block of the clique compiled) -/
  outcome : String
  encoding : Option String := none
  cause : Option String := none
  why : String := ""
  sigma : Array Nat := #[]
  carried : Array Name := #[]
  aliases : Array (Name × Name) := #[]
  /-- the side-car record (`CliquePlan.record`), stored on the functionals -/
  record : Option String := none
  /-- the canonical constants stored (name, address, the Lean constant it
  transports) -/
  canonical : Array (Name × Address × Name) := #[]
  deriving Inhabited

structure Record where
  blocks : Array BlockRow := #[]
  cliques : Array CliqueRow := #[]
  entries : Array Entry := #[]
  deriving Inhabited

/-! ## Order -/

/-- The sort key of a name: its pretty form, then its hash (pretty forms
can collide; the hash is the name's identity). -/
def nameKey (n : Name) : String × String := (n.pretty, toString n.getHash)

def nameLt (a b : Name) : Bool := compare (nameKey a) (nameKey b) == .lt

def sortNames (xs : Array Name) : Array Name := xs.qsort nameLt

def Entry.key (e : Entry) : String × String × String × String × String :=
  let (p, h) := nameKey e.name
  (p, h, e.change.tag, (e.cause.getD ""), (e.ref.map (·.pretty)).getD "")

/-! ## The record from the tables -/

/-- The prefix of `n` before its first reserved component, if any. -/
def beforeReserved (n : Name) : Option Name := do
  let cs := Ix.Compile.Pass.comps n
  let i ← cs.findIdx? fun
    | .s x => Ix.Compile.Pass.isReservedComponent x
    | .n _ => false
  return Ix.Compile.Pass.ofComps (cs.take i)

def kindOf : Option ConstantInfo → String
  | some (.defnInfo _) => "definition" | some (.thmInfo _) => "theorem"
  | some (.recInfo _) => "recursor" | some (.opaqueInfo _) => "opaque"
  | some (.inductInfo _) => "inductive" | some (.ctorInfo _) => "constructor"
  | some (.axiomInfo _) => "axiom" | some (.quotInfo _) => "quotient"
  | none => "absent"

def outcomeTag : CliqueOutcome → String
  | .transported _ => "transported" | .baseline .. => "baseline"
  | .unchanged .. => "unchanged" | .notEncoded _ => "not-encoded"

/-- The record of a Pass 3 compile (see the module docstring). -/
def ofCompile (cenv : CompileEnv) : Record := Id.run do
  let addrOf (n : Name) : Option Address := (cenv.nameToNamed.get? n).map (·.addr)
  let failed (n : Name) : Bool := cenv.ungrounded.contains n
  let mut es : Array Entry := #[]
  -- changed inductive blocks and their images
  let mut headsOf : Std.HashMap Name (Array Name) := {}
  for (h, key) in cenv.p3Heads do
    headsOf := headsOf.insert key ((headsOf.getD key #[]).push h)
    if failed h then continue
    let named? := cenv.nameToNamed.get? h
    let leanKind := kindOf (cenv.env.get? h)
    let stored := if leanKind == "theorem" then "theorem" else "definition"
    es := es.push { name := h, change := .image, cause := some "IMAGE", addr := named?.map (·.addr)
                    original := (named?.bind (·.original)).map (·.1), ref := some key
                    detail := s!"image of Lean's {leanKind}, stored as a {stored}" }
  let mut memberKey : Std.HashMap Name Name := {}
  let mut blocks : Array BlockRow := #[]
  for (key, all) in cenv.p3Blocks do
    for m in all do memberKey := memberKey.insert m key
    blocks := blocks.push { key, all := all.map fun m => (m, addrOf m)
                            heads := sortNames (headsOf.getD key #[]) }
  -- the call-site rewrite and its recorded declines
  for n in cenv.p3Rewritten do
    if failed n then continue
    es := es.push { name := n, change := .rewritten, addr := addrOf n
                    detail := "call sites into a changed block rewritten (Def 3.6, O1-O6/O11a); `_ix.inline` records" }
  for (n, cause) in cenv.p3NonCanonical do
    if failed n then continue
    let tag := if cause.startsWith "O11a declined" then "O11A-PENDING" else "DECLINE"
    es := es.push { name := n, change := .decline, cause := some tag, addr := addrOf n, detail := cause }
  -- definition cliques
  let mut cliqueOf : Std.HashMap Name (Array Name × Array Name) := {}
  for (_, (all, carried)) in cenv.p3Cliques do
    if let some k := all[0]? then cliqueOf := cliqueOf.insert k (all, carried)
  let mut cliques : Array CliqueRow := #[]
  let mut cliqueCanon : Std.HashSet Name := {}
  let mut transportedKeys : Std.HashMap Name (Array Name) := {}
  for (key, (all, carried)) in cliqueOf do
    match cenv.p3CliquePlans.get? key with
    | none => cliques := cliques.push { key, all, carried, outcome := "unplanned" }
    | some o@(.transported plan) =>
      transportedKeys := transportedKeys.insert key (all ++ carried)
      let causeOf (n : Name) : Option String :=
        (plan.causes.find? (·.1 == n)).map (·.2.1.tag)
      let enc := plan.encoding.tag
      for m in all do
        if failed m then continue
        let alias := (plan.aliases.find? (·.1 == m)).map fun (_, r) => s!"; O17: the constant of {r.pretty}"
        es := es.push { name := m, change := .transported, cause := causeOf m, addr := addrOf m, ref := some key
                        detail := s!"{enc}; sigma {plan.sigma}{alias.getD ""}" }
      for c in carried do
        if failed c then continue
        es := es.push { name := c, change := .carried, cause := causeOf c, addr := addrOf c, ref := some key
                        detail := s!"equation lemma carried with the {enc} clique" }
      let mut canon : Array (Name × Address × Name) := #[]
      for (d, src) in plan.canon do
        let some a := addrOf d.name | continue
        cliqueCanon := cliqueCanon.insert d.name
        canon := canon.push (d.name, a, src)
        let fn := if plan.functionals.contains d.name then "; carries the `_ix.clique` record" else ""
        es := es.push { name := d.name, change := .canonical, cause := causeOf d.name, addr := some a
                        ref := some key, detail := s!"canonical constant of the clique, transports {src.pretty}{fn}" }
      cliques := cliques.push { key, all, carried, outcome := outcomeTag o, encoding := some enc
                                sigma := plan.sigma, aliases := plan.aliases, record := some plan.record
                                canonical := canon.qsort fun a b => nameLt a.1 b.1 }
    | some o@(.baseline enc cause why) =>
      for m in all do
        if failed m then continue
        es := es.push { name := m, change := .leanForm, cause := some cause, addr := addrOf m, ref := some key
                        detail := s!"clique kept in Lean's form ({enc.tag}): {why}" }
      cliques := cliques.push { key, all, carried, outcome := outcomeTag o, encoding := some enc.tag
                                cause := some cause, why }
    | some o@(.unchanged enc src) =>
      cliques := cliques.push { key, all, carried, outcome := outcomeTag o, encoding := some enc.tag
                                why := s!"order by {src.tag}" }
    | some o@(.notEncoded why) =>
      cliques := cliques.push { key, all, carried, outcome := outcomeTag o, why }
  -- names the output binds: Lean's encoding constants of transported cliques,
  -- and the other reserved names
  let pjCanon : Std.HashMap Name Name := cenv.p3PjForms.fold (init := {}) fun m c _ =>
    m.insert (Ix.Compile.Pass.ixFormName c) c
  for (n, named) in cenv.nameToNamed do
    if Ix.Compile.Pass.hasReserved n then
      if cliqueCanon.contains n then continue
      let (ref, detail) := match pjCanon.get? n with
        | some c => (some c, s!"canonical form of {c.pretty} (D1)")
        | none => match (beforeReserved n).bind memberKey.get? with
          | some key => (some key, "Ix auxiliary of a changed block under its display name (D14)")
          | none => (none, "reserved name (D14)")
      es := es.push { name := n, change := .canonical, addr := some named.addr, ref, detail }
    else if !transportedKeys.isEmpty then
      if let some cl := Ix.Compile.Pass.encodingOwner? cenv.p3CliqueRoots n then
        if let some key := cl[0]? then
          if let some own := transportedKeys.get? key then
            if !own.contains n then
              es := es.push { name := n, change := .leanForm, cause := some "ORDER-STMT", addr := some named.addr
                              ref := some key, detail := "Lean's encoding constant of a transported clique (Lean's form)" }
  -- proof-justified passes: the Lean names, and the constants that reference them
  for (c, passes) in cenv.p3PjForms do
    if failed c then continue
    for p in (if passes.isEmpty then #[""] else passes) do
      es := es.push { name := c, change := .pjForm, cause := some s!"PJ-FORM-{p}", addr := addrOf c
                      ref := some (Ix.Compile.Pass.ixFormName c)
                      detail := "the Lean name keeps the faithful form; the canonical form is its `_ix` (D1)" }
  if !cenv.p3PjForms.isEmpty then
    for (n, named) in cenv.nameToNamed do
      if Ix.Compile.Pass.hasReserved n || cenv.p3PjForms.contains n then continue
      let some ci := cenv.env.get? n | continue
      let hits := sortNames ((Ix.Compile.Canon.refsConst ci).toArray.filter cenv.p3PjForms.contains)
      if let some c := hits[0]? then
        es := es.push { name := n, change := .inherited, cause := some "INHERITED", addr := some named.addr
                        ref := some c, detail := s!"references {", ".intercalate (hits.toList.map (·.pretty))}" }
  -- block failures
  for (n, msg) in cenv.ungrounded do
    let refused := (msg.splitOn Ix.Compile.Pass.callerRefusalPrefix).length > 1
    es := es.push { name := n, change := if refused then .refused else .failed, detail := msg }
  let sorted := es.qsort fun a b => compare a.key b.key == .lt
  return { blocks := blocks.qsort fun a b => nameLt a.key b.key
           cliques := cliques.qsort fun a b => nameLt a.key b.key
           entries := sorted }

/-! ## Rendering (JSON, one element per line) -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A JSON string literal. -/
def jstr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | '\t' => out ++ "\\t"
      | '\r' => out ++ "\\r"
      | c =>
        if c.toNat < 0x20 then
          out ++ "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++ String.singleton (hexDigit (c.toNat % 16))
        else out.push c
  return out.push '"'

def jopt (s : Option String) : String := (s.map jstr).getD "null"

def jarr (xs : Array String) : String := "[" ++ ",".intercalate xs.toList ++ "]"

def jname (n : Name) : String := jstr n.pretty

def jnames (ns : Array Name) : String := jarr (ns.map jname)

def Entry.render (e : Entry) : String :=
  "{" ++ ",".intercalate [
    s!"\"name\":{jname e.name}", s!"\"hash\":{jstr (toString e.name.getHash)}",
    s!"\"change\":{jstr e.change.tag}", s!"\"differs\":{e.change.differs}",
    s!"\"cause\":{jopt e.cause}", s!"\"addr\":{jopt (e.addr.map toString)}",
    s!"\"original\":{jopt (e.original.map toString)}", s!"\"ref\":{jopt (e.ref.map (·.pretty))}",
    s!"\"detail\":{jstr e.detail}"] ++ "}"

def BlockRow.render (b : BlockRow) : String :=
  let all := b.all.map fun (n, a) =>
    "{" ++ s!"\"name\":{jname n},\"hash\":{jstr (toString n.getHash)},\"addr\":{jopt (a.map toString)}" ++ "}"
  "{" ++ s!"\"key\":{jname b.key},\"all\":{jarr all},\"heads\":{jnames b.heads}" ++ "}"

def CliqueRow.render (c : CliqueRow) : String :=
  let canon := c.canonical.map fun (n, a, src) =>
    "{" ++ s!"\"name\":{jname n},\"hash\":{jstr (toString n.getHash)},\"addr\":{jstr (toString a)},\"transports\":{jname src}" ++ "}"
  let aliases := c.aliases.map fun (m, r) => jarr #[jname m, jname r]
  "{" ++ ",".intercalate [
    s!"\"key\":{jname c.key}", s!"\"all\":{jnames c.all}", s!"\"outcome\":{jstr c.outcome}",
    s!"\"encoding\":{jopt c.encoding}", s!"\"cause\":{jopt c.cause}", s!"\"why\":{jstr c.why}",
    s!"\"sigma\":{jarr (c.sigma.map toString)}", s!"\"carried\":{jnames c.carried}",
    s!"\"aliases\":{jarr aliases}", s!"\"record\":{jopt c.record}", s!"\"canonical\":{jarr canon}"] ++ "}"

/-- The number of entries of each change class, in `Change.tag` order. -/
def Record.counts (r : Record) : Array (String × Nat) :=
  #[Change.image, .rewritten, .decline, .transported, .carried, .canonical, .pjForm, .inherited,
    .leanForm, .refused, .failed].map fun c => (c.tag, (r.entries.filter (·.change == c)).size)

def Record.render (r : Record) : String :=
  let lines (xs : Array String) : String :=
    if xs.isEmpty then "[]" else "[\n" ++ ",\n".intercalate xs.toList ++ "\n]"
  let counts := r.counts.map fun (t, k) => s!"{jstr t}:{k}"
  "{" ++ s!"\"format\":{jstr formatTag},\n\"mode\":\"pass3\",\n" ++
    s!"\"counts\":" ++ "{" ++ ",".intercalate counts.toList ++ "}" ++ ",\n" ++
    s!"\"blocks\":{lines (r.blocks.map (·.render))},\n" ++
    s!"\"cliques\":{lines (r.cliques.map (·.render))},\n" ++
    s!"\"entries\":{lines (r.entries.map (·.render))}" ++ "}\n"

/-- The record's file next to an `.ixe`: `<stem>.changed.json`. -/
def pathFor (ixe : System.FilePath) : System.FilePath := ixe.withExtension "changed.json"

end Ix.Compile.ChangedSet

end
