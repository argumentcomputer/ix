import LSpec
import IxC.Kernel.Admission

/-! # The checks that admit user axioms, at the kernel

Small declaration arrays over the committed Ixon prelude, through the fold
under each axiom policy (`Ix.Kernel.Cached.AxiomPolicy`,
`IxC/Kernel/Cached/Policy.lean`), and the role table's admission under the
policy (`Ix.Kernel.Admission.admitAxiomPolicy`):

* a user axiom (`axiom cheat : False`) declines under `strict` and is admitted
  under `allowUser`, which lists it, and a theorem proved from it is accepted
  only there;
* Lean's own `sorryAx`, read under an input key because the table leaves the
  role unbound, declines under both, and so does a restated `Quot.sound`: the
  user arm refuses an axiom whose type is an axiom role's specification;
* without user axioms the two folds agree (T1), on the prelude and with an
  ordinary axiom-free declaration added;
* a check that admits user axioms refuses a table that leaves `sorryAx`,
  `propext` or `Classical.choice` unbound, as an admission error, before
  reading; the strict check does not ask. -/

open Ix.Kernel
open Ix.Kernel.Reader
open Ix.Kernel.Admission

namespace Tests.Ix.Kernel.UserAxioms

/-- A 32-byte address of one repeated byte. -/
def address (tag : UInt8) : Address := ⟨⟨Array.replicate 32 tag⟩⟩

/-- An input key. -/
def key (tag : UInt8) : Key .anon := .id (address tag)

def table : RoleTable := match defaultTable with | .ok t => t | .error _ => default
def pre : Prelude .anon := match builtinPrelude with | .ok p => p | .error _ => default

/-- The table without one role's binding. -/
def unbind (r : Role) (t : RoleTable) : RoleTable := { t with bound := t.bound.filter (·.1 != r) }

/-- The prelude's declarations followed by `extra`. -/
def decls (extra : Array (Declaration .anon)) : Array (Declaration .anon) := pre.ix.decls ++ extra

def strict (extra : Array (Declaration .anon)) :=
  Cached.checkDecls .verified [] (decls extra)

def user (extra : Array (Declaration .anon)) :=
  Cached.checkDeclsWithUserAxioms .verified [] (decls extra)

/-- The failure's message, rendered. -/
def failure (r : Except (CheckError .anon × Nat) (Env .anon)) : String :=
  match r with
  | .error (e, _) => toString e
  | .ok _ => ""

def contains (s pattern : String) : Bool := (s.splitOn pattern).length > 1

/-- The environments' sizes when both accept, and whether both decline. -/
def agree (a b : Except (CheckError .anon × Nat) (Env .anon)) : Bool :=
  match a, b with
  | .ok ea, .ok eb => ea.consts.length == eb.consts.length
  | .error (ea, ia), .error (eb, ib) => ia == ib && toString ea == toString eb
  | _, _ => false

/-- `axiom cheat : False`. -/
def cheat : Declaration .anon := .axiomDecl { name := key 211, levelParams := [], type := .const falseName [] }

/-- `theorem t : False := cheat`. -/
def fromCheat : Declaration .anon := .thmDecl { name := key 212, levelParams := [], type := .const falseName [] }
  (.const (key 211) [])

/-- Lean's `sorryAx.{u} : (α : Sort u) → Bool → α`, under an input key. -/
def sorryAxUnbound : Declaration .anon :=
  .axiomDecl { name := key 213, levelParams := [0], type := sorryAxSpecTy }

/-- `theorem t : False := sorryAx False false`, over the unbound `sorryAx`. -/
def fromSorry : Declaration .anon := .thmDecl { name := key 214, levelParams := [], type := .const falseName [] }
  (.app (.app (.const (key 213) [.zero]) (.const falseName [])) (.const boolFalseName []))

/-- `Quot.sound`'s specification, restated under an input key. -/
def quotSoundRestated : Declaration .anon :=
  .axiomDecl { quotSoundRaw.toConstantVal with name := key 215 }

/-- An axiom-free definition: `def d : Sort 1 := Sort 0`. -/
def plain : Declaration .anon :=
  .defnDecl { name := key 216, levelParams := [], type := .sort (.succ (.succ .zero)) }
    (.sort (.succ .zero)) .opaque

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

/-- The fold under each policy. -/
def foldChecks : Except String Unit := do
  need "the committed prelude reads" (pre.ix.decls.size > 0)
  -- a user axiom
  need "strict declines a user axiom" (strict #[cheat]).toOption.isNone
  need "the strict decline names a non-standard axiom" (contains (failure (strict #[cheat])) "non-standard axiom")
  need "allowUser admits a user axiom" (user #[cheat]).isOk
  need "allowUser lists exactly that user axiom"
    ((userAxiomsOfDecls (decls #[cheat]).toList).map (·.name) == [key 211])
  need "the prelude declares no user axiom" (userAxiomsOfDecls (decls #[]).toList).isEmpty
  need "strict declines a theorem from a user axiom" (strict #[cheat, fromCheat]).toOption.isNone
  need "allowUser accepts a theorem from a user axiom" (user #[cheat, fromCheat]).isOk
  -- Lean's `sorryAx` under an input key: an axiom role's specification
  need "strict declines an unbound sorryAx" (strict #[sorryAxUnbound]).toOption.isNone
  need "allowUser declines an unbound sorryAx" (user #[sorryAxUnbound]).toOption.isNone
  need "the decline names the sorryAx specification"
    (contains (failure (user #[sorryAxUnbound])) "restates the specification of")
  need "allowUser declines a theorem from an unbound sorryAx"
    (user #[sorryAxUnbound, fromSorry]).toOption.isNone
  need "allowUser declines a restated Quot.sound" (user #[quotSoundRestated]).toOption.isNone
  need "the decline names the Quot.sound specification"
    (contains (failure (user #[quotSoundRestated])) "restates the specification of")
  -- T1: without user axioms the folds agree
  need "the prelude: both folds accept alike" ((strict #[]).isOk && agree (strict #[]) (user #[]))
  need "an axiom-free definition: both folds accept alike"
    ((strict #[plain]).isOk && agree (strict #[plain]) (user #[plain]))
  need "an ill-typed theorem without user axioms: both folds decline alike"
    ((strict #[fromCheat]).toOption.isNone && agree (strict #[fromCheat]) (user #[fromCheat]))

/-- The role table's admission under each policy, and the entry over decoded
records under it. -/
def gateChecks : Except String Unit := do
  need "the default table binds sorryAx, propext and Classical.choice"
    (userAxiomRoles.all fun r => (table.addressOf? r).isSome)
  need "allowUser admits the default table" (admitAxiomPolicy .allowUser table).isOk
  for r in userAxiomRoles do
    let t := unbind r table
    need s!"the table without {repr r} leaves it unbound" (t.addressOf? r).isNone
    need s!"strict does not ask for {repr r}" (admitAxiomPolicy .strict t).isOk
    match admitAxiomPolicy .allowUser t with
    | .error (.axiomRoleUnbound r') => need s!"allowUser refuses the table without {repr r}" (r' == r)
    | _ => throw s!"allowUser admits a table without {repr r}"
    match checkConstantsUnder .allowUser (fun _ => address 0) t pre [] [] with
    | .error e@(.axiomRoleUnbound _) =>
      need s!"the refusal is a decline, as an admission error ({repr r})" (e.outcome == .declined)
      need s!"the refusal says which role ({repr r})" (contains (toString e) "unbound")
    | _ => throw s!"the entry admitting user axioms runs without {repr r}"
    need s!"checkConstantsWithUserAxioms refuses the table without {repr r}"
      (checkConstantsWithUserAxioms (fun _ => address 0) t pre [] []).toOption.isNone
  match checkConstantsUnder .allowUser (fun _ => address 0) table pre [] [],
      checkConstantsWith (fun _ => address 0) table pre [] [] with
  | .ok (env, axs), .ok env' =>
    need "the prelude through the entry lists no user axiom" axs.isEmpty
    need "the prelude through the entry: the same environment as strict"
      (env.consts.length == env'.consts.length)
  | _, _ => throw "the prelude through the entry does not accept under both policies"

private def unit (label : String) (check : Unit → Except String Unit) : LSpec.TestSeq :=
  .individualIO label none (do
    let result ← IO.lazyPure check
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

def suite : List LSpec.TestSeq := [
  unit "the fold under each axiom policy: user axioms, axiom role specifications, T1" (fun _ => foldChecks),
  unit "the role table's admission under each axiom policy" (fun _ => gateChecks)
]

end Tests.Ix.Kernel.UserAxioms
