module
public import Tests.Ix.Resource
public import Ix.Resource.Addressed
public import Tests.Ix.ResourceAddressed
public section
namespace Tests.ResourceScalar
open Ixon Ix.Resource Tests.Resource

def base : Program := { program with
  shareableTypes := #[]
  declarations := program.declarations.push
    { type := arr (b .erased) .shared (.sort 0) (.sort 0), kind := .typeConstructor } }
def enabled : Program := { base with scalarTypes := #[0, 11] }

def cases : Array Case := #[
  ⟨"scalar literal unique", arr (b .many) .unique, lam (b .many) zero, "ok"⟩,
  ⟨"scalar shared to unique", arr (b .many) .unique, lam (b .many) (v 0), "ok"⟩,
  ⟨"scalar unique reuse", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .many) (v 0) (v 1)), "ok"⟩,
  ⟨"scalar linear duplication refused", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (bind (b .many) (v 0) (v 1)), "usage"⟩,
  ⟨"scalar erased use refused", arr (b .erased) .unique, lam (b .erased) (v 0), "usage"⟩,
  ⟨"scalar usage does not cross", arr (b .linear), lam (b .linear) (call 5 (v 0)), "usage"⟩,
  ⟨"scalar locality retained", arr (b .many .localShared) .unique,
    lam (b .many .localShared) (v 0), "unrestricted"⟩,
  ⟨"boxed scalar container not scalar", arr (b .many) .unique pairTy pairTy,
    lam (b .many) (v 0) pairTy, "ownership"⟩,
  ⟨"polymorphic value not scalar",
    arr (b .erased) .shared (.sort 0) (arr (b .many) .unique (v 0) (v 1)),
    lam (b .erased) (lam (b .many) (v 0) (v 0)) (.sort 0), "ownership"⟩,
  ⟨"applied nominal head not scalar",
    arr (b .many) .unique (.app (ref 11) natTy) (.app (ref 11) natTy),
    lam (b .many) (v 0) (.app (ref 11) natTy), "ownership"⟩,
  ⟨"scalar reusable capture", arr (b .many .unique) .shared natTy (arr (b .many) .unique),
    lam (b .many .unique) (lam (b .many) (v 1)), "ok"⟩
]

def disabledCases : Array Case := cases.map fun c =>
  if c.name == "scalar literal unique" || c.name == "scalar shared to unique" then { c with expected := "ownership" }
  else if c.name == "scalar unique reuse" || c.name == "scalar linear duplication refused" then
    { c with expected := "capture" }
  else if c.name == "scalar erased use refused" then { c with expected := "ownership" }
  else if c.name == "scalar reusable capture" then { c with expected := "capture" }
  else c

def fixtureText (tests : Array Case) : String := tests.foldl
  (fun text c => text ++ fixtureLine c ++ "\n")
  "# name\texpected\ttype (ixon-v4 hex)\tbody (ixon-v4 hex)\n"

def run : IO Unit := do
  let a ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-scalar.tsv" enabled cases
  let b ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-scalar-disabled.tsv" base disabledCases
  IO.println s!"Scalar resource assumptions: {a+b} shared cases passed"
end Tests.ResourceScalar

namespace Tests.ResourceScalar
open Ixon Ix.Resource

def scalarProfile : Profile :=
  { scalarTypes := #[(Address.fromString "0000000000000000000000000000000000000000000000000000000000000000").get!] }

def profileFixture : Except String String := do
  return s!"scalar\t{hexOfBytes scalarProfile.bytes}\n"

def checkProfile : IO Unit := do
  let p := scalarProfile
  let decoded ← IO.ofExcept (Profile.ofBytes p.bytes)
  unless decoded.scalarTypes == p.scalarTypes && decoded.bytes == p.bytes do
    throw <| IO.userError "scalar profile roundtrip"
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/scalar-profile.tsv") == (← IO.ofExcept profileFixture) do
    throw <| IO.userError "scalar profile shared bytes differ"
  let unit := p.scalarTypes[0]!
  unless ({ p with scalarTypes := #[unit, unit] }.validate).toOption.isNone do
    throw <| IO.userError "duplicate scalar address accepted"
  let base : Profile := {}
  for bytes in [base.bytes ++ ⟨#[32, 0, 0]⟩, base.bytes ++ ⟨#[64, 0]⟩] do
    unless (Profile.ofBytes bytes).toOption.isNone do throw <| IO.userError "malformed scalar profile accepted"
  for n in [base.bytes.size+1:p.bytes.size] do
    unless (Profile.ofBytes (p.bytes.extract 0 n)).toOption.isNone do
      throw <| IO.userError "truncated scalar profile accepted"
  IO.println "Scalar profile: shared canonical bytes and malformed forms passed"
end Tests.ResourceScalar
