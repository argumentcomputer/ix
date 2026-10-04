module

public import Ix.Resource.Check

public section

namespace Tests.Resource

open Ixon Ix.Resource

abbrev E := Ixon.Expr

def natTy : E := .ref 0 #[]
def pairTy : E := .ref 7 #[]
def zero : E := .nat 0
def b (uses : Uses) (value : ValueContract := .shared) : BinderContract := ⟨uses, value⟩
def arr (input : BinderContract) (result : ValueContract := .shared)
    (domain : E := natTy) (codomain : E := natTy) : E := .all input result domain codomain
def lam (input : BinderContract) (body : E) (domain : E := natTy) : E := .lam input domain body
def v (n : UInt64) : E := .var n
def ref (n : UInt64) : E := .ref n #[]
def call (n : UInt64) (arg : E) : E := .app (ref n) arg
def bind (contract : BinderContract) (value body : E) (type : E := natTy) : E :=
  .letE { nonDep := false, binder := contract } type value body
def borrow (owner body : E) (uses : Uses := .many) (type : E := natTy) : E :=
  .letE (.borrow false uses) type owner body

def choiceType (result : ValueContract) : E :=
  arr (b .linear) .shared natTy
    (arr (b .affine result) .shared natTy (arr (b .affine result) result))

/-- Test-only explicit assumptions. Production admission must bind their
addresses and the special selection behavior in its checker profile. -/
def program : Program := {
  declarations := #[
    { type := .sort 0, kind := .typeConstructor },                            -- 0 Nat
    { type := arr (b .many .localShared), kind := .assumption },              -- 1 observe
    { type := arr (b .linear .localShared) .localShared,
      body := some (lam (b .linear .localShared) (v 0)) },                    -- 2 local id
    { type := arr (b .linear .unique) .unique,
      body := some (lam (b .linear .unique) (v 0)) },                         -- 3 unique id
    { type := arr (b .erased), kind := .assumption },                        -- 4 erased input
    { type := arr (b .many), kind := .assumption },                          -- 5 many input
    { type := choiceType .shared, kind := .assumption },                     -- 6 choice
    { type := .sort 0, kind := .typeConstructor },                            -- 7 Pair
    { type := arr (b .linear .localShared) .localShared natTy pairTy,
      kind := .assumption },                                               -- 8 retain in pair
    { type := choiceType .localShared, kind := .assumption },                -- 9 local choice
    { type := choiceType .unique, kind := .assumption }                      -- 10 unique choice
  ]
  fields := #[
    { typeRef := 7, index := 0, type := natTy, contract := .unique },
    { typeRef := 7, index := 1, type := arr (b .many), contract := .unique },
    { typeRef := 7, index := 2, type := arr (b .many), contract := .shared }
  ]
  natType := some natTy
  stringType := some natTy
  sharing := #[v 0, ref 6]
  shareableTypes := #[0, 7]
  choices := #[6, 9, 10]
}

def choose (which : UInt64) (left right : E) : E :=
  .app (.app (call which zero) left) right

def runCase (type value : E) (limits : Limits := {}) : Except Error Unit :=
  let p := { program with declarations := program.declarations.push { type, body := some value } }
  checkDefinition p program.declarations.size limits

def errorCode : Error → String
  | .budget => "budget"
  | .unbound _ => "unbound"
  | .badReference _ => "reference"
  | .unresolvedSharing _ => "sharing"
  | .unsupported _ => "unsupported"
  | .typeMismatch => "type"
  | .binderMismatch => "binder"
  | .usage .. => "usage"
  | .moved _ => "moved"
  | .sharedToUnique => "ownership"
  | .activeLoan _ => "loan"
  | .escape .. => "escape"
  | .unrestrictedEscape _ => "unrestricted"
  | .nonduplicable => "capture"
  | .invalidBorrow => "borrow"
  | .invalidPlace => "place"
  | .invalidScope => "scope"

structure Case where
  name : String
  type : E
  value : E
  expected : String := "ok"

def closureType (result : ValueContract := .shared) : E := arr (b .many) result

def scopedRead (body : E) : E :=
  bind (b .affine) (borrow (v 0) body) (v 1)

def cases : Array Case := #[
  -- Usage
  ⟨"ordinary identity", arr (b .many), lam (b .many) (v 0), "ok"⟩,
  ⟨"linear identity", arr (b .linear), lam (b .linear) (v 0), "ok"⟩,
  ⟨"unused erased", arr (b .erased), lam (b .erased) zero, "ok"⟩,
  ⟨"erased argument has zero demand", arr (b .erased),
    lam (b .erased) (call 4 (v 0)), "ok"⟩,
  ⟨"unused affine", arr (b .affine), lam (b .affine) zero, "ok"⟩,
  ⟨"missing linear consumption", arr (b .linear), lam (b .linear) zero, "usage"⟩,
  ⟨"runtime erased variable", arr (b .erased), lam (b .erased) (v 0), "usage"⟩,
  ⟨"many invocation crosses for a shareable immediate", arr (b .affine), lam (b .affine) (call 5 (v 0)), "ok"⟩,
  ⟨"many permits repeated demand", arr (b .many), lam (b .many) (call 5 (v 0)), "ok"⟩,
  ⟨"linear ordinary let", arr (b .linear),
    lam (b .linear) (bind (b .linear) (v 0) (v 0)), "ok"⟩,
  ⟨"erased let initializer", arr (b .linear),
    lam (b .linear) (bind (b .erased) (v 0) (v 1)), "ok"⟩,
  ⟨"duplicate affine through let", arr (b .affine),
    lam (b .affine) (bind (b .affine) (v 0) (v 1)), "usage"⟩,
  ⟨"fresh inner linear binder under many demand", arr (b .many),
    lam (b .many) (call 5 (bind (b .linear) (v 0) (v 0))), "ok"⟩,
  ⟨"type formation has zero runtime demand", arr (b .erased) .shared (.sort 0) (.sort 0),
    lam (b .erased) (v 0) (.sort 0), "ok"⟩,
  ⟨"type use cannot discharge linear runtime obligation", arr (b .linear) .shared (.sort 0) (.sort 0),
    lam (b .linear) (v 0) (.sort 0), "usage"⟩,

  -- Ownership transfers
  ⟨"linear unique transfer", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (v 0), "ok"⟩,
  ⟨"shared cannot become unique", arr (b .linear) .unique,
    lam (b .linear) (v 0), "ownership"⟩,
  ⟨"unique cannot transfer twice despite many", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .linear .unique) (v 0)
      (bind (b .linear .unique) (v 1) (v 0))), "moved"⟩,
  ⟨"permanent sharing relinquishes unique", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .affine) (v 0) (v 1)), "ownership"⟩,

  -- Locality
  ⟨"local input local output", arr (b .linear .localShared) .localShared,
    lam (b .linear .localShared) (v 0), "ok"⟩,
  ⟨"local unique input local unique output", arr (b .linear .localUnique) .localUnique,
    lam (b .linear .localUnique) (v 0), "ok"⟩,
  ⟨"local input cannot escape", arr (b .linear .localShared),
    lam (b .linear .localShared) (v 0), "unrestricted"⟩,
  ⟨"local helper result can be forwarded", arr (b .linear .localShared) .localShared,
    lam (b .linear .localShared) (call 2 (v 0)), "ok"⟩,
  ⟨"inner local let cannot escape as local", arr (b .linear) .localShared,
    lam (b .linear) (bind (b .linear .localShared) (v 0) (v 0)), "escape"⟩,

  -- Shared loans
  ⟨"borrow ends before owner transfer", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (scopedRead (call 1 (v 0))), "ok"⟩,
  ⟨"unique access during loan", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (borrow (v 0) (v 1)), "loan"⟩,
  ⟨"loan view cannot escape", arr (b .many .unique) .localShared,
    lam (b .many .unique) (borrow (v 0) (v 0)), "escape"⟩,
  ⟨"loan end does not restore permanently shared owner", arr (b .many .unique) .unique,
    lam (b .many .unique) (scopedRead (v 1)), "ownership"⟩,
  ⟨"nested shared reborrow", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (scopedRead (borrow (v 0) (call 1 (v 0)))), "ok"⟩,
  ⟨"borrow requires owner place", arr (b .many .unique),
    lam (b .many .unique) (borrow (call 3 (v 0)) zero), "place"⟩,
  ⟨"borrow cannot manufacture unique view", arr (b .many .unique),
    lam (b .many .unique) (.letE {
      nonDep := false
      kind := .borrowShared
      binder := b .many .localUnique } natTy (v 0) zero), "borrow"⟩,
  ⟨"moved owner cannot be borrowed", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .linear .unique) (v 0)
      (borrow (v 1) (v 1))), "moved"⟩,
  ⟨"projected loan suspends whole owner", arr (b .linear .unique) .unique pairTy pairTy,
    lam (b .linear .unique) (borrow (.prj 7 0 (v 0)) (v 1)) pairTy, "loan"⟩,
  ⟨"projected loan ends before owner transfer", arr (b .linear .unique) .unique pairTy pairTy,
    lam (b .linear .unique)
      (bind (b .affine) (borrow (.prj 7 0 (v 0)) (call 1 (v 0))) (v 1)) pairTy, "ok"⟩,
  ⟨"discarding borrow before narrowing fresh result", arr (b .many .unique) .localShared,
    lam (b .many .unique) (borrow (v 0) (call 1 (v 0))), "ok"⟩,
  ⟨"erased owner cannot be restored through a borrow", arr (b .erased .unique),
    lam (b .erased .unique) (borrow (v 0) (call 1 (v 0))), "unsupported"⟩,
  ⟨"erased view cannot be restored through a reborrow", arr (b .many .unique),
    lam (b .many .unique) (borrow (v 0) (borrow (v 0) (call 1 (v 0))) .erased), "unsupported"⟩,

  -- Captures and projections
  ⟨"shared closure may copy an affine immediate capture", arr (b .affine) .shared natTy (closureType .shared),
    lam (b .affine) (lam (b .many) (v 1)), "ok"⟩,
  ⟨"unique closure retains finite capture", arr (b .linear) .unique natTy (closureType .shared),
    lam (b .linear) (lam (b .many) (v 1)), "ok"⟩,
  ⟨"local closure may retain local input", arr (b .many .localShared) .localShared natTy (closureType .localShared),
    lam (b .many .localShared) (lam (b .many) (v 1)), "ok"⟩,
  ⟨"closure cannot hide local escape", arr (b .many .localShared) .shared natTy (closureType .localShared),
    lam (b .many .localShared) (lam (b .many) (v 1)), "unrestricted"⟩,
  ⟨"aggregate cannot hide local escape", arr (b .linear .localShared) .shared natTy pairTy,
    lam (b .linear .localShared) (call 8 (v 0)), "unrestricted"⟩,
  ⟨"aggregate retains caller locality", arr (b .linear .localShared) .localShared natTy pairTy,
    lam (b .linear .localShared) (call 8 (v 0)), "ok"⟩,
  ⟨"shared aggregate cannot expose reusable unique closure", arr (b .linear) .shared pairTy (closureType .shared),
    lam (b .linear) (.prj 7 1 (v 0)) pairTy, "capture"⟩,
  ⟨"unique aggregate transfers unique closure field", arr (b .linear .unique) .unique pairTy (closureType .shared),
    lam (b .linear .unique) (.prj 7 1 (v 0)) pairTy, "ok"⟩,
  ⟨"shared field retains its reusable function contract", arr (b .linear) .shared pairTy (closureType .shared),
    lam (b .linear) (.prj 7 2 (v 0)) pairTy, "ok"⟩,
  ⟨"projected borrow cannot launder unique closure", arr (b .many) .shared pairTy natTy,
    lam (b .many) (borrow (.prj 7 1 (v 0)) zero .many (closureType .shared)) pairTy, "capture"⟩,
  ⟨"capturing owner transfers it even when closure only borrows", arr (b .linear .unique) .unique natTy (closureType .shared),
    lam (b .linear .unique) (lam (b .many) (borrow (v 1) (call 1 (v 0)))), "ok"⟩,
  ⟨"reborrowing closure captures the view without moving its root", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (scopedRead
      (bind (b .linear .localShared)
        (lam (b .many) (borrow (v 1) (call 1 (v 0))))
        (.app (v 0) zero) (closureType .shared))), "ok"⟩,

  -- Branches and selection
  ⟨"linear use in both alternatives", arr (b .linear),
    lam (b .linear) (choose 6 (v 0) (v 0)), "ok"⟩,
  ⟨"linear missing in one alternative", arr (b .linear),
    lam (b .linear) (choose 6 (v 0) zero), "usage"⟩,
  ⟨"affine use in one alternative", arr (b .affine),
    lam (b .affine) (choose 6 (v 0) zero), "ok"⟩,
  ⟨"unique move in each alternative", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (choose 10 (v 0) (v 0)), "ok"⟩,
  ⟨"alternative move prevents later use", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .affine .unique) (choose 10 (v 0) (v 0)) (v 1)), "moved"⟩,
  ⟨"partial selection is not an ordinary function", arr (b .many),
    lam (b .many) (call 6 (v 0)), "unsupported"⟩,
  ⟨"selection cannot bypass its rule through a callback", arr (b .many) .shared natTy (choiceType .shared),
    lam (b .many) (ref 6), "unsupported"⟩,
  ⟨"branch analysis follows a shared application head", arr (b .linear),
    lam (b .linear) (.app (.app (.app (.share 1) zero) (v 0)) (v 0)), "ok"⟩,

  -- Interfaces and sharing
  ⟨"unregistered projection has no optimistic rule", arr (b .many .unique),
    lam (b .many .unique) (.prj 0 0 (v 0)), "unsupported"⟩,
  ⟨"sharing checked in live binder context", arr (b .linear),
    lam (b .linear) (.share 0), "ok"⟩,
  ⟨"sharing cannot cache away erased restriction", arr (b .erased),
    lam (b .erased) (.share 0), "usage"⟩,
  ⟨"lambda and interface input must agree", arr (b .linear),
    lam (b .many) (v 0), "binder"⟩,
  ⟨"erased higher order argument still checks its contracts", arr (b .erased) .shared (arr (b .linear)) natTy,
    lam (b .erased) (.app (lam (b .erased) zero (arr (b .many))) (v 0)) (arr (b .linear)), "type"⟩,
  ⟨"erased higher order argument with matching interface", arr (b .erased) .shared (arr (b .many)) natTy,
    lam (b .erased) (.app (lam (b .erased) zero (arr (b .many))) (v 0)) (arr (b .many)), "ok"⟩
]

def higherOrderCases : Array Case := Id.run do
  let callback := arr (b .linear .localShared)
  let type := arr (b .many .localShared) .localShared callback
    (arr (b .linear .localShared))
  let value := lam (b .many .localShared)
    (lam (b .linear .localShared) (.app (v 1) (v 0))) callback
  let recursiveType := arr (b .many) .shared natTy
    (arr (b .linear .localShared) .localShared)
  let recursiveBody := lam (b .many) (lam (b .linear .localShared)
    (choose 9 (v 0) (.app (call 11 (v 1)) (v 0))))
  let mismatched := arr (b .many) .shared (arr (b .linear .localShared))
    (arr (b .many) .shared (arr (b .many)) natTy)
  let mismatchBody := lam (b .many)
    (lam (b .many) (bind (b .linear) (v 1) zero (arr (b .many))))
    (arr (b .linear .localShared))
  return #[
    ⟨"higher order local callback and argument", type, value, "ok"⟩,
    ⟨"recursive contract retains resource across alternatives", recursiveType, recursiveBody, "ok"⟩,
    ⟨"higher order contract mismatch", mismatched, mismatchBody, "type"⟩
  ]

def allCases : Array Case := cases ++ higherOrderCases

/-- One `resource.tsv` row: name, expected outcome, type and body bytes. -/
def fixtureLine (test : Case) : String :=
  s!"{test.name}\t{test.expected}\t{hexOfBytes (runPut (putExpr test.type))}\t{hexOfBytes (runPut (putExpr test.value))}"

/-- The shared `resource.tsv` fixture, also read by the Rust resource checker.
`lake exe ixon-v4-tests --export-fixtures` writes it. -/
def fixtureText : String :=
  allCases.foldl (fun text test => text ++ fixtureLine test ++ "\n")
    s!"# name\texpected\ttype ({Ixon.wireFormatId} hex)\tbody ({Ixon.wireFormatId} hex)\n"

def resTy : E := .ref 11 #[]
def prfTy : E := .ref 13 #[]

/-- The base program extended for the usage and ownership modes. Mirrors the
Rust `modes_program`; new declarations are only appended. -/
def modesProgram : Program := { program with
  declarations := program.declarations ++ #[
    { type := .sort 0, kind := .typeConstructor },                            -- 11 Res
    { type := arr (b .many) .shared resTy resTy, kind := .assumption },       -- 12 Res consumer
    { type := .sort 1, kind := .typeConstructor },                            -- 13 Prf : Prop
    { type := arr (b .many) .shared prfTy natTy, kind := .assumption },       -- 14 proof consumer
    { type := arr (b .many) .shared natTy (arr (b .many)), kind := .assumption }, -- 15 binary
    { type := arr (b .many) .shared natTy (.sort 1),
      body := some (lam (b .many) (.prj 0 0 (v 0))) },                       -- 16 a proposition whose
                                                                              --    unfolding has no field rule
    { type := arr (b .many) .shared (.app (ref 16) zero) natTy,
      kind := .assumption },                                                 -- 17 consumes its proof
    { type := arr (b .many) .shared (.sort 0) (arr (b .many) .shared (.sort 0) (.sort 0)),
      kind := .typeConstructor },                                            -- 18 Duo α β
    { type := arr (b .many) .shared (.sort 0)
        (arr (b .many) .shared (arr (b .many) .shared (v 0) (.sort 0)) (.sort 0)),
      kind := .typeConstructor },                                            -- 19 Sig α β
    { type := arr (b .many) .shared natTy (.sort 0), kind := .typeConstructor } -- 20 F : Nat → Type
  ]
  -- Open field rules: `Duo α β` has `fst : α`, `snd : β`; `Sig α β` has
  -- `fst : α`, `snd : β fst`.
  fields := program.fields ++ #[
    { typeRef := 18, index := 0, type := v 1, contract := .shared, binders := 2 },
    { typeRef := 18, index := 1, type := v 1, contract := .shared, binders := 3 },
    { typeRef := 19, index := 0, type := v 1, contract := .shared, binders := 2 },
    { typeRef := 19, index := 1, type := .app (v 1) (v 0), contract := .shared, binders := 3 }
  ]
  propSort := some 1 }

def duoTy : E := .app (.app (ref 18) natTy) resTy
def sigTy : E := .app (.app (ref 19) natTy) (ref 20)

def modeCases : Array Case := #[
  -- Usage crossing for shareable immediates at call boundaries.
  ⟨"linear shareable value crosses a many call", arr (b .linear),
    lam (b .linear) (call 5 (v 0)), "ok"⟩,
  ⟨"many call scales demand of a non-shareable value", arr (b .affine) .shared resTy resTy,
    lam (b .affine) (call 12 (v 0)) resTy, "usage"⟩,
  ⟨"crossing still counts every caller read", arr (b .linear),
    lam (b .linear) (.app (call 15 (v 0)) (v 0)), "usage"⟩,
  ⟨"crossing keeps zero demand of an erased input", arr (b .linear),
    lam (b .linear) (call 4 (v 0)), "usage"⟩,
  -- Proof arguments are erased computation.
  ⟨"erased proof passed to an ordinary binder", arr (b .erased) .shared prfTy natTy,
    lam (b .erased) (call 14 (v 0)) prfTy, "ok"⟩,
  ⟨"local proof passed to an unrestricted binder", arr (b .many .localShared) .shared prfTy natTy,
    lam (b .many .localShared) (call 14 (v 0)) prfTy, "ok"⟩,
  ⟨"erased data passed to an ordinary binder", arr (b .erased),
    lam (b .erased) (call 5 (v 0)), "usage"⟩,
  ⟨"a returned proof is still checked as a value", arr (b .linear .localShared) .shared prfTy prfTy,
    lam (b .linear .localShared) (v 0) prfTy, "unrestricted"⟩,
  -- A proposition is typed before it is reduced.
  ⟨"a proposition is recognized before its unfolding", arr (b .erased) .shared (.app (ref 16) zero) natTy,
    lam (b .erased) (call 17 (v 0)) (.app (ref 16) zero), "ok"⟩,
  -- Captured immediates are copied into a closure.
  ⟨"a linear immediate capture keeps a closure reusable", arr (b .linear) .shared natTy (arr (b .linear)),
    lam (b .linear) (lam (b .linear) (.app (call 15 (v 1)) (v 0))), "ok"⟩,
  ⟨"a unique immediate capture read by a closure keeps it reusable", arr (b .linear .unique) .shared natTy (arr (b .linear)),
    lam (b .linear .unique) (lam (b .linear) (.app (call 15 (v 1)) (v 0))), "ok"⟩,
  -- Review F2: a capture the closure moves makes it one-shot, immediate or not.
  ⟨"a unique immediate capture moved by a closure makes it one-shot", arr (b .linear .unique) .shared natTy (arr (b .linear)),
    lam (b .linear .unique) (lam (b .linear) (.app (call 15 (call 3 (v 1))) (v 0))), "capture"⟩,
  ⟨"a one-shot closure may move a unique immediate capture", arr (b .linear .unique) .unique natTy (arr (b .linear)),
    lam (b .linear .unique) (lam (b .linear) (.app (call 15 (call 3 (v 1))) (v 0))), "ok"⟩,
  ⟨"a finite non-shareable capture stays one-shot", arr (b .affine) .shared resTy (arr (b .many) .shared natTy resTy),
    lam (b .affine) (lam (b .many) (v 1)) resTy, "capture"⟩,
  ⟨"a unique non-shareable capture stays one-shot", arr (b .linear .unique) .shared resTy (arr (b .many) .unique natTy resTy),
    lam (b .linear .unique) (lam (b .many) (v 1)) resTy, "capture"⟩,
  ⟨"a one-shot closure may carry a unique non-shareable capture", arr (b .linear .unique) .unique resTy (arr (b .many) .unique natTy resTy),
    lam (b .linear .unique) (lam (b .many) (v 1)) resTy, "ok"⟩,
  -- Fields of parameterised and dependent structures.
  ⟨"a parameterised field takes its type from the value's type", arr (b .linear) .shared duoTy natTy,
    lam (b .linear) (.prj 18 0 (v 0)) duoTy, "ok"⟩,
  ⟨"a later field is instantiated past the earlier ones", arr (b .linear) .shared duoTy resTy,
    lam (b .linear) (.prj 18 1 (v 0)) duoTy, "ok"⟩,
  ⟨"an instantiated field type is still checked", arr (b .linear) .shared duoTy natTy,
    lam (b .linear) (.prj 18 1 (v 0)) duoTy, "type"⟩,
  ⟨"a dependent field refers to the earlier field", arr (b .linear) .shared sigTy (.app (ref 20) (.prj 19 0 (v 0))),
    lam (b .linear) (.prj 19 1 (v 0)) sigTy, "ok"⟩,
  ⟨"a dependent field is not an arbitrary family member", arr (b .linear) .shared sigTy (.app (ref 20) zero),
    lam (b .linear) (.prj 19 1 (v 0)) sigTy, "type"⟩,
  ⟨"a projection needs the structure's own type", arr (b .linear) .shared resTy natTy,
    lam (b .linear) (.prj 18 0 (v 0)) resTy, "unsupported"⟩
]

/-- The mode program without shareable types, as under the strict profile
(strict setting S2): usage contracts never cross. Mirrors the Rust
`noshare_program`. -/
def noshareProgram : Program := { modesProgram with shareableTypes := #[] }

def noshareCases : Array Case := #[
  ⟨"without shareable types a linear value does not cross a many call", arr (b .linear),
    lam (b .linear) (call 5 (v 0)), "usage"⟩,
  ⟨"without shareable types a linear value may reach a linear callee",
    arr (b .linear .localShared) .localShared, lam (b .linear .localShared) (call 2 (v 0)), "ok"⟩,
  ⟨"without shareable types a linear capture makes a closure one-shot", arr (b .linear) .shared natTy (arr (b .many)),
    lam (b .linear) (lam (b .many) (v 1)), "capture"⟩,
  ⟨"without shareable types a unique capture read by a closure makes it one-shot",
    arr (b .linear .unique) .shared natTy (arr (b .many)),
    lam (b .linear .unique) (lam (b .many) (call 5 (v 1))), "capture"⟩,
  ⟨"without shareable types an erased proof still has no demand", arr (b .erased) .shared prfTy natTy,
    lam (b .erased) (call 14 (v 0)) prfTy, "ok"⟩
]

def boxTy : E := ref 21
def chainTy : E := ref 25
/-- `∀ (motive : T → Sort 0), …` premises over a constant motive. -/
def constMotive (t result : E) : E := lam (b .many) result t
def app4 (f a b c d : E) : E := .app (.app (.app (.app f a) b) c) d

/-- The mode program extended with case splits (`cases`), two inductive
types with recursors, a `casesOn`-style wrapper, and two more choices: one
whose alternatives receive a proof (as `dite`) and one with a leading type
argument (as `cond`). Mirrors the Rust `cases_program`. -/
def casesProgram : Program := { modesProgram with
  declarations := modesProgram.declarations ++ #[
    { type := .sort 0, kind := .typeConstructor },                            -- 21 Box
    { type := boxTy, kind := .constructor },                                  -- 22 Box.empty
    { type := arr (b .many) .shared resTy boxTy, kind := .constructor },      -- 23 Box.full
    { type := arr (b .many) .shared (arr (b .many) .shared boxTy (.sort 0))   -- 24 Box.rec
        (arr (b .many) .shared (.app (v 0) (ref 22))
          (arr (b .many) .shared (arr (b .many) .shared resTy (.app (v 2) (.app (ref 23) (v 0))))
            (arr (b .many) .shared boxTy (.app (v 3) (v 0))))),
      kind := .assumption },
    { type := .sort 0, kind := .typeConstructor },                            -- 25 Chain
    { type := chainTy, kind := .constructor },                                -- 26 Chain.stop
    { type := arr (b .many) .shared chainTy chainTy, kind := .constructor },  -- 27 Chain.link
    { type := arr (b .many) .shared (arr (b .many) .shared chainTy (.sort 0)) -- 28 Chain.rec
        (arr (b .many) .shared (.app (v 0) (ref 26))
          (arr (b .many) .shared
            (arr (b .many) .shared chainTy (arr (b .many) .shared (.app (v 2) (v 0))
              (.app (v 3) (.app (ref 27) (v 1)))))
            (arr (b .many) .shared chainTy (.app (v 3) (v 0))))),
      kind := .assumption },
    { type := arr (b .many) .shared (arr (b .many) .shared boxTy (.sort 0))   -- 29 Box.casesOn
        (arr (b .many) .shared boxTy
          (arr (b .many) .shared (.app (v 1) (ref 22))
            (arr (b .many) .shared (arr (b .many) .shared resTy (.app (v 3) (.app (ref 23) (v 0))))
              (.app (v 3) (v 2))))),
      body := some (lam (b .many) (lam (b .many) (lam (b .many) (lam (b .many)
        (app4 (ref 24) (v 3) (v 1) (lam (b .many) (.app (v 1) (v 0)) resTy) (v 2))
        (arr (b .many) .shared resTy (.app (v 3) (.app (ref 23) (v 0)))))
        (.app (v 1) (ref 22))) boxTy) (arr (b .many) .shared boxTy (.sort 0))) },
    { type := resTy, kind := .assumption },                                   -- 30 fresh Res
    { type := arr (b .many) .shared natTy                                     -- 31 proof choice
        (arr (b .many) .shared (arr (b .many) .shared prfTy resTy)
          (arr (b .many) .shared (arr (b .many) .shared prfTy resTy) resTy)),
      kind := .assumption },
    { type := arr (b .many) .shared (.sort 0) (arr (b .many) .shared natTy    -- 32 typed choice
        (arr (b .many) .shared (v 1) (arr (b .many) .shared (v 2) (v 3)))),
      kind := .assumption }
  ]
  choices := modesProgram.choices ++ #[31, 32]
  caseDefinitions := #[29]
  recursors := #[
    { index := 24, params := 0, motives := 1, minors := 2, indices := 0,
      fields := #[0, 1], binders := #[0, 1] },
    { index := 28, params := 0, motives := 1, minors := 2, indices := 0,
      fields := #[0, 1], binders := #[0, 2] } ]
  cases := true }

def resToRes (input : BinderContract) (result : ValueContract := .shared) : E :=
  arr input result resTy resTy
/-- `(r : Res) → (t : Box) → Res`, one-shot after `r`. -/
def resBoxRes (input : BinderContract) : E :=
  arr input .unique resTy (arr (b .many) .shared boxTy resTy)
def boxSplit (empty full major : E) : E :=
  app4 (ref 24) (constMotive boxTy resTy) empty full major

def caseCases : Array Case := #[
  -- Case splits over a recursor whose minors ignore their hypotheses.
  ⟨"a case split joins its alternatives", resBoxRes (b .linear),
    lam (b .linear) (lam (b .many) (boxSplit (v 1) (lam (b .many) (v 2) resTy) (v 0)) boxTy) resTy, "ok"⟩,
  ⟨"a linear value missing from one alternative", resBoxRes (b .linear),
    lam (b .linear) (lam (b .many) (boxSplit (v 1) (lam (b .many) (v 0) resTy) (v 0)) boxTy) resTy, "usage"⟩,
  ⟨"fields keep the major's locality", arr (b .many .localShared) .shared boxTy resTy,
    lam (b .many .localShared) (boxSplit (ref 30) (lam (b .many) (v 0) resTy) (v 0)) boxTy, "unrestricted"⟩,
  ⟨"a local field may return locally", arr (b .many .localShared) .localShared boxTy resTy,
    lam (b .many .localShared) (boxSplit (ref 30) (lam (b .many) (v 0) resTy) (v 0)) boxTy, "ok"⟩,
  ⟨"the major is inspected, not moved", arr (b .many .unique) .unique boxTy boxTy,
    lam (b .many .unique)
      (app4 (ref 24) (constMotive boxTy boxTy) (v 0) (lam (b .many) (v 1) resTy) (v 0)) boxTy, "ok"⟩,
  ⟨"a case split may not use an induction hypothesis", arr (b .many) .shared chainTy natTy,
    lam (b .many) (app4 (ref 28) (constMotive chainTy natTy) zero
      (lam (b .many) (lam (b .many) (v 0) natTy) chainTy) (v 0)) chainTy, "unsupported"⟩,
  ⟨"a dead induction hypothesis is ignored", arr (b .many) .shared chainTy natTy,
    lam (b .many) (app4 (ref 28) (constMotive chainTy natTy) zero
      (lam (b .many) (lam (b .many) zero natTy) chainTy) (v 0)) chainTy, "ok"⟩,
  -- Review F4: any occurrence of a hypothesis is a use.
  ⟨"a hypothesis passed to a dead binder is a use", arr (b .many) .shared chainTy natTy,
    lam (b .many) (app4 (ref 28) (constMotive chainTy natTy) zero
      (lam (b .many) (lam (b .many) (.app (lam (b .many) zero natTy) (v 0)) natTy) chainTy) (v 0)) chainTy,
    "unsupported"⟩,
  ⟨"a hypothesis in an erased argument is a use", arr (b .many) .shared chainTy natTy,
    lam (b .many) (app4 (ref 28) (constMotive chainTy natTy) zero
      (lam (b .many) (lam (b .many) (call 4 (v 0)) natTy) chainTy) (v 0)) chainTy, "unsupported"⟩,
  -- Wrappers and β-redexes.
  ⟨"a case wrapper is unfolded", resBoxRes (b .linear),
    lam (b .linear) (lam (b .many) (app4 (ref 29) (constMotive boxTy resTy) (v 0) (v 1)
      (lam (b .many) (v 2) resTy)) boxTy) resTy, "ok"⟩,
  ⟨"an unfolded wrapper still joins its alternatives", resBoxRes (b .linear),
    lam (b .linear) (lam (b .many) (app4 (ref 29) (constMotive boxTy resTy) (v 0) (v 1)
      (lam (b .many) (v 0) resTy)) boxTy) resTy, "usage"⟩,
  ⟨"a beta-redex binds a variable argument", resToRes (b .linear),
    lam (b .linear) (.app (lam (b .many) (v 0) resTy) (v 0)) resTy, "ok"⟩,
  ⟨"an annotated beta-redex keeps its binder contract", resToRes (b .linear),
    lam (b .linear) (.app (lam (b .linear) (v 0) resTy) (v 0)) resTy, "ok"⟩,
  ⟨"an affine beta-redex binder may drop a linear argument", resToRes (b .linear),
    lam (b .linear) (.app (lam (b .affine) (v 0) resTy) (v 0)) resTy, "usage"⟩,
  ⟨"a beta-redex binder still counts its uses", resToRes (b .linear),
    lam (b .linear) (.app (lam (b .linear) (ref 30) resTy) (v 0)) resTy, "usage"⟩,
  -- Generalized choices.
  ⟨"proof alternatives are entered", resToRes (b .linear),
    lam (b .linear) (.app (.app (call 31 zero) (lam (b .many) (v 1) prfTy)) (lam (b .many) (v 1) prfTy)) resTy, "ok"⟩,
  ⟨"proof alternatives still join", resToRes (b .linear),
    lam (b .linear) (.app (.app (call 31 zero) (lam (b .many) (v 1) prfTy)) (lam (b .many) (ref 30) prfTy)) resTy, "usage"⟩,
  ⟨"a typed choice selects by need", resToRes (b .linear),
    lam (b .linear) (app4 (ref 32) resTy zero (v 0) (v 0)) resTy, "ok"⟩,
  ⟨"a typed choice joins its alternatives", resToRes (b .linear),
    lam (b .linear) (app4 (ref 32) resTy zero (v 0) (ref 30)) resTy, "usage"⟩,
  ⟨"a choice takes its caller's contract", resToRes (b .linear .unique) .unique,
    lam (b .linear .unique) (app4 (ref 32) resTy zero (v 0) (v 0)) resTy, "ok"⟩,
  ⟨"a typed choice needs every argument", resToRes (b .linear),
    lam (b .linear) (.app (.app (call 32 resTy) zero) (v 0)) resTy, "unsupported"⟩
]

/-- The case program extended with `Eq` and an unfolding equation for the
definition under test (index 35): `∀ r, f r = r`. Mirrors the Rust
`equations_program`. -/
def equationsProgram : Program := { casesProgram with
  declarations := casesProgram.declarations ++ #[
    { type := arr (b .many) .shared (.sort 0)                                -- 33 Eq
        (arr (b .many) .shared (v 0) (arr (b .many) .shared (v 1) (.sort 1))),
      kind := .typeConstructor },
    { type := arr (b .many) .shared resTy                                    -- 34 ∀ r, f r = r
        (.app (.app (.app (ref 33) resTy) (.app (ref 35) (v 0))) (v 0)),
      body := some (lam (b .many) (ref 30) resTy), kind := .theorem }
  ]
  eqType := some 33
  equations := #[(35, 34)] }

def equationCases : Array Case := #[
  ⟨"a definition is checked through its unfolding equation", resToRes (b .linear),
    lam (b .linear) (ref 30) resTy, "ok"⟩,
  ⟨"an unfolding equation keeps the definition's contracts", resToRes (b .erased),
    lam (b .erased) (ref 30) resTy, "usage"⟩
]

/-- The case program with `Box` as an addressed block (type and
constructors), so that it is plain data. Mirrors the Rust `freeze_program`. -/
def freezeProgram : Program := { casesProgram with groups := #[#[21, 22, 23]] }

def freezeCases : Array Case := #[
  -- Freeze: a unique plain value enters a shared position as its last use.
  ⟨"a unique plain value may be shared as its last use", arr (b .many .unique) .shared boxTy boxTy,
    lam (b .many .unique) (v 0) boxTy, "ok"⟩,
  ⟨"a frozen value cannot be used again", arr (b .many .unique) .shared boxTy boxTy,
    lam (b .many .unique) (bind (b .affine) (v 0) (v 1) boxTy) boxTy, "moved"⟩,
  ⟨"a frozen value cannot be moved as unique", arr (b .many .unique) .unique boxTy boxTy,
    lam (b .many .unique) (bind (b .affine) (v 0) (v 1) boxTy) boxTy, "moved"⟩,
  ⟨"a unique value of an abstract type is not frozen", arr (b .many .unique) .shared resTy resTy,
    lam (b .many .unique) (v 0) resTy, "capture"⟩,
  -- Fresh constructor results are unique.
  ⟨"a fresh constructor result is unique", arr (b .many) .unique resTy boxTy,
    lam (b .many) (call 23 (v 0)) resTy, "ok"⟩,
  ⟨"a fresh nullary constructor is unique", arr (b .many) .unique resTy boxTy,
    lam (b .many) (ref 22) resTy, "ok"⟩,
  ⟨"a constructor as a function value is not fresh", arr (b .many) .unique resTy (arr (b .many) .shared resTy boxTy),
    lam (b .many) (ref 23) resTy, "ownership"⟩,
  -- Literals and closed constructions are static data, shared (strict
  -- setting S1); a construction is fresh only through a run-time local.
  ⟨"a literal is shared, not fresh", arr (b .many) .unique resTy natTy,
    lam (b .many) zero resTy, "ownership"⟩,
  ⟨"a string literal is shared, not fresh", arr (b .many) .unique resTy natTy,
    lam (b .many) (.str 0) resTy, "ownership"⟩,
  ⟨"a literal fills a shared position", arr (b .many) .shared resTy natTy,
    lam (b .many) zero resTy, "ok"⟩,
  ⟨"a closed constructor application is static, not fresh", arr (b .many) .unique resTy boxTy,
    lam (b .many) (call 23 (ref 30)) resTy, "ownership"⟩,
  ⟨"a field computed from a run-time local makes a construction fresh", arr (b .many) .unique resTy boxTy,
    lam (b .many) (call 23 (call 12 (v 0))) resTy, "ok"⟩,
  ⟨"a one-field constructor of a type without a known block is not fresh",
    arr (b .many) .unique chainTy chainTy, lam (b .many) (call 27 (v 0)) chainTy, "ownership"⟩,
  -- Plain-data owners can be borrowed.
  ⟨"a plain-data owner may be borrowed", arr (b .linear .unique) .unique boxTy boxTy,
    lam (b .linear .unique) (bind (b .affine) (borrow (v 0) (ref 30) .many boxTy) (v 1) resTy) boxTy, "ok"⟩,
  ⟨"a borrowed plain-data owner cannot move during the loan", arr (b .linear .unique) .unique boxTy boxTy,
    lam (b .linear .unique) (borrow (v 0) (v 1) .many boxTy) boxTy, "loan"⟩
]

/-- The case program with plain-data crossing, as under the plain profile
(setting S6): `Box` and `Chain` are addressed blocks (plain data), `Chain` is
opted out (`linear`), with a many and a unique `Box` consumer. Mirrors the
Rust `plain_program`. -/
def plainProgram : Program := { casesProgram with
  declarations := casesProgram.declarations ++ #[
    { type := arr (b .many) .shared boxTy natTy, kind := .assumption },             -- 33 useBox
    { type := arr (b .many .unique) .unique boxTy boxTy, kind := .assumption } ]    -- 34 keepBox
  groups := #[#[21, 22, 23], #[25, 26, 27]]
  crossing := true
  linearTypes := #[25] }

def natToNat : E := arr (b .many) .shared natTy natTy

def plainCases : Array Case := #[
  -- Usage crosses on plain data: both bounds of a written `1`/`&` dropped.
  ⟨"a linear plain-data value crosses a many call", arr (b .linear) .shared boxTy natTy,
    lam (b .linear) (call 33 (v 0)) boxTy, "ok"⟩,
  ⟨"a dropped linear plain-data value is not enforced", arr (b .linear) .shared boxTy natTy,
    lam (b .linear) zero boxTy, "ok"⟩,
  ⟨"an affine plain-data value may be used twice", arr (b .affine) .shared boxTy natTy,
    lam (b .affine) (.app (.app (ref 15) (call 33 (v 0))) (call 33 (v 0))) boxTy, "ok"⟩,
  ⟨"a linear plain-data capture keeps a closure reusable", arr (b .linear) .shared boxTy natToNat,
    lam (b .linear) (lam (b .many) (call 33 (v 1))) boxTy, "ok"⟩,
  -- Usage is enforced on everything else.
  ⟨"a linear value of a type without a visible block does not cross", arr (b .linear) .shared resTy resTy,
    lam (b .linear) (call 12 (v 0)) resTy, "usage"⟩,
  ⟨"a linear function does not cross", arr (b .linear) .shared natToNat natTy,
    lam (b .linear) (.app (.app (ref 15) (.app (v 0) zero)) (.app (v 0) zero)) natToNat, "usage"⟩,
  ⟨"an opted-out plain-data type does not cross", arr (b .linear) .shared chainTy natTy,
    lam (b .linear) zero chainTy, "usage"⟩,
  ⟨"an erased plain-data binder stays erased", arr (b .erased) .shared boxTy natTy,
    lam (b .erased) (call 33 (v 0)) boxTy, "usage"⟩,
  -- Ownership does not cross.
  ⟨"a unique plain-data capture moved by a closure still makes it one-shot",
    arr (b .many .unique) .shared boxTy (arr (b .many) .unique natTy boxTy),
    lam (b .many .unique) (lam (b .many) (call 34 (v 1))) boxTy, "capture"⟩,
  ⟨"a unique plain-data value still moves once", arr (b .many .unique) .shared boxTy natTy,
    lam (b .many .unique) (.app (.app (ref 15) (call 33 (call 34 (v 0)))) (call 33 (call 34 (v 0))))
      boxTy, "moved"⟩
]

/-- The diagnostic: plain-data crossing reports the binders whose `1`/`&`
contract it did not enforce (a header binder by its position). -/
def checkCrossedBinders : IO Unit := do
  let reported (type value : E) : Except Error (Array OwnerId) :=
    let p := { plainProgram with declarations := plainProgram.declarations.push { type, body := some value } }
    checkDefinitionCrossed p plainProgram.declarations.size
  let dropped := reported (arr (b .linear) .shared boxTy natTy) (lam (b .linear) zero boxTy)
  let enforced := reported (arr (b .many) .shared boxTy natTy) (lam (b .many) zero boxTy)
  let tested : Declaration :=
    { type := arr (b .linear) .shared boxTy natTy, body := some (lam (b .linear) (call 33 (v 0)) boxTy) }
  let withoutCrossing : Program :=
    { plainProgram with crossing := false, declarations := plainProgram.declarations.push tested }
  let strict := checkDefinitionCrossed withoutCrossing plainProgram.declarations.size
  unless dropped.toOption == some #[0] && enforced.toOption == some #[] && strict.toOption.isNone do
    throw <| IO.userError s!"plain-data crossing diagnostic differs: {repr dropped}, {repr enforced}, {repr strict}"

def app3 (f a b c : E) : E := .app (.app (.app f a) b) c
/-- `(t : Box) → (e : Nat → Res) → (f : Res → Res) → Res`, a matcher shape. -/
def matcherTy : E :=
  arr (b .many) .shared boxTy (arr (b .many) .shared (arr (b .many) .shared natTy resTy)
    (arr (b .many) .shared (arr (b .many) .shared resTy resTy) resTy))
/-- `fun t e f => Box.casesOn motive t (e 0) (fun r => f r)`. -/
def matcherBody : E :=
  lam (b .many) (lam (b .many) (lam (b .many)
    (app4 (ref 29) (constMotive boxTy resTy) (v 2) (.app (v 1) zero) (lam (b .many) (.app (v 1) (v 0)) resTy))
    (arr (b .many) .shared resTy resTy)) (arr (b .many) .shared natTy resTy)) boxTy

/-- The case program extended for strict binding (review F1): a unique
consumer, a match-shaped definition that is not bound, and a matcher-shaped
definition that is bound (35) next to an unbound copy (36). Mirrors the Rust
`strict_program`. -/
def strictProgram : Program := { casesProgram with
  declarations := casesProgram.declarations ++ #[
    { type := arr (b .linear .unique) .shared resTy resTy, kind := .assumption }, -- 33 take
    { type := arr (b .many) .shared boxTy (arr (b .many) .shared resTy           -- 34 sel t e f
        (arr (b .many) .shared resTy resTy)),
      body := some (lam (b .many) (lam (b .many) (lam (b .many)
        (app4 (ref 24) (constMotive boxTy resTy) (v 1) (lam (b .many) (v 1) resTy) (v 2))
        resTy) resTy) boxTy) },
    { type := matcherTy, body := some matcherBody },                             -- 35 bound matcher
    { type := matcherTy, body := some matcherBody }                              -- 36 unbound copy
  ]
  caseDefinitions := #[29, 35] }

/-- `(1 ! r : Res) → (t : Box) → Res` with body `x` over `t` (0) and `r` (1). -/
def uniqueBox (x : E) : E := lam (b .linear .unique) (lam (b .many) x boxTy) resTy

def strictCases : Array Case := #[
  -- Ordinary calls and β-redexes evaluate every argument once, before the body.
  ⟨"an unbound match-shaped definition is an ordinary call", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 34) (v 0) (call 33 (v 1)) (v 1)), "moved"⟩,
  ⟨"a bound case definition takes its alternatives by need", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 35) (v 0) (lam (b .many) (call 33 (v 2)) natTy)
      (lam (b .many) (call 33 (v 2)) resTy)), "ok"⟩,
  ⟨"an unbound copy of a case definition takes closures", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 36) (v 0) (lam (b .many) (call 33 (v 2)) natTy)
      (lam (b .many) (call 33 (v 2)) resTy)), "capture"⟩,
  ⟨"a dead beta-redex argument is still evaluated", resToRes (b .linear .unique) .unique,
    lam (b .linear .unique) (.app (lam (b .many) (v 1) resTy) (call 33 (v 0))) resTy, "moved"⟩,
  ⟨"a beta-redex argument is not re-evaluated under a closure", arr (b .many) .unique natTy boxTy,
    .app (lam (b .many) (lam (b .many) (v 1) natTy) boxTy) (ref 22), "capture"⟩,
  ⟨"a closure argument is built once, before the body", resToRes (b .linear .unique) .unique,
    lam (b .linear .unique) (.app (lam (b .many) (v 1) (arr (b .many) .shared natTy resTy))
      (lam (b .many) (call 33 (v 1)) natTy)) resTy, "capture"⟩,
  ⟨"a closed lambda argument is substituted", resToRes (b .linear .unique) .unique,
    lam (b .linear .unique) (.app (lam (b .many) (.app (v 0) (v 1)) (arr (b .many) .shared resTy resTy))
      (lam (b .many) (v 0) resTy)) resTy, "ok"⟩
]

/-- Evaluation-order regressions (R2-7); kept separate so the field-fixture
indices below do not move. `37` consumes an owner to produce a one-shot thunk. -/
def orderProgram : Program := { strictProgram with
  declarations := strictProgram.declarations ++ #[{
    type := arr (b .linear .unique) .unique resTy (arr (b .many) .shared natTy resTy)
    kind := .assumption }, -- 37 thunk producer
    { type := arr (b .linear .unique) .unique resTy (arr (b .many) .shared resTy resTy)
      kind := .assumption }, -- 38 field-alternative producer
    { type := strictProgram.declarations[29]!.type,
      body := some (lam (b .many) (lam (b .many) (lam (b .many) (lam (b .many)
        (app4 (ref 24) (v 3) (v 1) (v 0) (v 2))
        (arr (b .many) .shared resTy (.app (v 3) (.app (ref 23) (v 0)))))
        (.app (v 1) (ref 22))) boxTy) (arr (b .many) .shared boxTy (.sort 0))) }, -- 39 bare minor
    { type := strictProgram.declarations[29]!.type,
      body := some (lam (b .many) (lam (b .many) (lam (b .many) (lam (b .many)
        (app4 (ref 39) (v 3) (v 2) (v 1) (v 0))
        (arr (b .many) .shared resTy (.app (v 3) (.app (ref 23) (v 0)))))
        (.app (v 1) (ref 22))) boxTy) (arr (b .many) .shared boxTy (.sort 0))) } -- 40 nested bare minor
  ]
  caseDefinitions := strictProgram.caseDefinitions ++ #[39, 40] }

def orderFnTy : E := arr (b .linear) .shared resTy resTy
def orderId : E := lam (b .linear) (v 0) resTy
def orderBox (x : E) : E := lam (b .linear) (lam (b .many) x boxTy) resTy
def orderCase (wrapper : Bool) : E :=
  let motive := constMotive boxTy orderFnTy
  let full := lam (b .many) orderId resTy
  if wrapper then app4 (ref 29) motive (v 0) orderId full
  else app4 (ref 24) motive orderId full (v 0)

def bareMinorCase (wrapper : UInt64) (computed : Bool) : E :=
  let empty := .app (lam (b .many) (call 33 (v 2)) natTy) zero
  let full := if computed then .app (lam (b .many) (call 38 (v 2)) natTy) zero
    else lam (b .many) (call 33 (v 2)) resTy
  uniqueBox (app4 (ref wrapper) (constMotive boxTy resTy) (v 0) empty full)

def orderCases : Array Case := #[
  ⟨"a computation returning a matcher thunk is strict", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 35) (v 0) (call 37 (v 1))
      (lam (b .many) (call 33 (v 2)) resTy)), "capture"⟩,
  ⟨"a beta-wrapped computation returning a matcher thunk is strict", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 35) (v 0) (.app (lam (b .many) (call 37 (v 2)) natTy) zero)
      (lam (b .many) (call 33 (v 2)) resTy)), "capture"⟩,
  ⟨"a let-wrapped computation returning a matcher thunk is strict", resBoxRes (b .linear .unique),
    uniqueBox (app3 (ref 35) (v 0) (bind (b .many) zero (call 37 (v 2)) natTy)
      (lam (b .many) (call 33 (v 2)) resTy)), "capture"⟩,
  ⟨"a case over-application rejects a computed argument", resBoxRes (b .linear .unique),
    uniqueBox (.app (orderCase false) (call 33 (v 1))), "unsupported"⟩,
  ⟨"a case over-application accepts a value argument", resBoxRes (b .linear),
    orderBox (.app (orderCase false) (v 1)), "ok"⟩,
  ⟨"a bound case over-application rejects a computed argument", resBoxRes (b .linear .unique),
    uniqueBox (.app (orderCase true) (call 33 (v 1))), "unsupported"⟩,
  ⟨"a bound case over-application accepts a value argument", resBoxRes (b .linear),
    orderBox (.app (orderCase true) (v 1)), "ok"⟩,
  ⟨"a choice over-application rejects a computed argument", resToRes (b .linear .unique),
    lam (b .linear .unique) (.app (app4 (ref 32) orderFnTy zero orderId orderId)
      (call 33 (v 0))) resTy, "unsupported"⟩,
  ⟨"a choice over-application accepts a value argument", resToRes (b .linear),
    lam (b .linear) (.app (app4 (ref 32) orderFnTy zero orderId orderId)
      (v 0)) resTy, "ok"⟩,
  ⟨"an eta-unexpanded field minor still requires an alternative", resBoxRes (b .linear .unique),
    bareMinorCase 39 true, "capture"⟩,
  ⟨"a nested eta-unexpanded field minor still requires an alternative", resBoxRes (b .linear .unique),
    bareMinorCase 40 true, "capture"⟩,
  ⟨"an eta-unexpanded field minor accepts a lambda alternative", resBoxRes (b .linear .unique),
    bareMinorCase 39 false, "ok"⟩,
  ⟨"a nested eta-unexpanded field minor accepts a lambda alternative", resBoxRes (b .linear .unique),
    bareMinorCase 40 false, "ok"⟩
]

def uboxTy : E := ref 39

/-- The strict program extended for case-split fields (review F5) and joins
(F6): a unique consumer of `Box`, a binary consumer of `Res`, and `UBox`,
whose only constructor has a unique field. Mirrors the Rust `field_program`. -/
def fieldProgram : Program := { strictProgram with
  declarations := strictProgram.declarations ++ #[
    { type := arr (b .linear .unique) .shared boxTy resTy, kind := .assumption }, -- 37 takeBox
    { type := arr (b .many) .shared resTy (arr (b .many) .shared resTy resTy),     -- 38 pairR
      kind := .assumption },
    { type := .sort 0, kind := .typeConstructor },                               -- 39 UBox
    { type := arr (b .many .unique) .shared resTy uboxTy, kind := .constructor }, -- 40 UBox.mk
    { type := arr (b .many) .shared (arr (b .many) .shared uboxTy (.sort 0))     -- 41 UBox.rec
        (arr (b .many) .shared (arr (b .many .unique) .shared resTy (.app (v 1) (.app (ref 40) (v 0))))
          (arr (b .many) .shared uboxTy (.app (v 2) (v 0)))),
      kind := .assumption }
  ]
  recursors := strictProgram.recursors.push
    { index := 41, params := 0, motives := 1, minors := 1, indices := 0, fields := #[1], binders := #[1] } }

/-- `(! b : Box) → Res` splitting `b`: `Box.rec motive fresh (fun r => full) b`. -/
def splitBox (full : E) : E :=
  lam (b .many .unique) (app4 (ref 24) (constMotive boxTy resTy) (ref 30) (lam (b .many) full resTy) (v 0)) boxTy

def fieldCases : Array Case := #[
  -- Review F5: a case-split field is a view of the major.
  ⟨"a field is unusable after its major is moved", arr (b .many .unique) .shared boxTy resTy,
    splitBox (.app (.app (ref 38) (call 37 (v 1))) (v 0)), "moved"⟩,
  ⟨"consuming a field shares its major", arr (b .many .unique) .shared boxTy resTy,
    splitBox (.app (.app (ref 38) (v 0)) (call 37 (v 1))), "ownership"⟩,
  ⟨"a field may be used while its major is live", arr (b .many .unique) .shared boxTy resTy,
    splitBox (v 0), "ok"⟩,
  ⟨"a case split on a field with a contract has no rule", arr (b .many) .shared uboxTy resTy,
    lam (b .many) (.app (.app (.app (ref 41) (constMotive uboxTy resTy)) (lam (b .many) (v 0) resTy)) (v 0))
      uboxTy, "unsupported"⟩,
  -- Review F6: a join with no expected contract keeps every owner. The split
  -- returns `p1` or `p2` under a projection (no contract); moving its unique
  -- field moves both, so `p1` cannot be moved again.
  ⟨"a join without a contract keeps every owner", arr (b .many .unique) .shared pairTy
      (arr (b .many .unique) .shared pairTy (arr (b .many) .shared boxTy natTy)),
    lam (b .many .unique) (lam (b .many .unique) (lam (b .many)
      (.app (.app (ref 15)
        (call 3 (.prj 7 0 (app4 (ref 24) (constMotive boxTy pairTy) (v 2) (lam (b .many) (v 2) resTy) (v 0)))))
        (call 3 (.prj 7 0 (v 2))))
      boxTy) pairTy) pairTy, "moved"⟩
]

def runCaseIn (base : Program) (type value : E) (limits : Limits := {}) : Except Error Unit :=
  let p := { base with declarations := base.declarations.push { type, body := some value } }
  checkDefinition p base.declarations.size limits

def runFixtureFile (path : String) (base : Program) (tests : Array Case) : IO Nat := do
  let file ← IO.FS.readFile path
  let lines := file.splitOn "\n"
  let mut missing := #[]
  for test in tests do
    let actual := runCaseIn base test.type test.value
    let code := match actual with | .ok _ => "ok" | .error e => errorCode e
    unless code == test.expected do
      throw <| IO.userError s!"resource: {test.name}: expected {test.expected}, got {repr actual}"
    let line := fixtureLine test
    unless lines.contains line do missing := missing.push line
  unless missing.isEmpty do
    throw <| IO.userError s!"resource fixture bytes differ in {path}; expected lines:\n{"\n".intercalate missing.toList}"
  return tests.size

def checkOrderShapes : IO Unit := do
  for (index, expected) in [(29, #[none, none, some 0, some 1]),
      (35, #[none, some 1, some 1]),
      (39, #[none, none, some 0, some 1]),
      (40, #[none, none, some 0, some 1])] do
    match (caseDefinition orderProgram 256 4 index).run { remaining := 100000 } with
    | .ok (some shape) _ =>
      unless shape.byNeed == expected do
        throw <| IO.userError s!"case {index}: unexpected by-need counts {repr shape.byNeed}"
    | _ => throw <| IO.userError s!"case {index}: shape was not derived"

def runFixtureCases : IO Nat := do
  let base ← runFixtureFile "Tests/Fixtures/ixon-v4/resource.tsv" program allCases
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/resource.tsv") == fixtureText do
    throw <| IO.userError "resource fixture differs from its producer; regenerate it with \
      `lake exe ixon-v4-tests --export-fixtures`"
  let modes ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-modes.tsv" modesProgram modeCases
  let cases ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-cases.tsv" casesProgram caseCases
  let equations ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-equations.tsv" equationsProgram equationCases
  let freeze ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-freeze.tsv" freezeProgram freezeCases
  let strict ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-strict.tsv" strictProgram strictCases
  let order ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-order.tsv" orderProgram orderCases
  let fields ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-fields.tsv" fieldProgram fieldCases
  let noshare ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-noshare.tsv" noshareProgram noshareCases
  let plain ← runFixtureFile "Tests/Fixtures/ixon-v4/resource-plain.tsv" plainProgram plainCases
  checkCrossedBinders
  checkOrderShapes
  return base + modes + cases + equations + freeze + strict + order + fields + noshare + plain + 2

def runContractMatrix : IO Nat := do
  let mut checks := 0
  for code in [0:16] do
    let some input := BinderContract.ofBits? code.toUInt8
      | throw <| IO.userError "invalid generated input code"
    for resultCode in [0:4] do
      let some result := ValueContract.ofBits? resultCode.toUInt8
        | throw <| IO.userError "invalid generated result code"
      let body := if input.uses == .erased then zero else v 0
      -- An erased input leaves the literal `0`, which is shared: it satisfies
      -- every shared result and no unique one.
      let allowed := if input.uses == .erased then result.owned == .shared else
        ((input.value.owned == .unique || result.owned == .shared) &&
         (input.value.locality == .unrestricted || result.locality == .local))
      unless (runCase (arr input result) (lam input body)).toOption.isSome == allowed do
        throw <| IO.userError s!"resource contract matrix differs at {code}/{resultCode}"
      checks := checks + 1
  return checks

/-- Budget exhaustion is an error, including cycles through open sharing. -/
def checkSharingBudget : IO Unit := do
  let cyclic := { program with sharing := #[.share 0] }
  let action := analyze 20 { program := cyclic } (.share 0) none 0 .linear
  match action.run {} with
  | .error .budget _ => pure ()
  | _ => throw <| IO.userError "cyclic sharing did not exhaust the bound"

def run : IO Unit := do
  let fixtures ← runFixtureCases
  let matrix ← runContractMatrix
  checkSharingBudget
  IO.println s!"Resource checker: {fixtures + matrix + 1} positive/negative and mode checks passed"

end Tests.Resource

end
