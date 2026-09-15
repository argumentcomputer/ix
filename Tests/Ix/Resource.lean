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
  ⟨"ordinary identity", arr (b .many), lam (b .many) (v 0), "ok"⟩,
  ⟨"linear identity", arr (b .linear), lam (b .linear) (v 0), "ok"⟩,
  ⟨"linear unique transfer", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (v 0), "ok"⟩,
  ⟨"unused erased", arr (b .erased), lam (b .erased) zero, "ok"⟩,
  ⟨"erased argument has zero demand", arr (b .erased),
    lam (b .erased) (call 4 (v 0)), "ok"⟩,
  ⟨"unused affine", arr (b .affine), lam (b .affine) zero, "ok"⟩,
  ⟨"missing linear consumption", arr (b .linear), lam (b .linear) zero, "usage"⟩,
  ⟨"runtime erased variable", arr (b .erased), lam (b .erased) (v 0), "usage"⟩,
  ⟨"many invocation scales demand", arr (b .affine), lam (b .affine) (call 5 (v 0)), "usage"⟩,
  ⟨"many permits repeated demand", arr (b .many), lam (b .many) (call 5 (v 0)), "ok"⟩,
  ⟨"linear ordinary let", arr (b .linear),
    lam (b .linear) (bind (b .linear) (v 0) (v 0)), "ok"⟩,
  ⟨"erased let initializer", arr (b .linear),
    lam (b .linear) (bind (b .erased) (v 0) (v 1)), "ok"⟩,
  ⟨"duplicate affine through let", arr (b .affine),
    lam (b .affine) (bind (b .affine) (v 0) (v 1)), "usage"⟩,
  ⟨"shared cannot become unique", arr (b .linear) .unique,
    lam (b .linear) (v 0), "ownership"⟩,
  ⟨"unique cannot transfer twice despite many", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .linear .unique) (v 0)
      (bind (b .linear .unique) (v 1) (v 0))), "moved"⟩,
  ⟨"permanent sharing relinquishes unique", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .affine) (v 0) (v 1)), "ownership"⟩,
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
  ⟨"unregistered projection has no optimistic rule", arr (b .many .unique),
    lam (b .many .unique) (.prj 0 0 (v 0)), "unsupported"⟩,
  ⟨"shared closure cannot hide affine capture", arr (b .affine) .shared natTy (closureType .shared),
    lam (b .affine) (lam (b .many) (v 1)), "capture"⟩,
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
  ⟨"linear use in both alternatives", arr (b .linear),
    lam (b .linear) (choose 6 (v 0) (v 0)), "ok"⟩,
  ⟨"linear missing in one alternative", arr (b .linear),
    lam (b .linear) (choose 6 (v 0) zero), "usage"⟩,
  ⟨"affine use in one alternative", arr (b .affine),
    lam (b .affine) (choose 6 (v 0) zero), "ok"⟩,
  ⟨"unique move in each alternative", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (choose 10 (v 0) (v 0)), "ok"⟩,
  ⟨"alternative move prevents later use", arr (b .many .unique) .unique,
    lam (b .many .unique) (bind (b .affine .unique) (choose 10 (v 0) zero) (v 1)), "moved"⟩,
  ⟨"partial selection is not an ordinary function", arr (b .many),
    lam (b .many) (call 6 (v 0)), "unsupported"⟩,
  ⟨"sharing checked in live binder context", arr (b .linear),
    lam (b .linear) (.share 0), "ok"⟩,
  ⟨"sharing cannot cache away erased restriction", arr (b .erased),
    lam (b .erased) (.share 0), "usage"⟩,
  ⟨"lambda and interface input must agree", arr (b .linear),
    lam (b .many) (v 0), "binder"⟩,
  ⟨"fresh inner linear binder under many demand", arr (b .many),
    lam (b .many) (call 5 (bind (b .linear) (v 0) (v 0))), "ok"⟩,
  ⟨"discarding borrow before narrowing fresh result", arr (b .many .unique) .localShared,
    lam (b .many .unique) (borrow (v 0) (call 1 (v 0))), "ok"⟩,
  ⟨"type formation has zero runtime demand", arr (b .erased) .shared (.sort 0) (.sort 0),
    lam (b .erased) (v 0) (.sort 0), "ok"⟩,
  ⟨"type use cannot discharge linear runtime obligation", arr (b .linear) .shared (.sort 0) (.sort 0),
    lam (b .linear) (v 0) (.sort 0), "usage"⟩,
  ⟨"selection cannot bypass its rule through a callback", arr (b .many) .shared natTy (choiceType .shared),
    lam (b .many) (ref 6), "unsupported"⟩,
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
  ⟨"branch analysis follows a shared application head", arr (b .linear),
    lam (b .linear) (.app (.app (.app (.share 1) zero) (v 0)) (v 0)), "ok"⟩,
  ⟨"erased owner cannot be restored through a borrow", arr (b .erased .unique),
    lam (b .erased .unique) (borrow (v 0) (call 1 (v 0))), "unsupported"⟩,
  ⟨"erased view cannot be restored through a reborrow", arr (b .many .unique),
    lam (b .many .unique) (borrow (v 0) (borrow (v 0) (call 1 (v 0))) .erased), "unsupported"⟩,
  ⟨"erased higher order argument still checks its contracts", arr (b .erased) .shared (arr (b .linear)) natTy,
    lam (b .erased) (.app (lam (b .erased) zero (arr (b .many))) (v 0)) (arr (b .linear)), "type"⟩,
  ⟨"erased higher order argument with matching interface", arr (b .erased) .shared (arr (b .many)) natTy,
    lam (b .erased) (.app (lam (b .erased) zero (arr (b .many))) (v 0)) (arr (b .many)), "ok"⟩,
  ⟨"reborrowing closure captures the view without moving its root", arr (b .linear .unique) .unique,
    lam (b .linear .unique) (scopedRead
      (bind (b .linear .localShared)
        (lam (b .many) (borrow (v 1) (call 1 (v 0))))
        (.app (v 0) zero) (closureType .shared))), "ok"⟩
]

def additionalCases : Array Case := Id.run do
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

def allCases : Array Case := cases ++ additionalCases

def run : IO Unit := do
  let file ← IO.FS.readFile "Tests/Fixtures/ixon-v3/resource.tsv"
  for test in allCases do
    let actual := runCase test.type test.value
    let code := match actual with | .ok _ => "ok" | .error e => errorCode e
    unless code == test.expected do
      throw <| IO.userError s!"resource: {test.name}: expected {test.expected}, got {repr actual}"
    let line := s!"{test.name}\t{test.expected}\t{hexOfBytes (runPut (putExpr test.type))}\t{hexOfBytes (runPut (putExpr test.value))}"
    unless (file.splitOn "\n").contains line do
      throw <| IO.userError s!"resource fixture bytes differ: {test.name}"
  for code in [0:16] do
    let some input := BinderContract.ofBits? code.toUInt8
      | throw <| IO.userError "invalid generated input code"
    for resultCode in [0:4] do
      let some result := ValueContract.ofBits? resultCode.toUInt8
        | throw <| IO.userError "invalid generated result code"
      let body := if input.uses == .erased then zero else v 0
      let allowed := input.uses == .erased ||
        ((input.value.owned == .unique || result.owned == .shared) &&
         (input.value.locality == .unrestricted || result.locality == .local))
      unless (runCase (arr input result) (lam input body)).toOption.isSome == allowed do
        throw <| IO.userError s!"resource contract matrix differs at {code}/{resultCode}"
  -- Budget exhaustion is an error, including cycles through open sharing.
  let cyclic := { program with sharing := #[.share 0] }
  let action := analyze 20 { program := cyclic } (.share 0) none 0 .linear
  match action.run {} with
  | .error .budget _ => pure ()
  | _ => throw <| IO.userError "cyclic sharing did not exhaust the bound"
  IO.println s!"Resource checker: {allCases.size + 65} positive/negative and mode checks passed"

end Tests.Resource

end
