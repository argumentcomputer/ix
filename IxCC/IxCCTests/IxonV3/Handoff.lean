import IxCC.Ixon.V3.Source
import IxCC.Ixon.V3.Validate
import IxCC.Tools.Check

namespace IxCCTests.IxonV3

open IxCC.Ixon IxCC.Ixon.V3

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError message)

def handoff (root : System.FilePath) : IO Nat := do
  let directory := root / "handoff"
  let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (directory / "manifest.json")))
  let string := fun (key : String) => IO.ofExcept (manifest.getObjValAs? String key)
  let files ← IO.ofExcept (manifest.getObjVal? "files")
  for name in #["accepted.ixe", "rejected-local-escape.ixe", "profile.bin", "accepted.claim"] do
    let expected ← IO.ofExcept (files.getObjValAs? String name)
    require ((Address.blake3 (← IO.FS.readBinFile (directory / name))).toHex == expected)
      s!"handoff fixture hash differs: {name}"
  let bytes ← IO.FS.readBinFile (directory / "accepted.ixe")
  let profile ← IO.FS.readBinFile (directory / "profile.bin")
  let claimBytes ← IO.FS.readBinFile (directory / "accepted.claim")
  let input ← IO.ofExcept (admitResources bytes profile)
  require (input.env.root.toHex == (← string "subject")) "handoff subject differs"
  require (input.resolved.profileAddress.toHex == (← string "profile")) "handoff profile differs"
  require (input.profile.bytes == profile) "profile did not reencode exactly"
  IO.ofExcept (input.checkClaimBinding claimBytes)
  let claim ← IO.ofExcept (ResourceClaim.decode claimBytes)
  require (claim.bytes == claimBytes) "resource claim did not reencode exactly"
  require ((Address.blake3 claimBytes).toHex == (← string "claim")) "claim digest differs"
  let rejected ← IO.FS.readBinFile (directory / "rejected-local-escape.ixe")
  let rejectedEnv ← IO.ofExcept (decodeAnonymousEnv rejected)
  require (rejectedEnv.root != input.env.root) "changed contract retained the old subject"
  let failure := admitResources rejected profile
  require (failure.toOption.isNone) "accepted local escape"
  match failure with
  | .error error => require ((error.splitOn "unrestrictedEscape").length > 1) s!"wrong local-escape rejection: {error}"
  | .ok _ => pure ()
  require ((input.checkClaimBinding { claim with subject := rejectedEnv.root }.bytes).toOption.isNone)
    "accepted wrong claim subject"
  require ((input.checkClaimBinding { claim with profile := input.env.root }.bytes).toOption.isNone)
    "accepted wrong claim profile"
  require ((decodeAnonymousEnv (bytes.set! 0 0xE3)).toOption.isNone) "accepted v3 environment"
  require ((decodeAnonymousEnv (bytes.set! 1 (bytes[1]! ^^^ 1))).toOption.isNone) "accepted corrupt root"
  require ((decodeAnonymousEnv bytes (bytes.size - 1)).toOption.isNone) "ignored environment byte budget"
  require ((decodeAnonymousEnv (bytes.set! 180 (bytes[180]! ^^^ 1))).toOption.isNone) "accepted corrupt object"
  let raised := { input.profile with limits := { depth := 256, steps := 500000 } }
  let raisedInput ← IO.ofExcept (admitResources bytes raised.bytes)
  require (raisedInput.env.root == input.env.root && raisedInput.profile.bytes == raised.bytes)
    "500k admission changed the source or profile"
  require (raisedInput.resolved.profileAddress == Address.blake3 raised.bytes &&
      raisedInput.resolved.profileAddress != input.resolved.profileAddress)
    "500k profile did not receive its own address"
  match raisedInput.checkClaimBinding claimBytes with
  | .error error =>
    require (error == "ixon-v3: claim profile mismatch")
      s!"wrong old-profile claim rejection: {error}"
  | .ok _ => throw (IO.userError "accepted the old claim under the 500k profile")
  match admitResources rejected raised.bytes with
  | .error error =>
    require ((error.splitOn "unrestrictedEscape").length > 1)
      s!"wrong 500k local-escape rejection: {error}"
  | .ok _ => throw (IO.userError "accepted local escape under the 500k profile")
  let excessiveLimits : Array (String × Resource.Limits) := #[
    ("original depth", { depth := 257, steps := 100000 }),
    ("raised depth", { depth := 257, steps := 500000 }),
    ("steps", { depth := 256, steps := 500001 })]
  for (label, limits) in excessiveLimits do
    let excessive := { input.profile with limits }
    match admitResources bytes excessive.bytes with
    | .error error =>
      require (error == "ixon-v3: profile exceeds consumer checker budget")
        s!"wrong consumer {label} budget rejection: {error}"
    | .ok _ => throw (IO.userError s!"ignored consumer {label} checker budget")
  let mut assertions := 25
  for count in [:(bytes.size - input.env.metadata.size)] do
    require ((decodeAnonymousEnv (bytes.extract 0 count)).toOption.isNone) "accepted truncated anonymous environment"
    assertions := assertions + 1
  for count in [:claimBytes.size] do
    require ((ResourceClaim.decode (claimBytes.extract 0 count)).toOption.isNone) "accepted truncated claim"
    assertions := assertions + 1
  for count in [:profile.size] do
    require ((Resource.Profile.ofBytes (profile.extract 0 count)).toOption.isNone) "accepted truncated profile"
    assertions := assertions + 1
  for bad in #[claimBytes.push 0, claimBytes.set! 2 2, claimBytes.set! 3 1, claimBytes.set! 0 0xF6] do
    require ((ResourceClaim.decode bad).toOption.isNone) "accepted malformed or differently scoped claim"
    assertions := assertions + 1
  require ((Resource.Profile.ofBytes (profile.push 0)).toOption.isNone) "accepted trailing profile byte"
  require ((Resource.Profile.ofBytes (profile.set! 0 0)).toOption.isNone) "accepted wrong profile domain"
  for line in (← IO.FS.readFile (root / "addressed.tsv")).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [name, address, encoded] := line.splitOn "\t"
      | throw (IO.userError "invalid addressed fixture row")
    let raw ← IO.ofExcept (IxCC.Tools.Check.unhex encoded)
    require ((Address.blake3 raw).toHex == address) s!"addressed fixture hash differs: {name}"
    if name == "profile" then
      let decoded ← IO.ofExcept (Resource.Profile.ofBytes raw)
      require (decoded.bytes == raw) "addressed profile differs"
    else
      let decoded ← IO.ofExcept (decodeConstant raw)
      require (constantBytes decoded.value == raw) s!"addressed constant differs: {name}"
    assertions := assertions + 2
  for line in (← IO.FS.readFile (root / "claims.tsv")).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [name, address, encoded] := line.splitOn "\t"
      | throw (IO.userError "invalid claim fixture row")
    let raw ← IO.ofExcept (IxCC.Tools.Check.unhex encoded)
    require ((Address.blake3 raw).toHex == address) s!"claim fixture hash differs: {name}"
    if name == "resource" then
      let decoded ← IO.ofExcept (ResourceClaim.decode raw)
      require (decoded.bytes == raw) "resource claim fixture differs"
    else
      require ((ResourceClaim.decode raw).toOption.isNone) s!"accepted non-resource claim {name}"
    assertions := assertions + 2
  -- Parameterized two-parameter structure (`PProd` shape) and dependent structure (`Sigma` shape)
  let duoProg : Resource.Program := {
    declarations := #[
      { type := .sort 0, kind := .typeConstructor }, -- 0: A
      { type := .sort 0, kind := .typeConstructor }, -- 1: B
      { type := .all ⟨.many, .shared⟩ .shared (.sort 1)
          (.all ⟨.many, .shared⟩ .shared (.sort 1) (.sort 1)),
        kind := .typeConstructor },                  -- 2: Duo
      { type := .all ⟨.erased, .shared⟩ .shared (.sort 1)
          (.all ⟨.erased, .shared⟩ .shared (.sort 1)
            (.all ⟨.linear, .unique⟩ .shared (.var 1)
              (.all ⟨.linear, .unique⟩ .unique (.var 1)
                (.app (.app (.ref 2 #[]) (.var 3)) (.var 2))))),
        kind := .assumption },                       -- 3: Duo.mk
      -- 4: project fst of Duo A B (must have type A, not B)
      { type := .all ⟨.linear, .unique⟩ .unique (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.ref 0 #[]),
        body := some (.lam ⟨.linear, .unique⟩ (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.prj 2 0 (.var 0))) },
      -- 5: project snd of Duo A B (must have type B, not A)
      { type := .all ⟨.linear, .unique⟩ .unique (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.ref 1 #[]),
        body := some (.lam ⟨.linear, .unique⟩ (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.prj 2 1 (.var 0))) },
      -- 6: wrong return type (B instead of A) for fst must fail
      { type := .all ⟨.linear, .unique⟩ .unique (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.ref 1 #[]),
        body := some (.lam ⟨.linear, .unique⟩ (.app (.app (.ref 2 #[]) (.ref 0 #[])) (.ref 1 #[])) (.prj 2 0 (.var 0))) }
    ]
    fields := #[
      { typeRef := 2, index := 0, binders := 2, type := .var 1, contract := .unique },
      { typeRef := 2, index := 1, binders := 3, type := .var 1, contract := .unique }
    ]
    projections := #[
      { typeRef := 2, constructor := 3, params := 2, fields := 2 }
    ]
  }
  require ((Resource.checkDefinition duoProg 4).isOk) "rejected parameterized structure fst projection"
  require ((Resource.checkDefinition duoProg 5).isOk) "rejected parameterized structure snd projection"
  require ((Resource.checkDefinition duoProg 6).toOption.isNone) "accepted parameterized structure swapped parameter projection"
  assertions := assertions + 3
  -- Dependent structure (`Sigma` shape): `Sig.mk : (α : Type) → (β : α → Type) →
  -- (fst : α) → β fst → Sig α β`. The second field's rule is open over both
  -- parameters and the first field, so `x.2 : F x.1` for `x : Sig A F`.
  let ref (i : UInt64) : Expr := .ref i #[]
  let many : BinderContract := ⟨.many, .shared⟩
  let field : BinderContract := ⟨.many, .unique⟩
  let sigProg : Resource.Program := {
    declarations := #[
      { type := .sort 1, kind := .typeConstructor },                          -- 0: A
      { type := .all many .shared (ref 0) (.sort 1), kind := .typeConstructor }, -- 1: F : A → Type
      { type := .all many .shared (.sort 1)
          (.all many .shared (.all many .shared (.var 0) (.sort 1)) (.sort 1)),
        kind := .typeConstructor },                                           -- 2: Sig
      { type := .all ⟨.erased, .shared⟩ .shared (.sort 1)
          (.all ⟨.erased, .shared⟩ .shared (.all many .shared (.var 0) (.sort 1))
            (.all field .shared (.var 1)
              (.all field .unique (.app (.var 1) (.var 0))
                (.app (.app (ref 2) (.var 3)) (.var 2))))),
        kind := .assumption },                                                -- 3: Sig.mk
      { type := ref 0, kind := .assumption },                                 -- 4: a : A
      { type := .app (ref 1) (ref 4), kind := .assumption }                   -- 5: b : F a
    ]
    fields := #[
      { typeRef := 2, index := 0, binders := 2, type := .var 1, contract := .unique },
      { typeRef := 2, index := 1, binders := 3, type := .app (.var 1) (.var 0), contract := .unique }
    ]
    projections := #[{ typeRef := 2, constructor := 3, params := 2, fields := 2 }]
  }
  let sigAF : Expr := .app (.app (ref 2) (ref 0)) (ref 1)
  let project (index : UInt64) (result : Expr) : Resource.Declaration := {
    type := .all ⟨.linear, .unique⟩ .unique sigAF result
    body := some (.lam ⟨.linear, .unique⟩ sigAF (.prj 2 index (.var 0))) }
  let sigCases : Array (String × Resource.Declaration × Bool) := #[
    ("first field", project 0 (ref 0), true),
    ("second field depends on the first projection", project 1 (.app (ref 1) (.prj 2 0 (.var 0))), true),
    ("second field is not the parameter type", project 1 (ref 0), false),
    ("second field does not depend on itself", project 1 (.app (ref 1) (.prj 2 1 (.var 0))), false)
  ]
  for (label, declaration, accept) in sigCases do
    let program := { sigProg with declarations := sigProg.declarations.push declaration }
    require ((Resource.checkDefinition program sigProg.declarations.size).toOption.isSome == accept)
      s!"dependent structure {label}: expected {accept}"
  -- Projection reduction on a constructor application of the projected structure only.
  let built : Expr := .app (.app (.app (.app (ref 3) (ref 0)) (ref 1)) (ref 4)) (ref 5)
  let reducesTo (e target : Expr) : Bool :=
    match (Resource.whnf sigProg 32 e).run {} with
    | .ok reduced _ => reduced == target
    | .error _ _ => false
  require (reducesTo (.prj 2 0 built) (ref 4) && reducesTo (.prj 2 1 built) (ref 5))
    "projection of a constructor application did not reduce to its field"
  require (reducesTo (.prj 2 0 (ref 5)) (.prj 2 0 (ref 5)))
    "projection of a non-constructor value reduced"
  let partialMk : Expr := .app (.app (.app (ref 3) (ref 0)) (ref 1)) (ref 4)
  require (reducesTo (.prj 2 0 partialMk) (.prj 2 0 partialMk))
    "projection of a partial constructor application reduced"
  assertions := assertions + sigCases.size + 3
  -- Recursive annotated closure with `PProd` `.brecOn` projections and equation theorem (`OS-04`)
  let annotatedBytes ← IO.FS.readBinFile "fixtures/ownership/historical/annotated-recursion-cb68/Annotated.ixe"
  let annotatedEnv ← IO.ofExcept (decodeAnonymousEnv annotatedBytes)
  let annotatedProfile := standardProfile annotatedEnv
  let annotatedResolved ← IO.ofExcept (Resource.Addressed.checkResources annotatedEnv annotatedProfile)
  require (annotatedResolved.program.fields.any (fun f => f.binders > 0))
    "expected parameterized PProd field rules in Annotated.ixe"
  assertions := assertions + 2
  return assertions + 2

end IxCCTests.IxonV3
