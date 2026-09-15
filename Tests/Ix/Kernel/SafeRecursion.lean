module

public import Tests.Ix.Kernel.AnonDiff

/-!
Termination-checked source recursion must survive export and both host
kernels' safe-definition dependency guards. These positive cases complement
the raw Ixon self-reference and mutual-cycle rejection tests.
-/

public section

namespace Tests.Kernel.SafeRecursion

open LSpec Ix.Kernel

namespace Fixtures

def countStruct : Nat → Nat
  | 0 => 0
  | n + 1 => countStruct n + 1
termination_by structural n => n

def countWellFounded (n : Nat) : Nat :=
  if h : n = 0 then 0 else countWellFounded (n - 1) + 1
termination_by n
decreasing_by omega

mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  termination_by structural n => n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
  termination_by structural n => n
end

end Fixtures

private def checkCase (env : Lean.Environment) (label : String)
    (seeds : List Lean.Name) : IO Nat := do
  for seed in seeds do
    let some (.defnInfo declaration) := env.find? seed
      | throw <| IO.userError s!"missing elaborated definition {seed}"
    unless declaration.safety == .safe do
      throw <| IO.userError s!"{seed} is not a safe definition"
    if declaration.type.getUsedConstantsAsSet.contains seed ||
        declaration.value.getUsedConstantsAsSet.contains seed then
      throw <| IO.userError s!"elaboration retained a direct self-reference in {seed}"
  let constants := AnonDiff.closureOf env seeds
  let directory ← IO.FS.createTempDir
  let path := directory / s!"safe-recursion-{label}.ixe"
  try
    let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString false
    unless status.ungrounded.isEmpty do
      throw <| IO.userError s!"compilation omitted {status.ungrounded.size} declarations"
    let bytes ← IO.FS.readBinFile path
    let source ← IO.ofExcept (Ixon.deEnv bytes)
    let leanRows ← IO.ofExcept (checkEnvAnon source { verifyHashes := true })
    let rustRows ← Ix.KernelCheck.rsCheckAnonFFI path.toString true ""
    if leanRows.isEmpty || leanRows.size != rustRows.size then
      throw <| IO.userError s!"target coverage differs: Lean {leanRows.size}, Rust {rustRows.size}"
    -- Require successful checking, not merely agreement between two rejections.
    for row in leanRows do
      if let some error := row.err? then
        throw <| IO.userError s!"Lean rejected {row.addr}: {error}"
    for (address, error) in rustRows do
      if let some error := error then
        throw <| IO.userError s!"Rust rejected {address}: {error.message}"
      unless leanRows.any (fun row => toString row.addr == address) do
        throw <| IO.userError s!"Rust checked an unmatched address {address}"
    -- Each requested definition must actually be present and checked.
    for seed in seeds do
      let some address := source.getAddr? (Ix.Name.fromLeanName seed)
        | throw <| IO.userError s!"export omitted {seed}"
      unless leanRows.any (fun row => row.addr == address) &&
          rustRows.any (fun row => row.1 == toString address) do
        throw <| IO.userError s!"no checking result for {seed}"
    return leanRows.size
  finally
    IO.FS.removeDirAll directory

def suite : List TestSeq :=
  [([("structural", [``Fixtures.countStruct]),
     ("well-founded", [``Fixtures.countWellFounded]),
     ("mutual", [``Fixtures.even, ``Fixtures.odd])].foldl (init := .done)
      fun tests (label, seeds) => tests ++
        .individualIO s!"safe recursion survives both kernels: {label}" none (do
          let env ← get_env!
          let checked ← checkCase env label seeds
          return (true, checked, 0, none)) .done)]

end Tests.Kernel.SafeRecursion

end
