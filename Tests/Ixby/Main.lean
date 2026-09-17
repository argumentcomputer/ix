import Tests.Ixby

def main : IO UInt32 := do
  let a ← Tests.Ixby.Basic.suite
  let b ← Tests.Ixby.Crypto.suite
  let c ← Tests.Ixby.Codec.suite
  let d ← Tests.Ixby.Collections.suite
  let e ← Tests.Ixby.Claim.suite
  return a + b + c + d + e
