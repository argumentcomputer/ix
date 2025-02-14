import Ix.Address

initialize initSecret : Address ← do
  IO.setRandSeed (← IO.monoNanosNow)
  let mut secret : ByteArray := default
  for _ in [:32] do
    let rand ← IO.rand 0 (UInt8.size - 1)
    secret := secret.push rand.toUInt8
  return ⟨secret⟩
