import LSpec
import Ix.Iroh.Transfer

open LSpec Iroh Transfer

def Tests.Iroh.suite :=
  let file := "./README.md"
  let num := sendFile file
  [
    test "Sending file" (num = 0)
  ]
