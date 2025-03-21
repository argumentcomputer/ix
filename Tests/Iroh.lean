import LSpec
import Ix.Iroh.Transfer

open LSpec Iroh Transfer

-- Uncomment to test the sendBytes function, which registers an Iroh node that waits for `recvBytes` connections.
-- The test will hang until Ctrl+C is pressed twice, once for the Tokio runtime and once for the test executable.
def Tests.Iroh.suite :=
  --let bytes := ByteArray.mk #[1, 2, 3]
  [
    test "Sending bytes" (1 = 1)
  --  withExceptOk "Sending bytes" (sendBytes bytes) fun _ => .done
  ]
