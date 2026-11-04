Canonical C+ input-contract regression fixtures

These six reference-free definitions were constructed directly as Ixon data,
serialized and fully decoded, then checked by published 137
8fb4049f9f0833d1e583d5a19b049c7e9a7169c0. Each .const is exactly 15 bytes and
each complete .ixe envelope 122 bytes. input_contracts.rs checks the exact
addresses, scalar fields, structure and byte roundtrip before check_const.

The type is Prop -> Prop and the body is the identity lambda over Prop.
No external constant, primitive role, assumption or resource validation is
involved. The three mismatch fixtures differ respectively in input usage,
ownership and locality and must be rejected under C+. Matching many/linear
inputs and the result-only unique variant must be accepted.

Published 137 accepted all six, demonstrating the intended negative regression.
The bytes and expected behavior are fixed independently of compiler output.
