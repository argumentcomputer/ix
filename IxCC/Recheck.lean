import IxCC.Recheck.Err
import IxCC.Recheck.Cert
import IxCC.Recheck.Run
import IxCC.Recheck.Produce
import IxCC.Recheck.Json

/-! # The compiler: `produce` and `Recheck.run` (D17)

Design note 00 "Produce and recheck" and 06 S44, as built for Phase 1
(M1.I1):

* `Recheck.Cert` (`Recheck.Cert`): the untrusted certificate: the table in
  proposal form, the relevance annotation, the middle end's oracle, the
  allocation outputs, the frame layouts and the block order;
* `Recheck.produce` (`Recheck.Produce`): ingress's output to a certificate,
  natively, with every search and oracle;
* `Recheck.run` (`Recheck.Run`): a `Src.Program` and a certificate to an
  ELF object, re-running the P-style passes on the certificate's decisions
  and validating the rest, in kernel-evaluable style as far as the stages
  allow;
* `Recheck.compile`: ingress, `produce`, `run`;
* `Recheck.Json`: the certificate's serialisation (`ixcc/cert/1`);
* `Recheck.Err`: every decline or rejection as `stage: code: message`.

`Recheck.sound` (the per-artifact theorem, from which `compile_sound` and
`compile_safe` follow) is M2.8. The command-line compiler is
`IxCC.Cli`. -/
