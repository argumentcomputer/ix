/-! `String.utf8ByteSize` is specified by equations, one of which holds by a
certificate theorem whose closure reaches `Classical.choice` and `Nat.lor`. The
artifact keeps that closure, so its role table must bind both.

`artifactDefault` puts `inferInstance` in the source closure beside `id`. The
two (and `wfParam`) share one content address, with different reducibility
hints, and the certificates' closure holds a constant at that address. With
`id` alone in the source closure, the artifact's hint there is `id`'s, and
`ix compile` refuses the certificates' records because they would change it. -/
def artifactWidth (s : String) : Nat := s.utf8ByteSize

def artifactDefault : Nat := (inferInstance : Inhabited Nat).default
