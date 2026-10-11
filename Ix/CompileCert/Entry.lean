import Ix.CompileCert.Support

/-! # Admission-connected direct-cone certification

The executable reads and admits the exact bytes before comparing an
independent source export against the reader stream. Its result carries
proofs of the checks actually performed. No producer-supplied proposition,
Boolean verdict, or `Named.original` field is accepted as correspondence.

This is a conservative foundation of C1, not completed W. Singleton definitions
may use the proved raw reader-normalization relation; its semantic pull-back
and complete source/export refinement remain separate obligations.

The development is split by concern; this module gathers it. Imports form a
tree over `Installed` (the strong installed model, the installed checks and
annotated applications):

* `CheckCompiled`: the artifact check (W): `checkCompiled`, `faithful_sound`,
  `checkRoots`.
* `AnnotationTrace`: annotation traces of the checker's runs.
* `SourceInstallation`: installation of the original source and its models.
* `SourceNormalization` (on `AnnotationTrace`, `SourceInstallation`): source
  projection normalization and the normalized installation;
  `SourceProjection` on it: installed source projections;
  `ProjectionPullback` on that: projection laws through the pull-back.
* `RuleLaws`: rule and capability laws.
* `InstalledAssociation` (on `CheckCompiled`, `RuleLaws`,
  `SourceNormalization`): the installed association.
* `Support` (on `InstalledAssociation`, `ProjectionPullback`): admitted
  support and the public semantic model.
-/
