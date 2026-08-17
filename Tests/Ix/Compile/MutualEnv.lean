module
public import Tests.Ix.Compile.Mutual

/-!
Import wrapper for compiling the `Tests.Ix.Compile.Mutual` fixtures with
`ix compile … --module Tests.Ix.Compile.Mutual`. The CLI's `--module`
filter matches constants by their SOURCE module index, and a file's own
locally-elaborated constants have none — so compiling `Mutual.lean`
directly seeds nothing. Compiling this wrapper makes the fixture
constants imported (module-indexed) and the filter effective:

  lake exe ix compile Tests/Ix/Compile/MutualEnv.lean \
    --module Tests.Ix.Compile.Mutual
-/
