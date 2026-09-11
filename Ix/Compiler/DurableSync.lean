/-!
# Narrow durable-filesystem boundary

Lean's portable `IO.FS.Handle.flush` empties the runtime buffer but does not
request stable storage. These two operations are the intentionally small native
boundary used by the persistent HPT cache around its atomic rename.

Both functions reject a path of the wrong kind. Their filesystem and hardware
semantics remain assumptions recorded in the trusted-extern ledger; they do
not participate in any logical theorem or bless cache bytes as valid.
-/

namespace Ix.Compiler.DurableSync

/-- Request stable storage for one regular file. -/
@[extern "compilatrix_durable_sync_file"]
opaque file (path : @& System.FilePath) : IO Unit

/-- Request stable storage for one directory's entries. -/
@[extern "compilatrix_durable_sync_directory"]
opaque directory (path : @& System.FilePath) : IO Unit

end Ix.Compiler.DurableSync
