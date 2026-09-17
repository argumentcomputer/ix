# Current direct-conversion fixture

Format 1, semantics 2. The 77-byte program uses explicit Nat/Word32 conversions
and produces the 19-byte expected output from the 25-byte input in seven
logical transitions. The required gate reproduces all bytes and runs a fresh
standalone executor. The 184-byte profile and statement are independently
encoded; hashes appear in [runtime-v2-integration.json](../runtime-v2-integration.json).

The older conversions-v1 root does not prove this changed statement. No native
root is claimed for this fixture; the separate [runtime-v2 fixture](../runtime-v2/README.md)
has a freshly verified current root.
