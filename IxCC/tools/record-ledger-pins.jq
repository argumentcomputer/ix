# Merge the mechanical pins printed by `check-trusted-externs --record`
# (passed as `--slurpfile pins FILE`) into docs/trusted-externs.json.
# Each object keeps its key order: a changed value is replaced in place, a key
# no longer present is dropped and a new one is appended. A CI action keeps
# its entry (version, use) and takes its new commit; a new action repository
# is not added here, and the audit then names it. Everything else (seed
# versions, symbols, closures, csimp theorems, last_reviewed) is edited by
# hand. See "Routine updates" in docs/trusted-extern-ledger.md.

def merge($new):
  reduce ($new | keys_unsorted[]) as $key
    (with_entries(select(.key as $old | $new | has($old)));
     .[$key] = $new[$key]);

.integrity.tracked_files |= merge($pins[0].tracked_files)
| .integrity.repository_files = ((.integrity.repository_files // {}) | merge($pins[0].repository_files))
| .integrity.flake_nodes |= merge($pins[0].flake_nodes)
| .ci_actions |= map(.commit = ($pins[0].ci_actions[.repository] // .commit))
