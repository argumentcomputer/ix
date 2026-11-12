Input-mode fixtures: six reference-free definitions in Ixon v5

Each fixture is a complete .ixe envelope (version 4, no role binding) of
131 bytes holding one record: the definition `fun (x : Prop) => x : Prop ->
Prop`, constructed directly as Ixon data (lvls 0, universe table [zero]). Its
binder-data section has one block per root, each with one `never` node: the
`all` binder of the type (root 0) and the `lam` binder of the value (root 1).
The six fixtures differ only in those two nodes' modes (input, result):

  many-match          all (many, shared)       lam (many, shared)
  linear-match        all (once, shared)       lam (once, shared)
  uses-mismatch       all (once, shared)       lam (many, shared)
  ownership-mismatch  all (unique, shared)     lam (many, shared)
  locality-mismatch   all (borrowed, shared)   lam (many, shared)
  result-only-unique  all (once, unique)       lam (once, unique)

They carry over the earlier input-contract fixtures (which wrote the same
differences as contract bytes in the expressions) to modes in the section.
Every record is canonical and its section complete. The bytes are fixed
independently of compiler output.

Today only `crates/ixon/tests/role_binding.rs` reads them, as inputs for the
role-binding transport tests, which claim nothing about admission.
