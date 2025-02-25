/-!
Import this module if:

* Your file doesn't contain a definition that calls Rust code directly and
* One of your definitions calls C code and that C code calls Rust code

This is necessary for the linking between C and Rust to succeed when building on
Nix devshell.

TODO: check if this workaround is still necessary once `nix build` is set.
-/

@[extern "rs_noop"]
private opaque rs_noop [Inhabited α] : Unit → α
