# ix

A verifiable computing platform

## Build

For [elan](https://github.com/leanprover/elan) users: `lake build`

For [Nix Flakes](https://nixos.wiki/wiki/flakes) users: `nix build` or `nix develop` and then `lake build`.

> [!NOTE]
> It is highly recommended to set up [Cachix](https://github.com/cachix/cachix) before running `nix build`, or else you'll have to recompile Lean from source.
> ```
> # Install
> nix-env -iA cachix -f https://cachix.org/api/v1/install
> # Configure
> cachix use argumentcomputer
> ```
> Then you should see queries to argumentcomputer.cachix.org and a relatively short build time.
