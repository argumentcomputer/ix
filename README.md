# ix

A verifiable computing platform

## Build & Install

- Build and test the Ix library with `lake build` and `lake test`

- Run the Ix CLI with `lake exe ix`. Install the binary with `lake run install`

### Nix

#### Prerequisites

- Install [Nix](https://nixos.org/download/)

- Enable [Flakes](https://zero-to-nix.com/concepts/flakes/)
  - Add `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf` or `/etc/nix/nix.conf`
  - Add `trusted-users = root MYUSER` to `/etc/nix/nix.conf`
  - Then restart the Nix daemon with `sudo pkill nix-daemon`

- Install [Cachix](https://docs.cachix.org/installation)
  - Run `nix profile install --accept-flake-config nixpkgs#cachix`
  - Enable the cache with `cachix use argumentcomputer`
  - When building, you should see `querying <...> on https://argumentcomputer.cachix.org`

#### Build

Build and run the Ix CLI with `nix build` and `nix run`

To build and run the test suite, run `nix build .#test` and `nix run .#test`

#### Cache Troubleshooting

If the Nix build hangs with a message like `building lean-stage0`, it's not finding the cached packages and will likely take >15 minutes to build the Lean compiler from source. Ctrl+C and check the following:

- Note that caching is only provided for `x86_64-linux` and `aarch64-darwin` at the moment
- Make sure `substituters` and `trusted-public-keys` have been added to `~/.config/nix/nix.conf`
- Try restarting the Nix daemon again
- Check the given derivation is present in the cache, see the [Cachix FAQ](https://docs.cachix.org/faq#why-is-nix-not-picking-up-on-any-of-the-pre-built-artifacts)
- Check the Lean version is supported at https://github.com/argumentcomputer/lean4-nix/tree/dev/manifests
