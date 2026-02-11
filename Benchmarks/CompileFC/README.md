# CompileFC

Runs the Ix compiler over the Lean environment of https://github.com/google-deepmind/formal-conjectures.

Uses Lean v4.22.0 to match the formal-conjectures project, hence the separate project.

> [!NOTE]
> Doesn't build with lean4-nix v4.22.0 with the lake dev shell due to changes in `.lake` behavior

## Usage

`ix compile --path /path/to/CompileFC.lean`
