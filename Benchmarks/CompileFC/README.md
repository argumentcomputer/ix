# CompileFC

> [!NOTE]
> This project does not currently work with Ix as the Lean version is out of date.

Runs the Ix compiler over the Lean environment of all defs from https://github.com/google-deepmind/formal-conjectures.

The defs in CompileFC.lean were generated automatically with the following:
```
lake update
cd .lake/packages/formal_conjectures
lake exe mk_all --lib FormalConjectures
mv FormalConjectures.lean ../../../CompileFC.lean
```

Uses Lean v4.22.0 to match the formal-conjectures project, hence the separate project.

## Usage

`ix compile --path /path/to/CompileFC.lean`
