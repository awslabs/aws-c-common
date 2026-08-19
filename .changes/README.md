# Archived changelogs

Each file in this directory is the frozen `CHANGELOG.md` from a completed minor
version series (`X.Y.*`), archived at the moment the next minor version was cut.

## Layout

```
.changes/
  README.md          this file
  X.Y.md             the full changelog for minor series X.Y (patches Z=0..N)
  ...
```

For example, `.changes/0.14.md` holds every change released in `0.14.0`,
`0.14.1`, ..., `0.14.N` — the state of the top-level `CHANGELOG.md` just before
`0.15.0` was tagged.

## How to find a change

- **In the current minor version** (`X.Y.*` at HEAD): see the top-level
  [`CHANGELOG.md`](../CHANGELOG.md).
- **In a prior minor version** (`A.B.*` where `A.B != X.Y`): open `A.B.md` in
  this directory.
- **Attached to a specific tag**: see the GitHub Release page for that tag; the
  release notes there are generated from the same changelog entries.

## How the archive is populated

The release automation cuts a new minor version by rotating the top-level
`CHANGELOG.md` into this directory. Concretely, when releasing `X.(Y+1).0`:

1. Copy the current `CHANGELOG.md` to `.changes/X.Y.md`.
2. Reset the top-level `CHANGELOG.md` to an empty `[Unreleased]` skeleton.
3. Commit both, then tag `vX.(Y+1).0`.

Patch releases (`X.Y.Z+1`) do not rotate — they append entries under the same
top-level file.
