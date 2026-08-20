# Changelog fragments

Individual changes are authored here as JSON fragments — one per PR — before
they land in the top-level [`CHANGELOG.md`](../CHANGELOG.md). A bot regenerates
the `[Unreleased]` block on every merge and freezes those fragments into a
dated version section at each release. Fragments are the source of truth;
`CHANGELOG.md` is derived.

## Directory layout

```
.changes/
├── unreleased/                # in-flight fragments, one JSON per PR
├── latest/                    # active minor line
│   └── <version>/  { *.json } # per-patch fragment dir (e.g. 0.30.0/, 0.30.1/)
├── <M>.<N>.x/                 # frozen prior minor line
│   ├── <M>.<N>.0/  { *.json }
│   ├── <M>.<N>.1/  { *.json }
│   └── CHANGELOG.md           # frozen snapshot; never edited again
└── …
```

## Fragment schema

Each PR adds one file at `.changes/unreleased/<PR-number>.json`:

```json
{
  "pr": 843,
  "type": "feat",
  "summary": "Add SSO sign-in for enterprise accounts.",
  "impact": "minor",
  "breaking": false,
  "author": "azkrishpy",
  "url": "https://github.com/awslabs/aws-c-io/pull/843",
  "notes": ""
}
```

| Field | Values / source |
|---|---|
| `pr` | PR number, also the filename |
| `type` | `feat` \| `fix` \| `doc` \| `chore` \| `revert` (Conventional-Commit prefix) |
| `summary` | customer-facing one sentence; author writes this |
| `impact` | ABI-check label — `major` \| `minor` \| `patch` |
| `breaking` | `true` if title has `!`, has a `BREAKING CHANGE:` footer, or `impact == "major"` |
| `author` | PR author login, or omit to stay anonymous |
| `url` | link to the PR |
| `notes` | optional extended notes; keep it short |

Fields other than `summary` and `notes` are filled by the bot from PR metadata
and the ABI-check label.

## Authoring a fragment

Run `scripts/new-change` when you open a PR (or use the PR template checklist);
it seeds the fragment from the PR title. Then edit `summary` to be the
customer-facing sentence.

Merge is blocked until a valid fragment exists. For PRs with no
customer-visible change (docs-only, CI, refactor), apply the `skip-changelog`
label as an escape hatch.

## Lifecycle

- **PR open** — author creates a fragment under `unreleased/`.
- **PR merged** — renderer regenerates the `[Unreleased]` block of the root
  `CHANGELOG.md` in a queued chore commit. Renders serialize through a single
  concurrency group so merges never race on `CHANGELOG.md`.
- **Patch release** (e.g. `0.30.0 → 0.30.1`) — fragments move
  `unreleased/*.json → latest/0.30.1/`; a `## [0.30.1] — <date>` section is
  prepended under `[Unreleased]` in the root `CHANGELOG.md`. No freeze.
- **Minor or major release** (e.g. `0.30.x → 0.31.0`) — freeze happens:
  1. Rename `latest/` → `<M>.<N>.x/`.
  2. Copy root `CHANGELOG.md` into `<M>.<N>.x/CHANGELOG.md`, stripping
     `[Unreleased]`, retitled `# Changelog — <M>.<N>.x`. Never edited again.
  3. Reset root `CHANGELOG.md` to an empty `[Unreleased]` + fresh `[X.Y+1.0]`
     section.
  4. Move pending fragments from `unreleased/` → `latest/<X.Y+1.0>/`.

## Corrections after merge

Rare. A follow-up `chore(changelog):` PR may edit a fragment. Reverts get a new
fragment with `type: revert` that links the original PR; the original fragment
is preserved so the audit trail is intact.

## Rendered categories

The renderer maps fragment `type` to these customer-facing categories, in this
order, with breaking changes surfaced first:

- **Breaking changes** — fragments with `breaking: true` (⚠, tagged with the
  impact source, e.g. `major` or `minor · ABI-affecting`).
- **Features** — `type: feat`.
- **Fixes** — `type: fix`.
- **Docs** — `type: doc`.
- **Maintenance** — `type: chore` (hidden from the customer file by default;
  still recorded in the fragment for traceability).

## Finding a change

| You want | Look here |
|---|---|
| currently in-flight change | root `CHANGELOG.md`, `[Unreleased]` section |
| change in the current minor line (`X.Y.*`) | root `CHANGELOG.md`, per-version section |
| change in a prior minor line (`A.B.*` ≠ current) | `.changes/A.B.x/CHANGELOG.md` |
| the exact set of changes in a given tag | GitHub Release page for that tag |

## Directory sort caveat

Filesystem lex sort places `0.10.x/` before `0.2.x/`. Both the rendered root
`CHANGELOG.md` and each frozen per-minor `CHANGELOG.md` are semver-sorted by
the renderer, so customers never see this quirk. Only `ls .changes/` looks out
of order — and only for maintainers browsing raw.
