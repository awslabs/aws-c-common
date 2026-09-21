# Changelog fragments

Individual changes are recorded here as JSON fragments — one per PR. The
top-level [`CHANGELOG.md`](../CHANGELOG.md) is derived from these.

## Directory layout

```
.changes/
├── preview/                   # in-flight fragments, one JSON per PR
├── latest/                    # active minor line
│   └── <version>/  { *.json } # per-patch fragment dir (e.g. 0.30.0/, 0.30.1/)
├── <M>.<N>.x/                 # frozen prior minor line
│   ├── <M>.<N>.0/  { *.json }
│   ├── <M>.<N>.1/  { *.json }
│   └── CHANGELOG.md           # frozen snapshot for this minor line
└── …
```

## Fragment schema

Each fragment is `.changes/preview/<PR-number>.json` while in flight, then
moves into `latest/<version>/` at release time.

```json
{
  "pr": 1212,
  "type": "feat",
  "summary": "Add an API for compact (dash-free) UUID-to-string conversion.",
  "url": "https://github.com/awslabs/aws-c-common/pull/1212",
  "notes": ""
}
```

| Field | Values |
|---|---|
| `pr` | PR number; also the filename |
| `type` | `feat` \| `fix` \| `doc` \| `chore` \| `revert` |
| `summary` | customer-facing one sentence |
| `url` | link to the PR |
| `notes` | optional extended notes |

## Finding a change

| You want | Look here |
|---|---|
| currently in-flight | `preview/*.json` on `main`, or the rendered view on the `docs` branch |
| in the current minor line (`X.Y.*`) | root [`CHANGELOG.md`](../CHANGELOG.md) |
| in a prior minor line (`A.B.*`) | `.changes/A.B.x/CHANGELOG.md` |
| exact set for a tag | GitHub Release page for that tag |

> Note: filesystem lex sort places `0.10.x/` before `0.2.x/`. The rendered `CHANGELOG.md` files are semver-sorted, so only raw `ls .changes/` looks out of order.
