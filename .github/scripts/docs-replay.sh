#!/usr/bin/env bash
# Replay one merge commit from the release branch onto the docs branch, then
# regenerate CHANGELOG.md and fold it into that same commit -- one docs commit
# per release-branch merge, so the release branch stays free of bot commits.
#
# Called by changelog-render.yml in CI and by changelog-selftest.yml against a
# scratch repository. Both must run this file, never a copy of it.
#
#   TRIGGER_SHA      merge commit to replay (required)
#   DOCS_BRANCH      branch holding the rendered changelog  (default: docs)
#   DEFAULT_BRANCH   branch releases are cut from           (default: main)
#   CHANGELOG_PY     path to changelog.py                   (required)
#   PUSH             "true" to push the result              (default: true)
set -euo pipefail

: "${TRIGGER_SHA:?TRIGGER_SHA is required}"
: "${CHANGELOG_PY:?CHANGELOG_PY is required}"
DOCS_BRANCH="${DOCS_BRANCH:-docs}"
DEFAULT_BRANCH="${DEFAULT_BRANCH:-main}"
PUSH="${PUSH:-true}"

echo "replaying ${TRIGGER_SHA} from ${DEFAULT_BRANCH} onto ${DOCS_BRANCH}"

git config user.name  "aws-sdk-common-runtime-bot"
git config user.email "aws-sdk-common-runtime@amazon.com"

if git ls-remote --exit-code --heads origin "${DOCS_BRANCH}" >/dev/null 2>&1; then
  git fetch origin "${DOCS_BRANCH}:${DOCS_BRANCH}" 2>/dev/null || true
  git checkout "${DOCS_BRANCH}"
elif git rev-parse --verify --quiet "refs/heads/${DOCS_BRANCH}" >/dev/null; then
  git checkout "${DOCS_BRANCH}"
else
  # First run: branch from the parent of TRIGGER_SHA so the first cherry-pick
  # is meaningful -- it introduces the changes rather than replaying history.
  git checkout -B "${DOCS_BRANCH}" "$(git rev-parse "${TRIGGER_SHA}^")"
fi

# A merge commit has no single diff, so git needs the mainline named; branches
# that take pull requests as merges rather than squashes produce them.
MAINLINE=()
if git rev-parse --verify --quiet "${TRIGGER_SHA}^2" >/dev/null; then
  MAINLINE=(-m 1)
fi

# -x records the origin sha; --allow-empty tolerates an identical tree;
# -Xno-renames avoids false renames once a rollup has moved fragments out of
# preview/ into a released <version>/ directory on docs.
if ! git cherry-pick -x --allow-empty ${MAINLINE[@]+"${MAINLINE[@]}"} \
       --strategy=recursive -Xno-renames "${TRIGGER_SHA}"; then
  UNMERGED="$(git diff --name-only --diff-filter=U | sort -u)"
  if [[ -z "$UNMERGED" ]] && git diff --cached --quiet; then
    # Already replayed: the commit is empty against docs. A re-run of this
    # workflow must be a no-op, not a failure.
    echo "${TRIGGER_SHA} is already on ${DOCS_BRANCH}; nothing to replay"
    git cherry-pick --skip || git cherry-pick --abort || true
  elif [[ "$UNMERGED" == "CHANGELOG.md" ]]; then
    # CHANGELOG.md is derived entirely from .changes/, so a conflict in it
    # carries no information; the unconditional render below rewrites it.
    echo "auto-resolving the derived CHANGELOG.md conflict"
    git checkout --theirs CHANGELOG.md
    git add CHANGELOG.md
    GIT_EDITOR=true git cherry-pick --continue
  else
    echo "ERROR: cherry-pick conflict in: ${UNMERGED:-<none>}" >&2
    git cherry-pick --abort || true
    exit 1
  fi
fi

# Rendering unconditionally is cheaper than working out whether this commit
# touched fragments, and it self-heals drift. A no-op render amends nothing.
python3 "${CHANGELOG_PY}" render
git add CHANGELOG.md
if git diff --cached --quiet HEAD~1; then
  # The replay reproduced the tree already on this branch. That happens when the
  # commit is replayed twice: the CHANGELOG.md conflict resolves to the same
  # content, so committing would leave a duplicate. Drop it instead.
  echo "${TRIGGER_SHA} changed nothing on ${DOCS_BRANCH}; dropping the replay"
  git reset --hard -q HEAD~1
elif ! git diff --cached --quiet; then
  git commit --amend --no-edit
fi

if [[ "$PUSH" == "true" ]]; then
  git push origin "${DOCS_BRANCH}"
else
  echo "PUSH=false, leaving ${DOCS_BRANCH} local"
fi
