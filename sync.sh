#!/bin/bash

set -e

if ! git diff-index --quiet HEAD --; then
    echo "Changed files in worktree, not syncing. (git filter-repo resets the worktree)"
    exit 1
fi

for repo in afp-devel afp-2021-1 afp-2021 afp-2020 afp-2019; do
    echo "** $repo **"
    git fetch --quiet origin refs/notes/hg:refs/notes/hg
    git fetch --quiet "$repo" "branches/default:$repo"
    git filter-repo --quiet --force --prune-empty always --refs refs/notes/hg >/dev/null
    git push --quiet origin "$repo"
    git push --quiet origin refs/notes/hg
    echo
done
