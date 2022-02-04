#!/bin/bash

set -e

git worktree list --porcelain | while read DIR; do
    case "$DIR" in
	worktree\ *) DIR="${DIR#worktree }"
		     if ! git -C "$DIR" diff-index --quiet HEAD --; then
			 echo "Changed files in worktree $DIR, not syncing. (git filter-repo resets the worktree)"
			 exit 1
		     fi
		     ;;
    esac
done

for repo in afp-devel afp-2021-1 afp-2021 afp-2020 afp-2019; do
    echo "** $repo **"
    git fetch --quiet origin refs/notes/hg:refs/notes/hg
    git fetch --quiet "$repo" "branches/default:$repo"
    git filter-repo --quiet --force --prune-empty always --refs refs/notes/hg >/dev/null
    git push --quiet origin "$repo"
    git push --quiet origin refs/notes/hg
    echo
done
