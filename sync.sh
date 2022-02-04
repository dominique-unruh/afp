#!/bin/bash

set -e

set -x

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
    git -C /opt/afp-devel status -s
    git fetch --quiet origin refs/notes/hg:refs/notes/hg
    git -C /opt/afp-devel status -s
    git fetch --quiet "$repo" "branches/default:$repo"
    git -C /opt/afp-devel status -s
    git filter-repo --quiet --force --prune-empty always --refs refs/notes/hg >/dev/null
    git -C /opt/afp-devel status -s
    git push --quiet origin "$repo"
    git -C /opt/afp-devel status -s
    git push --quiet origin refs/notes/hg
    git -C /opt/afp-devel status -s
    echo
done
