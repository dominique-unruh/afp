#!/bin/bash

set -ex

for repo in afp-devel afp-2021-1 afp-2021 afp-2020 afp-2019; do
    git fetch origin refs/notes/hg
    git fetch "$repo" "branches/default:$repo"
    git filter-repo --force --prune-empty always --refs refs/notes/hg
    git push origin "$repo"
    git push origin refs/notes/hg
done

