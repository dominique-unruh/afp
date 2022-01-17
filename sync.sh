#!/bin/bash

set -ex

for repo in afp-devel afp-2021-1 afp-2021 afp-2020 afp-2019; do
    git fetch "$repo" "branches/default:$repo"
    git push origin "$repo"
done
