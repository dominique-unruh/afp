#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy")
else
    FILES=()
fi

SESSION=Lots-Of-Stuff
SESSION=Edit-BO

ISABELLE_DIR=/opt/Isabelle2021-1

"$ISABELLE_DIR/bin/isabelle" jedit -l "$SESSION" -d "$DIR" "${FILES[@]}" "$@" "$ISABELLE_DIR/src/Pure/ROOT.ML" &
