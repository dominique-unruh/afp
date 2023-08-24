A git fork of the afp repositories.

Uses the existing git clones from https://github.com/isabelle-prover/.

Use `sync2.sh` from main branch to do the synching. By putting
```
#!/bin/bash
bash -c "$(git -C ~/r/afp cat-file blob main:sync2.sh)"
```
into `.git/sync.sh`, you can invoke it more easily.

Branches:
* afp-XXXX: Mirror of the AFP version XXXX (incl. afp-devel)
* unruh-edits: General work in progress by Dominique Unruh
* registers-submission: Work on a paper submission (obsolete?)
