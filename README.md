A git fork of the afp repositories.

Local repo configuration used for synching:

* Uses https://github.com/mnauw/git-remote-hg to fork the Mercurial repo into git. (Install with `sudo pip3 install git-remote-hg`.)
* Local repository is a clone of https://github.com/dominique-unruh/afp
* Remotes configured using:
  * `git remote add XXX hg::https://foss.heptapod.net/isa-afp/XXX`
    where XXX is afp-devel afp-2021-1 afp-2021 afp-2020 afp-2019
* Show mercurial ids in logs: `git config core.notesRef refs/notes/hg` (local effect only)
* After the first pull (below), run `git gc --aggressive`
* Pulling new changes:
  * `git fetch XXX branches/default:XXX` for `XXX` being the different remotes (afp-devel, etc)
  * `git push origin XXX`
  * The previous two commands can be done by the script `sync.sh`, i.e.:
    `bash -c "$(git cat-file blob main:sync.sh)"`
* Merging changes into my own branch:
  * `git checkout unruh`
  * `git merge afp-devel`
