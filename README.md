An attempt to make a git fork of the afp repositories.

Local repo configuration used for synching:

* Uses https://github.com/mnauw/git-remote-hg to fork the Mercurial repo into git.
* Local repository is a clone of https://github.com/dominique-unruh/afp
* Remotes configured using:
  * `git remote add afp-devel hg::https://foss.heptapod.net/isa-afp/afp-devel`
  * `git remote add afp-2021-1 hg::https://foss.heptapod.net/isa-afp/afp-2021-1`
* Show mercurial ids in logs: `git config core.notesRef refs/notes/hg` (local effect only)
# * Cloning afp-devel:
#  * `git fetch afp-devel branches/default`
#  * `git fetch afp-2021-1 branches/default`
* SKIP Creating local branches for tracking upstream:
  * SKIP `git branch afp-devel remotes/afp-devel/branches/default`
  * SKIP `git branch afp-2021-1 remotes/afp-2021-1/branches/default`
* Pulling new changes:
  * `git fetch XXX branches/default:XXX` for `XXX` being the different remotes (afp-devel, etc)
  * `git push origin XXX`
  * The previous two commands can be done by the script `sync.sh`, i.e.:
    `bash -c "$(git cat-file blob main:sync.sh)"`
* Merging changes into my own branch:
  * `git checkout unruh`
  * `git merge afp-devel`
