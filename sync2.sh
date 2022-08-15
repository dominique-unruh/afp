set -ex

for VERSION in devel 2019 2020 2021 2021-1; do
    if ! git remote get-url mirror-afp-$VERSION; then
	git remote add mirror-afp-$VERSION https://github.com/isabelle-prover/mirror-afp-$VERSION.git
    fi

    git fetch mirror-afp-$VERSION master:afp-$VERSION
done
