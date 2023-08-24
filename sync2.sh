set -ex

for VERSION in devel 2023 2022 2021-1 2021 2020 2019; do
    if ! git remote get-url mirror-afp-$VERSION; then
	git remote add mirror-afp-$VERSION https://github.com/isabelle-prover/mirror-afp-$VERSION.git
    fi

    git fetch mirror-afp-$VERSION master:afp-$VERSION
    git push origin afp-$VERSION
done
