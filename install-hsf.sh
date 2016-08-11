if [[ ! -e hsf/qarmc/bin/qarmc ]]; then
    mkdir -p hsf/qarmc/bin/
    cd hsf/qarmc/bin/
    wget https://www7.in.tum.de/~popeea/research/synthesis/qarmc-64
    mv qarmc-64 qarmc
fi

cd $TRAVIS_BUILD_DIR
