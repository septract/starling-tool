if [[ ! -d hsf/qarmc ]]; then
    mkdir -p hsf/qarmc/bin/
    cd hsf/qarmc/bin/
    wget https://www7.in.tum.de/~popeea/research/synthesis/qarmc-64
fi

cd $TRAVIS_BUILD_DIR
