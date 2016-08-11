if [[ ! -d z3-z3-4.4.1 ]]; then
    wget https://github.com/Z3Prover/z3/archive/z3-4.4.1.zip
    unzip z3-4.4.1.zip
    cd z3-z3-4.4.1
    python scripts/mk_make.py  --prefix=`pwd`/install
    cd build
    make
    make install
fi

cd $TRAVIS_BUILD_DIR
