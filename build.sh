#!/bin/bash

git clone https://github.com/panda-planner-dev/pandaPIgrounder.git
cd pandaPIgrounder
git submodule init
git submodule update
cd cpddl
git apply ../0002-makefile.patch
make boruvka opts bliss lpsolve
make
cd ../src
make
