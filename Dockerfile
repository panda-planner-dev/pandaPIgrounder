FROM ubuntu:22.04
LABEL Description="Pandas Grounder"

ENV HOME /root

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get -y --no-install-recommends install \
    build-essential \
    clang \
    cmake \
    gdb \
    git \
    wget \
    ca-certificates zip unzip gengetopt

COPY . /pandaPIgrounder

RUN cd /pandaPIgrounder/cpddl && \
    git restore . && \
    cd third-party/boruvka && git restore .

RUN cd /pandaPIgrounder/cpddl && \
    git apply ../0002-makefile.patch

RUN cd /pandaPIgrounder && \
    cd cpddl && \
    make boruvka opts bliss lpsolve 

RUN cd /pandaPIgrounder/cpddl && make

RUN cd /pandaPIgrounder/src && \
    make
