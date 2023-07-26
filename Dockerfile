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

# Let us add some heavy dependency
RUN cd /pandaPIgrounder && \
    cd cpddl && \
    make boruvka opts bliss lpsolve && \
    make && \
    cd ../src && \
    make
