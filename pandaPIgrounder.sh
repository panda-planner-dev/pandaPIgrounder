#! /bin/bash

show_help() {
    echo "Usage: $(basename $0) INPUT-FILE OUTPUT-FILE"
}


while getopts "hu" opt; do
    case "$opt" in
         h|u)
             show_help
             exit 0
             ;;
     esac   
done

if (( $# != 2 )); then
    >&2 echo "Illegal number of parameters"
    show_help
    exit 1
fi

DIR=${TMPDIR}$(mktemp -d panda-grounder.XXXXXXXX)

mkdir -p ${DIR}

cp $1 ${DIR}/

input_filename=$( basename "$1" )

docker run -i -v ${DIR}:/io panda-pi-grounder:latest pandaPIgrounder/pandaPIgrounder /io/${input_filename} /io/output.sas

cp ${DIR}/output.sas $2

