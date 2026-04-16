#!/usr/bin/env sh

N=${1}
if [ -z ${N} ]; then
    N=1
fi

FILES=${2}
if [ -z ${FILES} ]; then
    FILES="fibn list_sum_int63 list_sum_int63_tinfo print_lst"
fi

# Run each test, exit upon failure.
for f in $FILES
do
    if [ -x ${f} ]; then
	echo "Running ${f} ${N} time(s)."
	./${f} ${N} > /tmp/${f}.txt
	diff /tmp/${f}.txt ./expected_outputs/${f}.txt || exit 1
    else
	echo "${f} not found."
    fi
done
