#!/bin/sh

FILES=`cat TESTS`

echo "Running tests"

for f in $FILES
do
    if [ -f "${f}_opt" ]; then
        echo "Running ${f} in direct-style with O1"
        ./${f}_opt 1 > /tmp/${f}_opt.txt
	diff /tmp/${f}_opt.txt ./expected_outputs/${f}.txt || exit 1
    fi

    for i in {1..5}
    do
	if [ -f "${f}_opt${i}" ]; then
            echo "Running ${f} in direct-style with O1"
            ./${f}_opt${i} 1 > /tmp/${f}_opt${i}.txt
	    diff /tmp/${f}_opt${i}.txt ./expected_outputs/${f}.txt || exit 1
	fi
    done
done

true
