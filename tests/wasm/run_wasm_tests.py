#!/usr/bin/env python3

import os
import sys
import subprocess

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

files = open("TESTS").read().strip().split("\n")

ret_code = 0

for f in files:
    name = f"CertiRocq.Tests.tests.{f}.wasm"
    assert os.path.isfile(name), f"didn't find wasm file {name}."

    print(f"\nrunning: {name}")
    r = subprocess.run(
        [
            "node",
            "--stack-size=10000000",
            "js/run_wasm.js",
            "./",
            f,
        ]
    )

    if r.returncode != 0:
        ret_code = r.returncode

sys.exit(ret_code)
