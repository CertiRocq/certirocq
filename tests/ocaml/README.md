Extraction to OCaml Tests
--------------------------

Extract and compile the CertiRocq tests with the OCaml compiler
(bytecode + native) to compare performance.


To extract, compile and run:

   # make all

Note that vs_easy and vs_hard are modified by hand so they will not
become extracted every time the script run.

The modification is neede to suspend top-level computations from
becoming evaluated once (and for all), so that we can run the
computation multiple times.
