# `tests/lib`

Shared Rocq library built as `CertiRocq.Tests.lib`.

Files built by default:

- [Binom.v](/Users/zoo/Repos/certirocq/tests/lib/Binom.v:1): binomial-heap benchmark that builds large priority queues, merges them, and removes the maximum element.
- [Color.v](/Users/zoo/Repos/certirocq/tests/lib/Color.v:1): graph-coloring benchmark based on the Kempe/Chaitin register-allocation algorithm. Blazy, Robillard, and Appel, ESOP 2010.
- [vs.v](/Users/zoo/Repos/certirocq/tests/lib/vs.v:1): VeriStar benchmark for separation-logic entailment checking.
- [sha256.v](/Users/zoo/Repos/certirocq/tests/lib/sha256.v:1): SHA-256 benchmark. Andrew W. Appel and Stephen Yi-Hsien Lin; adapted in CertiRocq from a VST/OEUF-based version.
- [coind.v](/Users/zoo/Repos/certirocq/tests/lib/coind.v:1): memoization and coinductive-stream examples, including a memoized factorial and selecting an element from an infinite stream.
- [stack_machine.v](/Users/zoo/Repos/certirocq/tests/lib/stack_machine.v:1): arithmetic-expression and stack-machine example instantiated with several numeric representations, including `nat`, `N`, and `PrimInt`.

Other files in this directory:

- [SqlQueries3.v](/Users/zoo/Repos/certirocq/tests/lib/SqlQueries3.v:1): SQL/DataCert benchmark. The header says it is not open-source, not licensed for redistribution, and is included with permission for CertiCoq performance benchmarking; it credits the DataCert library and Véronique Benzaken and Évelyne Contejean (2016).
- [bignum.v](/Users/zoo/Repos/certirocq/tests/lib/bignum.v:1): bignum implementation combining `Int31` and `BigN`, with arithmetic and normalization between the two representations.
- [coqprime.v](/Users/zoo/Repos/certirocq/tests/lib/coqprime.v:1): primality-certificate benchmark built on the `Coqprime` library via `PocklingtonRefl`; the file contains concrete certificates `cert1` through `cert4`.
