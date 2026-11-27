(lang dune 3.23)
(using rocq 0.11)
(name certirocq)

; The theories, the optimized plugin and the C runtime
(package (name rocq-certirocq))
; The plugin extracted without optimizations, used to bootstrap
(package (name rocq-certirocq-vanilla))
; The bootstrapped compiler and checker
(package (name rocq-certirocqc))
(package (name rocq-certirocqchk))
