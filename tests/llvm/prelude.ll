; The runtime prelude the correctness statement links in front of the emitted
; module: [runtime_prelude := [TLE_Declaration gc_decl]] in
; theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v.
declare void @garbage_collect(ptr)
