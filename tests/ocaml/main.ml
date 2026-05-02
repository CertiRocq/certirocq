open Unix

let iterations =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: ./main <iterations>";
    exit 1
  end;
  int_of_string Sys.argv.(1)

let run name arg bench =
  let t = Unix.gettimeofday () in
  for _ = 1 to iterations do
    ignore (bench arg)
  done;
  let elapsed_ms = (Unix.gettimeofday () -. t) *. 1000.0 in
  Printf.printf "%s execution time: %f milliseconds\n" name elapsed_ms

let () =
  run "demo1" Demo1.Tt Demo1.demo1;
  run "demo2" Demo2.Tt Demo2.demo2;
  run "list_sum" List_sum.Tt List_sum.list_sum;
  run "vs_easy" Vs_easy.Tt Vs_easy.vs_easy;
  run "vs_hard" Vs_hard.Tt Vs_hard.vs_hard;
  run "binom" Binom.Tt Binom.binom;
  run "sha_fast" Sha_fast.Tt Sha_fast.sha_fast
