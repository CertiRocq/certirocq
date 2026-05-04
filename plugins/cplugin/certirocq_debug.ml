let certirocq_debug = ref true

let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let certirocq_msg_debug s =
  if !certirocq_debug then
    Feedback.msg_debug (Pp.str (camlstring_of_coqstring s))
