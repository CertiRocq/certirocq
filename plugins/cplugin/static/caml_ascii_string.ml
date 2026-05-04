open Ascii

let rec caml_ascii_string_length_aux s acc =
  match s with
  | String0.EmptyString -> acc
  | String0.String (_, s) -> caml_ascii_string_length_aux s (succ acc)

let caml_ascii_string_length s = caml_ascii_string_length_aux s 0

let char_of_ascii a =
  let code = Ascii.byte_of_ascii a in
  Caml_byte.char_of_byte code

let ascii_of_char a =
  let code = Caml_byte.byte_of_char a in
  Ascii.ascii_of_byte code

let caml_string_of_ascii_string (l : String0.string) : string =
  let len = caml_ascii_string_length l in
  let buf = Bytes.create len in
  let rec aux i = function
    | String0.EmptyString -> ()
    | String0.String (c, cs) ->
      Bytes.set buf i (char_of_ascii c); aux (succ i) cs
  in
  aux 0 l;
  Bytes.to_string buf

let ascii_string_of_caml_string (s : string) : String0.string =
  let rec aux acc i =
    if i < 0 then acc
    else aux (String0.String (ascii_of_char s.[i], acc)) (i - 1)
  in aux String0.EmptyString (String.length s - 1)
  