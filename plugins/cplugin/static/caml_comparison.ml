
let of_coq = function
  | Datatypes.Eq -> 0
  | Datatypes.Lt -> (-1)
  | Datatypes.Gt -> 1

let to_coq = function
  | 0 -> Datatypes.Eq
  | x when x < 0 -> Datatypes.Lt
  | _ -> Datatypes.Gt