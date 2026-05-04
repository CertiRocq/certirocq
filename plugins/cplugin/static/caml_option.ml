
let of_coq = function
  | Datatypes.None -> None
  | Datatypes.Some x -> Some x

let to_coq = function
  | None -> Datatypes.None
  | Some x -> Datatypes.Some x