type command_args =
 | TYPED_ERASURE
 | UNSAFE_ERASURE
 | BYPASS_QED
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int
 | ANFCONFIG of int
 | BUILDDIR of string
 | EXT of string
 | DEV of int
 | PREFIX of string
 | TOPLEVEL_NAME of string
 | FILENAME of string

type prim = ((Kernames.kername * Kernames.ident) * int * bool)

type inductive_mapping = Kernames.inductive * (string * int list)
type inductives_mapping = inductive_mapping list

type extract_inductive = { cstrs : Kernames.kername list; elim : Kernames.kername }
type extract_inductives = (Kernames.kername * extract_inductive list) list

type options =
  { typed_erasure : bool;
    unsafe_erasure : bool;
    bypass_qed : bool;
    cps : bool;
    time : bool;
    time_anf : bool;
    olevel : int;
    debug : bool;
    args : int;
    anf_conf : int;
    build_dir : string;
    filename : string;
    ext : string;
    dev : int;
    prefix : string;
    toplevel_name : string;
    prims : prim list;
    inductives_mapping : inductives_mapping;
    extracted_inductives : extract_inductives;
  }

let check_build_dir d =
  if d = "" then "." else
  let isdir =
    try Unix.((stat d).st_kind = S_DIR)
    with Unix.Unix_error (Unix.ENOENT, _, _) ->
      CErrors.user_err Pp.(str "Could not compile: build directory " ++ str d ++ str " not found.")
  in
  if not isdir then
    CErrors.user_err Pp.(str "Could not compile: " ++ str d ++ str " is not a directory.")
  else d

let default_options ~build_dir ~inductives_mapping ~extracted_inductives () : options =
  { typed_erasure = false;
    unsafe_erasure = false;
    bypass_qed = false;
    cps = false;
    time = false;
    time_anf = false;
    olevel = 1;
    debug = false;
    args = 5;
    anf_conf = 0;
    build_dir = check_build_dir build_dir;
    filename = "";
    ext = "";
    dev = 0;
    prefix = "";
    toplevel_name = "body";
    prims = [];
    inductives_mapping;
    extracted_inductives;
  }

let make_options ~build_dir ~inductives_mapping ~extracted_inductives
    (l : command_args list) (pr : prim list) (fname : string) : options =
  let rec aux (o : options) l =
    match l with
    | [] -> o
    | TYPED_ERASURE :: xs -> aux {o with typed_erasure = true} xs
    | UNSAFE_ERASURE :: xs -> aux {o with unsafe_erasure = true} xs
    | BYPASS_QED :: xs -> aux {o with bypass_qed = true} xs
    | CPS :: xs -> aux {o with cps = true} xs
    | TIME :: xs -> aux {o with time = true} xs
    | TIMEANF :: xs -> aux {o with time_anf = true} xs
    | OPT n :: xs -> aux {o with olevel = n} xs
    | DEBUG :: xs -> aux {o with debug = true} xs
    | ARGS n :: xs -> aux {o with args = n} xs
    | ANFCONFIG n :: xs -> aux {o with anf_conf = n} xs
    | BUILDDIR s :: xs -> aux {o with build_dir = check_build_dir s} xs
    | EXT s :: xs -> aux {o with ext = s} xs
    | DEV n :: xs -> aux {o with dev = n} xs
    | PREFIX s :: xs -> aux {o with prefix = s} xs
    | TOPLEVEL_NAME s :: xs -> aux {o with toplevel_name = s} xs
    | FILENAME s :: xs -> aux {o with filename = s} xs
  in
  let opts =
    { (default_options ~build_dir ~inductives_mapping ~extracted_inductives ())
      with filename = fname }
  in
  let opts = aux opts l in
  { opts with prims = pr }
