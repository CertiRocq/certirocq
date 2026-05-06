type command_args =
 | TYPED_ERASURE
 | UNSAFE_ERASURE
 | BYPASS_QED
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | CARGS of int
 | ANFVARIANT of int
 | BUILD_DIR of string
 | OUTPUT_SUFFIX of string
 | FFI_PREFIX of string
 | ENTRY_POINT of string
 | OUTPUT of string

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
    anf_variant : int;
    build_dir : string;
    filename : string;
    ext : string;
    prefix : string;
    toplevel_name : string;
    prims : prim list;
    inductives_mapping : inductives_mapping;
    extracted_inductives : extract_inductives;
  }

val check_build_dir : string -> string

val default_options :
  build_dir:string ->
  inductives_mapping:inductives_mapping ->
  extracted_inductives:extract_inductives ->
  unit ->
  options

val make_options :
  build_dir:string ->
  inductives_mapping:inductives_mapping ->
  extracted_inductives:extract_inductives ->
  command_args list ->
  prim list ->
  string ->
  options
