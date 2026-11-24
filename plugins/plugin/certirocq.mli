open Plugin_utils

type command_args = Certirocq_options.command_args
type prim = Certirocq_options.prim
type inductive_mapping = Certirocq_options.inductive_mapping
type inductives_mapping = Certirocq_options.inductives_mapping
type extract_inductive = Certirocq_options.extract_inductive
type extract_inductives = Certirocq_options.extract_inductives
type options = Certirocq_options.options

val default_options : unit -> options
val make_options : command_args list -> prim list -> string -> options

(* Register primitive operations and associated include file *)
val register : prim list -> import list -> unit

val register_inductives : inductives_mapping -> unit
val register_constant_inductives : extract_inductives -> unit
val register_inlines : Kernames.kername list -> unit

val get_name : Names.GlobRef.t -> string

(* Support for running dynamically linked certirocq-compiled programs *)
type certirocq_run_function = unit -> Obj.t

(* [register_certirocq_run global_id fresh_name function]. A same global_id
  can be compiled multiple times with different definitions, fresh_name indicates
  the version used this time *)
val register_certirocq_run : string -> string -> certirocq_run_function -> unit
val run_certirocq_run : string -> certirocq_run_function

module type CompilerInterface = sig
  type name_env
  val compile : Pipeline_utils.coq_Options -> Ast0.Env.program -> ((name_env * Clight.program) * Clight.program) CompM.error * Bytestring.String.t
  val printProg : Clight.program -> name_env -> string -> import list -> unit

  val generate_glue : Pipeline_utils.coq_Options -> Ast0.Env.global_declarations -> 
    (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
end

module CompileFunctor (CI : CompilerInterface) : sig
  val compile_only : opaque_access:Global.indirect_accessor ->
                     options -> Names.GlobRef.t -> import list -> unit
  val generate_glue_only : opaque_access:Global.indirect_accessor ->
                           options -> Names.GlobRef.t -> unit
  val compile_C : opaque_access:Global.indirect_accessor ->
                  options -> Names.GlobRef.t -> import list -> unit
  val show_ir : opaque_access:Global.indirect_accessor ->
                options -> Names.GlobRef.t -> unit
  val compile_wasm : opaque_access:Global.indirect_accessor ->
                    options -> Names.GlobRef.t -> unit
  val glue_command : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t list -> unit
  val eval_gr : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> import list -> Constr.t
  val eval : opaque_access:Global.indirect_accessor -> options -> Environ.env -> Evd.evar_map -> EConstr.t -> import list -> Constr.t
end

val compile_only : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> import list -> unit
val generate_glue_only : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> unit
val compile_C : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> import list -> unit
val show_ir : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> unit
val compile_wasm : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> unit
val glue_command : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t list -> unit
val eval_gr : opaque_access:Global.indirect_accessor -> options -> Names.GlobRef.t -> import list -> Constr.t
val eval : opaque_access:Global.indirect_accessor -> options -> Environ.env -> Evd.evar_map -> EConstr.t -> import list -> Constr.t
