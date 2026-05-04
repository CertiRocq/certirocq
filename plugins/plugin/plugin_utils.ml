open Metarocq_template_plugin.Ast_quoter
open Names
open Pp
open Caml_bytestring

  
let debug_opt =
  let open Goptions in
  let key = ["CertiRocq"; "Debug"] in
  match get_option_value key with
  | Some get -> fun () ->
      begin match get () with
      | BoolValue b -> b
      | _ -> assert false
      end
  | None ->
   (declare_bool_option_and_ref ~key ~value:false ()).get

let debug (m : unit ->Pp.t) =
  if debug_opt () then
    Feedback.(msg_debug (m ()))
  else
    ()

type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
  | LibraryPath of string
  | Link of string

let string_of_bytestring = caml_string_of_bytestring
let bytestring_of_string = bytestring_of_caml_string

(* From GlobRef to kername *)

let extract_constant (g : Names.GlobRef.t) (s : string) : (Kernames.kername * Kernames.ident)  =
  match g with
  | Names.GlobRef.ConstRef c -> (Obj.magic (quote_kn (Names.Constant.canonical c)), bytestring_of_caml_string s)
  | Names.GlobRef.VarRef(v) -> CErrors.user_err (str "Expected a constant but found a variable. Only constants can be realized in C.")
  | Names.GlobRef.IndRef(i) -> CErrors.user_err (str "Expected a constant but found an inductive type. Only constants can be realized in C.")
  | Names.GlobRef.ConstructRef(c) -> CErrors.user_err (str "Expected a constant but found a constructor. Only constants can be realized in C. ")

let rec debug_mappings (ms : (Kernames.kername * Kernames.ident) list) : unit =
  match ms with
  | [] -> ()
  | (k, s) :: ms ->     
     Feedback.msg_debug (str ("Kername: " ^ (caml_string_of_bytestring (Kernames.string_of_kername k)) ^ 
      " C: "  ^ (caml_string_of_bytestring s)));
     debug_mappings ms
     
(* Help message *)
     
let help_msg : string =
  "Usage:\n\
To compile a Gallina definition named <gid> to C type:\n\
   CertiRocq Compile <options> <gid>.\n\n\
To compile a Gallina definition named <gid> to Wasm type:\n\
   CertiRocq Compile Wasm <options> <gid>.\n\n\
To evaluate a Gallina definition named <gid> type:\n\
   CertiRocq Eval <options> <gid>.\n\n\
To show this help message type:\n\
   CertiRocq -help.\n\n\
To produce an .ir file with the last IR (lambda-anf) of the compiler type:\n\
   CertiRocq Show IR <options> <gid>.\n\n\
Valid options:\n\
-file S   :  Specify the filename. Default: the fully qualified name of <gid>.\n\
-ext S    :  Specify the string s to be appended to the filename\n\
-prefix S :  Specify the string s to be prepended to the FFI functions (to avoid clashes with C functions)\n\
-O N      :  Where N=0 or N=1. N=1 (default) will enable the λΑΝF transformation lambda-lifting that will try to allocate closure environments is registers. N=0 disables lambda lifting.\n\
-debug    :  Show debugging information\n\
-args X   :  Specify how many arguments are used in the C translation (on top of the thread_info argument)\n\
-cps      :  Compile using continuation-passing style code (default: direct-style compilation)\n\
-time     :  Time each compilation phase\n\
-time_anf :  Time λanf optimizations\n\
-unsafe-erasure   :  Allow to use unsafe passes in the MetaRocq Erasure pipeline. This currently includes the cofixpoint-to-fixpoint translation.\n\
-typed-erasure    :  Uses the typed erasure and de-arging phase of the MetaRocq Erasure pipeline.\n\
\n\n\
To compile Gallina constants to specific C functions use:\n\
   CertiRocq Compile <options> <gid> Extract Constants [ constant1 => \"c_function1\", ... , constantN => \"c_functionN\" ] Include [ \"file1.h\" , Library \"runtime_header.h\", ... , Absolute \"fileM.h\" ].\n\
\n\
See https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-plugin for more detailed information."
