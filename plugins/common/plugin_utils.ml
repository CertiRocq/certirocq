open Metarocq_template_plugin.Ast_quoter
open Pp

type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
  | LibraryPath of string
  | Link of string

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

let debug (m : unit -> Pp.t) =
  if debug_opt () then
    Feedback.(msg_debug (m ()))
  else
    ()

let string_of_bytestring = Caml_bytestring.caml_string_of_bytestring
let bytestring_of_string = Caml_bytestring.bytestring_of_caml_string

let extract_constant (g : Names.GlobRef.t) (s : string) : Kernames.kername * Kernames.ident =
  match g with
  | Names.GlobRef.ConstRef c ->
      (Obj.magic (quote_kn (Names.Constant.canonical c)), bytestring_of_string s)
  | Names.GlobRef.VarRef _ ->
      CErrors.user_err (str "Expected a constant but found a variable. Only constants can be realized in C.")
  | Names.GlobRef.IndRef _ ->
      CErrors.user_err (str "Expected a constant but found an inductive type. Only constants can be realized in C.")
  | Names.GlobRef.ConstructRef _ ->
      CErrors.user_err (str "Expected a constant but found a constructor. Only constants can be realized in C. ")

let rec debug_mappings (ms : (Kernames.kername * Kernames.ident) list) : unit =
  match ms with
  | [] -> ()
  | (k, s) :: ms ->
      Feedback.msg_debug (str ("Kername: " ^ string_of_bytestring (Kernames.string_of_kername k) ^ " C: " ^ string_of_bytestring s));
      debug_mappings ms

let make_help_msg ~supports_wasm : string =
  let wasm_help =
    if supports_wasm then
      "To compile a Gallina definition named <gid> to Wasm type:\n\
         CertiRocq Compile Wasm <options> <gid>.\n\n\
"
    else
      ""
  in
  "Usage:\n\
To compile a Gallina definition named <gid> to C type:\n\
   CertiRocq Compile <options> <gid>.\n\n\
"
  ^ wasm_help
  ^ "To evaluate a Gallina definition named <gid> type:\n\
   CertiRocq Eval <options> <gid>.\n\n\
To show this help message type:\n\
   CertiRocq --help.\n\n\
To produce an .ir file with the last IR (lambda-anf) of the compiler type:\n\
   CertiRocq Show IR <options> <gid>.\n\n\
Valid options:\n\
--output S                 : Use S as the output name stem. Default: the fully qualified name of <gid>.\n\
--output-suffix S          : Append S to generated output names.\n\
-O N                       : Control closure-allocation optimization. N=0 disables lambda lifting; N=1 optimizes closures with lambda lifting. Values above 1 currently behave like 1.\n\
--debug                    : Show debugging information.\n\
--c-args N                 : Set the C-argument threshold used by lambda lifting and C translation.\n\
--cps                      : Compile through continuation-passing style (default: direct style).\n\
--time                     : Time the main compilation phases.\n\
--time-anf                 : Time LambdaANF optimization subphases.\n\
--anf-variant N            : Select an experimental LambdaANF pipeline variant.\n\
--allow-unsafe-erasure     : Allow unsafe MetaRocq erasure passes, including cofixpoint-to-fixpoint translation.\n\
--typed-erasure            : Use MetaRocq typed erasure and dearging.\n\
--bypass-qed               : Allow quotation to inspect Qed-opaque constants.\n\
--build-dir DIR            : Write generated files under DIR.\n\
--entry-point S            : Use S as the generated top-level function name.\n\
\n\n\
To compile Gallina constants to specific C functions use:\n\
   CertiRocq Compile <options> <gid> Extract Constants [ constant1 => \"c_function1\", ... , constantN => \"c_functionN\" ] Include [ \"file1.h\" , Library \"runtime_header.h\", ... , Absolute \"fileM.h\" ].\n\
\n\
See https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-plugin for more detailed information."
