Require Import MetaRocq.Utils.bytestring.
From CertiRocq.Plugin Require Import Loader.

Axiom (msg_info : string -> unit).
Axiom (msg_notice : string -> unit).
Axiom (msg_debug : string -> unit).
Axiom (user_error : string -> unit).

CertiRocq Register [
  msg_info => "rocq_msg_info",
  msg_notice => "rocq_msg_notice",
  msg_debug => "rocq_msg_debug",
  user_error => "rocq_user_error" ]
Include [ Library "rocq_c_ffi.h" "rocq_ffi.h" ].
