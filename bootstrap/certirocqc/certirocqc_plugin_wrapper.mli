open Pipeline_utils
open Toplevel0
open Bytestring

val compile : rocq_Options -> Ast0.Env.program -> rocq_Cprogram CompM.error * String.t
