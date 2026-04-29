open Pipeline_utils
open Toplevel0
open Bytestring

val compile : coq_Options -> Ast0.Env.program -> coq_Cprogram CompM.error * String.t
