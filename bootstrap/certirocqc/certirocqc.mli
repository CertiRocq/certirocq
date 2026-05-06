open Certirocq_vanilla_plugin
open Plugin_utils

val compile_only : opaque_access:Global.indirect_accessor ->
                   Certirocq.options -> Names.GlobRef.t -> import list -> unit
val compile_C : opaque_access:Global.indirect_accessor ->
                Certirocq.options -> Names.GlobRef.t -> import list -> unit
val generate_glue_only : opaque_access:Global.indirect_accessor ->
                         Certirocq.options -> Names.GlobRef.t -> unit
val show_ir : opaque_access:Global.indirect_accessor ->
              Certirocq.options -> Names.GlobRef.t -> unit
val glue_command : opaque_access:Global.indirect_accessor ->
                   Certirocq.options -> Names.GlobRef.t list -> unit
