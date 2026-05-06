From CertiRocq.Plugin Require Import CertiRocq.
From MetaRocq.Utils Require Import utils.
Open Scope bs_scope.

Require Import CertiRocq.Compiler.pipeline.
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.CertiRocqC Require Import CertiRocqC.

Set Warnings "-primitive-turned-into-axiom".

CertiRocq Compile --time -O 1 certirocqc.
CertiRocq Generate Glue --output "glue" [ ].
