# Where the tests find CertiRocq: by default the plugin and runtime of the source tree, which
# must be built first (make plugin), or the installed ones after ./configure.sh global.
-include ../../Makefile.conf

ifeq '$(CERTIROCQ_CONFIG)' 'global'
  PLUGINOPTS =
  INCLUDE := $(shell rocq c -where)/user-contrib/CertiRocq/Plugin/runtime
else
  PLUGINOPTS = -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin
  INCLUDE = ../../runtime
endif
