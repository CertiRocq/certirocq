.PHONY: all submodules runtime plugins plugin cplugin install clean bootstrap plugin-manifests

PLUGIN_MANIFEST_INPUTS=plugins/manifests/generate.py plugins/manifests/plugin-manifest
PLUGIN_MANIFEST_OUTPUTS=plugins/plugin/_CoqProject plugins/plugin/certirocq_plugin.mlpack plugins/cplugin/_CoqProject plugins/cplugin/certirocq_vanilla_plugin.mlpack
PYTHON ?= python3

all theories/Extraction/extraction.vo theories/ExtractionVanilla/extraction.vo: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries 
	$(MAKE) -C theories 

theories/Makefile: theories/_CoqProject
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile: libraries/_CoqProject
	cd libraries;coq_makefile -f _CoqProject -o Makefile

submodules:
	git submodule update
	./make_submodules.sh

plugins: plugin cplugin

plugin-manifests: $(PLUGIN_MANIFEST_OUTPUTS)

plugins/plugin/_CoqProject plugins/plugin/certirocq_plugin.mlpack: $(PLUGIN_MANIFEST_INPUTS) theories/Extraction/extraction.vo
	bash ./clean_extraction.sh plugins/plugin
	$(PYTHON) plugins/manifests/generate.py plugin

plugins/cplugin/_CoqProject plugins/cplugin/certirocq_vanilla_plugin.mlpack: $(PLUGIN_MANIFEST_INPUTS) theories/ExtractionVanilla/extraction.vo
	bash ./clean_extraction.sh plugins/cplugin
	$(PYTHON) plugins/manifests/generate.py cplugin

plugin: all runtime plugins/plugin/CertiRocq.vo

plugins/plugin/Makefile: plugins/plugin/_CoqProject plugins/plugin/certirocq_plugin.mlpack
	cd plugins/plugin ; coq_makefile -f _CoqProject -o Makefile

plugins/plugin/CertiRocq.vo: all plugins/plugin/Makefile
	bash ./make_plugin.sh plugins/plugin


cplugin: all runtime plugins/cplugin/CertiRocq.vo

plugins/cplugin/Makefile: plugins/cplugin/_CoqProject plugins/cplugin/certirocq_vanilla_plugin.mlpack
	cd plugins/cplugin ; coq_makefile -f _CoqProject -o Makefile

plugins/cplugin/CertiRocq.vo: all plugins/cplugin/Makefile
	bash ./make_plugin.sh plugins/cplugin

bootstrap: plugin cplugin
	$(MAKE) -C bootstrap all

install: plugin cplugin bootstrap
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C runtime install
	$(MAKE) -C plugins/plugin install
	$(MAKE) -C plugins/cplugin install
	$(MAKE) -C bootstrap install

# Clean generated makefiles
mrproper: theories/Makefile libraries/Makefile plugins/plugin/Makefile plugins/cplugin/Makefile
	rm -f theories/Makefile
	rm -f libraries/Makefile
	rm -f plugins/plugin/Makefile
	rm -f plugins/cplugin/Makefile

clean: theories/Makefile libraries/Makefile plugins/plugin/Makefile plugins/cplugin/Makefile
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
	$(MAKE) -C runtime clean
	$(MAKE) -C plugins/plugin clean
	$(MAKE) -C plugins/cplugin clean
	$(MAKE) -C bootstrap clean
	rm -f `find theories -name "*.ml*"`
	rm -rf plugins/plugin/extraction
	rm -rf plugins/cplugin/extraction
	$(MAKE) mrproper

runtime: runtime/Makefile
	$(MAKE) -C runtime
