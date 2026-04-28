.PHONY: all submodules runtime plugin cplugin install clean bootstrap


all theories/Extraction/extraction.vo: theories/Makefile libraries/Makefile
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

plugin: all runtime plugin/CertiRocq.vo

plugin/Makefile: plugin/_CoqProject
	cd plugin ; coq_makefile -f _CoqProject -o Makefile

plugin/CertiRocq.vo: all plugin/Makefile
	bash ./make_plugin.sh plugin


cplugin: all runtime cplugin/CertiRocq.vo

cplugin/Makefile: cplugin/_CoqProject
	cd cplugin ; coq_makefile -f _CoqProject -o Makefile

cplugin/CertiRocq.vo: all cplugin/Makefile
	bash ./make_plugin.sh cplugin

bootstrap: plugin cplugin
	$(MAKE) -C bootstrap all

install: plugin cplugin bootstrap
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C runtime install
	$(MAKE) -C plugin install
	$(MAKE) -C cplugin install
	$(MAKE) -C bootstrap install

# Clean generated makefiles
mrproper: theories/Makefile libraries/Makefile plugin/Makefile cplugin/Makefile
	rm -f theories/Makefile
	rm -f libraries/Makefile
	rm -f plugin/Makefile
	rm -f cplugin/Makefile

clean: theories/Makefile libraries/Makefile plugin/Makefile cplugin/Makefile
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
	$(MAKE) -C runtime clean
	$(MAKE) -C plugin clean
	$(MAKE) -C cplugin clean
	$(MAKE) -C bootstrap clean
	rm -f `find theories -name "*.ml*"`
	rm -rf plugin/extraction
	rm -rf cplugin/extraction
	$(MAKE) mrproper

runtime: runtime/Makefile
	$(MAKE) -C runtime
