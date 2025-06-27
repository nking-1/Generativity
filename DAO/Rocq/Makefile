# DAO Theory Coq Development

COQMAKEFILE := Makefile.coq
COQPROJECT := _CoqProject

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

cleanall: clean
	find src -name "*.aux" -o -name ".*.aux" -o -name ".*.cache" | xargs rm -f

install: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) install

uninstall: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) uninstall

.PHONY: all clean cleanall install uninstall

# Development targets
check: all
	@echo "All files compiled successfully!"

doc: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) html

.PHONY: check doc