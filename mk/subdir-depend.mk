# figure out dependencies for a given .ml file
# 1. use ocamldep
# 2. for each resulting module, check whether it's
#   - a local module -> add $(DIR)/build/X.cmx dependency
#     (a target may define a BLACKLIST to correct this guess)
#   - a toplevel module -> add src/X/X.cmxa dependency
# 3. also generate corresponding cmo -> cmo / cmo -> cma dependency

define dep
@echo DEP $<
@$(OCAMLDEP) -modules $< | $(PERL) -ne ' \
  @m = qw($(MODS)); \
  sub f { \
    $$s = lcfirst($$1); \
    $$r = ""; \
    @n = grep /\/$$s\.cmx$$/, @m; \
    if (@n && ! grep {$$_ eq $$1} qw($(BLACKLIST))) { \
      $$r = "$$r $$n[0]" if $$n[0] ne $$o; \
    } else { \
      if (grep {$$_ eq $$1} qw($(TOPLEVEL))) { \
        $$r = "$$r src/$$s/$$s.cmxa" \
      } \
    } \
    return $$r; \
  } \
  s=\.ml=\.cmx=g; \
  s=/src/=/build/=; \
  /(.*):/; \
  $$o = $$1; \
  s/ \*[^*]*\*//g; \
  s/ (\S*)/f $$1/ge; \
  print; \
  s=\.cmxa=.cma=g; \
  s=\.cmx=.cmo=g; \
  print; \
' > $@
endef

# one rule for .ml files in source dir
$(DEPDIR)/%.ml: DIR := $(DIR)
$(DEPDIR)/%.ml: MODS := $(FILES:%.ml=$(BUILD)/%.cmx)
$(DEPDIR)/%.ml: $(SRC)/%.ml $(BUILD).mk mk/subdir-depend.mk | $$(dir $$@).dir
	$(dep)

# one rule for (generated) .ml files in build dir
$(DEPDIR)/%.ml: DIR := $(DIR)
$(DEPDIR)/%.ml: MODS := $(FILES:%.ml=$(BUILD)/%.cmx)
$(DEPDIR)/%.ml: $(BUILD)/%.ml $(BUILD).mk mk/subdir-depend.mk | $$(dir $$@).dir
	$(dep)

# put given targets in dependency order
# (coerce $(MAKE) into doing the work for us, using a stub makefile)
depend-$(PACK) $(DEPDIR)/order: PACK := $(PACK)
depend-$(PACK) $(DEPDIR)/order: $(BUILD).mk mk/subdir-depend.mk $(FILES:%=$(DEPDIR)/%) | $(DEPDIR)/.dir
	@echo ORDER $(DIR_$(PACK))
	@( echo 'all: $(FILES_$(PACK):%.ml=$(DIR_$(PACK))/build/%.cmx) ;' ; \
	   echo 'include $(FILES_$(PACK))' ; \
	   echo '$(DIR_$(PACK))/%.cmx: ; @echo $$@' ;\
	   echo '%: ;' ) > $(DIR_$(PACK))/build/.dep/order.mk
	@cd $(DIR_$(PACK))/build/.dep; $(MAKE) --no-print-directory -srf order.mk > /dev/null
	@echo OBJS_$(PACK) := $$(cd $(DIR_$(PACK))/build/.dep; $(MAKE) --no-print-directory -srf order.mk) > $(DIR_$(PACK))/build/.dep/order

# ... profit
include $(FILES:%=$(DEPDIR)/%) $(DEPDIR)/$(PACKL).ml
include $(DEPDIR)/order

