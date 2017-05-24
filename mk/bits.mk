# 64-bit or 32-bit platform
BITS	  := $(shell OCAML=$(OCAML) mk/bits)

# sanity check
ifeq ($(BITS),)
$(warning *** Could not determine machine word size (see mk/bits).)
$(warning *** You can use  make ... BITS=32|64  to override this check.)
$(error Aborting)
endif
