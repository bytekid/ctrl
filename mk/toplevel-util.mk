# $(call check-opt,foo) tests whether a  foo.opt  executable exists, and uses
# it if available. Otherwise, fall back to foo.
check-opt = $(shell command -v $(1).opt || command -v $(1) || echo $(1))
