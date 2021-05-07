CASK = cask
SRCS = $(wildcard *.el)
OBJS = $(SRCS:.el=.elc)
PATTERN = .*

.cask/:
	$(CASK) install

# TODO: Individualize
$(OBJS): %.elc: %.el .cask/
	cask build

.PHONY: build
build: $(OBJS)

.PHONY: buttercup
buttercup: build
	$(CASK) exec buttercup -L . --pattern '$(PATTERN)' test

.PHONY: ert
ert: build
	$(CASK) exec ert-runner

.PHONY: test
test: buttercup ert

.PHONY: entr
entr: build
	find . -name "*.el" -or -name "Makefile" | entr -c -s "make test"

.PHONY: clean
clean:
	cask clean-elc
	rm -f $(OBJS)
	rm -f test/*.elc
