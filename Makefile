GAYC := cabal run exe:gayc --
LLC  := llc
GHC  := cabal exec -- ghc

SRC ?= program.gay

NAME := $(basename $(notdir $(SRC)))

BC  := build/$(NAME).bc
OBJ := build/$(NAME).o
OUT := build/$(NAME)

.PHONY: all run clean

all: $(OUT)

build:
	@mkdir -p build build/ghc

$(BC): $(SRC) | build
	@$(GAYC) "$<" "$@"

$(OBJ): $(BC)
	@$(LLC) -filetype=obj "$<" -o "$@"

$(OUT): $(OBJ) native/Main.hs native/Export.hs src/Runtime.hs | build
	@$(GHC) \
		-v0 \
		-O2 \
		-isrc \
		-inative \
		-odir build/ghc \
		-hidir build/ghc \
		-stubdir build/ghc \
		native/Main.hs \
		$(OBJ) \
		-o "$@"

run: $(OUT)
	@./$(OUT)

clean:
	@rm -rf build
