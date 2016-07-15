CXX = clang++
EXTRA ?= -O3
CXXFLAGS = $(EXTRA)
LDFLAGS =
BIN = build/goat
SRCS = $(wildcard src/*.{cc}) src/parser.cc src/lex.c
OBJS = $(SRCS:.{c,cc}=.o)

.PHONY: all
all: build ${BIN}

build:
	mkdir build

src/parser.cc: src/parser.yy
	bison $< -o $@

src/lex.c: src/lexer.l
	flex $< -o $@

$(SRCS:.{c,cc}=.d): %.d:%.{c,cc}
	$(CXX) $(CXXFLAGS) -MM $< > $@

include $(SRCS:.{c,cc}=.d)

$(BIN): $(OBJS)

clean:
	rm -f ${BIN} ${OBJS} $(SRCS:.{c,cc}=.d)
	rm -f src/parser.tab.hh src/stack.hh
	rm -r build

.PHONY: clean
