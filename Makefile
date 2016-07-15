CXX = clang++
EXTRA ?= -O3
CXXFLAGS = $(EXTRA)
LDFLAGS =
BIN = build/goat
SRCS = $(wildcard src/*.{cc}) src/parser.tab.cc src/lex.yy.c
OBJS = $(SRCS:.{c,cc}=.o)

.PHONY: all
all: build ${BIN}

parser.tab.cc: src/parser.yy
lex.yy.c: src/lexer.l

$(SRCS:.{c,cc}=.d): %.d:%.{c,cc}
	$(CXX) $(CXXFLAGS) -MM $< > $@

include $(SRCS:.{c,cc}=.d)

$(BIN): $(OBJS)

clean:
	rm -f ${BIN} ${OBJS} $(SRCS:.{c,cc}=.d)
	rm -r build

.PHONY: clean
