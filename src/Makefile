# XXX: might want to use CMake instead?

# Variables
# ==================================================
# Tools
CXX=g++
CC=gcc
LD=$(CXX)

# Command-line defines
CDEFS=

# Warning settings
#CWARN=-Wno-declaration-after-statement -Wno-variadic-macros
CWARN=-Wno-unused-parameter -Wno-sign-compare
CERROR=

# CFlags for libraries
CXXFLAGS_LIBS=

# CFlags for production and for debugging
CXXFLAGS_GENERAL=-pipe -Wall -Wextra -pedantic -std=gnu++17 $(CDEFS) $(CWARN) $(CERROR) $(CXXFLAGS_LIBS) -fconcepts -I../cpddl/ -I../cpddl/third-party/boruvka/
CCFLAGS_GENERAL=-pipe -Wall -Wextra -pedantic $(CDEFS) $(CWARN) $(CERROR) $(CXXFLAGS_LIBS) 
OPTIMIZER_PROD=-O3
OPTIMIZER_DEBUG=-Og
CXXFLAGS_PROD=$(OPTIMIZER_PROD) -g -DNDEBUG -flto
CXXFLAGS_DEBUG=$(OPTIMIZER_DEBUG) -ggdb3 -DDEBUG_MODE
CCFLAGS=$(CCFLAGS_GENERAL) $(CXXFLAGS_PROD)


CXXFLAGS=$(CXXFLAGS_GENERAL) $(CXXFLAGS_PROD)

# LDFlags
LDFLAGS_GENERAL=
LDFLAGS_PROD=$(OPTIMIZER_PROD) -flto -static -static-libgcc
LDFLAGS_DEBUG=-g $(OPTIMIZER_DEBUG)
LDFLAGS=$(LDFLAGS_GENERAL) $(LDFLAGS_PROD)

# Libs
LIBS=

# Files
HFILES=$(wildcard *.h)
SRCFILES=$(wildcard *.cpp)
CSRCFILES=$(filter-out cmdline.c, $(wildcard *.c))
OBJFILES=$(patsubst %.cpp,%.o,$(SRCFILES))
COBJFILES=$(patsubst %.c,%.o,$(CSRCFILES)) cmdline.o
DEPENDENCIES=
DEPENDENCIES_LD=
PROGNAME=../pandaPIgrounder

H2OBJFILES=../h2-fd-preprocessor/src/axiom.cc.o ../h2-fd-preprocessor/src/causal_graph.cc.o ../h2-fd-preprocessor/src/domain_transition_graph.cc.o ../h2-fd-preprocessor/src/h2_mutexes.cc.o ../h2-fd-preprocessor/src/helper_functions.cc.o ../h2-fd-preprocessor/src/max_dag.cc.o ../h2-fd-preprocessor/src/mutex_group.cc.o ../h2-fd-preprocessor/src/operator.cc.o ../h2-fd-preprocessor/src/scc.cc.o ../h2-fd-preprocessor/src/state.cc.o ../h2-fd-preprocessor/src/successor_generator.cc.o ../h2-fd-preprocessor/src/variable.cc.o ../cpddl/libpddl.a ../cpddl/third-party/boruvka/libboruvka.a


# Rules
# ==================================================
.PHONY: clean

all: $(PROGNAME)

$(PROGNAME): $(OBJFILES) $(COBJFILES) $(H2OBJFILES) $(DEPENDENCIES_LD) 
	$(LD) $(LDFLAGS) -o $(PROGNAME) $(OBJFILES) $(COBJFILES) $(H2OBJFILES) $(LIBS)

# All object files depend on the source file and all header files
../h2-fd-preprocessor/src/%.cc.o: ../h2-fd-preprocessor/src/%.cc
	$(CXX) -c $(CXXFLAGS) -o $@ $<

# All object files depend on the source file and all header files
%.o: %.cpp $(DEPENDENCIES) $(HFILES)
	$(CXX) -c $(CXXFLAGS) -o $@ $<

# All object files depend on the source file and all header files
%.o: %.c 
	$(CC) -c $(CCFLAGS) -o $@ $<

main.cpp: cmdline.h

cmdline.c cmdline.h: options.ggo
	gengetopt --include-getopt --default-optional --unamed-opts -i options.ggo

clean:
	rm -f $(PROGNAME) $(OBJFILES) $(COBJFILES)

# Disable built-in rules; otherwise "make debug" will do weird things since debug.o may exist
.SUFFIXES:

debug: CXXFLAGS = $(CXXFLAGS_GENERAL) $(CXXFLAGS_DEBUG)
debug: CCFLAGS = $(CCFLAGS_GENERAL) $(CXXFLAGS_DEBUG)
debug: LDFLAGS = $(LDFLAGS_GENERAL) $(LDFLAGS_DEBUG)
debug: all
