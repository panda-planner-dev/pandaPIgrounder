# XXX: might want to use CMake instead?

# Variables
# ==================================================
# Tools
CXX=g++
LD=$(CXX)

# Command-line defines
CDEFS=

# Warning settings
#CWARN=-Wno-declaration-after-statement -Wno-variadic-macros
CWARN=-Wno-unused-parameter -Wno-sign-compare
CERROR=-Werror=implicit-function-declaration

# CFlags for libraries
CXXFLAGS_LIBS=

# CFlags for production and for debugging
CXXFLAGS_GENERAL=-pipe -Wall -Wextra -pedantic -std=gnu++17 $(CDEFS) $(CWARN) $(CERROR) $(CXXFLAGS_LIBS) -fconcepts
OPTIMIZER_PROD=-O3
OPTIMIZER_DEBUG=-Og
CXXFLAGS_PROD=$(OPTIMIZER_PROD) -g -DNDEBUG -flto
CXXFLAGS_DEBUG=$(OPTIMIZER_DEBUG) -ggdb3 -DDEBUG_MODE
CXXFLAGS=$(CXXFLAGS_GENERAL) $(CXXFLAGS_PROD)

# LDFlags
LDFLAGS_GENERAL=
LDFLAGS_PROD=$(OPTIMIZER_PROD) -flto
LDFLAGS_DEBUG=$(OPTIMIZER_DEBUG)
LDFLAGS=$(LDFLAGS_GENERAL) $(LDFLAGS_PROD)

# Libs
LIBS=

# Files
HFILES=$(wildcard *.h)
SRCFILES=$(wildcard *.cpp)
OBJFILES=$(patsubst %.cpp,%.o,$(SRCFILES))
DEPENDENCIES=
DEPENDENCIES_LD=
PROGNAME=pandaPIgrounder

# Rules
# ==================================================
.PHONY: clean

all: $(PROGNAME)

$(PROGNAME): $(OBJFILES) $(DEPENDENCIES_LD)
	$(LD) $(LDFLAGS) -o $(PROGNAME) $(OBJFILES) $(LIBS)

# All object files depend on the source file and all header files
%.o: %.cpp $(DEPENDENCIES) $(HFILES)
	$(CXX) -c $(CXXFLAGS) -o $@ $<

clean:
	rm -f $(PROGNAME) $(OBJFILES)

# Disable built-in rules; otherwise "make debug" will do weird things since debug.o may exist
.SUFFIXES:

debug: CXXFLAGS = $(CXXFLAGS_GENERAL) $(CXXFLAGS_DEBUG)
debug: LDFLAGS = $(LDFLAGS_GENERAL) $(LDFLAGS_DEBUG)
debug: all
