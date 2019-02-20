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
CWARN=-Wno-unused-parameter
CERROR=-Werror=implicit-function-declaration

# CFlags for libraries
CXXFLAGS_LIBS=

# CFlags for production and for debugging
CXXFLAGS_GENERAL=-c -pipe -Wall -Wextra -pedantic -std=gnu++14 $(CDEFS) $(CWARN) $(CERROR) $(CXXFLAGS_LIBS)
CXXFLAGS_PROD=-g -O2 -DNDEBUG
CXXFLAGS_DEBUG=-ggdb3 -O0 -fsanitize=address -DDEBUG_MODE
CXXFLAGS=$(CXXFLAGS_GENERAL) $(CXXFLAGS_PROD)

# LDFlags
LDFLAGS=
LDFLAGS_DEBUG=-fsanitize=address

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
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f $(PROGNAME) $(OBJFILES)

# Disable built-in rules; otherwise "make debug" will do weird things since debug.o may exist
.SUFFIXES:

debug: CXXFLAGS = $(CXXFLAGS_GENERAL) $(CXXFLAGS_DEBUG)
debug: LDFLAGS = $(LDFLAGS_DEBUG)
debug: all
