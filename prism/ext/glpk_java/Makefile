################################################
#  NB: This Makefile is designed to be called  #
#      from the main PRISM Makefile. It won't  #
#      work on its own because it needs        #
#      various options to be passed in         #
################################################

default: all

all: checks ../../lib/glpk_java

LDPATH = $(shell cd ../glpk/src/glpk/src/.libs; pwd)
CFLAGSPATH = $(shell cd ../glpk/src/glpk/src; pwd)
SWIGFLAGSPATH = $(shell cd ../glpk/src/glpk/src; pwd)

glpkjavavers = "1.7.0"

IS_SRC_CREATED = $(shell find . -name "src" 2> /dev/null)
ALREADY_DOWNLOADED = $(shell ls src | grep libglpk-java-$(glpkjavavers).tar.gz 2> /dev/null)
ALREADY_INSTALLED_JAR = $(shell find src/glpk_java/swig -name glpk-java.jar 2> /dev/null)
ALREADY_INSTALLED_LIB = $(shell find src/glpk_java/swig/.libs -name $(LIBPREFIX)glpk_java$(LIBSUFFIX) 2> /dev/null)
ALREADY_INSTALLED = 1

ifeq ($(ALREADY_INSTALLED_JAR),)
	ALREADY_INSTALLED = 0
endif
ifeq ($(ALREADY_INSTALLED_LIB),)
	ALREADY_INSTALLED = 0
endif

# Try and prevent accidental makes (i.e. called manually, not from top-level Makefile)
checks:
	@if [ "$(LIBSUFFIX)" = "" ]; then \
	  (echo "Error: This Makefile is designed to be called from the main PRISM Makefile"; exit 1) \
	fi; 

../../lib/glpk_java:
	@(if [ "$(OSTYPE)" != "cygwin" ]; then \
	  (if [ "$(IS_SRC_CREATED)" = "" ]; then \
	   mkdir src ;fi) && \
	  export JAVA_HOME=$(JAVA_DIR) && \
	  (cd src/ && \
	   (if [ "$(ALREADY_DOWNLOADED)" = "" ]; then \
	    wget http://download.sourceforge.net/project/glpk-java/glpk-java/glpk-java-$(glpkjavavers)/libglpk-java-$(glpkjavavers).tar.gz && \
	    tar -xzf libglpk-java-$(glpkjavavers).tar.gz && \
	    mv libglpk-java-$(glpkjavavers) glpk_java; \
	   fi) && \
	   cd glpk_java/ && \
	   (if [ $(ALREADY_INSTALLED) = 0 ]; then \
	    patch -p1 < ../../libglpk_java_exact.patch && \
            export LD_LIBRARY_PATH=$(LD_LIBRARY_PATH):$(LDPATH) && \
            export CFLAGS=-I$(CFLAGSPATH) && \
            export SWIGFLAGS=-I$(SWIGFLAGSPATH) && \
	    ./autogen.sh > /dev/null && \
            ./configure > /dev/null && \
            make > /dev/null; \
	   fi) \
	  ) && cp --remove-destination src/glpk_java/swig/glpk-java.jar ../../lib/; \
	  cp --remove-destination src/glpk_java/swig/.libs/$(LIBPREFIX)glpk_java$(LIBSUFFIX) ../../lib/; \
	fi)

clean: checks
	rm -f ../../lib/$(LIBPREFIX)glpk_java$(LIBSUFFIX)
	rm -rf src/*

celan:	clean

#################################################
