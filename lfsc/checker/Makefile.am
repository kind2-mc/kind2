# Use GCC instead of Clang on mac
# CC = gcc-mp-5
# CXX = g++-mp-5

AM_CXXFLAGS = -Wall -Wno-deprecated #-Wl,-stack_size -Wl,1312D000
LDFLAGS = #-Wl,--stack,1312D000

bin_PROGRAMS = lfsc-checker

lfsc_checker_SOURCES = \
	main.cpp
lfsc_checker_LDADD = \
	@builddir@/liblfsc_checker.la

noinst_LTLIBRARIES = liblfsc_checker.la

liblfsc_checker_la_SOURCES = \
	check.cpp \
	check.h \
	chunking_memory_management.h \
	code.cpp \
	code.h \
	expr.cpp \
	expr.h \
	libwriter.cpp \
	libwriter.h \
	position.h \
	print_smt2.cpp \
	print_smt2.h \
	scccode.cpp \
	scccode.h \
	sccwriter.cpp \
	sccwriter.h \
	trie.cpp \
	trie.h
