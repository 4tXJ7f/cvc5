###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

find_package(ANTLR3 3.4 REQUIRED)

# Java runtime is required for ANTLR
find_package(Java COMPONENTS Runtime REQUIRED)

#-----------------------------------------------------------------------------#
# libcvc5parser source files

set(libcvc5parser_src_files
  antlr_input.cpp
  antlr_input.h
  antlr_input_imports.cpp
  antlr_line_buffered_input.cpp
  antlr_line_buffered_input.h
  bounded_token_buffer.cpp
  bounded_token_buffer.h
  bounded_token_factory.cpp
  bounded_token_factory.h
  input.cpp
  input.h
  line_buffer.cpp
  line_buffer.h
  parse_op.cpp
  parse_op.h
  parser.cpp
  parser.h
  parser_builder.cpp
  parser_builder.h
  parser_exception.h
  smt2/smt2.cpp
  smt2/smt2.h
  smt2/smt2_input.cpp
  smt2/smt2_input.h
  smt2/sygus_input.cpp
  smt2/sygus_input.h
  tptp/TptpLexer.c
  tptp/TptpParser.c
  tptp/tptp.cpp
  tptp/tptp.h
  tptp/tptp_input.cpp
  tptp/tptp_input.h
)

#-----------------------------------------------------------------------------#
# Generate parsers for all supported languages

foreach(lang Smt2 Tptp)
  string(TOLOWER ${lang} lang_dir)
  file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir})
  add_custom_command(
    OUTPUT
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.c
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.h
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.c
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.h
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}.tokens
    COMMAND
      ${ANTLR3_COMMAND}
        ${CMAKE_CURRENT_SOURCE_DIR}/${lang_dir}/${lang}.g
        -fo ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}
    DEPENDS
      ${lang_dir}/${lang}.g
  )
  set(gen_src_files
    ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.c
    ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.c)

  # Tell cmake that generated source files are actually c++ files
  set_source_files_properties(${gen_src_files} PROPERTIES LANGUAGE CXX)
  set_source_files_properties(${gen_src_files} PROPERTIES GENERATED TRUE)

  # We don't want to enable -Wall for code generated by ANTLR.
  set(GEN_SRC_FLAGS "")
  check_cxx_compiler_flag("-Wall" HAVE_CXX_FLAGWall)
  if(HAVE_CXX_FLAGWall)
    set(GEN_SRC_FLAGS "${GEN_SRC_FLAGS} -Wno-all")
  endif()
  check_cxx_compiler_flag("-Werror" HAVE_CXX_FLAGWerror)
  if(HAVE_CXX_FLAGWerror)
    set(GEN_SRC_FLAGS "${GEN_SRC_FLAGS} -Wno-error")
  endif()
  set_source_files_properties(
    ${gen_src_files} PROPERTIES COMPILE_FLAGS "${GEN_SRC_FLAGS}")

  # Add generated source files to the parser source files
  list(APPEND libcvc5parser_src_files ${gen_src_files})
endforeach()

#-----------------------------------------------------------------------------#
# libcvc5parser configuration

add_library(cvc5parser-objs OBJECT ${libcvc5parser_src_files})
set_target_properties(cvc5parser-objs PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_compile_definitions(cvc5parser-objs PUBLIC -D__BUILDING_CVC5PARSERLIB -Dcvc5_obj_EXPORTS)

add_dependencies(cvc5parser-objs ANTLR3)
target_include_directories(cvc5parser-objs PRIVATE ${ANTLR3_INCLUDE_DIR})

add_library(cvc5parser $<TARGET_OBJECTS:cvc5parser-objs>)
if(BUILD_SHARED_LIBS)
  set_target_properties(cvc5parser PROPERTIES SOVERSION ${CVC5_SOVERSION})
endif()

set_target_properties(cvc5parser PROPERTIES OUTPUT_NAME cvc5parser)
target_link_libraries(cvc5parser PRIVATE cvc5)
target_link_libraries(cvc5parser PRIVATE ANTLR3)

install(TARGETS cvc5parser-objs cvc5parser
  EXPORT cvc5-targets
  DESTINATION ${CMAKE_INSTALL_LIBDIR})

# The generated lexer/parser files define some functions as
# __declspec(dllexport) via the ANTLR3_API macro, which leads to lots of
# unresolved symbols when linking against libcvc5parser.
# -Wl,--export-all-symbols makes sure that all symbols are exported when
# building a DLL.
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  set_target_properties(cvc5parser-objs
    PROPERTIES LINK_FLAGS "-Wl,--export-all-symbols")
endif()
