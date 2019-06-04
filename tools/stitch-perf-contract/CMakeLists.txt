#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(stitch-perf-contract
  stitch-perf-contract.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_link_libraries(stitch-perf-contract -ldl ${KLEE_LIBS})

install(TARGETS stitch-perf-contract RUNTIME DESTINATION bin)
