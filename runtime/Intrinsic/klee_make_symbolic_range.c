//===-- klee_make_symbolic_range.c ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <assert.h>
#include <klee/klee.h>

void klee_make_symbolic_range(void* addr, size_t offset, size_t nbytes, const char* name) {
        assert(addr != NULL && "Must pass a valid addr");
        assert(name != NULL && "Must pass a valid name");

        if(nbytes == 0)
                return;

        void* start = addr + offset;
        klee_check_memory_access(start, nbytes);

        void* symbolic_data = malloc(nbytes);
        klee_make_symbolic(symbolic_data, nbytes, name);
        memcpy(start, symbolic_data, nbytes);
        free(symbolic_data);
}
