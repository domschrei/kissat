#ifndef _sweep_h_INCLUDED
#define _sweep_h_INCLUDED

#include <stdbool.h>

struct kissat;
bool kissat_sweep (struct kissat *);

int kissat_mallob_shweep(struct kissat *);

int kissat_mallob_shweep_just_import(struct kissat *);

int kissat_pure_sequential_sweeping(struct kissat *);

int kissat_mallob_distributed_sweep_multiple_iterations(struct kissat *);

#endif
