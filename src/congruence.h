#ifndef _congruence_h_INCLUDED
#define _congruence_h_INCLUDED

#include <stdbool.h>

struct kissat;
bool kissat_congruence (struct kissat *);
int kissat_mallob_congruencer(struct kissat *);
bool kissat_mallob_tightloop_congruence(struct kissat *);

#endif
