#ifndef _clauseimport_h_INCLUDED
#define _clauseimport_h_INCLUDED
#include "kissat.h"

bool kissat_importing_redundant_clauses (kissat * solver);
void kissat_import_redundant_clauses (kissat * solver);

// bool swissat_importing_equivalences (kissat * solver);
// void swissat_import_equivalences (kissat * solver);

#endif