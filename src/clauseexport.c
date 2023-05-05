
#include "internal.h"
#include "inline.h"
#include "utilities.h"

void kissat_export_redundant_clause (kissat * solver, unsigned glue, unsigned size, unsigned *lits) {
  if (!solver->consume_clause) return;
  if (size > solver->consume_clause_max_size) return;
  glue = MAX(glue, 1);
  glue = MIN(glue, size-1);
  // Export clause.
  for (unsigned i = 0; i < size; i++) {
    // Externalize each literal
    const unsigned ilit = lits[i];
    const int elit = kissat_export_literal (solver, ilit);
    solver->consume_clause_buffer[i] = elit;
  }
  // Execute learnt clause callback
  solver->consume_clause (solver->consume_clause_state, size, glue);
}
