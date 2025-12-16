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


void shweep_export_equivalence(kissat *solver, unsigned lit, unsigned other) {
  if (!solver->shweep_export_eq_callback) return;
  //Dont have any variable deletion/addition/renaming in shweep,
  //so we can directly work with internal literals, no need to convert to external representation
  solver->shweep_export_eq_buffer[0] = lit;
  solver->shweep_export_eq_buffer[1] = other;
  solver->shweep_export_eq_callback (solver->shweep_mallob_KissatState);

}

void shweep_export_unit(kissat *solver, unsigned lit) {
  if (!solver->shweep_export_unit_callback) return;
  solver->shweep_export_unit_callback (solver->shweep_mallob_KissatState, lit);

}
