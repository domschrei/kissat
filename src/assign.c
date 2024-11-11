#include "assign.h"
#include "inline.h"
#include "inlineassign.h"
#include "logging.h"
#include "clauseexport.h"

#include <limits.h>

void kissat_assign_unit (kissat *solver, unsigned lit, const char *reason) {
  kissat_assign (solver, solver->probing, 0, false, lit, UNIT_REASON);
  LOGUNARY (lit, "assign %s %s", LOGLIT (lit), reason);
#ifndef LOGGING
  (void) reason;
#endif
}

void learned_unit (kissat *solver, unsigned lit, bool export) {
  kissat_assign_unit (solver, lit, "learned reason");
  CHECK_AND_ADD_UNIT (lit);
  ADD_UNIT_TO_PROOF (lit);
  if (export) kissat_export_redundant_clause (solver, 1, 1, &lit);
}

void kissat_learned_unit (kissat *solver, unsigned lit) {
  learned_unit(solver, lit, true);
}

void kissat_learned_unit_from_import (kissat *solver, unsigned lit) {
  learned_unit(solver, lit, false);
}

void kissat_original_unit (kissat *solver, unsigned lit) {
  kissat_assign_unit (solver, lit, "original reason");
}

void kissat_assign_decision (kissat *solver, unsigned lit) {
  kissat_assign (solver, solver->probing, solver->level, false, lit,
                 DECISION_REASON);
  LOG ("assign %s decision", LOGLIT (lit));
}

void kissat_assign_binary (kissat *solver, unsigned lit, unsigned other) {
  assert (VALUE (other) < 0);
  assigned *assigned = solver->assigned;
  const unsigned other_idx = IDX (other);
  struct assigned *a = assigned + other_idx;
  unsigned level = a->level;
  if (GET_OPTION (jumpreasons) && level && a->binary) {
    LOGBINARY (lit, other, "jumping %s reason", LOGLIT (lit));
    INC (jumped_reasons);
    other = a->reason;
  }
  kissat_assign (solver, solver->probing, a->level, true, lit, other);
  LOGBINARY (lit, other, "assign %s reason", LOGLIT (lit));
}

void kissat_assign_reference (kissat *solver, unsigned lit, reference ref,
                              clause *reason) {
  assert (reason == kissat_dereference_clause (solver, ref));
  assigned *assigned = solver->assigned;
  value *values = solver->values;
  const unsigned level =
      kissat_assignment_level (solver, values, assigned, lit, reason);
  assert (level <= solver->level);
  assert (ref != DECISION_REASON);
  assert (ref != UNIT_REASON);
  kissat_assign (solver, solver->probing, level, false, lit, ref);
  LOGREF (ref, "assign %s reason", LOGLIT (lit));
}
