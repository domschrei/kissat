#include "krite.h"
#include "inline.h"
#include "internal.h"
#include "statistics.h"
#include "watch.h"
#include "error.h"
#include "require.h"
#include "print.h"

#include <inttypes.h>
#include <string.h>

void kissat_write_dimacs (kissat *solver, FILE *file) {
  size_t imported = SIZE_STACK (solver->import);
  if (imported)
    imported--;
  fprintf (file, "p cnf %zu %" PRIu64 "\n", imported, BINIRR_CLAUSES);
  assert (solver->watching);
  if (solver->watching) {
    for (all_literals (ilit))
      for (all_binary_blocking_watches (watch, WATCHES (ilit)))
        if (watch.type.binary) {
          const unsigned iother = watch.binary.lit;
          if (iother < ilit)
            continue;
          const int elit = kissat_export_literal (solver, ilit);
          const int eother = kissat_export_literal (solver, iother);
          fprintf (file, "%d %d 0\n", elit, eother);
        }
  } else {
    for (all_literals (ilit))
      for (all_binary_large_watches (watch, WATCHES (ilit)))
        if (watch.type.binary) {
          const unsigned iother = watch.binary.lit;
          if (iother < ilit)
            continue;
          const int elit = kissat_export_literal (solver, ilit);
          const int eother = kissat_export_literal (solver, iother);
          fprintf (file, "%d %d 0\n", elit, eother);
        }
  }
  for (all_clauses (c))
    if (!c->garbage && !c->redundant) {
      for (all_literals_in_clause (ilit, c)) {
        const int elit = kissat_export_literal (solver, ilit);
        fprintf (file, "%d ", elit);
      }
      fputs ("0\n", file);
    }
}

unsigned gather_units (kissat * solver, bool report) {
  size_t imported = SIZE_STACK (solver->import);
  if (imported) imported--;
  unsigned num_units = 0;
  for (int elit = 1; elit <= imported; elit++) {
    kissat_require_valid_external_internal (elit);
    const unsigned eidx = ABS (elit);
    if (eidx >= SIZE_STACK (solver->import)) continue;
    const import *const import = &PEEK_STACK (solver->import, eidx);
    if (!import->imported) continue;
    value tmp = 0;
    if (!import->eliminated) {
      const unsigned ilit = import->lit;
      tmp = VALUE (ilit);
    }
    if (!tmp) continue;
    num_units += 1;
    if (!report) continue;
    if (elit < 0) tmp = -tmp;
    solver->report_preprocessed_lit (solver->report_preprocess_state, tmp < 0 ? -elit : elit);
    solver->report_preprocessed_lit (solver->report_preprocess_state, 0);
  }
  return num_units;
}

void kissat_report_dimacs (kissat * solver) {
  size_t imported = SIZE_STACK (solver->import);
  //Need to subtract one because the first variable on the import stack is a dummy.
  //such that stack index 1 correspond to variable 1
  if (imported) imported--;
  if (GET_OPTION(mallob_sweeping) && solver->inconsistent) {
    kissat_custom_message (solver, 1, "SWEEPER will not report dimacs because it is already UNSAT");
    return;
  }
  unsigned num_units = gather_units(solver, false);
  if (num_units != SIZE_STACK(solver->units)) {
    kissat_custom_message (solver, 1, "WARN: SWEEPER num_units %i different to stack->units %i ", num_units, SIZE_STACK(solver->units));
  }
  bool do_report = solver->begin_report (solver->report_preprocess_state, imported, BINIRR_CLAUSES + num_units);
  if (!do_report) {
    kissat_custom_message (solver, 1, "SWEEPER should not report dimacs, told so by Mallob callback");
    return;
  }
  kissat_custom_message (solver, 1, "SWEEPER reports final formula via kissat_report_dimacs");
  assert (solver->watching);
  if (solver->watching) {
    for (all_literals (ilit))
      for (all_binary_blocking_watches (watch, WATCHES (ilit)))
        if (watch.type.binary) {
          const unsigned iother = watch.binary.lit;
          if (iother < ilit)
            continue;
          const int elit = kissat_export_literal (solver, ilit);
          const int eother = kissat_export_literal (solver, iother);
          solver->report_preprocessed_lit (solver->report_preprocess_state, elit);
          solver->report_preprocessed_lit (solver->report_preprocess_state, eother);
          solver->report_preprocessed_lit (solver->report_preprocess_state, 0);
        }
  } else {
    for (all_literals (ilit))
      for (all_binary_large_watches (watch, WATCHES (ilit)))
        if (watch.type.binary) {
          const unsigned iother = watch.binary.lit;
          if (iother < ilit)
            continue;
          const int elit = kissat_export_literal (solver, ilit);
          const int eother = kissat_export_literal (solver, iother);
          solver->report_preprocessed_lit (solver->report_preprocess_state, elit);
          solver->report_preprocessed_lit (solver->report_preprocess_state, eother);
          solver->report_preprocessed_lit (solver->report_preprocess_state, 0);
        }
  }
  for (all_clauses (c))
    if (!c->garbage && !c->redundant) {
      for (all_literals_in_clause (ilit, c)) {
        const int elit = kissat_export_literal (solver, ilit);
          solver->report_preprocessed_lit (solver->report_preprocess_state, elit);
      }
      solver->report_preprocessed_lit (solver->report_preprocess_state, 0);
    }
  if (num_units == 0) return;
  unsigned now_num_units = gather_units(solver, true);
  assert(now_num_units == num_units);
}

