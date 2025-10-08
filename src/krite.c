#include "krite.h"
#include "error.h"
#include "inline.h"
#include "internal.h"
#include "print.h"
#include "require.h"
#include "statistics.h"
#include "watch.h"

#include <inttypes.h>

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
  //imported is the largest eidx found, i.e. solver->import has entries at [eidx] for each eidx, with potentially holes inbetween
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
    kissat_custom_message (solver, 2, "Shweep reporting elit unit %d", tmp < 0 ? -elit : elit);
  }
  return num_units;
}

void kissat_report_dimacs (kissat * solver) {
  size_t imported = SIZE_STACK (solver->import);
  if (imported) imported--;
  kissat_custom_message (solver, 1, "Shweeper gathers units, only counting, not reporting yet");
  unsigned num_units = gather_units(solver, false);
  kissat_custom_message (solver, 1, "Shweeper gathered %i units",  num_units);
  bool do_report = solver->begin_report (solver->report_preprocess_state, imported, BINIRR_CLAUSES + num_units);
  if (!do_report)
    return;
  kissat_custom_message (solver, 1, "Shweeper reports final formula in kissat_report_dimacs");
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
  kissat_custom_message (solver, 1, "Shweeper second unit gather, now with reporting");
  unsigned now_num_units = gather_units(solver, true);
  kissat_custom_message (solver, 1, "Shweeper second, gathered %i units",  now_num_units);
  assert(now_num_units == num_units);
}

