#ifndef QUIET

#include "print.h"
#include "colors.h"
#include "handle.h"
#include "internal.h"

#include <inttypes.h>
#include <stdarg.h>
#include <string.h>

static inline int verbosity (kissat *solver) {
  if (!solver)
    return -1;
#ifdef LOGGING
  if (GET_OPTION (log))
    return 3;
#endif
#ifndef QUIET
  if (GET_OPTION (quiet))
    return -1;
  return GET_OPTION (verbose);
#else
  return 0;
#endif
}

void kissat_warning (kissat *solver, const char *fmt, ...) {
  if (verbosity (solver) < 0)
    return;
  TERMINAL (stdout, 1);
  fputs ("c ", stdout);
  COLOR (BOLD YELLOW);
  fputs ("warning:", stdout);
  COLOR (NORMAL);
  fputc (' ', stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
#ifdef NOPTIONS
  (void) solver;
#endif
}

void kissat_signal (kissat *solver, const char *type, int sig) {
  if (verbosity (solver) < 0)
    return;
  TERMINAL (stdout, 1);
  fputs ("c ", stdout);
  COLOR (BOLD RED);
  printf ("%s signal %d (%s)", type, sig, kissat_signal_name (sig));
  COLOR (NORMAL);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void print_message (const char *color, const char *fmt,
                           va_list *ap) {
  TERMINAL (stdout, 1);
  fputs ("c ", stdout);
  COLOR (color);
  vprintf (fmt, *ap);
  fputc ('\n', stdout);
  COLOR (NORMAL);
  fflush (stdout);
}

static void print_line (void) {
  fputs ("c\n", stdout);
  fflush (stdout);
}

int kissat_verbosity (kissat *solver) { return verbosity (solver); }

void kissat_message (kissat *solver, const char *fmt, ...) {
  if (verbosity (solver) < 0)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_message ("", fmt, &ap);
  va_end (ap);
}

void kissat_line (kissat *solver) {
  if (verbosity (solver) >= 0)
    print_line ();
}

void kissat_verbose (kissat *solver, const char *fmt, ...) {
  if (verbosity (solver) < 1)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_message (LIGHT_GRAY, fmt, &ap);
  va_end (ap);
}

void kissat_very_verbose (kissat *solver, const char *fmt, ...) {
  if (verbosity (solver) < 2)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_message (DARK_GRAY, fmt, &ap);
  va_end (ap);
}

void kissat_extremely_verbose (kissat *solver, const char *fmt, ...) {
  if (verbosity (solver) < 3)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_message (DARK_GRAY, fmt, &ap);
  va_end (ap);
}



void kissat_custom_message(kissat *solver, const char *fmt, ...) {
  if (GET_OPTION(mallob_custom_verbosity)<1) {
    return;
  }
  uint64_t mallob_solver_id = GET_OPTION(mallob_solver_id);
  uint64_t num_spaces = 15 * mallob_solver_id;

  // Add some spaces to the message to spacially distinguish the specific solver
  char new_fmt[1024];
  memset(new_fmt, ' ', num_spaces);
  new_fmt[num_spaces] = '\0';

  // Prepend [mallob_solver_id] to the format string
  char prefix[64];
  snprintf(prefix, sizeof(prefix), "[%" PRIu64 "] ", mallob_solver_id);

  strncat(new_fmt, prefix, sizeof(new_fmt) - strlen(new_fmt) - 1);
  strncat(new_fmt, fmt, sizeof(new_fmt) - strlen(new_fmt) - 1);

  va_list ap;
  va_start(ap, fmt);
  print_message (GREEN, new_fmt, &ap);
  va_end (ap);
}



void kissat_section (kissat *solver, const char *name) {
  if (verbosity (solver) < 0)
    return;
  TERMINAL (stdout, 1);
  if (solver->sectioned)
    fputs ("c\n", stdout);
  else
    solver->sectioned = true;
  fputs ("c ", stdout);
  COLOR (BLUE);
  fputs ("---- [ ", stdout);
  COLOR (BOLD BLUE);
  fputs (name, stdout);
  COLOR (NORMAL BLUE);
  fputs (" ] ", stdout);
  for (size_t i = strlen (name); i < 66; i++)
    fputc ('-', stdout);
  COLOR (NORMAL);
  fputs ("\nc\n", stdout);
  fflush (stdout);
}

void kissat_phase (kissat *solver, const char *name, uint64_t count,
                   const char *fmt, ...) {
  if (verbosity (solver) < 1)
    return;
  TERMINAL (stdout, 1);
  printf ("c ");
  if (solver->stable)
    COLOR (CYAN);
  else
    COLOR (BOLD CYAN);
  printf ("[%s", name);
  if (count != UINT64_MAX)
    printf ("-%" PRIu64, count);
  fputs ("] ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  COLOR (NORMAL);
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
int kissat_print_dummy_to_avoid_warning;
#endif
