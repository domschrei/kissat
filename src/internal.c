#include "allocate.h"
#include "backtrack.h"
#include "error.h"
#include "search.h"
#include "import.h"
#include "inline.h"
#include "inlineframes.h"
#include "print.h"
#include "propsearch.h"
#include "require.h"
#include "resize.h"
#include "resources.h"
#include "clauseimport.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>

kissat *
kissat_init (void)
{
  kissat *solver = kissat_calloc (0, 1, sizeof *solver);
#ifndef NOPTIONS
  kissat_init_options (&solver->options);
#else
  kissat_init_options ();
#endif
#ifndef QUIET
  kissat_init_profiles (&solver->profiles);
#endif
  START (total);
  kissat_init_queue (solver);
  assert (INTERNAL_MAX_LIT < UINT_MAX);
  kissat_push_frame (solver, UINT_MAX);
  kissat_init_reap (solver, &solver->reap);
  solver->watching = true;
  solver->conflict.size = 2;
  solver->conflict.keep = true;
  solver->scinc = 1.0;
  solver->first_reducible = INVALID_REF;
  solver->last_irredundant = INVALID_REF;
  solver->rephased.last = 'O';
#ifndef NDEBUG
  kissat_init_checker (solver);
#endif

  solver->consume_clause_state = 0;
  solver->consume_clause_buffer = 0;
  solver->consume_clause_max_size = 0;
  solver->consume_clause = 0;

  solver->produce_clause_state = 0;
  solver->produce_clause = 0;
  solver->num_conflicts_at_last_import = 0;

  solver->initial_variable_phases = 0;
  solver->initial_variable_phases_len = 0;

  solver->num_imported_external_clauses = 0;
  solver->num_discarded_external_clauses = 0;

  solver->r_ee = 0;
  solver->r_ed = 0;
  solver->r_pb = 0;
  solver->r_ss = 0;
  solver->r_sw = 0;
  solver->r_tr = 0;
  solver->r_fx = 0;
  solver->r_ia = 0;

  return solver;
}

#define DEALLOC_GENERIC(NAME, ELEMENTS_PER_BLOCK) \
do { \
  const size_t block_size = ELEMENTS_PER_BLOCK * sizeof *solver->NAME; \
  kissat_dealloc (solver, solver->NAME, solver->size, block_size); \
  solver->NAME = 0; \
} while (0)

#define DEALLOC_VARIABLE_INDEXED(NAME) \
  DEALLOC_GENERIC (NAME, 1)

#define DEALLOC_LITERAL_INDEXED(NAME) \
  DEALLOC_GENERIC (NAME, 2)

#define RELEASE_LITERAL_INDEXED_STACKS(NAME,ACCESS) \
do { \
  for (all_stack (unsigned, IDX_RILIS, solver->active)) \
    { \
      const unsigned LIT_RILIS = LIT (IDX_RILIS); \
      const unsigned NOT_LIT_RILIS = NOT (LIT_RILIS); \
      RELEASE_STACK (ACCESS (LIT_RILIS)); \
      RELEASE_STACK (ACCESS (NOT_LIT_RILIS)); \
    } \
  DEALLOC_LITERAL_INDEXED (NAME); \
} while (0)

void
kissat_release (kissat * solver)
{
  kissat_require_initialized (solver);

  kissat_release_heap (solver, &solver->scores);
  kissat_release_heap (solver, &solver->schedule);

  kissat_release_clueue (solver, &solver->clueue);
  kissat_release_reap (solver, &solver->reap);

  kissat_release_phases (solver);
  kissat_release_cache (solver);
  RELEASE_STACK (solver->nonces);

  RELEASE_STACK (solver->export);
  RELEASE_STACK (solver->import);

  DEALLOC_VARIABLE_INDEXED (assigned);
  DEALLOC_VARIABLE_INDEXED (flags);
  DEALLOC_VARIABLE_INDEXED (links);

  DEALLOC_LITERAL_INDEXED (marks);
  DEALLOC_LITERAL_INDEXED (values);
  DEALLOC_LITERAL_INDEXED (watches);

  RELEASE_STACK (solver->import);
  RELEASE_STACK (solver->eliminated);
  RELEASE_STACK (solver->extend);
  RELEASE_STACK (solver->witness);
  RELEASE_STACK (solver->etrail);

  RELEASE_STACK (solver->vectors.stack);
  RELEASE_STACK (solver->delayed);

  RELEASE_STACK (solver->clause);
  RELEASE_STACK (solver->shadow);
#if defined(LOGGING) || !defined(NDEBUG)
  RELEASE_STACK (solver->resolvent);
#endif

  RELEASE_STACK (solver->arena);

  RELEASE_STACK (solver->units);
  RELEASE_STACK (solver->frames);
  RELEASE_STACK (solver->sorter);

  RELEASE_ARRAY (solver->trail, solver->size);

  RELEASE_STACK (solver->analyzed);
  RELEASE_STACK (solver->levels);
  RELEASE_STACK (solver->minimize);
  RELEASE_STACK (solver->poisoned);
  RELEASE_STACK (solver->promote);
  RELEASE_STACK (solver->removable);
  RELEASE_STACK (solver->shrinkable);
  RELEASE_STACK (solver->xorted[0]);
  RELEASE_STACK (solver->xorted[1]);

  RELEASE_STACK (solver->ranks);

  RELEASE_STACK (solver->antecedents[0]);
  RELEASE_STACK (solver->antecedents[1]);
  RELEASE_STACK (solver->gates[0]);
  RELEASE_STACK (solver->gates[1]);
  RELEASE_STACK (solver->resolvents);

#if !defined(NDEBUG) || !defined(NPROOFS)
  RELEASE_STACK (solver->added);
  RELEASE_STACK (solver->removed);
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  RELEASE_STACK (solver->original);
#endif

#ifndef QUIET
  RELEASE_STACK (solver->profiles.stack);
#endif

#ifndef NDEBUG
  kissat_release_checker (solver);
#endif
#if !defined(NDEBUG) && defined(METRICS)
  uint64_t leaked = solver->statistics.allocated_current;
  if (leaked)
    if (!getenv ("LEAK"))
      kissat_fatal ("internally leaking %" PRIu64 " bytes", leaked);
#endif

  kissat_free (0, solver, sizeof *solver);
}

void
kissat_reserve (kissat * solver, int max_var)
{
  kissat_require_initialized (solver);
  kissat_require (0 <= max_var,
		  "negative maximum variable argument '%d'", max_var);
  kissat_require (max_var <= EXTERNAL_MAX_VAR,
		  "invalid maximum variable argument '%d'", max_var);
  kissat_increase_size (solver, (unsigned) max_var);
}

int
kissat_get_option (kissat * solver, const char *name)
{
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_get (&solver->options, name);
#else
  (void) solver;
  return kissat_options_get (name);
#endif
}

int
kissat_set_option (kissat * solver, const char *name, int new_value)
{
#ifndef NOPTIONS
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_set (&solver->options, name, new_value);
#else
  return kissat_options_set (name, new_value);
#endif
#else
  (void) solver, (void) new_value;
  return kissat_options_get (name);
#endif
}

void
kissat_set_decision_limit (kissat * solver, unsigned limit)
{
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->decisions = true;
  assert (UINT64_MAX - limit >= statistics->decisions);
  limits->decisions = statistics->decisions + limit;
  LOG ("set decision limit to %" PRIu64 " after %u decisions",
       limits->decisions, limit);
}

void
kissat_set_conflict_limit (kissat * solver, unsigned limit)
{
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->conflicts = true;
  assert (UINT64_MAX - limit >= statistics->conflicts);
  limits->conflicts = statistics->conflicts + limit;
  LOG ("set conflict limit to %" PRIu64 " after %u conflicts",
       limits->conflicts, limit);
}

void
kissat_print_statistics (kissat * solver)
{
#ifndef QUIET
  kissat_require_initialized (solver);
  const int verbosity = kissat_verbosity (solver);
  if (verbosity < 0)
    return;
  if (GET_OPTION (profile))
    {
      kissat_section (solver, "profiling");
      kissat_profiles_print (solver);
    }
  const bool complete = GET_OPTION (statistics);
  kissat_section (solver, "statistics");
  const bool verbose = (complete || verbosity > 0);
  kissat_statistics_print (solver, verbose);
#ifndef NPROOFS
  if (solver->proof)
    {
      kissat_section (solver, "proof");
      kissat_print_proof_statistics (solver, verbose);
    }
#endif
#ifndef NDEBUG
  if (GET_OPTION (check) > 1)
    {
      kissat_section (solver, "checker");
      kissat_print_checker_statistics (solver, verbose);
    }
#endif
  kissat_section (solver, "resources");
  kissat_print_resources (solver);
#endif
  (void) solver;
}

void
kissat_add (kissat * solver, int elit)
{
  kissat_require_initialized (solver);
  kissat_require (!GET (searches), "incremental solving not supported");
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  const int checking = kissat_checking (solver);
  const bool logging = kissat_logging (solver);
  const bool proving = kissat_proving (solver);
#endif
  if (elit)
    {
      kissat_require_valid_external_internal (elit);
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
      if (checking || logging || proving)
	PUSH_STACK (solver->original, elit);
#endif
      unsigned ilit = kissat_import_literal (solver, elit);

      const mark mark = MARK (ilit);
      if (!mark)
	{
	  const value value = kissat_fixed (solver, ilit);
	  if (value > 0)
	    {
	      if (!solver->clause_satisfied)
		{
		  LOG ("adding root level satisfied literal %u(%d)@0=1",
		       ilit, elit);
		  solver->clause_satisfied = true;
		}
	    }
	  else if (value < 0)
	    {
	      LOG ("adding root level falsified literal %u(%d)@0=-1",
		   ilit, elit);
	      if (!solver->clause_shrink)
		{
		  solver->clause_shrink = true;
		  LOG ("thus original clause needs shrinking");
		}
	    }
	  else
	    {
	      MARK (ilit) = 1;
	      MARK (NOT (ilit)) = -1;
	      assert (SIZE_STACK (solver->clause) < UINT_MAX);
	      PUSH_STACK (solver->clause, ilit);
	    }
	}
      else if (mark < 0)
	{
	  assert (mark < 0);
	  if (!solver->clause_trivial)
	    {
	      LOG ("adding dual literal %u(%d) and %u(%d)",
		   NOT (ilit), -elit, ilit, elit);
	      solver->clause_trivial = true;
	    }
	}
      else
	{
	  assert (mark > 0);
	  LOG ("adding duplicated literal %u(%d)", ilit, elit);
	  if (!solver->clause_shrink)
	    {
	      solver->clause_shrink = true;
	      LOG ("thus original clause needs shrinking");
	    }
	}
    }
  else
    {
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
      const size_t offset = solver->offset_of_last_original_clause;
      size_t esize = SIZE_STACK (solver->original) - offset;
      int *elits = BEGIN_STACK (solver->original) + offset;
      assert (esize <= UINT_MAX);
#endif
      ADD_UNCHECKED_EXTERNAL (esize, elits);
      const size_t isize = SIZE_STACK (solver->clause);
      unsigned *ilits = BEGIN_STACK (solver->clause);
      assert (isize < (unsigned) INT_MAX);

      if (solver->inconsistent)
	LOG ("inconsistent thus skipping original clause");
      else if (solver->clause_satisfied)
	LOG ("skipping satisfied original clause");
      else if (solver->clause_trivial)
	LOG ("skipping trivial original clause");
      else
	{
	  kissat_activate_literals (solver, isize, ilits);

	  if (!isize)
	    {
	      if (solver->clause_shrink)
		LOG ("all original clause literals root level falsified");
	      else
		LOG ("found empty original clause");

	      if (!solver->inconsistent)
		{
		  LOG ("thus solver becomes inconsistent");
		  solver->inconsistent = true;
		  CHECK_AND_ADD_EMPTY ();
		  ADD_EMPTY_TO_PROOF ();
		}
	    }
	  else if (isize == 1)
	    {
	      unsigned unit = TOP_STACK (solver->clause);

	      if (solver->clause_shrink)
		LOGUNARY (unit, "original clause shrinks to");
	      else
		LOGUNARY (unit, "found original");

	      kissat_original_unit (solver, unit);

	      COVER (solver->level);
	      if (!solver->level)
		(void) kissat_search_propagate (solver);
	    }
	  else
	    {
	      reference res = kissat_new_original_clause (solver);

	      const unsigned a = ilits[0];
	      const unsigned b = ilits[1];

	      const value u = VALUE (a);
	      const value v = VALUE (b);

	      const unsigned k = u ? LEVEL (a) : UINT_MAX;
	      const unsigned l = v ? LEVEL (b) : UINT_MAX;

	      bool assign = false;

	      if (!u && v < 0)
		{
		  LOG ("original clause immediately forcing");
		  assign = true;
		}
	      else if (u < 0 && k == l)
		{
		  LOG ("both watches falsified at level @%u", k);
		  assert (v < 0);
		  assert (k > 0);
		  kissat_backtrack_without_updating_phases (solver, k - 1);
		}
	      else if (u < 0)
		{
		  LOG ("watches falsified at levels @%u and @%u", k, l);
		  assert (v < 0);
		  assert (k > l);
		  assert (l > 0);
		  assign = true;
		}
	      else if (u > 0 && v < 0)
		{
		  LOG ("first watch satisfied at level @%u "
		       "second falsified at level @%u", k, l);
		  assert (k <= l);
		}
	      else if (!u && v > 0)
		{
		  LOG ("first watch unassigned "
		       "second falsified at level @%u", l);
		  assign = true;
		}
	      else
		{
		  assert (!u);
		  assert (!v);
		}

	      if (assign)
		{
		  assert (solver->level > 0);

		  if (isize == 2)
		    {
		      assert (res == INVALID_REF);
		      kissat_assign_binary (solver, false, a, b);
		    }
		  else
		    {
		      assert (res != INVALID_REF);
		      clause *c = kissat_dereference_clause (solver, res);
		      kissat_assign_reference (solver, a, res, c);
		    }
		}
	    }
	}

#if !defined(NDEBUG) || !defined(NPROOFS)
      if (solver->clause_satisfied || solver->clause_trivial)
	{
#ifndef NDEBUG
	  if (checking > 1)
	    kissat_remove_checker_external (solver, esize, elits);
#endif
#ifndef NPROOFS
	  if (proving)
	    {
	      if (esize == 1)
		LOG ("skipping deleting unit from proof");
	      else
		kissat_delete_external_from_proof (solver, esize, elits);
	    }
#endif
	}
      else if (!solver->inconsistent && solver->clause_shrink)
	{
#ifndef NDEBUG
	  if (checking > 1)
	    {
	      kissat_check_and_add_internal (solver, isize, ilits);
	      kissat_remove_checker_external (solver, esize, elits);
	    }
#endif
#ifndef NPROOFS
	  if (proving)
	    {
	      kissat_add_lits_to_proof (solver, isize, ilits);
	      kissat_delete_external_from_proof (solver, esize, elits);
	    }
#endif
	}
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
      if (checking)
	{
	  LOGINTS (esize, elits, "saved original");
	  PUSH_STACK (solver->original, 0);
	  solver->offset_of_last_original_clause =
	    SIZE_STACK (solver->original);
	}
      else if (logging || proving)
	{
	  LOGINTS (esize, elits, "reset original");
	  CLEAR_STACK (solver->original);
	  solver->offset_of_last_original_clause = 0;
	}
#endif
      for (all_stack (unsigned, lit, solver->clause))
	  MARK (lit) = MARK (NOT (lit)) = 0;

      CLEAR_STACK (solver->clause);

      solver->clause_satisfied = false;
      solver->clause_trivial = false;
      solver->clause_shrink = false;
    }
}

int
kissat_solve (kissat * solver)
{
  kissat_require_initialized (solver);
  kissat_require (EMPTY_STACK (solver->clause),
		  "incomplete clause (terminating zero not added)");
  kissat_require (!GET (searches), "incremental solving not supported");
  return kissat_search (solver);
}

void
kissat_terminate (kissat * solver)
{
  kissat_require_initialized (solver);
  solver->termination.flagged = ~(unsigned) 0;
  assert (solver->termination.flagged);
}

void
kissat_set_terminate (kissat * solver, void *state, int (*terminate) (void *))
{
  solver->termination.terminate = 0;
  solver->termination.state = state;
  solver->termination.terminate = terminate;
}

int
kissat_value (kissat * solver, int elit)
{
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return 0;
  const import *const import = &PEEK_STACK (solver->import, eidx);
  if (!import->imported)
    return 0;
  value tmp;
  if (import->eliminated)
    {
      if (!solver->extended && !EMPTY_STACK (solver->extend))
	kissat_extend (solver);
      const unsigned eliminated = import->lit;
      tmp = PEEK_STACK (solver->eliminated, eliminated);
    }
  else
    {
      const unsigned ilit = import->lit;
      tmp = VALUE (ilit);
    }
  if (!tmp)
    return 0;
  if (elit < 0)
    tmp = -tmp;
  return tmp < 0 ? -elit : elit;
}

void kissat_set_clause_export_callback (kissat * solver, void *state, int *buffer, unsigned max_size, void (*consume) (void* state, int size, int glue)) 
{
  solver->consume_clause_state = state;
  solver->consume_clause_buffer = buffer;
  solver->consume_clause_max_size = max_size;
  solver->consume_clause = consume;
}

void kissat_set_clause_import_callback (kissat * solver, void *state, void (*produce) (void *state, int **clause, int *size, int *glue)) 
{
  solver->produce_clause_state = state;
  solver->produce_clause = produce;
}

struct kissat_statistics kissat_get_statistics (kissat * solver) 
{
  statistics *statistics = &solver->statistics;
  struct kissat_statistics stats_out;
  stats_out.propagations = statistics->propagations;
  stats_out.decisions = statistics->decisions;
  stats_out.conflicts = statistics->conflicts;
  stats_out.restarts = statistics->restarts;
  stats_out.imported = solver->num_imported_external_clauses;
  stats_out.discarded = solver->num_discarded_external_clauses;
  stats_out.r_ed = solver->r_ed;
  stats_out.r_ee = solver->r_ee;
  stats_out.r_fx = solver->r_fx;
  stats_out.r_pb = solver->r_pb;
  stats_out.r_ss = solver->r_ss;
  stats_out.r_sw = solver->r_sw;
  stats_out.r_tr = solver->r_tr;
  stats_out.r_tl = solver->r_tl;
  stats_out.r_ia = solver->r_ia;
  return stats_out;
}

bool kissat_importing_redundant_clauses (kissat * solver) 
{
  if (solver->produce_clause == 0) return false;
  if (solver->level != 0) return false;
  unsigned long conflicts = solver->statistics.conflicts;
  if (conflicts == solver->num_conflicts_at_last_import) return false;
  return true;
}

void kissat_import_redundant_clauses (kissat * solver) 
{
  int *buffer = 0;
  int size = 0;
  int glue = 0;
  solver->num_conflicts_at_last_import = solver->statistics.conflicts;

  while (true) {
    solver->produce_clause (solver->produce_clause_state, &buffer, &size, &glue);

    //printf("KISSAT TRY_LEARN size=%i\n", size);

    if (size <= 0 || buffer == 0) {
      break; // No more clauses
    }

    // Literal flags to possibly check against:
    // bool eliminate:1; /* set by kissat_mark_removed_literal */
    //!bool eliminated:1; /*do not import*/
    // bool fixed:1; /*can be handled explicitly*/
    // bool probe:1; /*could be fine*/
    // bool subsume:1; /* set by kissat_mark_added_literal, also when importing the clause */
    // bool sweep:1; /*could be fine*/
    // bool transitive:1; /*seems to be used nowhere*/

    // Analyze each of the literals
    bool okToImport = true;
    unsigned effectiveSize = 0;
    for (unsigned i = 0; i < (unsigned)size; i++) {
      int elit = buffer[i];
      if (!VALID_EXTERNAL_LITERAL (elit)) {
	solver->r_ed++;
        okToImport = false;
        break;
      }
      const unsigned ilit = kissat_import_literal (solver, elit);
      if (!VALID_INTERNAL_LITERAL (ilit)) {
	solver->r_ed++;
        okToImport = false;
        break;
      }
      const unsigned idx = IDX (ilit);
      flags *flags = FLAGS (idx);
      if (flags->fixed) {
        const value value = kissat_fixed (solver, ilit);
        if (value > 0) {
          // Literal is fixed as positive: drop entire clause
          solver->r_fx++;
          okToImport = false;
          break;
        } else if (value < 0) {
          // Literal is fixed as negated: drop this literal
          buffer[i] = 0;
        } else {
          // Fixed, but neither positive nor negated? Drop clause to be safe
          solver->r_fx++;
          okToImport = false;
          break;
        }
      } else if (!flags->active || flags->eliminated) {
        // Literal in an invalid state for importing this clause
        okToImport = false;

        if (!flags->active) solver->r_ia++;
        if (flags->eliminate) solver->r_ee++;
        if (flags->eliminated) solver->r_ed++;
        if (flags->probe) solver->r_pb++;
        if (flags->subsume) solver->r_ss++;
        if (flags->sweep) solver->r_sw++;
        if (flags->transitive) solver->r_tr++;

        break;
      } else {
        // This literal is fine
        effectiveSize++;
      }
    }

    // Drop clause, or no valid literals?
    if (!okToImport || effectiveSize == 0) {
      solver->num_discarded_external_clauses++;
      continue;
    }

    if (effectiveSize == 1) {
      // Unit clause!

      // Get literal
      unsigned i = 0; while (buffer[i] == 0) i++;
      const unsigned lit = kissat_import_literal (solver, buffer[i]);
      assert (VALID_INTERNAL_LITERAL (lit));

      // Learn unit clause
      //printf("KISSAT LEARN %i\n", lit);
      kissat_learned_unit (solver, lit);
      solver->num_imported_external_clauses++;
      continue;
    }

    // Larger clause of size >= 2

    if (effectiveSize > CAPACITY_STACK (solver->clause)) {
      // Clause is too large
      solver->r_tl++;
      solver->num_discarded_external_clauses++;
      continue;
    }

    // Write clause into internal stack
    assert (EMPTY_STACK (solver->clause));
    //printf("KISSAT LEARN");
    for (unsigned i = 0; i < (unsigned)size; i++) {
      if (buffer[i] == 0) continue;
      const unsigned lit = kissat_import_literal (solver, buffer[i]);
      assert (VALID_INTERNAL_LITERAL (lit));
      PUSH_STACK (solver->clause, lit);
      //printf(" %i", lit);
    }
    //printf("\n");
    assert (SIZE_STACK (solver->clause) == effectiveSize);

    // Learn clause
    const reference ref = kissat_new_redundant_clause (solver, glue);

    if (ref != INVALID_REF) {
      // Valid reference => Long clause (size>2) 
      assert (effectiveSize > 2);
      clause *c = kissat_dereference_clause (solver, ref);
      c->used = 1 + (glue <= GET_OPTION (tier2));
    }

    // Clear internal stack for the next learnt clause
    CLEAR_STACK (solver->clause);
    solver->num_imported_external_clauses++;
  }

  //printf("KISSAT next import @ %lu conflicts\n", solver->num_conflicts_at_last_import);
}

void kissat_set_initial_variable_phases (kissat * solver, signed char *lookup, int size)
{
  solver->initial_variable_phases = lookup;
  solver->initial_variable_phases_len = size;
}
