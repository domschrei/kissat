#include "sweep.h"
#include "dense.h"
#include "inline.h"
#include "kitten.h"
#include "logging.h"
#include "print.h"
#include "promote.h"
#include "propdense.h"
#include "proprobe.h"
#include "random.h"
#include "rank.h"
#include "report.h"
#include "terminate.h"

#include "import.h" //currently not needed for shweeping as we directly share internal variables

#include <inttypes.h>
#include <string.h>

#include "clauseexport.h" //export stuff during shweeping
#include "substitute.h" //at the end of shweeping

/**
 * Overview of all methods
static int sweep_solve (sweeper *sweeper) {
void  x   set_kitten_ticks_limit (sweeper *sweeper) {
bool  x   kitten_ticks_limit_hit (sweeper *sweeper, const char *when) {
void      init_sweeper (kissat *solver, sweeper *sweeper) {
unsig     release_sweeper (sweeper *sweeper) {
void      clear_sweeper (sweeper *sweeper) {
unsig x   sweep_repr (sweeper *sweeper, unsigned lit) {
void  x   add_literal_to_environment (sweeper *sweeper, unsigned depth,
void  x   sweep_clause (sweeper *sweeper, unsigned depth) {
void  x   sweep_binary (sweeper *sweeper, unsigned depth, unsigned lit,
void  x   sweep_reference (sweeper *sweeper, unsigned depth,
void      save_core_clause (void *state, bool learned, size_t size,
void      add_core (sweeper *sweeper, unsigned core_idx) {
void      save_core (sweeper *sweeper, unsigned core) {
void      clear_core (sweeper *sweeper, unsigned core_idx) {
void      save_add_clear_core (sweeper *sweeper) {
void      init_backbone_and_partition (sweeper *sweeper) {
void      sweep_empty_clause (sweeper *sweeper) {
void  x   sweep_refine_partition (sweeper *sweeper) {
void  x   sweep_refine_backbone (sweeper *sweeper) {
void  x   sweep_refine (sweeper *sweeper) {
void  x   flip_backbone_literals (struct sweeper *sweeper) {
bool  x   sweep_backbone_candidate (sweeper *sweeper, unsigned lit) {
void      add_binary (kissat *solver, unsigned lit, unsigned other) {
bool  x   scheduled_variable (sweeper *sweeper, unsigned idx) {
void  x   schedule_inner (sweeper *sweeper, unsigned idx) {
void  x   schedule_outer (sweeper *sweeper, unsigned idx) {
unsig x   next_scheduled (sweeper *sweeper) {
void      substitute_connected_clauses (sweeper *sweeper, unsigned lit,
void      sweep_remove (sweeper *sweeper, unsigned lit) {
void      flip_partition_literals (struct sweeper *sweeper) {
bool      sweep_equivalence_candidates (sweeper *sweeper, unsigned lit,
const char *sweep_variable (sweeper *sweeper, unsigned idx) {
bool      scheduable_variable (sweeper *sweeper, unsigned idx,
unsig     schedule_all_other_not_scheduled_yet (sweeper *sweeper) {
unsig     reschedule_previously_remaining (sweeper *sweeper) {
unsig     incomplete_variables (sweeper *sweeper) {
void      mark_incomplete (sweeper *sweeper) {
unsig     schedule_sweeping (sweeper *sweeper) {
void      unschedule_sweeping (sweeper *sweeper, unsigned swept,
*/


const int V1_INFO_SWEEP = 1;
const int V2_VERB_SWEEP = 2;
const int V3_VVERB_SWEEP = 3;
const int V4_UVERB_SWEEP = 4;

struct sweeper {
  kissat *solver;
  unsigned *depths;
  unsigned *reprs;
  unsigned *next, *prev;
  unsigned first, last;
  unsigned encoded;
  unsigned save;
  unsigneds vars;
  references refs;
  unsigneds clause;
  unsigneds backbone;
  unsigneds partition;
  unsigneds core[2];
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;

  //For Mallob Shweep
  bool initialized;  //a guard against very early stealing attempts, where this solver is not even fully initialized yet
  unsigned *work;     //Variables scheduled for sweeping on this solver
  unsigneds RESWEEP;  //Local Equivalences found, for quick re-sweeping on them
  int work_end;    //size of the allocated work array.
  int work_head;   //index of the currently next scheduled variable in work
  int max_work_left; //a second approximation of how much work is left, updated when getting stolen
  bool just_imported_eqs;
  bool shweep_terminated;

  bool debug_singlethread_created_work;

  unsigned skipped_bc_done;
  unsigned stumbled_units;
};

typedef struct sweeper sweeper;

static int sweep_solve (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  kitten *kitten = solver->kitten;
  kitten_randomize_phases (kitten);
  INC (sweep_solved);
  int res = kitten_solve (kitten);
  if (res == 10)
    INC (sweep_sat);
  if (res == 20)
    INC (sweep_unsat);
  return res;
}

/*
 * Update the remaining kitten ticks
 */
static void set_kitten_ticks_limit (sweeper *sweeper) {
  uint64_t remaining = 0;
  kissat *solver = sweeper->solver;
  if (solver->statistics.kitten_ticks < sweeper->limit.ticks)
    remaining = sweeper->limit.ticks - solver->statistics.kitten_ticks;
  LOG ("'kitten_ticks' remaining %" PRIu64, remaining);
  kitten_set_ticks_limit (solver->kitten, remaining);
}


/**
 * Check whether kitten limit is reached
 */
static bool kitten_ticks_limit_hit (sweeper *sweeper, const char *when) {
  kissat *solver = sweeper->solver;
  if (solver->statistics.kitten_ticks >= sweeper->limit.ticks) {
    LOG ("'kitten_ticks' limit of %" PRIu64 " ticks hit after %" PRIu64
         " ticks during %s",
         sweeper->limit.ticks, solver->statistics.kitten_ticks, when);
    return true;
  }
#ifndef LOGGING
  (void) when;
#endif
  return false;
}



/** Initialize arrays and stacks.
Arrays:
  depths[idx]
  reprs[lit]
  prev[idx]
  next[idx]
Stacks:
  vars
  refs
  clause
  backbone
  partition
  core[0]
  core[1]
Kitten:
  Some kitten initialization.
**/
static void init_sweeper (kissat *solver, sweeper *sweeper) {
  solver->sweeper = sweeper; //Mallob Shweep: Kissat must also know about its sweeper
  sweeper->solver = solver;
  sweeper->encoded = 0;
  CALLOC (sweeper->depths, VARS);
  NALLOC (sweeper->reprs, LITS);
  for (all_literals (lit))
    sweeper->reprs[lit] = lit;
  NALLOC (sweeper->prev, VARS);
  memset (sweeper->prev, 0xff, VARS * sizeof *sweeper->prev);
  NALLOC (sweeper->next, VARS);
  memset (sweeper->next, 0xff, VARS * sizeof *sweeper->next);
#ifndef NDEBUG
  for (all_variables (idx))
    assert (sweeper->prev[idx] == INVALID_IDX);
  for (all_variables (idx))
    assert (sweeper->next[idx] == INVALID_IDX);
#endif
  sweeper->first = sweeper->last = INVALID_IDX;
  INIT_STACK (sweeper->vars);
  INIT_STACK (sweeper->refs);
  INIT_STACK (sweeper->clause);
  INIT_STACK (sweeper->backbone);
  INIT_STACK (sweeper->partition);
  INIT_STACK (sweeper->core[0]);
  INIT_STACK (sweeper->core[1]);
  assert (!solver->kitten);
  solver->kitten = kitten_embedded (solver);
  kitten_track_antecedents (solver->kitten);
  kissat_enter_dense_mode (solver, 0);
  kissat_connect_irredundant_large_clauses (solver);

  unsigned completed = solver->statistics.sweep_completed;
  const unsigned max_completed = 32;
  if (completed > max_completed)
    completed = max_completed;

  uint64_t vars_limit = GET_OPTION (sweepvars);
  vars_limit <<= completed;
  const unsigned max_vars_limit = GET_OPTION (sweepmaxvars);
  if (vars_limit > max_vars_limit)
    vars_limit = max_vars_limit;
  sweeper->limit.vars = vars_limit;
  kissat_extremely_verbose (solver, "sweeper variable limit %u",
                            sweeper->limit.vars);

  uint64_t depth_limit = solver->statistics.sweep_completed;
  depth_limit += GET_OPTION (sweepdepth);
  const unsigned max_depth = GET_OPTION (sweepmaxdepth);
  if (depth_limit > max_depth)
    depth_limit = max_depth;
  sweeper->limit.depth = depth_limit;
  kissat_extremely_verbose (solver, "sweeper depth limit %u",
                            sweeper->limit.depth);

  uint64_t clause_limit = GET_OPTION (sweepclauses);
  clause_limit <<= completed;
  const unsigned max_clause_limit = GET_OPTION (sweepmaxclauses);
  if (clause_limit > max_clause_limit)
    clause_limit = max_clause_limit;
  sweeper->limit.clauses = clause_limit;
  kissat_extremely_verbose (solver, "sweeper clause limit %u",
                            sweeper->limit.clauses);

  if (GET_OPTION (sweepcomplete)) {
    sweeper->limit.ticks = UINT64_MAX;
    kissat_extremely_verbose (solver, "unlimited sweeper ticks limit");
  } else {
    SET_EFFORT_LIMIT (ticks_limit, sweep, kitten_ticks);
    sweeper->limit.ticks = ticks_limit;
  }
  set_kitten_ticks_limit (sweeper);

  if (GET_OPTION (mallob_is_shweeper)) {
    INIT_STACK (sweeper->RESWEEP);
    sweeper->work_head=0;
    sweeper->work_end=0;
    sweeper->skipped_bc_done=0;
    sweeper->stumbled_units=0;
    sweeper->just_imported_eqs=false;
    sweeper->shweep_terminated=false;
    sweeper->debug_singlethread_created_work=false;
    sweeper->max_work_left=0;
    sweeper->initialized=true;
    //we don't allocate the work[] array, that will be allocated by Mallob/C++ and we only operate on it
  }
}

static unsigned release_sweeper (sweeper *sweeper) {
  kissat *solver = sweeper->solver;

  unsigned merged = 0;
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    if (sweeper->reprs[lit] != lit)
      merged++;
  }
  DEALLOC (sweeper->depths, VARS);
  DEALLOC (sweeper->reprs, LITS);
  DEALLOC (sweeper->prev, VARS);
  DEALLOC (sweeper->next, VARS);
  RELEASE_STACK (sweeper->vars);
  RELEASE_STACK (sweeper->refs);
  RELEASE_STACK (sweeper->clause);
  RELEASE_STACK (sweeper->backbone);
  RELEASE_STACK (sweeper->partition);
  RELEASE_STACK (sweeper->core[0]);
  RELEASE_STACK (sweeper->core[1]);
  kitten_release (solver->kitten);
  solver->kitten = 0;
  kissat_resume_sparse_mode (solver, false, 0);

  //When doing Mallob Shared Sweeping
  if (GET_OPTION (mallob_is_shweeper)) {
    RELEASE_STACK (sweeper->RESWEEP);
    solver->sweeper = 0;

    if (! solver->shweep_search_work_callback) {
      //this dealloc is only relevant for the single-threaded debugging case, where kissat allocates work[] itself
      //in the normal use cases, work[] is not managed by kissat, but by mallob
      DEALLOC(sweeper->work, VARS);
    }
  }

  //Maybe also free the solver->sweeper itself?

  return merged;
}

static void clear_sweeper (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("clearing sweeping environment");
  kitten_clear (solver->kitten);
  kitten_track_antecedents (solver->kitten);
  for (all_stack (unsigned, idx, sweeper->vars)) {
    assert (sweeper->depths[idx]);
    sweeper->depths[idx] = 0;
  }
  CLEAR_STACK (sweeper->vars);
  for (all_stack (reference, ref, sweeper->refs)) {
    clause *c = kissat_dereference_clause (solver, ref);
    assert (c->swept);
    c->swept = false;
  }
  CLEAR_STACK (sweeper->refs);
  CLEAR_STACK (sweeper->backbone);
  CLEAR_STACK (sweeper->partition);
  sweeper->encoded = 0;
  set_kitten_ticks_limit (sweeper);
}


/**
 * Return representative literal of lit
 * If multiple steps where needed, shortcut all steps to the end
 */
static unsigned sweep_repr (sweeper *sweeper, unsigned lit) {
  unsigned res;
  {
    unsigned prev = lit;
    while ((res = sweeper->reprs[prev]) != prev)
      prev = res;
  }
  if (res == lit)
    return res;
#if defined(LOGGING) || !defined(NDEBUG)
  kissat *solver = sweeper->solver;
#endif
  LOG ("sweeping repr[%s] = %s", LOGLIT (lit), LOGLIT (res));
  {
    const unsigned not_res = NOT (res);
    unsigned next, prev = lit;
    ;
    while ((next = sweeper->reprs[prev]) != res) {
      const unsigned not_prev = NOT (prev);
      sweeper->reprs[not_prev] = not_res;//shortcut all to not_res
      sweeper->reprs[prev] = res; //shortcut all to res
      prev = next;
    }
    assert (sweeper->reprs[NOT (prev)] == not_res);
  }
  return res;
}



/**
 *  Add lit to the current variable stack
 *  if
 *   --lit is its own representative
 *   --lit has no assigned depth yet
 */
static void add_literal_to_environment (sweeper *sweeper, unsigned depth,
                                        unsigned lit) {
  const unsigned repr = sweep_repr (sweeper, lit);
  if (repr != lit)
    return;
  kissat *solver = sweeper->solver;
  const unsigned idx = IDX (lit);
  if (sweeper->depths[idx])
    return;
  assert (depth < UINT_MAX);
  sweeper->depths[idx] = depth + 1;
  PUSH_STACK (sweeper->vars, idx);
  LOG ("sweeping[%u] adding literal %s", depth, LOGLIT (lit));
}


/**
 *  Add all literals of the current clause (solver->clause) to the environment
 *  Tell kitten about the clause
 */
static void sweep_clause (sweeper *sweeper, unsigned depth) {
  kissat *solver = sweeper->solver;
  assert (SIZE_STACK (sweeper->clause) > 1);
  for (all_stack (unsigned, lit, sweeper->clause))
    add_literal_to_environment (sweeper, depth, lit);
  kitten_clause (solver->kitten, SIZE_STACK (sweeper->clause),
                 BEGIN_STACK (sweeper->clause));
  CLEAR_STACK (sweeper->clause);
  sweeper->encoded++;
}



static bool stumbled_unit_in_binary(kissat *solver, unsigned lit, unsigned other) {
  value *values = solver->values;
  if (values[lit]) {
    if (values[lit]==1) //already satisfied
      return true;
    if (values[lit]==-1) {
      //NEW: directly assign this detected unit here in place
      kissat_assign_unit (solver, other, "stumbled while kitten-copying");
      /* Catch for Mallob Sharing */
      if (GET_OPTION (mallob_is_shweeper)) {
        kissat_custom_message(solver,V3_VVERB_SWEEP, " binary-stumble-U idx(%i)/lit(%i)", IDX(other),other);
        shweep_export_unit(solver, other);
      }
      INC (sweep_units);
      solver->sweeper->stumbled_units++;
      return true;
    }
  }
  return false;
}



/**
 * Sweep a binary clause, but only if it is really necessary
 * (both literals are representatives, the clause is not yet satisfied, and we haven't included the clause yet)
 */
static void sweep_binary (sweeper *sweeper, unsigned depth, unsigned lit,
                          unsigned other) {
  /** Dont continue of lit or other are not the representants of their equivalence class**/

  if (sweep_repr (sweeper, lit) != lit)
    return;
  if (sweep_repr (sweeper, other) != other)
    return;
  kissat *solver = sweeper->solver;
  LOGBINARY (lit, other, "sweeping[%u]", depth);
  value *values = solver->values;

  //Mallob Addition: It can happen that we stumble only here upon a unit clause that has not been detected yet,
  //due to some interactions with unit/equivalence imports that dont trigger such full unit propagations..
  //Current solution: Assign the unit right now on the spot
  if (stumbled_unit_in_binary (solver, lit, other))
    return;



  assert (!values[lit]);
  const value other_value = values[other];
  //Dont continue if other is already true, which directly satisfies the clause (?)
  if (other_value > 0) {
    LOGBINARY (lit, other, "skipping satisfied");
    return;
  }
  const unsigned *depths = sweeper->depths;
  const unsigned other_idx = IDX (other);
  const unsigned other_depth = depths[other_idx];
  const unsigned lit_idx = IDX (lit);
  const unsigned lit_depth = depths[lit_idx];
  if (other_depth && other_depth < lit_depth) {
    LOGBINARY (lit, other, "skipping depth %u copied", other_depth);
    return;
  }


  if (stumbled_unit_in_binary (solver, other, lit))
    return;


  assert (!other_value);
  assert (EMPTY_STACK (sweeper->clause));
  //Ok only now continue, sweep the clause
  PUSH_STACK (sweeper->clause, lit);
  PUSH_STACK (sweeper->clause, other);
  sweep_clause (sweeper, depth);
}




/**
* Sweep a clause, given by it's reference
* sweeping == add its variables to the environment and add the clause to kitten (per clause only those literals that are not yet decided)
* Don't sweep a clause if
* --its already satisfied (by some kissat-var with value==1)
* --its already been swept
* --its already garbage
*/
static void sweep_reference (sweeper *sweeper, unsigned depth,
                             reference ref) {
  assert (EMPTY_STACK (sweeper->clause));
  kissat *solver = sweeper->solver;
  clause *c = kissat_dereference_clause (solver, ref);
  if (c->swept)
    return;
  if (c->garbage)
    return;
  LOGCLS (c, "sweeping[%u]", depth);
  value *values = solver->values;
  for (all_literals_in_clause (lit, c)) {
    const value value = values[lit];
    if (value > 0) {
	    /*
	     * skip the clause
	     * one of it's literals is already set to true
	     *
	     */
      kissat_mark_clause_as_garbage (solver, c);
      CLEAR_STACK (sweeper->clause);
      return;
    }
    /*
       don't consider literals that are already to false
       Instead, their complement literal will be included
     */
    if (value < 0)
      continue;
    /**
     * Temporary buffer to pass this single clause to kitten
     */
    PUSH_STACK (sweeper->clause, lit);
  }
  PUSH_STACK (sweeper->refs, ref); //remember that we swept this clause
  c->swept = true;

  //Special behaviour in Mallob SWEEP: It can happen that we stumble here upon a unit-clause that has been undetected up to now -- because there are (apparently?) no unit-propagations happening in sweep
  //In sequential kissat this can not happen and is even forbidden via a SIZE>1 assertion, but apparently here with importing units/equivalences it can happen
  //Current solution is to assign the unit literal now on the spot here
  //Alternatively, maybe one could properly propagate all units, to find such other unit clauses directly (and maybe even others?)
  if (SIZE_STACK(sweeper->clause)==1) {
    assert( GET_OPTION (mallob_is_shweeper));
    // if ( ! GET_OPTION (mallob_is_shweeper)) {
      // assert(kissat_custom_assert_message (solver, V1_INFO_SWEEP, "found SIZE==1 clause but not in Mallob Shweep"));
    // }

    kissat_custom_message (solver, V1_INFO_SWEEP, "Warning: Detected Clause size %i, clause ref %i ", SIZE_STACK(sweeper->clause), ref);
    unsigned detected_unit = 0;
    for (all_literals_in_clause (lit, c)) {
      const value value = values[lit];
      if (value==0) {
        assert(detected_unit==0);
        detected_unit = lit;
      }
      kissat_custom_message (solver, V1_INFO_SWEEP, "idx(%i)/lit(%i)=val %i, repr_lit(%i)", IDX(lit), lit, value, sweep_repr (sweeper, lit));
    }
    //NEW: directly assign this detected unit here in place
    kissat_assign_unit (solver, detected_unit, "stumbled while kitten-copying");
     /* Catch for Mallob Sharing */
    if (GET_OPTION (mallob_is_shweeper)) {
      kissat_custom_message(solver,V3_VVERB_SWEEP, " stumble-U idx(%i)/lit(%i)", IDX(detected_unit),detected_unit);
      shweep_export_unit(solver, detected_unit);
    }
    INC (sweep_units);
    CLEAR_STACK (sweeper->clause); //usually done by sweep_clause, but we skip that here
    sweeper->stumbled_units++;
    return; //clause vanished, no need to pipe to kitten anymore
  }

  sweep_clause (sweeper, depth);
}






 /*
  Recieves the literals of implication graph clause and checks whether any literal has a satisfied value
  If all are unsatisfied, adds the clause-literals to the core-stack (marked off with INVALID_LIT boundaries per clause)
*/
static void save_core_clause (void *state, bool learned, size_t size,
                              const unsigned *lits) {
  sweeper *sweeper = state;
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  const value *const values = solver->values;
   /*
    * sweeper->save is either 0 or 1, i.e. this is core[save]
    */
  unsigneds *core = sweeper->core + sweeper->save;
  size_t saved = SIZE_STACK (*core);
  const unsigned *end = lits + size;
  unsigned non_false = 0;
   /*
    *Iterate over the literals of the given clause
    */
  for (const unsigned *p = lits; p != end; p++) {
    const unsigned lit = *p;
    const value value = values[lit];
    if (value > 0) {
       /*
        *clause is already satisfied. Abort, not part of the core
        */
      LOGLITS (size, lits, "extracted %s satisfied lemma", LOGLIT (lit));
      RESIZE_STACK (*core, saved);
      return;
    }
     /*
      * clause up to now not satisfied, extend the clause in the core by this literal
      */
    PUSH_STACK (*core, lit);
    if (value < 0)
      continue;
    if (!learned && ++non_false > 1) {
      LOGLITS (size, lits, "ignoring extracted original clause");
      RESIZE_STACK (*core, saved);
      return;
    }
  }
#ifdef LOGGING
  unsigned *saved_lits = BEGIN_STACK (*core) + saved;
  size_t saved_size = SIZE_STACK (*core) - saved;
  LOGLITS (saved_size, saved_lits, "saved core[%u]", sweeper->save);
#endif
   /*
    *Whole clause (all it's individual literals) has been copied onto the core-stack,
    *mark the end of the clause via an INVALID_LIT marker
    */
  PUSH_STACK (*core, INVALID_LIT);
}








 /*
  * Add information from an UNSAT core to kissat
  *
  * Situation: had UNSAT result, traversed the implication graph, collected all its clauses, then kept only those which were actually unsatisfied.
  * This can detect new unit clauses that we can tell kissat, and apparently is also needed for proof stuff
  *
  */
static void add_core (sweeper *sweeper, unsigned core_idx) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  LOG ("check and add extracted core[%u] lemmas to proof", core_idx);
  assert (core_idx == 0 || core_idx == 1);
  unsigneds *core = sweeper->core + core_idx;
  const value *const values = solver->values;

  unsigned *q = BEGIN_STACK (*core);
  const unsigned *const end_core = END_STACK (*core), *p = q;

   /*
    *Loop through the clauses of the core (separated by INVALID_LIT) markers)
    */
  while (p != end_core) {
    const unsigned *c = p;
    while (*p != INVALID_LIT)
      p++;
#ifdef LOGGING
    size_t old_size = p - c;
    LOGLITS (old_size, c, "simplifying extracted core[%u] lemma", core_idx);
#endif
     /*
      * c = Start of claue
      * p = End of clause
      */
    bool satisfied = false;
    unsigned unit = INVALID_LIT;

    unsigned *d = q;

     /*
      *loop through literals of this clause
      */
    for (const unsigned *l = c; !satisfied && l != p; l++) {
      const unsigned lit = *l;
      const value value = values[lit];
      if (value > 0) {
         /*
          *skip clause if it is satisfied
          */
        satisfied = true;
        break;
      }
      if (!value)
        unit = *q++ = lit;
    }

    size_t new_size = q - d;
    p++;

    if (satisfied) {
      q = d;
      LOG ("not adding satisfied clause");
      continue;
    }

    if (!new_size) {
      LOG ("sweeping produced empty clause");
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
      solver->inconsistent = true;
      CLEAR_STACK (*core);
      return;
    }

    if (new_size == 1) {
      q = d;
      assert (unit != INVALID_LIT);
      LOG ("sweeping produced unit %s", LOGLIT (unit));
      CHECK_AND_ADD_UNIT (unit);
      ADD_UNIT_TO_PROOF (unit);
       /*
        * Within the core there is a unit clause ----> Assign it (and propagate it?)
        */
      kissat_assign_unit (solver, unit, "sweeping backbone reason");
       /*
        * Catch for Mallob Sharing
        */
      if (GET_OPTION (mallob_is_shweeper)) {
        kissat_custom_message(solver,V3_VVERB_SWEEP, " core-U idx(%i)/lit(%i)", IDX(unit), unit);
        shweep_export_unit(solver, unit);
        // sweeper->done[IDX(unit)]=true;
      }


      INC (sweep_units);
      continue;
    }

    *q++ = INVALID_LIT;

    assert (new_size > 1);
    LOGLITS (new_size, d, "adding extracted core[%u] lemma", core_idx);
    CHECK_AND_ADD_LITS (new_size, d);
    ADD_LITS_TO_PROOF (new_size, d);
  }
  SET_END_OF_STACK (*core, q);
#ifndef LOGGING
  (void) core_idx;
#endif
}








 /*
  *We had an UNSAT result from a kitten call, i.e. an UNSAT core.
  *Now save this UNSAT result for further processing.
  */
static void save_core (sweeper *sweeper, unsigned core) {
  kissat *solver = sweeper->solver;
  LOG ("saving extracted core[%u] lemmas", core);
  assert (core == 0 || core == 1);
  assert (EMPTY_STACK (sweeper->core[core]));
  sweeper->save = core;
   /*
    * collect all clauses (only their reference, not their individual literals) by traversing the implication graph backwards
    */
  kitten_compute_clausal_core (solver->kitten, 0);
   /*
    * keep only those clauses that are actually unsatisfied (by looking at all the individual literals), i.e. kick out those that have satisfied literals
    */
  kitten_traverse_core_clauses (solver->kitten, sweeper, save_core_clause);
}





static void clear_core (sweeper *sweeper, unsigned core_idx) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
#if defined(LOGGING) || !defined(NDEBUG) || !defined(NPROOFS)
  assert (core_idx == 0 || core_idx == 1);
  LOG ("clearing core[%u] lemmas", core_idx);
#endif
  unsigneds *core = sweeper->core + core_idx;
#ifdef CHECKING_OR_PROVING
  LOG ("deleting sub-solver core clauses");
  const unsigned *const end = END_STACK (*core);
  const unsigned *c = BEGIN_STACK (*core);
  for (const unsigned *p = c; c != end; c = ++p) {
    while (*p != INVALID_LIT)
      p++;
    const size_t size = p - c;
    assert (size > 1);
    REMOVE_CHECKER_LITS (size, c);
    DELETE_LITS_FROM_PROOF (size, c);
  }
#endif
  CLEAR_STACK (*core);
}

/*
 * L.12-14
 * Found out that a backbone candidate is indeed a backbone. Propagate its value.
 */
static void save_add_clear_core (sweeper *sweeper) {
  save_core (sweeper, 0);
  add_core (sweeper, 0);
  clear_core (sweeper, 0);
}

#define LOGBACKBONE(MESSAGE) \
  LOGLITSET (SIZE_STACK (sweeper->backbone), \
             BEGIN_STACK (sweeper->backbone), MESSAGE)

#define LOGPARTITION(MESSAGE) \
  LOGLITPART (SIZE_STACK (sweeper->partition), \
              BEGIN_STACK (sweeper->partition), MESSAGE)



/**
 * Add all literals from the kitten solution to the backbone and partition stacks
 */
static void init_backbone_and_partition (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("initializing backbone and equivalent literals candidates");
  for (all_stack (unsigned, idx, sweeper->vars)) {
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    const unsigned not_lit = NOT (lit);
    const signed char tmp = kitten_value (solver->kitten, lit);//read the value from the kitten SAT solution
    const unsigned candidate = (tmp < 0) ? not_lit : lit; //Candidates are those literals from the solution, as these literals are "positive"
    LOG ("sweeping candidate %s", LOGLIT (candidate));
    PUSH_STACK (sweeper->backbone, candidate);
    PUSH_STACK (sweeper->partition, candidate);
  }
  PUSH_STACK (sweeper->partition, INVALID_LIT);

  LOGBACKBONE ("initialized backbone candidates");
  LOGPARTITION ("initialized equivalence candidates");
}





static void sweep_empty_clause (sweeper *sweeper) {
  assert (!sweeper->solver->inconsistent);
  save_add_clear_core (sweeper);
  assert (sweeper->solver->inconsistent);
}




/**
 * Splits each class in the partition into new true/false subclasses, following the true/false results from the current witness model
 * Datastructure: All classes live in the same partition stack, and are only divided from each other by INVALID_LIT markers
 */
static void sweep_refine_partition (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining partition");
  kitten *kitten = solver->kitten;
  unsigneds old_partition = sweeper->partition;
  unsigneds new_partition;
  INIT_STACK (new_partition);
  const value *const values = solver->values;
  const unsigned *const old_begin = BEGIN_STACK (old_partition);
  const unsigned *const old_end = END_STACK (old_partition);
#ifdef LOGGING
  unsigned old_classes = 0;
  unsigned new_classes = 0;
#endif
  //Copy literals from old_partition to new partition
  //But only those that are
  // -- their own representatives
  // -- not yet fixed by kissat
  // -- set to true in the kitten model
  for (const unsigned *p = old_begin, *q; p != old_end; p = q + 1) {
    unsigned assigned_true = 0, other;
    //Now scanning through one single class (classes are separated by INVALID_LIT)
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (!value)
        LOG ("dropping sub-solver unassigned %s", LOGLIT (other));
      else if (value > 0) {
        PUSH_STACK (new_partition, other);
        assigned_true++;
      }
    }
#ifdef LOGGING
    LOG ("refining class %u of size %zu", old_classes, (size_t) (q - p));
    old_classes++;
#endif
    if (assigned_true == 0)
      LOG ("no positive literal in class");
    else if (assigned_true == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u positive literal in class", assigned_true);
      PUSH_STACK (new_partition, INVALID_LIT); //Mark the end of this class via an INVALID_LIT. Separates if from the next class.
#ifdef LOGGING
      new_classes++;
#endif
    }

    unsigned assigned_false = 0;
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (value < 0) {
        PUSH_STACK (new_partition, other); //False partition comes on the same stack, but separated by one INVALID_LIT from the lower true partition
        assigned_false++;
      }
    }
    //Collected all false literals from the old class
    if (assigned_false == 0)
      LOG ("no negative literal in class");
    else if (assigned_false == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u negative literal in class", assigned_false);
      PUSH_STACK (new_partition, INVALID_LIT);
#ifdef LOGGING
      new_classes++;
#endif
    }
  }
  //Went through all classes and split them into twin true/false subclasses
  RELEASE_STACK (old_partition);
  sweeper->partition = new_partition;
  LOG ("refined %u classes into %u", old_classes, new_classes);
  LOGPARTITION ("refined equivalence candidates");
}

/**
 * Keep in the backbone only literals that
 *  -- are not yet fixed by kissat
 *  -- and are set to true
**/
static void sweep_refine_backbone (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining backbone candidates");
  const unsigned *const end = END_STACK (sweeper->backbone);
  unsigned *q = BEGIN_STACK (sweeper->backbone);
  const value *const values = solver->values;
  kitten *kitten = solver->kitten;
  for (const unsigned *p = q; p != end; p++) {
    const unsigned lit = *p;
    if (values[lit])
      continue;
    signed char value = kitten_value (kitten, lit);
    if (!value)
      LOG ("dropping sub-solver unassigned %s", LOGLIT (lit));
    else if (value >= 0)
      *q++ = lit;
  }
  SET_END_OF_STACK (sweeper->backbone, q);
  LOGBACKBONE ("refined backbone candidates");
}


/**
 * Refine the backbone and partition (using the current kitten model)
 */
static void sweep_refine (sweeper *sweeper) {
#ifdef LOGGING
  kissat *solver = sweeper->solver;
#endif
  if (EMPTY_STACK (sweeper->backbone))
    LOG ("no need to refine empty backbone candidates");
  else
    sweep_refine_backbone (sweeper);
  if (EMPTY_STACK (sweeper->partition))
    LOG ("no need to refine empty partition candidates");
  else
    sweep_refine_partition (sweeper);
}


/**
 * iteratively flip every literal from the backbone, only keep those that resist flipping.
 * --> Backbone shrinks.
 * If -lit flip gives new model: Kick the literal from the backbone. Leaves the flipped value in the model (!) i.e. with every flip the model random-walk through the solution-space
 * If -lit flip is unsat:        Keep the literal in the backbone, we could not rule it out via a cheap flip
 */
static void flip_backbone_literals (struct sweeper *sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = GET_OPTION (sweepfliprounds);
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->backbone));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {//Effectively only one round, because sweepflipround=1 per default
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->backbone), *q = begin;
    const unsigned *const end = END_STACK (sweeper->backbone), *p = q;
    while (p != end) {
      const unsigned lit = *p++;
      INC (sweep_flip_backbone);
      if (kitten_flip_literal (kitten, lit)) { //Successful flipping seems to be permanent! The new solution now contains this flipped literal
        LOG ("flipping backbone candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
        total_flipped++;
#endif
        INC (sweep_flipped_backbone);
        flipped++;
      } else {
        LOG ("flipping backbone candidate %s failed", LOGLIT (lit));//Since flipping failed, the literal remains in the backbone
        *q++ = lit;
      }
    }
    SET_END_OF_STACK (sweeper->backbone, q);//Reduces the stack to those literals that resisted flipping
    LOG ("flipped %u backbone candidates in round %u", flipped, round);

    if (TERMINATED (sweep_terminated_1))
      break;
    if (solver->statistics.kitten_ticks > sweeper->limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u backbone candidates in total in %u rounds",
       total_flipped, round);
}


/**
 * L.8-14
 * Invest full effort to find any model where lit is negated
 *  1. Try luck by just flipping, might work
 *  2. Assume -lit and run kitten. If new model, lit is not backbone, and have learned new model. Narrow down backbone and refine partitions
 *  3. If no model exists, kitten proved that lit must be kept positive -> propagate this info
 */
static bool sweep_backbone_candidate (sweeper *sweeper, unsigned lit) {
  kissat *solver = sweeper->solver;
  LOG ("trying backbone candidate %s", LOGLIT (lit));
  kitten *kitten = solver->kitten;
  signed char value = kitten_fixed (kitten, lit);
  if (value) {
    INC (sweep_fixed_backbone);
    LOG ("literal %s already fixed", LOGLIT (lit));
    assert (value > 0);
    return false;
  }

   /*
   *   //Try lucky normal flipping . Maybe it works now given the current random-walk-situation
   *   //If flip works, remove this lit from the backbone
   */
  INC (sweep_flip_backbone);
  if (kitten_status (kitten) == 10 && kitten_flip_literal (kitten, lit)) {
    INC (sweep_flipped_backbone);
    LOG ("flipping %s succeeded", LOGLIT (lit));
    LOGBACKBONE ("refined backbone candidates");
    return false;
  }

  /*
   *  Random flip was not successful. Amp up the investment.
      Run expensive SAT call to check whether there is *any* model where lit is flipped.
     */
  LOG ("flipping %s failed", LOGLIT (lit));
  const unsigned not_lit = NOT (lit);
  INC (sweep_solved_backbone);
  kitten_assume (kitten, not_lit);
  int res = sweep_solve (sweeper);
  if (res == 10) {
    /*
    Found a model with this lit flipped.
    So this lit is not a backbone, and the new model is new information to further split partition classed
     */
    LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
    sweep_refine (sweeper);
    INC (sweep_sat_backbone);
    return false;
  }

  if (res == 20) {
    /*
     * The current lit IS a backbone, because kitten couldn't find any model without this lit
     * the larger the environment is, the more constraints there are to show that a literal is a backbone
     * Larger environment ==> More detected backbones
     * We found the backbone even with the limited environment, nice. Now propagate this as a unit clause.
     */
    kissat_custom_message(solver,V3_VVERB_SWEEP, " lit is backbone -U! %u", lit);
    LOG ("sweep unit %s", LOGLIT (lit));
    save_add_clear_core (sweeper);
    INC (sweep_unsat_backbone);
    return true;
  }

  INC (sweep_unknown_backbone);

  LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
  return false;
}

static void add_binary (kissat *solver, unsigned lit, unsigned other) {
  kissat_new_binary_clause (solver, lit, other);
}

static bool scheduled_variable (sweeper *sweeper, unsigned idx) {
#ifndef NDEBUG
  kissat *const solver = sweeper->solver;
  assert (VALID_INTERNAL_INDEX (idx));
#endif
  return sweeper->prev[idx] != INVALID_IDX || sweeper->first == idx;
}


/**
* Schedule idx to be the very next variable to be popped for sweeping
* By moving it to the end ("last") of the schedule queue
**/
static void schedule_inner (sweeper *sweeper, unsigned idx) {
  kissat *const solver = sweeper->solver;
  assert (VALID_INTERNAL_INDEX (idx));
  if (!ACTIVE (idx))
    return;
  const unsigned next = sweeper->next[idx];
  if (next != INVALID_IDX) {
    LOG ("rescheduling inner %s as last", LOGVAR (idx));
    const unsigned prev = sweeper->prev[idx];
    assert (sweeper->prev[next] == idx);
    sweeper->prev[next] = prev;
    if (prev == INVALID_IDX) {
      assert (sweeper->first == idx);
      sweeper->first = next;
    } else {
      assert (sweeper->next[prev] == idx);
      sweeper->next[prev] = next;
    }
    const unsigned last = sweeper->last;
    if (last == INVALID_IDX) {
      assert (sweeper->first == INVALID_IDX);
      sweeper->first = idx;
    } else {
      assert (sweeper->next[last] == INVALID_IDX);
      sweeper->next[last] = idx;
    }
    sweeper->prev[idx] = last;
    sweeper->next[idx] = INVALID_IDX;
    sweeper->last = idx;
  } else if (sweeper->last != idx) {
    LOG ("scheduling inner %s as last", LOGVAR (idx));
    const unsigned last = sweeper->last;
    if (last == INVALID_IDX) {
      assert (sweeper->first == INVALID_IDX);
      sweeper->first = idx;
    } else {
      assert (sweeper->next[last] == INVALID_IDX);
      sweeper->next[last] = idx;
    }
    assert (sweeper->next[idx] == INVALID_IDX);
    sweeper->prev[idx] = last;
    sweeper->last = idx;
  } else
    LOG ("keeping inner %s scheduled as last", LOGVAR (idx));
}



/**
 *Move idx to the start of the schedule queue ("first") (where it will not be popped for a long time)
**/
static void schedule_outer (sweeper *sweeper, unsigned idx) {
#if !defined(NDEBUG) || defined(LOGGING)
  kissat *const solver = sweeper->solver;
#endif
  assert (VALID_INTERNAL_INDEX (idx));
  assert (!scheduled_variable (sweeper, idx));
  assert (ACTIVE (idx));
  const unsigned first = sweeper->first;
  if (first == INVALID_IDX) {
    assert (sweeper->last == INVALID_IDX);
    sweeper->last = idx;
  } else {
    assert (sweeper->prev[first] == INVALID_IDX);
    sweeper->prev[first] = idx;
  }
  assert (sweeper->prev[idx] == INVALID_IDX);
  sweeper->next[idx] = first;
  sweeper->first = idx;
  LOG ("scheduling outer %s as first", LOGVAR (idx));
}


/**
*Pop the *last* idx from the schedule queue
**/
static unsigned next_scheduled (sweeper *sweeper) {
#if !defined(NDEBUG) || defined(LOGGING)
  kissat *const solver = sweeper->solver;
#endif
  unsigned res = sweeper->last;
  if (res == INVALID_IDX) {
    LOG ("no more scheduled variables left");
    return INVALID_IDX;
  }
  assert (VALID_INTERNAL_INDEX (res));
  LOG ("dequeuing next scheduled %s", LOGVAR (res));
  const unsigned prev = sweeper->prev[res];
  assert (sweeper->next[res] == INVALID_IDX);
  sweeper->prev[res] = INVALID_IDX;
  if (prev == INVALID_IDX) {
    assert (sweeper->first == res);
    sweeper->first = INVALID_IDX;
  } else {
    assert (sweeper->next[prev] == res);
    sweeper->next[prev] = INVALID_IDX;
  }
  sweeper->last = prev;
  return res;
}

#define all_scheduled(IDX) \
  unsigned IDX = sweeper->first, NEXT_##IDX; \
  IDX != INVALID_IDX && (NEXT_##IDX = sweeper->next[IDX], true); \
  IDX = NEXT_##IDX






 /*
  *We found an equivalence lit == repr
  *now we replace in the whole clause database lit --> repr
  *Multiple things can happen to a clause: it can reduce to empty, unit, binary, or larger; each needs its own handling
  */
static void substitute_connected_clauses (sweeper *sweeper, unsigned lit,
                                          unsigned repr) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  value *const values = solver->values;
  if (values[lit])
    return;
  if (values[repr])
    return;
  LOG ("substituting %s with %s in all irredundant clauses", LOGLIT (lit),
       LOGLIT (repr));

  assert (lit != repr);
  assert (lit != NOT (repr));

#ifdef CHECKING_OR_PROVING
  const bool checking_or_proving = kissat_checking_or_proving (solver);
  assert (EMPTY_STACK (solver->added));
  assert (EMPTY_STACK (solver->removed));
#endif

  unsigneds *const delayed = &solver->delayed;
  assert (EMPTY_STACK (*delayed));

  {
    watches *lit_watches = &WATCHES (lit);
    watch *const begin_watches = BEGIN_WATCHES (*lit_watches);
    const watch *const end_watches = END_WATCHES (*lit_watches);

    watch *q = begin_watches;
    const watch *p = q;

    while (p != end_watches) {
      const watch head = *q++ = *p++;
      if (head.type.binary) {
        const unsigned other = head.binary.lit;
        const value other_value = values[other];
        if (other == NOT (repr))
          continue;
        if (other_value < 0)
          break;
        if (other_value > 0)
          continue;
        if (other == repr) {
          CHECK_AND_ADD_UNIT (lit);
          ADD_UNIT_TO_PROOF (lit);
          kissat_assign_unit (solver, lit, "substituted binary clause");

           /*
            * Catch for Mallob Sharing
            */
          if (GET_OPTION (mallob_is_shweeper)) {
            kissat_custom_message(solver,V3_VVERB_SWEEP, " binary-U idx(%i)/lit(%i)", IDX(lit),lit);
            shweep_export_unit(solver, lit);
          }

          INC (sweep_units);
          break;
        }
        CHECK_AND_ADD_BINARY (repr, other);
        ADD_BINARY_TO_PROOF (repr, other);
        REMOVE_CHECKER_BINARY (lit, other);
        DELETE_BINARY_FROM_PROOF (lit, other);
        PUSH_STACK (*delayed, head.raw);
        watch src = {.raw = head.raw};
        watch dst = {.raw = head.raw};
        src.binary.lit = lit;
        dst.binary.lit = repr;
        watches *other_watches = &WATCHES (other);
        kissat_substitute_large_watch (solver, other_watches, src, dst);
        q--;
      } else {
        const reference ref = head.large.ref;
        assert (EMPTY_STACK (sweeper->clause));
        clause *c = kissat_dereference_clause (solver, ref);
        if (c->garbage)
          continue;

        bool satisfied = false;
        bool repr_already_watched = false;
        const unsigned not_repr = NOT (repr);
#ifndef NDEBUG
        bool found = false;
#endif
        for (all_literals_in_clause (other, c)) {
          if (other == lit) {
#ifndef NDEBUG
            assert (!found);
            found = true;
#endif
            PUSH_STACK (solver->clause, repr);
            continue;
          }
          assert (other != NOT (lit));
          if (other == repr) {
            assert (!repr_already_watched);
            repr_already_watched = true;
            continue;
          }
          if (other == not_repr) {
            satisfied = true;
            break;
          }
          const value tmp = values[other];
          if (tmp < 0)
            continue;
          if (tmp > 0) {
            satisfied = true;
            break;
          }
          PUSH_STACK (solver->clause, other);
        }

        if (satisfied) {
          CLEAR_STACK (solver->clause);
          kissat_mark_clause_as_garbage (solver, c);
          continue;
        }


         /*
          *MALLOB DEBUG
          */

#ifndef NDEBUG
        if (!found) {
          kissat_custom_message (solver,V1_INFO_SWEEP , "assert at lit %u, repr %u", lit, repr);
          kissat_custom_message (solver,V1_INFO_SWEEP , "not finding lit %u in its own(?) watched clause(?)", lit);
          kissat_custom_message (solver,V1_INFO_SWEEP , "head.binary   %i", head.binary);
          kissat_custom_message (solver,V1_INFO_SWEEP , "head.blocking %i", head.blocking);
          kissat_custom_message (solver,V1_INFO_SWEEP , "head.large    %i", head.large);
          kissat_custom_message (solver,V1_INFO_SWEEP , "head.type     %i", head.type);
          kissat_custom_message (solver,V1_INFO_SWEEP , "begin watches %i", *begin_watches);
          kissat_custom_message (solver,V1_INFO_SWEEP , "end watches   %i", *end_watches);

        }

        assert (found);

#endif
        const unsigned new_size = SIZE_STACK (solver->clause);

        if (new_size == 0) {
          LOGCLS (c, "substituted empty clause");
          assert (!solver->inconsistent);
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY ();
          ADD_EMPTY_TO_PROOF ();
          break;
        }

        if (new_size == 1) {
          LOGCLS (c, "reduces to unit");
          const unsigned unit = POP_STACK (solver->clause);
          CHECK_AND_ADD_UNIT (unit);
          ADD_UNIT_TO_PROOF (unit);
          kissat_assign_unit (solver, unit, "substituted large clause");

           /*
            * Catch for Mallob Sharing
            */
          if (GET_OPTION (mallob_is_shweeper)) {
            //had bug, had "lit" here instead of "unit" !!
            kissat_custom_message(solver,V3_VVERB_SWEEP, " size1-U idx(%i)/lit(%i)", IDX(unit),unit);
            shweep_export_unit(solver, unit);
          }

          INC (sweep_units);
          break;
        }

        CHECK_AND_ADD_STACK (solver->clause);
        ADD_STACK_TO_PROOF (solver->clause);
        REMOVE_CHECKER_CLAUSE (c);
        DELETE_CLAUSE_FROM_PROOF (c);

        if (!c->redundant)
          kissat_mark_added_literals (solver, new_size,
                                      BEGIN_STACK (solver->clause));

        if (new_size == 2) {
          const unsigned second = POP_STACK (solver->clause);
          const unsigned first = POP_STACK (solver->clause);
          LOGCLS (c, "reduces to binary clause %s %s", LOGLIT (first),
                  LOGLIT (second));
          assert (first == repr || second == repr);
          const unsigned other = first ^ second ^ repr;
          const watch src = {.raw = head.raw};
          watch dst = kissat_binary_watch (repr);
          watches *other_watches = &WATCHES (other);
          kissat_substitute_large_watch (solver, other_watches, src, dst);
          assert (solver->statistics.clauses_irredundant);
          solver->statistics.clauses_irredundant--;
          assert (solver->statistics.clauses_binary < UINT64_MAX);
          solver->statistics.clauses_binary++;
          dst.binary.lit = other;
          PUSH_STACK (*delayed, dst.raw);
          const size_t bytes = kissat_actual_bytes_of_clause (c);
          ADD (arena_garbage, bytes);
          c->garbage = true;
          q--;
          continue;
        }

        assert (2 < new_size);
        const unsigned old_size = c->size;
        assert (new_size <= old_size);

        const unsigned *const begin = BEGIN_STACK (solver->clause);
        const unsigned *const end = END_STACK (solver->clause);

        unsigned *lits = c->lits;
        unsigned *q = lits;

        for (const unsigned *p = begin; p != end; p++) {
          const unsigned other = *p;
          *q++ = other;
        }

        if (new_size < old_size) {
          c->size = new_size;
          c->searched = 2;
          if (c->redundant && c->glue >= new_size)
            kissat_promote_clause (solver, c, new_size - 1);
          if (!c->shrunken) {
            c->shrunken = true;
            lits[old_size - 1] = INVALID_LIT;
          }
        }

        LOGCLS (c, "substituted");

        if (!repr_already_watched)
          PUSH_STACK (*delayed, head.raw);
        CLEAR_STACK (solver->clause);
        q--;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_WATCHES (*lit_watches, q);
  }
  {
    const unsigned *const begin_delayed = BEGIN_STACK (*delayed);
    const unsigned *const end_delayed = END_STACK (*delayed);
    for (const unsigned *p = begin_delayed; p != end_delayed; p++) {
      const watch head = {.raw = *p};
      watches *repr_watches = &WATCHES (repr);
      PUSH_WATCHES (*repr_watches, head);
    }

    CLEAR_STACK (*delayed);
  }

#ifdef CHECKING_OR_PROVING
  if (checking_or_proving) {
    CLEAR_STACK (solver->added);
    CLEAR_STACK (solver->removed);
  }
#endif
}











 /*
  *Remove lit from it's partition class, because it was found to be equivalent with some other representative
  *In case lit came from an imported equivalence, maybe it doesnt even appear in the local eq class
  *Or maybe the import does happen anyways after or before a sweep, so there might not even exist a partition to worry about during importing
  */
static void sweep_remove (sweeper *sweeper, unsigned lit) {
  kissat *solver = sweeper->solver;
  assert (sweeper->reprs[lit] != lit);
  unsigneds *partition = &sweeper->partition;
  unsigned *const begin_partition = BEGIN_STACK (*partition), *p;
  const unsigned *const end_partition = END_STACK (*partition);
  for (p = begin_partition; *p != lit; p++)
    assert (p + 1 != end_partition);
  unsigned *begin_class = p;
  while (begin_class != begin_partition && begin_class[-1] != INVALID_LIT)
    begin_class--;
  const unsigned *end_class = p;
  while (*end_class != INVALID_LIT)
    end_class++;
  const unsigned size = end_class - begin_class;
  LOG ("removing non-representative %s from equivalence class of size %u",
       LOGLIT (lit), size);
  assert (size > 1);
  unsigned *q = begin_class;
  if (size == 2) {
    LOG ("completely squashing equivalence class of %s", LOGLIT (lit));
    for (const unsigned *r = end_class + 1; r != end_partition; r++)
      *q++ = *r;
  } else {
    for (const unsigned *r = begin_class; r != end_partition; r++)
      if (r != p)
        *q++ = *r;
  }
  SET_END_OF_STACK (*partition, q);
#ifndef LOGGING
  (void) solver;
#endif
}







static void flip_partition_literals (struct sweeper *sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = GET_OPTION (sweepfliprounds);
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->partition));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->partition), *dst = begin;
    const unsigned *const end = END_STACK (sweeper->partition), *src = dst;
    while (src != end) {
      const unsigned *end_src = src;
      while (assert (end_src != end), *end_src != INVALID_LIT)
        end_src++;
      unsigned size = end_src - src;
      assert (size > 1);
      unsigned *q = dst;
      for (const unsigned *p = src; p != end_src; p++) {
        const unsigned lit = *p;
        if (kitten_flip_literal (kitten, lit)) {
          LOG ("flipping equivalence candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
          total_flipped++;
#endif
          flipped++;
          if (--size < 2)
            break;
        } else {
          LOG ("flipping equivalence candidate %s failed", LOGLIT (lit));
          *q++ = lit;
        }
      }
      if (size > 1) {
        *q++ = INVALID_LIT;
        dst = q;
      }
      src = end_src + 1;
    }
    SET_END_OF_STACK (sweeper->partition, dst);
    LOG ("flipped %u equivalence candidates in round %u", flipped, round);

    if (TERMINATED (sweep_terminated_2))
      break;
    if (solver->statistics.kitten_ticks > sweeper->limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u equivalence candidates in total in %u rounds",
       total_flipped, round);
}

/*
  Test conclusively whether (lit, other) are equivalent literals.
  If yes, map one to the other
  If not, then we found a new model that allows further partition refinement
*/
static bool sweep_equivalence_candidates (sweeper *sweeper, unsigned lit,
                                          unsigned other) {
  kissat *solver = sweeper->solver;
  LOG ("trying equivalence candidates %s = %s", LOGLIT (lit),
       LOGLIT (other));
  const unsigned not_other = NOT (other);
  const unsigned not_lit = NOT (lit);
  kitten *kitten = solver->kitten;
  const unsigned *const begin = BEGIN_STACK (sweeper->partition);
  unsigned *const end = END_STACK (sweeper->partition);
  assert (begin + 3 <= end);
  assert (end[-3] == lit);
  assert (end[-2] == other);
   /*
    * If the class boundary comes directly after the second literal, the class consists only of these two literals
    */
  const unsigned third = (end - begin == 3) ? INVALID_LIT : end[-4];
  const int status = kitten_status (kitten);
   /*
    *Try cheap flip of the first literal
    */
  if (status == 10 && kitten_flip_literal (kitten, lit)) {
    INC (sweep_flip_equivalences);
    INC (sweep_flipped_equivalences);
    LOG ("flipping %s succeeded", LOGLIT (lit));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (lit),
           LOGLIT (other));
      end[-3] = other;
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
   /*
    *Try cheap flip of the second literal
    */
  } else if (status == 10 && kitten_flip_literal (kitten, other)) {
    ADD (sweep_flip_equivalences, 2);
    INC (sweep_flipped_equivalences);
    LOG ("flipping %s succeeded", LOGLIT (other));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (other),
           LOGLIT (lit));
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
  }
  if (status == 10)
    ADD (sweep_flip_equivalences, 2);
  LOG ("flipping %s and %s both failed", LOGLIT (lit), LOGLIT (other));
   /*
    *Now invest first hard SAT call (G -l k)
    */
  kitten_assume (kitten, not_lit);
  kitten_assume (kitten, other);
  INC (sweep_solved_equivalences);
  int res = sweep_solve (sweeper);
  if (res == 10) {
     /*
      * SAT model was able to split l and k, because it found a solution (-l k)
      */
    INC (sweep_sat_equivalences);
    LOG ("first sweeping implication %s -> %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    INC (sweep_unknown_equivalences);
    LOG ("first sweeping implication %s -> %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20)
    return false;

  INC (sweep_unsat_equivalences);
  LOG ("first sweeping implication %s -> %s succeeded", LOGLIT (other),
       LOGLIT (lit));

   /*
    * Store this UNSAT-Core for (G -l k)
    */
  save_core (sweeper, 0);

   /*
    * The first SAT call could not split (l k), because it returned unsatisfiable for (-l k)
    * Now try the symmetric case (G l -k)
    */
  kitten_assume (kitten, lit);
  kitten_assume (kitten, not_other);
  res = sweep_solve (sweeper);
  INC (sweep_solved_equivalences);
  if (res == 10) {
     /*
      * Found a split. l and k are not equivalent.
      */
    INC (sweep_sat_equivalences);
    LOG ("second sweeping implication %s <- %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    INC (sweep_unknown_equivalences);
    LOG ("second sweeping implication %s <- %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20) {
    CLEAR_STACK (sweeper->core[0]);
    return false;
  }

   /*
    * Found out that l and k are indeed equivalent!
    *  both SAT calls (G -l k) and (G l -k) returned UNSAT.
    */
  INC (sweep_unsat_equivalences);
  LOG ("second sweeping implication %s <- %s succeeded too", LOGLIT (other),
       LOGLIT (lit));

   /*
    *Store also the second UNSAT core for (G l -k)
    */
  save_core (sweeper, 1);

  LOG ("sweep equivalence %s = %s", LOGLIT (lit), LOGLIT (other));
  INC (sweep_equivalences);


  // const int elit1 = kissat_export_literal (solver, lit);
  // const int elit2 = kissat_export_literal (solver, other);
  // kissat_custom_message(solver,V3_VVERB_SWEEP," %i==%i", elit1, elit2);

  // kissat_custom_message(solver, "(Repr  %i == %i)", IDX(sweeper->reprs[lit]), IDX(sweeper->reprs[other]));



   /*
    *Tell kissat about (G -l k) UNSAT
    *In particular relevant for proving (?), and by traversing the implication graph it might even find some more unit clauses
    *Uses the saved core nr. 0
    */
  add_core (sweeper, 0);
  add_binary (solver, lit, not_other);
  clear_core (sweeper, 0);

   /*
    *Repeat for the other core, tell kissat about (G l -k) UNSAT
    *Uses the saved core nr. 1
    */
  add_core (sweeper, 1);
  add_binary (solver, not_lit, other);
  clear_core (sweeper, 1);


  //Export this equivalence to mallob, to share it with other sweepers
  if (GET_OPTION (mallob_is_shweeper)) {
    unsigned idx_lit = IDX(lit);
    unsigned idx_other = IDX(other);

    if (lit < other) {
      shweep_export_equivalence(solver, lit, other);
      kissat_custom_message(solver,V3_VVERB_SWEEP, "found eq idx(%u)=idx(%u) [lit(%u)==lit(%u)]", idx_lit, idx_other, lit, other);
    } else {
      shweep_export_equivalence(solver, other, lit);
      kissat_custom_message(solver,V3_VVERB_SWEEP, "found eq idx(%u)=idx(%u) [lit(%u)==lit(%u)]", idx_other, idx_lit, other, lit);
    }
  }

   /*
    *  Now replace globally in the whole clause database the literals (other gets replaced by lit)
    */

  unsigned repr;
  if (lit < other) {
    repr = sweeper->reprs[other] = lit;
    sweeper->reprs[not_other] = not_lit;
     /*
      * Replace other --> lit in all (watched?) clauses
      */
    substitute_connected_clauses (sweeper, other, lit);
    substitute_connected_clauses (sweeper, not_other, not_lit);
     /*
      * Remove "other" from the sweeper partition
      */
    sweep_remove (sweeper, other);
  } else {
     /*
      * Symmetric case for inverse lexicographic order
      */
    repr = sweeper->reprs[lit] = other;
    sweeper->reprs[not_lit] = not_other;
    substitute_connected_clauses (sweeper, lit, other);
    substitute_connected_clauses (sweeper, not_lit, not_other);
    sweep_remove (sweeper, lit);
  }

 /*
  *L.9
  *Re-introduce repr to the queue, to where it is immediately scheduled next
  *heuristic argument: We just made progress around "repr" (and simplified some clauses) immediately search again here
  */

  //Vanilla sweeping now reschedules the found equivalent variable in the scheduling linked-list for immediate resweeping.
  //In distributed sweeping, instead, for simplicity we just use a stack, as the scheduling itself is already done via the array work[]
  const unsigned repr_idx = IDX (repr);
  if (!GET_OPTION (mallob_is_shweeper)) {
    schedule_inner (sweeper, repr_idx);
  } else {
    PUSH_STACK(sweeper->RESWEEP, repr_idx);
  }
  return true;

}





static const char *sweep_variable (sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  assert (!solver->inconsistent);
  if (!ACTIVE (idx))
    return "inactive variable";
  const unsigned start = LIT (idx);
  if (sweeper->reprs[start] != start)
    return "non-representative variable";
  assert (EMPTY_STACK (sweeper->vars));
  assert (EMPTY_STACK (sweeper->refs));
  assert (EMPTY_STACK (sweeper->backbone));
  assert (EMPTY_STACK (sweeper->partition));
  assert (!sweeper->encoded);

  INC (sweep_variables);

  LOG ("sweeping %s", LOGVAR (idx));
  assert (!VALUE (start));
  LOG ("starting sweeping[0]");
  /*
    *  Starts the environment by rooting it at idx
    */
  add_literal_to_environment (sweeper, 0, start);
  LOG ("finished sweeping[0]");
  LOG ("starting sweeping[1]");

  bool limit_reached = false;
  size_t expand = 0, next = 1;
  bool success = false;
  unsigned depth = 1;

  /**
   * l.4
   * Construct the environment around idx
   */
  while (!limit_reached) {
    if (sweeper->encoded >= sweeper->limit.clauses) {
      LOG ("environment clause limit reached");
      limit_reached = true;
      break;
    }
    if (expand == next) {
      LOG ("finished sweeping[%u]", depth);
      if (depth >= sweeper->limit.depth) {
        LOG ("environment depth limit reached");
        break;
      }
      next = SIZE_STACK (sweeper->vars);
      if (expand == next) {
        LOG ("completely copied all clauses");
        break;
      }
      depth++;
      LOG ("starting sweeping[%u]", depth);
    }
    const unsigned choices = next - expand;
    if (GET_OPTION (sweeprand) && choices > 1) {
      const unsigned swap =
          kissat_pick_random (&solver->random, 0, choices);
      if (swap) {
        unsigned *vars = sweeper->vars.begin;
        SWAP (unsigned, vars[expand], vars[expand + swap]);
      }
    }

    /*
    * Expand the environment by reading it's next variable
    */
    const unsigned idx = PEEK_STACK (sweeper->vars, expand);
    LOG ("traversing and adding clauses of %s", LOGVAR (idx));
    for (unsigned sign = 0; sign < 2; sign++) {
      const unsigned lit = LIT (idx) + sign;
      watches *watches = &WATCHES (lit);
      for (all_binary_large_watches (watch, *watches)) {
        if (watch.type.binary) {
          const unsigned other = watch.binary.lit;
          /*
           * Add clause and variables to environment
           * For binary clauses, need extra checks whether it's necessary to include them
           */
          sweep_binary (sweeper, depth, lit, other);
        } else {
          reference ref = watch.large.ref;
          /*
           * Add clause and variables to environment
          */
          sweep_reference (sweeper, depth, ref);
        }
        if (SIZE_STACK (sweeper->vars) >= sweeper->limit.vars) {
          LOG ("environment variable limit reached");
          limit_reached = true;
          break;
        }
      }
      if (limit_reached)
        break;
    }
    expand++;
  }
  /*
   *L.3
   *Environment around idx is now collected and kitten knows all its clauses
    Ask kitten to find a first model
   */
  ADD (sweep_depth, depth);
  ADD (sweep_clauses, sweeper->encoded);
  ADD (sweep_environment, SIZE_STACK (sweeper->vars));
  kissat_extremely_verbose (solver,
                            "sweeping       variable %d:  environment of "
                            "%zu variables %u clauses depth %u",
                            kissat_export_literal (solver, LIT (idx)),
                            SIZE_STACK (sweeper->vars), sweeper->encoded,
                            depth);
  int res = sweep_solve (sweeper);
  LOG ("sub-solver returns '%d'", res);
  if (res == 10) {
    init_backbone_and_partition (sweeper);
#ifndef QUIET
    uint64_t units = solver->statistics.sweep_units;
    uint64_t solved = solver->statistics.sweep_solved;
#endif
    START (sweepbackbone);
    /*
      *L.6
     Kitten has found a first model
     Narrow down the backbone via cheap flips. Flip successful -> Literal is not backbone, can be kicked
     Then try hard to flip one literal in particular
     */
    while (!EMPTY_STACK (sweeper->backbone)) {
      kissat_custom_message(solver, V4_UVERB_SWEEP, "    B(%i)", SIZE_STACK(sweeper->backbone));
      if (solver->inconsistent || TERMINATED (sweep_terminated_3) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
      STOP_SWEEP_BACKBONE:
        STOP (sweepbackbone);
        goto DONE;
      }
      /*
       L.8-9
       Cheap refine of the backbone: try lucky flips
        */
      flip_backbone_literals (sweeper);
      if (TERMINATED (sweep_terminated_4) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_BACKBONE;
      }
      if (EMPTY_STACK (sweeper->backbone))
        break;
      /*
       * L.8-14
       * Expensive SAT call: conclusively test whether lit is backbone or not. Either way, it is no longer a candidate after this.
       */
      const unsigned lit = POP_STACK (sweeper->backbone);
      if (!ACTIVE (IDX (lit)))
        continue;
      if (sweep_backbone_candidate (sweeper, lit))
        success = true;
    }
    STOP (sweepbackbone);
#ifndef QUIET
    units = solver->statistics.sweep_units - units;
    solved = solver->statistics.sweep_solved - solved;
    // kissat_custom_message(solver, V4_UVERB_SWEEP, "  %i SAT-B", solved);
    kissat_extremely_verbose (
        solver,
        "complete swept variable %d backbone with %" PRIu64
        " units in %" PRIu64 " solver calls",
        kissat_export_literal (solver, LIT (idx)), units, solved);
#endif
    assert (EMPTY_STACK (sweeper->backbone));
#ifndef QUIET
    uint64_t equivalences = solver->statistics.sweep_equivalences;
    solved = solver->statistics.sweep_solved;
#endif
    /*
     * L.15-22
     * Check pairwise within a class which variables are actually equivalent
     *
     * The backbone is now empty.
     * All backbone-variables have been propagated
     * All non-backbone variables are partitioned into potential equivalence classes
      */
    START (sweepequivalences);
    while (!EMPTY_STACK (sweeper->partition)) {
      // kissat_custom_message(solver, V4_UVERB_SWEEP, "    P(%i)", SIZE_STACK(sweeper->partition));
      if (solver->inconsistent || TERMINATED (sweep_terminated_5) ||
          kitten_ticks_limit_hit (sweeper, "partition refinement")) {
        limit_reached = true;
      STOP_SWEEP_EQUIVALENCES:
        STOP (sweepequivalences);
        goto DONE;
      }
      /*
        * Lucky attempts to quickly split partitions again
        */
      flip_partition_literals (sweeper);
      if (TERMINATED (sweep_terminated_6) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_EQUIVALENCES;
      }
      if (EMPTY_STACK (sweeper->partition))
        break;
      if (SIZE_STACK (sweeper->partition) > 2) {
        const unsigned *end = END_STACK (sweeper->partition);
        assert (end[-1] == INVALID_LIT);
        unsigned lit = end[-3];
        unsigned other = end[-2];
        /*
          Test conclusively whether "lit" and "other" are already in the given environment equivalent literals
        */
        if (sweep_equivalence_candidates (sweeper, lit, other))
          success = true;
      } else
        CLEAR_STACK (sweeper->partition);
    }
    STOP (sweepequivalences);
#ifndef QUIET
    equivalences = solver->statistics.sweep_equivalences - equivalences;
    solved = solver->statistics.sweep_solved - solved;
    // kissat_custom_message(solver, V4_UVERB_SWEEP, "  %i SAT-P", solved);
    if (equivalences)
      kissat_extremely_verbose (
          solver,
          "complete swept variable %d partition with %" PRIu64
          " equivalences in %" PRIu64 " solver calls",
          kissat_export_literal (solver, LIT (idx)), equivalences, solved);
#endif
  } else if (res == 20)
    sweep_empty_clause (sweeper);

DONE:
  clear_sweeper (sweeper);

  if (!solver->inconsistent && !kissat_propagated (solver))
    (void) kissat_dense_propagate (solver);

  if (success && limit_reached)
    return "successfully despite reaching limit";
  if (!success && !limit_reached)
    return "unsuccessfully without reaching limit";
  else if (success && !limit_reached)
    return "successfully without reaching limit";
  assert (!success && limit_reached);
  return "unsuccessfully and reached limit";
}

typedef struct sweep_candidate sweep_candidate;

struct sweep_candidate {
  unsigned rank;
  unsigned idx;
};

// clang-format off

typedef STACK(sweep_candidate) sweep_candidates;

// clang-format on

#define RANK_SWEEP_CANDIDATE(CAND) (CAND).rank

/**
 *  Checks how many watches idx has
 *  if zero positive watches or zero negative watches, returns false.
    Else: sets occ = pos_watches + neg_watches
 */
static bool scheduable_variable (sweeper *sweeper, unsigned idx,
                                 size_t *occ_ptr) {
  kissat *solver = sweeper->solver;
  const unsigned lit = LIT (idx);
  const size_t pos = SIZE_WATCHES (WATCHES (lit));
  if (!pos)
    return false;
  const unsigned max_occurrences = sweeper->limit.clauses;
  if (pos > max_occurrences)
    return false;
  const unsigned not_lit = NOT (lit);
  const size_t neg = SIZE_WATCHES (WATCHES (not_lit));
  if (!neg)
    return false;
  if (neg > max_occurrences)
    return false;
  *occ_ptr = pos + neg;
  return true;
}

/**
 * Puts *every* admissable kissat variable in the scheduling queue, those with the least watched clauses (but >0) come in front
 */
static unsigned schedule_all_other_not_scheduled_yet (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  sweep_candidates fresh;
  INIT_STACK (fresh);
  flags *const flags = solver->flags;
  const bool incomplete = solver->sweep_incomplete;

  // const size_t mallob_solver_id = GET_OPTION(mallob_solver_id);
  // const size_t mallob_solver_count = GET_OPTION(mallob_solver_count);
  // size_t round_robin_count = 0;
  // const size_t LOG_CUTOFF = 30;
  // kissat_custom_message(solver, V3_VVERB_SWEEP, "Total variables: %i, Solver id %i, Solver count %i", solver->vars, mallob_solver_id, mallob_solver_count);
  /**
   * check every variable for active and scheduable
   */
  for (all_variables (idx)) {

    struct flags *const f = flags + idx;
    if (!f->active) {
      // if (idx<LOG_CUTOFF) kissat_custom_message(solver,V3_VVERB_SWEEP, "skip %i: !active",idx);
      continue;
    }
    if (incomplete && !f->sweep) {
      // if (idx<LOG_CUTOFF) kissat_custom_message(solver,V3_VVERB_SWEEP, "skip %i: !sweep",idx);
      continue;
    }
    if (scheduled_variable (sweeper, idx)) {
      // if (idx<LOG_CUTOFF) kissat_custom_message(solver,V3_VVERB_SWEEP, "skip %i: already scheduled",idx);
      continue;
    }
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      FLAGS (idx)->sweep = false;
      // if (idx<LOG_CUTOFF) kissat_custom_message(solver,V3_VVERB_SWEEP, "skip %i: !scheduable",idx);
      continue;
    }
    //
    // if (!passed_round_robin)
    //   continue;


    // if (SIZE_STACK(fresh) < 100) {
      // kissat_custom_message(solver, V3_VVERB_SWEEP, "Stack %i (e%i) wc %i", idx, eidx, occ);
    // }

    sweep_candidate cand;
    cand.rank = occ;
    cand.idx = idx;
    PUSH_STACK (fresh, cand);
  }
  const size_t size = SIZE_STACK (fresh);
  assert (size <= UINT_MAX);

  RADIX_STACK (sweep_candidate, unsigned, fresh, RANK_SWEEP_CANDIDATE);
  /*
   * Variables are now sorted ascending by their watchlist-count
   * Insert them in the scheduling queue such that the LOWEST watchlist counts are popped FIRST
   */
  size_t enqueued_vars = 0;
  for (all_stack (sweep_candidate, cand, fresh)) {
    schedule_outer (sweeper, cand.idx);
    enqueued_vars++;
    // if (enqueued_vars < LOG_CUTOFF || enqueued_vars > size - LOG_CUTOFF) {
      // unsigned elit = kissat_export_literal (solver, LIT (cand.idx));
      // unsigned eidx = elit & 0x7FFFFFF;
      // kissat_custom_message (solver, V3_VVERB_SWEEP, "Enqueued %i (e%i), wc %i", cand.idx, eidx, cand.rank);
    // }
  }

  RELEASE_STACK (fresh);
  return size;
}


/*
 * Empties the remaining-stack and puts selected variables back to the end of the schedule queue
 * (variable put back if active AND not-yet-scheduled AND scheduable)
 */
static unsigned reschedule_previously_remaining (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned rescheduled = 0;
  unsigneds *remaining = &solver->sweep_schedule;
  for (all_stack (unsigned, idx, *remaining)) {
    struct flags *f = flags + idx;
    if (!f->active)
      continue;
    if (scheduled_variable (sweeper, idx))
      continue;
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      f->sweep = false;
      continue;
    }
    schedule_inner (sweeper, idx);
    rescheduled++;
  }
  RELEASE_STACK (*remaining);
  return rescheduled;
}

/*
 *  Counts the number of variables not yet sweept but in queue
 */
static unsigned incomplete_variables (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned res = 0;
  for (all_variables (idx)) {
    struct flags *f = flags + idx;
    if (!f->active)
      continue;
    if (f->sweep)
      res++;
  }
  return res;
}

static void mark_incomplete (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned marked = 0;
  for (all_scheduled (idx))
    if (!flags[idx].sweep) {
      flags[idx].sweep = true;
      marked++;
    }
  solver->sweep_incomplete = true;
#ifndef QUIET
  kissat_extremely_verbose (
      solver, "marked %u scheduled sweeping variables as incomplete",
      marked);
#else
  (void) marked;
#endif
}

/*
 * Set up the variables to sweep, and their order. Returns the number of scheduled variables
 */
static unsigned schedule_sweeping (sweeper *sweeper) {
  const unsigned rescheduled = reschedule_previously_remaining (sweeper);
  const unsigned fresh = schedule_all_other_not_scheduled_yet (sweeper);
  const unsigned scheduled = fresh + rescheduled;
  const unsigned incomplete = incomplete_variables (sweeper);
  kissat *solver = sweeper->solver;

#ifndef QUIET
  kissat_phase (solver, "sweep", GET (sweep),
                "scheduled %u variables %.0f%% "
                "(%u rescheduled %.0f%%, %u incomplete %.0f%%)",
                scheduled,
                kissat_percent (scheduled, sweeper->solver->active),
                rescheduled, kissat_percent (rescheduled, scheduled),
                incomplete, kissat_percent (incomplete, scheduled));
#endif
  if (incomplete)
    assert (solver->sweep_incomplete);
  else {
    if (solver->sweep_incomplete)
      INC (sweep_completed);
    mark_incomplete (sweeper);
  }
  return scheduled;
}






static void unschedule_sweeping (sweeper *sweeper, unsigned swept,
                                 unsigned scheduled) {
  kissat *solver = sweeper->solver;
#ifdef QUIET
  (void) scheduled, (void) swept;
#endif
  assert (EMPTY_STACK (solver->sweep_schedule));
  assert (solver->sweep_incomplete);
  flags *flags = solver->flags;
  for (all_scheduled (idx))
    if (flags[idx].active) {
      PUSH_STACK (solver->sweep_schedule, idx);
      LOG ("untried scheduled %s", LOGVAR (idx));
    }
#ifndef QUIET
  const unsigned retained = SIZE_STACK (solver->sweep_schedule);
  kissat_extremely_verbose (
      solver, "retained %u variables %.0f%% to be swept next time",
      retained, kissat_percent (retained, solver->active));
#endif
  const unsigned incomplete = incomplete_variables (sweeper);
  if (incomplete)
    kissat_extremely_verbose (
        solver, "need to sweep %u more variables %.0f%% for completion",
        incomplete, kissat_percent (incomplete, solver->active));
  else {
    kissat_extremely_verbose (solver,
                              "no more variables needed to complete sweep");
    solver->sweep_incomplete = false;
    INC (sweep_completed);
  }
  kissat_phase (solver, "sweep", GET (sweep),
                "swept %u variables (%u remain %.0f%%)", swept, incomplete,
                kissat_percent (incomplete, scheduled));
}




bool shweep_var_still_open(sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  // kissat_custom_message(solver,V2_VERB_SWEEP, " check idx=%u", idx);
  unsigned lit = LIT(idx);
  if (!FLAGS(idx)->sweep)
    return false;
  if (!ACTIVE(idx))
    return false;
  if (sweep_repr (sweeper, lit) != lit)
    return false;
  size_t occ;
  if (!scheduable_variable (sweeper, idx, &occ)) {
    FLAGS (idx)->sweep = false;
    return false;
  }
  return true;
}


void shweep_import_units(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  if (!solver->shweep_import_units_callback)
    return;
  int *imported_units = 0;
  int unit_count = 0;

  solver->shweep_import_units_callback(solver->shweep_mallob_KissatState, &imported_units, &unit_count);

  if (unit_count==0)
    return;

  kissat_custom_message(solver, V2_VERB_SWEEP, "about to import %i units", unit_count);
  solver->shweep_total_units += unit_count;

  unsigned long prev_useful = solver->shweep_useful_imported_units;
  unsigned long prev_invalid = solver->shweep_invalid_imported_units;
  unsigned long prev_fixed = solver->shweep_fixed_imported_units;
  unsigned long prev_eliminated = solver->shweep_eliminated_imported_units;
  unsigned long prev_transitive = solver->shweep_transitive_imported_units;

  for (int i=0; i<unit_count; i++) {
    const unsigned unit = imported_units[i];
    const unsigned repr_unit = sweep_repr (sweeper, unit);

    const bool is_transitive = (unit != repr_unit);

    if (!VALID_INTERNAL_LITERAL (repr_unit)) {
      kissat_custom_message(solver, V1_INFO_SWEEP, "invalid unit repr_unit=%u, imported as unit=%u", repr_unit, unit);
      solver->shweep_invalid_imported_units++;
      continue;
    }

    const unsigned repr_idx = IDX (repr_unit);
    flags *flags = FLAGS (repr_idx);

    if (!flags->active) {
      // kissat_custom_message(solver, V2_VERB_SWEEP, "inactive variable repr_idx=%u, imported as unit=%u", repr_idx, unit);
      solver->shweep_fixed_imported_units++;
      continue;
    }
    if (flags->eliminated) {
      // kissat_custom_message(solver, V2_VERB_SWEEP, "eliminated variable repr_idx=%u, imported as unit=%u", repr_idx, unit);
      solver->shweep_eliminated_imported_units++;
      continue;
    }

    if (is_transitive) {
      // kissat_custom_message(solver, V2_VERB_SWEEP, "transitive useful unit. repr_idx=%u, imported as unit=%u", repr_idx, unit);
      solver->shweep_transitive_imported_units++;
      //no continue, just tracking
    }

    kissat_custom_message(solver, V3_VVERB_SWEEP," importing idx(%i),lit(%i),repr_lit(%i)", IDX(repr_unit), unit, repr_unit);
    kissat_assign_unit (solver, repr_unit, "shweep imported unit");
    solver->shweep_useful_imported_units++;
    INC (sweep_units);
  }
  // kissat_custom_message (solver, V1_INFO_SWEEP, "Unit import statistics:");
  kissat_custom_message(solver, V2_VERB_SWEEP,"Imported Units:", unit_count);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Useful     %i / %i", solver->shweep_useful_imported_units - prev_useful, unit_count);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Invalid    %i", solver->shweep_invalid_imported_units - prev_invalid);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Fixed      %i", solver->shweep_fixed_imported_units - prev_fixed);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Eliminated %i", solver->shweep_eliminated_imported_units - prev_eliminated);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Transitive %i", solver->shweep_transitive_imported_units - prev_transitive);
  // kissat_custom_message(solver, V2_VERB_SWEEP, "Inconsistent? %i", solver->inconsistent);
}

void shweep_import_equivalences(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  if (!solver->shweep_import_eq_callback)
    return;

  int *imported_eq = 0;
  int eqs_size = 0;
  solver->shweep_import_eq_callback(solver->shweep_mallob_KissatState, &imported_eq, &eqs_size);
  assert(eqs_size%2==0);
  int eq_count = eqs_size/2;

  if (eq_count==0)
    return;

  assert(eq_count < 10000); //hotfix for debug, I once saw eq_count = 680.000.000 ish, catch these cases

  kissat_custom_message(solver, V2_VERB_SWEEP, "about to import %u equivalences", eq_count);

  unsigned long prev_useful = solver->shweep_useful_imported_eq;
  unsigned long prev_invalid = solver->shweep_invalid_imported_eq;
  unsigned long prev_unitprop = solver->shweep_unitprop_imported_eq;
  unsigned long prev_doublefixed = solver->shweep_doublefixed_imported_eq;
  unsigned long prev_eliminated = solver->shweep_eliminated_imported_eq;
  unsigned long prev_tautology = solver->shweep_tautological_imported_eq;
  unsigned long prev_transitive = solver->shweep_transitive_imported_eq;
  solver->shweep_total_eq += eq_count;

  for (int eq=0; eq < eq_count; eq++) {
    unsigned repr_ilits[2];
    bool okToImport = true;
    bool is_transitive = false;
    int already_fixed = 0;
    for (int i=0; i<2; i++) {
      const unsigned ilit = imported_eq[2*eq+i];
      // kissat_custom_message(solver, V3_VVERB_SWEEP,"importing lit(%i)", ilit);
      const unsigned repr_ilit = sweep_repr(sweeper, ilit);
      // kissat_custom_message(solver, V2_VERB_SWEEP, "eq %i: ilit %i repr %i", eq, ilit, repr_ilit);

      if (!VALID_INTERNAL_LITERAL (ilit)) {
        kissat_custom_message(solver, V1_INFO_SWEEP, "ilit %i failed assertion", ilit);
        assert (VALID_INTERNAL_LITERAL (ilit));
      }
      if (!VALID_INTERNAL_LITERAL (repr_ilit)) {
        kissat_custom_message(solver, V1_INFO_SWEEP, "repr_ilit %i failed assertion", repr_ilit);
        assert (VALID_INTERNAL_LITERAL (repr_ilit));
      }


      if (ilit != repr_ilit)
        is_transitive = true;

      if (!VALID_INTERNAL_LITERAL (repr_ilit)) {
        kissat_custom_message(solver, V1_INFO_SWEEP, "invalid internal literal repr_ilit=%u, imported as lit=%u", repr_ilit, ilit);
	solver->shweep_invalid_imported_eq++;
        okToImport = false;
        break;
      }
      const unsigned repr_idx = IDX (repr_ilit);
      flags *flags = FLAGS (repr_idx);
      //Commented out, because we want to import equivalences where one literal is already set! Means we have a gratis unit propagation!
      if (!flags->active) {
        already_fixed++;
      }
        // kissat_custom_message(solver, V2_VERB_SWEEP, "inactive internal literal repr_ilit=%u, imported as lit=%u", repr_ilit, ilit);
        // solver->shweep_inactive_imported_eq++;
        // okToImport = false;
        // break;
      // }
      if (flags->eliminated) {
        assert(kissat_custom_assert_message(solver, V1_INFO_SWEEP, "Error: imported eliminated eq-literal ilit(%i), elimination shouldn't exist", ilit));
        // solver->shweep_eliminated_imported_eq++;
        // okToImport = false;
        break;
      }
      repr_ilits[i]=repr_ilit;
    }


    if (!okToImport) {
      solver->shweep_skipped_imported_eq++;
      continue;
    }

    unsigned lit    = repr_ilits[0];
    unsigned other  = repr_ilits[1];

    if (IDX(lit) == IDX(other)) {
      // kissat_custom_message (solver, V2_VERB_SWEEP, " taut a==a");
      solver->shweep_tautological_imported_eq++;
      solver->shweep_skipped_imported_eq++;
      continue;
    }

    if (already_fixed==2) {
      //both values are already set, but the local solver didn't knew they were equivalent
      assert(solver->values[repr_ilits[0]] == solver->values[repr_ilits[1]]);
      solver->shweep_doublefixed_imported_eq++;
      //maybe its unnecessary at this point to introduce this equivalence, since anyways both units are already propagated...
      //skip for now
      continue;
    }


    if (already_fixed==1) //one of the two variables is already fixed, meaning this equivalence becomes a unit clause
      solver->shweep_unitprop_imported_eq++;


    if (other < lit) {
      unsigned tmp = lit;
      lit = other;
      other = tmp;
    }
    assert(lit < other);

    const unsigned not_lit = NOT (lit);
    const unsigned not_other = NOT (other);

    if (is_transitive)
      solver->shweep_transitive_imported_eq++;

    // assert(lit < other);

    // kissat_custom_message(solver, V2_VERB_SWEEP, "importing equality %i==%i", lit, other);

    kissat_custom_message(solver, V3_VVERB_SWEEP," imported idx(%i)==idx(%i), lit(%i)==lit(%i)", IDX(lit), IDX(other), lit, other);

    //maybe need also to add these two binary clauses? are added by original sweep_equivalence_candidates, for the cores...
    // add_binary (solver, lit,     not_other);
    // add_binary (solver, not_lit, other);

    sweeper->reprs[other] = lit;
    sweeper->reprs[not_other] = not_lit;
     /*
      * Actually replacing 'other' by 'lit' in all clauses
      */
    substitute_connected_clauses (sweeper, other, lit);
    substitute_connected_clauses (sweeper, not_other, not_lit);
    solver->shweep_useful_imported_eq++;
    INC (sweep_equivalences);
  }

  kissat_custom_message(solver, V2_VERB_SWEEP,"Imported Eqs:");
  kissat_custom_message(solver, V2_VERB_SWEEP, "Useful     %i / %i", solver->shweep_useful_imported_eq - prev_useful, eq_count);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Invalid    %i", solver->shweep_invalid_imported_eq - prev_invalid);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Unitprop   %i", solver->shweep_unitprop_imported_eq - prev_unitprop);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Doublefixd %i", solver->shweep_doublefixed_imported_eq - prev_doublefixed);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Eliminated %i", solver->shweep_eliminated_imported_eq - prev_eliminated);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Tautology  %i", solver->shweep_tautological_imported_eq - prev_tautology);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Transitive %i", solver->shweep_transitive_imported_eq - prev_transitive);
  // kissat_custom_message(solver, V2_VERB_SWEEP, "Inconsistent? %i", solver->inconsistent);
  sweeper->just_imported_eqs=true;

}


unsigned shweep_get_num_vars(kissat *solver) {
  return solver->vars;
}

//Want to allocate memory in C++ for the steal, but don't know yet how much memory, so we ask first here
//To know how much there is work left, needs to be compacted first
int shweep_get_max_steal_amount(kissat *solver) {
  if (!solver || !solver->sweeper || !solver->sweeper->initialized) {
    //guard against very early stealing attempts where this solver is not even initialized yet. happens quite often.
    kissat_custom_message(solver,V3_VVERB_SWEEP, "somebody tried to rob me, but I am not fully initialized yet");
    return 0;
  }
  sweeper *sweeper = solver->sweeper;
  int range_left = sweeper->work_end - sweeper->work_head;
  int count_left = sweeper->max_work_left;
  int min_left = MIN(count_left, range_left);
  int half = min_left/2;
  // if (half!=0)
    // kissat_custom_message(solver,V2_VERB_SWEEP, "found %i max_steal_amount (work_head=%i, work_end=%i, count_left=%i)", half, sweeper->work_head, sweeper->work_end, sweeper->max_work_left);
  return half;
}



//Mallob wants to steal half of this solvers work
//Mallob provides arrays "stolen_work" that we only fill
int shweep_steal_from_this_solver(kissat *solver, unsigned *stolen_work, int max_steal_count) {
  sweeper *sweeper = solver->sweeper;
  //steal every second local variable that is still open for sweeping
  // kissat_custom_message(solver,V2_VERB_SWEEP, "Incoming steal begins, could give up to %i", max_steal_count);
  int stolen_count=0;
  int locally_left = 0;
  bool steal_flipflop=false;
  unsigned *work = sweeper->work;
  const int work_end = sweeper->work_end;
  for (int i = sweeper->work_head; i < work_end; i++) {
    unsigned idx = work[i];
    if (idx==INVALID_IDX) //the variable that had been written at this spot has already been stolen or deactivated
      continue;
    if (!shweep_var_still_open(sweeper, idx)) { //this variable is no longer relevant for sweeping
      work[i] = INVALID_IDX;  //deactivate it, such that we don't have to check it again
      continue;
    }
    //variable is still open for sweeping. We steal every second
    if (steal_flipflop && stolen_count < max_steal_count) { //it could maybe happen that in the split second after determining it's max_steal_count this solver receives new work, and has now more work to provide than C++ expects
      stolen_work[stolen_count]=idx; //steal
      stolen_count++;
      work[i] = INVALID_IDX; //deactivate in original array
    } else {
      locally_left++;
    }
    steal_flipflop = !steal_flipflop;
  }
  kissat_custom_message(solver,V2_VERB_SWEEP, "#");
  kissat_custom_message(solver,V2_VERB_SWEEP, "# >> Providing %i (left %i)", stolen_count, locally_left);
  kissat_custom_message(solver,V2_VERB_SWEEP, "#");
  if (stolen_count > max_steal_count) {
    kissat_custom_message (solver, V1_INFO_SWEEP, "Error: stolen_count=%i, max_steal_count=%i", stolen_count, max_steal_count);
    assert(kissat_custom_assert_message (solver, V1_INFO_SWEEP, "stolen count > max_steal_count"));
  }
  sweeper->max_work_left = locally_left;
  return stolen_count;
}




unsigned shweep_search_work_from_others(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  //reset own counters, to signal to other stealers that we currently have nothing to offer
  sweeper->work_head = 0;
  sweeper->work_end = 0;
  sweeper->max_work_left = 0;

  kissat_custom_message (solver, V2_VERB_SWEEP, "searching for work");

  //Decouple stolen_amount from work_end as long as possible, to not have spurious reset-writes on work_end influence the logic here
  int stolen_amount = 0;
  const int local_id = GET_OPTION(mallob_local_id);

  //The new work will be allocated by Mallob/C++, and we will only read from it, by pointing our *work array on the provided data
  if (solver->shweep_search_work_callback) {
    solver->shweep_search_work_callback(solver->shweep_mallob_SweepJobState, &sweeper->work, &stolen_amount, local_id);
  } else if (!sweeper->debug_singlethread_created_work){
    //for debugging: running a single instance of kissat without Mallob/MPI overhead. Create work on my own.
    //Obviously, must deallocate this array here in the single threaded case, which is allocated by C++ in the full distributed run
    NALLOC (sweeper->work, VARS);
    for (unsigned idx = 0; idx < VARS; idx++) {
      sweeper->work[idx] = idx;
    }
    stolen_amount = VARS;
    sweeper->debug_singlethread_created_work=true;
  }

  kissat_custom_message(solver,V2_VERB_SWEEP, "*");
  if (stolen_amount>0)
    kissat_custom_message (solver, V2_VERB_SWEEP, "* << Got %i", stolen_amount);
  if (stolen_amount==0)
    kissat_custom_message (solver, V2_VERB_SWEEP, "* Sweep: received termination signal");
  kissat_custom_message(solver,V2_VERB_SWEEP, "*");
  // const int end = sweeper->work_end;
  const unsigned *work = sweeper->work;
  flags *flags = solver->flags;
  //We mark all stolen upcoming variables as to-sweep.
  //It can then happen that a variable is sweeped early due to equivalence re-shweeping.
  //In that case we can skip it later, noticing it by the falsified sweep flag
  for (int i=0; i<stolen_amount; i++) {
    flags[work[i]].sweep = true;
  }
  sweeper->work_head = 0;
  sweeper->work_end = stolen_amount;
  sweeper->max_work_left = stolen_amount;
  return sweeper->work_end;
}


bool shweep_sweepable_variable(sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  if (!ACTIVE (idx))
    return false;
  // if (!FLAGS(idx)->sweep) //the sweep flag is our own indicator whether we WANT to sweep, but these other checks are hard necessary requierements
    // return false;
  const unsigned lit = LIT (idx);
  if (sweeper->reprs[lit] != lit)
    return false;
  size_t occ;
  if (!scheduable_variable (sweeper, idx, &occ)) {
    FLAGS (idx)->sweep = false;
    // kissat_custom_message(solver,V3_VVERB_SWEEP, "skip %i: !scheduable",idx);
    return false;
  }
  return true;
}

void shweep_sweep_variable_with_prop(sweeper *sweeper, unsigned idx) {

  if (!shweep_sweepable_variable(sweeper, idx))
    return;

  shweep_import_units(sweeper);
  shweep_import_equivalences (sweeper);

  kissat *solver = sweeper->solver;

  kissat_custom_message(solver,V3_VVERB_SWEEP, "sweeping idx %i [%i=head, %i max left]", idx, sweeper->work_head, sweeper->max_work_left);

  FLAGS (idx)->sweep = false; //remember that we sweept this variable now. //still part of old sweeping. maybe in case of shweep we dont need this flag? leave it in for now...
  sweep_variable(sweeper, idx);

  sweeper->just_imported_eqs=false;

  //Re-sweep all equivalences that have been found in the last sweep
  //This can become recursive, where we eagerly always re-sweep first on the last found equivalence
  while (!EMPTY_STACK (sweeper->RESWEEP)) {
    unsigned resweep_idx = POP_STACK (sweeper->RESWEEP);
    kissat_custom_message(solver,V3_VVERB_SWEEP, "re-shweep idx %i [%i SIZE_STACK]", resweep_idx, SIZE_STACK (sweeper->RESWEEP));
    shweep_sweep_variable_with_prop (sweeper, resweep_idx);
  }
}

unsigned shweep_next_scheduled(sweeper *sweeper) {
  unsigned *work = sweeper->work;

  const int end  = sweeper->work_end;
  while (sweeper->work_head < end) {
    unsigned idx = work[sweeper->work_head++];
    sweeper->max_work_left = MIN(sweeper->max_work_left, end - sweeper->work_head);
    if (idx==INVALID_IDX) //skip hole
      continue;
    if (shweep_var_still_open(sweeper, idx)) {
      return idx;
    }
    // kissat_custom_message (sweeper->solver, V2_VERB_SWEEP, "    skip work[%i]=%u", head-1, work[head-1]);
    sweeper->skipped_bc_done++;
  }
  return INVALID_IDX;
}



void shweep_print_import_statistics(kissat *solver) {
  kissat_custom_message(solver, V1_INFO_SWEEP, "--------------");
  kissat_custom_message(solver, V1_INFO_SWEEP, "Final stats: Equivalences:");
  kissat_custom_message(solver, V1_INFO_SWEEP, "Useful     %i / %i ", solver->shweep_useful_imported_eq, solver->shweep_total_eq);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Invalid    %i", solver->shweep_invalid_imported_eq);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Unitprop   %i", solver->shweep_unitprop_imported_eq);
  kissat_custom_message(solver, V2_VERB_SWEEP, "Doublefixd %i", solver->shweep_doublefixed_imported_eq);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Eliminated %i", solver->shweep_eliminated_imported_eq);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Tautology  %i", solver->shweep_tautological_imported_eq);
  kissat_custom_message(solver, V1_INFO_SWEEP, "--------------");
  kissat_custom_message(solver, V1_INFO_SWEEP, "Final stats: Units:");
  kissat_custom_message(solver, V1_INFO_SWEEP, "Useful     %i / %i", solver->shweep_useful_imported_units, solver->shweep_total_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Invalid    %i", solver->shweep_invalid_imported_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Fixed      %i", solver->shweep_fixed_imported_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Eliminated %i", solver->shweep_eliminated_imported_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Transitive %i", solver->shweep_transitive_imported_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "Stumbled   %i", solver->sweeper->stumbled_units);
  kissat_custom_message(solver, V1_INFO_SWEEP, "--------------");
}



int kissat_mallob_shweep(kissat *solver) {
  kissat_custom_message(solver,V1_INFO_SWEEP, "--Jumped into kissat_mallob_shweep--");
  if (!GET_OPTION (mallob_is_shweeper))
    return false;
  if (solver->inconsistent) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "--exiting because solver->inconsistent--");
    return false;
  }
  if (TERMINATED (sweep_terminated_7))
    return false;
  if (DELAYING (sweep)) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "--exiting because DELAYING(sweep)--");
    return false;
  }
  assert (!solver->level);
  assert (!solver->unflushed);
  assert( !solver->probing);
  // solver->probing=true; //is also set to true for normal probing, of which sweep is part of, so probably good to have this here
  START (sweep);
  INC (sweep);
  statistics *statistics = &solver->statistics;
  uint64_t equivalences = statistics->sweep_equivalences;
  uint64_t units = statistics->sweep_units;
  sweeper sweeper;
  kissat_custom_message(solver,V1_INFO_SWEEP, "--init_sweeper--");
  init_sweeper (solver, &sweeper);

  kissat_custom_message(solver,V1_INFO_SWEEP, "--active=%d--", solver->active);
  // kissat_custom_message(solver,V1_INFO_SWEEP, "--unassigned=%d--", solver->unassigned);
  kissat_custom_message(solver,V1_INFO_SWEEP, "--starting shweep loop--");
  // shweep_import_equivalences(&sweeper);
  // shweep_search_work_from_others(&sweeper);

  for (;;) {
    if (solver->inconsistent) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "SHWEEP INCONSISTENT during loop!! \n");
      // kissat_custom_message(solver,V1_INFO_SWEEP, "invalid eq       %i", solver->shweep_invalid_imported_eq);
      // kissat_custom_message(solver,V1_INFO_SWEEP, "invalid units    %i", solver->shweep_invalid_imported_units);
      // kissat_custom_message(solver,V1_INFO_SWEEP, "unitprop         %i", solver->shweep_unitprop_imported_eq);
      // kissat_custom_message(solver,V1_INFO_SWEEP, "eliminated       %i", solver->shweep_eliminated_imported_eq);
      break;
    }
    if (TERMINATED (sweep_terminated_8))
      break;
    if (solver->statistics.kitten_ticks > sweeper.limit.ticks) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "# \n # \n Kitten Tick limit timeout \n # \n #");
      break;
    }

    unsigned idx = shweep_next_scheduled (&sweeper);

    if (idx == INVALID_IDX) {
      //we ran out of work. try to steal from somebody
      if (!shweep_search_work_from_others (&sweeper)) {
        break;
      }
      continue;
    }
    shweep_sweep_variable_with_prop (&sweeper, idx);

  }

  sweeper.shweep_terminated = true;
  shweep_print_import_statistics(solver);
  /*
    * Finished sweeping. Some cleanup and statistics.
    */
  equivalences = statistics->sweep_equivalences - equivalences,
  units = solver->statistics.sweep_units - units;
  kissat_phase (solver, "sweep", GET (sweep),
                "found %" PRIu64 " equivalences and %" PRIu64 " units",
                equivalences, units);
  kissat_custom_message (solver, V1_INFO_SWEEP, "Shweep: Found %i equivalences and %i units", equivalences, units);
  // unschedule_sweeping (&sweeper, swept, scheduled);
  unsigned inactive = release_sweeper (&sweeper);


  kissat_custom_message(solver,V1_INFO_SWEEP, "--active=%d--", solver->active);
  // kissat_custom_message(solver,V1_INFO_SWEEP, "--unassigned=%d--", solver->unassigned);

  START (probe);
  assert (!solver->probing);
  solver->probing = true;
  if (!solver->inconsistent) {
    solver->propagate = solver->trail.begin;
    kissat_custom_message(solver,V1_INFO_SWEEP, "final probing");
    kissat_probing_propagate (solver, 0, true);
  }
  assert (solver->probing);
  STOP (probe);

  kissat_custom_message(solver,V1_INFO_SWEEP, "--active=%d--", solver->active);

  STOP (sweep);
  if (solver->inconsistent)
    kissat_custom_message (solver, V1_INFO_SWEEP, "SHWEEP INCONSISTENT after loop !!");


  unsigned active_before = solver->active;
  //Equivalent Literal Subsitution.
  //Applies the equivalences we found to actually reduce the database.
  //Is Scheduled always directly after sweeping also in normal kissat.
  if (GET_OPTION (substitute)) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "running substitute.c for equivalent substitutions");
    kissat_substitute (solver, true);
  } else {
    kissat_custom_message(solver,V1_INFO_SWEEP, "skipping substitute.c, OPTION substitute==0 !");
  }

  solver->probing = false;

  kissat_custom_message(solver,V1_INFO_SWEEP, "--active=%d--", solver->active);
  kissat_custom_message(solver,V1_INFO_SWEEP, "--Substitute: %d --> %d active variables--", active_before, solver->active);

  kissat_custom_message(solver,V1_INFO_SWEEP, "--exit shweep--");
  //Shared Sweeping is finished.
  //We send the termination signal now, since this was the only job of this solver
  //Actually, before the check for termination the function "kissat_report_dimacs(...)" is still called,
  //so eventhough this solver is already set to terminate, the final formula reporting still takes place
  kissat_terminate(solver); //
  return 0; //allows search.c to continue with cascade until "kissat_report_dimacs(...)"
}












// int call_sweep_app(kissat *solver) {
  // if ( ! solver->start_sweep_app_callback)
    // return 0;
  // bool finished_flag = false;
  // solver->start_sweep_app_callback (solver->shweep_mallob_KissatState);
  //todo: as the main solver, talk with Mallob and start a distributed sweeping job
  //receive units and equivalences from this job (either at the end, or maybe already live)
  //replaces the single-threaded sweeping that this solver would have done otherwise
  // return 0;
// }


bool kissat_sweep (kissat *solver) {
  if (GET_OPTION (mallob_is_shweeper)) {
    assert(kissat_custom_assert_message (solver, V1_INFO_SWEEP, "error: Shweeper accidentally got into original sweeping code"));
    return false;
  }
  if (!GET_OPTION (sweep))
    return false;
  if (solver->inconsistent)
    return false;
  if (TERMINATED (sweep_terminated_7))
    return false;
  if (DELAYING (sweep))
    return false;
  assert (!solver->level);
  assert (!solver->unflushed);
  START (sweep);
  INC (sweep);
  statistics *statistics = &solver->statistics;
  uint64_t equivalences = statistics->sweep_equivalences;
  uint64_t units = statistics->sweep_units;
  sweeper sweeper;
  // kissat_custom_message(solver,V1_INFO_SWEEP, "--starting kissat_sweep--");
  init_sweeper (solver, &sweeper);

  /*
    * Set up the variables to sweep over and their order
    */
  const unsigned scheduled = schedule_sweeping (&sweeper);
  uint64_t swept = 0, limit = 10;

  /*
     * Sweep the formula until all kitten-ticks are consumed.
     * Always start with a new root variable and full-sweep its environment
     */
  for (;;) {
    if (solver->inconsistent) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "--during sweep-loop: Inconsistent 1\n");
      kissat_custom_message(solver,V1_INFO_SWEEP, "invalid_external %i", solver->shweep_invalid_imported_eq);
      kissat_custom_message(solver,V1_INFO_SWEEP, "invalid_internal %i", solver->shweep_invalid_imported_eq);
      kissat_custom_message(solver,V1_INFO_SWEEP, "unitprop         %i", solver->shweep_unitprop_imported_eq);
      kissat_custom_message(solver,V1_INFO_SWEEP, "eliminated       %i", solver->shweep_eliminated_imported_eq);
      break;
    }
    if (TERMINATED (sweep_terminated_8))
      break;
    if (solver->statistics.kitten_ticks > sweeper.limit.ticks)
      break;
    /*
     * Get the next root-variable "idx" to sweep around
     */
    unsigned idx = next_scheduled (&sweeper);
    if (idx == INVALID_IDX)
      break;
    FLAGS (idx)->sweep = false; //remember that we sweept this variable now
    // kissat_custom_message(solver, V3_VVERB_SWEEP, "Sw %i (e%i)", idx, kissat_export_literal (solver, LIT (idx)));
#ifndef QUIET
    const char *res =
#endif
        sweep_variable (&sweeper, idx);
    /*
     * Sweept the environment of this variable. Hope to split some equivalences or find direct assignments.
     */

    kissat_extremely_verbose (
        solver, "swept[%" PRIu64 "] external variable %d %s", swept,
        kissat_export_literal (solver, LIT (idx)), res);
    if (++swept == limit) {
      kissat_very_verbose (solver,
                           "found %" PRIu64 " equivalences and %" PRIu64
                           " units after sweeping %" PRIu64 " variables ",
                           statistics->sweep_equivalences - equivalences,
                           solver->statistics.sweep_units - units, swept);
      limit *= 10;
    }
  }
  /*
    * Finished sweeping. Some cleanup and statistics.
    */
  kissat_very_verbose (solver, "swept %" PRIu64 " variables", swept);

  equivalences = statistics->sweep_equivalences - equivalences,
  units = solver->statistics.sweep_units - units;
  kissat_phase (solver, "sweep", GET (sweep),
                "found %" PRIu64 " equivalences and %" PRIu64 " units",
                equivalences, units);
  unschedule_sweeping (&sweeper, swept, scheduled);
  unsigned inactive = release_sweeper (&sweeper);

  if (!solver->inconsistent) {
    solver->propagate = solver->trail.begin;
    kissat_probing_propagate (solver, 0, true);
  }

  uint64_t eliminated = equivalences + units;
#ifndef QUIET
  assert (solver->active >= inactive);
  solver->active -= inactive;
  REPORT (!eliminated, '=');
  solver->active += inactive;
#else
  (void) inactive;
#endif
  if (kissat_average (eliminated, swept) < 0.001)
    BUMP_DELAY (sweep);
  else
    REDUCE_DELAY (sweep);
  STOP (sweep);
  // kissat_custom_message(solver,V1_INFO_SWEEP, "exit sweep function. Inconsistent?-Inc%i ", solver->inconsistent);
  return eliminated;
}
