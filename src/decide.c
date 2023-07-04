#include "decide.h"
#include "heap.h"
#include "inlineframes.h"
#include "inlineheap.h"
#include "inlinequeue.h"
#include "inline.h" // new
#include "inlinescore.h"
#include "stack.h"

#include <inttypes.h>
#include <float.h>

static unsigned
last_enqueued_unassigned_variable (kissat * solver)
{
  assert (solver->unassigned);
  const links *const links = solver->links;
  const value *const values = solver->values;
  unsigned res = solver->queue.search.idx;
  if (values[LIT (res)])
    {
      do
	{
	  res = links[res].prev;
	  assert (!DISCONNECTED (res));
	}
      while (values[LIT (res)]);
      kissat_update_queue (solver, links, res);
    }
#ifdef LOGGING
  const unsigned stamp = links[res].stamp;
  LOG ("last enqueued unassigned %s stamp %u", LOGVAR (res), stamp);
#endif
#ifdef CHECK_QUEUE
  for (unsigned i = links[res].next; !DISCONNECTED (i); i = links[i].next)
    assert (VALUE (LIT (i)));
#endif
  return res;
}

static unsigned
largest_score_unassigned_variable (kissat * solver)
{
  unsigned res = kissat_max_heap (&solver->scores);
  const value *const values = solver->values;
  while (values[LIT (res)])
    {
      kissat_pop_max_heap (solver, &solver->scores);
      res = kissat_max_heap (&solver->scores);
    }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_get_heap_score (&solver->scores, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  for (all_variables (idx))
    {
      if (!ACTIVE (idx))
	continue;
      if (VALUE (LIT (idx)))
	continue;
      const double idx_score = kissat_get_heap_score (&solver->scores, idx);
      assert (score >= idx_score);
    }
#endif
  return res;
}

unsigned random_unassigned_variable (kissat * solver)
{
  --solver->nb_fanout_decisions;
  ++solver->attempted_fanout_decisions;
  unsigned rnd_pos = kissat_pick_random (&solver->random, 0, kissat_size_heap (&solver->scores));
  unsigned rnd_idx = PEEK_STACK (solver->scores.stack, rnd_pos);
  const value *const values = solver->values;
  unsigned nb_fails = 0;
  while (values[LIT (rnd_idx)]) {
    nb_fails++;
    if (nb_fails == 10) return -1;
    rnd_pos = kissat_pick_random (&solver->random, 0, kissat_size_heap (&solver->scores));
    rnd_idx = PEEK_STACK (solver->scores.stack, rnd_pos);
  }
  //printf("random decision #%i/%i picked idx %i after %i fails  (%i unassigned / %i total)\n",
  //  solver->options.fanoutdepth-solver->nb_fanout_decisions+1,
  //  solver->options.fanoutdepth, rnd_idx, nb_fails,
  //  solver->unassigned, (int)kissat_size_heap (&solver->scores));
  ++solver->successful_fanout_decisions;
  return rnd_idx;
}

unsigned
kissat_next_decision_variable (kissat * solver)
{
  unsigned res;
  if (solver->nb_fanout_decisions) {
    res = random_unassigned_variable (solver);
    if (res != -1u) return res;
    //printf("random decision failed! (%i unassigned / %i total)\n",
    //  solver->unassigned, (int) kissat_size_heap (&solver->scores));
  }
  if (solver->stable)
    res = largest_score_unassigned_variable (solver);
  else
    res = last_enqueued_unassigned_variable (solver);
  LOG ("next decision %s", LOGVAR (res));
  return res;
}

static inline value
decide_phase (kissat * solver, unsigned idx)
{
  bool force = GET_OPTION (forcephase);

  value *target;
  if (force)
    target = 0;
  else if (!GET_OPTION (target))
    target = 0;
  else if (solver->stable || GET_OPTION (target) > 1)
    target = solver->phases.target + idx;
  else
    target = 0;

  value *saved;
  if (force)
    saved = 0;
  else if (GET_OPTION (phasesaving))
    saved = solver->phases.saved + idx;
  else
    saved = 0;

  value res = 0;

  // NEW: use user-provided initial variable phases at most ONCE per literal
  int elit = kissat_export_literal (solver, LIT (idx));
  if (!res && elit >= 0 && elit < solver->initial_variable_phases_len)
    {
      // may be 0
      res = solver->initial_variable_phases[elit];
      solver->initial_variable_phases[elit] = 0; // mark initial phase as spent - do not use again
    }

  if (!res && target && (res = *target))
    {
      LOG ("%s uses target decision phase %d", LOGVAR (idx), (int) res);
      INC (target_decisions);
    }

  if (!res && saved && (res = *saved))
    {
      LOG ("%s uses saved decision phase %d", LOGVAR (idx), (int) res);
      INC (saved_decisions);
    }
  
  if (!res)
    {
      res = INITIAL_PHASE;
      LOG ("%s uses initial decision phase %d", LOGVAR (idx), (int) res);
      INC (initial_decisions);
    }
  assert (res);

  return res;
}

void
kissat_decide (kissat * solver)
{
  START (decide);
  assert (solver->unassigned);
  INC (decisions);
  if (solver->stable)
    INC (stable_decisions);
  else
    INC (focused_decisions);
  solver->level++;
  assert (solver->level != INVALID_LEVEL);
  const unsigned idx = kissat_next_decision_variable (solver);
  const value value = decide_phase (solver, idx);
  unsigned lit = LIT (idx);
  if (value < 0)
    lit = NOT (lit);
  kissat_push_frame (solver, lit);
  assert (solver->level < SIZE_STACK (solver->frames));
  LOG ("decide literal %s", LOGLIT (lit));
  kissat_assign_decision (solver, lit);
  STOP (decide);
}

void
kissat_internal_assume (kissat * solver, unsigned lit)
{
  assert (solver->unassigned);
  assert (!VALUE (lit));
  solver->level++;
  assert (solver->level != INVALID_LEVEL);
  kissat_push_frame (solver, lit);
  assert (solver->level < SIZE_STACK (solver->frames));
  LOG ("assuming literal %s", LOGLIT (lit));
  kissat_assign_decision (solver, lit);
}
