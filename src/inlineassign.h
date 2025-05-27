#ifndef _inlineassign_h_INLCUDED
#define _inlineassign_h_INLCUDED

#ifdef FAST_ASSIGN
#define kissat_assign kissat_fast_assign
#endif





 /*
  *Assign a given literal. Level is the decision level. For assigned unit clauses from backbone sweeping, level=0
  */
static inline void kissat_assign (kissat *solver, const bool probing,
                                  const unsigned level,
#ifdef FAST_ASSIGN
                                  value *values, assigned *assigned,
#endif
                                  bool binary, unsigned lit,
                                  unsigned reason) {
  const unsigned not_lit = NOT (lit);

   /*
    *Since we assign lit=1, the clauses watched by not_lit must be updated and search for a new watcher
    */
  watches watches = WATCHES (not_lit);
  if (!kissat_empty_vector (&watches)) {
    watch *w = BEGIN_WATCHES (watches);
    __builtin_prefetch (w, 0, 1);
  }

#ifndef FAST_ASSIGN
  value *values = solver->values;
#endif
  assert (!values[lit]);
  assert (!values[not_lit]);

   /*
    * Explicitly set the literal value to true
    *
    * Not quite sure why we do this redundant work of storing the variable value two times, for lit and not_lit, as they contain exactly the same information
    * Maybe it makes it a bit more convenient to code, but we could also just read values[lit] and negate it when we need it for not_lit ?
    * Especially since this approach here consumes 16 bits per lit when in theory only 2 bits would be needed (assigned/unassigned, true/false)
    */
  values[lit] = 1;
  values[not_lit] = -1;

  assert (solver->unassigned > 0);
  solver->unassigned--;

  if (!level) {
    kissat_mark_fixed_literal (solver, lit);
    assert (solver->unflushed < UINT_MAX);
    solver->unflushed++;
    if (reason != UNIT_REASON) {
      CHECK_AND_ADD_UNIT (lit);
      ADD_UNIT_TO_PROOF (lit);
      reason = UNIT_REASON;
      binary = false;
    }
  }

  const size_t trail = SIZE_ARRAY (solver->trail);
  PUSH_ARRAY (solver->trail, lit);

  const unsigned idx = IDX (lit);

#if !defined(PROBING_PROPAGATION)
  if (!probing) {
    const bool negated = NEGATED (lit);
    const value new_value = BOOL_TO_VALUE (negated);
    value *saved = &SAVED (idx);
    *saved = new_value;
  }
#endif

   /*
    *store some information about this literal assignment
    */
  struct assigned b;

  b.level = level;
  b.trail = trail;

  b.analyzed = false;
  b.binary = binary;
  b.poisoned = false;
  b.reason = reason;
  b.removable = false;
  b.shrinkable = false;

#ifndef FAST_ASSIGN
  assigned *assigned = solver->assigned;
#endif
  struct assigned *a = assigned + idx;
  *a = b;
}













static inline unsigned
kissat_assignment_level (kissat *solver, value *values, assigned *assigned,
                         unsigned lit, clause *reason) {
  unsigned res = 0;
  for (all_literals_in_clause (other, reason)) {
    if (other == lit)
      continue;
    assert (values[other] < 0), (void) values;
    const unsigned other_idx = IDX (other);
    struct assigned *a = assigned + other_idx;
    const unsigned level = a->level;
    if (res < level)
      res = level;
  }
#ifdef NDEBUG
  (void) solver;
#endif
  return res;
}

#endif
