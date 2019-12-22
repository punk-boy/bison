/* Conflict counterexample generation
 
 Copyright (C) 2019-2020 Free Software Foundation, Inc.
 
 This file is part of Bison, the GNU Compiler Compiler.
 
 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include <config.h>
#include <time.h>
#include <hash.h>
#include <stdlib.h>
#include <gl_linked_list.h>
#include <gl_xlist.h>
#include <gl_rbtreehash_list.h>
#include "counterexample.h"
#include "derivation.h"
#include "gram.h"
#include "complain.h"
#include "closure.h"
#include "nullable.h"
#include "getargs.h"
#include "lalr.h"
#include "parse-simulation.h"
#include "lssi.h"


#define TIME_LIMIT_ENFORCED true
/** If set to false, only consider the states on the shortest
 *  lookahead-sensitive path when constructing a unifying counterexample. */
#define EXTENDED_SEARCH false

/* various costs for making various steps in a search */
#define PRODUCTION_COST 50
#define REDUCE_COST 1
#define SHIFT_COST 1
#define UNSHIFT_COST 1
#define DUPLICATE_PRODUCTION_COST 0
#define EXTENDED_COST 10000

/** The time limit before printing an assurance message to the user to
 *  indicate that the search is still running. */
#define ASSURANCE_LIMIT 2.0f

/* The time limit before giving up looking for unifying counterexample. */
#define TIME_LIMIT 5.0f

#define CUMULATIVE_TIME_LIMIT 120.0f

typedef struct
{
  derivation *d1;
  derivation *d2;
  bool unifying;
  bool timeout;
} counterexample;

counterexample *
new_counterexample (derivation *d1, derivation *d2, bool u, bool t)
{
  counterexample *ret = xmalloc (sizeof (counterexample));
  ret->d1 = d1;
  ret->d2 = d2;
  ret->unifying = u;
  ret->timeout = t;
  return ret;
}

void
print_counterexample (counterexample *cex)
{
  if (cex->unifying)
    printf ("Example ");
  else
    printf ("First Example");
  derivation_print_leaves (cex->d1, stdout);
  printf ("\nFirst derivation ");
  derivation_print (cex->d1, stdout);
  if (!cex->unifying)
    {
      printf ("\nSecond example ");
      derivation_print_leaves (cex->d2, stdout);
    }
  printf ("\nSecond derivation ");
  derivation_print (cex->d2, stdout);
  fputs ("\n\n", stdout);
}

/*
 *
 * NON UNIFYING COUNTER EXAMPLES
 *
 */

// Search node for BFS on state items
struct si_bfs_node;
typedef struct si_bfs_node
{
  state_item_number si;
  struct si_bfs_node *parent;
  int reference_count;
} si_bfs_node;

si_bfs_node *
si_bfs_new (state_item_number si, si_bfs_node *parent)
{
  si_bfs_node *ret = xcalloc (1, sizeof (si_bfs_node));
  ret->si = si;
  ret->parent = parent;
  ret->reference_count = 0;
  if (parent)
    ++parent->reference_count;
  return ret;
}

void
si_bfs_free (si_bfs_node *n)
{
  if (n == NULL)
    return;
  if (n->reference_count == 0)
    {
      if (n->parent)
        {
          --n->parent->reference_count;
          si_bfs_free (n->parent);
        }
      free (n);
    }
}

/**
 * Repeatedly take production steps on the given StateItem so that the
 * first symbol of the derivation matches the conflict symbol.
 */
static inline gl_list_t
expand_first (state_item *start, symbol_number next_sym)
{
  si_bfs_node *init = si_bfs_new (start - state_items, NULL);

  gl_list_t queue = gl_list_create (GL_LINKED_LIST, NULL, NULL,
                                    (gl_listelement_dispose_fn) si_bfs_free,
                                    true, 1, (const void **) &init);
  si_bfs_node *node;
  // breadth-first search
  while (gl_list_size (queue) > 0)
    {
      node = (si_bfs_node *) gl_list_get_at (queue, 0);
      state_item *silast = state_items + node->si;
      symbol_number sym = item_number_as_symbol_number (*(silast->item));
      if (sym == next_sym)
        break;
      if (ISVAR (sym))
        {
          bitset_iterator biter;
          state_item_number sin;
          bitset sib = prods_lookup (node->si);
          BITSET_FOR_EACH (biter, sib, sin, 0)
            {
              const si_bfs_node *sn;
              for (sn = node; sn != NULL; sn = sn->parent)
                if (sn->si == sin)
                  break;
              if (sn)
                continue;
              si_bfs_node *next = si_bfs_new (sin, node);
              gl_list_add_last (queue, next);
            }
          if (nullable[sym - ntokens])
            {
              // If the nonterminal after dot is nullable,
              // we need to look further.
              si_bfs_node *next = si_bfs_new (trans[node->si], node);
              gl_list_add_last (queue, next);
            }
        }
      gl_list_remove_at (queue, 0);
    }
  if (gl_list_size (queue) == 0)
    {
      gl_list_free (queue);
      if (trace_flag & trace_cex)
        puts ("Error expanding derivation");
      return NULL;
    }
  // done - construct derivation

  derivation *dinit = derivation_new (next_sym, NULL);
  gl_list_t result =
    gl_list_create (GL_LINKED_LIST, NULL, NULL,
                    (gl_listelement_dispose_fn) derivation_free,
                    true, 1, (const void **) &dinit);
  for (si_bfs_node *n = node; n != NULL; n = n->parent)
    {
      state_item *si = state_items + n->si;
      item_number *pos = si->item;
      if (pos == ritem || item_number_is_rule_number (*(pos - 1)))
        {
          item_number *i;
          for (i = pos + 1; !item_number_is_rule_number (*i); ++i)
            gl_list_add_last (result, derivation_new (*i, NULL));
          symbol_number lhs =
            rules[item_number_as_rule_number (*i)].lhs->number;
          derivation *deriv = derivation_new (lhs, result);
          result =
            gl_list_create (GL_LINKED_LIST, NULL, NULL,
                            (gl_listelement_dispose_fn) derivation_free,
                            true, 1, (const void **) &deriv);
        }
      else
        {
          derivation *deriv =
            derivation_new (item_number_as_symbol_number (*(pos - 1)), NULL);
          gl_list_add_first (result, deriv);
        }
    }
  gl_list_free (queue);
  gl_list_remove_at (result, 0);
  return result;
}

/**
 * Auxiliary method to complete any pending productions in the given
 * sequence of parser states.
 */
derivation *
complete_diverging_example (symbol_number next_sym,
                            gl_list_t states, gl_list_t derivs)
{
  // The idea is to transfer each pending symbol on the productions
  // associated with the given StateItems to the resulting derivation.
  gl_list_t result =
    gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, true);
  if (!derivs)
    derivs = gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, true);
  bool lookahead_required = false;
  // This is the fastest way to get the tail node from the gl_list API
  gl_list_node_t tmpd = gl_list_add_last (derivs, NULL);
  gl_list_node_t tmps = gl_list_add_last (states, NULL);
  gl_list_node_t deriv = gl_list_previous_node (derivs, tmpd);
  gl_list_node_t state = gl_list_previous_node (states, tmps);
  gl_list_remove_node (derivs, tmpd);
  gl_list_remove_node (states, tmps);
  for (; state != NULL; state = gl_list_previous_node (states, state))
    {
      state_item *si = (state_item *) gl_list_node_value (states, state);
      item_number *item = si->item;
      item_number pos = *item;
      // symbols after dot
      if (gl_list_size (result) == 0)
        {
          if (gl_list_size (derivs) == 0)
            {
              gl_list_add_last (result, derivation_dot ());
              lookahead_required = true;
            }
          if (!item_number_is_rule_number (pos))
            {
              gl_list_add_last (result,
                                derivation_new (item_number_as_symbol_number
                                                (pos), NULL));
              lookahead_required = false;
            }
        }
      item_number *i;
      for (i = item; !item_number_is_rule_number (*i); ++i)
        {
          if (i == item)
            continue;
          symbol_number sym = item_number_as_symbol_number (*i);
          if (lookahead_required)
            {
              if (sym != next_sym)
                {
                  // Need to expand sym to match nextSym
                  if (!nullable[sym - ntokens]
                      || bitset_test (FIRSTS (sym), next_sym))
                    {
                      state_item *trans_si =
                        &state_items[trans[si - state_items]];
                      gl_list_t next_derivs =
                        expand_first (trans_si, next_sym);
                      if (!next_derivs)
                        // easiest way to not break everything on an error.
                        return derivation_dot ();
                      gl_list_iterator_t it = gl_list_iterator (next_derivs);
                      derivation *tmp;
                      while (gl_list_iterator_next
                             (&it, (const void **) &tmp, NULL))
                        gl_list_add_last (result, tmp);
                      i += gl_list_size (next_derivs) - 1;
                      gl_list_free (next_derivs);
                      lookahead_required = false;

                    }
                  else
                    {
                      // This nonterminal is nullable and cannot derive next_sym.
                      // So, this nonterminal must derive the empty string,
                      // and next_sym must be derived by a later nonterminal.
                      derivation *d = derivation_new (sym,
                                                      gl_list_create_empty
                                                      (GL_LINKED_LIST,
                                                       NULL, NULL,
                                                       NULL, 1));
                      gl_list_add_last (result, d);
                    }
                }
              else
                {
                  gl_list_add_last (result, derivation_new (sym, NULL));
                  lookahead_required = false;
                }
            }
          else
            gl_list_add_last (result, derivation_new (sym, NULL));

        }
      rule_number r = item_number_as_rule_number (*i);
      // symbols before dot
      for (i = item - 1; !item_number_is_rule_number (*i) && i >= ritem; i--)
        {
          gl_list_node_t p = gl_list_previous_node (states, state);
          if (p)
            state = p;
          if (deriv)
            {
              const void *tmp_deriv = gl_list_node_value (derivs, deriv);
              deriv = gl_list_previous_node (derivs, deriv);
              gl_list_add_first (result, tmp_deriv);
            }
          else
            gl_list_add_first (result, derivation_new (*i, NULL));
        }
      // completing the derivation
      derivation *new_deriv = derivation_new (rules[r].lhs->number, result);
      result =
        gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, true, 1,
                        (const void **) &new_deriv);
    }
  derivation *ret = (derivation *) gl_list_get_at (result, 0);
  gl_list_free (result);
  return ret;
}

/* iterates backwards through the shifts of the path in the
   reduce conflict, and finds a path of shifts in the shift
   conflict that goes through the same states.
 */
gl_list_t
nonunifying_shift_path (gl_list_t reduce_path, state_item *shift_conflict)
{
  gl_list_node_t tmp = gl_list_add_last (reduce_path, NULL);
  gl_list_node_t next_node = gl_list_previous_node (reduce_path, tmp);
  gl_list_node_t node = gl_list_previous_node (reduce_path, next_node);
  gl_list_remove_node (reduce_path, tmp);
  state_item *si = shift_conflict;
  gl_list_t result =
    gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, true, 1,
                    (const void **) &si);
  bool paths_merged;
  for (; node != NULL; next_node = node,
       node = gl_list_previous_node (reduce_path, node))
    {
      state_item *refsi =
        (state_item *) gl_list_node_value (reduce_path, node);
      state_item *nextrefsi =
        (state_item *) gl_list_node_value (reduce_path, next_node);
      if (nextrefsi == si)
        {
          gl_list_add_first (result, refsi);
          continue;
        }
      // skip reduction items
      if (nextrefsi->item != refsi->item + 1 && refsi->item != ritem)
        continue;

      // bfs to find a shift to the right state
      si_bfs_node *init = si_bfs_new (si - state_items, NULL);
      gl_list_t queue =
        gl_list_create (GL_LINKED_LIST, NULL, NULL,
                        (gl_listelement_dispose_fn) si_bfs_free,
                        true, 1, (const void **) &init);
      while (gl_list_size (queue) > 0)
        {
          si_bfs_node *sis = (si_bfs_node *) gl_list_get_at (queue, 0);
          state_item *sisrc = state_items + sis->si;
          item_number *srcpos = sisrc->item;
          // Reverse Transition
          symbol_number sym = *(srcpos - 1);
          // Only look for state compatible with the shortest path.
          bitset rsi = rev_trans[sis->si];
          bitset_iterator biter;
          state_item_number sin;
          state_item *prevsi = NULL;
          BITSET_FOR_EACH (biter, rsi, sin, 0)
            {
              state_item *psi = state_items + sin;
              if (psi->state == refsi->state)
                {
                  prevsi = psi;
                  // BITSET_FOR_EACH is two nested for loops
                  goto biter_exit;
                }
              si = prevsi;
              if (prevsi)
                si_list_prepend (result, si);
              break;
            }
        biter_exit:
          if (prevsi || sisrc == state_items)
            {
              for (si_bfs_node *n = sis; n->parent != NULL; n = n->parent)
                gl_list_add_first (result, state_items + n->si);
              si = prevsi;
              if (prevsi)
                gl_list_add_first (result, si);
              break;
            }
          // Reverse Production
          bitset rps = rev_prods_lookup (sisrc - state_items);
          if (rps)
            {
              bitset_iterator biter2;
              BITSET_FOR_EACH (biter2, rps, sin, 0)
                {
                  si_bfs_node *n;
                  for (n = sis; n != NULL; n = n->parent)
                    if (n->si == sin)
                      break;
                  if (!n)
                    {
                      si_bfs_node *prevsis = si_bfs_new (sin, sis);
                      gl_list_add_last (queue, prevsis);
                    }
                }
            }
          gl_list_remove_at (queue, 0);
        }
      gl_list_free (queue);
    }
  if (trace_flag & trace_cex)
    {
      puts ("SHIFT ITEM PATH:");
      gl_list_iterator_t it = gl_list_iterator (result);
      state_item *sip;
      while (gl_list_iterator_next (&it, (const void **) &sip, NULL))
        print_state_item (sip, stdout);
    }
  return result;
}


/**
 * Construct a nonunifying counterexample from the shortest
 * lookahead-sensitive path.
 */
counterexample *
example_from_path (bool shift_reduce, state_item_number itm2,
                   gl_list_t shortest_path, symbol_number next_sym)
{
  derivation *deriv1 =
    complete_diverging_example (next_sym, shortest_path, NULL);
  gl_list_t path_2 = shift_reduce ? nonunifying_shift_path (shortest_path,
                                                            &state_items
                                                            [itm2]) :
    shortest_path_from_start (itm2, next_sym);
  derivation *deriv2 = complete_diverging_example (next_sym, path_2, NULL);
  gl_list_free (path_2);
  return new_counterexample (deriv1, deriv2, false, true);
}

/*
 *
 * UNIFYING COUNTER EXAMPLES
 *
 */

/* A search state keeps track of two parser simulations,
 * one starting at each conflict. Complexity is a metric
 * which sums different parser actions with varying weights.
 */
typedef struct
{
  parse_state *states[2];
  int complexity;
} search_state;

static search_state *
empty_search_state (void)
{
  search_state *ret = xmalloc (sizeof (search_state));
  ret->states[0] = empty_parse_state ();
  ret->states[1] = empty_parse_state ();
  ++ret->states[0]->reference_count;
  ++ret->states[1]->reference_count;
  ret->complexity = 0;
  return ret;
}

static search_state *
new_search_state (parse_state *ps1, parse_state *ps2, int complexity)
{
  search_state *ret = xmalloc (sizeof (search_state));
  ret->states[0] = ps1;
  ret->states[1] = ps2;
  ++ret->states[0]->reference_count;
  ++ret->states[1]->reference_count;
  ret->complexity = complexity;
  return ret;
}

static search_state *
copy_search_state (search_state *parent)
{
  search_state *copy = xmalloc (sizeof (search_state));
  memcpy (copy, parent, sizeof (search_state));
  ++copy->states[0]->reference_count;
  ++copy->states[1]->reference_count;
  return copy;
}

static void
search_state_free_children (search_state *ss)
{
  free_parse_state (ss->states[0]);
  free_parse_state (ss->states[1]);
}

static void
search_state_free (search_state *ss)
{
  if (ss == NULL)
    return;
  search_state_free_children (ss);
  free (ss);
}

static void
search_state_print (search_state *ss)
{
  fputs ("CONFLICT 1 ", stdout);
  print_parse_state (ss->states[0]);
  fputs ("CONFLICT 2 ", stdout);
  print_parse_state (ss->states[1]);
  putc ('\n', stdout);
}

/* When a search state is copied, theses should be used
 * for operations which only change one parse state
 * init is used when the parse state is changed manually,
 * and set is used when there's a parse state ready to
 * replace what the copy has.
 */
static inline parse_state *
ss_init_parse_state (search_state *ss, int index, bool prepend)
{
  --ss->states[index]->reference_count;
  parse_state *ret = copy_parse_state (prepend, ss->states[index]);
  ss->states[index] = ret;
  ++ret->reference_count;
  return ret;
}

static inline void
ss_set_parse_state (search_state *ss, int index, parse_state *ps)
{
  --ss->states[index]->reference_count;
  ss->states[index] = ps;
  ++ps->reference_count;
}

/* Search states are stored in bundles with those that
 * share the same complexity. This is so the priority
 * queue takes less overhead.
 */
typedef struct
{
  gl_list_t states;
  int complexity;
} search_state_bundle;

void
ssb_free (search_state_bundle *ssb)
{
  gl_list_free (ssb->states);
  free(ssb);
}

static size_t
ssb_hasher (search_state_bundle *ssb)
{
  return ssb->complexity;
}

static int
ssb_comp (search_state_bundle *s1, search_state_bundle *s2)
{
  return s1->complexity - s2->complexity;
}

static bool
ssb_equals (search_state_bundle *s1, search_state_bundle *s2)
{
  return s1->complexity == s2->complexity;
}

static size_t
visited_hasher (search_state *ss, size_t max)
{
  ps_chunk *sis1 = &ss->states[0]->state_items;
  ps_chunk *sis2 = &ss->states[1]->state_items;
  return ((state_item *) sis1->head_elt - state_items +
          (state_item *) sis1->tail_elt - state_items +
          (state_item *) sis2->head_elt - state_items +
          (state_item *) sis2->tail_elt - state_items +
          sis1->total_size + sis2->total_size) % max;
}

static bool
visited_comparator (search_state *ss1, search_state *ss2)
{
  ps_chunk *sis11 = &ss1->states[0]->state_items;
  ps_chunk *sis12 = &ss1->states[1]->state_items;
  ps_chunk *sis21 = &ss2->states[0]->state_items;
  ps_chunk *sis22 = &ss2->states[1]->state_items;
  return sis11->head_elt == sis21->head_elt &&
    sis11->tail_elt == sis21->tail_elt &&
    sis11->total_size == sis21->total_size &&
    sis12->head_elt == sis22->head_elt &&
    sis12->tail_elt == sis22->tail_elt &&
    sis12->total_size == sis22->total_size;
}

/** Priority queue for search states with minimal complexity. */
static gl_list_t ssb_queue;
static Hash_table *visited;
/** The set of parser states on the shortest lookahead-sensitive path. */
static bitset scp_set;
/** The set of parser states used for the conflict reduction rule. */
static bitset rpp_set;

static void
ssb_append (search_state *ss)
{
  if (hash_lookup (visited, ss))
    {
      search_state_free (ss);
      return;
    }
  if (!hash_insert (visited, ss))
    xalloc_die ();
  ss->states[0]->visited = true;
  ss->states[1]->visited = true;
  ++ss->states[0]->reference_count;
  ++ss->states[1]->reference_count;
  search_state_bundle *ssb = xmalloc (sizeof (search_state_bundle));
  ssb->complexity = ss->complexity;
  gl_list_node_t n = gl_list_search (ssb_queue, ssb);
  if (!n)
    {
      ssb->states = gl_list_create_empty (GL_LINKED_LIST,
                                          NULL, NULL,
                                          search_state_free_children, true);
      gl_sortedlist_add (ssb_queue, (gl_listelement_compar_fn) ssb_comp, ssb);
    }
  else
    {
      free (ssb);
      ssb = (search_state_bundle *) gl_list_node_value (ssb_queue, n);
    }
  gl_list_add_last (ssb->states, ss);
}

/*
 * Construct a nonunifying example from a search state
 * which has its parse states unified at the beginning
 * but not the end of the example.
 */
counterexample *
complete_diverging_examples (search_state *ss, symbol_number next_sym)
{
  derivation *derivs[2];
  for (int i = 0; i < 2; ++i)
    {
      parse_state *ps = empty_parse_state ();
      size_t si_size = ss->states[i]->state_items.total_size;
      size_t deriv_size = ss->states[i]->derivs.total_size;
      parser_pop (ss->states[i], si_size, deriv_size, ps);
      derivs[i] = complete_diverging_example (next_sym,
                                              ps->state_items.contents,
                                              ps->derivs.contents);
      free_parse_state (ps);
    }
  return new_counterexample (derivs[0], derivs[1], false, true);
}

static void
production_step (search_state *ss, int parser_state)
{
  state_item *other_si = ss->states[1 - parser_state]->state_items.tail_elt;
  symbol_number other_sym = item_number_as_symbol_number (*other_si->item);
  gl_list_t prods = simulate_production (ss->states[parser_state], other_sym);
  int complexity = ss->complexity + PRODUCTION_COST;

  gl_list_iterator_t it = gl_list_iterator (prods);
  parse_state *ps;
  while (gl_list_iterator_next (&it, (const void **) &ps, NULL))
    {
      search_state *copy = copy_search_state (ss);
      ss_set_parse_state (copy, parser_state, ps);
      copy->complexity = complexity;
      ssb_append (copy);
    }
}

/**
 * Compute the number of production steps made
 *  in the parser state
 */
static int
reduction_cost (parse_state *ps)
{
  // only count fully formed productions
  parse_state *current_ps = ps;
  while (current_ps->parent != NULL)
    current_ps = current_ps->parent;

  gl_list_t sis = current_ps->state_items.contents;
  int count = 0;
  gl_list_iterator_t it = gl_list_iterator (sis);
  state_item *last = NULL;
  state_item *next = NULL;
  while (gl_list_iterator_next (&it, (const void **) &next, NULL))
    {
      if (last && last->state == next->state)
        ++count;
      last = next;
    }
  return UNSHIFT_COST *(current_ps->state_items.total_size - count)
    + PRODUCTION_COST *count;
}

static gl_list_t
reduction_step (search_state *ss, item_number *conflict_item,
                int parser_state, int rule_len)
{
  gl_list_t result =
    gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, 1);

  parse_state *ps = ss->states[parser_state];
  state_item *si = (state_item *) ps->state_items.tail_elt;
  bitset symbol_set = si->lookahead;
  parse_state *other = (state_item *) ss->states[1 - parser_state];
  state_item *other_si = other->state_items.tail_elt;
  // if the other state can transition on a symbol,
  // the reduction needs to have that symbol in its lookahead
  if (item_number_is_symbol_number (*other_si->item))
    {
      symbol_number other_sym =
        item_number_as_symbol_number (*other_si->item);
      if (!intersect_symbol (other_sym, symbol_set))
        return result;
      symbol_set = bitset_create (nsyms, BITSET_FIXED);
      bitset_set (symbol_set, other_sym);
    }

  search_state *new_root = copy_search_state (ss);
  gl_list_t reduced = simulate_reduction (ps, conflict_item,
                                          rule_len, symbol_set);
  gl_list_iterator_t it = gl_list_iterator (reduced);
  parse_state *reduced_ps;
  while (gl_list_iterator_next (&it, (const void **) &reduced_ps, NULL))
    {
      search_state *copy = copy_search_state (ss);
      ss_set_parse_state (copy, parser_state, reduced_ps);
      int r_cost = reduction_cost (reduced_ps);
      copy->complexity += r_cost + PRODUCTION_COST + 2 * SHIFT_COST;
      gl_list_add_last (result, copy);
    }
  return result;
}

/**
 * Attempt to prepend the given symbol to this search state, respecting
 * the given subsequent next symbol on each path.
 */
void
search_state_prepend (search_state *ss, symbol_number sym, bitset guide)
{
  state_item *si1src = (state_item *) ss->states[0]->state_items.head_elt;
  state_item *si2src = (state_item *) ss->states[1]->state_items.head_elt;
  bitset si1_lookahead = si1src->lookahead;
  bitset si2_lookahead = si2src->lookahead;
  bitset prev1 = NULL, prev2 = NULL;
  bitset prev1ext =
    lssi_reverse_transition (si1src - state_items, sym, si1_lookahead, guide);
  bitset prev2ext =
    lssi_reverse_transition (si2src - state_items, sym, si2_lookahead, guide);
  if (EXTENDED_SEARCH)
    {
      prev1 = prev1ext;
      prev2 = prev2ext;
      prev1ext =
        lssi_reverse_transition (si1src - state_items, sym, si1_lookahead,
                                 NULL);
      prev2ext =
        lssi_reverse_transition (si2src - state_items, sym, si2_lookahead,
                                 NULL);
    }
  bitset_set (prev1ext, si1src - state_items);
  bitset_set (prev2ext, si2src - state_items);
  bitset_iterator biter;
  state_item_number sin;
  BITSET_FOR_EACH (biter, prev1ext, sin, 0)
    {
      bool guided1 = !EXTENDED_SEARCH || bitset_test (prev1, sin);
      state_item *psi1 = state_items + sin;
      bitset_iterator biter2;
      state_item_number sin2;
      BITSET_FOR_EACH (biter2, prev2ext, sin2, 0)
        {
          bool guided2 = !EXTENDED_SEARCH || bitset_test (prev2, sin);
          state_item *psi2 = state_items + sin2;
          // Only continue if the StateItems on both paths are the same.
          if (psi1 == si1src && psi2 == si2src)
            continue;
          if (psi1->state != psi2->state)
            continue;
          search_state *copy = copy_search_state (ss);
          parse_state *ps1 = ss_init_parse_state (copy, 0, true);
          parse_state *ps2 = ss_init_parse_state (copy, 1, true);

          if (psi1 != si1src)
            ps_chunk_prepend (&ps1->state_items, psi1);
          if (psi2 != si2src)
            ps_chunk_prepend (&ps2->state_items, psi2);
          int production_steps = 0;
          if (psi1 != si1src && psi1->item + 1 == si1src->item)
            {
              if (psi2 != si2src && psi2->item + 1 == si2src->item)
                {
                  // Both are reverse transitions; add appropriate
                  // derivation of the corresponding symbol used for
                  // the reverse transition.
                  derivation *deriv = derivation_new (sym, NULL);
                  ps_chunk_prepend (&ps1->derivs, deriv);
                  ps_chunk_prepend (&ps2->derivs, deriv);
                }
              else
                {
                  search_state_free (copy);
                  continue;
                }
            }
          else if (psi2 != si2src && psi2->item + 1 == si2src->item)
            {
              search_state_free (copy);
              continue;
            }
          else
            production_steps = 2;
          // At this point, either reverse transition is made on both paths,
          // or reverse production is made on both paths.
          // Now, compute the complexity of the new search state.
          int prepend_size = (psi1 ? 1 : 0) + (psi2 ? 1 : 0);
          copy->complexity += PRODUCTION_COST *production_steps +
            UNSHIFT_COST * (prepend_size - production_steps);
          if (!guided1 || !guided2)
            copy->complexity += EXTENDED_COST;
          ssb_append (copy);
        }
    }
}

/**
 * Determine if the productions associated with the given parser items have
 * the same prefix up to the dot.
 */
static bool
has_common_prefix (item_number *itm1, item_number *itm2)
{
  int i = 0;
  for (; !item_number_is_rule_number (*(itm1 + i)); ++i)
    if (*(itm1 + i) != *(itm2 + i))
      return false;
  return item_number_is_rule_number (*(itm2 + i));
}

/*
 * Calculate the start and end locations of an item in ritem.
 */
static void
item_rule_bounds (item_number *item, item_number **start,
                  item_number **end)
{
  item_number *s, *e;
  for (s = item; item_number_is_symbol_number (*(s - 1)); --s);
  *start = s;

  for (e = item; item_number_is_symbol_number (*e); ++e);
  *end = e;
}

/*
 * Perform the appropriate possible parser actions
 * on a search state and add the results to the
 * search state priority queue.
 */
static inline void
generate_next_states (search_state *ss, state_item *conflict1,
                      state_item *conflict2)
{
  // Compute the successor configurations.
  parse_state *ps1 = ss->states[0];
  parse_state *ps2 = ss->states[1];
  const state_item *si1 = ps1->state_items.tail_elt;
  const state_item *si2 = ps2->state_items.tail_elt;
  bool si1reduce = item_number_is_rule_number (*si1->item);
  bool si2reduce = item_number_is_rule_number (*si2->item);
  if (!si1reduce && !si2reduce)
    {
      // Transition if both paths end at the same symbol
      if (*si1->item == *si2->item)
        {
          int complexity = ss->complexity + 2 * SHIFT_COST;
          gl_list_t trans1 = simulate_transition (ps1);
          gl_list_t trans2 = simulate_transition (ps2);
          gl_list_iterator_t it1 = gl_list_iterator (trans1);
          parse_state *tps1;
          while (gl_list_iterator_next (&it1, (const void **) &tps1, NULL))
            {
              gl_list_iterator_t it2 = gl_list_iterator (trans2);
              parse_state *tps2;
              while (gl_list_iterator_next
                     (&it2, (const void **) &tps2, NULL))
                ssb_append (new_search_state (tps1, tps2, complexity));
            }
          gl_list_free (trans1);
          gl_list_free (trans2);
        }

      // Take production steps if possible.
      production_step (ss, 0);
      production_step (ss, 1);
    }
  // One of the states requires a reduction
  else
    {
      item_number *rhs1, *rhe1;
      item_rule_bounds (si1->item, &rhs1, &rhe1);
      int len1 = rhe1 - rhs1;
      int size1 = ps1->state_items.total_size;
      bool ready1 = si1reduce && len1 < size1;

      item_number *rhs2, *rhe2;
      item_rule_bounds (si2->item, &rhs2, &rhe2);
      int len2 = rhe2 - rhs2;
      int size2 = ps2->state_items.total_size;
      bool ready2 = si2reduce && len2 < size2;
      // If there is a path ready for reduction
      // without being prepended further, reduce.
      if (ready1)
        {
          gl_list_t reduced1 = reduction_step (ss, conflict1->item, 0, len1);
          gl_list_iterator_t iter = gl_list_iterator (reduced1);
          search_state *red1;
          if (ready2)
            {
              gl_list_add_last (reduced1, ss);
              while (gl_list_iterator_next
                     (&iter, (const void **) &red1, NULL))
                {
                  gl_list_t reduced2 =
                    reduction_step (red1, conflict2->item, 1, len2);
                  gl_list_iterator_t iter2 = gl_list_iterator (reduced2);
                  search_state *red2;
                  while (gl_list_iterator_next
                         (&iter2, (const void **) &red2, NULL))
                    ssb_append (red2);
                  // avoid duplicates
                  if (red1 != ss)
                    ssb_append (red1);
                  gl_list_free (reduced2);
                }
            }
          else
            while (gl_list_iterator_next (&iter, (const void **) &red1, NULL))
              ssb_append (red1);
          gl_list_free (reduced1);
        }
      else if (ready2)
        {
          gl_list_t reduced2 = reduction_step (ss, conflict2->item, 1, len2);
          gl_list_iterator_t iter2 = gl_list_iterator (reduced2);
          search_state *red2;
          while (gl_list_iterator_next (&iter2, (const void **) &red2, NULL))
            ssb_append (red2);
          gl_list_free (reduced2);
        }
      // Otherwise, prepend both paths and continue.
      // This is preparing both paths for a reduction.
      else
        {
          symbol_number sym;
          if (si1reduce && !ready1)
            sym = *(rhs1 + len1 - size1);
          else
            sym = *(rhs2 + len2 - size2);
          search_state_prepend (ss, sym,
                                ss->states[0]->depth >= 0 ? rpp_set : scp_set);
        }
    }
}

/*
 * Perform the actual counter example search,
 * keeps track of what stage of the search algorithm
 * we are at and gives the appropriate counterexample
 * type based off of time constraints.
 */
counterexample *
unifying_example (state_item_number itm1, state_item_number itm2,
                  bool shift_reduce, gl_list_t reduce_path,
                  symbol_number next_sym)
{
  search_state *initial = empty_search_state ();
  state_item *conflict1 = state_items + itm1;
  state_item *conflict2 = state_items + itm2;
  ps_chunk_append (&initial->states[0]->state_items, conflict1);
  ps_chunk_append (&initial->states[1]->state_items, conflict2);
  ssb_queue = gl_list_create_empty (GL_RBTREEHASH_LIST,
                                    (gl_listelement_equals_fn) ssb_equals,
                                    (gl_listelement_hashcode_fn) ssb_hasher,
                                    (gl_listelement_dispose_fn) ssb_free, 
                                    false);
  visited =
    hash_initialize (32, NULL, (Hash_hasher) visited_hasher,
                     (Hash_comparator) visited_comparator,
                     (Hash_data_freer) search_state_free);
  ssb_append (initial);
  time_t start = time (NULL);
  bool assurance_printed = false;
  search_state *stage3result = NULL;
  counterexample *cex;
  while (gl_list_size (ssb_queue) > 0)
    {
      const search_state_bundle *ssb = gl_list_get_at (ssb_queue, 0);
      gl_list_iterator_t it = gl_list_iterator (ssb->states);
      search_state *ss;
      while (gl_list_iterator_next (&it, (const void **) &ss, NULL))
        {
          if (trace_flag & trace_cex)
            search_state_print (ss);
          // Stage 2
          parse_state *ps1 = ss->states[0];
          parse_state *ps2 = ss->states[1];
          if (ps1->depth < 0 && ps2->depth < 0)
            {
              // Stage 3: reduce and shift conflict items completed.
              const state_item *si1src = ps1->state_items.head_elt;
              const state_item *si2src = ps2->state_items.head_elt;
              if (item_rule (si1src->item)->lhs == item_rule (si2src->item)->lhs
                  && has_common_prefix (si1src->item, si2src->item))
                {
                  // Stage 4: both paths share a prefix
                  const derivation *d1 = ps1->derivs.head_elt;
                  const derivation *d2 = ps2->derivs.head_elt;
                  if (ps1->derivs.total_size == 1
                      && ps2->derivs.total_size == 1 && d1->sym == d2->sym)
                    {
                      // Once we have two derivations for the same symbol,
                      // we've found a unifying counterexample.
                      cex = new_counterexample (d1, d2, true, false);
                      // prevent d1/d2 from being freed.
                      ps1->derivs.contents = NULL;
                      ps2->derivs.contents = NULL;
                      goto cex_search_end;
                    }
                  if (!stage3result)
                    stage3result = ss;
                }
            }
          if (TIME_LIMIT_ENFORCED)
            {
              float time_passed = difftime (time (NULL), start);
              if (!assurance_printed && time_passed > ASSURANCE_LIMIT
                  && stage3result)
                {
                  puts
                    ("Productions leading up to the conflict state found.  Still finding a possible unifying counterexample...");
                  assurance_printed = true;
                }
              if (time_passed > TIME_LIMIT)
                {
                  printf ("time limit exceeded: %f\n", time_passed);
                  goto cex_search_end;
                }
            }
          generate_next_states (ss, conflict1, conflict2);
        }
      gl_sortedlist_remove (ssb_queue, (gl_listelement_compar_fn) ssb_comp,
                            ssb);
    }
cex_search_end:;
  if (!cex)
    {
      // No unifying counterexamples
      // If a search state from Stage 3 is available, use it
      // to construct a more compact nonunifying counterexample.
      if (stage3result)
        cex = complete_diverging_examples (stage3result, next_sym);
      // Otherwise, construct a nonunifying counterexample that
      // begins from the start state using the shortest
      // lookahead-sensitive path.
      else
        cex = example_from_path (shift_reduce, itm2, reduce_path, next_sym);
    }
  gl_list_free (ssb_queue);
  hash_free (visited);
  return cex;
}


static time_t cumulative_time;
static bool initialized = false;
static void
counterexample_init (void)
{
  if (!initialized)
    {
      initialized = true;
      time (&cumulative_time);
      scp_set = bitset_create (nstates, BITSET_FIXED);
      rpp_set = bitset_create (nstates, BITSET_FIXED);
    }
}


void
counter_example_free (void)
{
  bitset_free (scp_set);
  bitset_free (rpp_set);
}

/**
 * Report a counterexample for conflict on symbol next_sym
 * between the given state-items
 */
void
counterexample_report (state_item_number itm1, state_item_number itm2,
                       symbol_number next_sym, bool shift_reduce)
{
  counterexample_init ();
  if (shift_reduce)
    puts ("Shift-Reduce Conflict:");
  else
    puts ("Reduce-Reduce Conflict:");
  print_state_item (&state_items[itm1], stdout);
  print_state_item (&state_items[itm2], stdout);
  fputs ("On Symbol: ", stdout);
  symbol_print (symbols[next_sym], stdout);
  fputs ("\n", stdout);
  // Compute the shortest lookahead-sensitive path and associated sets of
  // parser states.
  gl_list_t shortest_path = shortest_path_from_start (itm1, next_sym);
  bool reduceProdReached = false;
  const rule *reduce_rule = item_rule (state_items[itm1].item);

  bitset_zero (scp_set);
  bitset_zero (rpp_set);
  gl_list_iterator_t it = gl_list_iterator (shortest_path);
  state_item *si;
  while (gl_list_iterator_next (&it, (const void **) &si, NULL))
    {
      bitset_set (scp_set, si->state->number);
      reduceProdReached = reduceProdReached
                          || item_rule (si->item) == reduce_rule;
      if (reduceProdReached)
        bitset_set (rpp_set, si->state->number);
    }
  time_t t = time (NULL);
  counterexample *cex = difftime (t, cumulative_time) < CUMULATIVE_TIME_LIMIT
    ? unifying_example (itm1, itm2, shift_reduce, shortest_path, next_sym)
    : example_from_path (shift_reduce, itm2, shortest_path, next_sym);

  gl_list_free (shortest_path);
  print_counterexample (cex);

}
