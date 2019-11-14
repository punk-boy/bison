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
#include "counterexample.h"
#include "derivation.h"
#include "gram.h"
#include "complain.h"
#include "closure.h"
#include "nullable.h"
#include "getargs.h"
#include "lalr.h"


/** True if the time limit is enforced; otherwise, search could run
 *  indefinitely. */
#define TIME_LIMIT_ENFORCED true
/** If set to true, when computing the shortest lookahead-sensitive path,
 *  only consider states that can reach the conflict state. */
#define OPTIMIZE_SHORTEST_PATH true
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
/** The time limit before giving up looking for unifying counterexample. */
#define TIME_LIMIT 5.0f

/** The set of parser states on the shortest lookahead-sensitive path. */
static bitset scpSet;
/** The set of parser states used for the conflict reduction rule. */
static bitset rppSet;

struct search_node;
typedef struct search_node
{
  state_item_number si;
  struct search_node *parent;
  bitset lookahead;
} search_node;

search_node *
new_search_node (state_item_number si, search_node *p, bitset l)
{
  search_node *ret = xmalloc (sizeof (search_node));
  ret->si = si;
  ret->parent = p;
  ret->lookahead = l;
  return ret;
}

static size_t
search_node_hasher (const void *sv, size_t max)
{
  search_node *sn = (search_node *) sv;
  size_t hash = sn->si;
  bitset_iterator biter;
  symbol_number syn;
  BITSET_FOR_EACH (biter, sn->lookahead, syn, 0)
    hash += syn;
  return hash % max;
}

static bool
search_node_comparator (const void *s1, const void *s2)
{
  search_node *n1 = (search_node *) s1;
  search_node *n2 = (search_node *) s2;
  if (n1->si == n2->si)
    return bitset_equal_p (n1->lookahead, n2->lookahead);
  return false;
}

typedef struct si_list_node
{
  struct si_list_node *prev;
  struct si_list_node *next;
  state_item *si;
} si_list_node;

typedef struct
{
  si_list_node *head;
  si_list_node *tail;
} si_list;

void
si_list_prepend (si_list *l, state_item *si)
{
  si_list_node *n = xmalloc (sizeof (si_list_node));
  n->si = si;
  n->prev = NULL;
  n->next = l->head;
  if (l->head)
    l->head->prev = n;
  else
    l->tail = n;
  l->head = n;
}

void
si_list_append (si_list *l, state_item *si)
{
  si_list_node *n = xmalloc (sizeof (si_list_node));
  n->si = si;
  n->next = NULL;
  n->prev = l->tail;
  if (l->tail)
    l->tail->next = n;
  else
    l->head = n;
  l->tail = n;
}

bool
si_list_contains (si_list *l, state_item *si)
{
  for (si_list_node *n = l->head; n != NULL; n = n->next)
    if (n->si == si)
      return true;
  return false;
}

void
si_list_free (si_list *l)
{
  for (si_list_node *n = l->head; n != NULL; n = n->next)
    free (l);
}

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
  printf ("First example ");
  derivation_print_leaves (cex->d1, stdout);
  printf ("\nFirst derivation ");
  derivation_print (cex->d1, stdout);
  printf ("\nSecond example ");
  derivation_print_leaves (cex->d2, stdout);
  printf ("\nSecond derivation ");
  derivation_print (cex->d2, stdout);
  fputc ('\n', stdout);
}

/**
 * Compute the set of StateItems that can reach the given conflict item via
 * a combination of transitions or production steps.
 */
bitset
eligible_state_items (state_item *target)
{
  bitset result = bitset_create (nstate_items, BITSET_FIXED);
  gl_list_t queue = gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, true, 1,
                                    (const void **) &target);
  while (gl_list_size (queue) > 0)
    {
      state_item *si = (state_item *) gl_list_get_at (queue, 0);
      gl_list_remove_at (queue, 0);
      if (bitset_test (result, si->num))
        continue;
      bitset_set (result, si->num);
      // Consider reverse transitions and reverse productions.
      bitset rsi = rev_trans[si->num];
      bitset_iterator biter;
      state_item_number sin;
      BITSET_FOR_EACH (biter, rsi, sin, 0)
        gl_list_add_last (queue, &state_items[sin]);
      if (si->item == ritem || *(si->item - 1) < 0)
        {
          bitset rp = rev_prods_lookup (si->num);
          bitset_iterator biter;
          state_item_number sin;
          if (rp)
            BITSET_FOR_EACH (biter, rp, sin, 0)
              gl_list_add_last (queue, &state_items[sin]);
        }
    }
  return result;
}

/**
 * Compute the shortest lookahead-sensitive path from the start state to
 * this conflict. If OPTIMIZE_SHORTEST_PATH is true,
 * only consider parser states that can reach the conflict state.
 */
si_list *
shortest_path_from_start (state_item_number target, symbol_number next_sym)
{
  state_items_init (stdout);
  time_t start = time (NULL);
  bitset eligible = OPTIMIZE_SHORTEST_PATH
    ? eligible_state_items (&state_items[target]) : NULL;
  Hash_table *visited = hash_initialize (32,
                                         NULL,
                                         search_node_hasher,
                                         search_node_comparator,
                                         NULL);
  bitset il = bitset_create (nsyms, BITSET_FIXED);
  bitset_set (il, 0);
  search_node *init = new_search_node (0, NULL, il);
  gl_list_t queue = gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, 1, 1,
                                    (const void **) &init);
  // breadth-first search
  while (gl_list_size (queue) > 0)
    {
      search_node *n = (search_node *) gl_list_get_at (queue, 0);
      gl_list_remove_at (queue, 0);
      if (hash_lookup (visited, n))
        continue;
      state_item_number last = n->si;
      hash_insert (visited, n);
      if (target == last && bitset_test (n->lookahead, next_sym))
        {
          si_list *ret = xcalloc (1, sizeof (si_list));
          for (search_node *sn = n; sn != NULL; sn = sn->parent)
            {
              si_list_prepend (ret, &state_items[sn->si]);
            }
          if (trace_flag & trace_cex)
            {
              puts ("REDUCE ITEM PATH:");
              for (si_list_node *sn = ret->head; sn != NULL; sn = sn->next)
                print_state_item (sn->si, stdout);
            }
          return ret;
        }
      // Transition
      if (trans[last] != -1)
        {
          state_item_number nextSI = trans[last];
          if (!OPTIMIZE_SHORTEST_PATH || bitset_test (eligible, nextSI))
            {
              search_node *next = new_search_node (nextSI, n, n->lookahead);
              gl_list_add_last (queue, next);
            }
        }
      // Production step
      bitset p = prods_lookup (last);
      if (p)
        {
          state_item si = state_items[last];
          // Compute possible terminals that can follow this production.
          // (This is first_L in the CupEx paper.)
          bitset lookahead = bitset_create (nsyms, BITSET_FIXED);
          item_number *pos = si.item + 1;
          for (; !item_number_is_rule_number (*pos); ++pos)
            {
              item_number it = *pos;
              if (ISTOKEN (it))
                {
                  bitset_set (lookahead, it);
                  break;
                }
              else
                {
                  bitset_union (lookahead, lookahead, tfirsts[it - ntokens]);
                  if (!nullable[it - ntokens])
                    break;
                }
            }
          if (item_number_is_rule_number (*pos))
            bitset_union (lookahead, n->lookahead, lookahead);
          // Try all possible production steps within this parser state.
          bitset_iterator biter;
          state_item_number nextSI;
          BITSET_FOR_EACH (biter, p, nextSI, 0)
            {
              if (OPTIMIZE_SHORTEST_PATH && !bitset_test (eligible, nextSI))
                continue;
              search_node *next = new_search_node (nextSI, n, lookahead);
              gl_list_add_last (queue, next);
            }
        }
    }
  fputs ("Cannot find shortest path to conflict state.", stderr);
  return NULL;
}

/**
 * Repeatedly take production steps on the given StateItem so that the
 * first symbol of the derivation matches the conflict symbol.
 */
gl_list_t
expand_first (state_item *start, symbol_number next_sym)
{
  si_list *init = xcalloc (1, sizeof (si_list));
  si_list_append (init, start);
  gl_list_t queue = gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, 1, 1,
                                    (const void **) &init);
  si_list *ret = NULL;
  // breadth-first search
  while (gl_list_size (queue) > 0)
    {
      si_list *states = (si_list *) gl_list_get_at (queue, 0);
      gl_list_remove_at (queue, 0);
      state_item *silast = states->head->si;
      symbol_number sym = item_number_as_symbol_number (*(silast->item));
      if (sym == next_sym)
        {
          ret = states;
          break;
        }
      if (ISVAR (sym))
        {
          bitset_iterator biter;
          state_item_number sin;
          bitset sib = prods_lookup (silast->num);
          BITSET_FOR_EACH (biter, sib, sin, 0)
            {
              state_item nextsi = state_items[sin];
              if (si_list_contains (states, &nextsi))
                continue;
              si_list *next = xmalloc (sizeof (si_list));
              next->head = states->head;
              next->tail = states->tail;
              si_list_prepend (next, &nextsi);
              gl_list_add_last (queue, next);
            }
          if (nullable[sym - ntokens])
            {
              // If the nonterminal after dot is nullable,
              // we need to look further.
              si_list *next = xmalloc (sizeof (si_list));
              next->head = states->head;
              next->tail = states->tail;
              si_list_prepend (next, &state_items[trans[silast->num]]);
              gl_list_add_last (queue, next);
            }
        }
    }
  if (!ret)
    {
      puts ("Should not happen");
      return NULL;
    }
  // done; construct derivation
  derivation *dinit = derivation_new (next_sym, NULL);
  gl_list_t result = gl_list_create (GL_LINKED_LIST, NULL, NULL, free, 1, 1,
                                     (const void **) &dinit);
  for (si_list_node *n = ret->head; n != NULL; n = n->next)
    {
      state_item *si = n->si;
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
            gl_list_create (GL_LINKED_LIST, NULL, NULL, free, 1, 1,
                            (const void **) &deriv);
        }
      else
        {
          derivation *deriv =
            derivation_new (item_number_as_symbol_number (*(pos - 1)), NULL);
          gl_list_add_first (result, deriv);
        }
    }
  gl_list_remove_at (result, 0);
  return result;
}

/**
 * Auxiliary method to complete any pending productions in the given
 * sequence of parser states.
 */
derivation *
complete_diverging_example (symbol_number next_sym,
                            si_list *states, gl_list_t derivs)
{
  // The idea is to transfer each pending symbol on the productions
  // associated with the given StateItems to the resulting derivation.
  gl_list_t result =
    gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, true);
  if (!derivs)
    derivs = gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, true);
  bool lookahead_required = false;
  gl_list_node_t tmp = gl_list_add_last (derivs, NULL);
  gl_list_node_t deriv = gl_list_previous_node (derivs, tmp);
  gl_list_remove_node (derivs, tmp);
  for (si_list_node *n = states->tail; n != NULL; n = n->prev)
    {
      state_item *si = n->si;
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
                      state_item *trans_si = &state_items[trans[si->num]];
                      gl_list_t next_derivs =
                        expand_first (trans_si, next_sym);
                      gl_list_iterator_t it = gl_list_iterator (next_derivs);
                      derivation *tmp;
                      while (gl_list_iterator_next
                             (&it, (const void **) &tmp, NULL))
                        gl_list_add_last (result, tmp);
                      //TODO: Might be dangerous to do this
                      i += gl_list_size (next_derivs) - 1;
                      lookahead_required = false;

                    }
                  else
                    {
                      // This nonterminal is nullable and cannot derive nextSym.
                      // So, this nonterminal must derive the empty string,
                      // and nextSym must be derived by a later nonterminal.

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
          if (n->prev)
            n = n->prev;
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
  return (derivation *) gl_list_get_at (result, 0);
}


//iterates backwards through the shifts of the path in the
//reduce conflict, and finds a path of shifts in the shift
//conflict that goes through the same states.
si_list *
nonunifying_shift_path (si_list *reduce_path, state_item *shift_conflict)
{
  state_item *si = shift_conflict;
  si_list *result = xcalloc (1, sizeof (si_list));
  si_list_append (result, si);
  bool paths_merged;
  for (si_list_node *node = reduce_path->tail->prev;
       node != NULL; node = node->prev)
    {
      state_item *refsi = node->si;
      state_item *nextrefsi = node->next->si;
      if (nextrefsi == si)
        {
          si_list_prepend (result, refsi);
          continue;
        }
      //skip reduction items
      if (nextrefsi->item != refsi->item + 1 && refsi->item != ritem)
        continue;

      //bfs to find a shift to the right state
      si_list *init = xcalloc (1, sizeof (si_list));
      gl_list_t queue =
        gl_list_create (GL_LINKED_LIST, NULL, NULL, NULL, 1, 1,
                        (const void **) &init);
      while (gl_list_size (queue) > 0)
        {
          si_list *sis = (si_list *) gl_list_get_at (queue, 0);
          gl_list_remove_at (queue, 0);
          state_item *sisrc;
          sisrc = sis->head ? sis->head->si : si;
          item_number *srcpos = sisrc->item;
          // Reverse Transition
          symbol_number sym = *(srcpos - 1);
          // Only look for state compatible with the shortest path.
          bitset rsi = rev_trans[sisrc->num];
          bitset_iterator biter;
          state_item_number sin;
          state_item *prevsi = NULL;
          BITSET_FOR_EACH (biter, rsi, sin, 0)
            {
              state_item *psi = &state_items[sin];
              if (psi->state == refsi->state)
                {
                  prevsi = psi;
                  //BITSET_FOR_EACH is a nested for loop
                  goto biter_exit;
                }
            }

        biter_exit:
          if (prevsi || sisrc == state_items)
            {
              if (sis->head)
                {
                  sis->tail->next = result->head;
                  result->head->prev = sis->tail;
                  sis->tail = result->tail;
                  free (result);
                  result = sis;
                }
              si = prevsi;
              if (prevsi)
                si_list_prepend (result, si);
              break;
            }
          // Reverse Production
          bitset rps = rev_prods_lookup (sisrc->num);
          if (rps)
            {
              bitset_iterator biter2;
              BITSET_FOR_EACH (biter2, rps, sin, 0)
                {
                  state_item *prevsi = state_items + sin;
                  if (!si_list_contains (sis, prevsi))
                    {
                      //since we only ever prepend, lists can be
                      //shallow copied as the head will always have
                      //the right path
                      si_list *prevsis = xmalloc (sizeof (si_list));
                      prevsis->tail = sis->tail;
                      prevsis->head = sis->head;
                      si_list_prepend (prevsis, prevsi);
                      gl_list_add_last (queue, prevsis);
                    }
                }
              free (sis);
            }
        }
      gl_list_free (queue);
    }
  //Fix inconsistencies due to shallow copying
  for (si_list_node *node = result->head; node->next != NULL;
       node = node->next)
    node->next->prev = node;
  if (trace_flag & trace_cex)
    {
      puts ("SHIFT ITEM PATH:");
      for (si_list_node *node = result->head; node != NULL;
           node = node->next)
        print_state_item (node->si, stdout);
    }
  return result;
}


/**
 * Construct a nonunifying counterexample from the shortest
 * lookahead-sensitive path.
 */
counterexample *
example_from_path (bool timeout, bool shift_reduce, state_item_number itm2,
                   si_list *shortest_path, symbol_number next_sym)
{
  derivation *deriv1 =
    complete_diverging_example (next_sym, shortest_path, NULL);
  si_list *path_2 = shift_reduce ? nonunifying_shift_path (shortest_path,
                                                           &state_items[itm2])
    : shortest_path_from_start (itm2, next_sym);
  derivation *deriv2 = complete_diverging_example (next_sym, path_2, NULL);
  return new_counterexample (deriv1, deriv2, false, timeout);
}

/**
 * Construct a search instance from a given conflict state, pair of items,
 * and next input symbol.
 */
void
report_counterexample (state_item_number itm1, state_item_number itm2,
                       symbol_number next_sym, bool shift_reduce)
{
  if (shift_reduce)
    puts ("Shift-Reduce Conflict:");
  else
    puts ("Reduce-Reduce Conflict:");
  print_state_item (&state_items[itm1], stdout);
  print_state_item (&state_items[itm2], stdout);
  fputs ("On Symbol: ", stdout);
  symbol_print (symbols[next_sym], stdout);
  puts ("");
  // Compute the shortest lookahead-sensitive path and associated sets of
  // parser states.
  si_list *shortest_path = shortest_path_from_start (itm1, next_sym);
  scpSet = bitset_create (nstates, BITSET_FIXED);
  rppSet = bitset_create (nstates, BITSET_FIXED);
  bool reduceProdReached = false;
  const rule *reduce_rule = item_rule (state_items[itm1].item);
  state_item *si;
  for (si_list_node *n = shortest_path->head; n != NULL; n = n->next)
    {
      state_item *si = n->si;
      bitset_set (scpSet, si->state->number);
      reduceProdReached =
        reduceProdReached || item_rule (si->item) == reduce_rule;
      if (reduceProdReached)
        bitset_set (rppSet, si->state->number);
    }
  counterexample *cex =
    example_from_path (true, shift_reduce, itm2, shortest_path, next_sym);
  print_counterexample (cex);

}

/**
 * Compute the number of production steps made in the given sequence of
 * StateItems until reaching the given StateItem
 */
static int
production_steps (si_list *sis, state_item *last)
{
  int count = 0;
  state *last_state = last->state;
  for (si_list_node *n = sis->tail->prev; n != NULL; n = n->prev)
    {
      state *s = n->si->state;
      if (s == last_state)
        ++count;
      last_state = s;
    }
  return count;
}

/**
 * Determine if the given symbols are compatible with each other.
 * That is, if both are terminals, they must be the same; otherwise, if
 * one is a terminal and the other a nonterminal, the terminal must be a
 * possible beginning of the nonterminal; finally, if both are nonterminals,
 * their first sets must intersect.
 */
static bool
compatible (symbol_number sym1, symbol_number sym2)
{
  if (sym1 == sym2)
    return true;
  if (ISTOKEN (sym1) && ISVAR (sym2))
    return bitset_test (FIRSTS (sym2), sym1);
  else if (ISVAR (sym1) && ISTOKEN (sym2))
    return bitset_test (FIRSTS (sym1), sym2);
  else if (ISVAR (sym1) && ISVAR (sym2))
    return !bitset_disjoint_p (FIRSTS (sym1), FIRSTS (sym2));
  else
    return false;
}

/**
 * Compute the number of consecutive production steps made before reaching
 * the last StateItem in the given sequence.
 */
static int
reduction_streak (si_list *sis)
{
  int count = 0;
  state_item *last = sis->tail->si;
  for (si_list_node *n = sis->tail->prev; n != NULL; n = n->prev)
    {
      if (n->si->state != last->state)
        break;
      ++count;
    }
  return count;
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
