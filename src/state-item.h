/* Counterexample Generation Search Nodes
 
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

#ifndef STATE_ITEM_H
#define STATE_ITEM_H

#include <hash.h>
#include <gl_list.h>
#include <bitsetv.h>
#include "gram.h"
#include "state.h"

/*
 Initializes a graph connecting (state, production item) pairs to
 pairs they can make a transition or production step to. This graph
 is used to search for paths that represent counterexamples of some
 conflict.
 
 state_items is an array of state state-item pairs ordered by state.
 state_item_map maps state numbers to the first item which corresponds
 to it in the array. A state's portion in state_items begins with its
 items in the same order as it was in the state. This is then followed by
 productions from the closure of the state in order by rule.
 
 There are two type of edges in this graph transitions and productions.
 Transitions are the same as transitions from the parser except edges
 are only between items from the same rule. These are stored as two
 arrays (as most items will have transitions) which are indexed the same
 way as state_items.
 
 trans maps a state-item to another state-item
 rev_trans maps a state-item to a bitset of the state-items
 it has transitions from.
 
 Productions are edges from items with a nonterminal after the dot to
 the production of that nonterminal in the same state. These edges are
 stored as hash maps from a state_item to a set of what productions
 it goes from/to
 
 */

#define SI_DISABLED(sin) (sin == -2)

typedef int state_item_number;

typedef struct
{
  state *state;
  item_number *item;
  bitset lookahead;
} state_item;

extern bitsetv tfirsts;

extern size_t nstate_items;
extern state_item_number *state_item_map;

/** Array mapping state_item_numbers to state_items */
extern state_item *state_items;

/** Transition map: StateItem -> StateItem */
extern state_item_number *trans;

/** Reverse transition map: StateItem -> Set of state_item_numbers */
extern bitsetv rev_trans;

/** Production map within the same state: StateItem -> Set of state_item offsets */
extern Hash_table *prods;

/** Reverse production map: state -> nonterminal -> Set of state_item offsets */
extern Hash_table *rev_prods;

state_item *state_item_lookup (state_number s, state_item_number off);

static inline state_item_number
state_item_index_lookup (state_number s, state_item_number off)
{
  return state_item_map[s] + off;
}

static inline state_item_number
state_item_pointer_lookup (state_item *s)
{
  return s - state_items;
}

bitset prods_lookup (state_item_number si);
bitset rev_prods_lookup (state_item_number si);

void state_items_init (FILE *report);
void print_state_item (state_item *si, FILE *out);
void state_items_free (void);

#endif /* STATE_ITEM_H */
