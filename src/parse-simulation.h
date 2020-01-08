/* Parser simulator for unifying counterexample search
 
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

#ifndef PARSE_SIMULATION_H
#define PARSE_SIMULATION_H

#include <stdio.h>
#include <gl_xlist.h>
#include "state-item.h"

/*
  Simulating states of the parser:

  Each state is an array of state-items and an array of derivations.
  Each consecutive state-item represents a transition/goto or production,
  and the derivations are the dereivation trees associated with the symbols
  transitioned on each step. In more detail:
 
  Parse states are stored as a tree. Each new parse state contains two "chunks,"
  one corresponding to its state-items and the other corresponding to its derivations.
  Chunks only have new elements which weren't present in its parent. Each chunk also stores
  the head, tail, and total_size of the list it represents. So if a parse state was to be
  copied and have
 
  A production
  A transition gets the state-item which the last state-item of the parse state
  transitions to. This is appended to the state-item list, and a derivation with
  just the symbol being transitioned on is appended to the derivation list.

 */
typedef struct
{
  // elements newly added in this chunk
  gl_list_t contents;
  // properties of the linked list this chunk represents
  const void *head_elt;
  const void *tail_elt;
  size_t total_size;
} ps_chunk;

struct parse_state;
typedef struct parse_state
{
  // path of state-items the parser has traversed
  ps_chunk state_items;
  // list of derivations of the symbols
  ps_chunk derivs;
  struct parse_state *parent;
  int reference_count;
  // incremented during productions,
  // decremented during reductions
  int depth;
  // whether the contents of the chunks should be
  // prepended or appended to the list the chunks
  // represent
  bool prepend;
  // causes chunk contents to be freed when the
  // reference count is one. Used when only the chunk metadata
  // will be needed.
  bool free_contents_early;
} parse_state;

parse_state *new_parse_state (state_item *conflict);

size_t parse_state_hasher (parse_state *ps, size_t max);

bool parse_state_comparator (parse_state *ps1, parse_state *ps2);

void free_parse_state (parse_state *ps);

void parse_state_lists (parse_state *ps, gl_list_t *state_items,
                        gl_list_t *derivs);

// various functions that return a list of states based off of
// whatever operation is simulated. After whatever operation, every possible
// transition on nullable nonterminals will be added to the returned list.

// Look at the tail state-item of the parse_state and transition on the symbol
// after its dot. The symbol gets added to derivs, and the resulting state-item
// is appended to state-items.
gl_list_t simulate_transition (parse_state *ps);

// Look at all of the productions for the non-terminal following the dot in the tail
// state-item. Appends to state-items each production state-item which may start with
// compat_sym.
gl_list_t simulate_production (parse_state *ps, symbol_number compat_sym);

// Removes the last rule_len state-items along with their derivations. A new state-item is
// appended representing the goto after the reduction. A derivation for the non-terminal that
// was just reduced is appended which consists of the list of derivations that were just removed.
gl_list_t simulate_reduction (parse_state *ps, int rule_len,
                              bitset symbol_set);

// Generate states with a state-item prepended for each state-item that has a
// transition or production step to ps's head.
gl_list_t parser_prepend (parse_state *ps);

void print_parse_state (parse_state *ps);
#endif /* PARSE_SIMULATION_H */
