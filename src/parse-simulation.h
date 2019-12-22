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

typedef struct
{
  gl_list_t contents;
  const void *head_elt;
  const void *tail_elt;
  size_t total_size;
} ps_chunk;

struct parse_state;
typedef struct parse_state
{
  ps_chunk state_items;
  ps_chunk derivs;
  struct parse_state *parent;
  int reference_count;
  int depth;
  bool prepend;
  bool visited;
} parse_state;

void ps_chunk_prepend (ps_chunk *chunk, void *element);
void ps_chunk_append (ps_chunk *chunk, void *element);

parse_state *empty_parse_state (void);
// generates an empty child parse state for parent
parse_state *copy_parse_state (bool prepend, parse_state *parent);
// generates an child parse state for parent
parse_state *new_parse_state (gl_list_t sis, gl_list_t derivs, bool prepend,
                              parse_state *parent);

void free_parse_state (parse_state *ps);

// Emulates a reduction on a parse state by popping some amount of
// derivations and state_items off of the parse_state and returning
// the result in ret. Returns the derivation of what's popped.
gl_list_t parser_pop (parse_state *ps, int deriv_index,
                      int si_index, parse_state *ret);

// various functions that return a list of states based off of
// whatever operation is simulated.
gl_list_t simulate_transition (parse_state *ps);
gl_list_t simulate_production (parse_state *ps, symbol_number compat_sym);
gl_list_t simulate_reduction (parse_state *ps, item_number *conflict_item,
                              int rule_len, bitset symbol_set);

void print_parse_state (parse_state *ps);
#endif /* PARSE_SIMULATION_H */
