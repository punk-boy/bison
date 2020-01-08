/* Lookahead sensative state item searches for counterexample generation
 
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

#ifndef LSSI_H
#define LSSI_H

#include "state-item.h"
/*
 * find shortest lookahead-sensitive path of state-items to target such that
 * next_sym is in the follow_L set of target in that position.
*/
gl_list_t shortest_path_from_start (state_item_number target,
                                    symbol_number next_sym);

/**
 * Determine if the given terminal is in the given symbol set or can begin
 * a nonterminal in the given symbol set.
 */
bool intersect_symbol (symbol_number sym, bitset syms);

/**
 * Determine if any symbol in ts is in syms
 * or can begin a nonterminal syms.
 */
bool intersect (bitset ts, bitset syms);

/**
 * Compute a set of sequences of StateItems that can make production steps
 * to this StateItem such that the resulting possible lookahead symbols are
 * as given.
 */
gl_list_t lssi_reverse_production (state_item *si, bitset lookahead);

#endif /* LSSI_H */
