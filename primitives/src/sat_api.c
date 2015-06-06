#include "sat_api.h"

/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/


/******************************************************************************
 * Debug
 ******************************************************************************/

void sat_clause_debug(Clause* clause) {
  printf("Clause: %lu %lu\n", clause->index, clause->size);
  for (c2dSize i = 0; i < clause->size; i++) {
    printf("%ld(%lu) ", clause->literals[i]->index, clause->literals[i]->op_lit->
      decision_level);
  }
  printf("\n");
}

void sat_state_debug(SatState* sat_state) {
  printf("%lu %lu\n", sat_state->num_vars, sat_state->num_cnf_clauses);
  for (c2dSize i = 1; i <= sat_state->num_cnf_clauses; i++) {
    printf("Clause %lu: %lu\n", sat_state->cnf_clauses[i]->index, sat_state->cnf_clauses[i]->size);
    for (c2dSize j = 0; j < sat_state->cnf_clauses[i]->size; j++) {
      printf("%ld ", sat_state->cnf_clauses[i]->literals[j]->index);
    }
    printf("\n");
  }

  for (c2dSize i = 1; i <= sat_state->num_vars; i++) {
    Var* var = sat_index2var(i, sat_state);
    printf("Var %lu %lu %lu: \n", i, var->num_clauses, var->dyn_cap);
    for (c2dSize k = 0; k < var->num_clauses; k++) {
      printf("%lu ", var->clauses[k]->index);
    }
    printf("\n");
  }
  printf("\n");
  
  printf("num_decided_literals: %lu\n", sat_state->num_decided_literals);
  for (c2dSize i = 0; i < sat_state->num_decided_literals; i++) {
    printf("%ld ", sat_state->decided_literals[i]->index);
  }
  printf("\n");

  printf("num_implied_literals: %lu\n", sat_state->num_implied_literals);
  for (c2dSize i = 0; i < sat_state->num_implied_literals; i++) {
    printf("%ld ", sat_state->implied_literals[i]->index);
  }
  printf("\n");   
}

/******************************************************************************
 * Memory
 ******************************************************************************/

// double capacity
void clause_pointer_double_capacity(c2dSize* cap, Clause*** dyn_clauses) {
  *cap *= 2;
  *dyn_clauses = realloc(*dyn_clauses, *cap * sizeof(Clause*));
}

// push an element into the list
void clause_pointer_push(Clause* new_cp, Clause*** dyn_clauses, c2dSize* sz, c2dSize* cap) {
  if ((*sz) + 1 >= *cap) clause_pointer_double_capacity(cap, dyn_clauses);
  (*dyn_clauses)[*sz] = new_cp;
  *sz += 1;
}

// pop
void clause_pointer_pop(Clause** dyn_clauses, c2dSize* sz) {
  *sz -= 1;
}

// updates the list of the clause mentioning variables
void push_clause_to_vars(Clause* clause) {
  Var* var;
  Lit* lit;
  for (c2dSize i = 0; i < clause->size; i++) {
    lit = clause->literals[i];
    clause_pointer_push(clause, &(lit->clauses), &(lit->num_clauses), &(lit->dyn_cap));
    var = sat_literal_var(lit);
    clause_pointer_push(clause, &(var->clauses), &(var->num_clauses), &(var->dyn_cap));
  }
}

/******************************************************************************
 * Variables
 ******************************************************************************/

Var* new_variable(c2dSize index) {
  Var* new_v = malloc(sizeof(Var));
  new_v->index = index;
  new_v->num_clauses = 0;
  new_v->dyn_cap = 2;
  new_v->clauses = malloc(sizeof(Clause*) * new_v->dyn_cap);
  new_v->p_literal = NULL;
  new_v->n_literal = NULL;
  new_v->mark = 0;
  return new_v;
}

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
  return sat_state->variables[index];
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
  return var->index;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
  return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
  return sat_implied_literal(var->p_literal) | sat_implied_literal(var->n_literal);
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
  for (c2dSize i = 0; i < sat_var_occurences(var); i++) {
    if (!sat_subsumed_clause(var->clauses[i]))
      return 0;
  }
  return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
  return sat_state->num_vars;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
  return var->num_cnf_clauses;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
  return var->clauses[index];
}

/******************************************************************************
 * Literals 
 ******************************************************************************/

void instantiate_literal(Lit* lit, c2dLiteral decision_level, Clause* decision_clause) {
  lit->decision_level = decision_level;
  lit->decision_clause = decision_clause;

  for (c2dSize i = 0; i < lit->num_clauses; i++) {
    if (lit->clauses[i]->decision_level == 0 ||
        lit->clauses[i]->decision_level > decision_level) {
      lit->clauses[i]->decision_level = decision_level;
    }
  }
  for (c2dSize i = 0; i < lit->op_lit->num_clauses; i++) {
    ++lit->op_lit->clauses[i]->num_false;
  }
}

void undo_instantiate_literal(Lit* lit) {
  for (c2dSize i = 0; i < lit->num_clauses; i++) {
    if (lit->clauses[i]->decision_level == lit->decision_level) {
      lit->clauses[i]->decision_level = 0;
    }
  }
  for (c2dSize i = 0; i < lit->op_lit->num_clauses; i++) {
    --lit->op_lit->clauses[i]->num_false;
  }
  lit->decision_level = 0;
  lit->decision_clause = NULL;
}

Lit* new_literal(c2dLiteral index, Var* var) {
  Lit* new_lit= malloc(sizeof(Lit));
  new_lit->index = index;
  new_lit->var = var;
  new_lit->decision_level = 0;
  new_lit->decision_clause = NULL;

  new_lit->num_clauses = 0;
  new_lit->dyn_cap = 2;
  new_lit->clauses = malloc(sizeof(Clause*) * new_lit->dyn_cap);
  return new_lit;
}

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
  if (index > 0) {
    return sat_state->p_literals[index];
  } else {
    return sat_state->n_literals[-index];
  }
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
  return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
  return var->p_literal;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
  return var->n_literal;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
  return lit->decision_level > 0;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
  instantiate_literal(lit, ++sat_state->cur_level, NULL);
  sat_state->decided_literals[sat_state->num_decided_literals++] = lit;

  sat_state->unit_resolution_s = UNIT_RESOLUTION_AFTER_DECIDING_LITERAL;
  sat_unit_resolution(sat_state);

  return sat_state->asserted_clause;
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
  c2dSize sz = sat_state->num_decided_literals;
  while (sz > 0 && sat_state->decided_literals[sz - 1]->decision_level == sat_state->cur_level) {
    undo_instantiate_literal(sat_state->decided_literals[sz - 1]);
    --sz;
  }
  sat_state->num_decided_literals = sz;
  sat_undo_unit_resolution(sat_state);
  --sat_state->cur_level;
}

/******************************************************************************
 * Clauses 
 ******************************************************************************/

Clause* new_clause(c2dSize index, c2dSize clause_size, Lit **buf_lit) {
  Clause* new_c = malloc(sizeof(Clause));
  new_c->index = index;
  new_c->size = clause_size;
  new_c->literals = malloc(sizeof(Lit*) * clause_size);

  new_c->num_false = 0;
  new_c->decision_level = 0;

  for (c2dSize i = 0; i < clause_size; i++)
    new_c->literals[i] = buf_lit[i];

  new_c->assertion_level = 0;
  new_c->mark = 0;
  return new_c;
}

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
  if (index <= sat_state->num_cnf_clauses) {
    return sat_state->cnf_clauses[index];
  } else {
    return sat_state->learned_clauses[index - sat_state->num_cnf_clauses - 1];
  }
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
  return clause->index;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
  return clause->literals;
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
  return clause->size; 
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
  return clause->decision_level > 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
  return sat_state->num_cnf_clauses;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
  return sat_state->num_learned_clauses;
}

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
  // Update the num_false and decision_level
  for (c2dSize i = 0; i < clause->size; i++) {
    if (clause->literals[i]->decision_level > 0) {
      if (clause->decision_level == 0 || clause->literals[i]->decision_level < clause->decision_level)
        clause->decision_level = clause->literals[i]->decision_level;
    } else 
    if (clause->literals[i]->op_lit->decision_level > 0) {
      clause->num_false ++;
    }
  }

  // Push the clause to learned_clauses list and update the index
  clause_pointer_push(clause, &(sat_state->learned_clauses), &(sat_state->num_learned_clauses), &(sat_state->dyn_cap));
  clause->index = sat_state->num_cnf_clauses + sat_state->num_learned_clauses;

  // Update the clauses mentioning list of the variables involing.
  push_clause_to_vars(clause);

  sat_state->unit_resolution_s = UNIT_RESOLUTION_AFTER_ASSERTING_CLAUSE;
  sat_unit_resolution(sat_state);
  return sat_state->asserted_clause;
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
 ******************************************************************************/

char* skip_a_string(char *p) {
  while (*p && (*p == ' ' || *p == (char)(9))) ++p;
  while (*p && *p != ' ' && *p != (char)(9)) ++p;
  return p;
}

char* read_an_interger(char *p, c2dLiteral *num) {
  while (*p && (*p == ' ' || *p == (char)(9))) ++p;
  c2dLiteral ret = 0, sign = 1;
  if (*p == '-') sign = -1, ++p;
  while ('0' <= *p && *p <= '9') {
    ret = ret * 10 + ((*p) - '0');
    ++p;
  }
  *num = sign * ret;
  return p;
}

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
  SatState* state = malloc(sizeof(SatState));
  c2dLiteral tmp_num;

  FILE *file = fopen(file_name, "r");
  char *line = (char*)malloc(BUF_LEN * sizeof(char));
  char *line_start_p = line;

  Lit **buf_literals;
  c2dSize cur_clause_index = 0;
  while (fgets(line, BUF_LEN, file)) {
    if (strlen(line) < 2) continue;
    if (line[0] == 'c' || line[0] == '%' || line[0] == '0') continue;
    if (line[0] == 'p') {
      line = skip_a_string(skip_a_string(line));
      line = read_an_interger(line, &tmp_num);
      state->num_vars = (c2dSize)tmp_num;
      line = read_an_interger(line, &tmp_num);
      state->num_cnf_clauses = (c2dSize)tmp_num;
      state->variables = malloc(sizeof(Var*) * (state->num_vars+1));
      state->p_literals = malloc(sizeof(Lit*) * (state->num_vars+1));
      state->n_literals = malloc(sizeof(Lit*) * (state->num_vars+1));
      for (c2dSize i = 1; i <= state->num_vars; i++) {
        state->variables[i] = new_variable(i);
        state->variables[i]->p_literal = state->p_literals[i] = new_literal((c2dLiteral)i, state->variables[i]);
        state->variables[i]->n_literal = state->n_literals[i] = new_literal(-((c2dLiteral)i), state->variables[i]);
        state->p_literals[i]->op_lit = state->n_literals[i];
        state->n_literals[i]->op_lit = state->p_literals[i]; 
      }
      state->cnf_clauses = malloc(sizeof(Clause*) * (state->num_cnf_clauses + 1));
      buf_literals = malloc(sizeof(Lit*) * 2 * state->num_vars);
    } else {
      c2dSize clause_size = 0;
      while ((line = read_an_interger(line, &tmp_num))) {
        if (tmp_num == 0) break;
        if (tmp_num > 0) {
          buf_literals[clause_size++] = state->p_literals[tmp_num];
        } else {
          buf_literals[clause_size++] = state->n_literals[-tmp_num];
        }
      }
      if (clause_size > 0) {
        ++cur_clause_index;
        state->cnf_clauses[cur_clause_index] = new_clause(cur_clause_index, clause_size, buf_literals);
        push_clause_to_vars(state->cnf_clauses[cur_clause_index]);
        if (cur_clause_index == state->num_cnf_clauses) break;
      }
    }
    line = line_start_p;
  }
  fclose(file);
  free(line_start_p);
  free(buf_literals);

  for (c2dSize i = 1; i <= state->num_vars; i++) {
    state->variables[i]->num_cnf_clauses = state->variables[i]->num_clauses;
  }
  state->cur_level = 1;
  state->dyn_cap = 2;
  state->num_learned_clauses = 0;
  state->learned_clauses = malloc(sizeof(Clause*) * state->dyn_cap);
  
  state->num_decided_literals = 0;
  state->decided_literals = malloc(state->num_vars * 2 * sizeof(Lit*));
  state->num_implied_literals = 0;
  state->implied_literals = malloc(state->num_vars * 2 * sizeof(Lit*));
  
  state->unit_resolution_s = UNIT_RESOLUTION_FIRST_TIME;

  state->tmp_lit_list = malloc(sizeof(Lit*) * state->num_vars * 2);
  state->seen = malloc(sizeof(BOOLEAN) * (state->num_vars+1));
  state->lit_list = malloc(sizeof(Lit*) * state->num_vars * 2);

  return state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
  for (c2dSize i = 1; i <= sat_state->num_vars; i++) {
    free(sat_state->variables[i]->clauses);
    free(sat_state->variables[i]);
    free(sat_state->p_literals[i]->clauses);
    free(sat_state->p_literals[i]);
    free(sat_state->n_literals[i]->clauses);  
    free(sat_state->n_literals[i]);
  }
  for (c2dSize i = 1; i <= sat_state->num_cnf_clauses; i++) {
    free(sat_state->cnf_clauses[i]->literals);
  }
  for (c2dSize i = 0; i < sat_state->num_learned_clauses; i++) {
    free(sat_state->learned_clauses[i]->literals);
  }
  free(sat_state->variables);
  free(sat_state->p_literals);
  free(sat_state->n_literals);
  free(sat_state->cnf_clauses);
  free(sat_state->learned_clauses);
  free(sat_state->decided_literals);
  free(sat_state->implied_literals);
  
  free(sat_state->lit_list);
  free(sat_state->tmp_lit_list);
  free(sat_state->seen);
  free(sat_state);
}

/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function 
 * should perform unit resolution at the current decision level 
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...)) 
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases
 * It may be useful to distinguish between the above three cases
 * 
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/

// checks the clause:
// returns -1: unconsistence right now
// returns  0: unknown
// returns  1: subsumed
// returns  2: unit clause currently, return the lit
c2dLiteral check_clause(Clause* clause, Lit** ret_lit) {
  if (clause->decision_level > 0) return 1;
  if (clause->num_false == clause->size) return -1;
  if (clause->num_false + 1 == clause->size) {
    for (c2dSize i = 0; i < clause->size; i++) {
      if (clause->literals[i]->decision_level == 0 &&
          clause->literals[i]->op_lit->decision_level == 0) {
        *ret_lit = clause->literals[i];
        break;
      }
    }
    return 2;
  }
  return 0;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
  Lit* ret_lit;
  Var* var;

  c2dLiteral tmp_value;
  Clause* conflict_clause = NULL;

  c2dSize f = 0, r = 0;
  Lit** tmp_lit_list = sat_state->tmp_lit_list;

  // Push the new decided literal
  if (sat_state->unit_resolution_s == UNIT_RESOLUTION_AFTER_DECIDING_LITERAL) {
    if (sat_state->num_decided_literals > 0) {
      tmp_lit_list[++r] = sat_state->decided_literals[sat_state->num_decided_literals-1];
    }
    if (sat_state->num_implied_literals > 0) {
      c2dSize i = sat_state->num_implied_literals - 1;
      while (sat_state->implied_literals[i]->decision_level == sat_state->cur_level) {
        tmp_lit_list[++r] = sat_state->implied_literals[i];
        if (i == 0) break;
        i--;
      }
    }
  }

  // Check whether has unit clause
  c2dSize start_clauses = 1;
  if (sat_state->unit_resolution_s == UNIT_RESOLUTION_AFTER_ASSERTING_CLAUSE) 
    start_clauses = sat_state->num_cnf_clauses + sat_state->num_learned_clauses;
  if (sat_state->unit_resolution_s == UNIT_RESOLUTION_AFTER_DECIDING_LITERAL)
    start_clauses = sat_state->num_cnf_clauses + sat_state->num_learned_clauses + 1;
  for (c2dSize i = start_clauses; i <= sat_state->num_cnf_clauses + sat_state->num_learned_clauses; i++) {
    Clause* clause = sat_index2clause(i, sat_state);
    tmp_value = check_clause(clause, &ret_lit);
    if (tmp_value == -1) {
      conflict_clause = clause;
      break;
    }
    if (tmp_value == 2) {
      instantiate_literal(ret_lit, sat_state->cur_level, clause);
      sat_state->implied_literals[sat_state->num_implied_literals++] = ret_lit;
      tmp_lit_list[++r] = ret_lit;
    }
  }

  if (conflict_clause == NULL) {
    // BFS, expands the implied literals
    while (f < r) {
      var = sat_literal_var(tmp_lit_list[++f]);
      for (c2dSize i = 0; i < var->num_clauses; i++) {
        tmp_value = check_clause(var->clauses[i], &ret_lit);
        if (tmp_value == -1) {
          conflict_clause = var->clauses[i];
          break;
        }
        if (tmp_value == 2) {
          instantiate_literal(ret_lit, sat_state->cur_level, var->clauses[i]);
          sat_state->implied_literals[sat_state->num_implied_literals++] = ret_lit;
          tmp_lit_list[++r] = ret_lit;
        }
      }
    }
  }

  if (conflict_clause == NULL) {
    // No conflict
    sat_state->asserted_clause = NULL;
    return 1;
  }

  // Has conflict, derives asserted clause  
  //
  // It follows the algorithm:
  //
  //    In implication graph, if the contradition happended at node n.
  //    then 
  //           { {n}   if n is root 
  //    C(n) = {
  //           { ePa(n) \union \union_{m \in Pa(n)} C(m)
  //    where Pa(n) are the parents of node n which are set at the same level as n
  //          ePa(n) are the parents of ndoe n set at earlier levels
  // 
  BOOLEAN* seen = sat_state->seen;
  for (c2dSize i = 1; i <= sat_state->num_vars; i++) seen[i] = 0;
  Lit** lit_list = sat_state->lit_list;
  c2dSize lit_list_sz = 0;

  f = 0, r = 0;
  for (c2dSize i = 0; i < conflict_clause->size; i++) {
    if (!seen[conflict_clause->literals[i]->var->index]) {
      tmp_lit_list[++r] = conflict_clause->literals[i]->op_lit;
      seen[conflict_clause->literals[i]->var->index] = 1;
    }
  }

  c2dSize assertion_level = 1;
  c2dSize dl;
  while (f < r) {
    Lit* lit = tmp_lit_list[++f];
    if (lit->decision_level < sat_state->cur_level ||
        lit->decision_clause == NULL) {
      lit_list[lit_list_sz++] = lit->op_lit;
      dl = lit->decision_level;
      if (dl < sat_state->cur_level && dl > assertion_level) {
        assertion_level = dl;
      }
    } else {
      for (c2dSize i = 0; i < lit->decision_clause->size; i++) {
        if (!seen[lit->decision_clause->literals[i]->var->index]) {
          tmp_lit_list[++r] = lit->decision_clause->literals[i]->op_lit;
          seen[lit->decision_clause->literals[i]->var->index] = 1;
        }
      }
    }
  }
  sat_state->asserted_clause = new_clause(0, lit_list_sz, lit_list);
  sat_state->asserted_clause->assertion_level = assertion_level;

  return 0;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
  c2dSize sz = sat_state->num_implied_literals;
  while (sz > 0 && sat_state->implied_literals[sz - 1]->decision_level >= sat_state->cur_level) {
    undo_instantiate_literal(sat_state->implied_literals[sz - 1]);
    --sz;
  }
  sat_state->num_implied_literals = sz;
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
  return clause->assertion_level == sat_state->cur_level;
}

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
  return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
  return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
  var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
  var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
  return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
  clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
  clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/
