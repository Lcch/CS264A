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
 * Variables
 ******************************************************************************/

Var* new_variable(c2dSize index) {
  Var* new_v = malloc(sizeof(Var));
  new_v->index = index;
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
  for (c2dSize i = 0; i < var->num_clauses; i++) {
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
  return var->num_clauses;
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

Lit* new_literal(c2dLiteral index, Var* var) {
  Lit* new_lit= malloc(sizeof(Lit));
  new_lit->index = index;
  new_lit->var = var;
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

  // ... TO DO ...
  
  return 0; //dummy valued
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {

  // ... TO DO ...
  
  return NULL; //dummy valued
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {

  // ... TO DO ...
  
  return; //dummy valued
}

/******************************************************************************
 * Clauses 
 ******************************************************************************/


Clause* new_clause(c2dSize index, c2dSize clause_size, Lit **buf_lit) {
  Clause* new_c = malloc(sizeof(Clause));
  new_c->index = index;
  new_c->size = clause_size;
  new_c->literals = malloc(sizeof(Lit*) * clause_size);
  for (c2dSize i = 0; i < clause_size; i++) {
    new_c->literals[i] = buf_lit[i];
  }
  return new_c;
}

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
  if (index <= sat_state->num_cnf_clauses) {
    return sat_state->cnf_clauses[index];
  } else {
    return sat_state->learned_clauses[index - sat_state->num_cnf_clauses];
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

  // ... TO DO ...
  
  return 0; //dummy valued
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

  // ... TO DO ...
  
  return NULL; //dummy valued
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
  while (*p && *p == ' ') ++p;
  while (*p && *p != ' ') ++p;
  return p;
}

char* read_a_interger(char *p, c2dLiteral *num) {
  while (*p && *p == ' ') ++p;

  c2dLiteral ret = 0, sign = 1;
  if (*p == '-') sign = -1, ++p;
  while ('0' <= *p && *p <= '9') {
    ret = ret * 10 + ((*p) - '0');
    ++p;
  }
  *num = sign * ret;
  return p;
}


void sat_state_debug(SatState* sat_state) {
  printf("%lu %lu\n", sat_state->num_vars, sat_state->num_cnf_clauses);
  for (c2dSize i = 1; i <= sat_state->num_cnf_clauses; i++) {
    printf("Clause %lu: \n", sat_state->cnf_clauses[i]->index);
    for (c2dSize j = 0; j < sat_state->cnf_clauses[i]->size; j++) {
      printf("%ld ", sat_state->cnf_clauses[i]->literals[j]->index);
    }
    printf("\n");
  }
}

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
  SatState* state = malloc(sizeof(SatState));
  c2dLiteral tmp_num;

  FILE *file = fopen(file_name, "r");
  char *line = (char*)malloc(BUF_LEN * sizeof(char));

  Lit **buf_literals;
  c2dSize cur_clause_index = 0;
  while (fgets(line, BUF_LEN, file)) {
    if (line[0] == 'c' || line[0] == '%' || line[0] == '0') continue;
    if (line[0] == 'p') {
      line = skip_a_string(skip_a_string(line));
      line = read_a_interger(line, &tmp_num);
      state->num_vars = (c2dSize)tmp_num;
      line = read_a_interger(line, &tmp_num);
      state->num_cnf_clauses = (c2dSize)tmp_num;
      state->variables = malloc(sizeof(Var*) * (state->num_vars+1));
      state->p_literals = malloc(sizeof(Lit*) * (state->num_vars+1));
      state->n_literals = malloc(sizeof(Lit*) * (state->num_vars+1));
      for (c2dSize i = 1; i <= state->num_vars; i++) {
        state->variables[i] = new_variable(i);
        state->variables[i]->p_literal = state->p_literals[i] = new_literal((c2dLiteral)i, state->variables[i]);
        state->variables[i]->n_literal = state->n_literals[i] = new_literal(-((c2dLiteral)i), state->variables[i]);
      }
      state->cnf_clauses = malloc(sizeof(Clause*) * state->num_cnf_clauses);
      buf_literals = malloc(2 * state->num_vars * sizeof(Lit*));
    } else {
      c2dSize clause_size = 0;
      while ((line = read_a_interger(line, &tmp_num))) {
        if (tmp_num == 0) break;
        if (tmp_num > 0) {
          buf_literals[clause_size++] = state->p_literals[tmp_num];
        } else {
          buf_literals[clause_size++] = state->n_literals[-tmp_num];
        }
      }
      ++cur_clause_index;
      state->cnf_clauses[cur_clause_index] = new_clause(cur_clause_index, clause_size, buf_literals);
    }
  }
  fclose(file);

  state->cur_level = 0;

  return state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
  
  return; //dummy valued
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

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {

  // ... TO DO ...
  
  return; //dummy valued
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
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
