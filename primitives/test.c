#include "sat_api.h"

void TEST_READ_FILE() {
  SatState* st = sat_state_new("cnf.in");
  sat_state_debug(st);
}

int main() {
  TEST_READ_FILE();
  return 0;
}
