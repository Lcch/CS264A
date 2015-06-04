#include "sat_api.h"

void TEST_READ_FILE() {
  printf("CAO\n");
  sat_state_new("cnf.in");
}

int main() {
  TEST_READ_FILE();
  return 0;
}
