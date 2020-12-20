#include "src/sparch.h"

int main() {
  Matrix *a = Matrix_malloc(4, 4);
  Matrix *b = Matrix_malloc(4, 4);

  Matrix *gem = gemm_sparch(a, b);

  Matrix_free(gem);
  Matrix_free(b);
  Matrix_free(a);
  
  return 0;
}
