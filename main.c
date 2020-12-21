#include "src/sparch.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define ZERO_FILL 0.8f

Matrix *randMat(size_t height, size_t width) {
  Matrix *mat = Matrix_malloc(height, width);
  
  for (size_t i = 0; i < height*width; i++) {
    if (rand() / (float)RAND_MAX < ZERO_FILL) {
      mat->values[i] = 0.0f;
    } else {
      mat->values[i] = rand() / (float)RAND_MAX * 2.0f; 
    }
  }

  return mat;
}

void Matrix_print(Matrix *mat) {
  size_t idx = 0; 
  for (size_t i = 0; i < mat->height; i++) {
    for (size_t j = 0; j < mat->width; j++) {
      printf("%6.2f ", mat->values[idx]);
      idx++;
    }
    printf("\n");
  }
}

int main(int argc, char *argv[]) {
  int genRand = 0;
  int print = 0;
  size_t randH, randI, randW;
  Matrix *a, *b;
  
  printf("usage: ./sparch [--print] [--rand] [HEIGHT_A WIDTH_A WIDTH_B]\n\n");
    
  if (argc >= 2) {
    for (int i = 0; i < argc; i++) {
      char *arg = argv[i];
      if (strcmp("--print", arg) == 0) {
        print = 1;
      } else if (strcmp("--rand", arg) == 0) {
        srand((unsigned int)time(NULL));
        genRand = 1;
        randH = atoi(argv[argc-3]);
        randI = atoi(argv[argc-2]);
        randW = atoi(argv[argc-1]);
      }
    }
  }
  
  if (genRand) {
    a = randMat(randH, randI);
    b = randMat(randI, randW);
  } else {
    FILE *fp = fopen("test.mat", "r");
    size_t h, w, idx;
    fscanf(fp, "%zu %zu", &h, &w);
    a = Matrix_malloc(h, w);
    idx = 0;
    for (size_t i = 0; i < h; i++) {
      for (size_t j = 0; j < w; j++) {
        fscanf(fp, "%f", &a->values[idx]);
        idx++;
      }
    }
  
    fscanf(fp, "%zu %zu", &h, &w);
    b = Matrix_malloc(h, w);
    idx = 0;
    for (size_t i = 0; i < h; i++) {
      for (size_t j = 0; j < w; j++) {
        fscanf(fp, "%f", &b->values[idx]);
        idx++;
      }
    }
  
    fclose(fp);
  }
  
  Matrix *gem = gemm_sparch(a, b);
  Matrix *mm = matmul(a, b);

  if (print) {
    printf("==== result of sparch ====\n");
    Matrix_print(gem);
  
    printf("==== result of matmul ====\n");
    Matrix_print(mm);
  }

  float diff = 0;
  for (size_t i = 0; i < gem->height * gem->width; i++) {
    float d = gem->values[i] - mm->values[i];
    diff += d >= 0 ? d : -d;
  }
  printf("==== absolute difference: (%f) ====\n", diff);
  
  
  Matrix_free(gem);
  Matrix_free(b);
  Matrix_free(a);
  
  
  return 0;
}
