#include "src/sparch.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define ZERO_FILL 0.2f

Matrix *randMat(size_t height, size_t width) {
  Matrix *mat = Matrix_malloc(height, width);
  
  for (size_t i = 0; i < height*width; i++) {
    if (rand() / (float)RAND_MAX < ZERO_FILL) {
      mat->values[i] = 0.0f;
    } else {
      mat->values[i] = rand() / (float)RAND_MAX * 2.0f - 1; 
    }
  }

  return mat;
}

CSRMatrix *randCSR(size_t height, size_t width) {
  size_t expectLen = height * width * (1 - ZERO_FILL + 0.05); 
  CSRMatrix *mat = CSR_malloc(height, width, 1);
  // remove temp float
  free(mat->values);
  free(mat->cols);
  float *values = (float *)malloc(expectLen * sizeof(float));
  size_t *cols = (size_t *)malloc(expectLen * sizeof(size_t));
  float *temp = (float *)malloc(width * sizeof(float));
  size_t *tempcols = (size_t *)malloc(width * sizeof(size_t));
  size_t len = 0;
  mat->rows[0] = 0;
  
  for (size_t i = 0; i < height; i++) {
    size_t lineLen = 0;
    for (size_t j = 0; j < width; j++) {
      if (rand() / (float)RAND_MAX >= ZERO_FILL) {
        temp[lineLen] = (rand() / (float)RAND_MAX) * 2.0f - 1;
        tempcols[lineLen] = j;
        lineLen++;
      }
    }

    if (lineLen > 0) {
      if (lineLen + len > expectLen) {
        size_t addLen = expectLen + width * 2 + 1;
        float *tv = (float *)malloc(addLen * sizeof(float));
        size_t *tc = (size_t *)malloc(addLen * sizeof(size_t));
        memcpy(tv, values, expectLen * sizeof(float));
        memcpy(tc, cols, expectLen * sizeof(size_t));
        values = tv;
        cols = tc;
        expectLen = addLen;
      }

      memcpy(&values[len], temp, lineLen * sizeof(float));
      memcpy(&cols[len], tempcols, lineLen * sizeof(size_t));
    }

    len += lineLen;
    mat->rows[i+1] = len;
  }

  mat->lenVal = len;
  mat->values = values;
  mat->cols = cols;

  free(tempcols);
  free(temp);
  
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
  int sparse = 0;
  size_t randH = 4, randI = 4, randW = 4;
  Matrix *a, *b;
  clock_t begin, end;
  // printf("usage: ./sparch [--sparse] [--print] [--rand] [HEIGHT_A WIDTH_A WIDTH_B]\n\n");
    
  if (argc >= 2) {
    for (int i = 0; i < argc; i++) {
      char *arg = argv[i];
      if (strcmp("--print", arg) == 0) {
        print = 1;
      } else if (strcmp("--rand", arg) == 0) {
        //srand((unsigned int)time(NULL) * getpid());
        srand(0);
        genRand = 1;
        randH = atoi(argv[argc-3]);
        randI = atoi(argv[argc-2]);
        randW = atoi(argv[argc-1]);
      } else if (strcmp("--sparse", arg) == 0) {
        sparse = 1;
      }
    }
  }

  if (sparse) {
    if (genRand == 0) {
      printf("ERROR: --sparse should be used with --rand\n");
      return -1;
    }
    
    CSRMatrix *a = randCSR(randH, randI);
    CSRMatrix *b = randCSR(randI, randW);

    begin = clock();
    CSRMatrix *mm = spgemm_sparch(a, b);
    end = clock();

    printf("running time: %f\n", (float)(end - begin) / CLOCKS_PER_SEC);
    
    CSR_free(mm);
    CSR_free(b);
    CSR_free(a);
    return 0;
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

  begin = clock();
  Matrix *gem = gemm_sparch(a, b);
  end = clock();
  
  printf("gemm_sparch running time: %f\n", (float)(end - begin) / CLOCKS_PER_SEC);

  begin = clock();
  Matrix *mm = matmul(a, b);
  end = clock();

  printf("matmul running time: %f\n", (float)(end - begin) / CLOCKS_PER_SEC);

  if (print) {
    printf("==== matA ====\n");
    Matrix_print(a);
    printf("==== matB ====\n");
    Matrix_print(b);
    printf("==== result of sparch ====\n");
    Matrix_print(gem);
  
    printf("==== result of matmul ====\n");
    Matrix_print(mm);
  }

  float absdiff = 0, diff = 0;
  for (size_t i = 0; i < gem->height * gem->width; i++) {
    float d = gem->values[i] - mm->values[i];
    absdiff += d >= 0 ? d : -d;
    diff += d;
  }
  printf("==== sum of difference: (%f) ====\n", diff);
  printf("==== sum of absolute difference: (%f) ====\n", absdiff);
  
  Matrix_free(mm);
  Matrix_free(gem);
  Matrix_free(b);
  Matrix_free(a);
  
  return 0;
}
