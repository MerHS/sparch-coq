#ifndef __SPARCH_H_
#define __SPARCH_H_

#include <stddef.h>

typedef struct _Matrix {
    size_t height;
    size_t width;
    float* values;
} Matrix;

typedef struct _COOItem {
    size_t row;
    size_t col;
    float value;
} COOItem;

typedef struct _CSRMatrix {
    size_t height;
    size_t width;
    size_t lenVal;
    float* values;
    size_t* cols;
    size_t* rows;
} CSRMatrix;

COOItem* COOItem_malloc(size_t row, size_t col, float value);
void COOItem_free(COOItem* item);

Matrix* Matrix_malloc(size_t height, size_t width);
void Matrix_free(Matrix* matrix);
CSRMatrix* Matrix_toCSR(Matrix* matrix);

CSRMatrix* CSR_malloc(size_t height, size_t width, size_t lenVal);
void CSR_free(CSRMatrix *csr);
Matrix* CSR_dense(CSRMatrix* csr);

Matrix* gemm_sparch(Matrix* matA, Matrix* matB);
CSRMatrix* spgemm_sparch(CSRMatrix* matA, CSRMatrix* matB);


#endif // __SPARCH_H_
