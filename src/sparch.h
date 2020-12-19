#ifndef __SPARCH_H_
#define __SPARCH_H_

typedef struct _Matrix {
    unsigned int height;
    unsigned int width;
    float** values;
} Matrix;

typedef struct _COOItem {
    unsigned int row;
    unsigned int col;
    float value;
} COOItem;

typedef struct _COOMatrix {
    unsigned int height;
    unsigned int width;
    unsigned int len;
    COOItem* values; 
} COOMatrix;

typedef struct _CSRMatrix {
    unsigned int height;
    unsigned int width;
    unsigned int lenVal;
    unsigned int lenCol;
    unsigned int lenRow;
    float* values;
    unsigned int* cols;
    unsigned int* rows;
} CSRMatrix;

#endif // __SPARCH_H_