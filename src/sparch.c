#include <stdlib.h>
#include "sparch.h"

#define LOW_COMP 4
#define TOP_COMP 4
#define HUFF_WAY 64
#define QUEUE_MAX 1280

typedef struct _LLNode {
    COOItem* item;
    struct _LLNode* next;
} LLNode;

typedef struct _COOChunk {
    size_t len;
    LLNode* head;
    LLNode* tail;
} COOChunk;

typedef struct _PriorQ {
    size_t count;
    COOChunk* heap[QUEUE_MAX];
} PriorQ;

// Tier 0. outer product
LLNode* LLNode_malloc(COOItem *item);
void LLNode_free(LLNode *node);
void LLNode_freeAll(LLNode *node);

void COOChunk_free(COOChunk *chunk);
void COOChunk_freeAll(COOChunk *chunk);

// calculate outer product of condensed column and matrix.
COOChunk* outerProd(COOChunk *left, CSRMatrix* right);


// Tier 1. hierarchical merger

// 4x4 low merger
COOChunk* mergeLow(COOChunk *left, COOChunk *right);

// 4x4 top merger
COOChunk* mergeTop(COOChunk *left, COOChunk *right);

// 8-chunk zero eliminator
void elimZero(COOChunk *chunk);


// Tier 2. merge tree
COOChunk* flattenByMergeTree(COOChunk** chunks, size_t len);

// Tier 3. matrix condensing
COOChunk** condense(CSRMatrix* csr, size_t* outLen); 

// Tier 4. priority queue (to implement huffman tree scheduler)
void addQueue(PriorQ *queue, COOChunk *chunk);
COOChunk* popQueue(PriorQ *queue, COOChunk *chunk);


// == Function implementations ==
LLNode* LLNode_malloc(COOItem *item) {    
    LLNode *node = (LLNode *)malloc(sizeof(LLNode));
    node->item = item;
    node->next = NULL;
    return node;
}

void LLNode_free(LLNode *node) {
    free(node);
}

void LLNode_freeAll(LLNode *node) {
    free(node->item);
    free(node);
}

void COOChunk_free(COOChunk *chunk) {
    free(chunk);
}

void COOChunk_freeAll(COOChunk *chunk) {
    LLNode *head, *next;
    head = chunk->head;
    while (head) {
        next = head->next;
        LLNode_freeAll(head);
        head = next;
    }
}

COOChunk* outerProd(COOChunk *left, CSRMatrix* right) {
    return NULL;
}

COOChunk* mergeLow(COOChunk *left, COOChunk *right) {
    return NULL;
}

COOChunk* mergeTop(COOChunk *left, COOChunk *right) {
    return NULL;
}

void elimZero(COOChunk *chunk) {
    return;
}

COOChunk* flattenByMergeTree(COOChunk** chunks, size_t len) {
    return NULL;
}

COOChunk** condense(CSRMatrix* csr, size_t* outLen) {
    return NULL;
} 

void addQueue(PriorQ *queue, COOChunk *chunk) {
    return;
}

COOChunk* popQueue(PriorQ *queue, COOChunk *chunk) {
    return NULL;
}

// Main implementations
COOItem* COOItem_malloc(size_t row, size_t col, float value) {
    COOItem *item = (COOItem *)malloc(sizeof(COOItem));
    item->row = row;
    item->col = col;
    item->value = value;
    return item;
}

void COOItem_free(COOItem* item) {
    free(item);
}

Matrix* Matrix_malloc(size_t height, size_t width) {
    Matrix *matrix;
    float *values = (float *)malloc((height * width) * sizeof(float));
    matrix = (Matrix *)malloc(sizeof(Matrix));

    matrix->height = height;
    matrix->width = width;
    matrix->values = values;
    
    return matrix;
}

void Matrix_free(Matrix* matrix) {
    free(matrix->values);
    free(matrix);
}

CSRMatrix* Matrix_toCSR(Matrix* matrix) {
    return NULL;
}

CSRMatrix* CSR_malloc(size_t height, size_t width, size_t lenVal) {
    CSRMatrix *csr;
    size_t *cols, *rows;
    float *values = (float *)malloc(lenVal * sizeof(float));
    cols = (size_t*)malloc(lenVal * sizeof(size_t));
    rows = (size_t*)malloc((height + 1) * sizeof(size_t));
    csr = (CSRMatrix *)malloc(sizeof(CSRMatrix));

    csr->height = height;
    csr->width = width;
    csr->lenVal = lenVal;
    csr->values = values;
    csr->cols = cols;
    csr->rows = rows;

    return csr;
}

void CSR_free(CSRMatrix *csr) {
    free(csr->values);
    free(csr->cols);
    free(csr->rows);
    free(csr);
}

Matrix* CSR_dense(CSRMatrix* csr) {
    return NULL;
}

CSRMatrix* spgemm_sparch(CSRMatrix* matA, CSRMatrix* matB) {
    return NULL;
}

Matrix* gemm_sparch(Matrix* matA, Matrix* matB) {
    CSRMatrix* left = Matrix_toCSR(matA);
    CSRMatrix* right = Matrix_toCSR(matB);
    CSRMatrix* mm = spgemm_sparch(left, right);

    Matrix* result = CSR_dense(mm);

    CSR_free(mm);
    CSR_free(right);
    CSR_free(left);

    return result;
}


