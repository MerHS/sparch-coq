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
    unsigned int len;
    LLNode* head;
    LLNode* tail;
} COOChunk;

typedef struct _PriorQ {
    unsigned int count;
    COOChunk* heap[QUEUE_MAX];
} PriorQ;

// Tier 0. outer product
COOChunk* outerProd(COOChunk *left, CSRMatrix* right);

// Tier 1. hierarchical merger
COOChunk* mergeLow(COOChunk *left, COOChunk *right);
COOChunk* mergeTop(COOChunk *left, COOChunk *right);
void elimZero(COOChunk *chunk);

// Tier 2. merge tree
COOChunk* flattenByMergeTree(COOChunk** chunks, unsigned int len);

// Tier 3. matrix condensing
COOChunk** condense(CSRMatrix* csr, unsigned int* outLen); 

// Tier 4. priority queue (to implement huffman tree scheduler)
void addQueue(PriorQ *queue, COOChunk *chunk);
COOChunk* popQueue(PriorQ *queue, COOChunk *chunk);


// == Function implementations ==
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

COOChunk* flattenByMergeTree(COOChunk** chunks, unsigned int len) {
    return NULL;
}

COOChunk** condense(CSRMatrix* csr, unsigned int* outLen) {
    return NULL;
} 

void addQueue(PriorQ *queue, COOChunk *chunk) {
    return;
}

COOChunk* popQueue(PriorQ *queue, COOChunk *chunk) {
    return NULL;
}

// Main implementations

CSRMatrix* Matrix_toCSR(Matrix* matrix) {
    return NULL;
}
COOMatrix* CSR_toCOO(CSRMatrix* csr) {
    return NULL;
}
CSRMatrix* COO_toCSR(COOMatrix* coo) {
    return NULL;
}
Matrix* CSR_dense(CSRMatrix* csr) {
    return NULL;
}

CSRMatrix* spgemm_sparch(CSRMatrix* matA, CSRMatrix* matB) {
    return NULL;
}

Matrix* gemm_sparch(Matrix* matA, Matrix* matB) {
    CSRMatrix* left = Matrix_toCSR(matA);
    CSRMatrix* right= Matrix_toCSR(matB);
    CSRMatrix* result = spgemm_sparch(left, right);

    return CSR_dense(result);
}


