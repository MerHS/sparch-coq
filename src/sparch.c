#include <stdlib.h>
#include "sparch.h"

#define LOW_COMP 4
#define TOP_COMP 4
#define HUFF_WAY 64

typedef struct _LLNode {
    COOItem* item;
    struct _LLNode* next;
} LLNode;

typedef struct _COOChunk {
    size_t len;
    LLNode* head;
    LLNode* tail;
} COOChunk;

// min heap by chunk len
typedef struct _PriorQ {
    size_t count;
    size_t maxCount;
    COOChunk** heap;
} PriorQ;

LLNode* LLNode_malloc(COOItem *item);
void LLNode_free(LLNode *node);
void LLNode_freeAll(LLNode *node);
COOChunk *COOChunk_malloc();
void COOChunk_free(COOChunk *chunk);
void COOChunk_freeList(COOChunk *chunk);
void COOChunk_push(COOChunk *chunk, COOItem *item);
void COOChunk_append(COOChunk *left, COOChunk *right);
CSRMatrix* COOChunk_toCSR(COOChunk *chunk, size_t height, size_t width);

// Tier 0. outer product
// calculate outer product of condensed column and matrix.
void outerProd(COOChunk *left, CSRMatrix* right, COOChunk *result);

// Tier 1. hierarchical merger
// merge right to left
void merge(COOChunk *left, COOChunk *right, COOChunk *result);
// 4x4 low merger (merge right to left)
void mergeLow(COOChunk *left, COOChunk *right, COOChunk *result);
// 4x4 top merger (merge right to left)
void mergeTop(COOChunk *left, COOChunk *right, COOChunk *result, size_t maxBound);
// 8-chunk zero eliminator
void elimZero(COOChunk *chunk);

// Tier 2. merge tree
// non-parallel merge tree. the tree is constructed on-the-fly.
// maximum len is 64 (HUFF_WAY). 
void flattenByMergeTree(COOChunk **chunks, size_t len, COOChunk *result);

// Tier 3. matrix condensing
// return each column of condensed matrix left-to-right
// the count of column is set to outLen.
COOChunk** condense(CSRMatrix *csr, size_t *outLen); 

// Tier 4. priority queue (to implement huffman tree scheduler)
void swapHeap(COOChunk **heap, size_t i, size_t j);
void addQueue(PriorQ *queue, COOChunk *chunk);
COOChunk* popQueue(PriorQ *queue);


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

COOChunk* COOChunk_malloc() {
    COOChunk* chunk = (COOChunk *)malloc(sizeof(COOChunk));
    chunk->len = 0;
    chunk->head = NULL;
    chunk->tail = NULL;
    return chunk;
}

void COOChunk_free(COOChunk *chunk) {
    free(chunk);
}

void COOChunk_freeList(COOChunk *chunk) {
    LLNode *head, *next;
    head = chunk->head;
    while (head) {
        next = head->next;
        LLNode_free(head);
        head = next;
    }
}

void COOChunk_push(COOChunk *chunk, COOItem* item) {
    LLNode *node = LLNode_malloc(item);
    if (chunk->tail) {
        chunk->tail->next = node;
        chunk->tail = node;
    } else {
        chunk->tail = node;
        chunk->head = node;
    }
    chunk->len += 1;
}

void COOChunk_append(COOChunk *left, COOChunk* right) {
    if (left->tail) {
        if (right->tail) {
            left->len += right->len;
            left->tail->next = right->head;
            left->tail = right->tail;
        }
    } else {
        left->len = right->len;
        left->head = right->head;
        left->tail = right->tail;
    }
}

CSRMatrix* COOChunk_toCSR(COOChunk *chunk, size_t height, size_t width) {
    size_t len = chunk->len;
    CSRMatrix *csr = CSR_malloc(height, width, len);
    LLNode* head = chunk->head;
    COOItem* item;
    size_t rowId = 0;
    csr->rows[0] = 0;
    
    for (size_t i = 0; i < len; i++) {
        item = head->item;
        csr->values[i] = item->value;
        csr->cols[i] = item->col;

        while (rowId < item->row) {
            rowId++;
            csr->rows[rowId] = i + 1;
        }
        
        head = head->next;
    }

    while (rowId <= height) {
        csr->rows[rowId] = height * width;
        rowId++;
    }
    
    return csr;
}

void outerProd(COOChunk *left, CSRMatrix* right, COOChunk *result) {
    size_t len = left->len;
    LLNode *colHead;
    
    result->len = 0;
    result->head = NULL;
    result->tail = NULL;
    
    colHead = left->head;
    
    for (size_t i = 0; i < len; i++) {
        COOItem *item = colHead->item;
        size_t leftVal = item->value;
        size_t row = item->row;
        size_t rowId = item->col;
        size_t rightRowStart = right->rows[rowId];
        size_t rightRowEnd = right->rows[rowId + 1];
        
        for (size_t i = rightRowStart; i < rightRowEnd; i++) {
            float rightVal = right->values[i];
            size_t col = right->cols[i];
            COOItem *newItem = COOItem_malloc(row, col, leftVal * rightVal);
            
            COOChunk_push(result, newItem);
        }

        colHead = colHead->next;
    }
    
    return;
}

void mergeLow(COOChunk *left, COOChunk *right, COOChunk* result) {
    
}

void mergeTop(COOChunk *left, COOChunk *right, COOChunk* result, size_t maxBound) {
    
}

void elimZero(COOChunk *chunk) {
    return;
}

void merge(COOChunk *left, COOChunk *right, COOChunk *result) {
    /* if (right == NULL) { */
    /*     result->len = left->len; */
    /*     result->head = left->head; */
    /*     result->tail = left->tail; */
    /*     return; */
    /* } */

    // naive merge
    LLNode *li, *ri, *node;
    li = left->head;
    ri = right->head;

    result->len = 0;
    result->head = NULL;
    result->tail = NULL;

    while (!(li == NULL && ri == NULL)) {
        if (li == NULL) {
            node = ri;
            ri = ri->next;
        } else if (ri == NULL) {
            node = li;
            li = li->next;
        } else {
            COOItem *litem = li->item;
            COOItem *ritem = ri->item;
            if (litem->row < ritem->row || (litem->row == ritem->row && litem->row < ritem->row)) {
                node = li;
                li = li->next;
            } else {
                node = ri;
                ri = ri->next;
            }
        }
        
        node->next = NULL;
        COOItem *item = node->item;
        if (result->tail) {
            COOItem* tailItem = result->tail->item;
            result->len++;

            if (item->row == tailItem->row && item->col == tailItem->col) {
                tailItem->value += item->value;
            } else {
                result->tail->next = node;
            }
            
        } else {
            result->len = 1;
            result->head = node;
            result->tail = node;
        }
    }
}

void flattenByMergeTree(COOChunk **chunks, size_t len, COOChunk *result) {
    if (len <= 0)  {
        result->len = 0;
        result->head = NULL;
        result->tail = NULL;
        return;
    } else if (len == 1) {
        result->len = chunks[0]->len;
        result->head = chunks[0]->head;
        result->tail = chunks[0]->tail;
        return;
    }

    size_t currLen = len;
    COOChunk *merger = (COOChunk *)malloc(len * sizeof(COOChunk));
    COOChunk *temp = (COOChunk *)malloc((len / 2 + 1) * sizeof(COOChunk));

    for (size_t i = 0; i < len; i++) {
        merger[i].len = chunks[i]->len;
        merger[i].head = chunks[i]->head;
        merger[i].tail = chunks[i]->tail;
    }

    while (currLen > 1) {
        size_t nextLen = (currLen + 1) / 2;
        for (size_t i = 0; i < nextLen; i++) {
            COOChunk *left = &merger[2 * i];
            COOChunk *right = 2 * i + 1 >= currLen ? NULL : &merger[2 * i + 1];
            merge(left, right, &temp[i]);
        }

        for (size_t i = 0; i < nextLen; i++) {
            merger[i].len = temp[i].len;
            merger[i].head = temp[i].head;
            merger[i].tail = temp[i].tail;
        }

        currLen = nextLen;
    }

    result->len = merger[0].len;
    result->head = merger[0].head;
    result->tail = merger[0].tail;

    free(merger);
    free(temp);
}

COOChunk** condense(CSRMatrix* csr, size_t* outLen) {
    size_t len = 0;
    for (size_t i = 0; i < csr->height; i++) {
        size_t rowCnt = csr->rows[i+1] - csr->rows[i];
        if (rowCnt > len) {
            len = rowCnt;
        }
    }

    *outLen = len; 
    COOChunk **chunks = (COOChunk **)malloc(len * sizeof(COOChunk *));

    size_t height = csr->height;
    for (size_t i = 0; i < len; i++) {
        COOChunk *chunk = COOChunk_malloc();
        chunks[i] = chunk;

        for (size_t j = 0; j < height; j++) {
            size_t rowCnt = csr->rows[j+1] - csr->rows[j];
            if (i < rowCnt) {
                size_t idx = csr->rows[j] + i;
                size_t col = csr->cols[idx];
                float value = csr->values[idx];
                COOItem *item = COOItem_malloc(j, col, value);
                COOChunk_push(chunk, item);
            }
        }
    }
    
    return chunks;
} 

void swapHeap(COOChunk **heap, size_t i, size_t j) {
    COOChunk *temp;
    temp = heap[i];
    heap[i] = heap[j];
    heap[j] = temp;
}

void addQueue(PriorQ *queue, COOChunk *chunk) {
    if (queue->count >= queue->maxCount) return;
    
    COOChunk **heap = queue->heap;
    size_t idx, parent;
    
    queue->count++;
    idx = queue->count;
    heap[idx] = chunk;

    while (idx > 1) {
        parent = idx / 2;
        if (heap[idx]->len < heap[parent]->len) {
            swapHeap(heap, idx, parent);
        }
        idx = parent;
    }
}

COOChunk* popQueue(PriorQ *queue) {
    if (queue->count == 0) return NULL;

    queue->count--;

    size_t idx = 1;
    size_t count = queue->count;
    COOChunk **heap = queue->heap; 
    COOChunk *result = heap[1];

    swapHeap(heap, 0, count);

    while (idx < count) {
        size_t leftIdx = idx * 2;
        size_t rightIdx = idx * 2 + 1;
        
        if (count < leftIdx) {
            idx = leftIdx;
        } else if (count == leftIdx) {
            if (heap[idx]->len > heap[leftIdx]->len) {
                swapHeap(heap, idx, leftIdx);
            }
            idx = leftIdx;
        } else {
            if (heap[idx]->len > heap[leftIdx]-> len) {
                if (heap[idx]->len > heap[rightIdx]->len) {
                    if (heap[leftIdx]->len < heap[rightIdx]->len) {
                        swapHeap(heap, idx, leftIdx);
                        idx = leftIdx;
                    } else {
                        swapHeap(heap, idx, rightIdx);
                        idx = rightIdx;
                    }
                } else {
                    swapHeap(heap, idx, leftIdx);
                    idx = leftIdx;
                }
            } else if (heap[idx]->len > heap[rightIdx]->len) {
                swapHeap(heap, idx, rightIdx);
                idx = rightIdx;
            } else {
                idx = rightIdx;
            }
        }
    }
    
    return result;
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
    size_t height = matrix->height;
    size_t width = matrix->width;
    size_t count = height * width;
    size_t lenVal = 0;
    
    for (size_t i = 0; i < count; i++) {
        if (matrix->values[i] != 0.0) {
            lenVal++;
        }
    }

    CSRMatrix* csr = CSR_malloc(height, width, lenVal);
    size_t index = 0;
    csr->rows[0] = 0;
    
    for (size_t i = 0; i < height; i++) {
        for (size_t j = 0; j < width; j++) {
            size_t offset = i * width + j;
            float value = matrix->values[offset];
            if (value != 0.0) {
                csr->values[index] = value;
                csr->cols[index] = j;
                index++;
            } 
        }
        csr->rows[i+1] = index;
    }

    return csr;
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
    size_t width = csr->width;
    size_t height = csr->height;
    Matrix *mat = Matrix_malloc(height, width);
    size_t count = height * width;
    
    for (size_t i = 0; i < count; i++) {
        mat->values[i] = 0;
    }

    for (size_t i = 0; i < height; i++) {
        size_t rowStart = csr->rows[i];
        size_t rowEnd = csr->rows[i + 1];
        for (size_t j = rowStart; j < rowEnd; j++) {
            size_t idx = i * width + csr->cols[j];
            mat->values[idx] = csr->values[j];
        }
    }
    
    return mat;
}

CSRMatrix* spgemm_sparch(CSRMatrix* matA, CSRMatrix* matB) {
    size_t leftLen = 0;
    COOChunk **leftChunk = condense(matA, &leftLen);
    COOChunk *multVal = (COOChunk *)malloc(leftLen * sizeof(COOChunk));

    for (size_t i = 0; i < leftLen; i++) {
        outerProd(leftChunk[i], matB, &multVal[i]);
    }

    PriorQ pq;
    pq.count = 0;
    pq.maxCount = leftLen;
    pq.heap = (COOChunk **)malloc((leftLen + 1) * sizeof(COOChunk *));

    for (size_t i = 0; i < leftLen; i++) {
        addQueue(&pq, &multVal[i]);
    }

    size_t mergedIdx = 0;
    size_t kInit = (leftLen - 2) % (HUFF_WAY - 1) + 2; 
    COOChunk *treeItems[HUFF_WAY];
    COOChunk *mergedVal = (COOChunk *)malloc((leftLen / (HUFF_WAY - 1) + 1) * sizeof(COOChunk));

    for (size_t i = 0; i < kInit; i++) {
        treeItems[i] = popQueue(&pq);
    }
    flattenByMergeTree(treeItems, kInit, &mergedVal[0]);
    addQueue(&pq, &mergedVal[0]);
    mergedIdx++;
    
    while (pq.count > 1) {
        size_t count = (pq.count < HUFF_WAY) ? pq.count : HUFF_WAY;
        for (size_t i = 0; i < count; i++) {
            treeItems[i] = popQueue(&pq);
        }
        flattenByMergeTree(treeItems, count, &mergedVal[mergedIdx]);
        addQueue(&pq, &mergedVal[mergedIdx]);
        mergedIdx++;
    }

    COOChunk* result = popQueue(&pq);
    
    for (size_t i = 0; i < leftLen; i++) {
        COOChunk_free(leftChunk[i]);
    }
    free(leftChunk);
    free(pq.heap);
    free(mergedVal);
    free(multVal);
    
    return COOChunk_toCSR(result, matA->height, matB->width);
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


