#include <stdio.h>
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
void COOChunk_freeNodes(COOChunk *chunk, size_t cnt);
void COOChunk_freeAll(COOChunk *chunk);
void COOChunk_push(COOChunk *chunk, COOItem *item);
void COOChunk_append(COOChunk *chunk, LLNode *node);
void COOChunk_concat(COOChunk *left, COOChunk *right);
CSRMatrix* COOChunk_toCSR(COOChunk *chunk, size_t height, size_t width);
void COOChunk_print(COOChunk *chunk);
// Tier 0. outer product
// calculate outer product of condensed column and matrix.
void outerProd(COOChunk *left, CSRMatrix* right, COOChunk *result);

// Tier 1. hierarchical merger
// return 1 if coordinate of left is greater than right
// zero if same coordinate, -1 if less.
int posCmp(COOItem *left, COOItem* right); 
// merge naive way
void merge(COOChunk *left, COOChunk *right, COOChunk *result);
// hierarchical merger
void mergeHier(COOChunk *left, COOChunk *right, COOChunk *result);
// 4x4 low merger (append to the result)
void mergeLow(COOChunk *left, COOChunk *right, COOItem* minBound, COOItem* maxBound, COOChunk *result);
// 4x4 top merger (append to the result)
int mergeTop(COOChunk *left, COOChunk *right, COOChunk *result, int lastDirection);
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

void COOChunk_freeNodes(COOChunk *chunk, size_t cnt) {
    LLNode *next;
    while (chunk->len > 0 && cnt > 0) {
        next = chunk->head->next;
        LLNode_freeAll(chunk->head);
        chunk->head = next;
        chunk->len--;
        cnt--;
    }
    
    if (chunk->len == 0) {
        chunk->head = NULL;
        chunk->tail = NULL;
    }
}

void COOChunk_freeAll(COOChunk *chunk) {
    LLNode *head, *next;
    size_t len = chunk->len;
    head = chunk->head;
    for (size_t i = 0; i < len; i++) {
        next = head->next;
        LLNode_freeAll(head);
        head = next;
    }
    free(chunk);
}

void COOChunk_push(COOChunk *chunk, COOItem* item) {
    LLNode *node = LLNode_malloc(item);
    COOChunk_append(chunk, node);
}

void COOChunk_append(COOChunk *chunk, LLNode *node) {
    if (chunk->tail) {
        chunk->tail->next = node;
        chunk->tail = node;
    } else {
        chunk->tail = node;
        chunk->head = node;
    }
    chunk->len += 1;
}

void COOChunk_concat(COOChunk *left, COOChunk* right) {
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
            csr->rows[rowId] = i;
        }
        
        head = head->next;
    }

    while (rowId < height) {
        rowId++;
        csr->rows[rowId] = len;
    }
    
    return csr;
}

void COOChunk_print(COOChunk *chunk) {
    LLNode *node = chunk->head;
    if (node) {
        printf("%zu nodes\n", chunk->len);
        while (node) {
            printf("(%zu, %zu, %6.2f)\n", node->item->row, node->item->col, node->item->value);
            node = node->next;
        }
    } else {
        printf("EMPTY\n");
    }
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
        float leftVal = item->value;
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

int posCmp(COOItem *left, COOItem* right) {
    if (left->row < right->row) {
        return -1;
    } else if (left->row == right->row) {
        if (left->col < right->col) {
            return -1;
        } else if (left->col == right->col) {
            return 0;
        } else {
            return 1;
        }
    } else {
        return 1;
    }
}

void mergeLow(COOChunk *left, COOChunk *right, COOItem* minBound, COOItem* maxBound, COOChunk* result) {
    // comparator array
    int comp[LOW_COMP+1][LOW_COMP+1];
    COOChunk temp;
    temp.len = 0;
    temp.head = NULL;
    temp.tail = NULL;

    // slice by chunk
    size_t lenA = left->len;
    size_t lenB = right->len;

    // making top comparator
    LLNode *an, *bn;
    bn = right->head;
    for (size_t i = 0; i < lenB; i++) {
        an = left->head;
        for (size_t j = 0; j < lenA; j++) {
            comp[i][j] = posCmp(an->item, bn->item) > 0 ? 1 : 0;
            an = an->next;
        }
        bn = bn->next;
        comp[i][lenA] = 1;
    }
    for (size_t j = 0; j <= lenA; j++) {
        comp[lenB][j] = 0;
    }
    
    // merge
    size_t posX = 0;
    size_t posY = 0;
    an = left->head;
    bn = right->head;

    // DANGER: left and right should be reused, so we must not break both chunks.
    while (!(posX >= lenA && posY >= lenB)) {
        int currComp = comp[posY][posX];
        COOItem *item;
            
        if (currComp) { // current cell is < : go down
            item = COOItem_malloc(bn->item->row, bn->item->col, bn->item->value);
            bn = bn->next;
            posY++;
        } else { // current cell is >= : go right
            item = COOItem_malloc(an->item->row, an->item->col, an->item->value);
            an = an->next;
            posX++;
        }
        
        COOChunk_push(&temp, item);
    }

    // add same and set bound
    size_t tempLen = temp.len;
    an = temp.head;
    for (size_t i = 0; i < tempLen; i++) {
        if (an->next && (posCmp(an->item, an->next->item) == 0)) {
            an->item->value += an->next->item->value;
            an->next->item->value = 0;
        }
        if (!(posCmp(minBound, an->item) <= 0 && (!maxBound || posCmp(an->item, maxBound) < 0))) {
            an->item->value = 0;
        }
        an = an->next;
    }
    
    // eliminate zero and concat to result
    elimZero(&temp);
    
    COOChunk_concat(result, &temp);
}

int mergeTop(COOChunk *left, COOChunk *right, COOChunk* result, int lastDirection) {
    int comp[TOP_COMP][TOP_COMP] = { 0 };
    COOChunk chunkA[TOP_COMP];
    COOChunk chunkB[TOP_COMP];

    // slice by chunk
    size_t lenLeft, lenRight;
    size_t lenA, lenB;
    lenLeft = left->len;
    lenRight = right->len;
    lenA = ((lenLeft + (LOW_COMP - 1)) / LOW_COMP);
    lenA = lenA > TOP_COMP ? TOP_COMP : lenA;
    lenB = ((lenRight + (LOW_COMP - 1)) / LOW_COMP);
    lenB = lenB > TOP_COMP ? TOP_COMP : lenB;

    LLNode *head = left->head;
    for (size_t i = 0; i < lenA; i++) {
        size_t chunkLen = lenLeft - i * LOW_COMP;
        chunkLen = chunkLen < LOW_COMP ? chunkLen : LOW_COMP;
        chunkA[i].len = chunkLen;
        chunkA[i].head = head;
        for (size_t j = 0; j < chunkLen - 1; j++) {
            head = head->next;
        }
        chunkA[i].tail = head;
        head = head->next;
    }

    head = right->head;
    for (size_t i = 0; i < lenB; i++) {
        size_t chunkLen = lenRight - i * LOW_COMP;
        chunkLen = chunkLen < LOW_COMP ? chunkLen : LOW_COMP;
        chunkB[i].len = chunkLen;
        chunkB[i].head = head;
        for (size_t j = 0; j < chunkLen - 1; j++) {
            head = head->next;
        }
        chunkB[i].tail = head;
        head = head->next;
    }

    // making top comparator and bound
    for (size_t i = 0; i < lenB; i++) {
        for (size_t j = 0; j < lenA; j++) {
            comp[i][j] = posCmp(chunkA[j].tail->item, chunkB[i].tail->item) > 0 ? 1 : 0;
        }
    }

    int direction = lastDirection;
    size_t posX = 0;
    size_t posY = 0;
    COOItem minBound, maxBound;
    
    switch (direction) {
        case 1:
            maxBound.row = chunkA[posX].head->item->row;
            maxBound.col = chunkA[posX].head->item->col;
            break;
        case -1:
            maxBound.row = chunkB[posY].head->item->row;
            maxBound.col = chunkB[posY].head->item->col;
            break;
        default:
            maxBound.row = 0;
            maxBound.col = 0;
            break;
    }

    int lastDir;
    while (posX < lenA && posY < lenB) {
        int currComp = comp[posY][posX];
        COOChunk *currA = &chunkA[posX];
        COOChunk *currB = &chunkB[posY];

        // set min bound
        minBound.row = maxBound.row;
        minBound.col = maxBound.col;

        lastDir = direction;
        if (currComp) { // current cell is < : go down
            posY++;
            direction = -1;
        } else { // current cell is >= : go right
            posX++;
            direction = 1;
        }

        if (posX < lenA && posY < lenB) {
            // go right before -> chunk A is min bound
            // go down before -> chunk B is min bound
            COOChunk *maxChunk = (direction == 1) ? &chunkA[posX] : &chunkB[posY];  
            maxBound.row = maxChunk->head->item->row;
            maxBound.col = maxChunk->head->item->col;
                
            mergeLow(currA, currB, &minBound, &maxBound, result);

            if (direction == 1) {
                /* left->len -= currA->len; */
                /* left->head = maxChunk->head; */
                COOChunk_freeNodes(left, currA->len);
            } else {
                /* right->len -= currB->len; */
                /* right->head = maxChunk->head; */
                COOChunk_freeNodes(right, currB->len);
            }
        } else if (posX == lenA && lenLeft <= LOW_COMP * TOP_COMP){ // hit the maximal right border
            // remained chunks fit to top/low comparator: merge every remained chunks
            // maxBound NULL indicates unlimited.
            mergeLow(currA, currB, &minBound, NULL, result);
            COOChunk_freeNodes(left, left->len);
            COOChunk_freeNodes(right, currB->len);
            /* left->len = 0; */
            /* left->head = NULL; */
            /* left->tail = NULL; */
            /* right->len -= currB->len; */
            /* right->head = currB->tail->next; */
            /* if (right->head == NULL) { */
            /*     right->tail = NULL; */
            /* } */
        } else if (posY == lenB && lenRight <= LOW_COMP * TOP_COMP) { // hit the maximal bottom border
            mergeLow(currA, currB, &minBound, NULL, result);
            COOChunk_freeNodes(right, right->len);
            COOChunk_freeNodes(left, currA->len);
            /* right->len = 0; */
            /* right->head = NULL; */
            /* right->tail = NULL; */
            /* left->len -= currA->len; */
            /* left->head = currA->tail->next; */
            /* if (left->head == NULL) { */
            /*     left->tail = NULL; */
            /* } */
        } else { // load last direction for next mergeTop
            direction = lastDir;
        }
    }


    return direction;
}

void elimZero(COOChunk *chunk) {
    size_t zeroCount[LOW_COMP*2];
    COOChunk temp;
    temp.len = 0;
    temp.head = NULL;
    temp.tail = NULL;

    size_t len = chunk->len;
    LLNode* node, *next;
    node = chunk->head;
    for (size_t i = 0; i < len; i++) {
        next = node->next;
        if (node->item->value == 0) {
            LLNode_freeAll(node);
        } else {
            COOChunk_append(&temp, node);
        }
        node = next;    
    }

    chunk->len = temp.len;
    chunk->head = temp.head;
    chunk->tail = temp.tail;
}

void mergeHier(COOChunk *left, COOChunk *right, COOChunk *result) {
    result->len = 0;
    result->head = NULL;
    result->tail = NULL;
    
    if (left == NULL || left->head == NULL) {
        if (right == NULL || right->head == NULL) {
            return;
        }
        result->len = right->len;
        result->head = right->head;
        result->tail = right->tail;
        return;
    } else if (right == NULL || right->head == NULL) {
        result->len = left->len;
        result->head = left->head;
        result->tail = left->tail;
        return;
    }

    int direction = 0;
    while (left->len > 0 && right->len > 0) {
        direction = mergeTop(left, right, result, direction);
    }

    if (left->len > 0) {
        COOChunk_concat(result, left);
    }
    
    if (right->len > 0) {
        COOChunk_concat(result, right);
    }

    if (result->tail) {
        result->tail->next = NULL;
    }
}

void merge(COOChunk *left, COOChunk *right, COOChunk *result) {
    // naive merge
    LLNode *li, *ri, *node;
    result->len = 0;
    result->head = NULL;
    result->tail = NULL;
    
    if (left == NULL || left->head == NULL) {
        if (right == NULL || right->head == NULL) {
            return;
        }
        result->len = right->len;
        result->head = right->head;
        result->tail = right->tail;
        return;
    } else if (right == NULL || right->head == NULL) {
        result->len = left->len;
        result->head = left->head;
        result->tail = left->tail;
        return;
    }

    li = left->head;
    ri = right->head;
    
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
            if (posCmp(litem, ritem) < 0) {
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

            if (item->row == tailItem->row && item->col == tailItem->col) {
                tailItem->value += item->value;
                LLNode_freeAll(node);
            } else {
                result->len++;
                result->tail->next = node;
                result->tail = node;
            }
        } else {
            result->len = 1;
            result->head = node;
            result->tail = node;
        }
    }

    if (result->tail) {
        result->tail->next = NULL;
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
            mergeHier(left, right, &temp[i]);
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

    COOChunk **heap = queue->heap; 
    COOChunk *result = heap[1];
    swapHeap(heap, 1, queue->count);
    queue->count--;

    size_t idx = 1;
    size_t count = queue->count;

    while (idx < count) {
        size_t leftIdx = idx * 2;
        size_t rightIdx = idx * 2 + 1;
        
        if (count < leftIdx) {
            break;
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
                break;
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

    // left is zero matrix
    if (leftLen == 0) {
        free(leftChunk);
        return CSR_malloc(matA->height, matB->width, 0);
    }
    
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
    size_t kInit = leftLen >= 2 ? (leftLen - 2) % (HUFF_WAY - 1) + 2 : leftLen; 
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
    CSRMatrix *csr = COOChunk_toCSR(result, matA->height, matB->width);

    LLNode* node = result->head;
    LLNode* next;
    while (node) {
        next = node->next;
        LLNode_freeAll(node);
        node = next;
    }
    
    for (size_t i = 0; i < leftLen; i++) {
        COOChunk_freeAll(leftChunk[i]);
    }
    free(leftChunk);
    free(pq.heap);
    free(mergedVal);
    free(multVal);

    return csr;
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


Matrix* matmul(Matrix* matA, Matrix* matB) {
    if (matA->width != matB->height) return NULL;
    
    Matrix* result = Matrix_malloc(matA->height, matB->width);
    size_t height = matA->height;
    size_t width = matB->width;
    size_t iterLen = matA->width;
    
    for (size_t i = 0; i < height; i++) {
        for (size_t j = 0; j < width; j++) {
            size_t idx = width * i + j;
            size_t ai = iterLen * i;
            size_t bi = j;
                
            result->values[idx] = 0;
            for (size_t k = 0; k < iterLen; k++) {
                result->values[idx] += matA->values[ai] * matB->values[bi];
                ai++;
                bi += width;
            }
        }
    }

    return result;
}
