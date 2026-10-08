/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
static char *heap_listp;
static char *free_listp;
// static char *free_lastp;

#define NUM_CLASSES 20                       // 서랍 개수. 짝수8바이트 정렬
static char *seg_heads;                      // 서랍 머리 20칸이 시작하는 주소

#define SEG_HEAD(cls)        TO_PTR(GET(seg_heads + (cls)*WSIZE))       // cls번 서랍의 첫 블록
#define SET_SEG_HEAD(cls, p) PUT(seg_heads + (cls)*WSIZE, TO_OFF(p))   // cls번 서랍의 첫 블록을 p

#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define HEAP_BASE ((char *)mem_heap_lo())       // 힙 시작 주소
#define TO_OFF(p) ((p) ? (unsigned int)((char *)(p) - HEAP_BASE) : 0)
#define TO_PTR(off) ((off) ? (void *)(HEAP_BASE + (off)) : NULL)

#define SET_PRED(bp, p)  PUT(bp, TO_OFF(p))
#define SET_SUCC(bp, p)  PUT((char *)(bp) + WSIZE, TO_OFF(p))
#define GET_PRED(bp)     TO_PTR(GET(bp))
#define GET_SUCC(bp)     TO_PTR(GET((char *)(bp) + WSIZE))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_free(void *bp);
static void remove_free(void *bp);
static int get_size_class(size_t size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((seg_heads = mem_sbrk(NUM_CLASSES*WSIZE)) == (void *)-1)
        return -1;
    for (int i = 0; i < NUM_CLASSES; i++)
        PUT(seg_heads + i*WSIZE, 0);         // 모든 서랍을 빈 상태로

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);
    free_listp = NULL;

    if (extend_heap(2*DSIZE/WSIZE) == NULL)      // 16바이트 = 4워드
        return -1;
    return 0;
}

static int get_size_class(size_t size)
{
    int cls = 0;
    while (cls < NUM_CLASSES - 1 && size > 16) {
        size >>= 1;                     // 2로 나누기
        cls++;
    }
    return cls;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_free(bp);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}




/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)
        return NULL;

    if (size >= 64 && size <= 512) {      // 2의 거듭제곱으로 올림
        size_t p = 1;
        while (p < size)
            p <<= 1;                      
            size = p;                         // 예: 448 → 512, 100 → 128
    }
    if(size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);     // 할당 공간 + 헤더,푸터 + 반올림
    
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = asize;
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){

    for (int cls = get_size_class(asize); cls < NUM_CLASSES; cls++) {   // 내 서랍부터 큰 서랍 쪽으로
        char *bp = SEG_HEAD(cls);
        char *best = NULL;

    while(bp){
        size_t size = GET_SIZE(HDRP(bp));
        if(!GET_ALLOC(HDRP(bp)) && size >= asize){
            if(size == asize)
                return bp;
            if(!best || size < GET_SIZE(HDRP(best)))
                best = bp;
        }       
        bp = GET_SUCC(bp);
    }

    if (best)                       // 이 서랍에서 찾았으면 끝
        return best;
    }
    return NULL;                        // 어느 서랍에도 없으면 힙 늘리기
}

void place(void *bp, size_t asize){
    if(GET_SIZE(HDRP(bp)) < asize + 2*DSIZE){       // PRED, SUCC 고려 크기 3*DSIZE 안되면 통으로
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        remove_free(bp);
    }
    else{       
        size_t resize = GET_SIZE(HDRP(bp)) - asize;     // 분할
        remove_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(resize, 0));
        PUT(FTRP(bp), PACK(resize, 0));
        insert_free(bp);
    }
}

static void insert_free(void *bp)
{
    int cls = get_size_class(GET_SIZE(HDRP(bp)));

    if(!SEG_HEAD(cls)){            //초기 listp 설정
        SET_SEG_HEAD(cls, bp);
        SET_SUCC(bp, NULL);
        SET_PRED(bp, NULL);
    }else{                      //마지막 listp에 연결
        SET_PRED(SEG_HEAD(cls), bp);
        SET_SUCC(bp, SEG_HEAD(cls));
        SET_SEG_HEAD(cls, bp);
        SET_PRED(bp, NULL);
    }
}

static void remove_free(void *bp)
{
    int cls = get_size_class(GET_SIZE(HDRP(bp)));

    if(bp == SEG_HEAD(cls))  // 맨 앞 위치 list 삭제
    {   
        SET_SEG_HEAD(cls, GET_SUCC(bp));
        if (SEG_HEAD(cls))
            SET_PRED(SEG_HEAD(cls), NULL);
    }
    else if(GET_PRED(bp) && GET_SUCC(bp)){      // 앞 뒤로 연결된 list 삭제
        SET_PRED(GET_SUCC(bp), GET_PRED(bp));
        SET_SUCC(GET_PRED(bp), GET_SUCC(bp));
    }
    else if(GET_PRED(bp) && !GET_SUCC(bp)){     // 마지막 위치 list 삭제
        SET_SUCC(GET_PRED(bp), NULL);
        SET_PRED(bp, NULL);
    }


}

/* mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_free(bp);
    coalesce(bp);
}
static void *coalesce(void *bp)     // 가용 블록 병합
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free(bp);            
        remove_free(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));        
        insert_free(bp);
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_free(PREV_BLKP(bp));
        remove_free(bp);
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_free(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_free(PREV_BLKP(bp));
        remove_free(bp);
        remove_free(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
        insert_free(bp);
    }
    return bp;

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t asize;

    if (!ptr){
        return mm_malloc(size);
    }
    else if (!size){
        mm_free(ptr);
        return NULL;
    }


    if (size <= DSIZE)
        asize = 2*DSIZE;
    else    
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    

    size_t col_size = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    size_t cur_size = GET_SIZE(HDRP(ptr));
    size_t need = MAX(asize - GET_SIZE(HDRP(ptr)), 2*DSIZE);

    if (cur_size >= asize)
        return ptr;
    else if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && col_size >= asize)
    {
        remove_free(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(col_size, 1));
        PUT(FTRP(ptr), PACK(col_size, 1));
        return ptr;
    }else if (!GET_SIZE(HDRP(NEXT_BLKP(ptr))) && GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
    {
        if (extend_heap(need / WSIZE) == NULL)
            return NULL;
        
        col_size = cur_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        remove_free(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(col_size, 1));
        PUT(FTRP(ptr), PACK(col_size, 1));

        return ptr;
    }
    else{
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        memcpy(newptr, ptr, GET_SIZE(HDRP(ptr)) - DSIZE);
        mm_free(ptr);

        return newptr;
    }
}