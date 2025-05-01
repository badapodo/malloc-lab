#include <stdio.h>

#include <stdlib.h>

#include <string.h>

#include <stdint.h>

#include "mm.h"

#include "memlib.h"

team_t team = {

    "8",

    "seongkwang",

    "ksg6736@gmail.com",

    "",

    ""

};

#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define WSIZE 4

#define DSIZE 8

#define CHUNKSIZE (1 << 12)

#define MINBLOCKSIZE 24

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))

#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)

#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)

#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))

#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define PRED_PTR(bp) ((char *)(bp))

#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

#define PRED(bp) (*(char **)(PRED_PTR(bp)))

#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define LISTLIMIT 20

static char *seg_free_lists[LISTLIMIT];

static void *extend_heap(size_t size);

static void *coalesce(void *bp);

static void insert_node(void *bp, size_t size);

static void remove_node(void *bp);

static int get_list_index(size_t size);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

int mm_init(void)
{

    for (int i = 0; i < LISTLIMIT; ++i)

        seg_free_lists[i] = NULL;

    char *heap_start = mem_sbrk(4 * WSIZE);

    if ((long)heap_start == -1)

        return -1;

    PUT(heap_start, 0);

    PUT(heap_start + WSIZE, PACK(DSIZE, 1));

    PUT(heap_start + 2 * WSIZE, PACK(DSIZE, 1));

    PUT(heap_start + 3 * WSIZE, PACK(0, 1));

    return extend_heap(CHUNKSIZE) == NULL ? -1 : 0;
}

static int get_list_index(size_t size)
{

    int idx = 0;

    size >>= 4;

    while (size > 1 && idx < LISTLIMIT - 1)
    {

        size >>= 1;

        idx++;
    }

    return idx;
}

static void insert_node(void *bp, size_t size)
{

    int idx = get_list_index(size);

    char *cur = seg_free_lists[idx];

    char *prev = NULL;

    // 주소 순으로 삽입 위치 찾기

    while (cur != NULL && cur < (char *)bp)
    {

        prev = cur;

        cur = SUCC(cur);
    }

    // 삽입

    if (prev == NULL)

        seg_free_lists[idx] = bp;

    else

        SUCC(prev) = bp;

    if (cur != NULL)

        PRED(cur) = bp;

    SUCC(bp) = cur;

    PRED(bp) = prev;
}

static void remove_node(void *bp)
{

    if (GET_ALLOC(HDRP(bp)))
        return;

    int idx = get_list_index(GET_SIZE(HDRP(bp)));

    if (PRED(bp))

        SUCC(PRED(bp)) = SUCC(bp);

    else

        seg_free_lists[idx] = SUCC(bp);

    if (SUCC(bp))

        PRED(SUCC(bp)) = PRED(bp);
}

static void *extend_heap(size_t size)
{

    size = ALIGN(size);

    if (size < MINBLOCKSIZE)
        size = MINBLOCKSIZE;

    char *bp = mem_sbrk(size);

    if ((long)bp == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));

    PUT(FTRP(bp), PACK(size, 0));

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    bp = coalesce(bp);

    insert_node(bp, GET_SIZE(HDRP(bp)));

    return bp;
}

static void *coalesce(void *bp)
{

    void *prev_bp = PREV_BLKP(bp);

    void *next_bp = NEXT_BLKP(bp);

    size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));

    size_t next_alloc = GET_ALLOC(HDRP(next_bp));

    size_t size = GET_SIZE(HDRP(bp));

    if (!prev_alloc && !next_alloc)
    {

        remove_node(prev_bp);

        remove_node(next_bp);

        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));

        PUT(HDRP(prev_bp), PACK(size, 0));

        PUT(FTRP(next_bp), PACK(size, 0));

        bp = prev_bp;
    }
    else if (!prev_alloc)
    {

        remove_node(prev_bp);

        size += GET_SIZE(HDRP(prev_bp));

        PUT(HDRP(prev_bp), PACK(size, 0));

        PUT(FTRP(bp), PACK(size, 0));

        bp = prev_bp;
    }
    else if (!next_alloc)
    {

        remove_node(next_bp);

        size += GET_SIZE(HDRP(next_bp));

        PUT(HDRP(bp), PACK(size, 0));

        PUT(FTRP(next_bp), PACK(size, 0));
    }
    else
    {

        // no coalescing needed

        PUT(HDRP(bp), PACK(size, 0));

        PUT(FTRP(bp), PACK(size, 0));
    }

    return bp;
}

static void *find_fit(size_t asize)
{

    int idx = get_list_index(asize);

    void *best_bp = NULL;

    size_t best_size = (size_t)-1;

    for (int i = idx; i < LISTLIMIT; ++i)
    {

        void *bp = seg_free_lists[i];

        while (bp != NULL)
        {

            size_t bsize = GET_SIZE(HDRP(bp));

            if (!GET_ALLOC(HDRP(bp)) && bsize >= asize)
            {

                if (bsize < best_size)
                {

                    best_size = bsize;

                    best_bp = bp;

                    // exact fit이면 바로 반환

                    if (bsize == asize)

                        return best_bp;
                }
            }

            bp = SUCC(bp);
        }

        if (best_bp != NULL)

            return best_bp; // 해당 리스트에서 best-fit 찾았으면 바로 반환
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{

    size_t csize = GET_SIZE(HDRP(bp));

    remove_node(bp);

    if (csize - asize >= MINBLOCKSIZE)
    {

        PUT(HDRP(bp), PACK(asize, 1));

        PUT(FTRP(bp), PACK(asize, 1));

        void *next = NEXT_BLKP(bp);

        size_t rem = csize - asize;

        PUT(HDRP(next), PACK(rem, 0));

        PUT(FTRP(next), PACK(rem, 0));

        insert_node(next, rem);
    }
    else
    {

        PUT(HDRP(bp), PACK(csize, 1));

        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{

    if (size == 0)
        return NULL;

    size_t asize = (size <= DSIZE) ? 2 * DSIZE : ALIGN(size + DSIZE);

    void *bp = find_fit(asize);

    if (bp != NULL)
    {

        place(bp, asize);

        return bp;
    }

    size_t extendsize = MAX(asize, CHUNKSIZE);

    bp = extend_heap(extendsize);

    if (bp == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}

void mm_free(void *bp)
{

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));

    PUT(FTRP(bp), PACK(size, 0));

    bp = coalesce(bp);

    insert_node(bp, GET_SIZE(HDRP(bp)));
}

void *mm_realloc(void *ptr, size_t size)
{

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0)
    {

        mm_free(ptr);

        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));

    size_t newsize = (size <= DSIZE) ? 2 * DSIZE : ALIGN(size + DSIZE);

    if (newsize <= oldsize)
        return ptr;

    // 다음 블록이 free이고 병합 시 충분한 크기 확보 가능하면

    void *next = NEXT_BLKP(ptr);

    if (!GET_ALLOC(HDRP(next)))
    {

        size_t combined_size = oldsize + GET_SIZE(HDRP(next));

        if (combined_size >= newsize)
        {

            remove_node(next); // free list에서 제거

            PUT(HDRP(ptr), PACK(combined_size, 1));

            PUT(FTRP(ptr), PACK(combined_size, 1));

            return ptr;
        }
    }

    // 기존 방식 fallback

    void *newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    size_t copySize = oldsize - DSIZE;

    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize);

    mm_free(ptr);

    return newptr;
}
