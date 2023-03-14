/*
 * ECE454 Lab 3 - Malloc
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "刘路尾生胡",
    /* First member's first name and last name */
    "Shanchun:Yi",
    /* First member's student number */
    "1005116508",
    /* Second member's first name and last name (do not modify if working alone) */
    "",
    /* Second member's student number (do not modify if working alone) */
    ""
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
#define DEBUG 0
#define WSIZE       sizeof(void *)            /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<7)      /* initial heap size (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define ALIGNEMENT 16
#define NUM_SEG_LISTS 20
#define BASE_NUM_WORDS 4 
#define BASE_BYTES (BASE_NUM_WORDS*WSIZE) // The smallest size of the seg list is BASE_NUM_WORDS*WSIZE 

void* seg_lists[NUM_SEG_LISTS];
void* heap_listp = NULL;
void* heap_epilogue = NULL;
int outer = 0;
int inner = 0;


static size_t get_size(void* bp)
{
    return GET_SIZE(HDRP(bp));
}

static size_t get_alloc(void* bp)
{
    return GET_ALLOC(HDRP(bp));
}

static void set_metadata(void* bp, size_t size, unsigned alloc)
{
    #if DEBUG
    assert(size > 0);
    #endif
    PUT(HDRP(bp), PACK(size, alloc));
    PUT(FTRP(bp), PACK(size, alloc));
}

static void clear_alloc(void* bp)
{
    uintptr_t* header = (uintptr_t*)HDRP(bp);
    *header = *header & ~0x1; 

    uintptr_t* footer = (uintptr_t*)FTRP(bp);
    *footer = *footer & ~0x1;
}

static void* get_prev(void* bp)
{
    return (void*)(*(uintptr_t**)bp);
}

static void* get_next(void* bp)
{
    return (void*)*(uintptr_t**)(FTRP(bp) - WSIZE);
}

static void set_prev(void* bp, void* prev)
{
    *(uintptr_t**)(bp) = (uintptr_t*)prev;
}

static void set_next(void* bp, void* next)
{
    *(uintptr_t**)(FTRP(bp) - WSIZE) = (uintptr_t*)next;
}

static size_t adjust_size(size_t size)
{
    if (size == 0)
    {
        return size;
    }

    size = MAX(BASE_BYTES, size + DSIZE);
    if (size % BASE_BYTES != 0)
    {
        size = size + (BASE_BYTES - size % BASE_BYTES);
    }

    return size;
}

static size_t find_seg_index(size_t size)
{
    size_t i = 0;
    size_t curr_size = BASE_BYTES;
    while (i < NUM_SEG_LISTS - 1 && curr_size < size)
    {
        curr_size = curr_size << 1;
        i++;
    }

    return i;
}

static void insert_at_start(void* bp)
{
    size_t bp_size = get_size(bp);
    size_t seg_i = find_seg_index(bp_size);

    set_next(bp, seg_lists[seg_i]);
    if (seg_lists[seg_i])
    {
        set_prev(seg_lists[seg_i], bp);
    }
    set_prev(bp, NULL);
    seg_lists[seg_i] = bp;
}

static void remove_from_seg(void* bp)
{
    void* prev = get_prev(bp);
    void* next = get_next(bp);

    if (prev && next)
    {
        set_next(prev, next);
        set_prev(next, prev);
    }

    else if (prev && !next)
    {
        set_next(prev, next);
    }

    else
    {
        size_t seg_i = find_seg_index(get_size(bp));
        seg_lists[seg_i] = next;
        if (next)
        {
            set_prev(next, NULL);
        }
    }
}

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
 int mm_init(void)
 {
   if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
         return -1;
     PUT(heap_listp, 0);                         // alignment padding
     PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
     PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
     PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
     heap_epilogue = (char*)heap_listp + 3 * WSIZE;  
     heap_listp += DSIZE;

     memset(seg_lists, 0, sizeof(void*) * NUM_SEG_LISTS);
     return 0;
 }

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/
void *coalesce(void *bp)
{
    void* left = PREV_BLKP(bp);
    void* right = NEXT_BLKP(bp);
    size_t left_alloc = get_alloc(left);
    size_t right_alloc = get_alloc(right);

    if (left_alloc && right_alloc)
    {
        return bp;
    }

    else if (!left_alloc && right_alloc)
    {
        size_t size = get_size(bp) + get_size(left);
        remove_from_seg(left);
        set_metadata(left, size, 0);

        return left;
    }

    else if (left_alloc && !right_alloc)
    {
        size_t size = get_size(bp) + get_size(right);
        remove_from_seg(right);
        set_metadata(bp, size, 0);

        return bp;
    }

    else
    {
        size_t size = get_size(bp) + get_size(left) + get_size(right);
        remove_from_seg(left);
        remove_from_seg(right);
        set_metadata(left, size, 0);

        return left;
    }
}

static void* allocate(void* bp, size_t asize)
{
    size_t orig_size = get_size(bp);
    #if DEBUG
    assert(orig_size >= asize);
    #endif
    size_t size_left = orig_size - asize;

    set_metadata(bp, asize, 1);
    if (size_left > 0)
    {
        #if DEBUG
        assert(size_left % BASE_BYTES == 0);
        #endif

        void* splitted_block = FTRP(bp) + DSIZE;
        set_metadata(splitted_block, size_left, 0);
        insert_at_start(splitted_block);
    }

    return bp;
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    #if DEBUG
    assert(size >= BASE_BYTES);
    #endif
    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;
    // bp is now at the head of the new memory region

    /* Initialize free block header/footer and the epilogue header */
    set_metadata(bp, size, 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header
    heap_epilogue = HDRP(NEXT_BLKP(bp));

    bp = coalesce(bp);
    return bp;
}


/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
  /* Get the current block size */
  size_t bsize = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(bsize, 1));
  PUT(FTRP(bp), PACK(bsize, 1));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    if (!bp)
    {
        return;
    }

    clear_alloc(bp);
    bp = coalesce(bp);
    insert_at_start(bp);
}


// /**********************************************************
//  * mm_malloc
//  * Allocate a block of size bytes.
//  * The type of search is determined by find_fit
//  * The decision of splitting the block, or not is determined
//  *   in place(..)
//  * If no block satisfies the request, the heap is extended
//  **********************************************************/
void *mm_malloc(size_t size)
{
    size_t asize = adjust_size(size);
    #if DEBUG
    assert(asize % BASE_BYTES == 0);
    #endif

    unsigned hashed_pos = find_seg_index(asize);
    void* ptr_to_allocate = NULL;

    for (int i = hashed_pos; i < NUM_SEG_LISTS; i++)
    {
        void* curr = seg_lists[i];
        while (curr)
        {
            inner ++;
            size_t curr_size = get_size(curr);
            if (curr_size >= asize)
            {
                ptr_to_allocate = curr;
                i = NUM_SEG_LISTS;
                break;
            }

            curr = get_next(curr);
        }
    }

    if (!ptr_to_allocate)
    {
        void* left = PREV_BLKP(heap_epilogue + WSIZE);
        if (get_alloc(left) == 0)
        {
            size_t left_size = get_size(left);
            if (left_size < asize)
            {
                ptr_to_allocate = extend_heap((asize - left_size) / WSIZE);
            }
            else
            {
                ptr_to_allocate = left;
            }
        }
        else
        {
            ptr_to_allocate = extend_heap(asize / WSIZE) ;
        }
    }
    else
    {
        remove_from_seg(ptr_to_allocate);
    }
    allocate(ptr_to_allocate, asize);
    #if DEBUG
    assert((uintptr_t)ptr_to_allocate % ALIGNEMENT == 0);
    #endif
    return ptr_to_allocate;
}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    if(size == 0){
      mm_free(ptr);
      return NULL;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
      return (mm_malloc(size));

    size_t orig_size = get_size(ptr);
    size_t asize = adjust_size(size);

    if (asize == orig_size)
    {
        return ptr;
    }

    else if (asize < orig_size)
    {
        allocate(ptr, asize);

        return ptr;
    }

    else
    {
        void* right = NEXT_BLKP(ptr);
        size_t right_alloc = get_alloc(right);
        size_t right_size = get_size(right);
        
        if (!right_alloc && right_size + orig_size >= asize)
        {
            remove_from_seg(right);
            set_metadata(ptr, orig_size + right_size, 0);
            allocate(ptr, asize);
        }

        else
        {
            void* newptr = mm_malloc(asize);
            memcpy(newptr, ptr, orig_size - DSIZE);
            mm_free(ptr);

            ptr = newptr;
        }

        return ptr;
    }
}

/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistant.
 *********************************************************/
int mm_check(void){
  return 1;
}
