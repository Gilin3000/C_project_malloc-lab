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
    "cheetah",
    /* First member's full name */
    "Gilin",
    /* First member's email address */
    "aa@aa.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 기본 선언 매크로 */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 10)
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))  /*macros*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))    /* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc)) /* Read and write a word at address p */
#define GET(p) (*((unsigned int *)(p)))
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* Read the size and allocated fields from address p */
#define GET_SIZE(p) ((unsigned int)GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p) (GET(p) & 0x1) /* Given block pointer bp, compute address of its header and footer */

#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

#define HDRP(bp) ((void *)(bp)-WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - 2 * WSIZE) /* Given block pointer bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(((void *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((void *)(bp)-GET_SIZE(((void *)(bp)-2 * WSIZE)))

/* 추가 선언 매크로*/
/* Given block ptr bp, compute address of next and previous blocks
다음과 이전 블록 포인터 리턴 */
#define PREV_FREE_BLKP(ptr) (*(void **)(ptr))
#define NEXT_FREE_BLKP(ptr) (*(void **)(ptr + WSIZE))
/* Given block pointers ptr and prev, set the PREV pointer of ptr to *prev.
bp 블록에 prev를 넣음, bp+w 블록에 next를 넣음*/
#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev)
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next)

static void *heap_listp ; 
static void *free_listp ; 

/* 기본 선언  */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

/* 추가 선언*/
static void delete_node(void *bp);
static void insert_node(void *bp);

/* 최초 힙 영역 할당, 문제 있으면 -1, 없으면 0
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  epilogue 1+
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 heap_listp                   
이후 1024 바이트 할당받는 extend_heap 실행
*/
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(2 * DSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(ALIGNMENT, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(ALIGNMENT, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));         /* Epilogue  */
    heap_listp += 2*WSIZE;
    free_listp = NULL;
    /* 사이즈(바이트)를 받아서 최소단위 묶음 이상으로 늘려(bit)준다. 이후 coalesce
    init -> extend_heap -> coalesce
    malloc(할당 사이즈 부족) -> extend_heap -> coalesce
    */
    if ((extend_heap(CHUNKSIZE / WSIZE)) == NULL)
    {
        return -1;
    }
    return 0;
}

/* 사이즈(바이트)를 받아서 최소단위 묶음 이상으로 늘려(bit)준다. 이후 coalesce
init -> extend_heap -> coalesce
malloc(할당 사이즈 부족) -> extend_heap -> coalesce
    ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    ++++++++++++++++++++++++++++
    +  padding 0+  prol header 1+  prol footer 1+  epilogue 1+          생성(1024byte)
    ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    ++++++++++++++++++++++++++++
                                   heap_listp

    ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    +++++++++++++++++++++++++++++
    +  padding 0+  prol header 1+  prol footer 1+  header   0+    ..  +  footer 0+  epilogue 1+
    ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    +++++++++++++++++++++++++++++
                                   heap_listp                      bp
*/
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;
    size = ALIGN(words * WSIZE);
    //성공시 이전 brk 주소(void*), 실패시 -1
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

/* bp를 받아서 앞뒤 블록 빈칸이면 합침
init -> extend_heap -> coalesce (case1)
malloc(할당 사이즈 부족) -> extend_heap -> coalesce
free -> coalesce
realloc -> malloc -> free -> coalesce ???
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case1 : prev 1, next 1
    if (prev_alloc && next_alloc)
    {
        insert_node(bp);
        return bp;
    }
    // case2 : prev 1, next 0
    else if (prev_alloc && !next_alloc)
    {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_node(bp);
    }
    // case3 : prev 0, next 1
    else if (!prev_alloc && next_alloc)
    {
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_node(bp);
    }
    else
    {
        // case4 : prev 0, next 0
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_node(bp);
    }
    return bp;
}

/* 가용리스트에서 해당 블록 삭제
next는 bp의 다음 free블록, prev는 bp의 이전 free블록
prev가 null이라면(free맨앞), free_listp는 next, 아니면 전 블록에 next를 넣어줌
bp의 이후 free블록이 있다면(마지막이 아님), null인경우는 그냥 null

+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++delete_node++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 1+   prev    +  next   +  footer 1+  epilogue 1+
                                                           null      null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                         free_listp 
                                                           orig_bp,bp
 */
static void delete_node(void *bp)
{
    void *next = (void *)NEXT_FREE_BLKP(bp);
    void *prev = (void *)PREV_FREE_BLKP(bp);
    if (prev == NULL)
        free_listp = next; /* 프리 리스트의 처음일 경우 */
    else
        SET_NEXT_FREE(prev, next);

    if (next != NULL)
        SET_PREV_FREE(next, prev);  /* 프리 리스트의 마지막이 아닐 경우 */
}

/* bp를 free_listp에 넣어줌 

case 1. init 시 init. insert bp
bp가 curr보다 크므로 while문 실행하지 않음 => free_listp를 bp로 설정, prev에 null, next에 prol foot

+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header   0+ .. +  footer 0+  epilogue 1+
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                bp
                                
saved, curr, free_listp, prev=null

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 0+   prev    +    next       + .. +  footer 0+  epilogue 1+
                                                            null        null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                  bp     
saved, curr, prev=null                                   free_listp


+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++delete_node+++++++++++++++++++++++++++++++++insert_node++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 1+   space    +  space   + footer 1+  header 0 + prev + next + .. +  footer 0+  epilogue 1+
                                                            null        null                          null     null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                                                             bp
                                                           orig_bp 
curr, saved,free_listp =null        prev = null          

+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++delete_node+++++++++++++++++++++++++++++++++insert_node++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 1+   space1  +  space2  + footer 1+  header 0 + prev + next + .. +  footer 0+  epilogue 1+
                                                            null        null                          null   null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                                                             bp
                                                           orig_bp                                    free_listp
curr, saved,free_listp =null      prev = null          

*/
static void insert_node(void *bp)
{
    void *curr = free_listp;
    void *saved = curr;
    void *prev = NULL;
    while (curr != NULL && bp < curr) //프리리스트로 오는 bp가 free_listp로 오는 경우
    {
        prev = PREV_FREE_BLKP(curr);
        saved = curr;
        curr = NEXT_FREE_BLKP(curr);
    }

    SET_PREV_FREE(bp, prev);
    SET_NEXT_FREE(bp, saved);
    if (prev != NULL)
    {
        SET_NEXT_FREE(prev, bp);
    }
    else
    {
        free_listp = bp; /* Insert bp before current free list head*/
    }
    if (saved != NULL)
    {
        SET_PREV_FREE(saved, bp);
    }
}

/* 데이터 공간 size(bytes)를 받아서 first으로 빈 공간을 찾아서 할당한다
size가 0이면 null, ALIGNMENT보다 작으면 asize는 2*DSIZE, 이외는 ALIGN해서 사이즈 올림
이후 find_fit 해서 place하고 안되면 extend_heap해서 place한다

시작 malloc => find_fit(return null)
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 0+   prev    +    next       + .. +  footer 0+  epilogue 1+
                                                            null        null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                free_listp       
saved, curr, prev=null                                   

+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++delete_node+++++++++++++++++++++++++++++++++insert_node++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 1+   space1  +  space2  + footer 1+  header 0 + prev + next + .. +  footer 0+  epilogue 1+
                                                            null        null                          null   null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                                                             bp
                                                           orig_bp                                    free_listp
curr, saved,free_listp =null      prev = null          

 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusting block size*/
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;
    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }
    /* Adjust block size to include overhead, alignment requirements*/
    if (size <= ALIGNMENT)
    {
        asize = 2 * ALIGNMENT; /* Minimum block size 16: 8 bytes for alignment, 8 bytes for header and footer*/
    }
    else
    {
        asize = ALIGN(size + DSIZE); /* Add in overhead bytes and round up to nearest multiple of ALIGNMENT */
    }

    /* Search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL)
    {
        bp = place(bp, asize);
        return bp;
    }

    /* No fit found. Get more meomory and place the block. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL; /* No more heap space */
    }
    bp = place(bp, asize);

    return bp;
}

/*
시작 malloc => find_fit => bp(주소)는 null이 아님
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 0+   prev    +    next       + .. +  footer 0+  epilogue 1+
                                                            null        null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                free_listp 
                                                            bp(찾았다)   
*/
static void *find_fit(size_t asize)
{
    void *bp;
    for (bp = free_listp; bp != NULL; bp = NEXT_FREE_BLKP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    // overlap_free_test(bp);
    return NULL;
}

/* 
시작 malloc => find_fit => place
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 0+   prev    +    next       + .. +  footer 0+  epilogue 1+
                                                            null        null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp                free_listp 
                                                            bp(찾았다)   

+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++delete_node+++++++++++++++++++++++++++++++++insert_node++++++++++++++++++++++++++
+  padding 0+  prol header 1+  prol footer 1+  header 1+   space    +  space   + footer 1+  header 0 + prev + next + .. +  footer 0+  epilogue 1+
                                                            null        null
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                                heap_listp               free_listp -> null
                                                           orig_bp                                            
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    int remaining_free_size = csize - asize;
    if ((csize - asize) >= (2 * ALIGNMENT))
    { // Enough room left to split
        delete_node(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *orig_bp = bp;
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remaining_free_size, 0));
        PUT(FTRP(bp), PACK(remaining_free_size, 0));
        insert_node(bp);
        bp = orig_bp;
    }
    else
    { // No need to split; include entire free block in size.
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete_node(bp);
    }
    return bp;
}

/*
  mm_free - frees a block of memory, enabling it to be reused later
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}
/* mm_realloc - reallocates a memory block to update it with the given s
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize;
    void *bp;
    /* malloc 부분 */
    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }

    /* Adjust block size to include overhead, alignment requirements*/
    if (size <= ALIGNMENT)
    {
        asize = 2 * ALIGNMENT; /* Minimum block size 16: 8 bytes for alignment, 8 bytes for header and footer*/
    }
    else
    {
        // asize = ALIGN(size + (2 * ALIGNMENT)); /* Add in overhead bytes and round up to nearest multiple of ALIGNMENT */
        asize = ALIGN(size + (DSIZE));
    }

    size_t cur_size = GET_SIZE(HDRP(ptr));
    // 현재 할당보다 작은 realloc을 요구할경우
    if (cur_size > asize)
    {
        bp = place(ptr, asize);
    }
    // 현재 할당보다 큰 realloc 요구할 경우
    else if (cur_size < asize)
    {
        void *next_bp = NEXT_BLKP(ptr);
        void *next_block_header = HDRP(next_bp);
        /* see if next block has room for the new size */
        //뒤에 공간이 있는경우
        if (!GET_ALLOC(next_block_header) && GET_SIZE(next_block_header) >= (asize - cur_size))
        {
            delete_node(next_bp);
            PUT(HDRP(ptr), PACK(cur_size + GET_SIZE(next_block_header), 0));
            PUT(FTRP(ptr), PACK(cur_size + GET_SIZE(next_block_header), 0));

            void *temp1; // hold data going to be overwritten by the prev pointer in insert_node
            void *temp2; // hold data going to be overwritten by the next pointer in insert_node
            memcpy(&temp1, ptr, WSIZE);
            memcpy(&temp2, ptr + WSIZE, WSIZE);

            insert_node(ptr);
            bp = place(ptr, asize);

            /* copy back the saved data */
            memcpy(bp, &temp1, WSIZE);
            memcpy(bp + WSIZE, &temp2, WSIZE);
        }
        //find fit 공간이 있는경우
        else if ((bp = find_fit(asize)) != NULL)
        { /* Search free list for a fit*/
            bp = place(bp, asize);
            memcpy(bp, ptr, cur_size - (2 * WSIZE));
            mm_free(ptr);
        }
        // 아예 공간이 없었을경우 메모리가 없다 할당 받아야함
        else
        {
            /* No fit found. Get more meomory and place the block. */
            size_t extendsize = asize*2;
            if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
            {
                return NULL; /* No more heap space */
            }


            ////이부분 주요 수정
            size_t extend_bp_size = GET_SIZE(HDRP(bp));
            if(GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0 )//끝이 에필로그이면 할당받아 에필로그만 옮김
            {
                
                size_t realloc_size = asize-cur_size;
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                delete_node(bp);
                bp = NEXT_BLKP(ptr);
                PUT(HDRP(bp), PACK(extend_bp_size-realloc_size, 0));
                PUT(FTRP(bp), PACK(extend_bp_size-realloc_size, 0));
                insert_node(bp);


                return ptr;
            }




            bp = place(bp, asize);
            memcpy(bp, ptr, cur_size - (2 * WSIZE));
            mm_free(ptr);
        }
    }
    // 할당된것 그대로 요구할경우
    else
    {
        bp = ptr;
    }

    return bp;
}