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
#define CHUNKSIZE (1 << 12) // 기본 extend heap amount bytes
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT
사이즈를 올림하여 ALIGNMENT로 함 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
/*size_t_size =
size_t = 32비트 운영체제에서 부호없는 32비트 정수(unsigned int)*/
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* Pack a size and allocated bit into a word
사이즈와 할당여부 패킹 -> 헤더 데이터 */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p
p가 참조하는 워드 리턴 / p에 워드 저장 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Read the size and allocated fields from address p
헤더에서 사이즈만 리턴 / 할당여부만 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer
헤더와 풋터를 가리키는 포인터 리턴 */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and previous blocks
다음과 이전 블록 포인터 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* 기본 선언*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);
static char *heap_listp;
static char *heap_nextp;

/* 최초 힙 영역 할당, 문제 있으면 -1, 없으면 0
+++++++++++++++++++++++++++++++++++++++++++++
+  prologue  +  head  +  foot  +  epilogue  +
+++++++++++++++++++++++++++++++++++++++++++++
                      heap_listp
이후 1024 바이트 할당받는 extend_heap 실행
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(2 * ALIGNMENT)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + DSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + WSIZE + DSIZE, PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    heap_nextp = heap_listp;
    return 0;
}

/* 사이즈(바이트)를 받아서 최소단위 묶음 이상으로 늘려(bit)준다. 이후 coalesce
init -> extend_heap -> coalesce
malloc(할당 사이즈 부족) -> extend_heap -> coalesce
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : (words)*WSIZE;
    //성공시 이전 brk 주소(void*), 실패시 -1
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // init 시
    // +++++++++++++++++++++++++++++++++++++++++++++   +++++++++++++++++++++++++++
    // +  prologue  +  head  +  foot  +  epilogue  +          생성(1024byte)
    // +++++++++++++++++++++++++++++++++++++++++++++   +++++++++++++++++++++++++++

    // +++++++++++++++++++++++++++++++++++++++++++++   +++++++++++++++++++++++++++
    // +  prologue  +  head  +  foot  +  head      +   ..  +  foot   +  epilogue +
    // +++++++++++++++++++++++++++++++++++++++++++++   +++++++++++++++++++++++++++
    //                                                  bp
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

/* bp를 받아서 앞뒤 블록 빈칸이면 합침
init -> extend_heap -> coalesce (효과없음)
malloc(할당 사이즈 부족) -> extend_heap -> coalesce
free -> coalesce
realloc -> malloc -> free -> coalesce // free 안하도록 바꿀예정
*/
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // case1 : prev 0, next 1
    if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // case2 : prev 1, next 0
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case3 : prev 0, next 0
    else if (!prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // case4 : prev 1, next 1
    // (효과 없음)
    heap_nextp = bp;
    return bp;
}

/* 데이터 공간 size(bytes)를 받아서 next fit으로 빈 공간을 찾아서 할당한다
size가 0이면 null, DSIZE보다 작으면 asize는 2*DSIZE, 이외는 ALIGN해서 사이즈 올림
이후 find_fit 해서 place하고 안되면 extend_heap해서 place한다
*/
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE); //asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE); // 최소 4kb씩 늘림
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* next fit으로 빈 공간 찾기
첫번째 for => 에필로그 전까지 할당x이며 사이즈가 asize보다 작아야함
두번째 for => heap_nextp 전까지 할당x이며 사이즈가 asize보다 작아야함
*/

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_nextp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    for (bp = heap_listp; bp < heap_nextp; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}


/* 남은 공간 bp와 할당량 asize를 받고, 남은 공간 bp의 사이즈 csize를 만듬
남은 공간에서 할당량을 뺀 것이 최소 공간보다 크면 나누고, 작으면 전부 할당
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* bp와 재할당 할 size를 받고, oldptr과 newptr(malloc하고 새로운 빈공간 bp)을 만듬
newptr이 할당이 안되서 null이면 bp 반납
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
    {
        return bp;
    }
    copySize = GET_SIZE(HDRP(bp));
    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*bp를 받아서 할당상태를 0으로 하고 coalesce 실시
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}