/*
변형된 SEGREGATED MALLOC
16, 17~32, 33~64, 65~128, 129~256, 257~512, 513~1024, 1025~2048, 2049~4096, inf
10개로 클래스로 나누어서 9번째까지는 segregated(simple) 실행, 10번째는 explicit malloc(address)
realloc시에 헤더 2번째 인자를 이용해서 2배를 extend해서 실행
태그 3개 운영
(SEGREGATED와 EXPLICIT(ADDRESS)구분) (REALLOC 버퍼 구분) (할당 구분)
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
    "Cheetah is smiling",
    /* First member's full name */
    "gilin",
    /* First member's email address */
    "aa@aa.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<14)
#define INITCHUNKSIZE (1<<6)    // 64
#define LISTLIMIT 10
#define REALLOC_BUFFER (1<<7)   // 128

// calculate max value
#define MAX(x,y) ((x)>(y) ? (x) : (y))

//size와 할당 여부를 하나로 합친다
#define PACK(size,alloc) ((size)|(alloc))

//포인터 p가 가리키는 주소의 값을 가져온다.
#define GET(p) (*(unsigned int *)(p))

//포인터 p가 가리키는 곳에 val을 역참조로 갱신
#define PUT(p,val) (*(unsigned int *)(p)=(val))

//포인터 p가 가리키는 곳의 값에서 하위 3비트를 제거하여 블럭 사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_SIZE(p) (GET(p) & ~0X7)
//포인터 p가 가리키는 곳의 값에서 맨 아래 비트를 반환하여 할당상태 판별
#define GET_ALLOC(p) (GET(p) & 0X1)
//REALLOC 구분 태그
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)
//SEGREGATED와 EXPLICIT(ADDRESS) 구분태그
#define GET_INFTAG(p)   (GET(p) & 0x4)
#define SET_INFTAG(p)   (GET(p) |= 0x4)
#define REMOVE_INFTAG(p) (GET(p) &= ~0x4)

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가리키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Address of free block's predecessor and successor entries 
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list 
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))
/* Given block pointers ptr and prev, set the PREV pointer of ptr to *prev.
bp 블록에 prev를 넣음, bp+w 블록에 next를 넣음*/
#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev)
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next)


//전역변수 
void *segregated_free_lists[LISTLIMIT];

//함수 목록
static void *find_fit_seg(int list_num);
static void place_seg(void *ptr, size_t asize, int list_num);
static void *extend_heap_seg(size_t asize, int list_num);
void remove_free(void *ptr, int list_num);
void insert_free_seg(void *ptr, size_t asize, int list_num);
static void *find_fit_exp(size_t asize);
static void *place_exp(void *ptr, size_t asize);
static void *extend_heap_exp(size_t size);
static void *coalesce(void *ptr);
void insert_free_exp(void *ptr, size_t size);


/* 
 * mm_init - initialize the malloc package.
 extend 실시 안함
 */
int mm_init(void)
{
    int list;
    char *heap_listp;
    
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    void *ptr = NULL;
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    size_t csize = asize-1;
    // segregated_free_lists 칸 확인
    int list = 0; 
    while ((list < LISTLIMIT-1) && (csize >= 16)) 
    { 
    csize >>= 1;
    list++;
    }

    if(list != 9)
    {
        if(ptr = find_fit_seg(list)!=NULL){
            place_seg(ptr, asize, list);
            return ptr;
        }
        // segregated_free_lists에 없는 경우 -> extend 필요
        if(ptr = extend_heap_seg(asize/WSIZE, list)!=NULL){
            place_seg(ptr, asize, list);
            return ptr;
        }
        return NULL;
    }

    else // list==9
    {
        if(ptr = find_fit_exp(asize)!=NULL){
            place_exp(ptr, asize);
            return ptr;
        }
        extendsize = MAX(asize, CHUNKSIZE);
        if(ptr = extend_heap_exp(extendsize) != NULL){
            place_exp(ptr, asize);
        }
        return NULL;
    }

}

static void *find_fit_seg(int list_num)
{
    void *ptr;
    ptr = segregated_free_lists[list_num];

    if (ptr != NULL)
        return ptr;
    return NULL;
}

static void place_seg(void *ptr, size_t asize, int list_num)
{
    remove_free(ptr, list_num);
    PUT(HDRP(ptr), PACK(asize, 1));
    PUT(FTRP(ptr), PACK(asize, 1));
}

static void *extend_heap_seg(size_t asize, int list_num)
{
    void *ptr;                  
    void *old_ptr;
    if ((ptr = mem_sbrk(asize*10)) == (void *)-1) 
        return NULL;
    old_ptr = ptr;
    // Set headers and footer 
    for(int i = 0; i < 10; i++)
    {
        PUT(HDRP(ptr), PACK(asize, 0));  
        PUT(FTRP(ptr), PACK(asize, 0));   
        insert_free_seg(ptr, asize, list_num);
        ptr = NEXT_BLKP(ptr);
    } 
    PUT(HDRP(ptr), PACK(0, 1));  //에필로그
    return old_ptr;
}

void remove_free(void *ptr, int list_num)
{
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list_num] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list_num] = NULL;
        }
    }
    return;
}

void insert_free_seg(void *ptr, size_t asize, int list_num)
{
    if(segregated_free_lists[list_num] != NULL)
    {
        SUCC(ptr) = segregated_free_lists[list_num];
        PRED(SUCC_PTR(ptr)) = ptr;
    }
    else
    {
        SUCC(ptr) = NULL;
    }
    PRED(ptr) = NULL;
    segregated_free_lists[list_num] = ptr;
}

static void *find_fit_exp(size_t asize)

{
    void *ptr;
    ptr = segregated_free_lists[LISTLIMIT-1];

    for(; ptr != NULL; ptr = SUCC(ptr))
    {
        if(GET_SIZE(HDRP(ptr)) >= asize)
            return ptr;
    }
    return NULL;
}

static void *place_exp(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    remove_free(ptr, LISTLIMIT-1);
    if(ptr_size >= (asize+2*ALIGNMENT)) //나눠질때
    {
        PUT(HDRP(ptr), PACK(asize, 1)); 
        PUT(FTRP(ptr), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_free_exp(ptr, remainder);
    }
    else //안나눠질때
    {
        PUT(HDRP(ptr), PACK(ptr_size, 1)); 
        PUT(FTRP(ptr), PACK(ptr_size, 1)); 
    }
    return ptr;
    
}

static void *extend_heap_exp(size_t size)
{
    void *ptr;
    size_t words = size/WSIZE;
    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((ptr = mem_sbrk(size)) == (void*)-1)
        return NULL;
    PUT(HDRP(ptr), PACK(size, 0));  
    PUT(FTRP(ptr), PACK(size, 0));   
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0,1));
    insert_free_exp(ptr, size);
    return coalesce(ptr);
}

static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); 
    size_t size = GET_SIZE(HDRP(ptr));
    //realloc 효율 개선(앞에게 realloc용 블록이면 합치지 않음)
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;
    
    if (prev_alloc && next_alloc)                          // Case 1
        return ptr;
    else if (prev_alloc && !next_alloc) {                   // Case 2
        remove_free(ptr, LISTLIMIT-1);
        remove_free(NEXT_BLKP(ptr), LISTLIMIT-1);
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        remove_free(ptr, LISTLIMIT-1);
        remove_free(PREV_BLKP(ptr), LISTLIMIT-1);
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {                                                // Case 4
        remove_free(ptr, LISTLIMIT-1);
        remove_free(PREV_BLKP(ptr), LISTLIMIT-1);
        remove_free(NEXT_BLKP(ptr), LISTLIMIT-1);
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    insert_free_exp(ptr, size);
    return ptr;
}

void insert_free_exp(void *ptr, size_t size)
{
    void *curr = segregated_free_lists[LISTLIMIT-1];
    void *saved = curr;
    void *prev = NULL;
    while (curr != NULL && ptr < curr) //프리리스트로 오는 bp가 free_listp로 오는 경우
    {
        prev = PRED(curr);
        saved = curr;
        curr = SUCC(curr);
    }

    SET_PREV_FREE(ptr, prev);
    SET_NEXT_FREE(ptr, saved);
    if (prev != NULL)
    {
        SET_NEXT_FREE(prev, ptr);
    }
    else
    {
        segregated_free_lists[LISTLIMIT-1] = ptr; /* Insert bp before current free list head*/
    }
    if (saved != NULL)
    {
        SET_PREV_FREE(saved, ptr);
    }
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    // REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    insert_free_exp(ptr, size);
    // coalesce(ptr); if list 마지막이면
    return;
}


void *mm_realloc(void *ptr, size_t size){
    return ptr;
}









