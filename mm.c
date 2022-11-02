/*
변형된 SEGREGATED MALLOC
16, 17~32, 33~64, 65~128, 129~256, 257~512, 513~1024, 1025~2048, 2049~4096, inf
10개로 클래스로 나누어서 9번째까지는 segregated(simple) 실행, 10번째는 explicit malloc(address)
realloc시에 헤더 2번째 인자를 이용해서 2배를 extend해서 실행
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
#define CHUNKSIZE (1<<12)
#define INITCHUNKSIZE (1<<6)    // 64
#define LISTLIMIT 20
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

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가리키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

//segregated list 내에서 next 와 prev의 포인터를 반환
#define NEXT(ptr) (*(char **)(ptr))
#define PREV(ptr) (*(char **)(PREV_PTR(ptr)))

//전역변수 
char *heap_listp = 0;
void *segregated_free_lists[LISTLIMIT];

//함수 목록
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    
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
    heap_listp += (2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;  
    return 0;
}
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 요청받은 크기를 2워드 배수(8byte)로 반올림. 그리고 힙 공간 요청
    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    insert_node(bp,size);       // 가용 리스트에 새로 할당받은 영역 추가

    return coalesce(bp);        // 가용 블록 합치기
}

static void insert_node(void *ptr, size_t size) {
    int idx = 0;   // 리스트의 인덱스
    void *search_ptr = ptr; 
    void *insert_ptr = NULL; //실제 노드가 삽입되는 위치
    
    // Select segregated list 
    // 2의 지수승으로 인덱스를 나누어 리스트를 관리하므로
    // size의 비트를 하나씩 제거하며 카운트를 세면 그 카운트수가 리스트의 index가 됨.
    while ((idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        idx++;
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[idx];    // search_ptr이 할당되어있으면 null이 아니겠지?
    // 첫 삽입이라면 search_ptr이 null이니까 반복문을 거치치 않음
    // 이 위치에 삽입이 되어있다면 null이 아닐 것이고 기존 블록의 사이즈보다 만들려는 사이즈가 더 크면 반복문 시작
    // 이게 가용 리스트에서 찾는 게 아니라 할당된 리스트에서 찾는거지?
    // insert_ptr이 가리키는 곳은 연속된 힐당된 주소 중 가장 끝에 있는 주소
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;        // insert ptr에 기존에 있던 주소값으로 업데이트
        search_ptr = NEXT(search_ptr);  // search ptr의 위치를 뒤 블록으로 옮김
    }
    
    // Set NEXT and PREV 
    // 이제부터 insert_ptr이 앞 블록, search_ptr이 뒷 블록이라고 보면 되겠지?
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {       // 앞뒤가 모두 할당된 블록인 경우
            SET_PTR(NEXT_PTR(ptr), search_ptr);     // 가용 리스트의 ptr의 next를 뒷 블록 주소로 변경
            SET_PTR(PREV_PTR(search_ptr), ptr);     // 뒷 블록의 앞 주소를 ptr로 변경
            SET_PTR(PREV_PTR(ptr), insert_ptr);     // ptr의 앞 주소를 앞 블록 주소로 변경
            SET_PTR(NEXT_PTR(insert_ptr), ptr);     // 앞 주소의 뒷 주소를 ptr로 변경
        } else {                        // 앞이 비었고 뒤가 할당된 경우
            SET_PTR(NEXT_PTR(ptr), search_ptr);     // ptr의 다음 주소를 뒷 블록으로 변경
            SET_PTR(PREV_PTR(search_ptr), ptr);     // 뒷 블록의 앞 주소를 ptr로 변경
            SET_PTR(PREV_PTR(ptr), NULL);           // ptr의 앞 주소를 null로 변경
            segregated_free_lists[idx] = ptr;       // 가용 리스트의 인덱스에 ptr 업데이트. 앞 포인터가 갱신되는 상황이니까?
        }
    } else {
        if (insert_ptr != NULL) {       // 앞이 할당되었고 뒤가 비어있는 경우
            SET_PTR(NEXT_PTR(ptr), NULL);           // ptr의 뒷 주소를 null로 변경
            SET_PTR(PREV_PTR(ptr), insert_ptr);     // ptr의 앞 주소를 앞 블록으로 변경
            SET_PTR(NEXT_PTR(insert_ptr), ptr);     // 앞 블록의 뒷 주소를 ptr로 변경
        } else {                        // 둘다 비어있는 경우
            SET_PTR(NEXT_PTR(ptr), NULL);           // ptr의 앞 주소 null로 변경
            SET_PTR(PREV_PTR(ptr), NULL);           // ptr의 뒷 주소 null로 변경
            segregated_free_lists[idx] = ptr;       // 가용 리스트의 인덱스에 ptr 업데이트. 앞 포인터가 갱신되는 상황이니까?
        }
    }
    
    return;
}

static void delete_node(void *ptr) {
    int idx = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    // 사이즈에 맞는 가용 리스트의 인덱스 찾기
    while ((idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        idx++;
    }
    
    if (NEXT(ptr) != NULL) {
        if (PREV(ptr) != NULL) {        // 앞 블록과 뒷 블록이 할당되어있는 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), PREV(ptr));    // 뒷 블록의 앞 주소를 앞 블록으로
            SET_PTR(NEXT_PTR(PREV(ptr)), NEXT(ptr));    // 앞 블록의 뒷 주소를 뒷 블록으로
        } else {    // 앞 블록이 가용 블록이고 뒷 블록이 할당된 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), NULL);         // 뒷 블록의 앞 주소를 null로 변경
            segregated_free_lists[idx] = NEXT(ptr);     // 가용 리스트에 뒷 블록 주소 넣기
        }
    } else {
        if (PREV(ptr) != NULL) {        // 앞 블록이 할당되었고 뒷 블록이 가용 블록인 경우
            SET_PTR(NEXT_PTR(PREV(ptr)), NULL);         // 앞 블록의 뒷 주소를 null로 변경
        } else {                        // 앞 블록과 뒷 블록 모두 가용 블록인 경우
            segregated_free_lists[idx] = NULL;          // 가용 리스트에 null 
        }
    }
    
    return;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

//전,후에 free block 이 있을시 합쳐줌 + 합쳐지는 경우 segregation_lists에서 기존 free block 노드 삭제해줌
// 합칠 때 기존 가용 블록들을 리스트에서 삭제하고 합쳐진 크기로 다시 리스트에 삽입
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){    // 뒷 블록이 가용 블록인 경우
        delete_node(bp);                // bp 블록 삭제
        delete_node(NEXT_BLKP(bp));     // bp의 뒷 블록 삭제
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc && next_alloc){    // 앞 블록이 가용 블록인 경우
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{               // 앞 뒷 블록이 모두 가용 블록인 경우
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp,size);       // bp가 가용 블록의 위치이므로 가용 블록 추가
    return bp;
}

static void *find_fit(size_t asize){
    char *bp; 
    
    int idx = 0; 
    size_t searchsize = asize;      // 찾고자 하는 사이즈
    // Search for free block in segregated list
    // 인덱스 0부터 가용 리스트 검색
    while (idx < LISTLIMIT) {
        // 마지막 인덱스 or (?? 비트연산 and 해당 인덱스가 할당된 경우)
        if ((idx == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[idx] != NULL))) {
            bp = segregated_free_lists[idx];    // bp에 현재 서치중인 블록 주소 넣기
            // Ignore blocks that are too small or marked with the reallocation bit
            // 너무 작거나 재할당 비트로 표시된 블록 무시
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))  // bp 블록이 비어있지 않고 타겟사이즈를 넣을 수 있는 블록을 찾을 때까지
            {
                bp = NEXT(bp);  // 블록 탐색
            }
            if (bp != NULL)     // 할당 가능한 블록을 찾은 경우
                return bp;
        }
        
        searchsize >>= 1;   // 반복문 종료 조건
        idx++;              // 인덱스를 올려서 더 큰 블록을 서치
    }

    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    delete_node(bp);

    if ((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        insert_node(bp,(csize-asize));
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    
    insert_node(bp,size);

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}