/*
SEGREGATED LIST

1. init -> 시작시에는 expend 안함

2. malloc -> 
2.1 find_fit 해당 크기 ptr불러옴 (성공하면 2.3)
2.2 공간이 부족한 경우 => 알맞은 값의 10배 받아옴(extend) => 프리리스트 해당 클래스에 잘라 넣음
16~32, 33~64, 65~128, 129~256, 257~512, 513~1024, 1025~2048, 2049~4096 에 플러스 데이터구조
4097~inf  (explicit address)으로 접근 

2.3 find_fit 성공 = > place 할당
2.4 delete_node 노드 리스트에서 삭제

3. free 
3.1 insert_node 해당크기간

4. realloc 공간 확인
4.1 공간이 부족한 경우 새로 필요한 공간+(적당량)2배만큼 더 확보,
    있던 공간은 잘라서 클래스로 사용(만약 끝이면 부족부분을 extend)
4.2 공간이 되면 그냥 늘림
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

// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<8)
#define CHUNKSIZE (1<<10)

#define LISTLIMIT 10        
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks 
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// Address of free block's predecessor and successor entries 
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list 
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

// End of my additional macros

// Global var
void *segregated_free_lists[LISTLIMIT]; 

// Functions
// static void *extend_heap(size_t size);
// static void *coalesce(void *ptr);
// static void *find_fit(int list_num);
// static void *place(int list_num, size_t asize);
// static void insert_node(void *ptr, size_t size);
// static void delete_node(void *ptr);


/* init 
힙 리스트를 만듬 성공시 0, 실패시 -1
클래스는 16~32, 33~64, 65~128, 129~256, 257~512, 513~1024, 1025~2048, 2049~4096, 4097~inf로
9개를 만듬
4개 공간에 패딩, 프롤로그 헤더, 프롤로그 풋터, 에필로그 헤더 할당
extend_heap해서 inf클래스에 넣어줌
*/
int mm_init(void)
{
    int list;         
    char *heap_start; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // Allocate memory for the initial empty heap 
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    if(extend_heap(INITCHUNKSIZE) == NULL) 
        return -1;
    
    return 0;
}

/* extend_heap
extend 해서 inf 클래스로 몰아준다
*/
static void *extend_heap(size_t size)
{
    void *ptr;                   
    void *next_ptr;
    size_t asize;                // 수정된 사이즈
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));  
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));   
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    
    // inf클래스 next로 몰아주기
    if (segregated_free_lists[LISTLIMIT-1] == NULL)
    {
        segregated_free_lists[LISTLIMIT-1] = ptr;
    }
    else
    {
        for(next_ptr = segregated_free_lists[LISTLIMIT-1]; *(void **)(next_ptr + WSIZE) != NULL;
        next_ptr =  *(void **)(next_ptr+WSIZE));
    
        SUCC(next_ptr) = ptr;
        PRED(ptr) = next_ptr;
        *(void **)(ptr + WSIZE) = NULL;
    }
    // coalesce
    return ptr;
}

/* malloc
말록해서 실패시 null, 성공시 prev부분 반환
할당할 크기 asize로 설정, segregated_free_lists의 몇번째 칸인지 확인
1. inf칸 이라면, inf칸에 공간있으면 할당, X-> inf와 chunk의 max크기만큼 extend하고 할당
2. inf칸 아니라면, inf칸에 공간있으면 할당, X-> inf리스트칸 최대 10칸 받아옴(X-> extend_heap이후) 
할당은 place
*/
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    
    // Ignore size 0 cases
    if (size <= 0)
        return NULL;
    
    // Align block size
    if (size <= DSIZE) 
        asize = 2 * DSIZE;
    else 
        asize = ALIGN(size+DSIZE);

    // segregated_free_lists 칸 확인
    int list = 0; 
    while ((list < LISTLIMIT) && (asize > 16)) 
    { 
    asize >>= 1;
    list++;
    }

    //  1. inf칸, inf와 chunk의 max크기만큼 extend하고 할당
    if (asize > 16)
        {
            list = LISTLIMIT-1;
            if((ptr = find_fit_inf(list, asize))!=NULL){ // find성공
            place_inf(ptr,asize); //가능하면 초과부분 분할
            return ptr;
            }
            
            // find실패 공간없음
            extendsize = MAX(asize,CHUNKSIZE);
            if((ptr = extend_heap(extendsize/WSIZE)) == NULL)
                return NULL;
            ptr = find_fit_inf(list, asize);
            place_inf(ptr,asize);
            return ptr;
        }

    // 2. inf아닌칸, 찾아보고 없으면 inf리스트칸에서 최대 10칸 받아옴(없다면 extend_heap이후) 
    // segregated_free_lists 칸과 동기화(16일시에 16~32(1,2,4,8,16,32))  
    
    // case1 find_fit으로 해당칸 확인
    if((ptr = find_fit_node(list))!=NULL){
        place_node(ptr); //가능하면 초과부분 분할
        return ptr;
    }
    
    int i = list + 4;
    int temp_chunksize =2;
    for (; i > 0; i--)
        temp_chunksize = temp_chunksize * temp_chunksize;
    temp_chunksize = (temp_chunksize + 8) * 10; //40? 10? byte단위

    // case2 없다면 inf리스트칸 최대 10칸까지 가져옴, case1부터 실행
    if(bring_list(list, temp_chunksize)!=0){
        ptr = find_fit_node(list);
        place_node(ptr);
        return ptr;
    }

    // case3 없다면 extend_heap 실행, case1부터 실행
    if((ptr = extend_heap(temp_chunksize/WSIZE)) != NULL){
        bring_list(list, temp_chunksize);
        ptr = find_fit_node(list);
        place_node(ptr);
        return ptr;
    }
    return NULL;
}

/* find_fit_node
list_num을 받아서 해당 클래스에 공간이 있나 확인해본다 아니면 null*/
static void *find_fit_node(int list_num)
{
    void *ptr;
    ptr = segregated_free_lists[list_num];

    if (ptr != NULL)
        return ptr;
    return NULL;
}
/* find_fit_inf
free_list에 맞는 ptr을 받아서 에필로그 만날때까지 이동하며 사이즈가 asize보다 크면 ptr 반환 */
static void *find_fit_inf(int list_num, size_t asize)
{
    void *ptr;
    ptr = segregated_free_lists[list_num];
    if (ptr != NULL)
        for(; ptr != NULL; ptr = SUCC(ptr))
        {
            if(GET_SIZE(HDRP(ptr)) >= asize)
                return ptr;
        }
    return NULL;
}
// ptr 삭제해주고 헤더, 풋터 붙여준다
static void place_node(void *ptr)
{
    size_t asize = GET_SIZE(ptr);
    remove_free_block(ptr);
    PUT_NOTAG(HDRP(ptr), PACK(asize, 1));
    PUT_NOTAG(FTRP(ptr), PACK(asize, 1));
}
/* place_inf
ptr블록은 삭제하고 크기가 크면 나눠서 할당하고 맞으면 그냥 할당*/
static void place_inf(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));
    remove_free_block(ptr);
    if ((csize - asize) >= (2*DSIZE)){
        PUT_NOTAG(HDRP(ptr), PACK(asize,1));//현재 크기를 헤더에 집어넣고
        PUT_NOTAG(FTRP(ptr), PACK(asize,1));
        ptr = NEXT_BLKP(ptr);
        PUT_NOTAG(HDRP(ptr), PACK(csize-asize,0));
        PUT_NOTAG(FTRP(ptr), PACK(csize-asize,0));
        put_free_block(ptr); // free list 첫번째에 분할된 블럭을 넣는다.
    }
    else{
        PUT_NOTAG(HDRP(ptr), PACK(csize,1));
        PUT_NOTAG(FTRP(ptr), PACK(csize,1));
    }
}

static int bring_list(int list_num, int temp_chunksize)
{
    void *ptr;
    ptr = segregated_free_lists[list_num];
    return 0;
}

static void remove_free_block(void *ptr)
{

}

static void put_free_block(void *ptr)
{

}
