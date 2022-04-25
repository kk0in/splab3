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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define LISTSIZE 20
#define CHECK 0

/* Basic Macros */
#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size)|(alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) &0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)
#define NEXT_PTR(ptr) ((char *)(ptr))

#define PREV(ptr) (*(char **)(PREV_PTR(ptr)))
#define NEXT(ptr) (*(char **)(ptr))

#define SET(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Global Variable */
void **segfree_lists = NULL; // 
char *heap_listp = 0;

/* Functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void add(void *ptr, size_t size);
static void delete(void *ptr);
int mm_check(void);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //initial heap 생성, segregated free list size(LISTSIZE)+4(Alignment padding, Prologue header, Prologue footer, Epilogue header)만큼 size로 설정
    if((segfree_lists = mem_sbrk((LISTSIZE+4)*WSIZE)) == (void*)-1) {
	return -1;
    }

    //segregated free list 초기화
    for(int i=0; i<LISTSIZE; i++) {
        segfree_lists[i] = NULL;
    }

    heap_listp = (char*)segfree_lists + LISTSIZE*WSIZE; // heap_listp는 segregated free list 영역 다음에 설정
    PUT(heap_listp, 0); // alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (2*WSIZE);

    //empty heap 확장
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
	return -1;
    }
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize; // adjusted block size 
    size_t extendsize; // no fit -> extend heap size 
    char *bp;

    // size가 0이하면 무시
    if(size <= 0) {
	return NULL;
    }

    // align the size 
    if(size <= DSIZE)
	newsize = 2*DSIZE;
    else 
	newsize = ALIGN(size+SIZE_T_SIZE);

    //find_fit 함수 이용해서 align된 size가 fit 가능한지 확인 -> 가능하면 fit 진행(place)
    if((bp=find_fit(newsize)) != NULL) {
        place(bp, newsize);
        return bp;
    }

    //위에서 fit이 불가능하면, heap을 extend해서 place 진행
    extendsize = MAX(newsize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, newsize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // null pointer는 무시
    if(bp == NULL) {
	return;
    }
    
    //macro 이용하여 주어진 block pointer가 가르키는 block의 size 파악
    size_t size = GET_SIZE(HDRP(bp));
    
    //free 진행
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    //bp가 NULL이면, malloc으로 동작
    if(bp == NULL) mm_malloc(size);
    
    // size가 음수이면 NULL return, 0이면 free로 동작
    if((int)size < 0) return NULL;
    else if ((int)size == 0) {
	mm_free(bp);
	return NULL;
    }
    //general case
    else {
	size_t oldsize = GET_SIZE(HDRP(bp)); //i parameter의 bp가 가르키는 block의 size, 즉 이전 size
	size_t newsize = size + DSIZE; // 새로 바꾸고자 하는 size, header+footer 때문에 DSIZE만큼 더 필요

	//size가 줄어들 때: 원래 포인터 그대로 return
	if(newsize <= oldsize) {
	    return bp;
	}
	//size가 늘어날 때
	else {
	    size_t nalloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // next block이 free인지 allocated인지 확인하기 위한 변수
	    size_t tempsize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp))); // next block의 size와 원래 size의 합
	    //next block이 free이긴 하지만 이걸 다 써도 부족함 or next block이 애초에 free가 아님 -> 완전 새로 옮김
	    if((newsize > tempsize) || nalloc) {
		void *newbp = mm_malloc(newsize); // 새로 malloc 진행
                memcpy(newbp, bp, newsize); // memcpy 함수 이용하여 메모리 복사
                mm_free(bp); // 새로 malloc 했으므로 원래 bp가 가르키는 block은 free
                return newbp;
	    }
	    //위 상황이 아니면 next block에 이어서 allocate 가능
	    else {
	        delete(NEXT_BLKP(bp)); // next block을 allocated에 사용하므로 segregated free list에서 next block 삭제
                PUT(HDRP(bp), PACK(tempsize, 1)); // 크기가 조정된 새로운 header 
		PUT(FTRP(bp), PACK(tempsize, 1)); // 크기가 조정된 새로운 footer
		return bp;
	    }
	}
    }
}

static void *extend_heap(size_t words) 
{
    char *bp;

    //for alignment 
    size_t size = (words % 2) ? (words+1)*WSIZE : words*WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1) {
	return NULL;
    }
    
    // free block header/footer 
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    //new epilogue header
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 2: prev block-allocated, next block-freed
    if(prev_alloc && !next_alloc) {
	delete(NEXT_BLKP(bp)); // next block을 segregated free list에서 삭제

	size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // size 병합
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
    }

    //case 3: prev block-freed, next block-allocated
    if(!prev_alloc && next_alloc) {
	delete(PREV_BLKP(bp)); // prev block을 segregated free list에서 삭제

	size += GET_SIZE(HDRP(PREV_BLKP(bp))); // size 병합
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp); // prev block과 병합되었기 때문에 bp가 prev block의 bp로 바뀜
    }
    if(!prev_alloc && !next_alloc) {
	delete(PREV_BLKP(bp)); // prev block을 segregated free list에서 삭제
	delete(NEXT_BLKP(bp)); // next block을 segregated free list에서 삭제

	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // size 병합
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp); // prev block과 병합되었기 때문에 bp가 prev block의 bp로 바뀜
    }

    // case 1: both-allocated -> prev or next block을 segregated free list에서 삭제할 필요도 없고, 병합이 일어나지 않아서 size를 다시 계산할 필요도 없다. 새로 free된 block에 대해서만 아래 add 수행
    add(bp, size); // 모든 case에서 새로 합쳐진 freed block을 segregated free list에 add해야함

    //heap의 상태가 바뀌었으므로 checker로 확인
    //CHECK가 1이면 mm_check를 호출하고 CHECK가 0이면 호출하지 않는다.
    if(CHECK) {
	if(!mm_check()) {
	    printf("fail\n"); exit(0);
	} 
    }

    return bp;
}

static void place(void *bp, size_t asize)
{
    //asize: 할당하고자 하는 size
    size_t rsize = GET_SIZE(HDRP(bp)); // free 가능한 block의 실제 size
    size_t restsize = rsize - asize; // 실제 size와 할당하고자 하는 size 차이 -> 남는 size -> 일정 크기 이상이면 free list로 설정해줘서 fragment를 낮출 수 있다.
    
    delete(bp); // allocate 되었으므로 segregated free list에서 삭제
    
    //한 block을 구성하기 위해 적어도 4개의 word가 필요 (header, footer, prev, next) -> 남는 size가 4개보다 작으면, 굳이 남는 부분을 free로 바꿔주지 않는다.
    if(restsize < 4*WSIZE) {
	PUT(HDRP(bp), PACK(rsize, 1));
	PUT(FTRP(bp), PACK(rsize, 1));
	return bp;
    }
    // 남는 size에 해당하는 부분을 free list로 만들어준다. 
    else {
	
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));

	//남는 부분 free 진행
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(restsize, 0));
	PUT(FTRP(bp), PACK(restsize, 0));
	coalesce(bp);
    }
}

static void *find_fit(size_t asize)
{
    char *bp;
    size_t tempsize = asize; //asize 복사
    
    //tempsize가 1이하가 될 때 까지 2로 나누면서 segregated free list의 index를 찾는다.
    for(int i=0; i<LISTSIZE; i++) {
	//tempsize가 1 이하가 될 때의 i 값이 segregated free list 내 index에 해당한다.
	//segregated free list의 마지막 index에는 block size의 상한이 없으므로 앞에서 못들어간 block이 여기에 있을 수 있다. 
	if(((tempsize<=1)&&(segfree_lists[i]!=NULL)) || (i==LISTSIZE-1)) {
	    //first fit 방식으로 size가 맞는 block이 있는지 찾는다.
	    for(bp=segfree_lists[i]; bp!=NULL; bp=NEXT(bp)) {
	        if(asize <= GET_SIZE(HDRP(bp))) {
	    	    return bp;
	        }
	    }
	}
	//bitwise 연산으로 tempsize를 절반씩 줄여간다. 이는 segregated free list에서의 index를 찾기 위함이다.
	tempsize = tempsize >> 1;
    }

    return NULL; 
}

// segregated free list에 새로 들어오는 freed block을 알맞은 위치에 add하는 함수
static void add(void *ptr, size_t size)
{
   int i = 0; // 
   void *find; // segregated free list를 순회할 pointer
   void *add = NULL; // 이전 find 값을 저장하는 용도
   size_t tempsize = size; // size 복사
   
   //size를 2로 나눠가면서 들어갈 segregated free list 내 index 찾기
   while((tempsize>1) && (i<LISTSIZE-1)) {
	i++;
	tempsize = tempsize  >>  1;
   }
   //찾은 index에 해당하는 free list에서 옆으로 옮겨가면서 들어갈 위치 찾는다. 끝까지 가서 find가 NULL이 되거나, 맞는 size를 찾아서 size 조건이 만족되면 for loop을 나간다.
   for(find = segfree_lists[i]; ((find != NULL) && (size>GET_SIZE(HDRP(find)))); find = NEXT(find)) {
	add = find;
   }

   // 위 for문에서 끝까지 가서 find가 NULL이 된 경우
   if(find == NULL) {
	// list에 내가 처음 넣을 때
	if(add == NULL) {
	    SET(PREV_PTR(ptr), NULL); // ptr의 앞 뒤를 NULL로 setting 
	    SET(NEXT_PTR(ptr), NULL);
            segfree_lists[i] = ptr; // ptr이 맨 앞에 있으므로 segregated free list update
        }
	// ptr이 들어갈 위치의 prev에 block이 있고 next는 비어있는 경우
        else {
            SET(PREV_PTR(ptr), add); // ptr의 앞 주소를 add로 setting
            SET(NEXT_PTR(add), ptr); // add(prev block)의 뒷 주소를 ptr로 setting
	    SET(NEXT_PTR(ptr), NULL); // ptr의 next를 NULL로 setting
        }

   }
   // 위 for문에서 중간에 size 조건이 맞아 for문을 나온 경우
   else {
	// ptr이 들어갈 위치의 next에 block이 있고 prev는 비어있는 경우
	if(add == NULL) {
	    SET(PREV_PTR(ptr), NULL); // ptr의 prev를 NULL로 setting
	    SET(NEXT_PTR(ptr), find); // ptr의 next를 find(next block)으로 setting
            SET(PREV_PTR(find), ptr); // find(next block)의 prev를 ptr로 setting
            segfree_lists[i] = ptr; // ptr이 맨 앞에 있으므로 segregated free list update
        }
	// ptr이 들어갈 위치의 next, prev에 모두 block이 있는 경우
        else {
            SET(PREV_PTR(ptr), add); // ptr의 앞 주소를 add(prev block)로 setting
            SET(NEXT_PTR(add), ptr); // add의 뒤 주소를 ptr로 setting
	    SET(NEXT_PTR(ptr), find); // ptr의 뒤 주소를 find(next block)로 setting
            SET(PREV_PTR(find), ptr); // find의 앞 주소를 ptr로 setting
        }
   } 

   return;
}

// 새로 allocated 되는 block을 segregated free list에서 delete하는 함수
static void delete(void *ptr)
{
    int i = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    // 찾고자 하는 block이 있는 segregated free list 내 index 찾기
    while((size>1) && (i<LISTSIZE-1)) {
	i++;
	size = size >> 1;
    }

    //	
    if(NEXT(ptr) == NULL) {
	// delete하는 block의 앞, 뒤에 block이 없는 경우: 해당 segregated free list에 이제 block이 하나도 없으므로 segregated free block을 NULL로 update한다.
	if(PREV(ptr) == NULL) {
	    segfree_lists[i] = NULL;
        }
	// delete하는 block의 앞에만 block이 있는 경우: 앞에 있던 block의 next를 NULL로 설정해준다. 
        else {
            SET(NEXT_PTR(PREV(ptr)), NULL);
        }
    }
    //
    else {
	// delete하는 block의 뒤에만 block이 있는 경우: 뒤에 있던 block의 prev를 NULL로 설정해준다. 그리고 이제 이 block이 맨 앞에 있으므로 segregated free list를 update한다.
	if(PREV(ptr) == NULL) {
	    SET(PREV_PTR(NEXT(ptr)), NULL);
            segfree_lists[i] = NEXT(ptr);
        }
	// delete하는 block의 앞, 뒤에 block이 있는 경우: 이 둘을 이어준다
        else {
            SET(NEXT_PTR(PREV(ptr)), NEXT(ptr)); 
	    SET(PREV_PTR(NEXT(ptr)), PREV(ptr));
        }
    }
    return;
}

/* Heap Checker */
int mm_check(void)
{
    void *ptr;
    int freelists = 0;
    int freeblocks = 0;
    void *start = mem_heap_lo(); // pointer to the first byte in the heap
    void *end = mem_heap_hi(); // ponter to the last byte in the heap
    size_t heapsize = mem_heapsize(); // current size of the heap in bytes

    //Is every block in the free list marked as free?
    for(int i=0; i<LISTSIZE; i++) {
	for(ptr = segfree_lists[i]; ptr != NULL; ptr = NEXT(ptr)) {
	    //Is every block in the free list marked as free?
	    //segregated free list를 순회하는데, alloc이 있으면 안됨
	    if(GET_ALLOC(HDRP(ptr)) || GET_ALLOC(FTRP(ptr))) {
		printf("ERROR: Some block in the free list is not marked as free\n");
		return 0;
	    }
	    //Do the pointers in the free list point to valid free blocks?
	    //ptr은 pointers in the free list를 의미하며, valid하기 위해서는 heap 범위 내에 있어야함
	    if((ptr > end) || (ptr < start)) {
		printf("ERROR: Some pointers in the free list point to unvalid free blocks\n");
                return 0;
	    }
	    //Are there any contiguous free blocks that somehow escaped coalescing?
	    //ptr(freed block)의 valid한 prev 또는 next에 대하여, 이들 역시 free이면 contiguous free blocks에 해당 
	    if(((PREV_BLKP(ptr)>start) && (!GET_ALLOC(HDRP(PREV_BLKP(ptr))))) || ((NEXT_BLKP(ptr)<end) && (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))))) ) {
		printf("ERROR: There are some contiguous free blocks that somehow escaped coalescing\n");
		return 0;
	    }

	    freelists++;
	}
    }

    for(ptr=heap_listp; ((ptr!=NULL) && (GET_SIZE(HDRP(ptr)))); ptr = NEXT_BLKP(ptr)) {
	//Do any allocated blocks overlap?
	//ptr의 next block과 ptr의 차이가 ptr이 있는 (block size - WSIZE) 보다 커야한다. 그렇지 않으면 overlap이 있다는 뜻이다. 
	if(GET_ALLOC(HDRP(ptr))) {
	    if((NEXT_BLKP(ptr) -(char*)ptr) <= (GET_SIZE(HDRP(ptr)) - WSIZE)) {
		printf("ERROR:i Some allocated blocks overlap\n");
		return 0;
	    }
	}
	else freeblocks++;

	//Do the pointers in a heap block point to valid heap address?
	//ptr은 pointers in a heap을 의미하며, valid한 범위 내에 있어야 한다.
	if(ptr<start || ptr>end) {
            printf("ERROR: Pointers do not point to a valid heap address\n");
            return 0;
        }	
    }

    //Is every free block actually in the free list?
    //위 두 개의 for문에서 한번은 segregated free list를 순회하면서 free list의 개수를 세고, 한번은 heap을 >순회하면서 GET_ALLOC을 조사하여 free block의 개수를 세었다. 이 둘이 같은 값을 가지고 있어야 한다.
    if(freelists != freeblocks) {
	printf("ERROR: Some free blocks are not in free lists, freelists: %d, freeblocks: %d\n", freelists, freeblocks);
	return 0;
    }

    //Pointer size check
    //start, end, heapsize 값이 서로 맞아 떨어지는지를 확인한다.
    if(end >= start+heapsize) {
	printf("ERROR: Pointer does not point to last byte of the heap\n");
	return 0;
    }

    return 1;
}







