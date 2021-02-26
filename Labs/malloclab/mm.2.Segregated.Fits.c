/*
 * Author   : 0xLucifer
 * Date     : 2021 Feb
 * Desc     : 本代码实现了一个简单的 Segregated Fits Dynamic Memory Allocator
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "memlib.h"
#include "mm.h"

team_t team =
{
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static size_t freelist[64];
static char* implicit_free_list_start;
static void* extend_heap(size_t words);
static void* coalesce(void* payload_pointer);
static void  chain_attach(char* payload_pointer);
static void  chain_detach(char* payload_pointer);
static void  chop(char* payload_pointer,size_t expect_size);
static void  set_chunk_status(char* payload_pointer,size_t status);

// 本系统最小 Block 大小为      : 4*SIZE_OF_WORD
// 本系统 Block 增长的单位长度为 : SIZE_OF_DOUBLE_WORD
#define SIZE_OF_WORD                           (sizeof(size_t))
#define SIZE_OF_DOUBLE_WORD                    (sizeof(size_t)) * 2
#define CHUNKSIZE                              (1 << 12)
#define MAX(x, y)                              ((x) > (y) ? (x) : (y))
#define MIN(x, y)                              ((x) < (y) ? (x) : (y))
#define PACK(size, alloc)                      ((size) | (alloc))
// 从 generic_pointer 中取信息使用的宏
#define STATUS_ALLOCATED                       0x1
#define STATUS_FREED                           0x0
#define GET(generic_pointer)                   (*(size_t*) (generic_pointer))
#define PUT(generic_pointer, value)            (*(size_t*) (generic_pointer) = (value))
#define GET_SIZE(generic_pointer)              (size_t)(GET(generic_pointer) & ~0x7)
#define GET_STATUS_ALLOC(generic_pointer)      (size_t)(GET(generic_pointer) &  0x1)
#define GET_STATUS_PREV_ALLOC(generic_pointer) (size_t)(GET(generic_pointer) &  0x2)
// 平坦内存中计算前后相邻 Block 等所使用的宏
#define HDRP(payload_pointer)                  ((char*) (payload_pointer) - SIZE_OF_WORD)
#define FTRP(payload_pointer)                  ((char*) (payload_pointer) + GET_SIZE((char*) (payload_pointer) -SIZE_OF_WORD) - SIZE_OF_DOUBLE_WORD)
#define NEXT_BLOCK_PAYLOAD(payload_pointer)    ((char*) (payload_pointer) + GET_SIZE((char*) (payload_pointer) -SIZE_OF_WORD))
#define PREV_BLOCK_PAYLOAD(payload_pointer)    ((char*) (payload_pointer) - GET_SIZE((char*) (payload_pointer) -SIZE_OF_DOUBLE_WORD))
#define EPILOGUE_HDRP                          ((char*) (mem_heap_hi()) + 1 - SIZE_OF_WORD)
//下面两个宏主要用于在 freelist[x] 中前后指针
#define LIST_GET_NEXT(payload_pointer)         *(size_t*) ((char*) (payload_pointer))
#define LIST_GET_PREV(payload_pointer)         *(size_t*) ((char*) (payload_pointer) + SIZE_OF_WORD)

int mm_init(void)
{
    char* chunk;
    memset(freelist, 0, sizeof(freelist));
    if ((implicit_free_list_start = mem_sbrk(4 * SIZE_OF_WORD)) == (void*) -1)
    {
        return -1;
    }
    PUT(implicit_free_list_start + (0 * SIZE_OF_WORD), PACK(0    , 1));               /* Alignment padding */
    PUT(implicit_free_list_start + (1 * SIZE_OF_WORD), PACK(SIZE_OF_DOUBLE_WORD, 1)); /* Prologue  header  */
    PUT(implicit_free_list_start + (2 * SIZE_OF_WORD), PACK(SIZE_OF_DOUBLE_WORD, 1)); /* Prologue  footer  */
    PUT(implicit_free_list_start + (3 * SIZE_OF_WORD), PACK(0    , 3));               /* Epilogue  header  */
    implicit_free_list_start += (2 * SIZE_OF_WORD);
    chunk = extend_heap(CHUNKSIZE / SIZE_OF_WORD);
    if (chunk == NULL)
    {
        return -1;
    }
    chain_attach(chunk);
    return 0;
}

// 本系统中最小堆块大小为 4 * 4 =16 字节，分别为 Header, FDP, BKP, Footer.
// Payload部分最小值为12字节，总大小需要按8字节对齐，即总大小需要是8的倍数
void* mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    int    index;
    char*  payload_pointer = NULL;
    char*  chunk_fd        = 0;
    char*  chunk_bk        = 0;
    /*
        List         : size      : asize
        freelist[01] : 001 - 012 : 012 + 4 = 016
        freelist[02] : 013 - 020 : 020 + 4 = 024
        freelist[03] : 021 - 028 : 028 + 4 = 032
        freelist[04] : 029 - 036 : 036 + 4 = 040
        freelist[63] : 500 - 508 : 508 + 4 = 512
        像类似上面这种需求【范围序列 -> 值序列】，可以考虑用除法，或者说位与操作（低X位清零等）
        说白了，就是归纳出范围内所有值的一个共性：把【范围序列 -> 值序列】 转化为【范围序列的共性 -> 值序列】
    */
    if (size == 0)
    {
        return NULL;
    }
    if (size <= 12)
    {
        asize = 2 * SIZE_OF_DOUBLE_WORD;
    }
    else
    {
        asize = ((size+3)/8+1)*8;
    }
    if(asize<=512)
    {
        // 如果计算出来的 asize<=512 则优先考虑从 freelist[1] ~ freelist[63] 先查找
        for(index = asize/8-1 ; index<=63 ; index++)
        {
            // 尝试在freelist中找到一个chunk
            if (0==freelist[index])
            {
                // 当前freelist[index]链表为空，则找下一个链表
                continue;
            }
            else
            {
                // 找到了一个不为空的freelist[index]链表
                chunk_bk=&(freelist[index]);
                payload_pointer=LIST_GET_NEXT(chunk_bk);
                chain_detach(payload_pointer);
                goto DONE;
            }
        }
    }
    /*
        走到这里说明可能为如下两种情况之一：
        1、要么freelist中已经找过一遍，但是所有freelist都为空；
        2、请求的asize大于等于512，只能考虑先从freelist[0]搜索
    */
    // 尝试freelist[0]
    if (0 != freelist[0])
    {
        chunk_fd=freelist[0];
        while(1)
        {
            if(asize<=GET_SIZE(HDRP(chunk_fd)))
            {
                chain_detach(chunk_fd);
                payload_pointer = chunk_fd;
                goto DONE;
            }
            chunk_fd=LIST_GET_NEXT(chunk_fd);
            if(0==chunk_fd)
            {
                break;
            }
        }
    }
    // 走到这里说明freelist全体都无法满足，需要扩容
    // 因为这里并不是从freelist中获取出一个块出来，所以并不会像上面调用chop的时候那样，还需要先chain_detach
    payload_pointer = extend_heap(asize / SIZE_OF_WORD);
DONE:
    // 不管怎么获取到的块，最后需要切成合适的大小。如果能切出剩余块，则链入freelist
    chop(payload_pointer, asize);
    // 在返回给用户之前，要设置其状态为已分配
    set_chunk_status(payload_pointer,STATUS_ALLOCATED);
    return payload_pointer;
}

void mm_free(void* payload_pointer)
{
    payload_pointer=coalesce(payload_pointer);
    chain_attach(payload_pointer);
}

static void* extend_heap(size_t words)
{
    /*
        extend_heap的主要流程
        1、保存【旧尾块】中记录的【旧尾块的前块 的 allocated信息】，等下【旧尾块】会被【新块的Header】占据
        2、扩充一个新块出来
        3、产生一个新的尾块
        4、将【旧尾块的前块 的 allocated信息】写到【新块的Header】，并把当前块的信息写入新的尾块
        其实 extend_heap 产生的是一个 working 状态的块，不是 free 也不是 allocated（至少在本函数最后的一步 coalesce 之前是这样的）
        extend_heap相当于凭空产生一块内存出来，然后放到现有的体系当中，而不是【通过detach或attach】与frelist交互得来，也不是通过【mm_free/mm_malloc】与用户交互得来
    */
    char*  payload_pointer = 0;
    size_t size            = 0;
    size_t used_flag       = 0;

    // 扩容时最低效的情况为：只扩容出一个合法大小的块
    // 所以最低扩容大小为4个word大小
    if (words<4)
    {
        words=4;
    }

    // 查看扩容前尾块的前一个块的状态（ Allocated or freed ? ）
    used_flag=GET_STATUS_PREV_ALLOC(EPILOGUE_HDRP);

    // 计算出实际需要扩容的字节数
    size = (words % 2) ? (words + 1) * SIZE_OF_WORD : words * SIZE_OF_WORD;
    if ((long) (payload_pointer = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    // 新申请的块占据了原尾块的位置（此时为working状态）
    PUT(HDRP(payload_pointer), PACK(size, used_flag));
    PUT(FTRP(payload_pointer), PACK(size, used_flag));
    // 新的尾块
    PUT(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)), PACK(0, 1));
    // 新产生的块，从未参与过 attach 或 detach 的操作
    // 而该块后续有可能立刻被使用，所以要对其单独设一个状态
    return coalesce(payload_pointer);
}

// 合并相邻堆块的函数，在 free 和 extend_heap 这两种操作结束时会执行 coalesce 操作 
static void* coalesce(void* payload_pointer)
{
    /*
        在两种情况下，会需要调用coalesce，分别为：
        1、当需要 free 时
        2、刚刚 extend_heap 后
        合并时，不管怎么合并，一定要注意【合并以后的块】的前块的原本状态，需要保存
        在链上的是不能轻易合并的，记住这一点，因为有链子拴着
    */
    size_t prev_alloc = GET_STATUS_PREV_ALLOC(HDRP(payload_pointer));
    size_t next_alloc = GET_STATUS_ALLOC(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)));
    size_t size       = GET_SIZE(HDRP(payload_pointer));
    size_t used_flag  = 0;
    if (prev_alloc && next_alloc)
    {
        // case1 : 前后堆块都无需合并，直接返回当前堆块
    }
    else if (prev_alloc && !next_alloc)
    {
        // case2 : 后堆块可合并
        used_flag=GET_STATUS_PREV_ALLOC(HDRP(payload_pointer));
        // 将后堆块detach
        chain_detach(NEXT_BLOCK_PAYLOAD(payload_pointer));
        // 将后堆块size增加到本堆块上
        size += GET_SIZE(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)));
        // 修改合并后堆块的块首和块尾
        PUT(HDRP(payload_pointer), PACK(size, used_flag));
        PUT(FTRP(payload_pointer), PACK(size, used_flag));
    }
    else if (!prev_alloc && next_alloc)
    {
        // case3 : 前堆块可合并
        used_flag=GET_STATUS_PREV_ALLOC(HDRP(PREV_BLOCK_PAYLOAD(payload_pointer)));
        // 将前堆块detach
        chain_detach(PREV_BLOCK_PAYLOAD(payload_pointer));
        // 将前堆块size增加到本堆块上
        size += GET_SIZE(HDRP(PREV_BLOCK_PAYLOAD(payload_pointer)));
        payload_pointer=PREV_BLOCK_PAYLOAD(payload_pointer);
        // 修改合并后堆块的块首和块尾
        PUT(HDRP(payload_pointer), PACK(size, used_flag));
        PUT(FTRP(payload_pointer), PACK(size, used_flag));
    }
    else
    {
        // case4 : 前后堆块可合并
        used_flag=GET_STATUS_PREV_ALLOC(HDRP(PREV_BLOCK_PAYLOAD(payload_pointer)));
        // 将前后堆块detach
        chain_detach(PREV_BLOCK_PAYLOAD(payload_pointer));
        chain_detach(NEXT_BLOCK_PAYLOAD(payload_pointer));
        // 将前后堆块size增加到本堆块上
        size += GET_SIZE(HDRP(PREV_BLOCK_PAYLOAD(payload_pointer))) + GET_SIZE(FTRP(NEXT_BLOCK_PAYLOAD(payload_pointer)));
        payload_pointer=PREV_BLOCK_PAYLOAD(payload_pointer);
        // 修改合并前后堆块的块首和块尾
        PUT(HDRP(payload_pointer), PACK(size, used_flag));
        PUT(FTRP(payload_pointer), PACK(size, used_flag));
    }
    // 为了安全起见，这里应该把生成后的新堆块上链再下链，但是为了提升效率，就只用下面这一句
    // 但是原理要明白
    // 返回块的payload指针
    return payload_pointer;
}

// 手写实现（其实就是封装 mm_malloc 和 mm_free )
void* mm_realloc(void* payload_pointer, size_t size)
{
    char* payload_pointer_new;
    if ((payload_pointer_new = mm_malloc(size)) == NULL)
    {
        return NULL;
    }
    memcpy(payload_pointer_new, payload_pointer, MIN(size, GET_SIZE(HDRP(payload_pointer))));
    mm_free(payload_pointer);
    return payload_pointer_new;
}

static void  chain_attach(char* payload_pointer)
{
    int   size     = GET_SIZE(HDRP(payload_pointer));
    int   index    = 0;
    char* chunk_fd = 0;
    char* chunk_bk = 0;
    index          = (size - 16) / 8 + 1;
    if (index > 63)
    {
        // 如果块总大小大于等于520，就会导致index大于等于64
        // 导致只能按块大小升序放入freelist[0]
        index    =   0;
        chunk_fd =   freelist[index];
        chunk_bk = &(freelist[index]);
        if(0==chunk_fd)
        {
            // freelist[0]中没有任何块，直接放入
            LIST_GET_NEXT(payload_pointer) =  (freelist[index]);
            LIST_GET_PREV(payload_pointer) = &(freelist[index]);
            freelist[index]                =   payload_pointer;
            goto DONE;
        }
        else
        {
            // 如果需要放入freelis[0]，且freelist[0]不为空则走到这里
            while (1)
            {
                if(0==chunk_fd)
                {
                    // 正常情况下chunk_fd是不会等于0的
                    // 但如果走到这里发现等于0了，则说明走到了freelist的末尾，也就完成了place
                    // 到末尾结果发现自己才是最大的
                    LIST_GET_NEXT(chunk_bk)=payload_pointer;
                    LIST_GET_NEXT(payload_pointer)=0;
                    LIST_GET_PREV(payload_pointer)=chunk_bk;
                    goto DONE;
                }
                else
                {
                    if(size < GET_SIZE(HDRP(chunk_fd)))
                    {
                        LIST_GET_NEXT(chunk_bk)=payload_pointer;
                        LIST_GET_PREV(chunk_fd)=payload_pointer;
                        LIST_GET_NEXT(payload_pointer)=chunk_fd;
                        LIST_GET_PREV(payload_pointer)=chunk_bk;
                        goto DONE;
                    }
                }
                chunk_fd = LIST_GET_NEXT(chunk_fd);
                chunk_bk = LIST_GET_NEXT(chunk_bk);
            }
        }
    }
    else
    {
        //期望放置的块下标在 [1,63] 区间内，直接链入链首即可。
        LIST_GET_NEXT(payload_pointer)=  (freelist[index]);
        LIST_GET_PREV(payload_pointer)= &(freelist[index]);
        if(0==freelist[index])
        {
            // freelist[index]原本为空的情况
            freelist[index]=payload_pointer;
        }
        else
        {
            // freelist[index]不为空，则直接链入链首
            LIST_GET_PREV(LIST_GET_NEXT(payload_pointer))=payload_pointer;
            freelist[index]=payload_pointer;
        }
        goto DONE;
    }
DONE:
    set_chunk_status(payload_pointer,STATUS_FREED);    
}
static void  chain_detach(char* payload_pointer)
{
    int   size     = GET_SIZE(HDRP(payload_pointer));
    int   index    = 0;
    char* chunk_fd = LIST_GET_NEXT(payload_pointer);
    char* chunk_bk = LIST_GET_PREV(payload_pointer);
    if (0==chunk_fd)
    {
        LIST_GET_NEXT(chunk_bk)= 0;
    }
    else
    {
        LIST_GET_PREV(chunk_fd)= chunk_bk;
        LIST_GET_NEXT(chunk_bk)= chunk_fd;
    }
    set_chunk_status(payload_pointer,STATUS_ALLOCATED);
}

static void chop(char* payload_pointer,size_t expect_size)
{
    // 获取切之前的大小
    size_t size=GET(HDRP(payload_pointer)) & ~7;
    // 获取切之前 Header 的 flag 信息
    size_t flag=GET(HDRP(payload_pointer)) &  2;
    if (size-expect_size < 16)
    {
        /*
            case1:不需要切，因为切完后产生的小碎片无法再分配，所以不切
            所以直接设置整个块的状态
        */
        return;
    }
    else
    {
        /*
            case2:需要切，还有4件事要做
            1、切
            2、为切完的左块设置status
            3、为切完的右块设置status
            4、右块链入freelist(自动设置状态)
        */
        PUT(HDRP(payload_pointer),expect_size|flag);
        PUT(FTRP(payload_pointer),expect_size|flag);
        PUT(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)),size-expect_size);
        PUT(FTRP(NEXT_BLOCK_PAYLOAD(payload_pointer)),size-expect_size);
        // 第一个块的状态还是要手动设置的
        // 第二个块的状态会在chain_attach中自动设置
        chain_attach(NEXT_BLOCK_PAYLOAD(payload_pointer));
        return;
    }
}

static void set_chunk_status(char* payload_pointer,size_t status)
{
    // 取出 this 块的header，对倒数第 1 位清零后，保存到 this_chunk_header
    size_t this_chunk_header = GET(HDRP(payload_pointer)) & ~1;
    // 取出 next 块的header，对倒数第 2 位清零后，保存到 next_chunk_header
    size_t next_chunk_header = GET(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer))) & ~2;
    switch (status)
    {
        case STATUS_ALLOCATED:
            PUT(HDRP(payload_pointer),this_chunk_header | 1);
            PUT(FTRP(payload_pointer),this_chunk_header | 1);
            PUT(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)),next_chunk_header | 2);
            break;
        case STATUS_FREED:
            PUT(HDRP(payload_pointer),this_chunk_header | 0);
            PUT(FTRP(payload_pointer),this_chunk_header | 0);
            PUT(HDRP(NEXT_BLOCK_PAYLOAD(payload_pointer)),next_chunk_header | 0);
            break;
        default:
            break;
    }
}
