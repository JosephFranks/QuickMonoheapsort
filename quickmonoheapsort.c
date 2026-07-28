/*
  Copyright (C) 2026 Joe Franks
  
  This file contains code derived from the GNU C Library.
  
  This program/library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public License 
  as published by the Free Software Foundation; either version 2.1 
  of the License, or (at your option) any later version.
*/

/* 
   Copyright (C) 1991-2019 Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Written by Douglas C. Schmidt (schmidt@ics.uci.edu).

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

/* If you consider tuning this algorithm, you should consult first:
   Engineering a sort function; Jon Bentley and M. Douglas McIlroy;
   Software - Practice and Experience; Vol. 23 (11), 1249-1265, 1993.  */
	
#include <alloca.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <sys/time.h>
	
/* Byte-wise swap two items of size SIZE. */
#define SWAP(a, b, size)                                                      \
  do                                                                              \
	  {                                                                              \
      size_t __size = (size);                                                      \
      char *__a = (a), *__b = (b);                                              \
      do                                                                      \
        {                                                                      \
          char __tmp = *__a;                                                      \
          *__a++ = *__b;                                                      \
          *__b++ = __tmp;                                                      \
        } while (--__size > 0);                                                      \
    } while (0)

#define MOVE(from, to, size)                                                      \
  do                                                                              \
    {                                                                              \
      size_t __size = (size);                                                      \
      char *__from = (from), *__to = (to);                                              \
      do                                                                      \
        {                                                                     \
          *__to++ = *__from++;                                                    \
        } while (--__size > 0);                                                      \
    } while (0)

static char TMP[sizeof(char)*sizeof(size_t)*2];
static char* TMP_SWAP_SPACE;
static int NUM_CMPS;
static int NUM_MOVES;
	
/* Discontinue quicksort algorithm when partition gets below this size.
   This particular magic number was chosen to work best on a Sun 4/260. */
#define MAX_THRESH 24
#define HEAP_THRESH 16383//63//127//255//511//1023//2047//4095//8191//16383//32767
#define SIZE  1048576//2048//4096//8192//16384//32768//65536//131072//262144//524288//16777216//1000000//1048576//2097152//16777216

/* Stack node declarations used to store unfulfilled partition obligations. */
typedef struct
  {
    char *lo;
    char *hi;
  } stack_node;

/* The next 4 #defines implement a very fast in-line stack abstraction. */
/* The stack needs log (total_elements) entries (we could even subtract
   log(MAX_THRESH)).  Since total_elements has type size_t, we get as
   upper bound for log (total_elements):
   bits per byte (CHAR_BIT) * sizeof(size_t).  */
#define STACK_SIZE        (CHAR_BIT * sizeof (size_t))
#define PUSH(low, high)        ((void) ((top->lo = (low)), (top->hi = (high)), ++top))
#define        POP(low, high)        ((void) (--top, (low = top->lo), (high = top->hi)))
#define        STACK_NOT_EMPTY        (stack < top)

static inline void monoheapsort (void* const data,
                    size_t total_elems,
                    size_t heap_size,
                    size_t size,
                    int (*cmp)(const void*, const void*));

static inline void sift_down (
        void* const heap_start,
        size_t total_elems,
        size_t value_index,
        size_t size, 
        int (*cmp)(const void*, const void*));

static inline void sift_down_floyd (
        void* const heap_start,
        size_t const total_elems,
        size_t const value_index,
        size_t const size, 
        char* const tmp,
        int (*cmp)(const void*, const void*));

/* Order size using quicksort.  This implementation incorporates
   four optimizations discussed in Sedgewick:

   1. Non-recursive, using an explicit stack of pointer that store the
      next array partition to sort.  To save time, this maximum amount
      of space required to store an array of SIZE_MAX is allocated on the
      stack.  Assuming a 32-bit (64 bit) integer for size_t, this needs
      only 32 * sizeof(stack_node) == 256 bytes (for 64 bit: 1024 bytes).
      Pretty cheap, actually.

   2. Chose the pivot element using a median-of-three decision tree.
      This reduces the probability of selecting a bad pivot value and
      eliminates certain extraneous comparisons.

   3. Only quicksorts TOTAL_ELEMS / MAX_THRESH partitions, leaving
      insertion sort to order the MAX_THRESH items within each partition.
      This is a big win, since insertion sort is faster for small, mostly
      sorted array segments.

   4. The larger of the two sub-partitions is always pushed onto the
      stack first, with the algorithm then concentrating on the
      smaller partition.  This *guarantees* no more than log (total_elems)
      stack size is needed (actually O(1) in this case)!  */

void _quicksort (void *const pbase, size_t total_elems, size_t size, int (*cmp)(const void*, const void*)) {
  char *base_ptr = (char *) pbase;

  const size_t max_thresh = MAX_THRESH * size;

  if (total_elems == 0)
    /* Avoid lossage with unsigned arithmetic below.  */
    return;

  if (total_elems > MAX_THRESH) {
    char *lo = base_ptr;
    char *hi = &lo[size * (total_elems - 1)];
    stack_node stack[STACK_SIZE];
    stack_node *top = stack;

    PUSH (NULL, NULL);

    while (STACK_NOT_EMPTY) {
        char *left_ptr;
        char *right_ptr;

        /* Select median value from among LO, MID, and HI. Rearrange
           LO and HI so the three values are sorted. This lowers the
           probability of picking a pathological pivot value and
           skips a comparison for both the LEFT_PTR and RIGHT_PTR in
           the while loops. */

        char *mid = lo + size * ((hi - lo) / size >> 1);

        if ((*cmp) ((void *) mid, (void *) lo) < 0) {
          SWAP (mid, lo, size);
          //NUM_MOVES += 3;
        }
        //NUM_CMPS++;
        //NUM_CMPS++;
        if ((*cmp) ((void *) hi, (void *) mid) < 0) {
          SWAP (mid, hi, size);
          //NUM_MOVES += 3;
        } else {
          goto jump_over;
        }
        if ((*cmp) ((void *) mid, (void *) lo) < 0) {
          SWAP (mid, lo, size);
          //NUM_MOVES += 3;
          //NUM_CMPS++;
        }
      jump_over:;

        left_ptr  = lo + size;
        right_ptr = hi - size;

        /* Here's the famous ``collapse the walls'' section of quicksort.
           Gotta like those tight inner loops!  They are the main reason
           that this algorithm runs much faster than others. */
        do
          {
            while ((*cmp) ((void *) left_ptr, (void *) mid) < 0) {
              left_ptr += size;
              //NUM_CMPS++;
            }
            //NUM_CMPS++;

            while ((*cmp) ((void *) mid, (void *) right_ptr) < 0) {
              right_ptr -= size;
              //NUM_CMPS++;
            }
            //NUM_CMPS++;

            if (left_ptr < right_ptr)
              {
                SWAP (left_ptr, right_ptr, size);
                //NUM_MOVES += 3;
                if (mid == left_ptr)
                  mid = right_ptr;
                else if (mid == right_ptr)
                  mid = left_ptr;
                left_ptr += size;
                right_ptr -= size;
              }
            else if (left_ptr == right_ptr)
              {
                left_ptr += size;
                right_ptr -= size;
                break;
              }
          }
        while (left_ptr <= right_ptr);

        /* Set up pointers for next iteration.  First determine whether
           left and right partitions are below the threshold size.  If so,
           ignore one or both.  Otherwise, push the larger partition's
           bounds on the stack and continue sorting the smaller one. */

        if ((size_t) (right_ptr - lo) < max_thresh)
          {
            if ((size_t) (hi - left_ptr) < max_thresh)
              /* Ignore both small partitions. */
              POP (lo, hi);
            else
              /* Ignore small left partition. */
              lo = left_ptr;
          }
        else if ((size_t) (hi - left_ptr) < max_thresh)
          /* Ignore small right partition. */
          hi = right_ptr;
        else if ((right_ptr - lo) > (hi - left_ptr))
          {
            /* Push larger left partition indices. */
            PUSH (lo, right_ptr);
            lo = left_ptr;
          }
        else
          {
            /* Push larger right partition indices. */
            PUSH (left_ptr, hi);
            hi = right_ptr;
          }
      }
  }

  /* Once the BASE_PTR array is partially sorted by quicksort the rest
     is completely sorted using insertion sort, since this is efficient
     for partitions below MAX_THRESH size. BASE_PTR points to the beginning
     of the array to sort, and END_PTR points at the very last element in
     the array (*not* one beyond it!). */

  #define min(x, y) ((x) < (y) ? (x) : (y))

  {
    char *const end_ptr = &base_ptr[size * (total_elems - 1)];
    char *tmp_ptr = base_ptr;
    char *thresh = min(end_ptr, base_ptr + max_thresh);
    char *run_ptr;

    /* Find smallest element in first threshold and place it at the
       array's beginning.  This is the smallest array element,
       and the operation speeds up insertion sort's inner loop. */

    for (run_ptr = tmp_ptr + size; run_ptr <= thresh; run_ptr += size) {
      if ((*cmp) ((void *) run_ptr, (void *) tmp_ptr) < 0) {
        tmp_ptr = run_ptr;
      }
      //NUM_CMPS++;
    }

    if (tmp_ptr != base_ptr) {
      SWAP (tmp_ptr, base_ptr, size);
      //NUM_MOVES += 3;
    }

    /* Insertion sort, running from left-hand-side up to right-hand-side.  */

    run_ptr = base_ptr + size;
    while ((run_ptr += size) <= end_ptr)
      {
        tmp_ptr = run_ptr - size;
        while ((*cmp) ((void *) run_ptr, (void *) tmp_ptr) < 0) {
          tmp_ptr -= size;
          //NUM_CMPS++;
        }
        //NUM_CMPS++;

        tmp_ptr += size;
        if (tmp_ptr != run_ptr) {
            char *trav;

            trav = run_ptr + size;
            while (--trav >= run_ptr) {
                char c = *trav;
                char *hi, *lo;

                for (hi = lo = trav; (lo -= size) >= tmp_ptr; hi = lo)
                  *hi = *lo;
                *hi = c;
                //NUM_MOVES++;
            }
        }
      }
  }
}

// This is a single heap variant of the QuickHeapsort algorithm.  The steps are as follows:
//  1. Use a standard quicksort to divide the array into partitions of max size HEAP_THRESH.
//  2. Shift all elements in the array such that the bottom HEAP_THRESH elements become
//     the elements at the start of the array.  This will become our monoheap.
//  3. Heapify the first HEAP_THRESH elements of the array to create a max binary heap.
//  4. Perform heap sort with Floyd's optimization.  For each root element of the heap,
//     swap it with the last element of the unsorted portion of the array.  After shifting
//     elements of the heap up, sift the new element up from the bottom. (1.33n avg case 
//     comparisons where n is HEAP_THRESH due to partitioned nature of the heap).
//  5. When the heap is the only remaining unsorted portion of the array, fall back on
//     standard heapsort to finish sorting.
void quickmonoheapsort (void *const pbase, size_t total_elems, size_t size, int (*cmp)(const void*, const void*)) {
  char *base_ptr = (char *) pbase;

  const size_t max_thresh = HEAP_THRESH * size;

  if (total_elems == 0) {
    /* Avoid lossage with unsigned arithmetic below.  */
    return;
  }
  
  if (total_elems > HEAP_THRESH) {
    char *lo = base_ptr;
    char *hi = &lo[size * (total_elems - 1)];
    stack_node stack[STACK_SIZE];
    stack_node *top = stack;

    PUSH (NULL, NULL);

    while (STACK_NOT_EMPTY) {
      char *left_ptr;
      char *right_ptr;

      /* Select median value from among LO, MID, and HI. Rearrange
         LO and HI so the three values are sorted. This lowers the
         probability of picking a pathological pivot value and
         skips a comparison for both the LEFT_PTR and RIGHT_PTR in
         the while loops. */

      char *mid = lo + size * ((hi - lo) / size >> 1);

      if ((*cmp) ((void *) mid, (void *) lo) >= 0) {
        SWAP (mid, lo, size);
        //NUM_MOVES += 3;
      }
      //NUM_CMPS++;
      //NUM_CMPS++;
      if ((*cmp) ((void *) hi, (void *) mid) >= 0) {
        SWAP (mid, hi, size);
        //NUM_MOVES += 3;
      } else {
        goto jump_over;
      }
      if ((*cmp) ((void *) mid, (void *) lo) >= 0) {
        SWAP (mid, lo, size);
        //NUM_MOVES += 3;
      }
      //NUM_CMPS++;
      jump_over:;

      left_ptr  = lo + size;
      right_ptr = hi - size;

      /* Here's the famous ``collapse the walls'' section of quicksort.
         Gotta like those tight inner loops!  They are the main reason
         that this algorithm runs much faster than others. */
      do
        {
          while ((*cmp) ((void *) left_ptr, (void *) mid) >= 0) {
            left_ptr += size;
            //NUM_CMPS++;
          }
          //NUM_CMPS++;

          while ((*cmp) ((void *) mid, (void *) right_ptr) >= 0) {
            right_ptr -= size;
            //NUM_CMPS++;
          }
          //NUM_CMPS++;

          if (left_ptr < right_ptr)
            {
              SWAP (left_ptr, right_ptr, size);
              //NUM_MOVES += 3;
              if (mid == left_ptr)
                mid = right_ptr;
              else if (mid == right_ptr)
                mid = left_ptr;
              left_ptr += size;
              right_ptr -= size;
            }
          else if (left_ptr == right_ptr)
            {
              left_ptr += size;
              right_ptr -= size;
              break;
            }
        }
      while (left_ptr <= right_ptr);

      /* Set up pointers for next iteration.  First determine whether
         left and right partitions are below the threshold size.  If so,
         ignore one or both.  Otherwise, push the larger partition's
         bounds on the stack and continue sorting the smaller one. */

      if ((size_t) (right_ptr - lo) <= max_thresh)
        {
          if ((size_t) (hi - left_ptr) <= max_thresh) {
            /* Ignore both small partitions. */
            //printf("left: %d, right: %d\n", (right_ptr - lo)/size, (hi - left_ptr)/size);
            POP (lo, hi);
          }
          else {
            /* Ignore small left partition. */
            //printf("left: %d\n", (right_ptr - lo)/size);
            lo = left_ptr;
          }
        }
      else if ((size_t) (hi - left_ptr) <= max_thresh) {
        /* Ignore small right partition. */
        //printf("right: %d\n", (hi - left_ptr)/size);
        hi = right_ptr;
      }
      else if ((right_ptr - lo) > (hi - left_ptr))
        {
          /* Push larger left partition indices. */
          PUSH (lo, right_ptr);
          lo = left_ptr;
        }
      else
        {
          /* Push larger right partition indices. */
          PUSH (left_ptr, hi);
          hi = right_ptr;
        }
    }
  }
  
  //printf("QUICKSORT PORTION: # SWAPS: %d, # CMPS: %d\n", NUM_MOVES, NUM_CMPS);
  monoheapsort(pbase, total_elems, HEAP_THRESH, size, cmp);
}

int cmpfunc (const void * a, const void * b) {
   const u_int64_t __a = *((const u_int64_t*)a);
   const u_int64_t __b = *((const  u_int64_t*)b);
   if (__a > __b) {
     return 1;
   } else {
     if (__b > __a) {
       return -1;
     }
     return 0;
   }
}

int cmpfuncInt (const void * a, const void * b) {
  return (*((const int*)a) - *((const int*)b));
  // int val_a = *(const int *)a;
  // int val_b = *(const int *)b;
  // if (val_a < val_b) return -1;
  // if (val_a > val_b) return 1;
  // return 0;
}

// int cmpfuncInt (const void * a, const void * b) {
//   int val_a = *(const int *)a;
//   int val_b = *(const int *)b;
  
//   // Artificially expensive CPU work: 100x100 matrix multiplication
//   int sum = 0;
//   int matrix_size = 10;
//   int matA[matrix_size][matrix_size], matB[matrix_size][matrix_size], matC[matrix_size][matrix_size];
  
//   for (int i = 0; i < matrix_size; i++) {
//       for (int j = 0; j < matrix_size; j++) {
//           matC[i][j] = 0;
//           for (int k = 0; k < matrix_size; k++) {
//               matC[i][j] += matA[i][k] * matB[k][j];
//           }
//           sum += matC[i][j]; // Prevent the compiler from optimizing out the loop
//       }
//   }

//   // if (val_a < val_b) return -1;
//   // if (val_a > val_b) return 1;
//   // return 0;
//   return (*((const int*)a) - *((const int*)b));
// }

static inline void monoheapsort (void* const data,   // Array to be sorted
                    size_t total_elems,
                    size_t heap_size,
                    size_t size,
                    int (*cmp)(const void*, const void*))         // Size of the array
{
    char* base_ptr = (char*)data;
    char* H = (char*)(data - size);
    size_t i;       
       
    TMP_SWAP_SPACE = TMP;
    
    char* lead_ptr = (char*)(data + (size * (heap_size - 1)));
    char* trailing_ptr = (char*)(data + (size * (total_elems - 1)));

    // Shift all elements of the array such that the bottom (greatest) heap_size elements
    // occupy the first 0 to heap_size - 1 slots of the array.  This will become the heap
    // that we construct once and maintain through the remainder of the sorting process.
    //
    // The quicksort performed previously reverses the comparison operator.  Thus, our
    // partitions are also reverse sorted (partition with greatest elements is at the
    // start of the array and the partition with the smallest elements is at the end of
    // the array).  The first heap_size elements of the array will become our cache
    // resident heap.  In order to feed elements from the next greatest partition
    // outside of the heap into the heap, we need to reverse the elements in the array
    // outside of the heap. 
    //
    // We could also achieve this without the necessity for the loop below by using some 
    // tricks during the quicksort phase, but I doubt that it would increase performance
    // due to increased bookkeeping cost.  I feel like it's more likely it would hinder 
    // performance given how highly optimized a normal array reversal is under the hood, 
    // but still may be worth investigating.  Perhaps there's some particularly clever 
    // trick that could be leveraged.
    //
    // Best I can come up with atm is don't reverse the operator during quicksort, but
    // instead of always choosing the smaller of the two paritions to perform the next
    // quicksort iteration on, choose the partition with the greater elements until the
    // two partitions with greatest elements are found.  Swap heap_size elements at the
    // start and end of the array.  Next, continue heapsort as normal, but with two
    // additional swap pointers pointing towards the swapped area at the end of the array.  
    // Instead of swapping elements withing the currently being sorted partition, you 
    // allow the swapped area to bubble up until it's in the correct place in the array.

    // To save n-2 element moves, where n is the size of the array, before we reverse
    // the partitions outside the heap area, we pluck an element from the parition of
    // least elements.  This allows us to skip the last move of moving the next greatest
    // element into the root of the heap.  The element we pluck is reinserted into the
    // heap before the final partition is sorted.

    // MOVE(trailing_ptr, TMP_SWAP_SPACE + size, size);
    // trailing_ptr -= size;
    // while(trailing_ptr > lead_ptr) {
    //   SWAP(lead_ptr, trailing_ptr, size);
    //   trailing_ptr -= size;
    //   lead_ptr += size;
    // }

    // Same as above, but with MOVEs instead of SWAPs.
    // Pluck the element to save MOVEs.
    MOVE(trailing_ptr, TMP_SWAP_SPACE + size, size);
    trailing_ptr -= size;
    // Reverse partitions outside heap area
    MOVE(trailing_ptr, TMP_SWAP_SPACE, size);
    while(trailing_ptr > lead_ptr) {
      MOVE(lead_ptr, trailing_ptr, size);
      trailing_ptr -= size;
      MOVE(trailing_ptr, lead_ptr, size);
      lead_ptr += size;
    }
    MOVE(TMP_SWAP_SPACE, lead_ptr, size);

    lead_ptr = (char*)(data + (size * (total_elems - heap_size - 1)));

    // Heapify the first heap_size elements of the array.
    // TODO: Can save on some comparisons if we know the size of the partitions
    for (i=(heap_size) >> 1; i; i--) {
      sift_down(H, heap_size, i, size, cmp);
    }

    // This is the main loop.  We perform heapsort here by using our heap_size
    // heap at the beginning of the array.  The element at the top of the heap is 
    // swapped with the next element of the bottom, unsorted array.  This new 
    // element is guaranteed to be from a partition lesser than the one currently 
    // being sorted.  As such, inserting this element into the heap takes around 
    // 2n comparisons in the worst case, but only around 1.33n comparisons in the 
    // average case, where n is the size of the heap.
    //
    // Thus, maintaining the heap like this beats calling heapify on each heap
    // of size n in the average case (around 1.88n comparisons) and matches it
    // in the worst case.  However, standard QuickHeapsort has the advantage of
    // never sifting up new elements at all, which saves n comparisons.
    // It also has the advantage that each heap size is exactly the parition size. 
    // In QuickMonoheapsort, the heap size is static, regardless of the size of
    // the parition currently being sorted.
    //
    // Overall, QuickMonoheapsort performs slightly more comparisons than standard
    // QuickHeapsort.  However, this tradeoff seems worthwhile due to improved
    // cache usage (at least, that's what I hope).
    //
    // TODO: See if the number of moves saved by buffering pops is helpful.
    lead_ptr = (char*)(data + (size * (heap_size - 1)));
    trailing_ptr = (char*)(data + (size * (total_elems - 1)));
    char* heap_ptr = H + size;

    MOVE(heap_ptr, trailing_ptr, size);
    trailing_ptr -= size;
    size_t next;
    while (trailing_ptr > lead_ptr) {
      MOVE(trailing_ptr, heap_ptr, size);
      
      // next = (*cmp)((void*)&H[2 * size], (void*)&H[3 * size]) < 0
      //   ? 3
      //   : 2;
      next = 2;
      if ((*cmp)((void*)&H[2 * size], (void*)&H[3 * size]) < 0) {
        next++;
      }
      // NUM_CMPS++;
      MOVE(&H[next * size], trailing_ptr, size);
      trailing_ptr -= size;
      //NUM_MOVES++;
      //NUM_MOVES++;
      
      sift_down_floyd(H, heap_size, next, size, heap_ptr, cmp);
    }
    

    size_t lastIndex = heap_size;
    
    // Move the element we plucked out earlier back into the heap.
    MOVE(TMP_SWAP_SPACE + size, TMP_SWAP_SPACE, size);
    // NUM_MOVES++;
    sift_down_floyd(H, lastIndex, 1, size, TMP_SWAP_SPACE, cmp);

    // Finally, fall back on standard heapsort for the final heap_size elements.
    while (trailing_ptr > base_ptr) {
      MOVE(&H[lastIndex * size], TMP_SWAP_SPACE, size);
      MOVE(heap_ptr, trailing_ptr, size);
      //NUM_MOVES++;     
      //NUM_MOVES++;

      lastIndex--;
      
      sift_down_floyd(H, lastIndex, 1, size, TMP_SWAP_SPACE, cmp);
      trailing_ptr -= size; 
    }
    
    SWAP(base_ptr, trailing_ptr, size);
    //NUM_MOVES++;
    //free(TMP_SWAP_SPACE);
}
static inline void sift_down (
        void* const heap_start,
        size_t const total_elems,
        size_t const value_index,
        size_t const size, 
        int (*cmp)(const void*, const void*)
) {    
  char* tmp = TMP_SWAP_SPACE;
  char* heap = (char*)heap_start;
  size_t p;
  size_t c;
  
  MOVE(&heap[value_index * size], tmp, size);
  //NUM_MOVES++;

  p = value_index;
  
  for (c = p << 1; c < total_elems + 1; c <<= 1) {
    //printf("p: %d c: %d\n", p, c);
    // if (c + 1 <= total_elems) {
    //   NUM_CMPS++;
    // }
    if (c + 1 <= total_elems && (*cmp)((void*)&heap[c * size], (void*)&heap[(c + 1) * size]) < 0) {
      c++;
    }
    
    //NUM_CMPS++;
    if ((*cmp) ((void*)&heap[c * size], (void*)tmp) <= 0) {
      break;
    }

    MOVE(&heap[c * size], &heap[p * size], size);
    //NUM_MOVES++;
    
    p = c;                   // go down
  }

  MOVE(tmp, &heap[p * size], size);
  //NUM_MOVES++;
}

static inline void sift_down_floyd (
        void* const heap_start,
        size_t const total_elems,
        size_t const value_index,
        size_t const size, 
        char* const tmp,
        int (*cmp)(const void*, const void*)
) {    
    char* heap = (char*)heap_start;
    size_t p = value_index;
    size_t c;        
    
    for (c = p << 1; c < total_elems + 1; c <<= 1) {
      // if (c + 1 <= total_elems) {
      //   NUM_CMPS++;
      // }
      if (c + 1 <= total_elems && (*cmp)((void*)&heap[c * size], (void*)&heap[(c + 1) * size]) < 0) {
        c++;
      }

      MOVE(&heap[c * size], &heap[p * size], size);
      //NUM_MOVES++;
      
      p = c;                   // go down
    }
    
    // This is some crazy ass optimization where if your heap is imperfect s.t. the last element is the 
    // only child of the parent, you don't have to do the c + 1 <= total_elems check above.  I seemed
    // to think it was worthwhile at some point, but it's highly doubtful. 
    // if (c == total_elems) {// && (*cmp)((void*)&heap[c * size], (void*)tmp) > 0) { 
    //   MOVE(&heap[c * size], &heap[p * size], size);
    //   NUM_MOVES++;
    //   //printf("MOVING [%d] %llu TO [%d] %llu\n", c, *(u_int64_t*)&heap[c * size], p, *(u_int64_t*)&heap[p * size]);
    //   p = c;
    //   //swap_occured = true;
    // }

    c = p;
    //NUM_CMPS++;

    // Sift the new element back up.
    // This conditional may save a MOVE since the leaf hasn't been overwritten yet.
    if ((*cmp) ((void*)&heap[p * size], (void*)tmp) < 0) {
      p >>= 1;
      c = p;

      while ((*cmp) ((void*)&heap[p * size], (void*)tmp) < 0) {
        c = p;
        p >>= 1;
        
        if (p == 0) {
          break;
        }

        MOVE(&heap[p * size], &heap[c * size], size);
        //printf("p: %d\n", *(int*)&heap[p*size]);
        //NUM_CMPS++;
        //NUM_MOVES++;
      }
    }
    

    MOVE(tmp, &heap[c * size], size);
    //NUM_MOVES++;
}

void main()
{
  // u_int64_t *data = (u_int64_t*) malloc(SIZE*sizeof(u_int64_t));
  // u_int64_t *data2 = (u_int64_t*) malloc(SIZE*sizeof(u_int64_t));
  int *data = (int*) malloc(SIZE*sizeof(int));
  int *data2 = (int*) malloc(SIZE*sizeof(int));
  size_t data_size = sizeof(int);
  int x;
  int i;
  srand(time(NULL));
  
  for (x = 0; x < SIZE; x++)
  {
    data[x] = x + 1;//rand() % SIZE;
    //data2[x] = data[x];
  }
  
  int value;
  for (x = SIZE - 1; x > 0; x--) {
   value = rand() % x;
   SWAP((char*)&data[x], (char*)&data[value], sizeof(int));
   data2[x] = data[x];
   data2[value] = data[value];
  }

  NUM_CMPS = 0;
  NUM_MOVES = 0;
  
  struct timespec tv;
  clock_gettime(CLOCK_MONOTONIC, &tv);
  u_int64_t start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;
  
  qsort(data, SIZE, data_size, cmpfuncInt);
  //_quicksort(data, SIZE, data_size, cmpfuncInt);

  clock_gettime(CLOCK_MONOTONIC, &tv);
  u_int64_t finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;
  
  printf("Qsort Pass 1 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);
  for (x = 0; x < SIZE; x++)
  {
    data[x] = data2[x];
  }
  NUM_CMPS = 0;
  NUM_MOVES = 0;

  clock_gettime(CLOCK_MONOTONIC, &tv);
  start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  //_quicksort(data, SIZE, data_size, cmpfuncInt);
  qsort(data, SIZE, data_size, cmpfuncInt);
  clock_gettime(CLOCK_MONOTONIC, &tv);
  finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  printf("Qsort Pass 2 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);
  for (x = 0; x < SIZE; x++)
  {
    data[x] = data2[x];
  }
  NUM_CMPS = 0;
  NUM_MOVES = 0;

  clock_gettime(CLOCK_MONOTONIC, &tv);
  start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  _quicksort(data, SIZE, data_size, cmpfuncInt);
  //qsort(data, SIZE, data_size, cmpfuncInt);
  clock_gettime(CLOCK_MONOTONIC, &tv);
  finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  printf("Quicksort Pass 1 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);

  for (x = 0; x < SIZE; x++)
  {
    data[x] = data2[x];
  }
  NUM_CMPS = 0;
  NUM_MOVES = 0;

  clock_gettime(CLOCK_MONOTONIC, &tv);
  start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  _quicksort(data, SIZE, data_size, cmpfuncInt);
  //qsort(data, SIZE, data_size, cmpfuncInt);
  clock_gettime(CLOCK_MONOTONIC, &tv);
  finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  printf("Quicksort Pass 2 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);

  // qsort(data3, SIZE, sizeof(u_int64_t), cmpfunc);
  for (x = 0; x < SIZE; x++)
  {
    data[x] = data2[x];
  }
  NUM_CMPS = 0;
  NUM_MOVES = 0;

  clock_gettime(CLOCK_MONOTONIC, &tv);
  start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;
 
  quickmonoheapsort(data, SIZE, data_size, cmpfuncInt);
  
  clock_gettime(CLOCK_MONOTONIC, &tv);
  finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;
  printf("Quickmonoheapsort Pass 1 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);

  for (x = 0; x < SIZE; x++)
  {
    data[x] = data2[x];
  }
  NUM_CMPS = 0;
  NUM_MOVES = 0;
  
  clock_gettime(CLOCK_MONOTONIC, &tv);
  start = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;
  
  //quickmonoheapsort(data, SIZE, data_size, cmpfuncInt);
  quickmonoheapsort(data, SIZE, data_size, cmpfuncInt);
  clock_gettime(CLOCK_MONOTONIC, &tv);
  finish = (u_int64_t)tv.tv_sec*1000000+(u_int64_t)(tv.tv_nsec)/1000;

  printf("Quickmonoheapsort Pass 2 time in nanoseconds: %llu, # SWAPS: %d, # CMPS: %d\n", finish-start, NUM_MOVES, NUM_CMPS);
  int num_bad = 0;
  for (x = 0; x < SIZE; x++) {
    //printf("%d: %llu\n",x, data[x]);
    if (data[x] != x + 1) {  
      num_bad++;
      //printf("BAD\n");
      //printf("BAD: %d: %llu, %d: %llu, %d: %llu\n", x-1, data[x-1], x, data[x], x+1, data[x+1]);
    }
  }
  printf("num bad: %d\n", num_bad);
  
  free(data);
  free(data2);
}

