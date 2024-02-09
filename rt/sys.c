#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <string.h>
#include <sys/resource.h>

#include "sys.h"

#define is_tuple(val) ((val & MASK_TAG) == TUPLE_TAG)
#define is_closure(val) ((val & MASK_TAG) == CLOSURE_TAG)
#define is_forwarded(val) ((val & MASK_TAG) == FORWARD_TAG)
#define is_bool(val) ((val & MASK_TAG) == BOOL_TAG)
#define is_number(val) ((val & 0x1) == 0)

typedef int64_t Number;

int count_digits(Number n) {
  if (n == 0)
    return 1;
  int ans = 0;
  while (n > 0) {
    n /= 10;
    ans++;
  }
  return ans;
}

typedef struct {
  int size;
  i64 *data;
} Tuple;

void to_tuple(Tuple *t, i64 val) {
  // untagging
  val--;
  t->data = (i64 *)val;
  // get size
  t->size = *t->data;
  // correct data
  t->data++;
}

typedef struct {
  int argc;
  i64 *dir;
  int fsize;
  i64 *fvars;
} Closure;

void to_closure(Closure *c, i64 val) {
  // untagging
  val -= 5;
  // get adrress
  i64 *addr = (i64 *)val;
  // get argc
  c->argc = addr[0];
  // get dir  c->dir = (i64 *)addr[1];
  c->dir = (i64 *)addr[1];
  // get fsize
  c->fsize = addr[2];
  // get fvars
  c->fvars = addr + 3;
}

int get_tuple(i64 **dest, i64 src) {
  // untagging
  src--;
  // get address
  i64 *addr = (i64 *)src;
  // get size
  int size = *addr;
  // move
  *dest = addr + 1;
  return size;
}

char *get_string(i64 val) {
  if ((val & TUPLE_TAG) == 0) {
    Number n = val >> 1;
    int len = count_digits(n);
    char *str = malloc(len + 1);
    sprintf(str, "%" PRId64, n);
    return str;
  }
  i64 type = val & MASK_TAG;
  if (type == TUPLE_TAG) {
    Tuple t;
    to_tuple(&t, val);
    char *strs[t.size];
    int tsize = 4; // (tup
    for (int i = 0; i < t.size; i++) {
      char *str = get_string(t.data[i]);
      tsize += strlen(str) + 1; // ' ' + it
      strs[i] = str;
    }
    tsize++; // )
    char* str = malloc(tsize + 1);
    char* w = str;
    strcpy(str, "(tup");
    w += 4;
    for (int i = 0; i < t.size; i++) {
      *w++ = ' ';
      char* l = strs[i];
      while (*l != '\0')
        *w++ = *l++;
      free(strs[i]);
    }
    *w = ')';
    str[tsize] = '\0';
    return str;
  }
  if (type == CLOSURE_TAG) {
    Closure c;
    to_closure(&c, val);
    int len = count_digits(c.argc);
    char *str = malloc(len + 7 + 1);
    sprintf(str, "<clos:%d>", c.argc);
    return str;
  }

  if (val == B_TRUE) {
    char *str = malloc(5);
    strcpy(str, "true");
    return str;
  }

  char *str = malloc(6);
  strcpy(str, "false");
  return str;
}


void type_error(int error_code, i64 val) {
  char *str = get_string(val);
  const char *type_err_msg = "Type error: Expected %s but got %s\n";
  // i64 type = val & MASK_TAG;
  char ntype[20];
  int err = 0;

  switch (error_code) {
  case ERR_NOT_NUMBER: {
    err = !is_number(val);
    strcpy(ntype, "integer");
    break;
  }
  case ERR_NOT_TUPLE: {
    err = !is_tuple(val);
    strcpy(ntype, "tuple");
    break;
  }
  case ERR_NOT_CLOSURE: {
    err = !is_closure(val);
    strcpy(ntype, "closure");
    break;
  }
  case ERR_NOT_BOOLEAN: {
    err = !is_bool(val);
    strcpy(ntype, "boolean");
    break;
  }
  }
  if (err) {
    fprintf(stderr, type_err_msg, ntype, get_string(val));
    exit(error_code);
  }
}

void extra_error(int error_code, i64 v1, i64 v2) {
  int err = 0;
  switch (error_code) {
  case ERR_OUT_OF_BOUNDS: {
    Tuple t;
    to_tuple(&t, v1);
    Number k = v2 >> 1;
    if (t.size <= k || 0 > k) {
      fprintf(stderr, "Index out of bounds: Tried to access index %s of %s\n",
              get_string(v2), get_string(v1));
      err = 1;
    }
    break;
  }
  case ERR_ARITY_MISMATCH: {
    Closure c;
    to_closure(&c, v1);
    if (c.argc != v2) {
      fprintf(stderr,
              "Arity mismatch: closure expected %d arguments but got %" PRId64 "\n",
              c.argc, v2);
      err = 1;
    }
    break;
  }
  }

  if (err)
    exit(error_code);
}

i64 print(i64 val) {
  char *str = get_string(val);
  printf("> %s\n", str);
  free(str);
  return val;
}


/* configuration */
u64 STACK_SIZE = 0x800000;
u64 HEAP_SIZE = 16;
int USE_GC = 1;

/* GC */
u64* HEAP_START;
u64* HEAP_END;
u64* HEAP_MID;
u64* TO_SPACE;
u64* FROM_SPACE;
u64* ALLOC_PTR = 0;
u64* SCAN_PTR = 0;
u64* STACK_BOTTOM = 0;

void set_stack_bottom(u64* stack_bottom) {
  STACK_BOTTOM = stack_bottom;
}

bool is_heap_ptr(u64 val){
  return (u64*)val < HEAP_END && (u64*)val >= HEAP_START;
}

void print_stack(u64* rbp, u64* rsp) {
  printf("|------- frame %p to %p  ------\n", rsp, rbp);
  for (u64* cur_word = rsp; cur_word < rbp; cur_word++) {
    u64 val = (u64)*cur_word;
    printf("| %p: %p", cur_word, (u64*)*cur_word);
    if (is_heap_ptr(val)) {
      if (is_tuple(val)){ printf(" (tuple)"); }
      else if (is_closure(val)){ printf(" (closure)"); }
    }
    printf("\n");
  }
  if (rbp < STACK_BOTTOM) {
    print_stack((u64*)*rbp, rbp + 2);
  }
  else {
    printf("|------- bottom %p  ------\n\n", STACK_BOTTOM);
  }
}

void print_heap(u64* heap_start, u64* heap_end){
  printf("| Heap from %p to %p\n", heap_start, heap_end);
  for (u64 i = 0; i <= (u64)(heap_end - heap_start); i++) {
    printf("|  %lld/%p: %p \n", i, (heap_start + i), (u64*)*(heap_start + i));
  }
}

void print_heaps(){
  printf("|\n|=======HEAP 1==========\n");
  print_heap(HEAP_START, HEAP_MID-1);
  printf("|=======HEAP 2==========\n");
  print_heap(HEAP_MID, HEAP_END);
  printf("|=================\n\n");
}

u64 copy(u64 val) {
  u64 new_val = (u64)ALLOC_PTR;
  if (is_tuple(val)) {
    u64* val_ptr = (u64*)val;
    // printf("| Copying tuple from %p to %p\n", val_ptr, ALLOC_PTR);
    if (is_forwarded(*val_ptr)) {
      return *val_ptr;
    } 
    Tuple t;
    to_tuple(&t, val);
    *ALLOC_PTR = t.size;
    ALLOC_PTR++;
    for (int i = 0; i < t.size; i++) {
      *ALLOC_PTR = t.data[i];
      ALLOC_PTR++;
    }
    *val_ptr = new_val | FORWARD_TAG;
    new_val |= TUPLE_TAG;
  } else if (is_closure(val)) {
    u64* val_ptr = (u64*)val;
    // printf("| Copying closure from %p to %p\n", val_ptr, ALLOC_PTR);
    if (is_forwarded(*val_ptr)) {
      return *val_ptr;
    } 
    Closure c;
    to_closure(&c, val);
    *ALLOC_PTR = c.argc;
    *(ALLOC_PTR + 1) = (u64)c.dir;
    *(ALLOC_PTR + 2) = c.fsize;
    for (int i = 0; i < c.fsize; i++) {
      *(ALLOC_PTR + 3 + i) = c.fvars[i];
    }
    ALLOC_PTR += 3 + c.fsize;
    *val_ptr = new_val | FORWARD_TAG;
    new_val |= CLOSURE_TAG;
  } else {
    new_val = val;
  }
  return new_val;
}


u64* collect(u64* cur_frame, u64* cur_sp) {
  /* TBD: see https://en.wikipedia.org/wiki/Cheney%27s_algorithm */
  // swap from-space to-space
  u64* tmp = FROM_SPACE;
  FROM_SPACE = TO_SPACE;
  TO_SPACE = tmp;
  // init spaces
  ALLOC_PTR = FROM_SPACE;
  SCAN_PTR = FROM_SPACE;

  // scan stack and copy roots
  // print_stack(STACK_BOTTOM, cur_sp);
  for (u64* cur=cur_sp; cur < STACK_BOTTOM; cur++) {
    u64 val = (u64)*cur;
    if (is_heap_ptr(val)) {
      u64 new_val = copy(val);
      *cur = new_val;
    }
  }
  // scan objects in the heap
  while (SCAN_PTR < ALLOC_PTR) {
    u64 val = (u64)*SCAN_PTR;
    if (is_heap_ptr(val)) {
      u64 new_val = copy(val);
      *SCAN_PTR = new_val;
    }
    SCAN_PTR++;
  }
  // clean old space
  memset(TO_SPACE, 0, HEAP_SIZE * sizeof(u64));
  return ALLOC_PTR;
}

/* trigger GC if enabled and needed, out-of-memory error if insufficient */
u64* try_gc(u64* alloc_ptr, u64 words_needed, u64* cur_frame, u64* cur_sp) {
  // printf("| Trying to allocate %lld words in %p\n", words_needed, alloc_ptr);
  if (USE_GC==1 && alloc_ptr + words_needed > FROM_SPACE + HEAP_SIZE) {
    printf("| need memory: GC!\n");
    // print_heaps();
    alloc_ptr = collect(cur_frame, cur_sp);
    // print_heaps();
  }
  if (alloc_ptr + words_needed > FROM_SPACE + HEAP_SIZE) {
    printf("| Error: out of memory!\n\n");
    print_stack(cur_frame, cur_sp);
    print_heaps();
    exit(-1);
  }
  return alloc_ptr;
}

/* start */
int main(int argc, char** argv){

  /* stack size config */
  char* stack_size_envvar = getenv("STACK_SIZE");
  if (stack_size_envvar) STACK_SIZE = strtoull(stack_size_envvar, NULL, 0);
  printf("| Setting stack size to %" PRId64 " .\n", STACK_SIZE);
  struct rlimit limit;
  getrlimit(RLIMIT_STACK, &limit);
  limit.rlim_cur = STACK_SIZE < limit.rlim_max ? STACK_SIZE : limit.rlim_max;
  int res = setrlimit(RLIMIT_STACK, &limit);
  if (res != 0) { printf("| Setting rlimit failed...\n") ; }

  /* GC config */
  char* use_gc_envvar = getenv("USE_GC");
  if (use_gc_envvar) USE_GC = strtoull(use_gc_envvar, NULL, 0);
  printf("| Use GC: %d\n", USE_GC);

  /* heap size config */
  char* heap_size_envvar = getenv("HEAP_SIZE");
  if (heap_size_envvar) HEAP_SIZE = strtoull(heap_size_envvar, NULL, 0);
  printf("| Heap size: %" PRId64 " .\n", HEAP_SIZE);

  /* setting up two space heap for GC */
  u64* heap = (u64*)calloc((HEAP_SIZE * 2) + 15, sizeof(u64));
  HEAP_START = (u64*)(((u64)heap + 15) & ~0xF);
  /* TBD: initialize HEAP_MID, HEAP_END, FROM_SPACE, TO_SPACE */
  HEAP_MID = HEAP_START + HEAP_SIZE;   /* TBD */
  HEAP_END = HEAP_MID + HEAP_SIZE - 1;   /* TBD */
  FROM_SPACE = HEAP_START; /* TBD */
  TO_SPACE = HEAP_MID;   /* TBD */

  /* Go! */
  /* Q: when do you need to call `free(heap)`? */
  // print_heaps();
  i64 result = our_code_starts_here(HEAP_START);
  char* s = get_string(result);
  printf("%s\n", s);
  // print_heaps();
  free(s);
  free(heap);
  return 0;
}

// funciones extras (testing)
i64 max(i64 a1, i64 a2) asm("max");
i64 max(i64 a1, i64 a2) { return a1 > a2 ? a1 : a2; }

i64 long_fun(i64 a1, i64 a2, i64 a3, i64 a4, i64 a5, i64 a6, i64 a7,
             i64 a8) asm("long_fun");
i64 long_fun(i64 a1, i64 a2, i64 a3, i64 a4, i64 a5, i64 a6, i64 a7, i64 a8) {
  i64 ans = 0;
  if (a1) {
    ans += a2;
  }
  if (a3) {
    ans += a4;
  }
  if (a5) {
    ans += a6;
  }
  if (a7) {
    ans += a8;
  }
  return ans;
}
