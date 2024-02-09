#include <inttypes.h>
#include <stdlib.h>
typedef int64_t i64;
typedef uint64_t u64;

extern void type_error(int error_code, i64 val) asm("type_error");
extern void extra_error(int error_code, i64 v1, i64 v2) asm("extra_error");
extern i64 print(i64 val) asm("print");
extern u64* try_gc(u64* alloc_ptr, u64 words_needed, u64* cur_frame, u64* cur_sp) asm("try_gc");
extern u64 our_code_starts_here(u64* heap) asm("our_code_starts_here");
extern void set_stack_bottom(u64* stack_bottom) asm("set_stack_bottom");

const i64 MASK_TAG = 0x0000000000000007;

const i64 TUPLE_TAG = 0x0000000000000001;
const i64 FORWARD_TAG = 0x0000000000000003;
const i64 CLOSURE_TAG = 0x0000000000000005;
const i64 BOOL_TAG = 0x0000000000000007;

const i64 B_TRUE = 0xFFFFFFFFFFFFFFFF;
const i64 B_FALSE = 0x7FFFFFFFFFFFFFFF;

const int ERR_NOT_NUMBER = 1;
const int ERR_NOT_BOOLEAN = 2;
const int ERR_NOT_TUPLE = 3;
const int ERR_NOT_CLOSURE = 4;
const int ERR_OUT_OF_BOUNDS = 5;
const int ERR_ARITY_MISMATCH = 6;


