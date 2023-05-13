#include <stdio.h>
#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

typedef union {
  int32_t i[2];
  double d;
} dbl;

typedef union {
  int32_t i;
  float d;
} dbl2;

value gethi(value v) {
  dbl d;
  d.d = Double_val(v);
  return copy_int32(d.i[0]);
}

value getlo(value v) {
  dbl d;
  d.d = Double_val(v);
  return copy_int32(d.i[1]);
}

value get_upper(value v){
  dbl2 d;
  d.d = Double_val(v);
  return copy_int32((d.i >> 12) + ((d.i & 0x800) >> 11));
}

value get_lower(value v){
  dbl2 d;
  d.d = Double_val(v);
  return copy_int32((d.i << 20) >> 20);
}