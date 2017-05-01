#include <stdbool.h>

void write_labeled_val(int v, bool b, int* highptr, int* lowptr) {
  if (b) {
    *highptr = v;
  } else {
    *lowptr = v;
  }
}

int main() {
  int high, low;
  write_labeled_val(1, true, &high, &low);
  write_labeled_val(2, false, &high, &low);
  return high + low;
}

