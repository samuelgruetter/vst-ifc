#include <stdbool.h>

int sum_cl_array(int a[], bool isPublic[], int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    if (isPublic[i]) {
      int v = a[i];
      sum += v;
    }
  }
  return sum;
}

int four[4] = {1,2,3,4};

bool cl[4] = {true, false, true, true};

int main(void) {
  int s;
  s = sum_cl_array(four, cl, 4);
  return s;
}

