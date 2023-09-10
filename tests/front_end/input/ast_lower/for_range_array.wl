//a
int main() {
  int mem[1][2][3];
  for (int *arr1[1][2] : mem) {
    for (int *arr2[1] : arr1) {
      for (int *i : arr2) {
        *i = 666;
      }
    }
  }
}