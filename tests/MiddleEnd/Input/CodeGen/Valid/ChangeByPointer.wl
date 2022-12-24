// 123
void change(int *ptr) {
  *ptr = 123;
}

int main() {
   int mem = 0;
   change(&mem);
   return mem;
}
