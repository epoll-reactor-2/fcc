//fun f(int t0, int t1, int t2):
//       0:   int t3
//       1:   int t4
//       2:   int t5
//       3:   t5 = t1 + t2
//       4:   t4 = t0 + t5
//       5:   t3 = t4
//       6:   ret
//fun main():
//       0:   call f(1, 2, 3)
//       1:   ret 0
void f(int a, int b, int c) {
    int r = a + b + c;
}

int main() {
    f(1, 2, 3);
    return 0;
}