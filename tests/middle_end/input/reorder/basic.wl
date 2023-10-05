//fun main():
//       0:   int t0
//       4:   int t2
//       5:   int t3
//       6:   int t4
//       9:   int t5
//       2:   int t1
//       1:   t0 = 1
//       3:   t1 = 2
//       7:   t4 = t1 * 2
//       8:   t3 = t0 + t4
//      10:   t5 = 3 + 4
//      11:   t2 = t3 << t5
//      12:   ret t2
int main() {
    int a = 1;
    int b = 2;
    return a + b * 2 << 3 + 4;
}