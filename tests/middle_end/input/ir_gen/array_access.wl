//fun main():
//       0:   int t0[2]
//       1:   int * t1
//       2:   t1 = t0 + 0
//       3:   *t1 = 1
//       4:   int * t2
//       5:   t2 = t0 + 1
//       6:   *t2 = 0
//       7:   int t3
//       8:   int * t4
//       9:   t4 = t0 + 0
//      10:   int * t5
//      11:   t5 = t0 + 1
//      12:   t3 = *t4 + *t5
//      13:   ret t3
int main() {
    int mem_1[2];
    mem_1[0] = 1;
    mem_1[1] = 0;
    return mem_1[0] + mem_1[1];
}