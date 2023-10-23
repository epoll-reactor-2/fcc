//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   int t3(@loop)
//       7:   t3 = 0(@loop)
//       8:   int t4
//       9:   t4 = t3 < t0
//      10:   if t4 != 0 goto L12
//      11:   jmp L39
//      12:   t0 = t0(@noalias) + 1
//      13:   int t5
//      14:   int t6
//      15:   t6 = t3 % 2
//      16:   t5 = t6 == 0
//      17:   if t5 != 0 goto L19
//      18:   jmp L37
//      19:   jmp L8
//      37:   t3 = t3(@noalias) + 1(@loop)
//      38:   jmp L8
//      39:   ret t0
int main() {
    int a = 1;
    int b = a;
    int c = b;

    for (int i = 0; i < a; ++i) {
        ++a;
        if (i % 2 == 0) {
            continue;
            while (a < b) {
                ++b;
                continue;
                --c;
                for (int j = 0; j < 1; ++j) {
                    return 1;
                }
            }
        }
    }

    return a;
}