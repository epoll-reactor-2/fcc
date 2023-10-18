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
//      19:   jmp L0
//      37:   t3 = t3(@noalias) + 1(@loop)
//      38:   jmp L8
//      39:   ret 0
int main() {
    // Dead instruction at 20
    // Dead instruction at 21
    // Dead instruction at 22
    // Dead instruction at 23
    // Dead instruction at 24
    // Dead instruction at 25
    // Dead instruction at 26
    // Dead instruction at 27
    // Dead instruction at 28
    // Dead instruction at 29
    // Dead instruction at 30
    // Dead instruction at 31
    // Dead instruction at 32
    // Dead instruction at 33
    // Dead instruction at 34
    // Dead instruction at 35
    // Dead instruction at 36

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
    
    return 0;
}