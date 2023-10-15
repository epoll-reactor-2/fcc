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
//       9:   int t5
//      10:   int t6
//      11:   t6 = t1 + t2
//      12:   t5 = t0 + t6
//      13:   t4 = t3 < t5
//      14:   if t4 != 0 goto L16
//      15:   jmp L33
//      16:   t0 = t0(@noalias) + 1
//      17:   t1 = t1(@noalias) + 1
//      18:   t2 = t2(@noalias) + 1
//      19:   int t7
//      20:   int t8
//      21:   t8 = t3 % 2
//      22:   t7 = t8 == 0
//      23:   if t7 != 0 goto L25
//      24:   jmp L27
//      25:   t3 = t3(@noalias) + 1
//      26:   jmp L28
//      27:   jmp L8
//      28:   t0 = t0(@noalias) - 1
//      29:   t1 = t1(@noalias) - 1
//      30:   t2 = t2(@noalias) - 1
//      31:   t3 = t3(@noalias) + 1(@loop)
//      32:   jmp L8
//      33:   ret 0
int main() {
    int a = 1;
    int b = a;
    int c = b;

    for (int i = 0; i < a + b + c; ++i) {
        ++a;
        ++b;
        ++c;
        if (i % 2 == 0) {
            ++i;
        } else {
            continue;
        }
        --a;
        --b;
        --c;
    }

    return 0;
}