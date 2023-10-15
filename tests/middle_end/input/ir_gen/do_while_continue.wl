//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   t0 = t0(@noalias) + 1
//       7:   t1 = t1(@noalias) + 1
//       8:   t2 = t2(@noalias) + 1
//       9:   int t3
//      10:   int t4
//      11:   t4 = t1 % 2
//      12:   t3 = t4 == 0
//      13:   if t3 != 0 goto L15
//      14:   jmp L17
//      15:   t2 = t2(@noalias) + 1
//      16:   jmp L18
//      17:   jmp L6
//      18:   t0 = t0(@noalias) - 1
//      19:   t1 = t1(@noalias) - 1
//      20:   t2 = t2(@noalias) - 1
//      21:   int t5(@loop)
//      22:   int t6(@loop)
//      23:   t6 = t1 + t2(@loop)
//      24:   t5 = t0 + t6(@loop)
//      25:   if t5 != 0 goto L6
//      26:   ret 0
int main() {
    int a = 1;
    int b = a;
    int c = b;

    do {
        ++a;
        ++b;
        ++c;
        if (b % 2 == 0) {
            ++c;
        } else {
            continue;
        }
        --a;
        --b;
        --c;
    } while (a + b + c);

    return 0;
}