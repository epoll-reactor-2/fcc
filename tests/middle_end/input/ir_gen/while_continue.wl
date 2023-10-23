//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   | int t3(@loop)
//       7:   | int t4(@loop)
//       8:   | t4 = t1 + t2(@loop)
//       9:   | t3 = t0 + t4(@loop)
//      10:   | if t3 != 0 goto L12
//      11:   | jmp L28
//      12:   | t0 = t0(@noalias) + 1
//      13:   | t1 = t1(@noalias) + 1
//      14:   | t2 = t2(@noalias) + 1
//      15:   | int t5
//      16:   | int t6
//      17:   | t6 = t1 % 2
//      18:   | t5 = t6 == 0
//      19:   | if t5 != 0 goto L21
//      20:   | jmp L23
//      21:   | t2 = t2(@noalias) + 1
//      22:   | jmp L24
//      23:   | jmp L6
//      24:   | t0 = t0(@noalias) - 1
//      25:   | t1 = t1(@noalias) - 1
//      26:   | t2 = t2(@noalias) - 1
//      27:   | jmp L6
//      28:   ret 0
int main() {
    int a = 1;
    int b = a;
    int c = b;

    while (a + b + c) {
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
    }

    return 0;
}