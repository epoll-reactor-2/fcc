//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   | t0 = t0 + 1
//       7:   | t1 = t1 + 1
//       8:   | t2 = t2 + 1
//       9:   | | int t3
//      10:   | | int t4
//      11:   | | t4 = t2 % 2
//      12:   | | t3 = t4 == 0
//      13:   | | if t3 != 0 goto L15
//      14:   | | jmp L17
//      15:   | | t2 = t2 + 1
//      16:   | | jmp L18
//      17:   | | jmp L26
//      18:   | t0 = t0 - 1
//      19:   | t1 = t1 - 1
//      20:   | t2 = t2 - 1
//      21:   | int t5
//      22:   | int t6
//      23:   | t6 = t1 + t2
//      24:   | t5 = t0 + t6
//      25:   | if t5 != 0 goto L6
//      26:   ret 0
int main() {
    int a = 1;
    int b = a;
    int c = b;

    do {
        ++a;
        ++b;
        ++c;
        if (c % 2 == 0) {
            ++c;
        } else {
            break;
        }
        --a;
        --b;
        --c;
    } while (a + b + c);

    return 0;
}