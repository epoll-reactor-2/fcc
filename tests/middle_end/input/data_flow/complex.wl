//fun __do():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 1
//       6:   int t3
//       7:   t3 = 3
//      39:   int t10
//      40:   int t11
//      41:   t11 = t1 + t3
//      42:   t10 = t0 + t11
//      43:   ret t10
//fun __dont():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 1
//       4:   int t2
//       5:   t2 = 2
//       6:   int t3
//       7:   t3 = 3
//       8:   int t4
//       9:   t4 = 0
//      10:   | int t5
//      11:   | int t6
//      12:   | int t7
//      13:   | t7 = t0 + t1
//      14:   | int t8
//      15:   | t8 = t2 * t3
//      16:   | t6 = t7 << t8
//      17:   | t5 = t4 < t6
//      18:   | if t5 != 0 goto L20
//      19:   | jmp L39
//      20:   | | if t0 != 0 goto L22
//      21:   | | jmp L37
//      22:   | | | if t1 != 0 goto L24
//      23:   | | | jmp L36
//      24:   | | | | if t2 != 0 goto L26
//      25:   | | | | jmp L32
//      26:   | | | | | if t3 != 0 goto L28
//      27:   | | | | | jmp L30
//      28:   | | | | | t4 = t4 - 1
//      29:   | | | | | jmp L31
//      30:   | | | | | t4 = t4 + 1
//      31:   | | | | jmp L24
//      32:   | | | int t9
//      33:   | | | t9 = t0 % 13
//      34:   | | | t0 = t9
//      35:   | | | jmp L22
//      36:   | | jmp L20
//      37:   | t4 = t4 + 1
//      38:   | jmp L10
//      39:   ret t0
int __do() {
    int a = 0;
    int b = 1;
    int c = 2;
    int d = 3;

    for (int i = 0; i < a + b << c * d; ++i) {
        while (a) {
            while (b) {
                while (c) {
                    if (d) {
                        --i;
                    } else {
                        ++i;
                    }
                }
                c = c % 13;
            }
        }
    }

    return a + b + d;
}

int __dont() {
    int a = 0;
    int b = 1;
    int c = 2;
    int d = 3;

    for (int i = 0; i < a + b << c * d; ++i) {
        while (a) {
            while (b) {
                while (c) {
                    if (d) {
                        --i;
                    } else {
                        ++i;
                    }
                }
                a = a % 13;
            }
        }
    }

    return a;
}
