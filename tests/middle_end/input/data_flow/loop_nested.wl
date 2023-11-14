//fun __dont():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       4:   int t2
//       5:   t2 = 0
//       6:   | if t1 != 0 goto L8
//       7:   | jmp L18
//       8:   | | if t2 != 0 goto L10
//       9:   | | jmp L16
//      10:   | | | if t0 != 0 goto L12
//      11:   | | | jmp L14
//      12:   | | | t0 = t0(@noalias) + 1
//      13:   | | | jmp L10
//      14:   | | t0 = t0(@noalias) + 1
//      15:   | | jmp L8
//      16:   | t0 = t0(@noalias) + 1
//      17:   | jmp L6
//      18:   ret t0
//fun __do():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//      18:   ret t1
int __do() {
    int a = 0;
    int b = 0;
    int c = 0;

    while (b) {
        while (c) {
            while (a) {
                ++a;
            }
            ++a;
        }
        ++a;
    }

    return b;
}

int __dont() {
    int a = 0;
    int b = 0;
    int c = 0;

    while (b) {
        while (c) {
            while (a) {
                ++a;
            }
            ++a;
        }
        ++a;
    }

    return a;
}