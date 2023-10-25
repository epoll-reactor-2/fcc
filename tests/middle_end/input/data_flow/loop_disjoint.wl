//fun __do():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       4:   int t2
//       5:   t2 = 0
//       6:   | if t0 != 0 goto L8
//       7:   | jmp L10
//       8:   | t1 = t1(@noalias) + 1
//       9:   | jmp L6
//      10:   | if t1 != 0 goto L12
//      11:   | jmp L14
//      12:   | t0 = t0(@noalias) + 1
//      13:   | jmp L10
//      14:   | if t2 != 0 goto L16
//      15:   | jmp L18
//      16:   | t0 = t0(@noalias) + 1
//      17:   | jmp L14
//      18:   int t3
//      19:   t3 = t0 + t1
//      20:   ret t3
//fun __dont():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       6:   | if t0 != 0 goto L8
//       7:   | jmp L10
//       8:   | t0 = t0(@noalias) + 1
//       9:   | jmp L6
//      10:   | if t1 != 0 goto L12
//      11:   | jmp L14
//      12:   | t1 = t1(@noalias) + 1
//      13:   | jmp L10
//      18:   int t3
//      19:   t3 = t0 + t1
//      20:   ret t3
int __do() {
    int i = 0;
    int j = 0;
    int k = 0;

    while (i) { ++j; }
    while (j) { ++i; }
    while (k) { ++i; }

    return i + j;
}

int __dont() {
    int i = 0;
    int j = 0;
    int k = 0;

    while (i) { ++i; }
    while (j) { ++j; }
    while (k) { ++k; }

    return i + j;
}