//fun __dont():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       4:   int t2
//       5:   t2 = 0
//       6:   | if t0 != 0 goto L8
//       7:   | jmp L10
//       8:   | t0 = t0 + 1
//       9:   | jmp L6
//      10:   | if t1 != 0 goto L12
//      11:   | jmp L14
//      12:   | t1 = t1 + 1
//      13:   | jmp L10
//      14:   | if t2 != 0 goto L16
//      15:   | jmp L18
//      16:   | t2 = t2 + 1
//      17:   | jmp L14
//      18:   int t3
//      19:   t3 = t0 + t1
//      20:   ret t3
//--------
//instr  0: depends on ()
//instr  1: depends on ()
//instr  2: depends on ()
//instr  3: depends on ()
//instr  4: depends on ()
//instr  5: depends on ()
//instr  6: depends on (0, 1)
//instr  7: depends on ()
//instr  8: depends on (0, 1, 8)
//instr  9: depends on ()
//instr 10: depends on (2, 3)
//instr 11: depends on ()
//instr 12: depends on (2, 3, 12)
//instr 13: depends on ()
//instr 14: depends on (4, 5)
//instr 15: depends on ()
//instr 16: depends on (4, 5, 16)
//instr 17: depends on ()
//instr 18: depends on ()
//instr 19: depends on (0, 1, 2, 3, 8, 12)
//instr 20: depends on (18, 19)
int __dont() {
    int i = 0;
    int j = 0;
    int k = 0;

    while (i) { ++i; }
    while (j) { ++j; }
    while (k) { ++k; }

    return i + j;
}