//fun __do():
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
//      12:   | | | t0 = t0 + 1
//      13:   | | | jmp L10
//      14:   | | t0 = t0 + 1
//      15:   | | jmp L8
//      16:   | t0 = t0 + 1
//      17:   | jmp L6
//      18:   ret t0
//--------
//instr  0: depends on ()
//instr  1: depends on ()
//instr  2: depends on ()
//instr  3: depends on ()
//instr  4: depends on ()
//instr  5: depends on ()
//instr  6: depends on (2, 3)
//instr  7: depends on ()
//instr  8: depends on (4, 5)
//instr  9: depends on ()
//instr 10: depends on (0, 1)
//instr 11: depends on ()
//instr 12: depends on (0, 1, 12)
//instr 13: depends on ()
//instr 14: depends on (0, 1, 12, 14)
//instr 15: depends on ()
//instr 16: depends on (0, 1, 12, 14, 16)
//instr 17: depends on ()
//instr 18: depends on (0, 1, 12, 14, 16)
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

    return a;
}