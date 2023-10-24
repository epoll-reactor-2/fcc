//fun main(int t0):
//       0:   int t1
//       1:   t1 = 1
//       2:   int t2
//       3:   t2 = 2
//       4:   if t0 != 0 goto L6
//       5:   jmp L8
//       6:   t1 = t1(@noalias) + 1
//       7:   jmp L9
//       8:   t1 = t1(@noalias) - 1
//       9:   if t2 != 0 goto L11
//      10:   jmp L20
//      11:   int t3
//      12:   t3 = 0
//      13:   | int t4(@loop)
//      14:   | t4 = t3 < 10(@loop)
//      15:   | if t4 != 0 goto L17
//      16:   | jmp L20
//      17:   | t3 = t3(@noalias) + 1
//      18:   | t2 = t2(@noalias) + 1
//      19:   | jmp L13
//      20:   ret t1
//--------
//instr  0: depends on ()
//instr  1: depends on ()
//instr  2: depends on ()
//instr  3: depends on ()
//instr  4: depends on ()
//instr  5: depends on ()
//instr  6: depends on (6, 0, 1)
//instr  7: depends on ()
//instr  8: depends on (8, 6, 0, 1)
//instr  9: depends on (2, 3)
//instr 10: depends on ()
//instr 11: depends on ()
//instr 12: depends on ()
//instr 13: depends on ()
//instr 14: depends on (11, 12)
//instr 15: depends on (14, 13)
//instr 16: depends on ()
//instr 17: depends on (11, 12, 17)
//instr 18: depends on (2, 3, 18)
//instr 19: depends on ()
//instr 20: depends on (8, 6, 0, 1)
int main(int arg) {
    int a = 1;
    int b = 2;

    if (arg) {
        ++a;
    } else {
        --a;
    }

    if (b) {
        int i = 0;
        while (i < 10) {
            ++i;
            ++b;
        }
    }

    return a;
}