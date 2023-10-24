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
//       9:   ret t1
//--------
//instr  0: depends on ()
//instr  1: depends on ()
//instr  2: depends on ()
//instr  3: depends on ()
//instr  4: depends on ()
//instr  5: depends on ()
//instr  6: depends on (1, 6, 0)
//instr  7: depends on ()
//instr  8: depends on (1, 6, 8, 0)
//instr  9: depends on (1, 6, 8, 0)
int main(int arg) {
    int a = 1;
    int b = 2;

    if (arg) {
        ++a;
    } else {
        --a;
    }

    return a;
}