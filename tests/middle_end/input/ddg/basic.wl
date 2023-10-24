//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = 2
//       4:   int t2
//       5:   t2 = 3
//       6:   ret t0
//--------
//instr  0: depends on ()
//instr  1: depends on ()
//instr  2: depends on ()
//instr  3: depends on ()
//instr  4: depends on ()
//instr  5: depends on ()
//instr  6: depends on (1, 0)
int main() {
    int a = 1;
    int b = 2;
    int c = 3;
    return a;
}