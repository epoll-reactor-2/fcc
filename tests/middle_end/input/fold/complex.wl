//fun complex():
//       0:   int t0
//       1:   t0 = 10000
//       6:   int t3
//       7:   t3 = 25000
//       8:   int t4
//       9:   t4 = 0
//      10:   int t5(@loop)
//      11:   t5 = 0(@loop)
//      12:   int t6
//      13:   t6 = t5 < 100
//      14:   if t6 != 0 goto L16
//      15:   jmp L39
//      16:   int t7
//      17:   int t8
//      18:   int t9
//      19:   t9 = 10000 * t5
//      20:   int t10
//      21:   int t11
//      26:   t11 = 70000
//      27:   int t14
//      28:   t14 = t5 + 25000
//      29:   t10 = 70000 - t14
//      30:   t8 = t9 + t10
//      31:   t7 = t4 + t8
//      32:   t4 = t7
//      33:   if t0 != 0 goto L35
//      34:   jmp L37
//      35:   t0 = t0 - 1
//      36:   jmp L33
//      37:   t5 = t5(@noalias) + 1(@loop)
//      38:   jmp L12
//      39:   ret t4
int complex() {
    int a = 10000;
    int b = 15000;
    int c = 20000;
    int d = 25000;
    int result = 0;

    for (int i = 0; i < 100; ++i) {
        result = result + a * i + (a + b + c + d) - i + d;
        while (a) {
            --a;
        }
    }

    return result;
}