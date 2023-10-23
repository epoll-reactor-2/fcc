//fun complex():
//       0:   int t0
//       1:   t0 = 10000
//       2:   int t1
//       3:   int t2
//       4:   t2 = 25000
//       5:   t1 = 25000
//       6:   int t3
//       7:   int t4
//       8:   t4 = 45000
//       9:   t3 = 45000
//      10:   int t5
//      11:   int t6
//      12:   t6 = 70000
//      13:   t5 = 70000
//      14:   int t7
//      15:   t7 = 0
//      16:   int t8(@loop)
//      17:   t8 = 0(@loop)
//      18:   | int t9
//      19:   | int t10
//      20:   | int t11
//      21:   | t11 = 11
//      22:   | t10 = 111
//      23:   | t9 = t8 < 111
//      24:   | if t9 != 0 goto L26
//      25:   | jmp L58
//      26:   | int t12
//      27:   | int t13
//      28:   | int t14
//      29:   | t14 = t0 * t8
//      30:   | int t15
//      31:   | int t16
//      32:   | int t17
//      33:   | int t18
//      34:   | int t19
//      35:   | int t20
//      36:   | t20 = 50
//      37:   | t19 = t3 + 50
//      38:   | t18 = 10 + t19
//      39:   | t17 = t1 + t18
//      40:   | t16 = t0 + t17
//      41:   | int t21
//      42:   | t21 = t8 + t5
//      43:   | t15 = t16 - t21
//      44:   | t13 = t14 + t15
//      45:   | t12 = t7 + t13
//      46:   | t7 = t12
//      47:   | | if t0 != 0 goto L49
//      48:   | | jmp L56
//      49:   | | t0 = t0 - 1
//      50:   | | int t22
//      51:   | | int t23
//      52:   | | t23 = t3 + t5
//      53:   | | t22 = t1 + t23
//      54:   | | t0 = t22
//      55:   | | jmp L47
//      56:   | t8 = t8(@noalias) + 1(@loop)
//      57:   | jmp L18
//      58:   ret t7
int complex() {
    int a = 10000;
    int b = 15000 + a;
    int c = 20000 + b;
    int d = 25000 + c;
    int result = 0;

    for (int i = 0; i < 100 + 10 + 1; ++i) {
        result = result + a * i + (a + b + 10 + c + 20 + 30) - i + d;
        while (a) {
            --a;
            a = b + c + d;
        }
    }

    return result;
}