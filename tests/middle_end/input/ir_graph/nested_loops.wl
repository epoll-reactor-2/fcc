//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = 2
//       4:   int t2
//       5:   t2 = 3
//       6:   | if t0 != 0 goto L8
//       7:   | jmp L59
//       8:   | int t3
//       9:   | t3 = 0
//      10:   | int t4(@loop)
//      11:   | t4 = 0(@loop)
//      12:   | | int t5
//      13:   | | t5 = t4 < 1000
//      14:   | | if t5 != 0 goto L16
//      15:   | | jmp L32
//      16:   | | int t6
//      17:   | | int t7
//      18:   | | t7 = t0 % 2
//      19:   | | t6 = t7 == 0
//      20:   | | if t6 != 0 goto L22
//      21:   | | jmp L23
//      22:   | | t1 = t1(@noalias) + 1
//      23:   | | int t8
//      24:   | | int t9
//      25:   | | t9 = t0 % 3
//      26:   | | t8 = t9 == 0
//      27:   | | if t8 != 0 goto L29
//      28:   | | jmp L30
//      29:   | | t2 = t2(@noalias) + 1
//      30:   | | t4 = t4(@noalias) + 1(@loop)
//      31:   | | jmp L12
//      32:   | | if t1 != 0 goto L34
//      33:   | | jmp L58
//      34:   | | t1 = t1(@noalias) - 1
//      35:   | | | if t2 != 0 goto L37
//      36:   | | | jmp L57
//      37:   | | | t2 = t2(@noalias) - 1
//      38:   | | | | if t3 != 0 goto L40
//      39:   | | | | jmp L56
//      40:   | | | | t3 = t3(@noalias) - 1
//      41:   | | | | int t10
//      42:   | | | | int t11
//      43:   | | | | int t12
//      44:   | | | | int t13
//      45:   | | | | int t14
//      46:   | | | | int t15
//      47:   | | | | int t16
//      48:   | | | | t16 = t1 + t0
//      49:   | | | | t15 = t0 - t16
//      50:   | | | | t14 = t0 + t15
//      51:   | | | | t13 = t1 + t14
//      52:   | | | | t12 = t2 + t13
//      53:   | | | | t11 = t1 - t12
//      54:   | | | | t10 = t0 + t11
//      55:   | | | | jmp L38
//      56:   | | | jmp L35
//      57:   | | jmp L32
//      58:   | jmp L6
//      59:   ret t0
int main() {
    int a = 1;
    int b = 2;
    int c = 3;

    while (a) {
        int d = 0;

        for (int i = 0; i < 1000; ++i) {
            if (a % 2 == 0) {
                ++b;
            }
            if (a % 3 == 0) {
                ++c;
            }
        }

        while (b) {
            --b;
            while (c) {
                --c;
                while (d) {
                    --d;
                    a + b - c + b + a + a - b + a;
                }
            }
        }
    }

    return a;
}