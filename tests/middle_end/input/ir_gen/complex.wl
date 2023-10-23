//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 1
//       4:   int t2
//       5:   t2 = 2
//       6:   int t3
//       7:   t3 = 3
//       8:   int t4
//       9:   t4 = 4
//      10:   int t5
//      11:   t5 = 5
//      12:   int t6(@loop)
//      13:   int t7(@loop)
//      14:   int t8(@loop)
//      15:   t8 = 123 * 456(@loop)
//      16:   int t9(@loop)
//      17:   int t10(@loop)
//      18:   t10 = t1 / t0(@loop)
//      19:   t9 = 2 * t10(@loop)
//      20:   t7 = t8 << t9(@loop)
//      21:   t6 = t7(@loop)
//      22:   | int t11
//      23:   | int t12
//      24:   | int t13
//      25:   | int t14
//      26:   | int t15
//      27:   | t15 = t5 / t0
//      28:   | t14 = t15 % t1
//      29:   | t13 = t4 + t14
//      30:   | t12 = t3 + t13
//      31:   | t11 = t6 < t12
//      32:   | if t11 != 0 goto L34
//      33:   | jmp L76
//      34:   | | int t16(@loop)
//      35:   | | int t17(@loop)
//      36:   | | int t18(@loop)
//      37:   | | int t19(@loop)
//      38:   | | t19 = t2 + t3(@loop)
//      39:   | | t18 = t1 + t19(@loop)
//      40:   | | t17 = t18 < 100(@loop)
//      41:   | | t16 = t0 & t17(@loop)
//      42:   | | if t16 != 0 goto L44
//      43:   | | jmp L46
//      44:   | | t1 = t1(@noalias) + 1
//      45:   | | jmp L34
//      46:   | | int t20(@loop)
//      47:   | | int t21(@loop)
//      48:   | | int t22(@loop)
//      49:   | | int t23(@loop)
//      50:   | | t23 = 1 + 2(@loop)
//      51:   | | t22 = t1 + t23(@loop)
//      52:   | | t21 = t4 + t22(@loop)
//      53:   | | t20 = t3 + t21(@loop)
//      54:   | | if t20 != 0 goto L46
//      55:   | if t3 != 0 goto L57
//      56:   | jmp L71
//      57:   | if 1 != 0 goto L59
//      58:   | jmp L63
//      59:   | if 0 != 0 goto L61
//      60:   | jmp L62
//      61:   | ret 666
//      62:   | jmp L70
//      63:   | if 2 != 0 goto L65
//      64:   | jmp L67
//      65:   | ret 777
//      66:   | jmp L70
//      67:   | if 3 != 0 goto L69
//      68:   | jmp L70
//      69:   | ret 888
//      70:   | jmp L74
//      71:   | if 4 != 0 goto L73
//      72:   | jmp L74
//      73:   | ret 999
//      74:   | t6 = t6(@noalias) + 1(@loop)
//      75:   | jmp L22
//      76:   ret 0
int main() {
    int a = 0;
    int b = 1;
    int c = 2;
    int d = 3;
    int e = 4;
    int f = 5;
    
    for (int i = 123 * 456 << 2 * b / a; i < d + e + (f / a) % b; ++i) {
        while (a & b + c + d < 100) {
            ++b;
        }
        do {
        
        } while (d + e + b + 1 + 2);
        
        if (d) {
            if (1) {
                if (0) {
                    return 666;
                }
            } else {
                if (2) {
                    return 777;
                } else {
                    if (3) {
                        return 888;
                    }
                }
            }
        } else {
            if (4) {
                return 999;
            }
        }
    }

    return 0;
}