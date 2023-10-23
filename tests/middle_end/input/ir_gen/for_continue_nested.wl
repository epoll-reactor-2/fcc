//fun in_out():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   int t3(@loop)
//       7:   t3 = 0(@loop)
//       8:   | int t4
//       9:   | int t5
//      10:   | int t6
//      11:   | t6 = t1 + t2
//      12:   | t5 = t0 + t6
//      13:   | t4 = t3 < t5
//      14:   | if t4 != 0 goto L16
//      15:   | jmp L42
//      16:   | t0 = t0(@noalias) + 1
//      17:   | t1 = t1(@noalias) + 1
//      18:   | t2 = t2(@noalias) + 1
//      19:   | int t7
//      20:   | int t8
//      21:   | t8 = t3 % 2
//      22:   | t7 = t8 == 0
//      23:   | if t7 != 0 goto L25
//      24:   | jmp L27
//      25:   | t3 = t3(@noalias) + 1
//      26:   | jmp L37
//      27:   | int t9(@loop)
//      28:   | t9 = 0(@loop)
//      29:   | | int t10
//      30:   | | t10 = t9 < 100
//      31:   | | if t10 != 0 goto L33
//      32:   | | jmp L36
//      33:   | | jmp L29
//      34:   | | t3 = t3(@noalias) + 1(@loop)
//      35:   | | jmp L29
//      36:   | jmp L29
//      37:   | t0 = t0(@noalias) - 1
//      38:   | t1 = t1(@noalias) - 1
//      39:   | t2 = t2(@noalias) - 1
//      40:   | t3 = t3(@noalias) + 1(@loop)
//      41:   | jmp L8
//      42:   ret
//fun out_in():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = t1
//       6:   int t3(@loop)
//       7:   t3 = 0(@loop)
//       8:   | int t4
//       9:   | int t5
//      10:   | int t6
//      11:   | t6 = t1 + t2
//      12:   | t5 = t0 + t6
//      13:   | t4 = t3 < t5
//      14:   | if t4 != 0 goto L16
//      15:   | jmp L42
//      16:   | t0 = t0(@noalias) + 1
//      17:   | t1 = t1(@noalias) + 1
//      18:   | t2 = t2(@noalias) + 1
//      19:   | int t7
//      20:   | int t8
//      21:   | t8 = t3 % 2
//      22:   | t7 = t8 == 0
//      23:   | if t7 != 0 goto L25
//      24:   | jmp L27
//      25:   | t3 = t3(@noalias) + 1
//      26:   | jmp L37
//      27:   | jmp L8
//      28:   | int t9(@loop)
//      29:   | t9 = 0(@loop)
//      30:   | | int t10
//      31:   | | t10 = t9 < 100
//      32:   | | if t10 != 0 goto L34
//      33:   | | jmp L37
//      34:   | | jmp L30
//      35:   | | t3 = t3(@noalias) + 1(@loop)
//      36:   | | jmp L30
//      37:   | t0 = t0(@noalias) - 1
//      38:   | t1 = t1(@noalias) - 1
//      39:   | t2 = t2(@noalias) - 1
//      40:   | t3 = t3(@noalias) + 1(@loop)
//      41:   | jmp L8
//      42:   ret
void in_out() {
    int a = 1;
    int b = a;
    int c = b;

    for (int i = 0; i < a + b + c; ++i) {
        ++a;
        ++b;
        ++c;
        if (i % 2 == 0) {
            ++i;
        } else {
            for (int j = 0; j < 100; ++i) {
                continue;
            }
            continue;
        }
        --a;
        --b;
        --c;
    }
}

void out_in() {
    int a = 1;
    int b = a;
    int c = b;

    for (int i = 0; i < a + b + c; ++i) {
        ++a;
        ++b;
        ++c;
        if (i % 2 == 0) {
            ++i;
        } else {
            continue;
            for (int j = 0; j < 100; ++i) {
                continue;
            }
        }
        --a;
        --b;
        --c;
    }
}