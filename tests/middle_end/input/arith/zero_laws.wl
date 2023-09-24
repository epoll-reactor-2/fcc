//fun f(int t0):
//       0:   int t1
//       1:   int t2
//       2:   t2 = t0
//       3:   t1 = t2
//       4:   int t3
//       5:   int t4
//       6:   t4 = t1
//       7:   t3 = t4
//       8:   int t5
//       9:   int t6
//      10:   t6 = 0
//      11:   t5 = t6
//      12:   int t7
//      13:   int t8
//      14:   t8 = 0
//      15:   t7 = t8
//      16:   int t9
//      17:   int t10
//      18:   t10 = t7
//      19:   t9 = t10
//      20:   int t11
//      21:   int t12
//      22:   t12 = 0
//      23:   t11 = t12
//      24:   int t13
//      25:   int t14
//      26:   t14 = t11 << 1
//      27:   t13 = t14
//      28:   int t15
//      29:   int t16
//      30:   t16 = t11 << 2
//      31:   t15 = t16
//      32:   int t17
//      33:   int t18
//      34:   t18 = t11 << 3
//      35:   t17 = t18
//      36:   int t19
//      37:   int t20
//      38:   t20 = t11 << 4
//      39:   t19 = t20
//      40:   int t21
//      41:   int t22
//      42:   t22 = t11 * 17
//      43:   t21 = t22
//      44:   int t23
//      45:   int t24
//      46:   t24 = t11 << 5
//      47:   t23 = t24
//      48:   int t25
//      49:   int t26
//      50:   t26 = t11 * 33
//      51:   t25 = t26
//      52:   ret 0
int f(int arg) {
    int i1  = arg +  0;
    int i2  = i1  -  0;
    int i3  = i2  *  0;
    int i4  = i3  &  0;
    int i5  = i4  |  0;
    int i6  = i5  - i5;
    int i7  = i6  *  2;
    int i8  = i6  *  4;
    int i9  = i6  *  8;
    int i10 = i6  * 16;
    int i11 = i6  * 17;
    int i12 = i6  * 32;
    int i13 = i6  * 33;
    return 0;
}