//fun f(alloca int %0):
//       0:   alloca int %0
//       1:   alloca int %1
//       2:   store %1 %0
//       3:   store %0 %1
//       4:   alloca int %2
//       5:   alloca int %3
//       6:   store %3 %0
//       7:   store %2 %3
//       8:   alloca int %4
//       9:   alloca int %5
//      10:   store %5 $0
//      11:   store %4 %5
//      12:   alloca int %6
//      13:   alloca int %7
//      14:   store %7 $0
//      15:   store %6 %7
//      16:   alloca int %8
//      17:   alloca int %9
//      18:   store %9 %6
//      19:   store %8 %9
//      20:   alloca int %10
//      21:   alloca int %11
//      22:   store %11 $0
//      23:   store %10 %11
//      24:   alloca int %12
//      25:   alloca int %13
//      26:   store %13 %10 shl $1
//      27:   store %12 %13
//      28:   alloca int %14
//      29:   alloca int %15
//      30:   store %15 %10 shl $2
//      31:   store %14 %15
//      32:   alloca int %16
//      33:   alloca int %17
//      34:   store %17 %10 shl $3
//      35:   store %16 %17
//      36:   alloca int %18
//      37:   alloca int %19
//      38:   store %19 %10 shl $4
//      39:   store %18 %19
//      40:   alloca int %20
//      41:   alloca int %21
//      42:   store %21 %10 mul $17
//      43:   store %20 %21
//      44:   alloca int %22
//      45:   alloca int %23
//      46:   store %23 %10 shl $5
//      47:   store %22 %23
//      48:   alloca int %24
//      49:   alloca int %25
//      50:   store %25 %10 mul $33
//      51:   store %24 %25
//      52:   ret $0
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