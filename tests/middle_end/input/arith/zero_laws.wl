//fun f(alloca int %0):
//       0:   alloca int %1
//       1:   alloca int %2
//       2:   store %2 %0
//       3:   store %1 %2
//       4:   alloca int %3
//       5:   alloca int %4
//       6:   store %4 %1
//       7:   store %3 %4
//       8:   alloca int %5
//       9:   alloca int %6
//      10:   store %6 $0
//      11:   store %5 %6
//      12:   alloca int %7
//      13:   alloca int %8
//      14:   store %8 $0
//      15:   store %7 %8
//      16:   alloca int %9
//      17:   alloca int %10
//      18:   store %10 %7
//      19:   store %9 %10
//      20:   alloca int %11
//      21:   alloca int %12
//      22:   store %12 $0
//      23:   store %11 %12
//      24:   alloca int %13
//      25:   alloca int %14
//      26:   store %14 %11 shl $1
//      27:   store %13 %14
//      28:   alloca int %15
//      29:   alloca int %16
//      30:   store %16 %11 shl $2
//      31:   store %15 %16
//      32:   alloca int %17
//      33:   alloca int %18
//      34:   store %18 %11 shl $3
//      35:   store %17 %18
//      36:   alloca int %19
//      37:   alloca int %20
//      38:   store %20 %11 shl $4
//      39:   store %19 %20
//      40:   alloca int %21
//      41:   alloca int %22
//      42:   store %22 %11 mul $17
//      43:   store %21 %22
//      44:   alloca int %23
//      45:   alloca int %24
//      46:   store %24 %11 shl $5
//      47:   store %23 %24
//      48:   alloca int %25
//      49:   alloca int %26
//      50:   store %26 %11 mul $33
//      51:   store %25 %26
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