//fun f(alloca int %0):
//       1:   alloca int %1
//       2:   alloca int %2
//       3:   store %2 %0
//       4:   store %1 %2
//       5:   alloca int %3
//       6:   alloca int %4
//       7:   store %4 %1
//       8:   store %3 %4
//       9:   alloca int %5
//      10:   alloca int %6
//      11:   store %6 $0
//      12:   store %5 %6
//      13:   alloca int %7
//      14:   alloca int %8
//      15:   store %8 $0
//      16:   store %7 %8
//      17:   alloca int %9
//      18:   alloca int %10
//      19:   store %10 %7
//      20:   store %9 %10
//      21:   alloca int %11
//      22:   alloca int %12
//      23:   store %12 $0
//      24:   store %11 %12
//      25:   alloca int %13
//      26:   alloca int %14
//      27:   store %14 %11 shl $1
//      28:   store %13 %14
//      29:   alloca int %15
//      30:   alloca int %16
//      31:   store %16 %11 shl $2
//      32:   store %15 %16
//      33:   alloca int %17
//      34:   alloca int %18
//      35:   store %18 %11 shl $3
//      36:   store %17 %18
//      37:   alloca int %19
//      38:   alloca int %20
//      39:   store %20 %11 shl $4
//      40:   store %19 %20
//      41:   alloca int %21
//      42:   alloca int %22
//      43:   store %22 %11 mul $17
//      44:   store %21 %22
//      45:   alloca int %23
//      46:   alloca int %24
//      47:   store %24 %11 shl $5
//      48:   store %23 %24
//      49:   alloca int %25
//      50:   alloca int %26
//      51:   store %26 %11 mul $33
//      52:   store %25 %26
//      53:   ret $0
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