//fun complex():
//       8:   alloca int %4
//      10:   alloca int %5
//      11:   store %5 $0
//      12:   alloca int %6
//      13:   store %6 %5 lt $100
//      14:   if %6 neq $0 goto L16
//      15:   jmp L29
//      16:   alloca int %7
//      17:   alloca int %8
//      24:   store %8 %5 add $70000
//      25:   store %7 $0 add %8
//      26:   store %4 %7
//      27:   store %5 %5 add $1
//      28:   jmp L12
//      29:   ret %4
int complex() {
    int a = 10000;
    int b = 15000;
    int c = 20000;
    int d = 25000;
    int result = 0;

    for (int i = 0; i < 100; ++i) {
        result = result + i + a + b + c + d;
    }

    return result;
}