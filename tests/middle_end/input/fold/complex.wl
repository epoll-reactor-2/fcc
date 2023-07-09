//fun complex():
//      10:   alloca int %5
//      12:   alloca int %6
//      13:   store %6 %5 lt $100
//      14:   if %6 neq $0 goto L16
//      15:   jmp L30
//      16:   alloca int %7
//      17:   alloca int %8
//      18:   alloca int %9
//      25:   store %9 %5 add $70000
//      26:   store %8 %4 add %9
//      27:   store %7 %4 ??? %8
//      28:   store %5 %5 add $1
//      29:   jmp L14
//      30:   ret %4
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