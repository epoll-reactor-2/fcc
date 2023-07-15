//fun complex():
//       0:   alloca int %0
//       8:   alloca int %4
//      10:   alloca int %5(@loop)
//      11:   store %5 $0(@loop)
//      12:   alloca int %6
//      13:   store %6 %5 lt $100
//      14:   if %6 neq $0 goto L16
//      15:   jmp L39
//      16:   alloca int %7
//      17:   alloca int %8
//      18:   alloca int %9
//      19:   store %9 $10000 mul %5
//      20:   alloca int %10
//      27:   alloca int %14
//      28:   store %14 %5 add $25000
//      29:   store %10 $70000 sub %14
//      30:   store %8 %9 add %10
//      31:   store %7 %4 add %8
//      32:   store %4 %7
//      33:   if %0 neq $0 goto L35
//      34:   jmp L37
//      35:   store %0 %0 sub $1
//      36:   jmp L33
//      37:   store %5 %5(@noalias) add $1(@loop)
//      38:   jmp L12
//      39:   ret %4
int complex() {
    int a = 10000;
    int b = 15000;
    int c = 20000;
    int d = 25000;
    int result = 0;

    for (int i = 0; i < 100; ++i) {
        result = result + a * i + (a + b + c + d) - i + d;
        while (a) {
            --a;
        }
    }

    return result;
}