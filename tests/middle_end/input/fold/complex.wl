//fun complex():
//       0:   alloca int %0
//       8:   alloca int %4
//      10:   alloca int %5(@loop)
//      11:   store %5 $0(@loop)
//      12:   alloca int %6
//      13:   store %6 %5 lt $100
//      14:   if %6 neq $0 goto L16
//      15:   jmp L31
//      16:   alloca int %7
//      23:   store %7 %4 add $70000
//      24:   store %4 %7
//      25:   if %0 neq $0 goto L27
//      26:   jmp L29
//      27:   store %0 %0 sub $1
//      28:   jmp L25
//      29:   store %5 %5(@noalias) add $1(@loop)
//      30:   jmp L12
//      31:   ret %4
int complex() {
    int a = 10000;
    int b = 15000;
    int c = 20000;
    int d = 25000;
    int result = 0;

    for (int i = 0; i < 100; ++i) {
        result = result + a + b + c + d;
        while (a) {
            --a;
        }
    }

    return result;
}