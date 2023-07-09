//fun f(alloca int %0):
//       1:   alloca int %1
//       3:   if %0 neq $0 goto L5
//       4:   jmp L7
//       5:   store %1 %1 sub $1
//       6:   jmp L8
//       7:   store %1 %1 add $1
//       8:   ret %1
int f(int arg) {
    int r = 0;
    if (arg) {
        --r;
    } else {
        ++r;
    }
    return r;
}