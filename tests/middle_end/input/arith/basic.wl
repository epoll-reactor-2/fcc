//fun f(alloca int %0):
//       0:   alloca int %0
//       1:   store %0 $0
//       2:   ret %0
int f(int arg) {
    return arg - arg;
}