//fun f(int t0):
//       0:   int t1
//       1:   t1 = 0
//       2:   int t2
//       3:   t2 = t0 < 2
//       4:   if t2 != 0 goto L6
//       5:   jmp L8
//       6:   t1 = 1
//       7:   jmp L9
//       8:   t1 = 2
//       9:   ret t1
int f(int arg) {
    int result = 0;
    if (arg < 2) {
        result = 1;
    } else {
        result = 2;
    }
    return result;
}