//fun f(int t0):
//       0:   int t1
//       1:   t1 = 0
//       2:   | if t0 != 0 goto L4
//       3:   | jmp L6
//       4:   | t1 = 1
//       5:   | jmp L7
//       6:   | t1 = 2
//       7:   ret t1
int f(int arg) {
    int r = 0;
    if (arg) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}