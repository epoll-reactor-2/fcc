//fun __dont(int t0):
//       0:   int t1
//       1:   t1 = 0
//       4:   | if t0 != 0 goto L6
//       5:   | jmp L8
//       6:   | t1 = 1
//       7:   | jmp L9
//       8:   | t1 = 2
//       9:   ret t1
//fun __do(int t0):
//       0:   int t1
//       1:   t1 = 0
//       2:   int t2
//       3:   t2 = 0
//       9:   ret t2
int __dont(int arg) {
    int a = 0;
    int b = 0;

    if (arg) {
        a = 1;
    } else {
        a = 2;
    }

    return a;
}

int __do(int arg) {
    int a = 0;
    int b = 0;

    if (arg) {
        a = 1;
    } else {
        a = 2;
    }

    return b;
}