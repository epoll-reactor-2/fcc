//a
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