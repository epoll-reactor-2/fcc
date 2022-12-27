// 40
int f1() {
    int i = 0;
    for ( ; i < 10; ++i)
        {}
    return i;
}

int f2() {
    for (int i = 0; ; ++i) {
        if (i == 10) {
            return i;
        }
    }
    return 0;
}

int f3() {
    int i = 0;
    for ( ; i < 10; ) {
        ++i;
    }
    return i;
}

int f4() {
    int i = 0;
    for (;;) {
        if (i == 10) {
            return i;
        }
        ++i;
    }
    return 0;
}

int main() {
    int ret = 0;
    ret += f1();
    ret += f2();
    ret += f3();
    ret += f4();
    return ret;
}