// a
int complex() {
    int a = 10000;
    int b = 20000;
    int c = 30000;
    int d = 40000;
    int result = 0;

    for (int i = 0; i < 100; ++i) {
        result = result + i + a + b + c + d;
    }

    return result;
}