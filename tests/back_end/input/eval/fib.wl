//34
int main() {
    int a = 0;
    int b = 1;
    int r = 1;

    for (int i = 3; i < 10; ++i) {
        a = b;
        b = r;
        r = a + b;
    }

    return r;
}