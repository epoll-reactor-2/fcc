//0
int f_0() { return 1 + 2; }
int f_1() { return f_0(); }
int f_2() { return f_1(); }

int main() {
    return f_0() + f_1() + f_2();
}