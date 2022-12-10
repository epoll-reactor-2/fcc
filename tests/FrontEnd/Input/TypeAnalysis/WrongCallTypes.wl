// Error at line 5, column 18: For argument `c` got int, but expected char
void f(int a, char b, int c) {}

int main() {
    f(0, 'a', 'b');
    return 0;
}