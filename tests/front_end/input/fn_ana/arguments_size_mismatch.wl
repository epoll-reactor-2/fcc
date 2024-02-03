//E<5:5>: Arguments size mismatch: 9 got, but 5 expected
void f(int a, int b, int c, int d, int e) {}

int main() {
    f(1, 2, 3, 4, 5, 6, 7, 8, 9);
    return 0;
}