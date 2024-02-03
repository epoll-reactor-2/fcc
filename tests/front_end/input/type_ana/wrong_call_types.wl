//E<5:15>: For argument `c` got char, but int expected
void f(int a, char b, int c) {}

int main() {
    f(0, 'a', 'b');
    return 0;
}
