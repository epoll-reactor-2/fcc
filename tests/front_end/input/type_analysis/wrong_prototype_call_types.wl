//E<5:10>: For argument `b` got boolean, but char expected
void f(int a, char b);

int main() {
    f(1, false);
    return 0;
}
