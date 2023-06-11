//E<2:1>: Cannot return char instead of float
float f() {
    char a = 'a';
    char b = a;
    return a + b;
}

int main() {
    return 0;
}
