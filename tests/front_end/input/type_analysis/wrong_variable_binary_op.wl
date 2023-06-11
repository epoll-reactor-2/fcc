//E<7:25>: Cannot apply `+` to int and char
int main() {
    int a = 1;
    char b = 'a';
    int c = a + a;
    char d = b + b;
    /* ??? */ int e = a + b;
    return 0;
}