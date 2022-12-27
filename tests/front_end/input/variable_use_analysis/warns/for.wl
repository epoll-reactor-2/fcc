// Warning at line 5, column 10: Variable `i` is never used
// Warning at line 6, column 5: Variable `i` written, but never read
// Warning at line 10, column 5: Variable `j` is never used
int main() {
    for (int i = 0; ; ) {}
    int i = 0;
    for (;;) {
        ++i;
    }
    int j = 0;
    for (;;) {}
    return 0;
}
