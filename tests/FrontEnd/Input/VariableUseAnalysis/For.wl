// Warning at line 4, column 10: Variable `i` is never used
// Warning at line 9, column 5: Variable `j` is never used
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