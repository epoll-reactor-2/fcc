// Error at line 7, column 25: Cannot apply `+` to <INT> and <CHAR>
int main() {
    int a = 1;
    char b = 'a';
    int c = a + a;
    char d = b + b;
    /* ??? */ int e = a + b;
    return 0;
}