// Error at line 2, column 1: Cannot return <CHAR> instead of <FLOAT>
float f() {
    char a = 1;
    char b = a;
    return a + b;
}

int main() {
    return 0;
}