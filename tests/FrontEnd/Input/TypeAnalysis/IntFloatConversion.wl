// Error at line 5, column 30: Cannot apply `+` to <INT> and <FLOAT>
int main() {
    int   i =   0;
    float f = 0.0;
    /* ??? */ int result = i + f;
    return 0;
}