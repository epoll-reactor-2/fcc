// Error at line 5, column 30: Cannot apply `+` to <FLOAT> and <INT>
int main() {
    float f = 0.0;
    int   i =   0;
    /* ??? */ int result = f + i;
    return 0;
}