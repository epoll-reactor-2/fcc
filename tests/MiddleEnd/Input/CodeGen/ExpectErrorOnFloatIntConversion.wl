// Error at line 5, column 30: Type mismatch: float and i32
int main() {
    float f = 0.0;
    int   i =   0;
    /* ??? */ int result = f + i;
    return 0;
}