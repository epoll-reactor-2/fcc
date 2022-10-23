// Error at line 5, column 30: Type mismatch: i32 and float
int main() {
    int   i =   0;
    float f = 0.0;
    /* ??? */ int result = i + f;
    return 0;
}