// Error at line 5, column 30: Type mismatch: float and i1
int main() {
    float f =  0.0;
    bool  b = true;
    /* ??? */ int result = f + b;
    return 0;
}