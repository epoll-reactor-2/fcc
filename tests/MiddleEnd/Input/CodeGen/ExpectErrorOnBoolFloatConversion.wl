// Error at line 5, column 30: Type mismatch: i1 and float
int main() {
    bool  b = true;
    float f =  0.0;
    /* ??? */ int result = b + f;
    return 0;
}