// Error at line 5, column 30: Cannot apply `+` to float and bool
int main() {
    float f =  0.0;
    bool  b = true;
    /* ??? */ int result = f + b;
    return 0;
}