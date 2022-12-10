// Error at line 5, column 30: Cannot apply `+` to bool and float
int main() {
    bool  b = true;
    float f =  0.0;
    /* ??? */ int result = b + f;
    return 0;
}