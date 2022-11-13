// Error at line 5, column 30: Cannot apply `+` to <BOOLEAN> and <FLOAT>
int main() {
    bool  b = true;
    float f =  0.0;
    /* ??? */ int result = b + f;
    return 0;
}