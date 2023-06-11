//E<5:30>: Cannot apply `+` to float and boolean
int main() {
    float f =  0.0;
    bool  b = true;
    /* ??? */ int result = f + b;
    return 0;
}
