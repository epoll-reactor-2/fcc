//E<5:30>: Cannot apply `+` to boolean and float
int main() {
    bool  b = true;
    float f =  0.0;
    /* ??? */ int result = b + f;
    return 0;
}
