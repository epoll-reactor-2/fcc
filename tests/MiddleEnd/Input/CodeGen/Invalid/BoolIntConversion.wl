// Error at line 5, column 30: Type mismatch: i1 and i32
int main() {
    bool  b = true;
    int   i =    0;
    /* ??? */ int result = b + i;
    return 0;
}