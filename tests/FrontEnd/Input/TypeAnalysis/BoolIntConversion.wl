// Error at line 5, column 30: Cannot apply `+` to <BOOLEAN> and <INT>
int main() {
    bool  b = true;
    int   i =    0;
    /* ??? */ int result = b + i;
    return 0;
}