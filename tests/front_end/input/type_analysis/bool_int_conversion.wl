//Error at line 5, column 30: Cannot apply `+` to boolean and int
int main() {
    bool  b = true;
    int   i =    0;
    /* ??? */ int result = b + i;
    return 0;
}
