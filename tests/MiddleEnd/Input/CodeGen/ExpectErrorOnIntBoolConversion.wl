// Error at line 5, column 30: Type mismatch: i32 and i1
int main() {
    int  i =   0;
    bool b = true;
    /* ??? */ int result = i + b;
    return 0;
}