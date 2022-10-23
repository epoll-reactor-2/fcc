// Error at line 5, column 30: Type mismatch: i1 and i8*
int main() {
    bool   b = true;
    string s =   "";
    /* ??? */ int result = b + s;
    return 0;
}