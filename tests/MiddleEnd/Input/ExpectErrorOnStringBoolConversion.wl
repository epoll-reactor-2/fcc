// Error at line 5, column 30: Type mismatch: i8* and i1
int main() {
    string s =   "";
    bool   b = true;
    /* ??? */ int result = s + b;
    return 0;
}