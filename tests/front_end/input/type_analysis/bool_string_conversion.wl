// Error at line 5, column 30: Cannot apply `+` to bool and string
int main() {
    bool   b = true;
    string s =   "";
    /* ??? */ int result = b + s;
    return 0;
}